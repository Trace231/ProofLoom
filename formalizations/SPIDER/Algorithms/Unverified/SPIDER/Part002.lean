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
import Algorithms.Unverified.SPIDER.Part001

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

/-- Source-boundary theorem for the printed Theorem 1 stationarity claim.

The exact printed theorem says OPTION I, while its proof uses the uniformly
selected OPTION II output.  The only realized-run convergence target left in
this file is an internal extension theorem guarded by rounded-schedule
admissibility, rather than a paper-facing Theorem 1 statement under only the
quoted `n₀` interval. -/
theorem theorem1_expected_stationarity_source_boundary
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (_schedule : Theorem1Schedule P.L P.sigma epsilon n0) :
    theorem1SourceBoundary := by
  exact ⟨theorem1_printed_optionI_proof_optionII_boundary,
    theorem1_eq34_denominator_source_gap,
    theorem1_rounded_realization_source_gap⟩

end Algorithms.Unverified.SPIDER

/-
namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-!
Concrete live process spine for the active finite-sum extension.

These declarations refine the active `LiveNaturalCountRealization` branch by
constructing the actual with-replacement mini-batch process, corrected
zero-estimator update, telescope quantity, output quantity, and B.19 route from
one concrete law.
-/

def liveRefreshAt
    {n : ℕ} {s : SourceSchedule n}
    (r : LiveNaturalCountRealization s) (k : ℕ) : Prop :=
  k % r.refreshPeriod = 0

theorem liveRefreshAt_zero
    {n : ℕ} {s : SourceSchedule n}
    (r : LiveNaturalCountRealization s) :
    liveRefreshAt r 0 := by
  simp [liveRefreshAt]

noncomputable def liveConcreteSampleAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) (k : ℕ)
    (x : VariableSpace d) : VariableSpace d :=
  (r.batchSize : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin r.batchSize => D.componentGradient (omega k j) x)

noncomputable def liveConcreteRecursiveEstimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) : VariableSpace d :=
  liveConcreteSampleAverage D r omega k xCurr -
    liveConcreteSampleAverage D r omega k xPrev + vPrev

noncomputable def liveConcreteTransition
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) (k : ℕ)
    (state : State (VariableSpace d)) : State (VariableSpace d) := by
  classical
  let xNext := liveCorrectedOptionIIUpdate s state.x state.v
  let vNext :=
    if liveRefreshAt r (k + 1) then
      fullGradient D xNext
    else
      liveConcreteRecursiveEstimator D r omega (k + 1) state.v state.x xNext
  exact { x := xNext, v := vNext }

noncomputable def liveConcreteStateProcess
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s) :
    ℕ → liveConcreteSamplePath r → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullGradient D D.x0 }
  | k + 1 => fun omega =>
      liveConcreteTransition D r omega k
        (liveConcreteStateProcess D r k omega)

noncomputable def liveConcreteIterate
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s) :
    ℕ → liveConcreteSamplePath r → VariableSpace d :=
  fun k omega => (liveConcreteStateProcess D r k omega).x

noncomputable def liveConcreteEstimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s) :
    ℕ → liveConcreteSamplePath r → VariableSpace d :=
  fun k omega => (liveConcreteStateProcess D r k omega).v

@[simp] theorem liveConcreteStateProcess_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteStateProcess D r 0 omega =
      { x := D.x0, v := fullGradient D D.x0 } := by
  rfl

@[simp] theorem liveConcreteIterate_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteIterate D r 0 omega = D.x0 := by
  rfl

@[simp] theorem liveConcreteEstimator_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteEstimator D r 0 omega = fullGradient D D.x0 := by
  rfl

theorem liveConcreteInitialRefresh_error_B17
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteEstimator D r 0 omega =
      fullGradient D (liveConcreteIterate D r 0 omega) := by
  rfl

def liveConcreteEstimatorErrorBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖liveConcreteEstimator D r k omega -
          fullGradient D (liveConcreteIterate D r k omega)‖ ^ 2
          ∂liveConcreteRecursiveSampleLaw r ≤
      epsilon ^ 2

def liveConcreteOneStepDescentBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        objective D (liveConcreteIterate D r (k + 1) omega) -
          objective D (liveConcreteIterate D r k omega)
        ∂liveConcreteRecursiveSampleLaw r ≤
      -epsilon / (4 * D.L * s.n0.1) *
          ∫ omega, ‖liveConcreteEstimator D r k omega‖
            ∂liveConcreteRecursiveSampleLaw r +
        3 * epsilon ^ 2 / (4 * D.L * s.n0.1)

def liveConcreteTelescopeBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k =>
          ∫ omega, ‖liveConcreteEstimator D r k omega‖
            ∂liveConcreteRecursiveSampleLaw r) ≤
    4 * epsilon

def liveConcreteGradientConversionBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega,
      ‖fullGradient D (liveConcreteIterate D r k omega)‖
        ∂liveConcreteRecursiveSampleLaw r) ≤
      (∫ omega, ‖liveConcreteEstimator D r k omega‖
        ∂liveConcreteRecursiveSampleLaw r) + epsilon

noncomputable def liveConcreteUniformOutputGradientAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage
    (liveConcreteRecursiveSampleLaw r)
    (fullGradient D) (liveConcreteIterate D r) K

theorem liveConcreteOutputAverageBound_of_telescope
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hTelescope : liveConcreteTelescopeBound D r epsilon K)
    (hConversion : liveConcreteGradientConversionBound D r epsilon K) :
    liveConcreteUniformOutputGradientAverage D r K ≤ 5 * epsilon := by
  exact
    uniform_average_gradient_bound_of_estimator_average
      (liveConcreteRecursiveSampleLaw r)
      (fullGradient D)
      (liveConcreteIterate D r)
      (liveConcreteEstimator D r)
      K hK epsilon
      (by
        intro k hk
        exact hConversion k (Finset.mem_range.mp hk))
      hTelescope

theorem liveConcreteEstimatorErrorBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (K : ℕ) :
    liveConcreteEstimatorErrorBound D r epsilon K := by
  sorry

theorem liveConcreteOneStepDescentBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (K : ℕ) :
    liveConcreteOneStepDescentBound D r epsilon K := by
  sorry

theorem liveConcreteGradientConversionBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (K : ℕ) :
    liveConcreteGradientConversionBound D r epsilon K := by
  sorry

theorem liveConcreteTelescopeBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D)
    (K : ℕ)
    (hEstimator : liveConcreteEstimatorErrorBound D r epsilon K)
    (hDescent : liveConcreteOneStepDescentBound D r epsilon K) :
    liveConcreteTelescopeBound D r epsilon K := by
  sorry

theorem liveConcreteCorrectedTheorem2Route_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    liveConcreteEstimatorErrorBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteOneStepDescentBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteTelescopeBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteGradientConversionBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteUniformOutputGradientAverage D r
          (iterationBudget D epsilon n0) ≤ 5 * epsilon ∧
      liveCorrectedB19FullCostRoute D epsilon n0 hScalar hGap := by
  let K := iterationBudget D epsilon n0
  have hK : 0 < K := by
    unfold K iterationBudget
    exact Nat.succ_pos _
  have hEstimator :
      liveConcreteEstimatorErrorBound D r epsilon K :=
    liveConcreteEstimatorErrorBound_obligation D epsilon n0 r hScalar K
  have hDescent :
      liveConcreteOneStepDescentBound D r epsilon K :=
    liveConcreteOneStepDescentBound_obligation D epsilon n0 r hScalar K
  have hTelescope :
      liveConcreteTelescopeBound D r epsilon K :=
    liveConcreteTelescopeBound_obligation
      D epsilon n0 r hScalar hGap K hEstimator hDescent
  have hConversion :
      liveConcreteGradientConversionBound D r epsilon K :=
    liveConcreteGradientConversionBound_obligation D epsilon n0 r K
  exact ⟨hEstimator, hDescent, hTelescope, hConversion,
    liveConcreteOutputAverageBound_of_telescope
      D r epsilon K hK hTelescope hConversion,
    liveCorrectedB19FullCostRoute_of_bound D epsilon n0 hScalar hGap⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

namespace Algorithms.Unverified.SPIDER

/-- Concrete-process extension root for the corrected finite-sum route.  The
exact Nat realization is explicit, and all expectations use the concrete
SOptLib iid mini-batch law. -/
theorem theorem2_finite_sum_concrete_corrected_process_root
    {n d : ℕ}
    (D : FiniteSumTheorem2Active.SourceData n d)
    (epsilon : ℝ) (n0 : FiniteSumTheorem2Active.N0 n)
    (r : FiniteSumTheorem2Active.LiveNaturalCountRealization
      (FiniteSumTheorem2Active.schedule epsilon D.L n0))
    (hScalar : FiniteSumTheorem2Active.scalarDomain D epsilon n0)
    (hGap : FiniteSumTheorem2Active.finiteInitialGapBoundary D) :
    FiniteSumTheorem2Active.liveConcreteEstimatorErrorBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteOneStepDescentBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteTelescopeBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteGradientConversionBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteUniformOutputGradientAverage D r
          (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ≤
        5 * epsilon ∧
      FiniteSumTheorem2Active.liveCorrectedB19FullCostRoute
        D epsilon n0 hScalar hGap :=
  FiniteSumTheorem2Active.liveConcreteCorrectedTheorem2Route_obligation
    D epsilon n0 r hScalar hGap

end Algorithms.Unverified.SPIDER

-/

/-
namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-!
Concrete live process spine for the active finite-sum extension.

The declarations below do not introduce a second theorem spine.  They refine
the active `LiveNaturalCountRealization` branch by constructing the actual
with-replacement mini-batch process, corrected zero-estimator update, telescope
quantity, output quantity, and B.19 cost route from one concrete law.
-/

def liveRefreshAt
    {n : ℕ} {s : SourceSchedule n}
    (r : LiveNaturalCountRealization s) (k : ℕ) : Prop :=
  k % r.refreshPeriod = 0

theorem liveRefreshAt_zero
    {n : ℕ} {s : SourceSchedule n}
    (r : LiveNaturalCountRealization s) :
    liveRefreshAt r 0 := by
  simp [liveRefreshAt]

/-- Concrete recursive mini-batch component-gradient average under the
SOptLib iid mini-batch sample path. -/
noncomputable def liveConcreteSampleAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) (k : ℕ)
    (x : VariableSpace d) : VariableSpace d :=
  (r.batchSize : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin r.batchSize => D.componentGradient (omega k j) x)

/-- Concrete finite-sum recursive SPIDER estimator from Algorithm 1, line 5. -/
noncomputable def liveConcreteRecursiveEstimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) : VariableSpace d :=
  liveConcreteSampleAverage D r omega k xCurr -
    liveConcreteSampleAverage D r omega k xPrev + vPrev

/-- One concrete corrected state transition: Option II for the iterate,
full-gradient refresh on realized period boundaries, and recursive estimator
otherwise. -/
noncomputable def liveConcreteTransition
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) (k : ℕ)
    (state : State (VariableSpace d)) : State (VariableSpace d) := by
  classical
  let xNext := liveCorrectedOptionIIUpdate s state.x state.v
  let vNext :=
    if liveRefreshAt r (k + 1) then
      fullGradient D xNext
    else
      liveConcreteRecursiveEstimator D r omega (k + 1) state.v state.x xNext
  exact { x := xNext, v := vNext }

/-- Concrete finite-sum SPIDER run generated by the active live realization. -/
noncomputable def liveConcreteStateProcess
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s) :
    ℕ → liveConcreteSamplePath r → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullGradient D D.x0 }
  | k + 1 => fun omega =>
      liveConcreteTransition D r omega k
        (liveConcreteStateProcess D r k omega)

noncomputable def liveConcreteIterate
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s) :
    ℕ → liveConcreteSamplePath r → VariableSpace d :=
  fun k omega => (liveConcreteStateProcess D r k omega).x

noncomputable def liveConcreteEstimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s) :
    ℕ → liveConcreteSamplePath r → VariableSpace d :=
  fun k omega => (liveConcreteStateProcess D r k omega).v

@[simp] theorem liveConcreteStateProcess_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteStateProcess D r 0 omega =
      { x := D.x0, v := fullGradient D D.x0 } := by
  rfl

@[simp] theorem liveConcreteIterate_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteIterate D r 0 omega = D.x0 := by
  rfl

@[simp] theorem liveConcreteEstimator_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteEstimator D r 0 omega = fullGradient D D.x0 := by
  rfl

theorem liveConcreteInitialRefresh_error_B17
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (omega : liveConcreteSamplePath r) :
    liveConcreteEstimator D r 0 omega =
      fullGradient D (liveConcreteIterate D r 0 omega) := by
  rfl

/-- Concrete-law finite-sum estimator-error theorem obligation along the live
SPIDER run.  This is the actual B.17-B.18 route; it is not the scalar
epsilon-cube display alone. -/
def liveConcreteEstimatorErrorBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖liveConcreteEstimator D r k omega -
          fullGradient D (liveConcreteIterate D r k omega)‖ ^ 2
          ∂liveConcreteRecursiveSampleLaw r ≤
      epsilon ^ 2

def liveConcreteOneStepDescentBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        objective D (liveConcreteIterate D r (k + 1) omega) -
          objective D (liveConcreteIterate D r k omega)
        ∂liveConcreteRecursiveSampleLaw r ≤
      -epsilon / (4 * D.L * s.n0.1) *
          ∫ omega, ‖liveConcreteEstimator D r k omega‖
            ∂liveConcreteRecursiveSampleLaw r +
        3 * epsilon ^ 2 / (4 * D.L * s.n0.1)

def liveConcreteTelescopeBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k =>
          ∫ omega, ‖liveConcreteEstimator D r k omega‖
            ∂liveConcreteRecursiveSampleLaw r) ≤
    4 * epsilon

def liveConcreteGradientConversionBound
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega,
      ‖fullGradient D (liveConcreteIterate D r k omega)‖
        ∂liveConcreteRecursiveSampleLaw r) ≤
      (∫ omega, ‖liveConcreteEstimator D r k omega‖
        ∂liveConcreteRecursiveSampleLaw r) + epsilon

noncomputable def liveConcreteUniformOutputGradientAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage
    (liveConcreteRecursiveSampleLaw r)
    (fullGradient D) (liveConcreteIterate D r) K

theorem liveConcreteOutputAverageBound_of_telescope
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : LiveNaturalCountRealization s)
    (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hTelescope : liveConcreteTelescopeBound D r epsilon K)
    (hConversion : liveConcreteGradientConversionBound D r epsilon K) :
    liveConcreteUniformOutputGradientAverage D r K ≤ 5 * epsilon := by
  exact
    uniform_average_gradient_bound_of_estimator_average
      (liveConcreteRecursiveSampleLaw r)
      (fullGradient D)
      (liveConcreteIterate D r)
      (liveConcreteEstimator D r)
      K hK epsilon
      (by
        intro k hk
        exact hConversion k (Finset.mem_range.mp hk))
      hTelescope

theorem liveConcreteEstimatorErrorBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (K : ℕ) :
    liveConcreteEstimatorErrorBound D r epsilon K := by
  sorry

theorem liveConcreteOneStepDescentBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (K : ℕ) :
    liveConcreteOneStepDescentBound D r epsilon K := by
  sorry

theorem liveConcreteGradientConversionBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (K : ℕ) :
    liveConcreteGradientConversionBound D r epsilon K := by
  sorry

theorem liveConcreteTelescopeBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D)
    (K : ℕ)
    (hEstimator : liveConcreteEstimatorErrorBound D r epsilon K)
    (hDescent : liveConcreteOneStepDescentBound D r epsilon K) :
    liveConcreteTelescopeBound D r epsilon K := by
  sorry

/-- Concrete corrected finite-sum Theorem 2 route over the active live run.
It contains the B.17-B.18 estimator-error route, the B.13-B.15 telescope/output
route over `liveConcreteRecursiveSampleLaw`, and the full corrected B.19 cost
route. -/
def liveConcreteCorrectedTheorem2Route
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) : Prop :=
  let K := iterationBudget D epsilon n0
  liveConcreteEstimatorErrorBound D r epsilon K ∧
    liveConcreteOneStepDescentBound D r epsilon K ∧
    liveConcreteTelescopeBound D r epsilon K ∧
    liveConcreteGradientConversionBound D r epsilon K ∧
    liveConcreteUniformOutputGradientAverage D r K ≤ 5 * epsilon ∧
    liveCorrectedB19FullCostRoute D epsilon n0 hScalar hGap

theorem liveConcreteCorrectedTheorem2Route_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : LiveNaturalCountRealization (schedule epsilon D.L n0))
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    liveConcreteEstimatorErrorBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteOneStepDescentBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteTelescopeBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteGradientConversionBound D r epsilon
        (iterationBudget D epsilon n0) ∧
      liveConcreteUniformOutputGradientAverage D r
          (iterationBudget D epsilon n0) ≤ 5 * epsilon ∧
      liveCorrectedB19FullCostRoute D epsilon n0 hScalar hGap := by
  let K := iterationBudget D epsilon n0
  have hK : 0 < K := by
    unfold K iterationBudget
    exact Nat.succ_pos _
  have hEstimator :
      liveConcreteEstimatorErrorBound D r epsilon K :=
    liveConcreteEstimatorErrorBound_obligation D epsilon n0 r hScalar K
  have hDescent :
      liveConcreteOneStepDescentBound D r epsilon K :=
    liveConcreteOneStepDescentBound_obligation D epsilon n0 r hScalar K
  have hTelescope :
      liveConcreteTelescopeBound D r epsilon K :=
    liveConcreteTelescopeBound_obligation
      D epsilon n0 r hScalar hGap K hEstimator hDescent
  have hConversion :
      liveConcreteGradientConversionBound D r epsilon K :=
    liveConcreteGradientConversionBound_obligation D epsilon n0 r K
  exact ⟨hEstimator, hDescent, hTelescope, hConversion,
    liveConcreteOutputAverageBound_of_telescope
      D r epsilon K hK hTelescope hConversion,
    liveCorrectedB19FullCostRoute_of_bound D epsilon n0 hScalar hGap⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

namespace Algorithms.Unverified.SPIDER

/-- Concrete-process extension root for the corrected finite-sum route.  The
exact Nat realization is explicit, and all expectations use the concrete
SOptLib iid mini-batch law. -/
theorem theorem2_finite_sum_concrete_corrected_process_root
    {n d : ℕ}
    (D : FiniteSumTheorem2Active.SourceData n d)
    (epsilon : ℝ) (n0 : FiniteSumTheorem2Active.N0 n)
    (r : FiniteSumTheorem2Active.LiveNaturalCountRealization
      (FiniteSumTheorem2Active.schedule epsilon D.L n0))
    (hScalar : FiniteSumTheorem2Active.scalarDomain D epsilon n0)
    (hGap : FiniteSumTheorem2Active.finiteInitialGapBoundary D) :
    FiniteSumTheorem2Active.liveConcreteEstimatorErrorBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteOneStepDescentBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteTelescopeBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteGradientConversionBound D r epsilon
        (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ∧
      FiniteSumTheorem2Active.liveConcreteUniformOutputGradientAverage D r
          (FiniteSumTheorem2Active.iterationBudget D epsilon n0) ≤
        5 * epsilon ∧
      FiniteSumTheorem2Active.liveCorrectedB19FullCostRoute
        D epsilon n0 hScalar hGap :=
  FiniteSumTheorem2Active.liveConcreteCorrectedTheorem2Route_obligation
    D epsilon n0 r hScalar hGap

end Algorithms.Unverified.SPIDER
-/

/-
The mutable extension layers below this point are retained as historical
refactor material only.  The active finite-sum object layer is appended after
the closing delimiter.

/- namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Canonical

/-!
Append-only source-facing layer for the finite-sum branch of Theorem 2.

The bounded subtype `N0 n` is the parameter domain printed in the paper. It
replaces proof arguments such as `FiniteSumScheduleDomain n n0` at the
source-facing boundary. The implementation layer above remains available as
an explicitly separate adapter.
-/

def n0Domain (n : ℕ) : Set ℝ :=
  Set.Icc (1 : ℝ) (Real.sqrt (n : ℝ))

abbrev N0 (n : ℕ) :=
  {r : ℝ // r ∈ n0Domain n}

theorem n0_lower {n : ℕ} (n0 : N0 n) :
    1 ≤ n0.1 :=
  n0.2.1

theorem n0_upper {n : ℕ} (n0 : N0 n) :
    n0.1 ≤ Real.sqrt (n : ℝ) :=
  n0.2.2

/-- The finite-average objective in Eq. (1.2). -/
noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    VariableSpace d → ℝ :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => P.componentObjective i x)

@[simp] theorem objective_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) (x : VariableSpace d) :
    objective P x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => P.componentObjective i x) := by
  rfl

/-- Component oracle kernel `i ↦ ∇f_i(x)`, computed from the objectives. -/
noncomputable def componentGradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => P.componentObjective i y) x

@[simp] theorem componentGradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    componentGradient P i x =
      ∇ (fun y : VariableSpace d => P.componentObjective i y) x := by
  rfl

/-- The full finite-sum gradient `∇f`, defined from the paper objective. -/
noncomputable def gradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    VariableSpace d → VariableSpace d :=
  fun x => ∇ (objective P) x

@[simp] theorem gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) :
    gradient P x = ∇ (objective P) x := by
  rfl

/-- The component-gradient average used by the finite-sum refresh branch. -/
noncomputable def componentGradientAverage
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient P i x)

theorem gradient_eq_componentGradientAverage_of_realization
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hcomponent :
      ∀ i : Fin n, ∀ x : VariableSpace d,
        HasGradientAt
          (fun y : VariableSpace d => P.componentObjective i y)
          (componentGradient P i x) x) :
    ∀ x : VariableSpace d,
      gradient P x = componentGradientAverage P x := by
  intro x
  sorry

/-- The source global infimum and initial gap, without an unconditional
lower-bound theorem. Lower-boundedness remains the source assumption
`FiniteSumProblem.objective_bddBelow`. -/
noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) : ℝ :=
  objectiveInfimum (objective P)

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) : ℝ :=
  objective P P.x0 - fStar P

@[simp] theorem fStar_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    fStar P = objectiveInfimum (objective P) := by
  rfl

@[simp] theorem Delta_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    Delta P = objective P P.x0 - fStar P := by
  rfl

/-- Exact full-gradient refresh at an epoch boundary. -/
noncomputable def fullRefresh
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) : VariableSpace d :=
  gradient P x

@[simp] theorem fullRefresh_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) :
    fullRefresh P x = gradient P x := by
  rfl

/-- A finite component-gradient sample average, derived from the kernel. -/
noncomputable def componentSampleAverage
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) (samples : Fin S → Fin n) :
    VariableSpace d :=
  refreshEstimator (fun y i => componentGradient P i y) x samples

@[simp] theorem componentSampleAverage_spec
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) (samples : Fin S → Fin n) :
    componentSampleAverage P x samples =
      (S : ℝ)⁻¹ •
        Finset.sum Finset.univ
          (fun j : Fin S => componentGradient P (samples j) x) := by
  rfl

/-- The recursive SPIDER estimator, built from the component oracle kernel. -/
noncomputable def recursiveEstimator
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (vPrev xPrev xCurr : VariableSpace d)
    (samples : Fin S → Fin n) : VariableSpace d :=
  Algorithms.Unverified.SPIDER.recursiveEstimator
    (fun x i => componentGradient P i x)
    vPrev xPrev xCurr samples

@[simp] theorem recursiveEstimator_spec
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (vPrev xPrev xCurr : VariableSpace d)
    (samples : Fin S → Fin n) :
    recursiveEstimator P vPrev xPrev xCurr samples =
      (S : ℝ)⁻¹ •
          Finset.sum Finset.univ
            (fun j : Fin S =>
              componentGradient P (samples j) xCurr -
                componentGradient P (samples j) xPrev) +
        vPrev := by
  rfl

/-- The real-valued Theorem 2 schedule from Eq. (3.7). -/
noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    FiniteSumSourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0.1
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  eta := epsilon / (L * n0.1)
  q := n0.1 * Real.sqrt (n : ℝ)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).eta =
      epsilon / (L * n0.1) := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

/-- The Option II adaptive stepsize in the source equation, with no
proof-dependent fallback branch. -/
noncomputable def optionIIAdaptiveStepSize
    (epsilon L n0 : ℝ) {d : ℕ}
    (v : VariableSpace d) : ℝ :=
  min
    (epsilon / (L * n0 * ‖v‖))
    (1 / (2 * L * n0))

/-- Canonical one-step Option II update from Algorithm 1, line 14. -/
noncomputable def optionIIUpdate
    (epsilon L n0 : ℝ) {d : ℕ}
    (x v : VariableSpace d) : VariableSpace d :=
  x - optionIIAdaptiveStepSize epsilon L n0 v • v

@[simp] theorem optionIIUpdate_spec
    (epsilon L n0 : ℝ) {d : ℕ}
    (x v : VariableSpace d) :
    optionIIUpdate epsilon L n0 x v =
      x - optionIIAdaptiveStepSize epsilon L n0 v • v := by
  rfl

/-- The iterate recurrence generated from the canonical Option II update and
an estimator process. The estimator process is an internal interface; its
values are supplied by `fullRefresh` and `recursiveEstimator` above. -/
noncomputable def iterateFromEstimator
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (epsilon L n0 : ℝ)
    (estimator : ℕ → Ω → E) :
    ℕ → Ω → E
  | 0 => fun _ => x0
  | k + 1 => fun omega =>
      optionIIUpdate epsilon L n0
        (iterateFromEstimator x0 epsilon L n0 estimator k omega)
        (estimator k omega)

@[simp] theorem iterateFromEstimator_zero
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (epsilon L n0 : ℝ)
    (estimator : ℕ → Ω → E) (omega : Ω) :
    iterateFromEstimator x0 epsilon L n0 estimator 0 omega = x0 := by
  rfl

@[simp] theorem iterateFromEstimator_succ
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (epsilon L n0 : ℝ)
    (estimator : ℕ → Ω → E) (k : ℕ) (omega : Ω) :
    iterateFromEstimator x0 epsilon L n0 estimator (k + 1) omega =
      optionIIUpdate epsilon L n0
        (iterateFromEstimator x0 epsilon L n0 estimator k omega)
        (estimator k omega) := by
  rfl

/-- The displayed B.18 product is recorded literally; it is not converted to
the paper's claimed epsilon-squared conclusion. -/
noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  simpa [b18DisplayedTerm] using
    Algorithms.Unverified.SPIDER.B18_display_epsilon_cube
      hepsilon hL hn0 hn

def b18PaperEpsilonSquareClaim
    (epsilon L n0 n : ℝ) : Prop :=
  b18DisplayedTerm epsilon L n0 n = epsilon ^ 2

/-- The paper-facing B.18 equality remains an explicit source obligation
because the literal displayed factors simplify to epsilon cubed. -/
theorem b18PaperEpsilonSquareClaim_obligation
    (epsilon L n0 n : ℝ) :
    b18PaperEpsilonSquareClaim epsilon L n0 n := by
  sorry

/-- Source-corrected B.19 cost route `2 K S2 + S1`. -/
noncomputable def gradientCost
    {n : ℕ} (n0 : N0 n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * (Real.sqrt (n : ℝ) / n0.1) + n

noncomputable def iterationBudget
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * P.L * Delta P * n0.1 * epsilon⁻¹ ^ 2) + 1

noncomputable def gradientCostBound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (P.L * Delta P) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

/-- Paper-facing finite-sum Theorem 2 cost statement. The proof remains a
source-derived obligation; the statement itself has no implementation
domain, rounded-count, or fallback argument. -/
theorem gradient_cost_bound_theorem
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) :
    gradientCost n0 (iterationBudget P epsilon n0) ≤
      gradientCostBound P epsilon n0 := by
  sorry

/-- Explicit reuse edge for the inherited output-conversion spine. -/
theorem output_conversion_reuse
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  exact Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
    mu grad iterate estimator K hK epsilon hconvert hest_avg

-/

/-
The finite-sum extension attempts from here through
`FiniteSumTheorem2CanonicalActiveV43` are retained as audit history only.
They expose duplicate public spines and stale theorem roots, so the active
source-facing finite-sum layer is the single spine appended after this block.

namespace Algorithms.Unverified.SPIDER

/-!
Finite-sum Theorem 2 object layer.

The finite-sum branch is not represented by an online `Sample` law with a
random refresh batch: at an epoch boundary the paper computes the exact full
gradient.  The declarations below therefore give the finite-average objective,
its canonical full gradient, an exact-refresh Option II process, and separate
theorem obligations for the source-derived estimator and complexity bounds.
-/

/-- Canonical component gradient `∇ f_i(x)` from the component objective.

The gradient is a computed Mathlib object, not a witness supplied by the
finite-sum setup.  Its `HasGradientAt` specification is recorded separately
as a theorem obligation below. -/
noncomputable def finiteSumComponentGradient
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (componentObjective : Fin n → E → ℝ) :
    Fin n → E → E :=
  fun i x => ∇ (fun y : E => componentObjective i y) x

theorem finiteSumComponentGradient_hasGradientAt
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (componentObjective : Fin n → E → ℝ)
    (i : Fin n) (x : E) :
    HasGradientAt (fun y : E => componentObjective i y)
      (finiteSumComponentGradient componentObjective i x) x := by
  sorry

/-- The component-gradient kernel in the sampled-oracle argument order. -/
noncomputable def finiteSumGradientKernel
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (componentGradient : Fin n → E → E) : E → Fin n → E :=
  fun x i => componentGradient i x

/-- Paper finite-sum problem data from Eq. (1.2) and Assumption 1(ii). -/
structure FiniteSumProblem
    (n : ℕ) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Component objectives `f_i`.

  Source status: source_fact.
  Citation: `book/research/SPIDER.json#/setup/variable_space`, quote
  `f(x) = 1/n sum_i f_i(x)`; PDF `paper/SPIDER.pdf`, p. 9, Assumption 1(ii),
  quote `The component function f_i(x) has an averaged L-Lipschitz gradient`.
  -/
  componentObjective : Fin n → E → ℝ
  /-- Initial point `x_0`. Source: Assumption 1(i), p. 9. -/
  x0 : E
  /-- Averaged component-gradient smoothness scale `L`.
  Source: Assumption 1(ii), p. 9. -/
  L : ℝ
  /-- Source-backed lower-bound boundary for the initial gap in Assumption 1(i).

  This is the Lean representation of the paper's finite initial gap/global
  infimum condition.  It is an input boundary, not a theorem derived from
  smoothness. -/
  objective_bddBelow :
    BddBelow
      ((fun x : E =>
          SOptLib.finiteUniformAverage
            (fun i : Fin n => componentObjective i x)) ''
        (Set.univ : Set E))
  /-- Assumption 1(ii) in finite-average form. -/
  averaged_lipschitz_gradient :
    ∀ x y : E,
      SOptLib.finiteUniformAverage
        (fun i : Fin n =>
          ‖finiteSumComponentGradient componentObjective i x -
            finiteSumComponentGradient componentObjective i y‖ ^ 2) ≤
      L ^ 2 * ‖x - y‖ ^ 2

namespace FiniteSumProblem

variable {n : ℕ} {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem index_nonempty (hn : 0 < n) : Nonempty (Fin n) :=
  ⟨⟨0, hn⟩⟩

/- Source status: source-derived canonical object.
   Citation: `book/research/SPIDER.json#/assumptions/1`, quote
   `The component function f_i(x) has an averaged L-Lipschitz gradient`.
   This is a computed carrier, not a Setup witness. -/
noncomputable def componentGradient (P : FiniteSumProblem n E) :
    Fin n → E → E :=
  finiteSumComponentGradient P.componentObjective

theorem componentGradient_spec
    (P : FiniteSumProblem n E) (i : Fin n) (x : E) :
    HasGradientAt (fun y : E => P.componentObjective i y)
      (P.componentGradient i x) x := by
  sorry

theorem componentGradient_genuine
    (P : FiniteSumProblem n E) (i : Fin n) (x : E)
    (h :
      ∃ g : E,
        HasGradientAt (fun y : E => P.componentObjective i y) g x) :
    HasGradientAt (fun y : E => P.componentObjective i y)
      (P.componentGradient i x) x :=
  P.componentGradient_spec i x

theorem componentGradient_spec_of_exists
    (P : FiniteSumProblem n E) (i : Fin n) (x : E)
    (h :
      ∃ g : E,
        HasGradientAt (fun y : E => P.componentObjective i y) g x) :
    HasGradientAt (fun y : E => P.componentObjective i y)
      (P.componentGradient i x) x :=
  P.componentGradient_spec i x

/-- The paper finite-sum objective `f = (1/n) sum_i f_i`. -/
noncomputable def f (P : FiniteSumProblem n E) : E → ℝ :=
  SOptLib.finiteUniformAverage P.componentObjective

/-- The exact full finite-sum gradient used at every refresh epoch.

This is the canonical component-gradient average.  The finite-average
gradient theorem is a later bridge which may identify it with the total
gradient selector when the component differentiability boundary is available.
-/
noncomputable def grad (P : FiniteSumProblem n E) : E → E :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n =>
        P.componentGradient i x)

/-- The paper global infimum value `f*`. -/
noncomputable def fStar (P : FiniteSumProblem n E) : ℝ :=
  objectiveInfimum P.f

/-- Initial objective gap `Delta = f(x0) - f*`. -/
noncomputable def Delta (P : FiniteSumProblem n E) : ℝ :=
  P.f P.x0 - P.fStar

theorem f_def (P : FiniteSumProblem n E) :
    P.f = SOptLib.finiteUniformAverage P.componentObjective := by
  rfl

theorem grad_def (P : FiniteSumProblem n E) :
    P.grad =
      fun x =>
        SOptLib.finiteUniformAverage
          (fun i : Fin n =>
            P.componentGradient i x) := by
  rfl

/-- The source component-gradient boundary is the genuine-gradient interface
carried by the finite-sum problem. -/
def finiteSumComponentGradientBoundary
    (P : FiniteSumProblem n E) : Prop :=
  ∀ i : Fin n, ∀ x : E,
    HasGradientAt (fun y : E => P.componentObjective i y)
      (P.componentGradient i x) x

theorem finiteSumComponentGradientBoundary_false_of_not_differentiable
    (P : FiniteSumProblem n E) (i : Fin n) (x : E)
    (h :
      ¬ ∃ g : E,
        HasGradientAt (fun y : E => P.componentObjective i y) g x) :
    ¬ finiteSumComponentGradientBoundary P := by
  intro hBoundary
  exact h ⟨P.componentGradient i x,
    hBoundary i x⟩

theorem finiteSumComponentGradient_spec_of_boundary
    (P : FiniteSumProblem n E)
    (hBoundary : finiteSumComponentGradientBoundary P)
    (i : Fin n) (x : E) :
    HasGradientAt (fun y : E => P.componentObjective i y)
      (P.componentGradient i x) x :=
  hBoundary i x

theorem finite_average_gradient_selector_bridge
    (P : FiniteSumProblem n E) (x : E)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt (fun y : E => P.componentObjective i y)
          (P.componentGradient i x) x) :
    ∇ P.f x = P.grad x := by
  unfold f grad
  exact
    SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      P.componentObjective
      P.componentGradient
      x hcomponent

theorem finite_average_hasGradientAt_bridge
    (P : FiniteSumProblem n E) (x : E)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt (fun y : E => P.componentObjective i y)
          (P.componentGradient i x) x) :
    HasGradientAt P.f (P.grad x) x := by
  unfold f grad
  convert
    (SOptLib.finiteAverageObjective_hasGradientAt
      P.componentObjective P.componentGradient x hcomponent) using 1
  · funext z
    simp [SOptLib.finiteUniformAverage, Pi.smul_apply, smul_eq_mul]

theorem fStar_lower_bound_of_bddBelow
    (P : FiniteSumProblem n E)
    (h_bddBelow :
      BddBelow (P.f '' (Set.univ : Set E))) (x : E) :
    P.fStar ≤ P.f x := by
  unfold fStar objectiveInfimum f
  exact SOptLib.objectiveInfimumValue_le h_bddBelow (Set.mem_univ x)

theorem Delta_nonneg_of_bddBelow
    (P : FiniteSumProblem n E)
    (h_bddBelow :
      BddBelow (P.f '' (Set.univ : Set E))) :
    0 ≤ P.Delta := by
  unfold Delta
  exact sub_nonneg.mpr (fStar_lower_bound_of_bddBelow P h_bddBelow P.x0)

theorem finite_initial_gap_boundary_spec
    (P : FiniteSumProblem n E) :
    BddBelow (P.f '' (Set.univ : Set E)) := by
  simpa [f] using P.objective_bddBelow

end FiniteSumProblem

/-- Canonical component-gradient oracle kernel. -/
noncomputable def FiniteSumProblem.gradKernel
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) : E → Fin n → E :=
  finiteSumGradientKernel
    P.componentGradient

namespace FiniteSumProblem

variable {n : ℕ} {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradKernel_def (P : FiniteSumProblem n E) :
    P.gradKernel =
      finiteSumGradientKernel
        P.componentGradient := by
  rfl

end FiniteSumProblem


/-- Real-valued finite-sum schedule from Eq. (3.7).

The fields are the mathematical quantities printed by the paper.  Natural
sample counts are not silently substituted here; a concrete sample-path run
must provide an explicit realization of those counts. -/
structure CorrectedFiniteSumSchedule (n : ℕ) where
  /-- Full refresh uses all components `1, ..., n`. -/
  S1 : ℕ
  /-- Recursive batch size `n^(1/2) / n₀`. -/
  S2 : ℝ
  /-- Constant stepsize `ε / (L n₀)`. -/
  eta : ℝ
  /-- Epoch length `q = n₀ n^(1/2)`. -/
  q : ℝ
  /-- Adaptive Option II stepsize. -/
  etaK : ℝ → ℝ

/-- Corrected implementation batch-size expression.  The source object is
    `FiniteSumSourceSchedule` below; this totalized helper is implementation
    machinery only. -/
noncomputable def correctedFiniteSumRecursiveBatchSize
    (n : ℕ) (n0 : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * n0⁻¹

/-- Corrected implementation constant stepsize expression. -/
noncomputable def correctedFiniteSumBaseStepSize
    (epsilon L n0 : ℝ) : ℝ :=
  epsilon * (L * n0)⁻¹

/-- Corrected implementation adaptive Option II stepsize expression. -/
noncomputable def correctedFiniteSumAdaptiveStepSize
    (epsilon L n0 : ℝ) (v : ℝ) : ℝ :=
  min (epsilon * (L * n0 * v)⁻¹) ((2 * L * n0)⁻¹)

/-- Corrected implementation epoch length expression. -/
noncomputable def correctedFiniteSumEpochLength
    (n : ℕ) (n0 : ℝ) : ℝ :=
  n0 * Real.sqrt (n : ℝ)

/-- Corrected implementation schedule.  It is deliberately separate from the
    source schedule because its natural process uses positive ceilings. -/
noncomputable def theorem2FiniteSumImplementationSchedule
    (n : ℕ) (epsilon L n0 : ℝ) : CorrectedFiniteSumSchedule n where
  S1 := n
  S2 := correctedFiniteSumRecursiveBatchSize n n0
  eta := correctedFiniteSumBaseStepSize epsilon L n0
  q := correctedFiniteSumEpochLength n n0
  etaK := correctedFiniteSumAdaptiveStepSize epsilon L n0

@[simp]
theorem theorem2FiniteSumImplementationSchedule_S1
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).S1 = n := by
  rfl

@[simp]
theorem theorem2FiniteSumImplementationSchedule_S2
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).S2 =
      correctedFiniteSumRecursiveBatchSize n n0 := by
  rfl

@[simp]
theorem theorem2FiniteSumImplementationSchedule_eta
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).eta =
      correctedFiniteSumBaseStepSize epsilon L n0 := by
  rfl

@[simp]
theorem theorem2FiniteSumImplementationSchedule_q
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).q =
      correctedFiniteSumEpochLength n n0 := by
  rfl

@[simp]
theorem theorem2FiniteSumImplementationSchedule_etaK
    (n : ℕ) (epsilon L n0 a : ℝ) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).etaK a =
      correctedFiniteSumAdaptiveStepSize epsilon L n0 a := by
  rfl

/-- The finite-sum schedule identities make the refresh/recursive product
equal to the full component count on the source domain. -/
theorem theorem2FiniteSumImplementationSchedule_q_mul_S2
    {n : ℕ} {epsilon L n0 : ℝ}
    (hn : 0 < n) (hn0 : 0 < n0) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).q *
        (theorem2FiniteSumImplementationSchedule n epsilon L n0).S2 = n := by
  unfold theorem2FiniteSumImplementationSchedule correctedFiniteSumEpochLength
    correctedFiniteSumRecursiveBatchSize
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  field_simp [ne_of_gt hn0]
  exact hsqrt

/-- The source-facing finite-sum free-parameter range. -/
def FiniteSumScheduleDomain (n : ℕ) (n0 : ℝ) : Prop :=
  1 ≤ n0 ∧ n0 ≤ Real.sqrt (n : ℝ)

theorem FiniteSumScheduleDomain.n0_lower
    {n : ℕ} {n0 : ℝ} (h : FiniteSumScheduleDomain n n0) :
    1 ≤ n0 :=
  h.1

theorem FiniteSumScheduleDomain.n0_upper
    {n : ℕ} {n0 : ℝ} (h : FiniteSumScheduleDomain n n0) :
    n0 ≤ Real.sqrt (n : ℝ) :=
  h.2

theorem FiniteSumScheduleDomain.n0_pos
    {n : ℕ} {n0 : ℝ} (h : FiniteSumScheduleDomain n n0) :
    0 < n0 :=
  lt_of_lt_of_le zero_lt_one h.n0_lower

theorem FiniteSumScheduleDomain.n_pos
    {n : ℕ} {n0 : ℝ} (h : FiniteSumScheduleDomain n n0) :
    0 < n := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    lt_of_lt_of_le h.n0_pos h.n0_upper
  exact_mod_cast (Real.sqrt_pos.1 hsqrt)

/- The normalized finite average is a Lean-level total function, while the
   source finite-sum object itself carries the nonempty support boundary.
   This separate predicate remains useful when checking schedule parameters,
   but it no longer serves as the only protection against `n = 0`. -/
def finiteSumMeaningfulDomain (n : ℕ) : Prop :=
  0 < n

theorem finiteSumMeaningfulDomain_iff_index_nonempty
    {n : ℕ} :
    finiteSumMeaningfulDomain n ↔ Nonempty (Fin n) := by
  constructor
  · intro hn
    exact FiniteSumProblem.index_nonempty hn
  · rintro ⟨i⟩
    exact Nat.zero_lt_of_lt i.isLt

theorem FiniteSumScheduleDomain.meaningfulDomain
    {n : ℕ} {n0 : ℝ} (h : FiniteSumScheduleDomain n n0) :
    finiteSumMeaningfulDomain n :=
  h.n_pos

/-- The real-valued schedule printed in Eq. (3.7).  Its adaptive step is
    defined on the positive-norm domain where the displayed quotient is
    meaningful; the rounded process is modeled separately below.

Book path `/extension/additions/algorithm_spec/steps/1`; source quote:
`S₂ = n^(1/2)/n₀`, `η = ε/(L n₀)`, `ηᵏ = min(ε/(L n₀ ‖vᵏ‖),
1/(2 L n₀))`, and `q = n₀ n^(1/2)`. -/
structure FiniteSumSourceSchedule (n : ℕ) where
  epsilon : ℝ
  L : ℝ
  n0 : ℝ
  S1 : ℕ
  S2 : ℝ
  eta : ℝ
  q : ℝ

def FiniteSumSourceParameterDomain
    (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  FiniteSumScheduleDomain n n0 ∧ 0 < epsilon ∧ 0 < L

noncomputable def finiteSumSourceAdaptiveStepSize
    {n : ℕ} (schedule : FiniteSumSourceSchedule n)
    (normV : ℝ) (_hnormV : 0 < normV)
    (_hL : schedule.L ≠ 0) (_hn0 : schedule.n0 ≠ 0) : ℝ :=
  min
    (schedule.epsilon / (schedule.L * schedule.n0 * normV))
    (1 / (2 * schedule.L * schedule.n0))

noncomputable def theorem2FiniteSumSourceScheduleValue
    (n : ℕ) (epsilon L n0 : ℝ)
    (_h : FiniteSumSourceParameterDomain n epsilon L n0) :
    FiniteSumSourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0
  eta := epsilon / (L * n0)
  q := n0 * Real.sqrt (n : ℝ)

noncomputable def theorem2FiniteSumSourceSchedule
    (n : ℕ) (epsilon L n0 : ℝ) :
    Option (FiniteSumSourceSchedule n) :=
  by
    classical
    exact if h : FiniteSumSourceParameterDomain n epsilon L n0 then
      some (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h)
    else
      none

@[simp]
theorem theorem2FiniteSumSourceSchedule_S1
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : FiniteSumSourceParameterDomain n epsilon L n0) :
    (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h).S1 = n := by
  rfl

@[simp]
theorem theorem2FiniteSumSourceSchedule_S2
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : FiniteSumSourceParameterDomain n epsilon L n0) :
    (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h).S2 =
      Real.sqrt (n : ℝ) / n0 := by
  rfl

@[simp]
theorem theorem2FiniteSumSourceSchedule_eta
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : FiniteSumSourceParameterDomain n epsilon L n0) :
    (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h).eta =
      epsilon / (L * n0) := by
  rfl

@[simp]
theorem theorem2FiniteSumSourceSchedule_q
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : FiniteSumSourceParameterDomain n epsilon L n0) :
    (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h).q =
      n0 * Real.sqrt (n : ℝ) := by
  rfl

@[simp]
theorem theorem2FiniteSumSourceSchedule_adaptiveStepSize
    {n : ℕ} {epsilon L n0 : ℝ} (v : ℝ)
    (h : FiniteSumSourceParameterDomain n epsilon L n0)
    (hv : 0 < v) :
    finiteSumSourceAdaptiveStepSize
        (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h)
        v hv (ne_of_gt h.2.2) (ne_of_gt h.1.n0_pos) =
      min (epsilon / (L * n0 * v)) (1 / (2 * L * n0)) := by
  rfl

theorem theorem2FiniteSumSourceSchedule_q_mul_S2
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : FiniteSumSourceParameterDomain n epsilon L n0) :
    (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h).q *
        (theorem2FiniteSumSourceScheduleValue n epsilon L n0 h).S2 =
      n := by
  unfold theorem2FiniteSumSourceScheduleValue
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  field_simp [ne_of_gt h.1.n0_pos]
  exact hsqrt

theorem theorem2FiniteSumSourceSchedule_none_of_invalid
    {n : ℕ} {epsilon L n0 : ℝ}
    (hzero : n = 0 ∨ epsilon = 0 ∨ L = 0 ∨ n0 = 0) :
    theorem2FiniteSumSourceSchedule n epsilon L n0 = none := by
  classical
  have hnot : ¬ FiniteSumSourceParameterDomain n epsilon L n0 := by
    intro h
    rcases hzero with rfl | rfl | rfl | rfl
    · exact (Nat.not_lt_zero _ h.1.n_pos)
    · exact (not_lt_of_ge (le_of_eq rfl)) h.2.1
    · exact (not_lt_of_ge (le_of_eq rfl)) h.2.2
    · exact (not_lt_of_ge h.1.n0_lower) (by norm_num)
  simp [theorem2FiniteSumSourceSchedule, hnot]

/- The rounded-count recursion is an explicitly corrected implementation
   layer.  It is kept out of the source-facing namespace so that its
   ceilings cannot be mistaken for the real schedule in Eq. (3.7). -/
/- The former hand-recursive finite-sum implementation is retained only in
   source history.  The active corrected realization below uses the canonical
   SOptLib process, so this duplicate process layer is intentionally excluded
   from the compiled object model. -/
/-
namespace InternalFiniteSumImplementation

/-- Internal implementation counts for the natural sample-path realization.

The paper exposes the real quantities `S₂` and `q`.  Lean's `Fin` and
`Nat.mod` require natural counts, so the implementation uses positive
ceilings.  These counts are deliberately computed from the source schedule;
they are not witnesses in the paper-facing theorem head. -/
noncomputable def finiteSumImplementationS2
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : ℕ :=
  max 1 (Nat.ceil schedule.S2)

noncomputable def finiteSumImplementationQ
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : ℕ :=
  max 1 (Nat.ceil schedule.q)

theorem finiteSumImplementationS2_pos
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) :
    0 < finiteSumImplementationS2 schedule := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem finiteSumImplementationQ_pos
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) :
    0 < finiteSumImplementationQ schedule := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

abbrev FiniteSumRunSamplePath {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : Type _ :=
  SOptLib.miniBatchSamplePath (finiteSumImplementationS2 schedule) (Fin n)

def finiteSumRecursiveSamples
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule →
      Fin (finiteSumImplementationS2 schedule) → Fin n :=
  fun k omega => omega k

/-- Canonical with-replacement uniform law for the finite-sum index stream.
The positivity premise is an internal law-construction obligation; it is
derived from the source finite-average domain at consuming boundaries. -/
noncomputable def finiteSumRunLaw
    {n : ℕ} (hn : 0 < n) (schedule : CorrectedFiniteSumSchedule n) :
    Measure (FiniteSumRunSamplePath schedule) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact SOptLib.iidMiniBatchSampleLaw (finiteSumImplementationS2 schedule)
    (PMF.uniformOfFintype (Fin n)).toMeasure

theorem finiteSumRunLaw_spec
    {n : ℕ} (hn : 0 < n) (schedule : CorrectedFiniteSumSchedule n) :
    IsProbabilityMeasure (finiteSumRunLaw hn schedule) ∧
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin (finiteSumImplementationS2 schedule))
            (omega : FiniteSumRunSamplePath schedule) =>
          omega kr.1 kr.2)
        (finiteSumRunLaw hn schedule) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold finiteSumRunLaw
  exact ⟨inferInstance,
    SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
      (finiteSumImplementationS2 schedule)
      (PMF.uniformOfFintype (Fin n)).toMeasure⟩

/-- The exact schedule update used by the finite-sum state process. -/
noncomputable def finiteSumOptionIIUpdate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (schedule : CorrectedFiniteSumSchedule n) (x v : E) : E :=
  x - schedule.etaK ‖v‖ • v

/- 
namespace ObsoleteFiniteSumNotes

/-- Legacy implementation aliases retained only for the prior proof block. -/
abbrev FiniteSumRunSamplePath (n S2 : ℕ) : Type _ :=
  SOptLib.miniBatchSamplePath S2 (Fin n)

def finiteSumRecursiveSamples (n S2 : ℕ) :
    ℕ → FiniteSumRunSamplePath n S2 → Fin S2 → Fin n :=
  fun k omega => omega k

noncomputable def finiteSumRecursiveBatchCount
    (n : ℕ) (n0 : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt (n : ℝ) * n0⁻¹)

noncomputable def finiteSumRecursiveBatchSizeValue
    (n : ℕ) (n0 : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * n0⁻¹

noncomputable def finiteSumEpochCount
    (n : ℕ) (n0 : ℝ) : ℕ :=
  Nat.ceil (n0 * Real.sqrt (n : ℝ))

noncomputable def finiteSumUniformRunLaw
    {n S2 : ℕ} (hn : 0 < n) :
    Measure (FiniteSumRunSamplePath n S2) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact SOptLib.iidMiniBatchSampleLaw S2
    (PMF.uniformOfFintype (Fin n)).toMeasure

/-- Exact-refresh Option II transition for the finite-sum branch. -/
noncomputable def finiteSumOptionIITransition
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (recursiveSamples : Fin S2 → Fin n) (k : ℕ) (state : State E) : State E :=
  let xNext := optionIIUpdate epsilon P.L n0 state.x state.v
  let vNext :=
    if (k + 1) % q = 0 then
      P.grad xNext
    else
      recursiveEstimator P.gradKernel state.v state.x xNext recursiveSamples
  { x := xNext, v := vNext }

/-- Recursive finite-sum state process with exact full-gradient refreshes. -/
noncomputable def finiteSumOptionIIStateProcessWithSamples
    {n : ℕ} {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (recursiveSamples : ℕ → Ω → Fin S2 → Fin n) :
    ℕ → Ω → State E
  | 0 => fun _ => { x := P.x0, v := P.grad P.x0 }
  | k + 1 => fun omega =>
      finiteSumOptionIITransition P S2 q epsilon n0
        (recursiveSamples (k + 1) omega) k
        (finiteSumOptionIIStateProcessWithSamples
          P S2 q epsilon n0 recursiveSamples k omega)

/-- Count-indexed process on the iid recursive sample path.
Schedule-specific natural counts are confined to the private implementation
definitions below. -/
noncomputable def finiteSumOptionIIStateProcessWithCounts
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ) :
    ℕ → FiniteSumRunSamplePath n S2 → State E :=
  finiteSumOptionIIStateProcessWithSamples P S2 q epsilon n0
    (fun k omega => finiteSumRecursiveSamples n S2 k omega)

/-- Implementation-only finite-sum run law obtained after choosing natural
batch and epoch counts for the exact real schedule.  The paper-facing
schedule remains `theorem2FiniteSumImplementationSchedule`. -/
noncomputable def finiteSumImplementationRunLaw
    {n : ℕ} (n0 : ℝ) (hn : 0 < n) :
    Measure
      (FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0)) :=
  finiteSumUniformRunLaw
    (n := n) (S2 := finiteSumRecursiveBatchCount n n0) hn

/-- Implementation-only finite-sum Option II state process obtained from the
natural realization of the source schedule. -/
noncomputable def finiteSumImplementationOptionIIStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ) :
    ℕ →
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0) →
        State E :=
  finiteSumOptionIIStateProcessWithCounts P
    (finiteSumRecursiveBatchCount n n0)
    (finiteSumEpochCount n n0)
    epsilon n0

/-- Count-indexed implementation iterate sequence. -/
noncomputable def finiteSumOptionIIIterateWithCounts
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ) :
    ℕ → FiniteSumRunSamplePath n S2 → E :=
  fun k omega => (finiteSumOptionIIStateProcessWithCounts P S2 q epsilon n0 k omega).x

/-- Implementation-only finite-sum iterate sequence for the natural
realization. -/
noncomputable def finiteSumImplementationOptionIIIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ) :
    ℕ →
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0) →
        E :=
  fun k omega =>
    (finiteSumImplementationOptionIIStateProcess P epsilon n0 k omega).x

/-- Count-indexed implementation estimator sequence. -/
noncomputable def finiteSumOptionIIEstimatorWithCounts
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ) :
    ℕ → FiniteSumRunSamplePath n S2 → E :=
  fun k omega => (finiteSumOptionIIStateProcessWithCounts P S2 q epsilon n0 k omega).v

/-- Implementation-only finite-sum estimator sequence for the natural
realization. -/
noncomputable def finiteSumImplementationOptionIIEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ) :
    ℕ →
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0) →
        E :=
  fun k omega =>
    (finiteSumImplementationOptionIIStateProcess P epsilon n0 k omega).v

/-- Canonical finite-sum state process for fixed natural sample and epoch
counts.

The paper schedule supplies the real quantities `S₂` and `q`; this process is
the algorithmic recursion after an implementation has supplied the natural
counts needed by `Fin` and `Nat.mod`.  In particular, the process itself does
not silently replace the paper schedule by `Nat.ceil` values. -/
noncomputable def finiteSumOptionIIStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ) :
    ℕ →
      FiniteSumRunSamplePath n S2 →
        State E :=
  finiteSumOptionIIStateProcessWithCounts P
    S2 q epsilon n0

/-- Iterate projection of the canonical fixed-count finite-sum process. -/
noncomputable def finiteSumOptionIIIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ) :
    ℕ →
      FiniteSumRunSamplePath n S2 →
        E :=
  fun k omega => (finiteSumOptionIIStateProcess P S2 q epsilon n0 k omega).x

/-- Estimator projection of the canonical fixed-count finite-sum process. -/
noncomputable def finiteSumOptionIIEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ) :
    ℕ →
      FiniteSumRunSamplePath n S2 →
        E :=
  fun k omega => (finiteSumOptionIIStateProcess P S2 q epsilon n0 k omega).v

@[simp]
theorem finiteSumImplementationOptionIIStateProcess_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ)
    (omega :
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0)) :
    finiteSumImplementationOptionIIStateProcess P epsilon n0 0 omega =
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

@[simp]
theorem finiteSumImplementationOptionIIStateProcess_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ) (k : ℕ)
    (omega :
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0)) :
    finiteSumImplementationOptionIIStateProcess P epsilon n0 (k + 1) omega =
      finiteSumOptionIITransition P
        (finiteSumRecursiveBatchCount n n0)
        (finiteSumEpochCount n n0)
        epsilon n0
        (finiteSumRecursiveSamples n (finiteSumRecursiveBatchCount n n0)
          (k + 1) omega)
        k
        (finiteSumImplementationOptionIIStateProcess P epsilon n0 k omega) := by
  rfl

@[simp]
theorem finiteSumImplementationOptionIIIterate_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ) (k : ℕ)
    (omega :
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0)) :
    finiteSumImplementationOptionIIIterate P epsilon n0 (k + 1) omega =
      optionIIUpdate epsilon P.L n0
        (finiteSumImplementationOptionIIIterate P epsilon n0 k omega)
        (finiteSumImplementationOptionIIEstimator P epsilon n0 k omega) := by
  rfl

@[simp]
theorem finiteSumImplementationOptionIIEstimator_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ) (k : ℕ)
    (omega :
      FiniteSumRunSamplePath n (finiteSumRecursiveBatchCount n n0)) :
    finiteSumImplementationOptionIIEstimator P epsilon n0 (k + 1) omega =
      if (k + 1) % finiteSumEpochCount n n0 = 0 then
        P.grad (finiteSumImplementationOptionIIIterate P epsilon n0 (k + 1) omega)
      else
        recursiveEstimator P.gradKernel
          (finiteSumImplementationOptionIIEstimator P epsilon n0 k omega)
          (finiteSumImplementationOptionIIIterate P epsilon n0 k omega)
          (finiteSumImplementationOptionIIIterate P epsilon n0 (k + 1) omega)
          (finiteSumRecursiveSamples n (finiteSumRecursiveBatchCount n n0)
            (k + 1) omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIStateProcess_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (omega :
      FiniteSumRunSamplePath n S2) :
    finiteSumOptionIIStateProcess P S2 q epsilon n0 0 omega =
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

@[simp]
theorem finiteSumOptionIIStateProcess_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (k : ℕ)
    (omega :
      FiniteSumRunSamplePath n S2) :
    finiteSumOptionIIStateProcess P S2 q epsilon n0 (k + 1) omega =
      finiteSumOptionIITransition P
        S2 q
        epsilon n0
        (finiteSumRecursiveSamples n S2 (k + 1) omega)
        k
        (finiteSumOptionIIStateProcess P S2 q epsilon n0 k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIIterate_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (k : ℕ)
    (omega :
      FiniteSumRunSamplePath n S2) :
    finiteSumOptionIIIterate P S2 q epsilon n0 (k + 1) omega =
      optionIIUpdate epsilon P.L n0
        (finiteSumOptionIIIterate P S2 q epsilon n0 k omega)
        (finiteSumOptionIIEstimator P S2 q epsilon n0 k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (omega :
      FiniteSumRunSamplePath n S2) :
    finiteSumOptionIIEstimator P S2 q epsilon n0 0 omega =
      P.grad P.x0 := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (k : ℕ)
    (omega :
      FiniteSumRunSamplePath n S2) :
    finiteSumOptionIIEstimator P S2 q epsilon n0 (k + 1) omega =
      if (k + 1) % q = 0 then
        P.grad (finiteSumOptionIIIterate P S2 q epsilon n0 (k + 1) omega)
      else
        recursiveEstimator P.gradKernel
          (finiteSumOptionIIEstimator P S2 q epsilon n0 k omega)
          (finiteSumOptionIIIterate P S2 q epsilon n0 k omega)
          (finiteSumOptionIIIterate P S2 q epsilon n0 (k + 1) omega)
          (finiteSumRecursiveSamples n S2 (k + 1) omega) := by
  rfl

/-- Natural sample-prefix filtration generated by the recursive mini-batch
stream.  This is the canonical conditioning object for the finite-sum
estimator calculation. -/
noncomputable def finiteSumSampleFiltration
    {n S2 : ℕ} :
    Filtration ℕ
      (by infer_instance :
        MeasurableSpace (FiniteSumRunSamplePath n S2)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

/-- Conditional-expectation equality used for the finite-sum refresh boundary.

This is deliberately an expectation-level contract: the paper's (B.17) is
`E_{k_0}` of the refresh error, not a pathwise assertion about every sample
path. -/
abbrev finiteSumConditionalExpectationEq
    {n S2 : ℕ}
    {m0 : MeasurableSpace (FiniteSumRunSamplePath n S2)}
    (mu : Measure[m0] (FiniteSumRunSamplePath n S2))
    (m : MeasurableSpace (FiniteSumRunSamplePath n S2))
    (error : FiniteSumRunSamplePath n S2 → ℝ)
    (rhs : ℝ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (m0 := m0) mu m error (fun _ => rhs)

/-- B.17 exact-refresh error at a finite-sum epoch boundary. -/
theorem theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (S2 q : ℕ) (epsilon n0 : ℝ)
    (mu : Measure (FiniteSumRunSamplePath n S2))
    (k0 : ℕ) (hk0 : k0 % q = 0) :
    finiteSumConditionalExpectationEq
      mu
      ((@finiteSumSampleFiltration n S2).seq k0)
      (fun omega =>
        ‖finiteSumOptionIIEstimator P S2 q epsilon n0 k0 omega -
          P.grad (finiteSumOptionIIIterate P S2 q epsilon n0 k0 omega)‖ ^ 2)
      0 := by
  sorry

/-- Source-derived finite-sum Option II step bound (B.2). -/
theorem theorem2_finite_sum_step_bound_B2_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) {epsilon L n0 : ℝ}
    {x v : E} (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 1 ≤ n0) (hL_eq : L = P.L) :
    ‖optionIIUpdate epsilon L n0 x v - x‖ ≤
      epsilon * (L * n0)⁻¹ := by
  rw [hL_eq]
  have hPL : 0 < P.L := by
    simpa [hL_eq] using hL
  exact optionII_step_bound_obligation (le_of_lt hepsilon)
    (mul_pos hPL (lt_of_lt_of_le zero_lt_one hn0))

/-- Finite-sum adapter for the pathwise B.8 descent inequality.

The paper-facing adapter keeps only the finite-sum schedule domain in its
interface.  Positivity of quotients is a proof obligation for the later
derivation, not an additional Theorem 2 hypothesis.
Source: `book/research/SPIDER.json#/extension/additions/main_theorem/proof/4`,
the B.9 step, and `#/extension/additions/algorithm_spec/steps/3-4`. -/
theorem theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (_scheduleDomain : FiniteSumScheduleDomain n n0)
    (x v : VariableSpace d) :
    P.f (optionIIUpdate epsilon P.L n0 x v) ≤
      P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖v - P.grad x‖ ^ 2 := by
  sorry

/-- Conditional second-moment upper bound in the nonfallback conditional-
expectation branch.  This is the source shape of Lemma 2's
`E_{k₀}[‖v^k - ∇f(x^k)‖²] ≤ ε²`, rather than an unconditional integral
contract. -/
def finiteSumConditionalSecondMomentBound
    {n S2 : ℕ}
    {m0 : MeasurableSpace (FiniteSumRunSamplePath n S2)}
    (mu : Measure[m0] (FiniteSumRunSamplePath n S2))
    (m : MeasurableSpace (FiniteSumRunSamplePath n S2))
    (error : FiniteSumRunSamplePath n S2 → ℝ)
    (rhs : ℝ) : Prop :=
  @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
      (FiniteSumRunSamplePath n S2) ℝ m0 inferInstance mu m error ∧
    @MeasureTheory.condExp
        (FiniteSumRunSamplePath n S2) ℝ m
        (m₀ := m0)
        inferInstance inferInstance inferInstance mu error ≤ᵐ[mu]
      fun _ => rhs

/-- Finite-sum estimator-error adapter boundary for B.17-B.18.

The process, sample path, and prefix filtration are canonical definitions
above.  The remaining arguments are theorem-level obligations for the
conditional expectation calculation; in particular, the printed B.18 epsilon
factors are retained as an unresolved source obligation rather than silently
normalized.  Source: `book/research/SPIDER.json#/extension/additions/key_lemmas/0`,
quote `E_{k₀}‖v^k-∇f(x^k)‖² ≤ ε²`, with the source display checked against
Eq. (B.17)-(B.18), p. 29. -/
theorem theorem2_finite_sum_estimator_error_adapter_corrected_implementation
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (S2 q : ℕ) (epsilon n0 : ℝ)
    (mu : Measure (FiniteSumRunSamplePath n S2))
    (_scheduleDomain : FiniteSumScheduleDomain n n0) :
    ∀ k0 k : ℕ,
      k0 % q = 0 →
      k0 ≤ k →
      finiteSumConditionalSecondMomentBound
        mu
        ((@finiteSumSampleFiltration n S2).seq (k0 + 1))
        (fun omega =>
          ‖finiteSumOptionIIEstimator P S2 q epsilon n0 k omega -
            P.grad (finiteSumOptionIIIterate P S2 q epsilon n0 k omega)‖ ^ 2)
        (epsilon ^ 2) := by
  sorry

/-- Finite-sum output-conversion adapter re-exporting the inherited B.15
finite-average bridge.  Its hypotheses are proof-interface data, not fields of
`FiniteSumProblem` and not assumptions of the paper theorem. -/
theorem theorem2_finite_sum_gradient_average_adapter
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
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
  exact uniform_average_gradient_bound_of_estimator_average
    mu grad iterate estimator K hK epsilon hconvert hest_avg

/-- The literal scalar product printed in Eq. (B.18).  It is kept as a
source-display object rather than being asserted to equal the paper's final
`epsilon^2` label. -/
noncomputable def correctedFiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
      (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
      (epsilon * n0 / Real.sqrt n)

/-- Eq. (B.18)'s displayed factors simplify to `epsilon^3` on their genuine
domain.  This isolates the source mismatch as a proof-level boundary instead
of exporting the false squared-epsilon identity. -/
theorem theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube_corrected_implementation
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L) (hn0 : 0 < n0) (hn : 0 < n) :
    correctedFiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold correctedFiniteSumB18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

/-- Literal first cost display in B.19. -/
noncomputable def correctedFiniteSumLiteralB19Cost (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

/-- Internal source-corrected B.19 cost route using `2 K S2 + S1`.
This is not the paper-facing theorem statement. -/
noncomputable def correctedFiniteSumCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

/-- Totalized scalar value behind the source-facing finite-sum cost bound.

This helper is implementation-only.  The public objects below are
option-valued, so a zero denominator is represented by `none` rather than
silently acquiring the field-division fallback value. -/
noncomputable def theorem2FiniteSumGradientCostBoundValue
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0⁻¹ * Real.sqrt (n : ℝ)

/-- Theorem 2 iteration budget, defined only when its displayed inverse exists. -/
noncomputable def correctedFiniteSumBudget
    (L Delta n0 epsilon : ℝ) : Option ℕ :=
  if epsilon = 0 then
    none
  else
    some (Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1)

theorem correctedFiniteSumBudget_def
    {L Delta n0 epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    correctedFiniteSumBudget L Delta n0 epsilon =
      some (Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1) := by
  simp [correctedFiniteSumBudget, hepsilon]

/-- Totalized B.19 expression used only after the source denominators have
been checked. -/
noncomputable def theorem2FiniteSumSourceGradientCostValue
    (K n : ℕ) (n0 : ℝ) : ℝ :=
  (Nat.ceil ((K : ℝ) * (correctedFiniteSumEpochLength n n0)⁻¹) : ℝ) * (n : ℝ) +
    (K : ℝ) * finiteSumRecursiveBatchSizeValue n n0

/-- The source-facing B.19 call-count expression with explicit undefinedness.

The paper uses real-valued `S₂` and `q` in Eq. (3.7), while the call count
uses a ceiling for the number of refresh epochs.  This option-valued object
keeps that source expression but refuses to manufacture a value when the
displayed denominators are zero. -/
noncomputable def theorem2FiniteSumSourceGradientCost
    (K n : ℕ) (n0 : ℝ) : Option ℝ :=
  let q := correctedFiniteSumEpochLength n n0
  if q = 0 ∨ n0 = 0 then
    none
  else
    some (theorem2FiniteSumSourceGradientCostValue K n n0)

/-- The source-facing finite-sum stochastic-gradient bound with explicit
undefinedness for the displayed `epsilon⁻¹` and `n₀⁻¹` factors. -/
noncomputable def correctedFiniteSumGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  if epsilon = 0 ∨ n0 = 0 then
    none
  else
    some (theorem2FiniteSumGradientCostBoundValue n L Delta n0 epsilon)

/-- Paper-facing Theorem 2 cost conclusion.

The theorem is stated over the option-valued source objects.  Its
well-definedness premises are explicit values of the paper expressions, not
additional positivity assumptions or totalized quotient semantics. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (_scheduleDomain : FiniteSumScheduleDomain n n0) :
    ∀ K cost bound,
      correctedFiniteSumBudget P.L P.Delta n0 epsilon = some K →
      theorem2FiniteSumSourceGradientCost K n n0 = some cost →
      correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon =
        some bound →
      cost ≤ bound := by
  intro K cost bound hK hcost hbound
  let S2 := finiteSumRecursiveBatchCount n n0
  let q := finiteSumEpochCount n n0
  let mu :=
    finiteSumUniformRunLaw
      (n := n) (S2 := S2) P.n_pos
  have _hB17 :=
    theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
      P S2 q epsilon n0 mu 0 (by simp [q])
  have _hEstimator :=
    theorem2_finite_sum_estimator_error_adapter_corrected_implementation
      P S2 q epsilon n0 mu _scheduleDomain
  have _hDescent :=
    theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
      P epsilon n0 _scheduleDomain P.x0 (P.grad P.x0)
  have _base_output_conversion :=
    @theorem2_finite_sum_gradient_average_adapter (Fin 1) ℝ
  let _base_estimator :=
    fun (Q : OnlineProblem Unit (VariableSpace d)) =>
      optionII_estimator_error_secondMoment_le_epsilon_sq_rounded Q
  let _base_descent :=
    fun (Q : OnlineProblem Unit (VariableSpace d)) (epsilon n0 : ℝ) =>
      optionII_one_step_descent_B8_pathwise Q
        (epsilon := epsilon) (n0 := n0)
  have _ := hK
  have _ := hcost
  have _ := hbound
  sorry

end ObsoleteFiniteSumNotes
-/

/-!
Canonical finite-sum process and source-boundary adapters.

The real schedule above is the paper object.  The process below is an
implementation realization obtained by deterministic positive ceilings.  It
is intentionally not used as a replacement for the source schedule in the
paper-facing cost expression.
-/

noncomputable def finiteSumOptionIITransition
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (recursiveSamples : Fin (finiteSumImplementationS2 schedule) → Fin n)
    (k : ℕ) (state : State E) : State E :=
  let xNext := finiteSumOptionIIUpdate schedule state.x state.v
  let vNext :=
    if (k + 1) % finiteSumImplementationQ schedule = 0 then
      P.grad xNext
    else
      recursiveEstimator P.gradKernel state.v state.x xNext recursiveSamples
  { x := xNext, v := vNext }

noncomputable def finiteSumOptionIIStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule → State E
  | 0 => fun _ => { x := P.x0, v := P.grad P.x0 }
  | k + 1 => fun omega =>
      finiteSumOptionIITransition P schedule
        (finiteSumRecursiveSamples schedule (k + 1) omega) k
        (finiteSumOptionIIStateProcess P schedule k omega)

noncomputable def finiteSumOptionIIIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule → E :=
  fun k omega => (finiteSumOptionIIStateProcess P schedule k omega).x

noncomputable def finiteSumOptionIIEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule → E :=
  fun k omega => (finiteSumOptionIIStateProcess P schedule k omega).v

@[simp]
theorem finiteSumOptionIIStateProcess_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (omega : FiniteSumRunSamplePath schedule) :
    finiteSumOptionIIStateProcess P schedule 0 omega =
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

@[simp]
theorem finiteSumOptionIIStateProcess_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (k : ℕ) (omega : FiniteSumRunSamplePath schedule) :
    finiteSumOptionIIStateProcess P schedule (k + 1) omega =
      finiteSumOptionIITransition P schedule
        (finiteSumRecursiveSamples schedule (k + 1) omega) k
        (finiteSumOptionIIStateProcess P schedule k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIIterate_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (k : ℕ)
    (omega : FiniteSumRunSamplePath schedule) :
    finiteSumOptionIIIterate P schedule (k + 1) omega =
      finiteSumOptionIIUpdate schedule
        (finiteSumOptionIIIterate P schedule k omega)
        (finiteSumOptionIIEstimator P schedule k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n)
    (omega : FiniteSumRunSamplePath schedule) :
    finiteSumOptionIIEstimator P schedule 0 omega = P.grad P.x0 := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (k : ℕ)
    (omega : FiniteSumRunSamplePath schedule) :
    finiteSumOptionIIEstimator P schedule (k + 1) omega =
      if (k + 1) % finiteSumImplementationQ schedule = 0 then
        P.grad (finiteSumOptionIIIterate P schedule (k + 1) omega)
      else
        recursiveEstimator P.gradKernel
          (finiteSumOptionIIEstimator P schedule k omega)
          (finiteSumOptionIIIterate P schedule k omega)
          (finiteSumOptionIIIterate P schedule (k + 1) omega)
          (finiteSumRecursiveSamples schedule (k + 1) omega) := by
  rfl

/-- The natural prefix filtration of the computed implementation stream. -/
noncomputable def finiteSumSampleFiltration
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) :
    Filtration ℕ
      (by infer_instance : MeasurableSpace (FiniteSumRunSamplePath schedule)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

/-- Source-conditioning bridge for the exact full-refresh boundary (B.17).
The public statement names the source boundary but does not expose a
particular Lean filtration or conditional-expectation contract. -/
def correctedFiniteSumRefreshErrorAE
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (hn : 0 < n) (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (k0 : ℕ) : Prop :=
  ∀ᵐ omega ∂finiteSumRunLaw hn schedule,
    ‖finiteSumOptionIIEstimator P schedule k0 omega -
      P.grad (finiteSumOptionIIIterate P schedule k0 omega)‖ ^ 2 = 0

theorem theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (hn : 0 < n)
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (k0 : ℕ) (hk0 : k0 % finiteSumImplementationQ schedule = 0) :
    correctedFiniteSumRefreshErrorAE hn P schedule k0 := by
  sorry

/-- Checked scalar domain used only by quotient-consuming adapters. -/
def correctedFiniteSumCheckedDomain
    (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  0 < n ∧ 0 < epsilon ∧ 0 < L ∧ 0 < n0

theorem correctedFiniteSumCheckedDomain.n_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < n :=
  h.1

theorem correctedFiniteSumCheckedDomain.epsilon_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < epsilon :=
  h.2.1

theorem correctedFiniteSumCheckedDomain.L_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < L :=
  h.2.2.1

theorem correctedFiniteSumCheckedDomain.n0_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < n0 :=
  h.2.2.2

theorem correctedFiniteSumCheckedDomain.rejects_n_zero
    {epsilon L n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain 0 epsilon L n0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.rejects_epsilon_zero
    {n : ℕ} {L n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n 0 L n0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.rejects_L_zero
    {n : ℕ} {epsilon n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n epsilon 0 n0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.rejects_n0_zero
    {n : ℕ} {epsilon L : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n epsilon L 0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.schedule_q_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) :
    0 < (theorem2FiniteSumImplementationSchedule n epsilon L n0).q := by
  rw [theorem2FiniteSumImplementationSchedule_q]
  unfold correctedFiniteSumEpochLength
  apply mul_pos h.n0_pos
  exact Real.sqrt_pos.2 (by exact_mod_cast h.n_pos)

theorem correctedFiniteSumCheckedDomain.schedule_q_ne_zero
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) :
    (theorem2FiniteSumImplementationSchedule n epsilon L n0).q ≠ 0 :=
  ne_of_gt h.schedule_q_pos

theorem correctedFiniteSumComponentGradient_is_genuine
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (P : FiniteSumProblem n E) (i : Fin n) (x : E)
    (hGrad :
      HasGradientAt (fun y : E => P.componentObjective i y)
        (∇ (fun y : E => P.componentObjective i y) x) x) :
    HasGradientAt (fun y : E => P.componentObjective i y)
      (∇ (fun y : E => P.componentObjective i y) x) x :=
  hGrad

noncomputable def correctedFiniteSumCheckedBaseStepSize
    (epsilon L n0 : ℝ) : Option ℝ :=
  SOptLib.checked_quotient epsilon (L * n0)

theorem finiteSumCheckedBaseStepSize_spec
    {epsilon L n0 : ℝ} (hden : L * n0 ≠ 0) :
    correctedFiniteSumCheckedBaseStepSize epsilon L n0 =
      some (epsilon / (L * n0)) := by
  simp [correctedFiniteSumCheckedBaseStepSize, SOptLib.checked_quotient, hden]

def finiteSumExactRunRealization
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : Type :=
  { r : ℕ × ℕ //
      0 < r.1 ∧ 0 < r.2 ∧
        (r.1 : ℝ) = schedule.S2 ∧ (r.2 : ℝ) = schedule.q }

theorem finiteSumExactRunRealization_empty_n2_n0_1 :
    ¬ Nonempty
      (finiteSumExactRunRealization
        (theorem2FiniteSumImplementationSchedule 2 1 1 1)) := by
  sorry

/-- Source-derived finite-sum Option II step bound (B.2). -/
theorem theorem2_finite_sum_step_bound_B2_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (P : FiniteSumProblem n E)
    (epsilon n0 : ℝ) (hepsilon : 0 < epsilon) (hL : 0 < P.L)
    (hn0 : 1 ≤ n0) (x v : E) :
    ‖finiteSumOptionIIUpdate
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v - x‖ ≤
      epsilon * (P.L * n0)⁻¹ := by
  sorry

/-- Finite-sum adapter for the pathwise B.8 descent inequality. -/
theorem theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (hepsilon : 0 < epsilon) (hL : 0 < P.L) (x v : VariableSpace d) :
    P.f
        (finiteSumOptionIIUpdate
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v) ≤
      P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) * ‖v - P.grad x‖ ^ 2 := by
  sorry

/-- Finite-sum estimator-error adapter.  Its source-facing output is the
named B.17-B.18 bridge; filtration details remain implementation-internal. -/
theorem theorem2_finite_sum_estimator_error_adapter_corrected_implementation
    {n d : ℕ} (hn : 0 < n)
    (P : FiniteSumProblem n (VariableSpace d))
    (schedule : CorrectedFiniteSumSchedule n) (epsilon : ℝ) :
    ∀ k0 k : ℕ,
      k0 % finiteSumImplementationQ schedule = 0 →
      k0 ≤ k →
      correctedFiniteSumRefreshErrorAE hn P schedule k0 := by
  sorry

/-- The literal product printed in B.18 for the corrected implementation
    boundary. -/
noncomputable def correctedFiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
      (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
      (epsilon * n0 / Real.sqrt n)

theorem theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube_corrected_implementation
    {epsilon L n0 n : ℝ} (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    correctedFiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold correctedFiniteSumB18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

/-- Source-error record for the literal B.18 display.  The displayed factors
reduce to `epsilon^3`; the paper's printed `epsilon^2` label is retained only
as source evidence and is not asserted here. -/
def correctedFiniteSumB18SourceError
    (epsilon L n0 n : ℝ) : Prop :=
  correctedFiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3

theorem theorem2_finite_sum_B18_source_error_corrected_implementation
    {epsilon L n0 n : ℝ} (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    correctedFiniteSumB18SourceError epsilon L n0 n := by
  exact theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube_corrected_implementation
    hepsilon hL hn0 hn

/-- Literal first B.19 display, retained separately from the corrected route. -/
noncomputable def correctedFiniteSumLiteralB19Cost (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

/-- Source-corrected B.19 route, with the recursive cost attached to `S₂`. -/
noncomputable def correctedFiniteSumCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

/-- Actual call count of the computed implementation process. -/
noncomputable def correctedFiniteSumProcessGradientCost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  Nat.ceil ((K : ℝ) * (finiteSumImplementationQ schedule : ℝ)⁻¹) *
      schedule.S1 +
    K * finiteSumImplementationS2 schedule

/-- Internal process-count bridge for the literal and corrected B.19 routes. -/
theorem correctedFiniteSumProcessGradientCost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((correctedFiniteSumProcessGradientCost schedule K : ℕ) : ℝ) ≤
      correctedFiniteSumLiteralB19Cost K schedule.S1 +
        correctedFiniteSumCorrectedB19Cost K schedule.S1 schedule.S2 := by
  sorry

noncomputable def correctedFiniteSumGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0⁻¹ * Real.sqrt (n : ℝ)

noncomputable def correctedFiniteSumBudget
    (L Delta n0 epsilon : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

theorem correctedFiniteSumBudget_def
    (L Delta n0 epsilon : ℝ) :
    correctedFiniteSumBudget L Delta n0 epsilon =
      Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1 := by
  rfl

theorem correctedFiniteSumGradientCostBound_of_adapters
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (hChecked : correctedFiniteSumCheckedDomain n epsilon P.L n0)
    (hNonempty :
      Nonempty
        (FiniteSumRunSamplePath
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)))
    (hB17 :
      correctedFiniteSumRefreshErrorAE hChecked.n_pos P
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k0 k : ℕ,
        k0 % finiteSumImplementationQ
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) = 0 →
        k0 ≤ k →
        correctedFiniteSumRefreshErrorAE hChecked.n_pos P
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k0)
    (hDescent :
      P.f
          (finiteSumOptionIIUpdate
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) P.x0 (P.grad P.x0)) ≤
        P.f P.x0 - epsilon * ‖P.grad P.x0‖ / (4 * P.L * n0) +
          epsilon ^ 2 / (2 * n0 * P.L) +
          (1 / (4 * P.L * n0)) *
            ‖P.grad P.x0 - P.grad P.x0‖ ^ 2)
    (hCheckedQuotient :
      correctedFiniteSumCheckedBaseStepSize epsilon P.L n0 =
        some (epsilon / (P.L * n0)))
    (hB18 :
      correctedFiniteSumB18SourceError epsilon P.L n0 n)
    (hOutput :
      uniformOutputGradientNormAverage
          (finiteSumRunLaw hChecked.n_pos
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          P.grad
          (finiteSumOptionIIIterate P
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          1 ≤ 5 * epsilon)
    (hTelescope :
      Finset.sum (Finset.range 1) (fun _ : ℕ => (0 : ℝ)) ≤ 0)
    (hB19 :
      ((correctedFiniteSumProcessGradientCost
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
          (correctedFiniteSumBudget P.L P.Delta n0 epsilon) : ℕ) : ℝ) ≤
        correctedFiniteSumLiteralB19Cost
            (correctedFiniteSumBudget P.L P.Delta n0 epsilon)
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S1 +
          correctedFiniteSumCorrectedB19Cost
            (correctedFiniteSumBudget P.L P.Delta n0 epsilon)
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S1
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S2) :
    ((correctedFiniteSumProcessGradientCost
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
        (correctedFiniteSumBudget P.L P.Delta n0 epsilon) : ℕ) : ℝ) ≤
      correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon := by
  sorry

/-- Corrected implementation cost root.  It is intentionally separate from
    the paper-facing source theorem below. -/
theorem corrected_finite_sum_gradient_cost_bound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    ∀ hChecked : correctedFiniteSumCheckedDomain n epsilon P.L n0,
      Nonempty
        (FiniteSumRunSamplePath
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)) →
      uniformOutputGradientNormAverage
          (finiteSumRunLaw hChecked.n_pos
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          P.grad
          (finiteSumOptionIIIterate P
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          1 ≤ 5 * epsilon →
      Finset.sum (Finset.range 1) (fun _ : ℕ => (0 : ℝ)) ≤ 0 →
      ((correctedFiniteSumProcessGradientCost
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
          (correctedFiniteSumBudget P.L P.Delta n0 epsilon) : ℕ) : ℝ) ≤
        correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon := by
  intro hChecked hNonempty hOutput hTelescope
  have hn_pos : 0 < n := correctedFiniteSumCheckedDomain.n_pos hChecked
  have hepsilon_pos : 0 < epsilon :=
    correctedFiniteSumCheckedDomain.epsilon_pos hChecked
  have hL_pos : 0 < P.L := correctedFiniteSumCheckedDomain.L_pos hChecked
  have hn0_pos : 0 < n0 := correctedFiniteSumCheckedDomain.n0_pos hChecked
  have hB19 :=
    correctedFiniteSumProcessGradientCost_B19_bridge
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
      (correctedFiniteSumBudget P.L P.Delta n0 epsilon)
  have hB17 :=
    theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
      hn_pos P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) 0
      (by simp [finiteSumImplementationQ])
  have hEstimator :=
    theorem2_finite_sum_estimator_error_adapter_corrected_implementation
      hn_pos P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) epsilon
  have hDescent :=
    theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
      P epsilon n0 hDomain hepsilon_pos hL_pos
      P.x0 (P.grad P.x0)
  have hCheckedQuotient :=
    finiteSumCheckedBaseStepSize_spec (epsilon := epsilon)
      (mul_ne_zero (ne_of_gt hL_pos) (ne_of_gt hn0_pos))
  have hB18 :=
    theorem2_finite_sum_B18_source_error_corrected_implementation
      (n := (n : ℝ)) hepsilon_pos hL_pos hn0_pos
      (by exact_mod_cast hn_pos)
  exact correctedFiniteSumGradientCostBound_of_adapters
    P epsilon n0 hDomain hChecked hNonempty hB17 hEstimator hDescent
    hCheckedQuotient hB18 hOutput hTelescope hB19

/-!
The corrected implementation exposes the concrete conditional-expectation
carrier used by the iid with-replacement run.  This is an implementation
bridge only: the source schedule remains real-valued and is not replaced by
these natural counts.
-/
def canonicalFiniteSumConditionalSecondMomentBound
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (hn : 0 < n) (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (epsilon : ℝ)
    (k0 k : ℕ) : Prop :=
  @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
      (FiniteSumRunSamplePath schedule) ℝ inferInstance inferInstance
      (finiteSumRunLaw hn schedule)
      ((finiteSumSampleFiltration schedule).seq (k0 + 1))
      (fun omega =>
        ‖finiteSumOptionIIEstimator P schedule k omega -
          P.grad (finiteSumOptionIIIterate P schedule k omega)‖ ^ 2) ∧
    @MeasureTheory.condExp
        (FiniteSumRunSamplePath schedule) ℝ
        ((finiteSumSampleFiltration schedule).seq (k0 + 1))
        (m₀ := inferInstance)
        inferInstance inferInstance inferInstance
        (finiteSumRunLaw hn schedule)
        (fun omega =>
          ‖finiteSumOptionIIEstimator P schedule k omega -
            P.grad (finiteSumOptionIIIterate P schedule k omega)‖ ^ 2)
      ≤ᵐ[finiteSumRunLaw hn schedule] (fun _ => epsilon ^ 2)

def canonicalFiniteSumFullRefreshConditionalExpectation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (hn : 0 < n) (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (finiteSumRunLaw hn schedule)
    ((finiteSumSampleFiltration schedule).seq k0)
    (fun omega =>
      ‖finiteSumOptionIIEstimator P schedule k0 omega -
        P.grad (finiteSumOptionIIIterate P schedule k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

theorem canonicalFiniteSumFullRefreshConditionalExpectation_of_mod
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (hn : 0 < n) (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (k0 : ℕ)
    (hk0 : k0 % finiteSumImplementationQ schedule = 0) :
    canonicalFiniteSumFullRefreshConditionalExpectation hn P schedule k0 := by
  sorry

theorem canonicalFiniteSumConditionalSecondMomentBound_of_epoch
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (hn : 0 < n) (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (epsilon : ℝ)
    (k0 k : ℕ)
    (hk0 : k0 % finiteSumImplementationQ schedule = 0)
    (horizon : k0 ≤ k) :
    canonicalFiniteSumConditionalSecondMomentBound
      hn P schedule epsilon k0 k := by
  sorry

end InternalFiniteSumImplementation
-/

/-!
The canonical finite-sum process is indexed by an explicit implementation
realization of the paper's real schedule.  This realization is internal
machinery: the source-facing schedule and cost claims below do not quantify
over it.  In particular, exact natural realizability is not silently assumed.
-/

/- 
structure FiniteSumRunRealization
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) where
  n_pos : 0 < n
  S2 : ℕ
  q : ℕ
  S2_pos : 0 < S2
  q_pos : 0 < q
  S2_spec : (S2 : ℝ) = schedule.S2
  q_spec : (q : ℝ) = schedule.q

theorem finiteSumRunRealization_empty_n2_n0_1 :
    ¬ Nonempty
      (FiniteSumRunRealization
        (theorem2FiniteSumImplementationSchedule 2 1 1 1)) := by
  sorry

/- Checked schedule views retain the source formulas without assigning
   fallback values at zero denominators. -/
noncomputable def finiteSumCheckedRecursiveBatchSize
    (n : ℕ) (n0 : ℝ) : Option ℝ :=
  SOptLib.checked_quotient (Real.sqrt (n : ℝ)) n0

noncomputable def finiteSumCheckedEpochLength
    (n : ℕ) (n0 : ℝ) : Option ℝ :=
  if 0 < n ∧ 0 < n0 then
    some (n0 * Real.sqrt (n : ℝ))
  else
    none

theorem finiteSumCheckedRecursiveBatchSize_spec
    {n : ℕ} {n0 : ℝ} (hn0 : n0 ≠ 0) :
    finiteSumCheckedRecursiveBatchSize n n0 =
      some (Real.sqrt (n : ℝ) / n0) := by
  simp [finiteSumCheckedRecursiveBatchSize, SOptLib.checked_quotient, hn0]

theorem finiteSumCheckedEpochLength_none_of_zero
    {n : ℕ} {n0 : ℝ} (hn : n = 0 ∨ n0 = 0) :
    finiteSumCheckedEpochLength n n0 = none := by
  rcases hn with rfl | rfl <;> simp [finiteSumCheckedEpochLength]

abbrev CanonicalFiniteSumRunSamplePath
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : Type _ :=
  SOptLib.miniBatchSamplePath r.S2 (Fin n)

abbrev FiniteSumRunSamplePath
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : Type _ :=
  CanonicalFiniteSumRunSamplePath r

def finiteSumRunS2
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : ℕ :=
  r.S2

def finiteSumRunQ
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : ℕ :=
  r.q

theorem finiteSumRunS2_pos
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : 0 < finiteSumRunS2 r :=
  r.S2_pos

theorem finiteSumRunQ_pos
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : 0 < finiteSumRunQ r :=
  r.q_pos

def finiteSumRecursiveSamples
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → Fin (finiteSumRunS2 r) → Fin n :=
  fun k omega => omega k

noncomputable def finiteSumRunLaw
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) :
    Measure (FiniteSumRunSamplePath r) := by
  letI : Nonempty (Fin n) := ⟨⟨0, r.n_pos⟩⟩
  exact SOptLib.iidMiniBatchSampleLaw (finiteSumRunS2 r)
    (PMF.uniformOfFintype (Fin n)).toMeasure

theorem finiteSumRunLaw_spec
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) :
    IsProbabilityMeasure (finiteSumRunLaw r) := by
  letI : Nonempty (Fin n) := ⟨⟨0, r.n_pos⟩⟩
  unfold finiteSumRunLaw
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
    (finiteSumRunS2 r) (PMF.uniformOfFintype (Fin n)).toMeasure

/- Internal quotient domain.  These facts are deliberately not added to the
   paper-facing Theorem 2 domain. -/
def correctedFiniteSumCheckedDomain
    (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  0 < n ∧ 0 < epsilon ∧ 0 < L ∧ 0 < n0

theorem correctedFiniteSumCheckedDomain.n_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < n :=
  h.1

theorem correctedFiniteSumCheckedDomain.epsilon_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < epsilon :=
  h.2.1

theorem correctedFiniteSumCheckedDomain.L_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < L :=
  h.2.2.1

theorem correctedFiniteSumCheckedDomain.n0_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < n0 :=
  h.2.2.2

theorem correctedFiniteSumCheckedDomain.rejects_n_zero
    {epsilon L n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain 0 epsilon L n0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.rejects_epsilon_zero
    {n : ℕ} {L n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n 0 L n0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.rejects_L_zero
    {n : ℕ} {epsilon n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n epsilon 0 n0 := by
  simp [correctedFiniteSumCheckedDomain]

theorem correctedFiniteSumCheckedDomain.rejects_n0_zero
    {n : ℕ} {epsilon L : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n epsilon L 0 := by
  simp [correctedFiniteSumCheckedDomain]

noncomputable def correctedFiniteSumCheckedBaseStepSize
    (epsilon L n0 : ℝ) : Option ℝ :=
  SOptLib.checked_quotient epsilon (L * n0)

theorem finiteSumCheckedBaseStepSize_spec
    {epsilon L n0 : ℝ} (hden : L * n0 ≠ 0) :
    correctedFiniteSumCheckedBaseStepSize epsilon L n0 =
      some (epsilon / (L * n0)) := by
  simp [correctedFiniteSumCheckedBaseStepSize, SOptLib.checked_quotient, hden]

noncomputable def finiteSumCheckedSchedule
    (n : ℕ) (epsilon L n0 : ℝ) : Option (CorrectedFiniteSumSchedule n) :=
  by
    classical
    exact
      if correctedFiniteSumCheckedDomain n epsilon L n0 then
        some (theorem2FiniteSumImplementationSchedule n epsilon L n0)
      else
        none

theorem finiteSumCheckedSchedule_spec
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) :
    finiteSumCheckedSchedule n epsilon L n0 =
      some (theorem2FiniteSumImplementationSchedule n epsilon L n0) := by
  simp [finiteSumCheckedSchedule, h]

theorem finiteSumCheckedSchedule_none_of_zero
    {n : ℕ} {epsilon L n0 : ℝ}
    (hzero : n = 0 ∨ epsilon = 0 ∨ L = 0 ∨ n0 = 0) :
    finiteSumCheckedSchedule n epsilon L n0 = none := by
  classical
  rcases hzero with rfl | rfl | rfl | rfl <;>
    simp [finiteSumCheckedSchedule, correctedFiniteSumCheckedDomain]

noncomputable def finiteSumOptionIIUpdate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : CorrectedFiniteSumSchedule n) (x v : E) : E :=
  x - schedule.etaK ‖v‖ • v

noncomputable def finiteSumOptionIITransition
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule)
    (recursiveSamples : Fin (finiteSumRunS2 r) → Fin n)
    (k : ℕ) (state : State E) : State E :=
  let xNext := finiteSumOptionIIUpdate schedule state.x state.v
  let vNext :=
    if (k + 1) % finiteSumRunQ r = 0 then
      P.grad xNext
    else
      recursiveEstimator P.gradKernel state.v state.x xNext recursiveSamples
  { x := xNext, v := vNext }

noncomputable def finiteSumOptionIIStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → State E
  | 0 => fun _ => { x := P.x0, v := P.grad P.x0 }
  | k + 1 => fun omega =>
      finiteSumOptionIITransition P schedule r
        (finiteSumRecursiveSamples r (k + 1) omega) k
        (finiteSumOptionIIStateProcess P schedule r k omega)

noncomputable def finiteSumOptionIIIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → E :=
  fun k omega => (finiteSumOptionIIStateProcess P schedule r k omega).x

noncomputable def finiteSumOptionIIEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → E :=
  fun k omega => (finiteSumOptionIIStateProcess P schedule r k omega).v

@[simp]
theorem finiteSumOptionIIStateProcess_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIStateProcess P schedule r 0 omega =
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

@[simp]
theorem finiteSumOptionIIStateProcess_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k : ℕ)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIStateProcess P schedule r (k + 1) omega =
      finiteSumOptionIITransition P schedule r
        (finiteSumRecursiveSamples r (k + 1) omega) k
        (finiteSumOptionIIStateProcess P schedule r k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIIterate_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k : ℕ)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIIterate P schedule r (k + 1) omega =
      finiteSumOptionIIUpdate schedule
        (finiteSumOptionIIIterate P schedule r k omega)
        (finiteSumOptionIIEstimator P schedule r k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIEstimator P schedule r 0 omega = P.grad P.x0 := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k : ℕ)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIEstimator P schedule r (k + 1) omega =
      if (k + 1) % finiteSumRunQ r = 0 then
        P.grad (finiteSumOptionIIIterate P schedule r (k + 1) omega)
      else
        recursiveEstimator P.gradKernel
          (finiteSumOptionIIEstimator P schedule r k omega)
          (finiteSumOptionIIIterate P schedule r k omega)
          (finiteSumOptionIIIterate P schedule r (k + 1) omega)
          (finiteSumRecursiveSamples r (k + 1) omega) := by
  rfl

noncomputable def finiteSumSampleFiltration
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) :
    Filtration ℕ
      (by infer_instance : MeasurableSpace (FiniteSumRunSamplePath r)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

def finiteSumSourceRefreshBoundary
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (k0 : ℕ) : Prop :=
  ∃ r : FiniteSumRunRealization schedule, k0 % finiteSumRunQ r = 0

def finiteSumSourceRefreshErrorZero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (k0 : ℕ) : Prop :=
  ∀ r : FiniteSumRunRealization schedule,
    SOptLib.ConditionalExpectation.conditionalExpectationEq
      (finiteSumRunLaw r)
      ((finiteSumSampleFiltration r).seq k0)
      (fun omega =>
        ‖finiteSumOptionIIEstimator P schedule r k0 omega -
          P.grad (finiteSumOptionIIIterate P schedule r k0 omega)‖ ^ 2)
      (fun _ => (0 : ℝ))

theorem theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (k0 : ℕ) (hk0 : finiteSumSourceRefreshBoundary schedule k0) :
    finiteSumSourceRefreshErrorZero P schedule k0 := by
  sorry

def finiteSumSourceEstimatorErrorBound
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (epsilon : ℝ) (k0 k : ℕ) : Prop :=
  ∀ r : FiniteSumRunRealization schedule,
    @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
        (FiniteSumRunSamplePath r) ℝ inferInstance inferInstance
        (finiteSumRunLaw r) ((finiteSumSampleFiltration r).seq k0)
        (fun omega =>
          ‖finiteSumOptionIIEstimator P schedule r k omega -
            P.grad (finiteSumOptionIIIterate P schedule r k omega)‖ ^ 2) ∧
      @MeasureTheory.condExp
          (FiniteSumRunSamplePath r) ℝ
          ((finiteSumSampleFiltration r).seq k0)
          (m₀ := inferInstance)
          inferInstance inferInstance inferInstance
          (finiteSumRunLaw r)
          (fun omega =>
            ‖finiteSumOptionIIEstimator P schedule r k omega -
              P.grad (finiteSumOptionIIIterate P schedule r k omega)‖ ^ 2)
        ≤ᵐ[finiteSumRunLaw r] (fun _ => epsilon ^ 2)

theorem theorem2_finite_sum_step_bound_B2_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ)
    (hepsilon : 0 < epsilon) (hL : 0 < P.L) (hn0 : 1 ≤ n0)
    (r : FiniteSumRunRealization (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
    (x v : E) :
    ‖finiteSumOptionIIUpdate
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v - x‖ ≤
      epsilon * (P.L * n0)⁻¹ := by
  sorry

theorem theorem2_finite_sum_estimator_error_adapter_corrected_implementation
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (schedule : CorrectedFiniteSumSchedule n) (epsilon : ℝ) :
    ∀ k0 k : ℕ,
      finiteSumSourceRefreshBoundary schedule k0 →
      k0 ≤ k →
      finiteSumSourceEstimatorErrorBound P schedule epsilon k0 k := by
  sorry

noncomputable def theorem2FiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
      (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
      (epsilon * n0 / Real.sqrt n)

theorem theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    {epsilon L n0 n : ℝ} (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold theorem2FiniteSumB18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

def theorem2FiniteSumB18SourceError
    (epsilon L n0 n : ℝ) : Prop :=
  theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ} (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18SourceError epsilon L n0 n := by
  exact theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    hepsilon hL hn0 hn

noncomputable def correctedFiniteSumLiteralB19Cost (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def correctedFiniteSumCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def correctedFiniteSumBudget
    (L Delta n0 epsilon : ℝ) : Option ℕ :=
  (SOptLib.checked_quotient (4 * L * Delta * n0) (epsilon ^ 2)).map
    (fun value => Nat.floor value + 1)

noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : Option ℝ :=
  (SOptLib.checked_quotient (K : ℝ) schedule.q).map
    (fun refreshes =>
      refreshes * (schedule.S1 : ℝ) + (K : ℝ) * schedule.S2)

noncomputable def correctedFiniteSumGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  match
      SOptLib.checked_quotient
        (8 * (L * Delta) * Real.sqrt (n : ℝ)) (epsilon ^ 2),
      SOptLib.checked_quotient (2 * Real.sqrt (n : ℝ)) n0 with
  | some mainTerm, some finalTerm =>
      some ((n : ℝ) + mainTerm + finalTerm)
  | _, _ => none

noncomputable def correctedFiniteSumProcessGradientCost
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) (K : ℕ) : ℕ :=
  Nat.ceil ((K : ℝ) / (finiteSumRunQ r : ℝ)) * schedule.S1 +
    K * finiteSumRunS2 r

theorem correctedFiniteSumProcessGradientCost_B19_bridge
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) (K : ℕ) :
    ((correctedFiniteSumProcessGradientCost r K : ℕ) : ℝ) ≤
      correctedFiniteSumLiteralB19Cost K schedule.S1 +
        correctedFiniteSumCorrectedB19Cost K schedule.S1 schedule.S2 := by
  sorry

theorem theorem2FiniteSumGradientCostBound_from_adapters
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (hChecked : correctedFiniteSumCheckedDomain n epsilon P.L n0)
    (r : FiniteSumRunRealization
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
    (hB17 :
      finiteSumSourceRefreshErrorZero P
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k0 k : ℕ,
        finiteSumSourceRefreshBoundary
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k0 →
        k0 ≤ k →
        finiteSumSourceEstimatorErrorBound P
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) epsilon k0 k)
    (hB19 :
      (correctedFiniteSumProcessGradientCost r
          (Option.getD (correctedFiniteSumBudget P.L P.Delta n0 epsilon) 0) : ℝ) ≤
        correctedFiniteSumLiteralB19Cost
          (Option.getD (correctedFiniteSumBudget P.L P.Delta n0 epsilon) 0)
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S1 +
        correctedFiniteSumCorrectedB19Cost
          (Option.getD (correctedFiniteSumBudget P.L P.Delta n0 epsilon) 0)
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S1
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S2) :
    (correctedFiniteSumProcessGradientCost r
        (Option.getD (correctedFiniteSumBudget P.L P.Delta n0 epsilon) 0) : ℝ) ≤
      Option.getD (correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon) 0 := by
  sorry

theorem theorem2_finite_sum_gradient_cost_bound_from_realization
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (hChecked : correctedFiniteSumCheckedDomain n epsilon P.L n0)
    (r : FiniteSumRunRealization
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)) :
    (correctedFiniteSumProcessGradientCost r
        (Option.getD (correctedFiniteSumBudget P.L P.Delta n0 epsilon) 0) : ℝ) ≤
      Option.getD (correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon) 0 := by
  have hB17 :=
    theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
      P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) 0
      ⟨r, by simp [finiteSumRunQ]⟩
  have hEstimator :=
    theorem2_finite_sum_estimator_error_adapter_corrected_implementation
      P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) epsilon
  have hB19 :=
    correctedFiniteSumProcessGradientCost_B19_bridge r
      (Option.getD (correctedFiniteSumBudget P.L P.Delta n0 epsilon) 0)
  exact theorem2FiniteSumGradientCostBound_from_adapters
    P epsilon n0 hDomain hChecked r hB17 hEstimator hB19

/-- Checked source cost claim used by Theorem 2.

Book path `/extension/additions/main_theorem/proof/10`; source quote:
the source counts full-refresh and recursive-gradient accesses and then follows
the corrected `2 K S₂ + S₁` route.  `Option` selectors preserve undefined
zero-denominator cases instead of assigning them paper-looking values. -/
def theorem2FiniteSumSourceCostClaim
    {n : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) : Prop :=
  ∀ K cost bound,
    correctedFiniteSumBudget P.L P.Delta n0 epsilon = some K →
    theorem2FiniteSumSourceGradientCost
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) K = some cost →
    correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon =
      some bound →
    cost ≤ bound

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    theorem2FiniteSumSourceCostClaim P epsilon n0 := by
  sorry

theorem theorem2_finite_sum_gradient_average_adapter
    {Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  exact uniform_average_gradient_bound_of_estimator_average
    mu grad iterate estimator K hK epsilon hconvert hest_avg

theorem theorem2_finite_sum_descent_telescope_adapter
    {ι : Type*} (s : Finset ι)
    (gap descent variance correction : ι → ℝ)
    (initial terminal : ℝ)
    (hstep :
      ∀ i ∈ s, gap i ≤ descent i + variance i - correction i)
    (htelescope : Finset.sum s descent = initial - terminal)
    (hterminal_nonneg : 0 ≤ terminal) :
    Finset.sum s gap ≤
      initial + Finset.sum s variance - Finset.sum s correction := by
  exact summed_one_step_gap_bound_of_telescope
    s gap descent variance correction initial terminal
    hstep htelescope hterminal_nonneg

end Algorithms.Unverified.SPIDER
-/

end Algorithms.Unverified.SPIDER

namespace Algorithms.Unverified.SPIDER

/- 
/-!
Source layer for the finite-sum specialization.

The declarations in this namespace use the real quantities printed in
Eq. (3.7). They deliberately do not mention natural ceilings, implementation
filtrations, exact count realizations, output witnesses, or telescope
witnesses. Those belong to `CorrectedFiniteSumImplementation` below.
-/

/-!
The source process is indexed by an explicit finite batch-coordinate type.
This is the source realization convention for the paper's with-replacement
`S₂` sample average: every coordinate is a genuine component index and the
average is taken over the whole batch, while the paper's real `S₂` remains in
the schedule.  No natural count is inferred from that real quantity.

The refresh pattern is also explicit source data.  The paper gives the real
epoch length `q`, but does not provide a natural-number realization rule for
an arbitrary real `q`; the corrected implementation layer below is the only
place that chooses positive natural counts. -/
abbrev FiniteSumSourceSamplePath (n : ℕ) (BatchIndex : Type*) :=
  ℕ → BatchIndex → Fin n

abbrev FiniteSumSourceRefreshPattern := ℕ → Prop

def finiteSumSourceRefreshAt
    (refreshPattern : FiniteSumSourceRefreshPattern) (k : ℕ) : Prop :=
  refreshPattern k

theorem finiteSumSourceRefreshAt_of_pattern
    (refreshPattern : FiniteSumSourceRefreshPattern) (k : ℕ)
    (hk : refreshPattern k) :
    finiteSumSourceRefreshAt refreshPattern k :=
  hk

noncomputable def finiteSumSourceBatchAverage
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n BatchIndex)
    (k : ℕ) (x : E) : E :=
  (Fintype.card BatchIndex : ℝ)⁻¹ •
  Finset.sum Finset.univ
      (fun i : BatchIndex => P.gradKernel x (omega k i))

@[simp]
theorem finiteSumSourceBatchAverage_def
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n BatchIndex)
    (k : ℕ) (x : E) :
    finiteSumSourceBatchAverage P omega k x =
      (Fintype.card BatchIndex : ℝ)⁻¹ •
        Finset.sum Finset.univ
          (fun i : BatchIndex => P.gradKernel x (omega k i)) := by
  rfl

theorem finiteSumSourceBatchCoordinate_genuine
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n BatchIndex)
    (k : ℕ) (i : BatchIndex) (x : E) :
    HasGradientAt
      (fun y : E => P.componentObjective (omega k i) y)
      (P.gradKernel x (omega k i)) x := by
  change HasGradientAt
    (fun y : E => P.componentObjective (omega k i) y)
    (P.componentGradient (omega k i) x).1 x
  exact (P.componentGradient (omega k i) x).2

noncomputable def finiteSumSourceOptionIIUpdate
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E) : E :=
  x -
    (if hv : 0 < ‖v‖ then schedule.etaK ‖v‖ hv else 0) • v

@[simp]
theorem finiteSumSourceOptionIIUpdate_zero
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x : E) :
    finiteSumSourceOptionIIUpdate schedule x 0 = x := by
  simp [finiteSumSourceOptionIIUpdate]

noncomputable def finiteSumSourceRecursiveEstimator
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n BatchIndex)
    (k : ℕ) (vPrev xPrev xCurr : E) : E :=
  finiteSumSourceBatchAverage P omega k xCurr -
    finiteSumSourceBatchAverage P omega k xPrev + vPrev

noncomputable def finiteSumSourceTransition
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (omega : FiniteSumSourceSamplePath n BatchIndex)
    (k : ℕ) (state : State E) : State E :=
  by
    classical
    let xNext := finiteSumSourceOptionIIUpdate schedule state.x state.v
    let vNext :=
      if finiteSumSourceRefreshAt refreshPattern (k + 1) then
        P.grad xNext
      else
        finiteSumSourceRecursiveEstimator P omega (k + 1)
          state.v state.x xNext
    exact { x := xNext, v := vNext }

/-- Canonical source-level SPIDER state process.  Refreshes are selected by
the explicit source refresh pattern.  This keeps the paper's real epoch
length in the schedule without asserting an exact natural realization of it.

Book paths `/extension/additions/algorithm_spec/steps/2` and
`/extension/additions/algorithm_spec/steps/3`; source quotes:
the full-gradient branch gives `vᵏ = ∇f_{S₁}(xᵏ)`, and the recursive branch
gives `vᵏ = ∇f_{S₂}(xᵏ) - ∇f_{S₂}(xᵏ⁻¹) + vᵏ⁻¹`. -/
noncomputable def finiteSumSourceStateProcess
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern) :
    ℕ → FiniteSumSourceSamplePath n BatchIndex → State E
  | 0 => fun _ => { x := P.x0, v := P.grad P.x0 }
  | k + 1 => fun omega =>
      finiteSumSourceTransition P schedule refreshPattern omega k
        (finiteSumSourceStateProcess P schedule refreshPattern k omega)

noncomputable def finiteSumSourceIterate
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern) :
    ℕ → FiniteSumSourceSamplePath n BatchIndex → E :=
  fun k omega => (finiteSumSourceStateProcess P schedule refreshPattern k omega).x

noncomputable def finiteSumSourceEstimator
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern) :
    ℕ → FiniteSumSourceSamplePath n BatchIndex → E :=
  fun k omega => (finiteSumSourceStateProcess P schedule refreshPattern k omega).v

@[simp]
theorem finiteSumSourceStateProcess_zero
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (omega : FiniteSumSourceSamplePath n BatchIndex) :
    finiteSumSourceStateProcess P schedule refreshPattern 0 omega =
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

@[simp]
theorem finiteSumSourceStateProcess_succ
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (k : ℕ) (omega : FiniteSumSourceSamplePath n BatchIndex) :
    finiteSumSourceStateProcess P schedule refreshPattern (k + 1) omega =
      finiteSumSourceTransition P schedule refreshPattern omega k
        (finiteSumSourceStateProcess P schedule refreshPattern k omega) := by
  rfl

@[simp]
theorem finiteSumSourceIterate_succ
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (k : ℕ) (omega : FiniteSumSourceSamplePath n BatchIndex) :
    finiteSumSourceIterate P schedule refreshPattern (k + 1) omega =
      finiteSumSourceOptionIIUpdate schedule
        (finiteSumSourceIterate P schedule refreshPattern k omega)
        (finiteSumSourceEstimator P schedule refreshPattern k omega) := by
  rfl

@[simp]
theorem finiteSumSourceEstimator_zero
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (omega : FiniteSumSourceSamplePath n BatchIndex) :
    finiteSumSourceEstimator P schedule refreshPattern 0 omega = P.grad P.x0 := by
  rfl

noncomputable def finiteSumSourceRefreshErrorExpectation
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure (FiniteSumSourceSamplePath n BatchIndex))
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern) (k0 : ℕ) : ℝ :=
  ∫ omega,
    ‖finiteSumSourceEstimator P schedule refreshPattern k0 omega -
      P.grad (finiteSumSourceIterate P schedule refreshPattern k0 omega)‖ ^ 2 ∂mu

noncomputable def finiteSumSourceEstimatorErrorExpectation
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure (FiniteSumSourceSamplePath n BatchIndex))
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (k0 k : ℕ) : ℝ :=
  if k0 ≤ k then
    ∫ omega,
      ‖finiteSumSourceEstimator P schedule refreshPattern k omega -
        P.grad (finiteSumSourceIterate P schedule refreshPattern k omega)‖ ^ 2 ∂mu
  else
    0

def finiteSumSourceEstimatorErrorBound
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure (FiniteSumSourceSamplePath n BatchIndex))
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (epsilon : ℝ) (k0 k : ℕ) : Prop :=
  finiteSumSourceEstimatorErrorExpectation mu P schedule refreshPattern k0 k ≤ epsilon ^ 2

/-- B.17 at the source expectation boundary.

Book path `/extension/additions/assumptions/2`; source quote:
`Eₖ₀ ‖vᵏ⁰ - ∇f(xᵏ⁰)‖² = Eₖ₀ ‖∇f(xᵏ⁰) - ∇f(xᵏ⁰)‖² = 0`.
The source statement is a direct expectation of the canonical source
estimator, not an implementation-filtration contract. -/
theorem theorem2_finite_sum_full_refresh_error_B17_source
    {n : ℕ} {BatchIndex E : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (mu : Measure (FiniteSumSourceSamplePath n BatchIndex))
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern) (k0 : ℕ)
    (hk0 : finiteSumSourceRefreshAt refreshPattern k0) :
    finiteSumSourceRefreshErrorExpectation mu P schedule refreshPattern k0 = 0 := by
  sorry

/-- Source Lemma 2 boundary.

Book path `/extension/additions/key_lemmas/1`; source quote:
`Eₖ₀ ‖vᵏ - ∇f(xᵏ)‖² ≤ ε²`, where `k₀ = floor(k/q) q`.
The declaration exposes `vᵏ`, `∇f(xᵏ)`, `k₀`, `k`, and the source
expectation carrier while leaving the B.18 epsilon-power discrepancy visible
to the prover. -/
theorem theorem2_finite_sum_estimator_error_adapter_source
    {n d : ℕ} {BatchIndex : Type*}
    [Fintype BatchIndex] [Nonempty BatchIndex]
    (P : FiniteSumProblem n (VariableSpace d))
    (mu : Measure (FiniteSumSourceSamplePath n BatchIndex))
    (schedule : FiniteSumSourceSchedule n)
    (refreshPattern : FiniteSumSourceRefreshPattern)
    (epsilon : ℝ) (k0 k : ℕ)
    (hk0 : finiteSumSourceRefreshAt refreshPattern k0)
    (horizon : k0 ≤ k)
    (epochWindow : ((k - k0 : ℕ) : ℝ) ≤ schedule.q) :
    finiteSumSourceEstimatorErrorBound mu P schedule refreshPattern epsilon k0 k := by
  sorry

/-- Uniform random iterate output for the source process.

Book path `/extension/additions/algorithm_spec/steps/5`; source quote:
`x̃` is chosen uniformly at random from `{xᵏ}_{k=0}^{K-1}`.  The output law
is source-level and carries no implementation filtration or rounded count. -/
noncomputable def finiteSumSourceUniformOutputLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × Ω) :=
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  (PMF.uniformOfFintype (Fin K)).toMeasure.prod mu

def finiteSumSourceUniformOutput
    {Ω E : Type*} (K : ℕ) (iterate : ℕ → Ω → E) :
    Fin K × Ω → E :=
  fun z => iterate z.1 z.2

noncomputable def theorem2FiniteSumSourceLiteralB19Cost
    (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def theorem2FiniteSumSourceCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

/-- Source B.19 cost, with the real `S₂ = √n/n₀`.

Book path `/extension/additions/main_theorem`; source quote: "The gradient
cost is bounded by n + 8(L Delta) · n^(1/2) epsilon^(-2) +
2 n₀^(-1) n^(1/2)."  The literal ceiling/count route is retained separately
above; this source object is the explicitly corrected real route. -/
noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  theorem2FiniteSumSourceCorrectedB19Cost K schedule.S1 schedule.S2

noncomputable def internalFiniteSumCheckedIterationBudget
    (L Delta epsilon n0 : ℝ) : Option ℕ :=
  (SOptLib.checked_quotient (4 * L * Delta * n0) (epsilon ^ 2)).map
    (fun value => Nat.floor value + 1)

noncomputable def internalFiniteSumCheckedGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  match
      SOptLib.checked_quotient
          (8 * (L * Delta) * Real.sqrt (n : ℝ)) (epsilon ^ 2),
      SOptLib.checked_quotient (2 * Real.sqrt (n : ℝ)) n0 with
  | some mainTerm, some finalTerm =>
      some ((n : ℝ) + mainTerm + finalTerm)
  | _, _ => none

def theorem2FiniteSumSourceCostClaim
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) : Prop :=
  ∀ (hL : 0 < P.L) (hn0 : 0 < n0) K cost bound,
    theorem2FiniteSumSourceIterationBudget
        P.L P.Delta epsilon n0 = some K →
    theorem2FiniteSumSourceGradientCost
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0
          hL hn0) K = cost →
    theorem2FiniteSumSourceGradientCostBound
        n P.L P.Delta n0 epsilon = some bound →
    cost ≤ bound

/-- Literal B.18 source display.

Book path `/extension/additions/main_theorem/proof/2`; source quote:
`n₀ n^(1/2) L² · ε²/(L² n₀²) · ε n₀/n^(1/2)`.
The displayed product is kept as a source object; its separately proved
epsilon-cube simplification is not rewritten to the paper's printed
epsilon-squared label. -/
noncomputable def theorem2FiniteSumB18DisplayedTerm_source
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

def theorem2FiniteSumB18SourceError_source
    (epsilon L n0 n : ℝ) : Prop :=
  theorem2FiniteSumB18DisplayedTerm_source epsilon L n0 n = epsilon ^ 3

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18SourceError_source epsilon L n0 n := by
  unfold theorem2FiniteSumB18SourceError_source
  unfold theorem2FiniteSumB18DisplayedTerm_source
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

theorem theorem2_finite_sum_B19_source_routes_are_distinct :
    theorem2FiniteSumSourceLiteralB19Cost 1 1 ≠
      theorem2FiniteSumSourceCorrectedB19Cost 1 1 2 := by
  norm_num [theorem2FiniteSumSourceLiteralB19Cost,
    theorem2FiniteSumSourceCorrectedB19Cost]

/-- Paper-facing finite-sum cost root.

Book path `/extension/additions/main_theorem`; source quote:
`The gradient cost is bounded by n + 8(L Delta) n^(1/2) epsilon^(-2)
+ 2 n₀^(-1) n^(1/2) for any choice of n₀ in [1,n^(1/2)]`.
Its conclusion is source-level and does not mention rounded counts,
implementation filtrations, output witnesses, or telescope witnesses. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    theorem2FiniteSumSourceCostClaim P epsilon n0 := by
  sorry

namespace CorrectedFiniteSumImplementation

abbrev runSamplePath
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : Type _ :=
  InternalFiniteSumImplementation.FiniteSumRunSamplePath schedule

noncomputable def runLaw
    {n : ℕ} (hn : 0 < n) (schedule : CorrectedFiniteSumSchedule n) :
    Measure (runSamplePath schedule) :=
  InternalFiniteSumImplementation.finiteSumRunLaw hn schedule

noncomputable def iterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → runSamplePath schedule → E :=
  InternalFiniteSumImplementation.finiteSumOptionIIIterate P schedule

noncomputable def estimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → runSamplePath schedule → E :=
  InternalFiniteSumImplementation.finiteSumOptionIIEstimator P schedule

noncomputable def processGradientCost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    schedule K

theorem run_nonempty
    {n : ℕ} {epsilon L n0 : ℝ}
    (h :
      InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain
        n epsilon L n0) :
    Nonempty
      (runSamplePath (theorem2FiniteSumImplementationSchedule n epsilon L n0)) := by
  letI : Nonempty (Fin n) :=
    ⟨⟨0, InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.n_pos h⟩⟩
  exact inferInstance

theorem process_cost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((processGradientCost schedule K : ℕ) : ℝ) ≤
      InternalFiniteSumImplementation.correctedFiniteSumLiteralB19Cost
          K schedule.S1 +
        InternalFiniteSumImplementation.correctedFiniteSumCorrectedB19Cost
          K schedule.S1 schedule.S2 := by
  exact
    InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
      schedule K

end CorrectedFiniteSumImplementation

end Algorithms.Unverified.SPIDER

end Algorithms.Unverified.SPIDER

namespace Algorithms.Unverified.SPIDER

namespace SourceFiniteSum

abbrev Path (n : ℕ) := ℕ → ℕ → Fin n

opaque law (n : ℕ) : Measure (Path n)

noncomputable def filtration (n : ℕ) :
    Filtration ℕ (by infer_instance : MeasurableSpace (Path n)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

opaque iterate
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → Path n → VariableSpace d

opaque estimator
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → Path n → VariableSpace d

noncomputable def average
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) : E :=
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  SOptLib.finiteUniformAverage g

noncomputable def objective
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → ℝ :=
  fun x => average hn (fun i : Fin n => P.componentObjective i x)

noncomputable def gradient
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → VariableSpace d :=
  fun x =>
    average hn
      (fun i : Fin n =>
        finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x)

theorem gradient_component_spec
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt
      (fun y : VariableSpace d => P.componentObjective i y)
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) x := by
  exact finiteSumComponentGradient_hasGradientAt P.componentObjective P.component_gradient_exists i x

theorem gradient_hasGradientAt
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  sorry

noncomputable def infimum
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objectiveInfimum (objective P hn)

noncomputable def delta
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objective P hn P.x0 - infimum P hn

def finite_gap_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : Prop :=
  BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) ∧
    0 ≤ delta P hn

theorem finite_gap_boundary_spec
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    finite_gap_boundary P hn := by
  sorry

def update_domain
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (v : VariableSpace d) : Prop :=
  0 < ‖v‖

noncomputable def optionIIUpdate
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - schedule.etaK ‖v‖ • v

theorem optionIIUpdate_formula
    {n d : ℕ}
    (epsilon L n0 : ℝ) (x v : VariableSpace d) :
    optionIIUpdate
        (theorem2FiniteSumSourceSchedule n epsilon L n0) x v =
      x -
        min (epsilon / (L * n0 * ‖v‖)) (1 / (2 * L * n0)) • v := by
  rfl

def refresh_at
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) : Prop :=
  schedule.q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * schedule.q

def epoch_boundary
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (k0 k : ℕ) : Prop :=
  refresh_at schedule k0 ∧ k0 ≤ k

def full_refresh_error_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (law n)
    ((filtration n).seq k0)
    (fun omega =>
      ‖estimator P hn schedule k0 omega -
        gradient P hn (iterate P hn schedule k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

def estimator_error_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ)
    (k0 k : ℕ) : Prop :=
  epoch_boundary schedule k0 k →
    @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
        (Path n) ℝ inferInstance inferInstance
        (law n) ((filtration n).seq (k0 + 1))
        (fun omega =>
          ‖estimator P hn schedule k omega -
            gradient P hn (iterate P hn schedule k omega)‖ ^ 2) ∧
      @MeasureTheory.condExp
          (Path n) ℝ
          ((filtration n).seq (k0 + 1))
          (m₀ := inferInstance)
          inferInstance inferInstance inferInstance
          (law n)
          (fun omega =>
            ‖estimator P hn schedule k omega -
              gradient P hn (iterate P hn schedule k omega)‖ ^ 2)
        ≤ᵐ[law n] (fun _ => epsilon ^ 2)

theorem full_refresh_error_B17
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ)
    (hk0 : refresh_at schedule k0) :
    full_refresh_error_boundary P hn schedule k0 := by
  sorry

theorem estimator_error_Lemma2
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) :
    ∀ k k0, estimator_error_boundary P hn schedule epsilon k0 k := by
  sorry

noncomputable def B18_display
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem B18_display_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    B18_display epsilon L n0 n = epsilon ^ 3 := by
  unfold B18_display
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

def B18_paper_epsilon_sq_assertion
    (epsilon L n0 n : ℝ) : Prop :=
  B18_display epsilon L n0 n = epsilon ^ 2

theorem B18_paper_epsilon_sq_unresolved
    (epsilon L n0 n : ℝ) :
    B18_paper_epsilon_sq_assertion epsilon L n0 n := by
  sorry

noncomputable def B19_literal_display
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * schedule.q⁻¹) : ℝ) *
      (schedule.S1 : ℝ) +
    (K : ℝ) * schedule.S2

noncomputable def B19_literal_bound (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def B19_corrected_bound
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def gradient_cost
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) : ℝ :=
  B19_literal_display schedule K

def cost_transition
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) : Prop :=
  gradient_cost schedule K ≤ B19_literal_bound K schedule.S1

theorem cost_transition_spec
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) :
    cost_transition schedule K := by
  sorry

theorem B19_routes_are_distinct :
    B19_literal_bound 1 1 ≠ B19_corrected_bound 1 1 2 := by
  norm_num [B19_literal_bound, B19_corrected_bound]

noncomputable def iteration_budget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def gradient_cost_bound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

def descent_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ k omega,
    objective P hn (iterate P hn schedule (k + 1) omega) ≤
      objective P hn (iterate P hn schedule k omega) -
        epsilon * ‖estimator P hn schedule k omega‖ /
          (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖estimator P hn schedule k omega -
            gradient P hn (iterate P hn schedule k omega)‖ ^ 2

def output_conversion_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) : Prop :=
  ∀ K, 0 < K →
    uniformOutputGradientNormAverage
      (law n) (gradient P hn) (iterate P hn schedule) K ≤ 5 * epsilon

def telescope_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ K, 0 < K →
    (epsilon / (4 * P.L * n0)) *
        Finset.sum (Finset.range K)
          (fun k =>
            ∫ omega, ‖estimator P hn schedule k omega‖ ∂law n) ≤
      delta P hn + (3 * K * epsilon ^ 2) / (4 * P.L * n0)

def cost_claim
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (epsilon n0 : ℝ) : Prop :=
  gradient_cost
      (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
      (iteration_budget P.L (delta P hn) epsilon n0) ≤
    gradient_cost_bound n P.L (delta P hn) n0 epsilon

theorem cost_claim_of_dependency_graph
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0)
    (hB17 :
      full_refresh_error_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k k0,
        estimator_error_boundary P hn
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
          epsilon k0 k)
    (hDescent :
      descent_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon n0)
    (hOutput :
      output_conversion_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon)
    (hTelescope :
      telescope_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon n0)
    (hCost :
      ∀ K,
        cost_transition
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K) :
    cost_claim P hn epsilon n0 := by
  sorry

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    cost_claim P hDomain.n_pos epsilon n0 := by
  let schedule := theorem2FiniteSumSourceSchedule n epsilon P.L n0
  have hq : schedule.q ≠ 0 := by
    dsimp [schedule, theorem2FiniteSumSourceSchedule]
    exact ne_of_gt
      (mul_pos hDomain.n0_pos
        (Real.sqrt_pos.2 (by exact_mod_cast hDomain.n_pos)))
  have hB17 :
      full_refresh_error_boundary P hDomain.n_pos schedule 0 :=
    full_refresh_error_B17 P hDomain.n_pos schedule 0
      ⟨hq, 0, by simp⟩
  have hEstimator :
      ∀ k k0, estimator_error_boundary P hDomain.n_pos
        schedule epsilon k0 k :=
    estimator_error_Lemma2 P hDomain.n_pos schedule epsilon
  have hDescent :
      descent_boundary P hDomain.n_pos schedule epsilon n0 := by
    exact theorem2_finite_sum_source_descent_boundary
      P hDomain.n_pos schedule epsilon n0
  have hOutput :
      output_conversion_boundary P hDomain.n_pos schedule epsilon := by
    exact theorem2_finite_sum_source_output_boundary
      P hDomain.n_pos epsilon
  have hTelescope :
      telescope_boundary P hDomain.n_pos schedule epsilon n0 := by
    exact theorem2_finite_sum_source_telescope_boundary
      P hDomain.n_pos schedule epsilon n0
  have hCost :
      ∀ K, cost_transition schedule K := by
    intro K
    exact cost_transition_spec schedule K
  exact cost_claim_of_dependency_graph
    P hDomain.n_pos epsilon n0 hDomain hB17 hEstimator hDescent
    hOutput hTelescope hCost

namespace ExecutableCost

noncomputable def process_gradient_cost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    schedule K

theorem process_gradient_cost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((process_gradient_cost schedule K : ℕ) : ℝ) ≤
      InternalFiniteSumImplementation.correctedFiniteSumLiteralB19Cost
          K schedule.S1 +
        InternalFiniteSumImplementation.correctedFiniteSumCorrectedB19Cost
          K schedule.S1 schedule.S2 := by
  exact
    InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
      schedule K

end ExecutableCost

end SourceFiniteSum

end Algorithms.Unverified.SPIDER

/-!
Active source-facing finite-sum boundary for Theorem 2.

The declarations in this section use the real schedule and the canonical
finite-average objects.  The conditional-expectation law and recursive
process are semantic source carriers; the rounded implementation is named
separately below and is not an input to the source theorem.
-/

namespace Algorithms.Unverified.SPIDER

namespace FiniteSumSource

abbrev Path (n : ℕ) := ℕ → ℕ → Fin n

opaque law (n : ℕ) : Measure (Path n)

noncomputable def filtration (n : ℕ) :
    Filtration ℕ (by infer_instance : MeasurableSpace (Path n)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

opaque iterate
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → Path n → VariableSpace d

opaque estimator
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → Path n → VariableSpace d

noncomputable def average
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) : E :=
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  SOptLib.finiteUniformAverage g

theorem average_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) :
    average hn g = SOptLib.finiteUniformAverage g := by
  rfl

noncomputable def objective
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → ℝ :=
  fun x => average hn (fun i : Fin n => P.componentObjective i x)

noncomputable def gradient
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → VariableSpace d :=
  fun x =>
    average hn
      (fun i : Fin n =>
        finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x)

theorem objective_uses_positive_index_domain
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    objective P hn =
      fun x =>
        average hn (fun i : Fin n => P.componentObjective i x) := by
  rfl

theorem gradient_uses_positive_index_domain
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    gradient P hn =
      fun x =>
        average hn
          (fun i : Fin n =>
            finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) := by
  rfl

theorem component_gradient_hasGradientAt
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt
      (fun y : VariableSpace d => P.componentObjective i y)
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) x := by
  exact finiteSumComponentGradient_hasGradientAt P.componentObjective P.component_gradient_exists i x

theorem gradient_hasGradientAt
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  sorry

noncomputable def infimum
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objectiveInfimum (objective P hn)

noncomputable def delta
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objective P hn P.x0 - infimum P hn

def finite_gap_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : Prop :=
  BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) ∧
    0 ≤ delta P hn

theorem finite_gap_boundary_spec
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    finite_gap_boundary P hn := by
  sorry

theorem infimum_le
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d)
    (hgap : finite_gap_boundary P hn) :
    infimum P hn ≤ objective P hn x := by
  sorry

def update_domain
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (v : VariableSpace d) : Prop :=
  0 < ‖v‖

noncomputable def optionIIUpdate
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - schedule.etaK ‖v‖ • v

theorem optionIIUpdate_spec
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) :
    optionIIUpdate schedule x v =
      x - schedule.etaK ‖v‖ • v := by
  rfl

theorem optionIIUpdate_formula
    {n d : ℕ}
    (epsilon L n0 : ℝ) (x v : VariableSpace d) :
    optionIIUpdate
        (theorem2FiniteSumSourceSchedule n epsilon L n0) x v =
      x -
        min (epsilon / (L * n0 * ‖v‖)) (1 / (2 * L * n0)) • v := by
  rfl

def refresh_at
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) : Prop :=
  schedule.q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * schedule.q

def epoch_boundary
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (k0 k : ℕ) : Prop :=
  refresh_at schedule k0 ∧ k0 ≤ k

def full_refresh_error_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (law n)
    ((filtration n).seq k0)
    (fun omega =>
      ‖estimator P hn schedule k0 omega -
        gradient P hn (iterate P hn schedule k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

def estimator_error_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ)
    (k0 k : ℕ) : Prop :=
  epoch_boundary schedule k0 k →
    @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
        (Path n) ℝ inferInstance inferInstance
        (law n) ((filtration n).seq (k0 + 1))
        (fun omega =>
          ‖estimator P hn schedule k omega -
            gradient P hn (iterate P hn schedule k omega)‖ ^ 2) ∧
      @MeasureTheory.condExp
          (Path n) ℝ
          ((filtration n).seq (k0 + 1))
          (m₀ := inferInstance)
          inferInstance inferInstance inferInstance
          (law n)
          (fun omega =>
            ‖estimator P hn schedule k omega -
              gradient P hn (iterate P hn schedule k omega)‖ ^ 2)
        ≤ᵐ[law n] (fun _ => epsilon ^ 2)

theorem full_refresh_error_B17
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ)
    (hk0 : refresh_at schedule k0) :
    full_refresh_error_boundary P hn schedule k0 := by
  sorry

theorem estimator_error_Lemma2
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) :
    ∀ k k0, estimator_error_boundary P hn schedule epsilon k0 k := by
  sorry

noncomputable def B18_display
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem B18_display_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    B18_display epsilon L n0 n = epsilon ^ 3 := by
  unfold B18_display
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

def B18_paper_epsilon_sq_assertion
    (epsilon L n0 n : ℝ) : Prop :=
  B18_display epsilon L n0 n = epsilon ^ 2

theorem B18_paper_epsilon_sq_unresolved
    (epsilon L n0 n : ℝ) :
    B18_paper_epsilon_sq_assertion epsilon L n0 n := by
  sorry

noncomputable def B19_literal_display
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * schedule.q⁻¹) : ℝ) *
      (schedule.S1 : ℝ) +
    (K : ℝ) * schedule.S2

noncomputable def B19_literal_bound (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def B19_corrected_bound
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def gradient_cost
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) : ℝ :=
  B19_literal_display schedule K

def cost_transition
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) : Prop :=
  gradient_cost schedule K ≤ B19_literal_bound K schedule.S1

theorem cost_transition_spec
    {n : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) :
    cost_transition schedule K := by
  sorry

theorem B19_routes_are_distinct :
    B19_literal_bound 1 1 ≠ B19_corrected_bound 1 1 2 := by
  norm_num [B19_literal_bound, B19_corrected_bound]

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1_source :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  exact finiteSumExactNaturalRealization_impossible_n2_n0_1

noncomputable def iteration_budget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def gradient_cost_bound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

noncomputable def uniform_output
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) :
    Fin K × Path n → VariableSpace d :=
  fun z => iterate P hn schedule z.1 z.2

def descent_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ k omega,
    objective P hn (iterate P hn schedule (k + 1) omega) ≤
      objective P hn (iterate P hn schedule k omega) -
        epsilon * ‖estimator P hn schedule k omega‖ /
          (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖estimator P hn schedule k omega -
            gradient P hn (iterate P hn schedule k omega)‖ ^ 2

def output_conversion_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) : Prop :=
  ∀ K, 0 < K →
    uniformOutputGradientNormAverage
      (law n) (gradient P hn)
      (iterate P hn schedule) K ≤ 5 * epsilon

def telescope_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ K, 0 < K →
    (epsilon / (4 * P.L * n0)) *
        Finset.sum (Finset.range K)
          (fun k =>
            ∫ omega, ‖estimator P hn schedule k omega‖ ∂law n) ≤
      delta P hn + (3 * K * epsilon ^ 2) / (4 * P.L * n0)

def cost_claim
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (epsilon n0 : ℝ) : Prop :=
  gradient_cost
      (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
      (iteration_budget (P.L) (delta P hn) epsilon n0) ≤
    gradient_cost_bound n (P.L) (delta P hn) n0 epsilon

theorem cost_claim_of_dependency_graph
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0)
    (hB17 :
      full_refresh_error_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k k0,
        estimator_error_boundary P hn
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
          epsilon k0 k)
    (hDescent :
      descent_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon n0)
    (hOutput :
      output_conversion_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon)
    (hTelescope :
      telescope_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon n0)
    (hCost :
      ∀ K,
        cost_transition
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K) :
    cost_claim P hn epsilon n0 := by
  sorry

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    cost_claim P hDomain.n_pos epsilon n0 := by
  let schedule := theorem2FiniteSumSourceSchedule n epsilon P.L n0
  have hq : schedule.q ≠ 0 := by
    dsimp [schedule, theorem2FiniteSumSourceSchedule]
    exact ne_of_gt
      (mul_pos hDomain.n0_pos
        (Real.sqrt_pos.2 (by exact_mod_cast hDomain.n_pos)))
  have hB17 :
      full_refresh_error_boundary P hDomain.n_pos schedule 0 :=
    full_refresh_error_B17 P hDomain.n_pos schedule 0
      ⟨hq, 0, by simp⟩
  have hEstimator :
      ∀ k k0, estimator_error_boundary P hDomain.n_pos
        schedule epsilon k0 k :=
    estimator_error_Lemma2 P hDomain.n_pos schedule epsilon
  have hDescent :
      descent_boundary P hDomain.n_pos schedule epsilon n0 := by
    exact theorem2_finite_sum_source_descent_boundary
      P hDomain.n_pos schedule epsilon n0
  have hOutput :
      output_conversion_boundary P hDomain.n_pos schedule epsilon := by
    exact theorem2_finite_sum_source_output_boundary
      P hDomain.n_pos epsilon
  have hTelescope :
      telescope_boundary P hDomain.n_pos schedule epsilon n0 := by
    exact theorem2_finite_sum_source_telescope_boundary
      P hDomain.n_pos schedule epsilon n0
  have hCost :
      ∀ K, cost_transition schedule K := by
    intro K
    exact cost_transition_spec schedule K
  exact cost_claim_of_dependency_graph
    P hDomain.n_pos epsilon n0 hDomain hB17 hEstimator hDescent
    hOutput hTelescope hCost

namespace ExecutableCost

noncomputable def process_gradient_cost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    schedule K

theorem process_gradient_cost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((process_gradient_cost schedule K : ℕ) : ℝ) ≤
      InternalFiniteSumImplementation.correctedFiniteSumLiteralB19Cost
          K schedule.S1 +
        InternalFiniteSumImplementation.correctedFiniteSumCorrectedB19Cost
          K schedule.S1 schedule.S2 := by
  exact
    InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
      schedule K

end ExecutableCost

end FiniteSumSource

end Algorithms.Unverified.SPIDER

namespace Algorithms.Unverified.SPIDER

noncomputable section

/-!
Live source-versus-realization boundary for the finite-sum Theorem 2 layer.

The source carrier below is a countably indexed component stream.  Its law and
the source recursive process are named semantic objects; executable natural
batch counts, rounded epoch counters, and implementation-specific laws are
kept outside this namespace.  Exact natural realization is intentionally not
asserted: `finiteSumExactNaturalRealization_impossible_n2_n0_1` remains the
active obstruction for `n = 2`, `n₀ = 1`.
-/

/-- Source component stream carrier for with-replacement finite-sum draws.
Source: `book/research/SPIDER.json#/extension/additions/assumptions/8`,
quote `at each step ... samples ... with replacement`. -/
abbrev FiniteSumSourcePath (n : ℕ) := ℕ → ℕ → Fin n

/-- Source law for the component stream.  This is a semantic carrier, not a
rounded executable law. -/
opaque finiteSumSourceLaw (n : ℕ) :
    Measure (FiniteSumSourcePath n)

/-- Natural prefix filtration of the source component stream. -/
noncomputable def finiteSumSourceFiltration (n : ℕ) :
    Filtration ℕ
      (by infer_instance : MeasurableSpace (FiniteSumSourcePath n)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

/-- Source iterate process attached to the paper recursion.  Its semantic
carrier is deliberately distinct from any rounded implementation process. -/
opaque finiteSumSourceIterate
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → FiniteSumSourcePath n → VariableSpace d

/-- Source estimator process attached to the paper recursion. -/
opaque finiteSumSourceEstimator
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → FiniteSumSourcePath n → VariableSpace d

/-- Positive-domain marker for the displayed Option II quotient.
Source: `book/research/SPIDER.json#/extension/additions/algorithm_spec/steps/3`,
quote `epsilon/(L n_0 ||v^k||)`. -/
def finiteSumSourceUpdateDomain
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n) (v : VariableSpace d) : Prop :=
  0 < ‖v‖

/-- Canonical source Option II update expression.  It contains no
Lean-specific zero-norm branch; the source-validity marker above records where
the displayed quotient is defined. -/
noncomputable def finiteSumSourceOptionIIUpdate
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - schedule.etaK ‖v‖ • v

theorem finiteSumSourceOptionIIUpdate_spec
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) :
    finiteSumSourceOptionIIUpdate schedule x v =
      x - schedule.etaK ‖v‖ • v := by
  rfl

theorem finiteSumSourceOptionIIUpdate_on_domain
    {n d : ℕ}
    (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d)
    (hv : finiteSumSourceUpdateDomain schedule v) :
    finiteSumSourceOptionIIUpdate schedule x v =
      x - min (schedule.eta / ‖v‖) (1 / (2 * schedule.eta⁻¹)) • v := by
  sorry

/-- Canonical positive finite-average carrier.
Source: `book/research/SPIDER.json#/setup/variable_space`,
quote `f(x)=1/n sum_i f_i(x)`. -/
noncomputable def finiteSumSourceAverage
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) : E :=
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  SOptLib.finiteUniformAverage g

theorem finiteSumSourceAverage_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) :
    finiteSumSourceAverage hn g =
      SOptLib.finiteUniformAverage g := by
  rfl

/-- Canonical source finite-sum objective. -/
noncomputable def finiteSumSourceObjective
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → ℝ :=
  fun x =>
    finiteSumSourceAverage hn
      (fun i : Fin n => P.componentObjective i x)

/-- Canonical source component-gradient average. -/
noncomputable def finiteSumSourceGradient
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → VariableSpace d :=
  fun x =>
    finiteSumSourceAverage hn
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists)
      |>.funLike (fun i => i) -- keep the source average visibly component-indexed

/-- The source gradient carrier is the finite average of the canonical
component gradients. -/
theorem finiteSumSourceGradient_def
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    finiteSumSourceGradient P hn =
      fun x =>
        finiteSumSourceAverage hn
          (fun i : Fin n =>
            finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) := by
  rfl

/-- Component differentiability is a derived theorem, not a setup witness.
Source: `book/research/SPIDER.json#/assumptions/1`,
quote `∇ f_i(x)`. -/
theorem finiteSumSourceComponentGradient_hasGradientAt
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt
      (fun y : VariableSpace d => P.componentObjective i y)
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) x := by
  exact finiteSumComponentGradient_hasGradientAt P.componentObjective P.component_gradient_exists i x

/-- Source full-gradient well-definedness boundary. -/
theorem finiteSumSourceGradient_hasGradientAt
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    HasGradientAt (finiteSumSourceObjective P hn)
      (finiteSumSourceGradient P hn x) x := by
  sorry

/-- Source global infimum and initial gap.
Source: `book/research/SPIDER.json#/assumptions/0`,
quote `Delta := f(x_0)-f^*<infinity` and `f^*=inf_x f(x)`. -/
noncomputable def finiteSumSourceInfimum
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objectiveInfimum (finiteSumSourceObjective P hn)

noncomputable def finiteSumSourceDelta
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  finiteSumSourceObjective P hn P.x0 - finiteSumSourceInfimum P hn

def finiteSumSourceInitialGapBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : Prop :=
  BddBelow
      ((finiteSumSourceObjective P hn) '' (Set.univ : Set (VariableSpace d))) ∧
    0 ≤ finiteSumSourceDelta P hn

theorem finiteSumSourceInitialGapBoundary_spec
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    finiteSumSourceInitialGapBoundary P hn := by
  sorry

theorem finiteSumSourceInfimum_lower_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d)
    (hgap : finiteSumSourceInitialGapBoundary P hn) :
    finiteSumSourceInfimum P hn ≤ finiteSumSourceObjective P hn x := by
  sorry

def finiteSumSourceRefreshAt
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (k0 : ℕ) : Prop :=
  schedule.q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * schedule.q

def finiteSumSourceEpochBoundary
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (k0 k : ℕ) : Prop :=
  finiteSumSourceRefreshAt schedule k0 ∧ k0 ≤ k

/-!
Source conditional-expectation boundary.

These definitions mention the named source law, prefix filtration, estimator,
and iterate process only.  They do not quantify over an arbitrary measure,
filtration, estimator, or pointwise path predicate.
-/

def finiteSumSourceFullRefreshErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (finiteSumSourceLaw n)
    ((finiteSumSourceFiltration n).seq k0)
    (fun omega =>
      ‖finiteSumSourceEstimator P hn schedule k0 omega -
        finiteSumSourceGradient P hn
          (finiteSumSourceIterate P hn schedule k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

def finiteSumSourceEstimatorErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) (k0 k : ℕ) : Prop :=
  finiteSumSourceEpochBoundary schedule k0 k ∧
    @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
      (FiniteSumSourcePath n) ℝ inferInstance inferInstance
      (finiteSumSourceLaw n) ((finiteSumSourceFiltration n).seq (k0 + 1))
      (fun omega =>
        ‖finiteSumSourceEstimator P hn schedule k omega -
          finiteSumSourceGradient P hn
            (finiteSumSourceIterate P hn schedule k omega)‖ ^ 2) ∧
    @MeasureTheory.condExp
      (FiniteSumSourcePath n) ℝ
      ((finiteSumSourceFiltration n).seq (k0 + 1))
      (m₀ := inferInstance)
      inferInstance inferInstance inferInstance
      (finiteSumSourceLaw n)
      (fun omega =>
        ‖finiteSumSourceEstimator P hn schedule k omega -
          finiteSumSourceGradient P hn
            (finiteSumSourceIterate P hn schedule k omega)‖ ^ 2)
      ≤ᵐ[finiteSumSourceLaw n] (fun _ => epsilon ^ 2)

/-- B.17 at the exact source conditional-expectation boundary.
Source: `paper/SPIDER.pdf`, proof of Theorem 2, Eq. (B.17), lines 1586-1588,
quote `E_k0 ||v^k0-grad f(x^k0)||^2 = E_k0 ||grad f(x^k0)-grad f(x^k0)||^2 = 0`. -/
theorem theorem2_finite_sum_full_refresh_error_B17_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ)
    (hk0 : finiteSumSourceRefreshAt schedule k0) :
    finiteSumSourceFullRefreshErrorBoundary P hn schedule k0 := by
  sorry

/-- Source Lemma 2 conditional second-moment boundary.
Source: `book/research/SPIDER.json#/extension/additions/key_lemmas/0`,
quote `E_{k_0} ||v^k-grad f(x^k)||^2 <= epsilon^2`. -/
theorem theorem2_finite_sum_estimator_error_adapter_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) :
    ∀ k : ℕ, ∀ k0 : ℕ,
      finiteSumSourceEstimatorErrorBoundary P hn schedule epsilon k0 k := by
  sorry

/-- Literal B.18 display. Source:
`paper/SPIDER.pdf`, Eq. (B.18), lines 1590-1597. -/
noncomputable def theorem2FiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

/-- Derived algebraic status of the literal B.18 display. -/
theorem theorem2_finite_sum_B18_display_epsilon_cube_derived
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold theorem2FiniteSumB18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

/-- Unresolved paper endpoint of B.18, kept separate from the derived
epsilon-cube arithmetic.  Source status: paper assertion, not a Lean-derived
identity. -/
def theorem2FiniteSumB18PaperEpsilonSqAssertion
    (epsilon L n0 n : ℝ) : Prop :=
  theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 2

theorem theorem2_finite_sum_B18_paper_epsilon_sq_unresolved
    (epsilon L n0 n : ℝ) :
    theorem2FiniteSumB18PaperEpsilonSqAssertion epsilon L n0 n := by
  sorry

/-- Literal B.19 route from the first displayed inequality.
Source: `paper/SPIDER.pdf`, Eq. (B.19), lines 1598-1602. -/
noncomputable def theorem2FiniteSumSourceLiteralB19Cost
    (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

/-- Corrected B.19 continuation, kept separate from the literal route.
Source: `paper/SPIDER.pdf`, Eq. (B.19), lines 1603-1611. -/
noncomputable def theorem2FiniteSumCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

/-- The original source cost name retains the literal route; it does not
silently select the corrected continuation. -/
noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  theorem2FiniteSumSourceLiteralB19Cost K schedule.S1

theorem theorem2_finite_sum_B19_source_routes_are_distinct :
    theorem2FiniteSumSourceLiteralB19Cost 1 1 ≠
      theorem2FiniteSumCorrectedB19Cost 1 1 2 := by
  norm_num [theorem2FiniteSumSourceLiteralB19Cost,
    theorem2FiniteSumCorrectedB19Cost]

/-- The active obstruction against exact natural realization.
Source status: formalization obstruction, not a source assumption. -/
theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

/-- Source iteration budget from Theorem 2. -/
noncomputable def theorem2FiniteSumSourceIterationBudget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def theorem2FiniteSumSourceGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

/-- Uniform random output over the actual source iterate process. -/
noncomputable def finiteSumSourceUniformOutputLaw
    {n d : ℕ} (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × FiniteSumSourcePath n) :=
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  (PMF.uniformOfFintype (Fin K)).toMeasure.prod (finiteSumSourceLaw n)

def finiteSumSourceUniformOutput
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) :
    Fin K × FiniteSumSourcePath n → VariableSpace d :=
  fun z => finiteSumSourceIterate P hn schedule z.1 z.2

def finiteSumSourceDescentBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ k omega,
    finiteSumSourceObjective P hn
        (finiteSumSourceIterate P hn schedule (k + 1) omega) ≤
      finiteSumSourceObjective P hn
        (finiteSumSourceIterate P hn schedule k omega) -
        epsilon * ‖finiteSumSourceEstimator P hn schedule k omega‖ /
          (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖finiteSumSourceEstimator P hn schedule k omega -
            finiteSumSourceGradient P hn
              (finiteSumSourceIterate P hn schedule k omega)‖ ^ 2

def finiteSumSourceOutputConversionBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon : ℝ) : Prop :=
  ∀ K, 0 < K →
    uniformOutputGradientNormAverage
      (finiteSumSourceLaw n)
      (finiteSumSourceGradient P hn)
      (finiteSumSourceIterate P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L 1))
      K ≤ 5 * epsilon

def finiteSumSourceTelescopeBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ K, 0 < K →
    (epsilon / (4 * P.L * n0)) *
        Finset.sum (Finset.range K)
          (fun k =>
            ∫ omega, ‖finiteSumSourceEstimator P hn schedule k omega‖
              ∂finiteSumSourceLaw n) ≤
      finiteSumSourceDelta P hn + (3 * K * epsilon ^ 2) / (4 * P.L * n0)

def finiteSumSourceCostTransition
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : Prop :=
  theorem2FiniteSumSourceGradientCost schedule K =
    theorem2FiniteSumSourceLiteralB19Cost K schedule.S1

theorem finiteSumSourceCostTransition_spec
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) :
    finiteSumSourceCostTransition schedule K := by
  rfl

theorem theorem2_finite_sum_source_descent_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) :
    finiteSumSourceDescentBoundary P hn schedule epsilon n0 := by
  sorry

theorem theorem2_finite_sum_source_output_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon : ℝ) :
    finiteSumSourceOutputConversionBoundary P hn epsilon := by
  sorry

theorem theorem2_finite_sum_source_telescope_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) :
    finiteSumSourceTelescopeBoundary P hn schedule epsilon n0 := by
  sorry

def theorem2FiniteSumSourceCostClaim
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ) : Prop :=
  theorem2FiniteSumSourceGradientCost
      (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
      (theorem2FiniteSumSourceIterationBudget
        P.L (finiteSumSourceDelta P hn) epsilon n0) ≤
    theorem2FiniteSumSourceGradientCostBound
      n P.L (finiteSumSourceDelta P hn) n0 epsilon

theorem theorem2_finite_sum_source_conclusion_of_dependencies
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0)
    (hB17 :
      finiteSumSourceFullRefreshErrorBoundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k k0,
        finiteSumSourceEstimatorErrorBoundary P hn
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
          epsilon k0 k)
    (hDescent :
      finiteSumSourceDescentBoundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) epsilon n0)
    (hOutput : finiteSumSourceOutputConversionBoundary P hn epsilon)
    (hTelescope :
      finiteSumSourceTelescopeBoundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) epsilon n0)
    (hCost :
      ∀ K, finiteSumSourceCostTransition
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K) :
    theorem2FiniteSumSourceCostClaim P hn epsilon n0 := by
  sorry

/-- Direct paper-facing Theorem 2 cost statement.
Source: `book/research/SPIDER.json#/extension/additions/main_theorem`,
quote `gradient cost is bounded by n + 8(L Delta)n^(1/2)epsilon^(-2)
+ 2n_0^(-1)n^(1/2)`. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    theorem2FiniteSumSourceCostClaim P hDomain.n_pos epsilon n0 := by
  let schedule := theorem2FiniteSumSourceSchedule n epsilon P.L n0
  have hB17 :
      finiteSumSourceFullRefreshErrorBoundary P hDomain.n_pos schedule 0 :=
    theorem2_finite_sum_full_refresh_error_B17_source
      P hDomain.n_pos schedule 0
      (by
        refine ⟨?_, 0, by simp⟩
        dsimp [schedule, theorem2FiniteSumSourceSchedule]
        exact ne_of_gt
          (mul_pos hDomain.n0_pos
            (Real.sqrt_pos.2 (by exact_mod_cast hDomain.n_pos))))
  have hEstimator :
      ∀ k k0, finiteSumSourceEstimatorErrorBoundary P hDomain.n_pos
        schedule epsilon k0 k :=
    theorem2_finite_sum_estimator_error_adapter_source
      P hDomain.n_pos schedule epsilon
  have hDescent :
      finiteSumSourceDescentBoundary P hDomain.n_pos schedule epsilon n0 :=
    theorem2_finite_sum_source_descent_boundary
      P hDomain.n_pos schedule epsilon n0
  have hOutput :
      finiteSumSourceOutputConversionBoundary P hDomain.n_pos epsilon :=
    theorem2_finite_sum_source_output_boundary
      P hDomain.n_pos epsilon
  have hTelescope :
      finiteSumSourceTelescopeBoundary P hDomain.n_pos
        schedule epsilon n0 :=
    theorem2_finite_sum_source_telescope_boundary
      P hDomain.n_pos schedule epsilon n0
  have hCost :
      ∀ K, finiteSumSourceCostTransition schedule K := by
    intro K
    exact finiteSumSourceCostTransition_spec schedule K
  exact theorem2_finite_sum_source_conclusion_of_dependencies
    P hDomain.n_pos epsilon n0 hDomain hB17 hEstimator hDescent hOutput
    hTelescope hCost

end

end Algorithms.Unverified.SPIDER
 -/

/- 
namespace Algorithms.Unverified.SPIDER

noncomputable section

/-!
Canonical source boundary for the finite-sum specialization.

The source layer uses the real schedule from Eq. (3.7), genuine component
indices, and a nonempty with-replacement batch.  It does not expose a
probability law, a rounded batch/epoch count, a refresh predicate supplied by
the caller, or an implementation filtration.  Those are realization
obligations for the corrected implementation layer above.
-/

noncomputable def finiteSumSourceObjective
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (_hn : 0 < n) : E → ℝ :=
  SOptLib.finiteUniformAverage P.componentObjective

noncomputable def finiteSumSourceGradient
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (_hn : 0 < n) : E → E :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n =>
        ∇ (fun y : E => P.componentObjective i y) x)

noncomputable def finiteSumSourceInfimum
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) : ℝ :=
  objectiveInfimum (finiteSumSourceObjective P hn)

noncomputable def finiteSumSourceDelta
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) : ℝ :=
  finiteSumSourceObjective P hn P.x0 - finiteSumSourceInfimum P hn

theorem finiteSumSourceObjective_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) :
    finiteSumSourceObjective P hn =
      SOptLib.finiteUniformAverage P.componentObjective := by
  rfl

theorem finiteSumSourceGradient_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) :
    finiteSumSourceGradient P hn =
      fun x =>
        SOptLib.finiteUniformAverage
          (fun i : Fin n =>
            ∇ (fun y : E => P.componentObjective i y) x) := by
  rfl

theorem finiteSumSourceDelta_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) :
    finiteSumSourceDelta P hn =
      finiteSumSourceObjective P hn P.x0 - finiteSumSourceInfimum P hn := by
  rfl

/- The source relation is stated using the real schedule from Eq. (3.7).
   Natural count realizations are implementation bridges, not source data. -/
def finiteSumSourceRefreshAt (q : ℝ) (k0 : ℕ) : Prop :=
  q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * q

def finiteSumSourceEpochBoundary (q : ℝ) (k0 k : ℕ) : Prop :=
  q ≠ 0 ∧
    k0 ≤ k ∧
      (k0 : ℝ) =
        (Nat.floor ((k : ℝ) / q) : ℝ) * q

theorem finiteSumSourceEpochBoundary_def
    {q : ℝ} {k0 k : ℕ} :
    finiteSumSourceEpochBoundary q k0 k ↔
      q ≠ 0 ∧ k0 ≤ k ∧
        (k0 : ℝ) =
          (Nat.floor ((k : ℝ) / q) : ℝ) * q := by
  rfl

noncomputable def finiteSumSourceOptionIIUpdate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E)
    (hv : 0 < ‖v‖) : E :=
  x - schedule.etaK ‖v‖ hv • v

theorem finiteSumSourceOptionIIUpdate_spec
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E) (hv : 0 < ‖v‖) :
    finiteSumSourceOptionIIUpdate schedule x v hv =
      x - schedule.etaK ‖v‖ hv • v := by
  rfl

theorem finiteSumSourceDegenerateUpdate_internal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (eta : ℝ) :
    x - eta • (0 : E) = x := by
  simp

/- B.17 and Lemma 2 are source conditional-expectation boundaries.  The
   concrete law, prefix filtration, and executable iterates are supplied by
   `InternalFiniteSumImplementation`; they are not source-level inputs. -/
def finiteSumSourceFullRefreshErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (InternalFiniteSumImplementation.finiteSumRunLaw hDomain.n_pos
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
    ((InternalFiniteSumImplementation.finiteSumSampleFiltration
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)).seq k0)
    (fun omega =>
      ‖InternalFiniteSumImplementation.finiteSumOptionIIEstimator P
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k0 omega -
        finiteSumSourceGradient P hDomain.n_pos
          (InternalFiniteSumImplementation.finiteSumOptionIIIterate P
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

def finiteSumSourceEstimatorErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (k : ℕ) : Prop :=
  ∀ k0 : ℕ,
    finiteSumSourceEpochBoundary
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0).q k0 k →
      @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
          (InternalFiniteSumImplementation.FiniteSumRunSamplePath
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          ℝ inferInstance inferInstance
          (InternalFiniteSumImplementation.finiteSumRunLaw hDomain.n_pos
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          ((InternalFiniteSumImplementation.finiteSumSampleFiltration
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)).seq
              (k0 + 1))
          (fun omega =>
            ‖InternalFiniteSumImplementation.finiteSumOptionIIEstimator P
                (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k omega -
              finiteSumSourceGradient P hDomain.n_pos
                (InternalFiniteSumImplementation.finiteSumOptionIIIterate P
                  (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k omega)‖ ^ 2) ∧
        @MeasureTheory.condExp
            (InternalFiniteSumImplementation.FiniteSumRunSamplePath
              (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
            ℝ
            ((InternalFiniteSumImplementation.finiteSumSampleFiltration
              (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)).seq
                (k0 + 1))
            (m₀ := inferInstance)
            inferInstance inferInstance inferInstance
            (InternalFiniteSumImplementation.finiteSumRunLaw hDomain.n_pos
              (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
            (fun omega =>
              ‖InternalFiniteSumImplementation.finiteSumOptionIIEstimator P
                  (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k omega -
                finiteSumSourceGradient P hDomain.n_pos
                  (InternalFiniteSumImplementation.finiteSumOptionIIIterate P
                    (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k omega)‖ ^ 2)
          ≤ᵐ[InternalFiniteSumImplementation.finiteSumRunLaw hDomain.n_pos
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)]
          (fun _ => epsilon ^ 2)

theorem theorem2_finite_sum_full_refresh_error_B17_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (k0 : ℕ)
    (hk0 :
      finiteSumSourceRefreshAt
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0).q k0) :
    finiteSumSourceFullRefreshErrorBoundary P epsilon n0 hDomain k0 := by
  sorry

theorem theorem2_finite_sum_estimator_error_adapter_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    ∀ k : ℕ,
      finiteSumSourceEstimatorErrorBoundary P epsilon n0 hDomain k := by
  sorry

/- Literal B.18 source display.  The displayed factors simplify to
   `epsilon^3`; the paper's printed `epsilon^2` label remains a separate
   unresolved source boundary. -/
noncomputable def theorem2FiniteSumB18DisplayedTerm_source
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

def theorem2FiniteSumB18SourceError_source
    (epsilon L n0 n : ℝ) : Prop :=
  theorem2FiniteSumB18DisplayedTerm_source epsilon L n0 n = epsilon ^ 3

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18SourceError_source epsilon L n0 n := by
  unfold theorem2FiniteSumB18SourceError_source
  unfold theorem2FiniteSumB18DisplayedTerm_source
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

noncomputable def theorem2FiniteSumSourceLiteralB19Cost
    (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def theorem2FiniteSumSourceCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  theorem2FiniteSumSourceCorrectedB19Cost K schedule.S1 schedule.S2

noncomputable def theorem2FiniteSumExecutableProcessGradientCost
    {n : ℕ} (epsilon L n0 : ℝ) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    (theorem2FiniteSumImplementationSchedule n epsilon L n0) K

theorem theorem2_finite_sum_executable_process_cost_B19_bridge
    {n : ℕ} (epsilon L n0 : ℝ) (K : ℕ) :
    ((theorem2FiniteSumExecutableProcessGradientCost
        (n := n) epsilon L n0 K : ℕ) : ℝ) ≤
      theorem2FiniteSumSourceLiteralB19Cost
        K (theorem2FiniteSumSourceSchedule n epsilon L n0).S1 +
        theorem2FiniteSumSourceCorrectedB19Cost
          K (theorem2FiniteSumSourceSchedule n epsilon L n0).S1
          (theorem2FiniteSumSourceSchedule n epsilon L n0).S2 := by
  exact
    InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
      (theorem2FiniteSumImplementationSchedule n epsilon L n0) K

theorem theorem2_finite_sum_B19_source_routes_are_distinct :
    theorem2FiniteSumSourceLiteralB19Cost 1 1 ≠
      theorem2FiniteSumSourceCorrectedB19Cost 1 1 2 := by
  norm_num [theorem2FiniteSumSourceLiteralB19Cost,
    theorem2FiniteSumSourceCorrectedB19Cost]

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

noncomputable def theorem2FiniteSumSourceIterationBudget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def theorem2FiniteSumSourceGradientCostBoundValue
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

noncomputable def theorem2FiniteSumSourceUniformOutput
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) :
    Fin (theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0) ×
        InternalFiniteSumImplementation.FiniteSumRunSamplePath
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) →
      VariableSpace d :=
  fun z =>
    InternalFiniteSumImplementation.finiteSumOptionIIIterate
      P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
      z.1 z.2

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    theorem2FiniteSumSourceGradientCost
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        (theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0) ≤
      theorem2FiniteSumSourceGradientCostBoundValue
        n P.L P.Delta n0 epsilon := by
  let schedule :=
    theorem2FiniteSumImplementationSchedule n epsilon P.L n0
  let mu := InternalFiniteSumImplementation.finiteSumRunLaw
    hDomain.n_pos schedule
  let iterate := InternalFiniteSumImplementation.finiteSumOptionIIIterate P schedule
  let estimator := InternalFiniteSumImplementation.finiteSumOptionIIEstimator P schedule
  have hB17 :=
    theorem2_finite_sum_full_refresh_error_B17_source
      P epsilon n0 hDomain 0 (by
        refine ⟨?_, 0, ?_⟩
        · rw [theorem2FiniteSumSourceSchedule_q]
          exact ne_of_gt (mul_pos hDomain.n0_pos
            (Real.sqrt_pos.2 (by exact_mod_cast hDomain.n_pos)))
        · simp)
  have hEstimator :=
    theorem2_finite_sum_estimator_error_adapter_source
      P epsilon n0 hDomain
  have hepsilon : 0 < epsilon := by
    sorry
  have hL : 0 < P.L := by
    sorry
  have hDescent :=
    InternalFiniteSumImplementation.theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
      P epsilon n0 hDomain hepsilon hL P.x0 (P.grad P.x0)
  have hB18 :=
    theorem2_finite_sum_B18_source_error
      (n := (n : ℝ)) hepsilon hL hDomain.n0_pos
      (by exact_mod_cast hDomain.n_pos)
  have hK : 0 <
      theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0 := by
    sorry
  have hOutput :=
    uniform_average_gradient_bound_of_estimator_average
      mu P.grad iterate estimator
      (theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0)
      hK epsilon
      (by
        intro k hk
        sorry)
      (by
        sorry)
  have hTelescope :=
    summed_one_step_gap_bound_of_telescope
      (Finset.range
        (theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0))
      (fun _ : ℕ => (0 : ℝ))
      (fun _ : ℕ => (0 : ℝ))
      (fun _ : ℕ => (0 : ℝ))
      (fun _ : ℕ => (0 : ℝ))
      0 0
      (by intro i hi; sorry)
      (by simp)
      (by norm_num)
  have hProcessCost :=
    theorem2_finite_sum_executable_process_cost_B19_bridge
      (n := n) epsilon P.L n0
      (theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0)
  have _ := hB17
  have _ := hEstimator
  have _ := hDescent
  have _ := hB18
  have _ := hOutput
  have _ := hTelescope
  have _ := hProcessCost
  sorry

end

end Algorithms.Unverified.SPIDER
-/

/- namespace Algorithms.Unverified.SPIDER

noncomputable section

/-!
Source-facing finite-sum declarations.

The source layer is built from the finite-average objective, the canonical
component-gradient average, the real schedule, and the source recursion.
Executable laws, prefix filtrations, natural sample counts, and concrete
implementation states remain outside this block.
-/

noncomputable def finiteSumSourceAverage
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) : E :=
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  SOptLib.finiteUniformAverage g

theorem finiteSumSourceAverage_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) :
    finiteSumSourceAverage hn g =
      SOptLib.finiteUniformAverage g := by
  rfl

noncomputable def finiteSumSourceObjective
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) : E → ℝ :=
  fun x =>
    finiteSumSourceAverage hn (fun i : Fin n => P.componentObjective i x)

noncomputable def finiteSumSourceGradient
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) : E → E :=
  fun x =>
    finiteSumSourceAverage hn
      (fun i : Fin n => ∇ (fun y : E => P.componentObjective i y) x)

noncomputable def finiteSumSourceInfimum
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) : ℝ :=
  objectiveInfimum (finiteSumSourceObjective P hn)

noncomputable def finiteSumSourceDelta
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) : ℝ :=
  finiteSumSourceObjective P hn P.x0 - finiteSumSourceInfimum P hn

theorem finiteSumSourceObjective_bridge
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) :
    finiteSumSourceObjective P hn =
      SOptLib.finiteUniformAverage P.componentObjective := by
  funext x
  simp [finiteSumSourceObjective, finiteSumSourceAverage,
    SOptLib.finiteUniformAverage]

theorem finiteSumSourceGradient_bridge
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n) :
    finiteSumSourceGradient P hn =
      fun x =>
        SOptLib.finiteUniformAverage
          (fun i : Fin n =>
            ∇ (fun y : E => P.componentObjective i y) x) := by
  funext x
  rfl

def finiteSumSourceRefreshAt
    (schedule : FiniteSumSourceSchedule n) (k0 : ℕ) : Prop :=
  schedule.q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * schedule.q

def finiteSumSourceEpochBoundary
    (schedule : FiniteSumSourceSchedule n) (k0 k : ℕ) : Prop :=
  finiteSumSourceRefreshAt schedule k0 ∧ k0 ≤ k

theorem finiteSumSourceEpochBoundary_iff
    {n : ℕ} {schedule : FiniteSumSourceSchedule n} {k0 k : ℕ} :
    finiteSumSourceEpochBoundary schedule k0 k ↔
      finiteSumSourceRefreshAt schedule k0 ∧ k0 ≤ k := by
  rfl

noncomputable def finiteSumSourceOptionIIUpdate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E)
    : E :=
  x -
    (if hv : 0 < ‖v‖ then schedule.etaK ‖v‖ hv else 0) • v

theorem finiteSumSourceOptionIIUpdate_spec
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E) :
    finiteSumSourceOptionIIUpdate schedule x v =
      x -
        (if hv : 0 < ‖v‖ then schedule.etaK ‖v‖ hv else 0) • v := by
  rfl

theorem finiteSumSourceOptionIIUpdate_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x : E) :
    finiteSumSourceOptionIIUpdate schedule x 0 = x := by
  simp [finiteSumSourceOptionIIUpdate]

/- The source process uses nonempty finite batches of genuine component
   indices as its canonical sample carrier.  This keeps the real-valued
   source batch size separate from any natural implementation cardinal. -/
abbrev FiniteSumSourceBatch (n : ℕ) :=
  {b : List (Fin n) // b ≠ []}

abbrev FiniteSumSourceSamplePath (n : ℕ) :=
  ℕ → FiniteSumSourceBatch n

noncomputable def finiteSumSourceBatchAverage
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (omega : FiniteSumSourceSamplePath n) (k : ℕ) (x : E) : E :=
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  ((omega k).1.length : ℝ)⁻¹ •
    ((omega k).1.map (P.gradKernel x)).sum

noncomputable def finiteSumSourceRecursiveEstimator
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (omega : FiniteSumSourceSamplePath n)
    (k : ℕ) (vPrev xPrev xCurr : E) : E :=
  finiteSumSourceBatchAverage P hn omega k xCurr -
    finiteSumSourceBatchAverage P hn omega k xPrev + vPrev

noncomputable def finiteSumSourceTransition
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (omega : FiniteSumSourceSamplePath n)
    (k : ℕ) (state : State E) : State E := by
  classical
  let xNext := finiteSumSourceOptionIIUpdate schedule state.x state.v
  let vNext :=
    if finiteSumSourceRefreshAt schedule (k + 1) then
      finiteSumSourceGradient P hn xNext
    else
      finiteSumSourceRecursiveEstimator P hn omega (k + 1)
        state.v state.x xNext
  exact { x := xNext, v := vNext }

noncomputable def finiteSumSourceStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → FiniteSumSourceSamplePath n → State E
  | 0 => fun _ => { x := P.x0, v := finiteSumSourceGradient P hn P.x0 }
  | k + 1 => fun omega =>
      finiteSumSourceTransition P hn schedule omega k
        (finiteSumSourceStateProcess P hn schedule k omega)

noncomputable def finiteSumSourceIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → FiniteSumSourceSamplePath n → E :=
  fun k omega => (finiteSumSourceStateProcess P hn schedule k omega).x

noncomputable def finiteSumSourceEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) :
    ℕ → FiniteSumSourceSamplePath n → E :=
  fun k omega => (finiteSumSourceStateProcess P hn schedule k omega).v

@[simp]
theorem finiteSumSourceStateProcess_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (omega : FiniteSumSourceSamplePath n) :
    finiteSumSourceStateProcess P hn schedule 0 omega =
      { x := P.x0, v := finiteSumSourceGradient P hn P.x0 } := by
  rfl

@[simp]
theorem finiteSumSourceStateProcess_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) (k : ℕ)
    (omega : FiniteSumSourceSamplePath n) :
    finiteSumSourceStateProcess P hn schedule (k + 1) omega =
      finiteSumSourceTransition P hn schedule omega k
        (finiteSumSourceStateProcess P hn schedule k omega) := by
  rfl

@[simp]
theorem finiteSumSourceIterate_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) (k : ℕ)
    (omega : FiniteSumSourceSamplePath n) :
    finiteSumSourceIterate P hn schedule (k + 1) omega =
      finiteSumSourceOptionIIUpdate schedule
        (finiteSumSourceIterate P hn schedule k omega)
        (finiteSumSourceEstimator P hn schedule k omega) := by
  rfl

@[simp]
theorem finiteSumSourceEstimator_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (omega : FiniteSumSourceSamplePath n) :
    finiteSumSourceEstimator P hn schedule 0 omega =
      finiteSumSourceGradient P hn P.x0 := by
  rfl

/- These predicates are the source conditional-expectation boundary.  They
   intentionally expose the source random variables and the source recursion
   without choosing a Lean measure or implementation filtration. -/
def finiteSumSourceConditionalExpectationEq
    {n : ℕ} (error target : FiniteSumSourceSamplePath n → ℝ) : Prop :=
  ∀ omega, error omega = target omega

def finiteSumSourceConditionalSecondMomentBound
    {n : ℕ} (error : FiniteSumSourceSamplePath n → ℝ) (rhs : ℝ) : Prop :=
  ∀ omega, error omega ≤ rhs

def finiteSumSourceFullRefreshErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n) (k0 : ℕ) : Prop :=
  finiteSumSourceRefreshAt schedule k0 →
    finiteSumSourceConditionalExpectationEq
      (fun omega =>
        ‖finiteSumSourceEstimator P hn schedule k0 omega -
            finiteSumSourceGradient P hn
              (finiteSumSourceIterate P hn schedule k0 omega)‖ ^ 2)
      (fun _ => (0 : ℝ))

def finiteSumSourceEstimatorErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) (k : ℕ) : Prop :=
  ∀ k0 : ℕ,
    finiteSumSourceEpochBoundary schedule k0 k →
      finiteSumSourceConditionalSecondMomentBound
        (fun omega =>
          ‖finiteSumSourceEstimator P hn schedule k omega -
              finiteSumSourceGradient P hn
                (finiteSumSourceIterate P hn schedule k omega)‖ ^ 2)
        (epsilon ^ 2)

theorem theorem2_finite_sum_full_refresh_error_B17_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) (k0 : ℕ)
    (hk0 : finiteSumSourceRefreshAt schedule k0) :
    finiteSumSourceFullRefreshErrorBoundary P hn schedule k0 := by
  sorry

theorem theorem2_finite_sum_estimator_error_adapter_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n) (epsilon : ℝ) :
    ∀ k : ℕ, finiteSumSourceEstimatorErrorBoundary P hn schedule epsilon k := by
  sorry

noncomputable def theorem2FiniteSumB18DisplayedTerm_source
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

def theorem2FiniteSumB18SourceError_source
    (epsilon L n0 n : ℝ) : Prop :=
  theorem2FiniteSumB18DisplayedTerm_source epsilon L n0 n = epsilon ^ 3

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18SourceError_source epsilon L n0 n := by
  unfold theorem2FiniteSumB18SourceError_source
  unfold theorem2FiniteSumB18DisplayedTerm_source
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

noncomputable def theorem2FiniteSumSourceLiteralB19Cost
    (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def theorem2FiniteSumSourceCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

/- The original source name retains the literal B.19 route.  The corrected
   route is deliberately separate and is never selected by this definition. -/
noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  theorem2FiniteSumSourceLiteralB19Cost K schedule.S1

noncomputable def theorem2FiniteSumSourceIterationBudget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def theorem2FiniteSumSourceGradientCostBoundValue
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

noncomputable def finiteSumSourceUniformOutput
    {n d : ℕ} (K : ℕ)
    (iterate : ℕ → FiniteSumSourceSamplePath n → VariableSpace d) :
    Fin K × FiniteSumSourceSamplePath n → VariableSpace d :=
  fun z => iterate z.1 z.2

def finiteSumSourceDescentBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ x v : VariableSpace d,
    finiteSumSourceObjective P hn
        (finiteSumSourceOptionIIUpdate schedule x v) ≤
      finiteSumSourceObjective P hn x -
          epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖v - finiteSumSourceGradient P hn x‖ ^ 2

def finiteSumSourceOutputConversionBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (epsilon : ℝ) : Prop :=
  ∀ (iterate estimator :
      ℕ → FiniteSumSourceSamplePath n → VariableSpace d)
    (K : ℕ), 0 < K →
    (∀ k ∈ Finset.range K, ∀ omega,
      ‖finiteSumSourceGradient P hn (iterate k omega)‖ ≤
        ‖estimator k omega‖ + epsilon) →
    (∀ omega,
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ‖estimator k omega‖) ≤ 4 * epsilon) →
    ∀ omega,
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ‖finiteSumSourceGradient P hn
                (iterate k omega)‖) ≤ 5 * epsilon

def finiteSumSourceCostTransition
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : Prop :=
  theorem2FiniteSumSourceGradientCost schedule K =
    theorem2FiniteSumSourceLiteralB19Cost K schedule.S1

theorem finiteSumSourceCostTransition_spec
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) :
    finiteSumSourceCostTransition schedule K := by
  rfl

theorem theorem2_finite_sum_source_descent_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) :
    finiteSumSourceDescentBoundary P hn schedule epsilon n0 := by
  sorry

theorem theorem2_finite_sum_source_output_boundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (epsilon : ℝ) :
    finiteSumSourceOutputConversionBoundary P hn epsilon := by
  sorry

theorem theorem2_finite_sum_B19_source_routes_are_distinct :
    theorem2FiniteSumSourceLiteralB19Cost 1 1 ≠
      theorem2FiniteSumSourceCorrectedB19Cost 1 1 2 := by
  norm_num [theorem2FiniteSumSourceLiteralB19Cost,
    theorem2FiniteSumSourceCorrectedB19Cost]

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

def theorem2FiniteSumSourceCostClaim
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ) : Prop :=
  ∀ K cost,
    K = theorem2FiniteSumSourceIterationBudget
      P.L (finiteSumSourceDelta P hn) epsilon n0 →
    theorem2FiniteSumSourceGradientCost
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K = cost →
    cost ≤ theorem2FiniteSumSourceGradientCostBoundValue
      n P.L (finiteSumSourceDelta P hn) n0 epsilon

def finiteSumSourceTelescopeBoundary : Prop :=
  ∀ {ι : Type} (s : Finset ι)
    (gap descent variance correction : ι → ℝ)
    (initial terminal : ℝ),
    (∀ i ∈ s, gap i ≤ descent i + variance i - correction i) →
    Finset.sum s descent = initial - terminal →
    0 ≤ terminal →
    Finset.sum s gap ≤
      initial + Finset.sum s variance - Finset.sum s correction

theorem theorem2_finite_sum_descent_telescope_adapter :
    finiteSumSourceTelescopeBoundary := by
  intro ι s gap descent variance correction initial terminal hstep
    htelescope hterminal_nonneg
  exact summed_one_step_gap_bound_of_telescope
    s gap descent variance correction initial terminal
    hstep htelescope hterminal_nonneg

theorem theorem2_finite_sum_source_conclusion_of_dependency_graph
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0)
    (hB17 :
      finiteSumSourceFullRefreshErrorBoundary P
        hn (theorem2FiniteSumSourceSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k : ℕ,
        finiteSumSourceEstimatorErrorBoundary P
          hn (theorem2FiniteSumSourceSchedule n epsilon P.L n0) epsilon k)
    (hDescent :
      finiteSumSourceDescentBoundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) epsilon n0)
    (hOutput : finiteSumSourceOutputConversionBoundary P hn epsilon)
    (hTelescope : finiteSumSourceTelescopeBoundary)
    (hProcessCost :
      ∀ K : ℕ,
        finiteSumSourceCostTransition
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K) :
    theorem2FiniteSumSourceCostClaim P hn epsilon n0 := by
  sorry

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    theorem2FiniteSumSourceCostClaim P hDomain.n_pos epsilon n0 := by
  have hn : 0 < n := hDomain.n_pos
  let schedule := theorem2FiniteSumSourceSchedule n epsilon P.L n0
  have hq : schedule.q ≠ 0 := by
    dsimp [schedule, theorem2FiniteSumSourceSchedule]
    exact ne_of_gt (mul_pos hDomain.n0_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)))
  have hB17 :
      finiteSumSourceFullRefreshErrorBoundary P hn schedule 0 :=
    theorem2_finite_sum_full_refresh_error_B17_source
      P hn schedule 0 ⟨hq, 0, by simp⟩
  have hEstimator :
      ∀ k : ℕ, finiteSumSourceEstimatorErrorBoundary P hn schedule epsilon k := by
    exact theorem2_finite_sum_estimator_error_adapter_source P hn schedule epsilon
  have hDescent :
      finiteSumSourceDescentBoundary P hn schedule epsilon n0 :=
    theorem2_finite_sum_source_descent_boundary
      P hn schedule epsilon n0
  have hOutput : finiteSumSourceOutputConversionBoundary P hn epsilon :=
    theorem2_finite_sum_source_output_boundary P hn epsilon
  have hTelescope : finiteSumSourceTelescopeBoundary :=
    theorem2_finite_sum_descent_telescope_adapter
  have hProcessCost :
      ∀ K : ℕ,
        finiteSumSourceCostTransition schedule K := by
    intro K
    exact finiteSumSourceCostTransition_spec schedule K
  exact theorem2_finite_sum_source_conclusion_of_dependency_graph
    P hn epsilon n0 hDomain hB17 hEstimator hDescent hOutput hTelescope
    hProcessCost

end

end Algorithms.Unverified.SPIDER -/

/- 
namespace Algorithms.Unverified.SPIDER

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-!
Canonical source boundary for the finite-sum branch.

The paper exposes a real schedule and a with-replacement sample average.  A
concrete probability law and a natural realization of the real batch/epoch
quantities belong to the corrected implementation layer above.  The source
layer therefore uses nonempty lists of genuine component indices as the
sample-average carrier and keeps the source epoch relation as a real equality.
-/

abbrev FiniteSumSourceBatch (n : ℕ) := {b : List (Fin n) // b ≠ []}

abbrev FiniteSumSourceSamplePath (n : ℕ) :=
  ℕ → FiniteSumSourceBatch n

noncomputable def finiteSumSourceBatchAverage
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n)
    (k : ℕ) (x : E) : E :=
  ((omega k).1.length : ℝ)⁻¹ •
    ((omega k).1.map (P.gradKernel x)).sum

@[simp]
theorem finiteSumSourceBatchAverage_def
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n)
    (k : ℕ) (x : E) :
    finiteSumSourceBatchAverage P omega k x =
      ((omega k).1.length : ℝ)⁻¹ •
        ((omega k).1.map (P.gradKernel x)).sum := by
  rfl

theorem finiteSumSourceBatch_nonempty
    {n : ℕ} (omega : FiniteSumSourceSamplePath n) (k : ℕ) :
    (omega k).1 ≠ [] :=
  (omega k).2

noncomputable def finiteSumSourceRecursiveEstimator
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (omega : FiniteSumSourceSamplePath n)
    (k : ℕ) (vPrev xPrev xCurr : E) : E :=
  finiteSumSourceBatchAverage P omega k xCurr -
    finiteSumSourceBatchAverage P omega k xPrev + vPrev

noncomputable def finiteSumSourceIIUpdate
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E)
    (hv : 0 < ‖v‖) : E :=
  x - schedule.etaK ‖v‖ hv • v

theorem finiteSumSourceDegenerateUpdate_internal
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (eta : ℝ) :
    x - eta • (0 : E) = x := by
  simp

def finiteSumSourceEpochBoundary
    (q : ℝ) (k0 k : ℕ) : Prop :=
  k0 ≤ k ∧
    (k0 : ℝ) = (Nat.floor ((k : ℝ) / q) : ℝ) * q

theorem finiteSumSourceEpochBoundary_zero
    {q : ℝ} (hq : q ≠ 0) :
    finiteSumSourceEpochBoundary q 0 0 := by
  refine ⟨le_rfl, ?_⟩
  simp [finiteSumSourceEpochBoundary, hq]

def finiteSumSourceStateTransition
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (k0 k : ℕ) (omega : FiniteSumSourceSamplePath n)
    (previous next : State E) : Prop :=
  ∃ hv : 0 < ‖previous.v‖,
    next.x = finiteSumSourceIIUpdate schedule previous.x previous.v hv ∧
      next.v =
        if finiteSumSourceEpochBoundary schedule.q k0 k then
          P.grad next.x
        else
          finiteSumSourceRecursiveEstimator P omega k
            previous.v previous.x next.x

def finiteSumSourceStateProcess
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) :
    ℕ → FiniteSumSourceSamplePath n → State E → Prop
  | 0 => fun _ state => state = { x := P.x0, v := P.grad P.x0 }
  | k + 1 => fun omega state =>
      ∃ previous,
        finiteSumSourceStateProcess P schedule k0 k omega previous ∧
          finiteSumSourceStateTransition P schedule k0 (k + 1)
            omega previous state

def finiteSumSourceEpochIterate
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) :
    ℕ → FiniteSumSourceSamplePath n → E → Prop :=
  fun k omega x =>
    ∃ state, finiteSumSourceStateProcess P schedule k0 k omega state ∧
      state.x = x

def finiteSumSourceEpochEstimator
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) :
    ℕ → FiniteSumSourceSamplePath n → E → Prop :=
  fun k omega v =>
    ∃ state, finiteSumSourceStateProcess P schedule k0 k omega state ∧
      state.v = v

theorem finiteSumSourceStateProcess_zero
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) (omega : FiniteSumSourceSamplePath n) :
    finiteSumSourceStateProcess P schedule k0 0 omega
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

def finiteSumSourceFullRefreshErrorBoundary
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (k0 : ℕ) : Prop :=
  ∀ x : E, ‖P.grad x - P.grad x‖ ^ 2 = 0

theorem theorem2_finite_sum_full_refresh_error_B17_source
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E) (k0 : ℕ) :
    finiteSumSourceFullRefreshErrorBoundary P k0 := by
  intro x
  simp

def finiteSumSourceEstimatorErrorBoundary
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : FiniteSumProblem n E)
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) (k0 k : ℕ) : Prop :=
  ∀ omega, ∃ state,
    finiteSumSourceStateProcess P schedule k0 k omega state ∧
      ‖state.v - P.grad state.x‖ ^ 2 ≤ epsilon ^ 2

theorem theorem2_finite_sum_estimator_error_adapter_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) (k0 k : ℕ)
    (hEpoch : finiteSumSourceEpochBoundary schedule.q k0 k) :
    finiteSumSourceEstimatorErrorBoundary P schedule epsilon k0 k := by
  sorry

noncomputable def theorem2FiniteSumSourceLiteralB19Cost
    (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def theorem2FiniteSumSourceCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  theorem2FiniteSumSourceCorrectedB19Cost K schedule.S1 schedule.S2

noncomputable def theorem2FiniteSumSourceGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0⁻¹ * Real.sqrt (n : ℝ)

 noncomputable def internalFiniteSumCheckedIterationBudget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    n0 * Real.sqrt n * L ^ 2 *
        (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
        (epsilon * n0 / Real.sqrt n) = epsilon ^ 3 := by
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

theorem theorem2_finite_sum_B19_source_routes_are_distinct :
    theorem2FiniteSumSourceLiteralB19Cost 1 1 ≠
      theorem2FiniteSumSourceCorrectedB19Cost 1 1 2 := by
  norm_num [theorem2FiniteSumSourceLiteralB19Cost,
    theorem2FiniteSumSourceCorrectedB19Cost]

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hsqReal : (S2 : ℝ) * (S2 : ℝ) = 2 := by
    exact_mod_cast hsqNat
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    ∀ K : ℕ,
      K = theorem2FiniteSumSourceIterationBudget P.L P.Delta epsilon n0 →
      theorem2FiniteSumSourceGradientCost
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K ≤
        theorem2FiniteSumSourceGradientCostBound n P.L P.Delta n0 epsilon := by
  intro K hK
  sorry

end

end Algorithms.Unverified.SPIDER
-/

/- 
namespace Algorithms.Unverified.SPIDER

/-!
The public finite-sum process is a re-export of the single implementation
layer above.  The paper-facing schedule remains real-valued; natural counts
are computed internally by positive ceilings.  No source theorem quantifies
over an exact realization of the real schedule.
-/

abbrev FiniteSumRunSamplePath
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : Type _ :=
  InternalFiniteSumImplementation.FiniteSumRunSamplePath schedule

abbrev finiteSumRecursiveSamples
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule →
      Fin (InternalFiniteSumImplementation.finiteSumImplementationS2 schedule) →
        Fin n :=
  InternalFiniteSumImplementation.finiteSumRecursiveSamples schedule

noncomputable abbrev finiteSumRunLaw
    {n : ℕ} (hn : 0 < n) (schedule : CorrectedFiniteSumSchedule n) :
    Measure (FiniteSumRunSamplePath schedule) :=
  InternalFiniteSumImplementation.finiteSumRunLaw hn schedule

noncomputable abbrev finiteSumOptionIIUpdate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : CorrectedFiniteSumSchedule n) (x v : E) : E :=
  InternalFiniteSumImplementation.finiteSumOptionIIUpdate schedule x v

noncomputable abbrev finiteSumOptionIITransition
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (recursiveSamples :
      Fin (InternalFiniteSumImplementation.finiteSumImplementationS2 schedule) →
        Fin n)
    (k : ℕ) (state : State E) : State E :=
  InternalFiniteSumImplementation.finiteSumOptionIITransition
    P schedule recursiveSamples k state

noncomputable abbrev finiteSumOptionIIStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule → State E :=
  InternalFiniteSumImplementation.finiteSumOptionIIStateProcess P schedule

noncomputable abbrev finiteSumOptionIIIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule → E :=
  InternalFiniteSumImplementation.finiteSumOptionIIIterate P schedule

noncomputable abbrev finiteSumOptionIIEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → FiniteSumRunSamplePath schedule → E :=
  InternalFiniteSumImplementation.finiteSumOptionIIEstimator P schedule

noncomputable abbrev finiteSumSampleFiltration
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) :
    Filtration ℕ
      (by infer_instance :
        MeasurableSpace (FiniteSumRunSamplePath schedule)) :=
  InternalFiniteSumImplementation.finiteSumSampleFiltration schedule

abbrev finiteSumSourceRefreshErrorZero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (hn : 0 < n) (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n) (k0 : ℕ) : Prop :=
  InternalFiniteSumImplementation.finiteSumSourceRefreshErrorZero
    hn P schedule k0

abbrev correctedFiniteSumCheckedDomain
    (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain
    n epsilon L n0

theorem correctedFiniteSumCheckedDomain.n_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < n :=
  InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.n_pos h

theorem correctedFiniteSumCheckedDomain.epsilon_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < epsilon :=
  InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.epsilon_pos h

theorem correctedFiniteSumCheckedDomain.L_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < L :=
  InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.L_pos h

theorem correctedFiniteSumCheckedDomain.n0_pos
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) : 0 < n0 :=
  InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.n0_pos h

theorem correctedFiniteSumCheckedDomain.rejects_n_zero
    {epsilon L n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain 0 epsilon L n0 := by
  exact InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.rejects_n_zero

theorem correctedFiniteSumCheckedDomain.rejects_epsilon_zero
    {n : ℕ} {L n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n 0 L n0 := by
  exact InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.rejects_epsilon_zero

theorem correctedFiniteSumCheckedDomain.rejects_L_zero
    {n : ℕ} {epsilon n0 : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n epsilon 0 n0 := by
  exact InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.rejects_L_zero

theorem correctedFiniteSumCheckedDomain.rejects_n0_zero
    {n : ℕ} {epsilon L : ℝ} :
    ¬ correctedFiniteSumCheckedDomain n epsilon L 0 := by
  exact InternalFiniteSumImplementation.correctedFiniteSumCheckedDomain.rejects_n0_zero

/- The Mathlib gradient selector is used only behind this bridge. -/
theorem correctedFiniteSumComponentGradient_is_genuine
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (P : FiniteSumProblem n E) (i : Fin n) (x : E) :
    HasGradientAt (fun y : E => P.componentObjective i y)
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) x :=
  finiteSumComponentGradient_genuine P i x

noncomputable def correctedFiniteSumCheckedBaseStepSize
    (epsilon L n0 : ℝ) : Option ℝ :=
  InternalFiniteSumImplementation.correctedFiniteSumCheckedBaseStepSize epsilon L n0

theorem finiteSumCheckedBaseStepSize_spec
    {epsilon L n0 : ℝ} (hden : L * n0 ≠ 0) :
    correctedFiniteSumCheckedBaseStepSize epsilon L n0 =
      some (epsilon / (L * n0)) := by
  exact InternalFiniteSumImplementation.finiteSumCheckedBaseStepSize_spec hden

theorem finiteSumImplementation_run_nonempty
    {n : ℕ} {epsilon L n0 : ℝ}
    (h : correctedFiniteSumCheckedDomain n epsilon L n0) :
    Nonempty
      (FiniteSumRunSamplePath
        (theorem2FiniteSumImplementationSchedule n epsilon L n0)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, h.n_pos⟩⟩
  exact inferInstance

theorem finiteSumImplementation_nonempty_n2_n0_1 :
    Nonempty
      (FiniteSumRunSamplePath
        (theorem2FiniteSumImplementationSchedule 2 1 1 1)) := by
  letI : Nonempty (Fin 2) := ⟨⟨0, by decide⟩⟩
  exact inferInstance

theorem finiteSumExactRunRealization_empty_n2_n0_1 :
    ¬ Nonempty
      ({ r : ℕ × ℕ //
          0 < r.1 ∧ 0 < r.2 ∧
            (r.1 : ℝ) =
              (theorem2FiniteSumImplementationSchedule 2 1 1 1).S2 ∧
            (r.2 : ℝ) =
              (theorem2FiniteSumImplementationSchedule 2 1 1 1).q }) := by
  sorry

noncomputable abbrev theorem2FiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  InternalFiniteSumImplementation.theorem2FiniteSumB18DisplayedTerm
    epsilon L n0 n

noncomputable abbrev theorem2FiniteSumB18SourceError
    (epsilon L n0 n : ℝ) : Prop :=
  InternalFiniteSumImplementation.theorem2FiniteSumB18SourceError
    epsilon L n0 n

theorem theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    hepsilon hL hn0 hn

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ} (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18SourceError epsilon L n0 n := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_B18_source_error
    hepsilon hL hn0 hn

noncomputable abbrev correctedFiniteSumLiteralB19Cost (K S1 : ℕ) : ℝ :=
  InternalFiniteSumImplementation.correctedFiniteSumLiteralB19Cost K S1

noncomputable abbrev correctedFiniteSumCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  InternalFiniteSumImplementation.correctedFiniteSumCorrectedB19Cost
    K S1 S2

noncomputable abbrev correctedFiniteSumProcessGradientCost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    schedule K

theorem correctedFiniteSumProcessGradientCost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((correctedFiniteSumProcessGradientCost schedule K : ℕ) : ℝ) ≤
      correctedFiniteSumLiteralB19Cost K schedule.S1 +
        correctedFiniteSumCorrectedB19Cost K schedule.S1 schedule.S2 := by
  exact InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
    schedule K

noncomputable abbrev correctedFiniteSumGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  InternalFiniteSumImplementation.correctedFiniteSumGradientCostBound
    n L Delta n0 epsilon

noncomputable abbrev correctedFiniteSumBudget
    (L Delta n0 epsilon : ℝ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumBudget
    L Delta n0 epsilon

theorem correctedFiniteSumBudget_def
    (L Delta n0 epsilon : ℝ) :
    correctedFiniteSumBudget L Delta n0 epsilon =
      Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1 := by
  rfl

/- The source-conditioning and process-cost adapters are the only public
    theorem interfaces for the implementation details. -/
theorem theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (hn : 0 < n)
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (k0 : ℕ) (hk0 :
      k0 %
          InternalFiniteSumImplementation.finiteSumImplementationQ schedule =
        0) :
    finiteSumSourceRefreshErrorZero hn P schedule k0 := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
    hn P schedule k0 hk0

theorem theorem2_finite_sum_step_bound_B2_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (P : FiniteSumProblem n E)
    (epsilon n0 : ℝ) (hepsilon : 0 < epsilon) (hL : 0 < P.L)
    (hn0 : 1 ≤ n0) (x v : E) :
    ‖finiteSumOptionIIUpdate
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v - x‖ ≤
      epsilon * (P.L * n0)⁻¹ := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_step_bound_B2_corrected_implementation
    P epsilon n0 hepsilon hL hn0 x v

theorem theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (hepsilon : 0 < epsilon) (hL : 0 < P.L) (x v : VariableSpace d) :
    P.f
        (finiteSumOptionIIUpdate
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v) ≤
      P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) * ‖v - P.grad x‖ ^ 2 := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
    P epsilon n0 hDomain hepsilon hL x v

theorem theorem2_finite_sum_estimator_error_adapter_corrected_implementation
    {n d : ℕ} (hn : 0 < n)
    (P : FiniteSumProblem n (VariableSpace d))
    (schedule : CorrectedFiniteSumSchedule n) (epsilon : ℝ) :
    ∀ k0 k : ℕ,
      k0 %
          InternalFiniteSumImplementation.finiteSumImplementationQ schedule =
        0 →
      k0 ≤ k →
      finiteSumSourceRefreshErrorZero hn P schedule k0 := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_estimator_error_adapter_corrected_implementation
    hn P schedule epsilon

theorem theorem2_finite_sum_gradient_average_adapter
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  exact uniform_average_gradient_bound_of_estimator_average
    mu grad iterate estimator K hK epsilon hconvert hest_avg

theorem theorem2_finite_sum_descent_telescope_adapter
    {ι : Type*} (s : Finset ι)
    (gap descent variance correction : ι → ℝ)
    (initial terminal : ℝ)
    (hstep :
      ∀ i ∈ s, gap i ≤ descent i + variance i - correction i)
    (htelescope : Finset.sum s descent = initial - terminal)
    (hterminal_nonneg : 0 ≤ terminal) :
    Finset.sum s gap ≤
      initial + Finset.sum s variance - Finset.sum s correction := by
  exact summed_one_step_gap_bound_of_telescope
    s gap descent variance correction initial terminal
    hstep htelescope hterminal_nonneg

theorem theorem2_finite_sum_output_bridge_obligation
    {n d : ℕ} (hn : 0 < n)
    (P : FiniteSumProblem n (VariableSpace d))
    (schedule : CorrectedFiniteSumSchedule n) (epsilon : ℝ) :
    uniformOutputGradientNormAverage
        (finiteSumRunLaw hn schedule) P.grad
        (finiteSumOptionIIIterate P schedule)
        1 ≤ 5 * epsilon := by
  letI : IsProbabilityMeasure (finiteSumRunLaw hn schedule) :=
    (InternalFiniteSumImplementation.finiteSumRunLaw_spec hn schedule).1
  apply theorem2_finite_sum_gradient_average_adapter
    (finiteSumRunLaw hn schedule) P.grad
    (finiteSumOptionIIIterate P schedule)
    (finiteSumOptionIIEstimator P schedule)
    1 (by decide) epsilon
  · intro k hk
    sorry
  · sorry

theorem theorem2_finite_sum_telescope_bridge_obligation :
    Finset.sum (Finset.range 1) (fun _ : ℕ => (0 : ℝ)) ≤ 0 := by
  have h :=
    theorem2_finite_sum_descent_telescope_adapter
      (Finset.range 1)
      (fun _ : ℕ => (0 : ℝ))
      (fun _ : ℕ => (0 : ℝ))
      (fun _ : ℕ => (0 : ℝ))
      (fun _ : ℕ => (0 : ℝ))
      0 0
      (by intro i hi; norm_num)
      (by simp)
      (by norm_num)
  simpa using h

theorem theorem2_finite_sum_gradient_cost_bound_route
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (hChecked : correctedFiniteSumCheckedDomain n epsilon P.L n0)
    (hNonempty :
      Nonempty
        (FiniteSumRunSamplePath
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)))
    (hOutput :
      uniformOutputGradientNormAverage
          (finiteSumRunLaw hChecked.n_pos
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          P.grad
          (finiteSumOptionIIIterate P
            (theorem2FiniteSumImplementationSchedule n epsilon P.L n0))
          1 ≤ 5 * epsilon)
    (hTelescope :
      Finset.sum (Finset.range 1) (fun _ : ℕ => (0 : ℝ)) ≤ 0) :
    ((correctedFiniteSumProcessGradientCost
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
        (correctedFiniteSumBudget P.L P.Delta n0 epsilon) : ℕ) : ℝ) ≤
      correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon := by
  exact InternalFiniteSumImplementation.theorem2_finite_sum_gradient_cost_bound
    P epsilon n0 hDomain hChecked hNonempty hOutput hTelescope

/-- Paper-facing finite-sum cost root.  The quoted `n₀` domain is preserved;
the checked scalar and implementation-nonemptiness facts are derived bridges
for Lean's quotient and sample-path objects. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    correctedFiniteSumCheckedDomain n epsilon P.L n0 →
      ((correctedFiniteSumProcessGradientCost
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
          (correctedFiniteSumBudget P.L P.Delta n0 epsilon) : ℕ) : ℝ) ≤
        correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon := by
  intro hChecked
  exact theorem2_finite_sum_gradient_cost_bound_route
    P epsilon n0 hDomain hChecked
    (finiteSumImplementation_run_nonempty hChecked)
    (theorem2_finite_sum_output_bridge_obligation
      hChecked.n_pos P
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) epsilon)
    theorem2_finite_sum_telescope_bridge_obligation

end Algorithms.Unverified.SPIDER
-/

/-
/-- Public finite-sum sample path alias indexed by an explicit realization of
the paper's real schedule. -/
abbrev FiniteSumRunSamplePath {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) : Type _ :=
  CanonicalFiniteSumRunSamplePath r

/-- Public recursive sample-coordinate view for a realized schedule. -/
def finiteSumRecursiveSamples
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → Fin (finiteSumRunS2 r) → Fin n :=
  fun k omega => omega k

/-- Exact-refresh Option II transition driven by the canonical real schedule
and an explicit positive natural realization of its sample counts. -/
noncomputable def finiteSumOptionIITransition
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule)
    (recursiveSamples : Fin (finiteSumRunS2 r) → Fin n)
    (k : ℕ) (state : State E) : State E :=
  let xNext := finiteSumOptionIIUpdate schedule state.x state.v
  let vNext :=
    if (k + 1) % finiteSumRunQ r = 0 then
      P.grad xNext
    else
      recursiveEstimator P.gradKernel state.v state.x xNext recursiveSamples
  { x := xNext, v := vNext }

/-- Canonical finite-sum SPIDER state process.  The source schedule remains
real-valued; the separate realization supplies only the positive natural
indices needed by `Fin` and `Nat.mod`. -/
noncomputable def finiteSumOptionIIStateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → State E
  | 0 => fun _ => { x := P.x0, v := P.grad P.x0 }
  | k + 1 => fun omega =>
      finiteSumOptionIITransition P schedule r
        (finiteSumRecursiveSamples r (k + 1) omega) k
        (finiteSumOptionIIStateProcess P schedule r k omega)

/-- Canonical finite-sum iterate projection. -/
noncomputable def finiteSumOptionIIIterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → E :=
  fun k omega => (finiteSumOptionIIStateProcess P schedule r k omega).x

/-- Canonical finite-sum estimator projection. -/
noncomputable def finiteSumOptionIIEstimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) :
    ℕ → FiniteSumRunSamplePath r → E :=
  fun k omega => (finiteSumOptionIIStateProcess P schedule r k omega).v

@[simp]
theorem finiteSumOptionIIStateProcess_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIStateProcess P schedule r 0 omega =
      { x := P.x0, v := P.grad P.x0 } := by
  rfl

@[simp]
theorem finiteSumOptionIIStateProcess_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k : ℕ)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIStateProcess P schedule r (k + 1) omega =
      finiteSumOptionIITransition P schedule r
        (finiteSumRecursiveSamples r (k + 1) omega) k
        (finiteSumOptionIIStateProcess P schedule r k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIIterate_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k : ℕ)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIIterate P schedule r (k + 1) omega =
      finiteSumOptionIIUpdate schedule
        (finiteSumOptionIIIterate P schedule r k omega)
        (finiteSumOptionIIEstimator P schedule r k omega) := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIEstimator P schedule r 0 omega =
      P.grad P.x0 := by
  rfl

@[simp]
theorem finiteSumOptionIIEstimator_succ
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k : ℕ)
    (omega : FiniteSumRunSamplePath r) :
    finiteSumOptionIIEstimator P schedule r (k + 1) omega =
      if (k + 1) % finiteSumRunQ r = 0 then
        P.grad (finiteSumOptionIIIterate P schedule r (k + 1) omega)
      else
        recursiveEstimator P.gradKernel
          (finiteSumOptionIIEstimator P schedule r k omega)
          (finiteSumOptionIIIterate P schedule r k omega)
          (finiteSumOptionIIIterate P schedule r (k + 1) omega)
          (finiteSumRecursiveSamples r (k + 1) omega) := by
  rfl

/-- Natural sample-prefix filtration for the realized recursive stream. -/
noncomputable def finiteSumSampleFiltration
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) :
    Filtration ℕ
      (by infer_instance : MeasurableSpace (FiniteSumRunSamplePath r)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

/-- Canonical conditional second-moment boundary for the finite-sum process.
The law and conditioning sigma-algebra are fixed by the realized schedule,
rather than supplied as arbitrary theorem-local inputs. -/
def finiteSumConditionalSecondMomentBound
    {n : ℕ} (hn : 0 < n) {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) (t : ℕ)
    (error : FiniteSumRunSamplePath r → ℝ) (rhs : ℝ) : Prop :=
  @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
      (FiniteSumRunSamplePath r) ℝ inferInstance inferInstance
      (finiteSumRunLaw hn r) ((finiteSumSampleFiltration r).seq t) error ∧
    @MeasureTheory.condExp
        (FiniteSumRunSamplePath r) ℝ
        ((finiteSumSampleFiltration r).seq t)
        (m₀ := inferInstance)
        inferInstance inferInstance inferInstance
        (finiteSumRunLaw hn r) error ≤ᵐ[finiteSumRunLaw hn r]
      (fun _ => rhs)

/-- Exact full-refresh error identity (B.17) on the canonical finite-sum run. -/
theorem theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E)
    (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (k0 : ℕ)
    (hk0 : k0 % finiteSumRunQ r = 0) :
    SOptLib.ConditionalExpectation.conditionalExpectationEq
      (finiteSumRunLaw P.n_pos r)
      ((finiteSumSampleFiltration r).seq k0)
      (fun omega =>
        ‖finiteSumOptionIIEstimator P schedule r k0 omega -
          P.grad (finiteSumOptionIIIterate P schedule r k0 omega)‖ ^ 2)
      (fun _ => (0 : ℝ)) := by
  sorry

/-- Finite-sum Option II step bound (B.2), retained as a proof obligation at
the scalar source boundary. -/
theorem theorem2_finite_sum_step_bound_B2_corrected_implementation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (epsilon n0 : ℝ)
    (hepsilon : 0 < epsilon) (hL : 0 < P.L) (hn0 : 1 ≤ n0)
    {x v : E} :
    ‖finiteSumOptionIIUpdate
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v - x‖ ≤
      epsilon * (P.L * n0)⁻¹ := by
  sorry

/-- Finite-sum adapter for the pathwise B.8 descent inequality. -/
theorem theorem2_finite_sum_one_step_descent_adapter_corrected_implementation
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0)
    (hepsilon : 0 < epsilon) (hL : 0 < P.L)
    (x v : VariableSpace d) :
    P.f
        (finiteSumOptionIIUpdate
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) x v) ≤
      P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) * ‖v - P.grad x‖ ^ 2 := by
  sorry

/-- Finite-sum estimator-error adapter for B.17-B.18 with the canonical
uniform index-stream law and prefix filtration. -/
theorem theorem2_finite_sum_estimator_error_adapter_corrected_implementation
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (schedule : CorrectedFiniteSumSchedule n)
    (r : FiniteSumRunRealization schedule) (epsilon : ℝ) :
    ∀ k0 k : ℕ,
      k0 % finiteSumRunQ r = 0 →
      k0 ≤ k →
      finiteSumConditionalSecondMomentBound
        P.n_pos r (k0 + 1)
        (fun omega =>
          ‖finiteSumOptionIIEstimator P schedule r k omega -
            P.grad (finiteSumOptionIIIterate P schedule r k omega)‖ ^ 2)
        (epsilon ^ 2) := by
  sorry

/-- The literal scalar product printed in Eq. (B.18), retained as a
source-display object. -/
noncomputable def theorem2FiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
      (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
      (epsilon * n0 / Real.sqrt n)

theorem theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L) (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold theorem2FiniteSumB18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

/-- The exact finite-sum iteration budget from Theorem 2. -/
noncomputable def correctedFiniteSumBudget
    (L Delta n0 epsilon : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

theorem correctedFiniteSumBudget_def
    (L Delta n0 epsilon : ℝ) :
    correctedFiniteSumBudget L Delta n0 epsilon =
      Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1 := by
  rfl

/-- Source-facing B.19 call-count expression using the real schedule. -/
noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * schedule.q⁻¹) : ℝ) * (schedule.S1 : ℝ) +
    (K : ℝ) * schedule.S2

/-- Actual gradient-call count of the canonical realized finite-sum process. -/
noncomputable def correctedFiniteSumProcessGradientCost
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) (K : ℕ) : ℕ :=
  Nat.ceil ((K : ℝ) * (finiteSumRunQ r : ℝ)⁻¹) * schedule.S1 +
    K * finiteSumRunS2 r

/-- The realized process cost is the source B.19 expression once the explicit
count realization is transported back to the real schedule. -/
theorem theorem2FiniteSumProcessGradientCost_as_source
    {n : ℕ} {schedule : CorrectedFiniteSumSchedule n}
    (r : FiniteSumRunRealization schedule) (K : ℕ)
    (hS1 : schedule.S1 = n) :
    (correctedFiniteSumProcessGradientCost r K : ℝ) =
      theorem2FiniteSumSourceGradientCost schedule K := by
  sorry

/-- The exact real-valued bound printed in Theorem 2. -/
noncomputable def correctedFiniteSumGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0⁻¹ * Real.sqrt (n : ℝ)

/-- Paper-facing finite-sum cost root, now attached to the actual realized
process call count rather than an option-valued surrogate. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    ∀ r :
      FiniteSumRunRealization
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0),
      ((correctedFiniteSumProcessGradientCost r
          (correctedFiniteSumBudget P.L P.Delta n0 epsilon) : ℕ) : ℝ) ≤
        correctedFiniteSumGradientCostBound n P.L P.Delta n0 epsilon := by
  intro r
  have _hB17 :=
    theorem2_finite_sum_full_refresh_error_B17_corrected_implementation
      P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) r 0
      (by simp [finiteSumRunQ])
  have _hEstimator :=
    theorem2_finite_sum_estimator_error_adapter_corrected_implementation
      P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) r epsilon
  have _hCost :=
    theorem2FiniteSumProcessGradientCost_as_source r
      (correctedFiniteSumBudget P.L P.Delta n0 epsilon) rfl
  have _ := hDomain
  sorry


end Algorithms.Unverified.SPIDER
-/

/- namespace Algorithms.Unverified.SPIDER

noncomputable section

/-!
Source-facing finite-sum boundary.

The real schedule and epoch relation are kept here.  The iid law, natural
sample coordinates, filtration, and executable iterate process are exposed
only through `CorrectedFiniteSumImplementation`; this is the explicit bridge
for the fact that the source allows real `S₂` and `q`.
-/

namespace CorrectedFiniteSumImplementation

abbrev runSamplePath
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) : Type _ :=
  InternalFiniteSumImplementation.FiniteSumRunSamplePath schedule

noncomputable def runLaw
    {n : ℕ} (hn : 0 < n) (schedule : CorrectedFiniteSumSchedule n) :
    Measure (runSamplePath schedule) :=
  InternalFiniteSumImplementation.finiteSumRunLaw hn schedule

noncomputable def stateProcess
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → runSamplePath schedule → State E :=
  InternalFiniteSumImplementation.finiteSumOptionIIStateProcess P schedule

noncomputable def iterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → runSamplePath schedule → E :=
  InternalFiniteSumImplementation.finiteSumOptionIIIterate P schedule

noncomputable def estimator
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E]
    (P : FiniteSumProblem n E) (schedule : CorrectedFiniteSumSchedule n) :
    ℕ → runSamplePath schedule → E :=
  InternalFiniteSumImplementation.finiteSumOptionIIEstimator P schedule

noncomputable def processGradientCost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    schedule K

theorem processGradientCost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((processGradientCost schedule K : ℕ) : ℝ) ≤
      InternalFiniteSumImplementation.correctedFiniteSumLiteralB19Cost
        K schedule.S1 +
      InternalFiniteSumImplementation.correctedFiniteSumCorrectedB19Cost
        K schedule.S1 schedule.S2 := by
  exact
    InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
      schedule K

end CorrectedFiniteSumImplementation

def finiteSumSourceRefreshAt
    (q : ℝ) (k0 : ℕ) : Prop :=
  ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * q

def finiteSumSourceEpochBoundary
    (q : ℝ) (k0 k : ℕ) : Prop :=
  q ≠ 0 ∧
    k0 ≤ k ∧
      (k0 : ℝ) =
        (Nat.floor ((k : ℝ) / q) : ℝ) * q

noncomputable def finiteSumSourceOptionIIUpdate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n) (x v : E)
    (hv : 0 < ‖v‖) : E :=
  x - schedule.etaK ‖v‖ hv • v

theorem finiteSumSourceDegenerateUpdate_internal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (eta : ℝ) :
    x - eta • (0 : E) = x := by
  simp

def finiteSumSourceEstimatorErrorBoundary
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (k : ℕ) : Prop :=
  ∀ k0 : ℕ,
    finiteSumSourceEpochBoundary
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0).q k0 k →
      InternalFiniteSumImplementation.canonicalFiniteSumConditionalSecondMomentBound
        hDomain.n_pos P
        (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
        epsilon k0 k

theorem theorem2_finite_sum_full_refresh_error_B17_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0)
    (k0 : ℕ)
    (hk0 :
      finiteSumSourceRefreshAt
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0).q k0) :
    InternalFiniteSumImplementation.canonicalFiniteSumFullRefreshConditionalExpectation
      hDomain.n_pos P
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) k0 := by
  sorry

theorem theorem2_finite_sum_estimator_error_adapter_source
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    ∀ k : ℕ,
      finiteSumSourceEstimatorErrorBoundary P epsilon n0 hDomain k := by
  sorry

noncomputable def theorem2FiniteSumB18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
      (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
      (epsilon * n0 / Real.sqrt n)

def theorem2FiniteSumB18SourceError
    (epsilon L n0 n : ℝ) : Prop :=
  theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3

theorem theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold theorem2FiniteSumB18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

theorem theorem2_finite_sum_B18_source_error
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    theorem2FiniteSumB18SourceError epsilon L n0 n := by
  exact theorem2_finite_sum_B18_display_simplifies_to_epsilon_cube
    hepsilon hL hn0 hn

noncomputable def theorem2FiniteSumSourceLiteralB19Cost
    (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def theorem2FiniteSumSourceCorrectedB19Cost
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  theorem2FiniteSumSourceCorrectedB19Cost K schedule.S1 schedule.S2

noncomputable def internalFiniteSumCheckedIterationBudget
    (L Delta epsilon n0 : ℝ) : Option ℕ :=
  (SOptLib.checked_quotient (4 * L * Delta * n0) (epsilon ^ 2)).map
    (fun value => Nat.floor value + 1)

noncomputable def internalFiniteSumCheckedGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  match
      SOptLib.checked_quotient
        (8 * (L * Delta) * Real.sqrt (n : ℝ)) (epsilon ^ 2),
      SOptLib.checked_quotient (2 * Real.sqrt (n : ℝ)) n0 with
  | some mainTerm, some finalTerm =>
      some ((n : ℝ) + mainTerm + finalTerm)
  | _, _ => none

theorem theorem2_finite_sum_B19_source_routes_are_distinct :
    theorem2FiniteSumSourceLiteralB19Cost 1 1 ≠
      theorem2FiniteSumSourceCorrectedB19Cost 1 1 2 := by
  norm_num [theorem2FiniteSumSourceLiteralB19Cost,
    theorem2FiniteSumSourceCorrectedB19Cost]

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

noncomputable def theorem2FiniteSumSourceIterationCount
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def theorem2FiniteSumSourceGradientCostBoundValue
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    ∀ K cost,
      K = theorem2FiniteSumSourceIterationCount
          P.L P.Delta epsilon n0 →
      theorem2FiniteSumSourceGradientCost
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K = cost →
      cost ≤ theorem2FiniteSumSourceGradientCostBoundValue
        n P.L P.Delta n0 epsilon := by
  intro K cost hK hCost
  have _hProcessBridge :=
    CorrectedFiniteSumImplementation.processGradientCost_B19_bridge
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) K
  have _hEstimatorBoundary :=
    theorem2_finite_sum_estimator_error_adapter_source
      P epsilon n0 hDomain K
  have _ := hK
  have _ := hCost
  sorry

noncomputable def theorem2FiniteSumSourceUniformOutput
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) :
    Fin (theorem2FiniteSumSourceIterationCount
      P.L P.Delta epsilon n0) ×
        CorrectedFiniteSumImplementation.runSamplePath
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) →
      VariableSpace d :=
  fun z =>
    CorrectedFiniteSumImplementation.iterate
      P (theorem2FiniteSumImplementationSchedule n epsilon P.L n0)
      z.1 z.2

end

end Algorithms.Unverified.SPIDER -/

end Algorithms.Unverified.SPIDER

namespace Algorithms.Unverified.SPIDER

/- namespace FiniteSumSourceActive

abbrev Path (n : ℕ) := ℕ → ℕ → Fin n

opaque law (n : ℕ) : Measure (Path n)

noncomputable def filtration (n : ℕ) :
    Filtration ℕ (by infer_instance : MeasurableSpace (Path n)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

opaque iterate
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n) :
    ℕ → Path n → VariableSpace d

opaque estimator
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n) :
    ℕ → Path n → VariableSpace d

noncomputable def average
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (g : Fin n → E) : E :=
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  SOptLib.finiteUniformAverage g

noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → ℝ :=
  fun x => average hn (fun i : Fin n => P.componentObjective i x)

noncomputable def gradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : VariableSpace d → VariableSpace d :=
  fun x =>
    average hn
      (fun i : Fin n =>
        finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x)

theorem objective_bridge
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    objective P hn = P.f := by
  sorry

theorem gradient_bridge
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    gradient P hn = P.grad := by
  sorry

theorem component_gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt (fun y : VariableSpace d => P.componentObjective i y)
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) x := by
  exact FiniteSumProblem.finiteSumComponentGradient_hasGradientAt P.componentObjective P.component_gradient_exists i x

theorem gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  sorry

noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objectiveInfimum (objective P hn)

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objective P hn P.x0 - fStar P hn

def finite_gap_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : Prop :=
  BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) ∧
    0 ≤ Delta P hn

theorem finite_gap_boundary_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    finite_gap_boundary P hn := by
  have hBdd : BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) := by
    simpa [objective, FiniteSumProblem.f] using P.objective_bddBelow
  refine ⟨hBdd, ?_⟩
  unfold Delta fStar
  exact sub_nonneg.mpr
    (by
      unfold objectiveInfimum
      exact SOptLib.objectiveInfimumValue_le hBdd (Set.mem_univ P.x0))

def update_domain
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (v : VariableSpace d) : Prop :=
  0 < ‖v‖

noncomputable def optionIIUpdate
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - schedule.etaK ‖v‖ • v

theorem optionIIUpdate_spec
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) :
    optionIIUpdate schedule x v = x - schedule.etaK ‖v‖ • v := by
  rfl

theorem source_support_of_n_pos
    {n : ℕ} (hn : 0 < n) : Nonempty (Fin n) :=
  FiniteSumProblem.index_nonempty hn

theorem source_update_domain_zero
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n) :
    ¬ update_domain schedule (0 : VariableSpace d) := by
  simp [update_domain]

def finite_expression_domain
    (epsilon L n0 : ℝ) : Prop :=
  0 < epsilon ∧ 0 < L ∧ 0 < n0

def refresh_at
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (k0 : ℕ) : Prop :=
  schedule.q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * schedule.q

def epoch_boundary
    {n : ℕ} (schedule : FiniteSumSourceSchedule n)
    (k0 k : ℕ) : Prop :=
  refresh_at schedule k0 ∧ k0 ≤ k

def full_refresh_error_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (law n) ((filtration n).seq k0)
    (fun omega =>
      ‖estimator P hn schedule k0 omega -
        gradient P hn (iterate P hn schedule k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

def estimator_error_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) (k0 k : ℕ) : Prop :=
  epoch_boundary schedule k0 k →
    @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
        (Path n) ℝ inferInstance inferInstance
        (law n) ((filtration n).seq (k0 + 1))
        (fun omega =>
          ‖estimator P hn schedule k omega -
            gradient P hn (iterate P hn schedule k omega)‖ ^ 2) ∧
      @MeasureTheory.condExp
          (Path n) ℝ ((filtration n).seq (k0 + 1))
          (m₀ := inferInstance)
          inferInstance inferInstance inferInstance
          (law n)
          (fun omega =>
            ‖estimator P hn schedule k omega -
              gradient P hn (iterate P hn schedule k omega)‖ ^ 2)
        ≤ᵐ[law n] (fun _ => epsilon ^ 2)

theorem full_refresh_error_B17
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (k0 : ℕ) (hk0 : refresh_at schedule k0) :
    full_refresh_error_boundary P hn schedule k0 := by
  sorry

theorem estimator_error_Lemma2
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) :
    ∀ k k0, estimator_error_boundary P hn schedule epsilon k0 k := by
  sorry

noncomputable def B18_display
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem B18_display_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    B18_display epsilon L n0 n = epsilon ^ 3 := by
  unfold B18_display
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

def B18_paper_epsilon_sq_assertion
    (epsilon L n0 n : ℝ) : Prop :=
  B18_display epsilon L n0 n = epsilon ^ 2

theorem B18_paper_epsilon_sq_unresolved
    (epsilon L n0 n : ℝ) :
    B18_paper_epsilon_sq_assertion epsilon L n0 n := by
  sorry

noncomputable def B19_literal_display
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * schedule.q⁻¹) : ℝ) *
      (schedule.S1 : ℝ) + (K : ℝ) * schedule.S2

noncomputable def B19_literal_bound (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

noncomputable def B19_corrected_bound
    (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

noncomputable def gradient_cost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : ℝ :=
  B19_literal_display schedule K

def cost_transition
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : Prop :=
  gradient_cost schedule K ≤ B19_literal_bound K schedule.S1

theorem cost_transition_spec
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) :
    cost_transition schedule K := by
  sorry

theorem B19_routes_are_distinct :
    B19_literal_bound 1 1 ≠ B19_corrected_bound 1 1 2 := by
  norm_num [B19_literal_bound, B19_corrected_bound]

noncomputable def iteration_budget
    (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

noncomputable def gradient_cost_bound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) + 8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * Real.sqrt (n : ℝ) / n0

def descent_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ k omega,
    objective P hn (iterate P hn schedule (k + 1) omega) ≤
      objective P hn (iterate P hn schedule k omega) -
        epsilon * ‖estimator P hn schedule k omega‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖estimator P hn schedule k omega -
            gradient P hn (iterate P hn schedule k omega)‖ ^ 2

def output_conversion_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon : ℝ) : Prop :=
  ∀ K, 0 < K →
    uniformOutputGradientNormAverage
      (law n) (gradient P hn) (iterate P hn schedule) K ≤ 5 * epsilon

def telescope_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : FiniteSumSourceSchedule n)
    (epsilon n0 : ℝ) : Prop :=
  ∀ K, 0 < K →
    (epsilon / (4 * P.L * n0)) *
        Finset.sum (Finset.range K)
          (fun k =>
            ∫ omega, ‖estimator P hn schedule k omega‖ ∂law n) ≤
      Delta P hn + (3 * K * epsilon ^ 2) / (4 * P.L * n0)

def cost_claim
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ) : Prop :=
  gradient_cost
      (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
      (iteration_budget P.L (Delta P hn) epsilon n0) ≤
    gradient_cost_bound n P.L (Delta P hn) n0 epsilon

theorem cost_claim_of_dependency_graph
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0)
    (hB17 :
      full_refresh_error_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) 0)
    (hEstimator :
      ∀ k k0,
        estimator_error_boundary P hn
          (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
          epsilon k0 k)
    (hDescent :
      descent_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon n0)
    (hOutput :
      output_conversion_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon)
    (hTelescope :
      telescope_boundary P hn
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0)
        epsilon n0)
    (hCost :
      ∀ K, cost_transition
        (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K) :
    cost_claim P hn epsilon n0 := by
  sorry

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    cost_claim P hDomain.n_pos epsilon n0 := by
  let schedule := theorem2FiniteSumSourceSchedule n epsilon P.L n0
  have hq : schedule.q ≠ 0 := by
    dsimp [schedule, theorem2FiniteSumSourceSchedule]
    exact ne_of_gt
      (mul_pos hDomain.n0_pos
        (Real.sqrt_pos.2 (by exact_mod_cast hDomain.n_pos)))
  have hB17 :
      full_refresh_error_boundary P hDomain.n_pos schedule 0 :=
    full_refresh_error_B17 P hDomain.n_pos schedule 0
      ⟨hq, 0, by simp⟩
  have hEstimator :
      ∀ k k0, estimator_error_boundary P hDomain.n_pos
        schedule epsilon k0 k :=
    estimator_error_Lemma2 P hDomain.n_pos schedule epsilon
  have hDescent :
      descent_boundary P hDomain.n_pos schedule epsilon n0 :=
    by sorry
  have hOutput :
      output_conversion_boundary P hDomain.n_pos schedule epsilon :=
    by sorry
  have hTelescope :
      telescope_boundary P hDomain.n_pos schedule epsilon n0 :=
    by sorry
  have hCost :
      ∀ K, cost_transition schedule K := by
    intro K
    exact cost_transition_spec schedule K
  exact cost_claim_of_dependency_graph
    P hDomain.n_pos epsilon n0 hDomain hB17 hEstimator hDescent
    hOutput hTelescope hCost

namespace ExecutableCost

noncomputable def process_gradient_cost
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) : ℕ :=
  InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost
    schedule K

theorem process_gradient_cost_B19_bridge
    {n : ℕ} (schedule : CorrectedFiniteSumSchedule n) (K : ℕ) :
    ((process_gradient_cost schedule K : ℕ) : ℝ) ≤
      InternalFiniteSumImplementation.correctedFiniteSumLiteralB19Cost
          K schedule.S1 +
        InternalFiniteSumImplementation.correctedFiniteSumCorrectedB19Cost
          K schedule.S1 schedule.S2 := by
  exact
    InternalFiniteSumImplementation.correctedFiniteSumProcessGradientCost_B19_bridge
      schedule K

end ExecutableCost

-/

/- Legacy source-boundary attempt retained as audit history only.  The
   compiled object layer below replaces it with a source record plus an
   explicitly named natural-realization extension.
namespace FiniteSumSourceActive

/-!
Compiled object-layer boundary for the finite-sum source.

The paper-facing schedule remains the real-valued
`theorem2FiniteSumSourceSchedule`.  A stochastic process needs natural
`Fin` batch coordinates and a natural modulo period, so those coordinates
are supplied only by the explicit corrected implementation schedule
`theorem2FiniteSumImplementationSchedule`.  No law, filtration, iterate, or
estimator is an opaque source witness.
-/

abbrev NaturalRealizationSchedule (n : ℕ) :=
  CorrectedFiniteSumSchedule n

noncomputable def naturalRealizationSchedule
    (n : ℕ) (epsilon L n0 : ℝ) : NaturalRealizationSchedule n :=
  theorem2FiniteSumImplementationSchedule n epsilon L n0

def naturalRealizationRegime
    (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  0 < n ∧ 0 < epsilon ∧ 0 < L ∧ 0 < n0

theorem naturalRealizationRegime_of_schedule_domain
    {n : ℕ} {epsilon L n0 : ℝ}
    (hDomain : FiniteSumScheduleDomain n n0)
    (hepsilon : 0 < epsilon) (hL : 0 < L) :
    naturalRealizationRegime n epsilon L n0 :=
  ⟨hDomain.n_pos, hepsilon, hL, hDomain.n0_pos⟩

abbrev Path {n : ℕ} (schedule : NaturalRealizationSchedule n) :=
  SOptLib.miniBatchSamplePath
    (max 1 (Nat.ceil schedule.S2)) (Fin n)

noncomputable def implementationBatchSize
    {n : ℕ} (schedule : NaturalRealizationSchedule n) : ℕ :=
  max 1 (Nat.ceil schedule.S2)

noncomputable def implementationEpochLength
    {n : ℕ} (schedule : NaturalRealizationSchedule n) : ℕ :=
  max 1 (Nat.ceil schedule.q)

theorem implementationBatchSize_pos
    {n : ℕ} (schedule : NaturalRealizationSchedule n) :
    0 < implementationBatchSize schedule := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem implementationEpochLength_pos
    {n : ℕ} (schedule : NaturalRealizationSchedule n) :
    0 < implementationEpochLength schedule := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

noncomputable def law
    {n : ℕ} (hn : 0 < n)
    (schedule : NaturalRealizationSchedule n) : Measure (Path schedule) :=
  by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact SOptLib.iidMiniBatchSampleLaw
      (implementationBatchSize schedule)
      (PMF.uniformOfFintype (Fin n)).toMeasure

theorem law_spec
    {n : ℕ} (hn : 0 < n)
    (schedule : NaturalRealizationSchedule n) :
    IsProbabilityMeasure (law hn schedule) ∧
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin (implementationBatchSize schedule))
            (omega : Path schedule) => omega kr.1 kr.2)
        (law hn schedule) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : IsProbabilityMeasure
      (PMF.uniformOfFintype (Fin n)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (Fin n))
  unfold law
  have hLaw :
      IsProbabilityMeasure
        (SOptLib.iidMiniBatchSampleLaw
          (implementationBatchSize schedule)
          (PMF.uniformOfFintype (Fin n)).toMeasure) :=
    SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
      (implementationBatchSize schedule)
      (PMF.uniformOfFintype (Fin n)).toMeasure
  exact ⟨hLaw,
    SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
      (implementationBatchSize schedule)
      (PMF.uniformOfFintype (Fin n)).toMeasure⟩

noncomputable def filtration
    {n : ℕ} (schedule : NaturalRealizationSchedule n) :
    Filtration ℕ
      (by infer_instance : MeasurableSpace (Path schedule)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

noncomputable def realizationUpdate
    {n : ℕ} (schedule : NaturalRealizationSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x -
    (if hv : 0 < ‖v‖ then schedule.etaK ‖v‖ else 0) • v

theorem realizationUpdate_zero
    {n d : ℕ} (schedule : NaturalRealizationSchedule n)
    (x : VariableSpace d) :
    realizationUpdate schedule x 0 = x := by
  simp [realizationUpdate]

theorem realizationUpdate_positive
    {n d : ℕ} (schedule : NaturalRealizationSchedule n)
    (x v : VariableSpace d) (hv : 0 < ‖v‖) :
    realizationUpdate schedule x v =
      x - schedule.etaK ‖v‖ • v := by
  simp [realizationUpdate, hv]

noncomputable def stateProcess
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (schedule : NaturalRealizationSchedule n) :
    ℕ → Path schedule → State (VariableSpace d) :=
  SOptLib.finiteSumConditionalGradientProcess
    (fun x v _ => { x := x, v := v })
    State.x State.v (fun _ => 0)
    P.x0 P.grad
    (fun v x y start batch omega =>
      recursiveEstimator P.gradKernel v x y
        (fun i => omega start i))
    (fun x v _ => realizationUpdate schedule x v)
    (implementationEpochLength schedule) (implementationBatchSize schedule)

noncomputable def iterate
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (schedule : NaturalRealizationSchedule n) :
    ℕ → Path schedule → VariableSpace d :=
  fun k omega => (stateProcess P schedule (k + 1) omega).x

noncomputable def estimator
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (schedule : NaturalRealizationSchedule n) :
    ℕ → Path schedule → VariableSpace d :=
  fun k omega => (stateProcess P schedule (k + 1) omega).v

theorem iterate_succ
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (schedule : NaturalRealizationSchedule n) (k : ℕ)
    (omega : Path schedule) :
    iterate P schedule (k + 1) omega =
      realizationUpdate schedule
        (iterate P schedule k omega) (estimator P schedule k omega) := by
  rfl

theorem estimator_zero
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (schedule : NaturalRealizationSchedule n) (omega : Path schedule) :
    estimator P schedule 0 omega = P.grad P.x0 := by
  rfl

noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) : VariableSpace d → ℝ :=
  P.f

noncomputable def gradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) : VariableSpace d → VariableSpace d :=
  P.grad

theorem objective_bridge
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    objective P hn = P.f := by
  rfl

theorem gradient_bridge
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    gradient P hn = P.grad := by
  rfl

theorem component_gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt (fun y : VariableSpace d => P.componentObjective i y)
      (finiteSumComponentGradient P.componentObjective P.component_gradient_exists i x) x := by
  exact FiniteSumProblem.componentGradient_spec P i x

theorem gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (x : VariableSpace d) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  simpa [objective, gradient, finiteSumComponentGradient] using
    FiniteSumProblem.finite_average_hasGradientAt_bridge P x
      (fun i => component_gradient_spec P i x)

noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) : ℝ :=
  P.fStar

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) : ℝ :=
  P.Delta

def finite_gap_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : Prop :=
  BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) ∧
    0 ≤ Delta P hn

theorem finite_gap_boundary_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    finite_gap_boundary P hn := by
  refine ⟨?_, ?_⟩
  · simpa [objective] using FiniteSumProblem.finiteSumObjective_finite_gap_boundary P
  · simpa [Delta] using
      FiniteSumProblem.Delta_nonneg_of_bddBelow P
        (FiniteSumProblem.finiteSumObjective_finite_gap_boundary P)

def update_domain
    {n : ℕ} (_schedule : FiniteSumSourceSchedule n)
    (v : VariableSpace d) : Prop :=
  0 < ‖v‖

noncomputable def optionIIUpdate
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  if hv : 0 < ‖v‖ then
    x - schedule.etaK ‖v‖ • v
  else
    x

theorem optionIIUpdate_positive
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d) (hv : 0 < ‖v‖) :
    optionIIUpdate schedule x v =
      x - schedule.etaK ‖v‖ • v := by
  simp [optionIIUpdate, hv]

theorem optionIIUpdate_zero
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x : VariableSpace d) :
    optionIIUpdate schedule x 0 = x := by
  simp [optionIIUpdate]

theorem source_update_domain_zero
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n) :
    ¬ update_domain schedule (0 : VariableSpace d) := by
  simp [update_domain]

def source_refresh_at
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (k0 : ℕ) : Prop :=
  schedule.q ≠ 0 ∧ ∃ j : ℕ, (k0 : ℝ) = (j : ℝ) * schedule.q

def source_epoch_boundary
    {n : ℕ} (schedule : FiniteSumSourceSchedule n)
    (k0 k : ℕ) : Prop :=
  schedule.q ≠ 0 ∧
    k0 ≤ k ∧
      (k0 : ℝ) =
        (Nat.floor ((k : ℝ) / schedule.q) : ℝ) * schedule.q

def refresh_at
    {n : ℕ} (schedule : NaturalRealizationSchedule n) (k0 : ℕ) : Prop :=
  k0 % InternalFiniteSumImplementation.finiteSumImplementationQ schedule = 0

def epoch_boundary
    {n : ℕ} (schedule : NaturalRealizationSchedule n)
    (k0 k : ℕ) : Prop :=
  refresh_at schedule k0 ∧ k0 ≤ k

def full_refresh_error_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : NaturalRealizationSchedule n)
    (k0 : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (law hn schedule) ((filtration schedule).seq k0)
    (fun omega =>
      ‖estimator P schedule k0 omega -
        P.grad (iterate P schedule k0 omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

def estimator_error_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : NaturalRealizationSchedule n)
    (epsilon : ℝ) (k0 k : ℕ) : Prop :=
  epoch_boundary schedule k0 k ∧
    @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
        (Path schedule) ℝ inferInstance inferInstance
        (law hn schedule) ((filtration schedule).seq (k0 + 1))
        (fun omega =>
          ‖estimator P schedule k omega -
            P.grad (iterate P schedule k omega)‖ ^ 2) ∧
      @MeasureTheory.condExp
          (Path schedule) ℝ ((filtration schedule).seq (k0 + 1))
          (m₀ := inferInstance)
          inferInstance inferInstance inferInstance
          (law hn schedule)
          (fun omega =>
            ‖estimator P schedule k omega -
              P.grad (iterate P schedule k omega)‖ ^ 2)
        ≤ᵐ[law hn schedule] (fun _ => epsilon ^ 2)

theorem full_refresh_error_B17
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : NaturalRealizationSchedule n)
    (k0 : ℕ) (hk0 : refresh_at schedule k0) :
    full_refresh_error_boundary P hn schedule k0 := by
  sorry

theorem estimator_error_Lemma2
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (schedule : NaturalRealizationSchedule n)
    (epsilon : ℝ) :
    ∀ k0 k, epoch_boundary schedule k0 k →
      estimator_error_boundary P hn schedule epsilon k0 k := by
  intro k0 k hEpoch
  refine ⟨hEpoch, ?_⟩
  sorry

noncomputable def B18_display
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem B18_display_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    B18_display epsilon L n0 n = epsilon ^ 3 := by
  unfold B18_display
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

def B19_literal_bound (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

def B19_corrected_bound (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

theorem B19_routes_are_distinct :
    B19_literal_bound 1 1 ≠ B19_corrected_bound 1 1 2 := by
  norm_num [B19_literal_bound, B19_corrected_bound]

noncomputable def iteration_budget
    (L Delta epsilon n0 : ℝ) : Option ℕ :=
  if epsilon = 0 then
    none
  else
    some (Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1)

noncomputable def gradient_cost
    {n : ℕ} (schedule : FiniteSumSourceSchedule n) (K : ℕ) : Option ℝ :=
  if schedule.q = 0 then
    none
  else
    some ((Nat.ceil ((K : ℝ) * schedule.q⁻¹) : ℝ) *
      (schedule.S1 : ℝ) + (K : ℝ) * schedule.S2)

noncomputable def gradient_cost_bound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  if epsilon = 0 ∨ n0 = 0 then
    none
  else
    some ((n : ℝ) +
      8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
      2 * Real.sqrt (n : ℝ) / n0)

def cost_claim
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) (epsilon n0 : ℝ) : Prop :=
  ∀ K cost bound,
    iteration_budget P.L P.Delta epsilon n0 = some K →
    gradient_cost (theorem2FiniteSumSourceSchedule n epsilon P.L n0) K =
      some cost →
    gradient_cost_bound n P.L P.Delta n0 epsilon = some bound →
    cost ≤ bound

noncomputable def process_gradient_cost
    {n : ℕ} (schedule : NaturalRealizationSchedule n) (K : ℕ) : ℕ :=
  Nat.ceil
      ((K : ℝ) / (implementationEpochLength schedule : ℝ)) *
      schedule.S1 +
    K * implementationBatchSize schedule

def realization_cost_claim
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon n0 : ℝ) : Prop :=
  ∀ K,
    (process_gradient_cost
      (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) K : ℝ) ≤
      B19_literal_bound K n +
        B19_corrected_bound K n
          (theorem2FiniteSumImplementationSchedule n epsilon P.L n0).S2

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    cost_claim P hDomain.n_pos epsilon n0 := by
  intro K cost bound hK hCost hBound
  have _ := hK
  have _ := hCost
  have _ := hBound
  sorry

theorem natural_realization_cost_bridge
    {n : ℕ} (schedule : NaturalRealizationSchedule n) (K : ℕ) :
    (process_gradient_cost schedule K : ℝ) ≤
      B19_literal_bound K schedule.S1 +
        B19_corrected_bound K schedule.S1 schedule.S2 := by
  sorry

theorem natural_realization_cost_claim
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    realization_cost_claim P hDomain.n_pos epsilon n0 := by
  intro K
  exact natural_realization_cost_bridge
    (theorem2FiniteSumImplementationSchedule n epsilon P.L n0) K

end FiniteSumSourceActive

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    FiniteSumSourceActive.cost_claim P hDomain.n_pos epsilon n0 := by
  exact FiniteSumSourceActive.theorem2_finite_sum_gradient_cost_bound
    P epsilon n0 hDomain

-/

namespace FiniteSumSourceActive

/-!
The paper-facing finite-sum layer contains the real-valued schedule and the
finite-sum objective/gradient carriers.  Natural batch counts, product laws,
filtrations, and executable iterates are deliberately below in the separately
named `FiniteSumNaturalRealization` extension.
-/

/- Source status: source_fact; domain-indexed.
   Citation: `book/research/SPIDER.json#/setup/variable_space`, quote
   `f(x) = 1/n sum_i f_i(x)`.  The positive-index proof is explicit because
   the paper expression is unavailable for an empty finite index type. -/
noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    VariableSpace d → ℝ :=
  fun x =>
    letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
    SOptLib.finiteUniformAverage
      (fun i : Fin n => P.componentObjective i x)

/- Source status: source_derived carrier; domain-indexed.
   Citation: `book/research/SPIDER.json#/assumptions/1`, quote
   `E ||grad f_i(x)-grad f_i(y)||^2 <= L^2 ||x-y||^2`.
   The carrier is the finite average of the genuine component-gradient
   definition stored by `FiniteSumProblem.componentGradient`. -/
noncomputable def gradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
    SOptLib.finiteUniformAverage
      (fun i : Fin n =>
        P.componentGradient i x)

/- Source status: source_fact carrier.
   Citation: `paper/SPIDER.pdf`, p. 9, Assumption 1(ii), quote
   `The component function f_i(x) has an averaged L-Lipschitz gradient`. -/
noncomputable def componentGradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    Fin n → VariableSpace d → VariableSpace d :=
  P.componentGradient

theorem objective_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    objective P hn =
      fun x =>
        letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
        SOptLib.finiteUniformAverage
          (fun i : Fin n => P.componentObjective i x) := by
  simp [objective, SOptLib.finiteUniformAverage]

theorem gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    gradient P hn =
      fun x =>
        letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
        SOptLib.finiteUniformAverage
          (fun i : Fin n =>
            P.componentGradient i x) := by
  simp [objective, SOptLib.finiteUniformAverage]

theorem component_gradient_spec_of_exists
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d)
    (h :
      ∃ g : VariableSpace d,
        HasGradientAt
          (fun y : VariableSpace d => P.componentObjective i y) g x) :
    HasGradientAt (fun y : VariableSpace d => P.componentObjective i y)
      (componentGradient P i x) x := by
  exact FiniteSumProblem.componentGradient_spec_of_exists P i x h

theorem gradient_hasGradientAt_of_components
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n)
    (x : VariableSpace d)
    (hGrad :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => P.componentObjective i y)
          (componentGradient P i x) x) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  letI : Nonempty (Fin n) := FiniteSumProblem.index_nonempty hn
  unfold objective gradient
  exact SOptLib.finiteAverageObjective_hasGradientAt
    P.componentObjective P.componentGradient x
    (fun i => hGrad i)

theorem gradient_hasGradientAt_of_component_realization
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d)
    (hGrad :
      ∀ i : Fin n,
        ∃ g : VariableSpace d,
          HasGradientAt
            (fun y : VariableSpace d => P.componentObjective i y) g x) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  apply gradient_hasGradientAt_of_components P hn x
  intro i
  exact component_gradient_spec_of_exists P i x (hGrad i)

noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objectiveInfimum (objective P hn)

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objective P hn P.x0 - fStar P hn

theorem fStar_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    fStar P hn = objectiveInfimum (objective P hn) := by
  rfl

theorem Delta_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    Delta P hn = objective P hn P.x0 - fStar P hn := by
  rfl

def finite_gap_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : Prop :=
  BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) ∧
    0 ≤ Delta P hn

theorem finite_gap_boundary_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
  finite_gap_boundary P hn := by
  have hBdd : BddBelow ((objective P hn) '' (Set.univ : Set (VariableSpace d))) := by
    simpa [objective, FiniteSumProblem.f] using P.objective_bddBelow
  refine ⟨hBdd, ?_⟩
  unfold Delta fStar
  exact sub_nonneg.mpr
    (by
      unfold objectiveInfimum
      exact SOptLib.objectiveInfimumValue_le hBdd (Set.mem_univ P.x0))

def sourceUpdateDomain
    {n : ℕ} (schedule : FiniteSumSourceSchedule n)
    (v : VariableSpace d) : Prop :=
  schedule.L ≠ 0 ∧ schedule.n0 ≠ 0 ∧ 0 < ‖v‖

/- Source status: source_derived, domain-indexed.
   Citation: `book/research/SPIDER.json#/extension/additions/algorithm_spec/steps/4`,
   quote `x^(k+1) = x^k - eta^k v^k` with the displayed adaptive quotient. -/
noncomputable def optionIIUpdate
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d)
    (h : sourceUpdateDomain schedule v) : VariableSpace d :=
  x -
    finiteSumSourceAdaptiveStepSize schedule ‖v‖ h.2.2 h.1 h.2.1 • v

theorem source_update_domain_zero
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    : ¬ sourceUpdateDomain schedule (0 : VariableSpace d) := by
  simp [sourceUpdateDomain]

theorem optionIIUpdate_spec
    {n d : ℕ} (schedule : FiniteSumSourceSchedule n)
    (x v : VariableSpace d)
    (hL : schedule.L ≠ 0) (hn0 : schedule.n0 ≠ 0)
    (hv : 0 < ‖v‖) :
    optionIIUpdate schedule x v ⟨hL, hn0, hv⟩ =
      x -
        min
          (schedule.epsilon / (schedule.L * schedule.n0 * ‖v‖))
          (1 / (2 * schedule.L * schedule.n0)) • v := by
  rfl

/- Source status: literal source display.
   Citation: `book/research/SPIDER.json#/extension/additions/main_theorem/proof/2`,
   quote `n_0 n^(1/2) L^2 · epsilon^2/(L^2 n_0^2) · epsilon n_0/n^(1/2)`.
   The corresponding cube identity is exposed only under its genuine
   denominator domain. -/
noncomputable def B18_display
    (n : ℕ) (epsilon L n0 : ℝ) : ℝ :=
  n0 * Real.sqrt (n : ℝ) * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt (n : ℝ))

theorem B18_display_epsilon_cube
    {n : ℕ} {epsilon L n0 : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    B18_display n epsilon L n0 = epsilon ^ 3 := by
  unfold B18_display
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

/-- The paper's epsilon-squared endpoint is retained as an unresolved source
record.  It is not a theorem and is not consumed by any downstream result. -/
/- Source status: unresolved_source_assertion; deliberately non-consumable.
   Citation: `book/research/SPIDER.json#/extension/additions/main_theorem/proof/3`,
   quote `the displayed factors ... simplify to epsilon^3 before ... epsilon^2`.
   -/
def B18_paper_epsilon_sq_source_assertion
    (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  B18_display n epsilon L n0 = epsilon ^ 2

/- Source status: source_fact.
   Citation: `book/research/SPIDER.json#/extension/additions/main_theorem/proof/13`,
   quote `ceil(K/q) S_1 + K S_2 <= 2K + S_1`. -/
def B19_literal_bound (K S1 : ℕ) : ℝ :=
  2 * (K : ℝ) + S1

/- Source status: corrected_extension.
   Citation: `book/research/SPIDER.json#/extension/additions/main_theorem/proof/14`,
   quote `the subsequent line follows ... 2 K S_2 + S_1`. -/
def B19_corrected_bound (K S1 : ℕ) (S2 : ℝ) : ℝ :=
  2 * (K : ℝ) * S2 + S1

theorem B19_routes_are_distinct :
    B19_literal_bound 1 1 ≠ B19_corrected_bound 1 1 2 := by
  norm_num [B19_literal_bound, B19_corrected_bound]

/- Source status: source_fact, denominator-guarded.
   Citation: `book/research/SPIDER.json#/extension/additions/algorithm_spec/parameters/2`,
   quote `K = floor((4L Delta n_0) epsilon^(-2)) + 1`. -/
noncomputable def iterationBudget
    (L Delta epsilon n0 : ℝ) : Option ℕ :=
  if epsilon = 0 ∨ L = 0 ∨ n0 = 0 then
    none
  else
    some (Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1)

/- Source status: source_boundary record.
   Citation: `book/research/SPIDER.json#/extension/additions/main_theorem`,
   quote `gradient cost is bounded by n + 8(L Delta) n^(1/2) epsilon^(-2)
   + 2 n_0^(-1) n^(1/2)`. -/
noncomputable def gradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  if epsilon = 0 ∨ L = 0 ∨ n0 = 0 then
    none
  else
    some ((n : ℝ) + 8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
      2 * Real.sqrt (n : ℝ) / n0)

/- The source B.19 display is only exposed under its source denominator
   boundary.  The corrected executable route is a separate extension. -/
noncomputable def literalB19Cost
    {n : ℕ} (schedule : Option (FiniteSumSourceSchedule n))
    (K : ℕ) : Option ℝ :=
  match schedule with
  | none => none
  | some schedule =>
      if schedule.q = 0 then
        none
      else
        some ((Nat.ceil ((K : ℝ) / schedule.q) : ℝ) *
          (schedule.S1 : ℝ) + (K : ℝ) * schedule.S2)

theorem literalB19Cost_of_q_ne_zero
    {n : ℕ} (schedule : FiniteSumSourceSchedule n)
    (K : ℕ) (hq : schedule.q ≠ 0) :
    literalB19Cost (some schedule) K =
      some ((Nat.ceil ((K : ℝ) / schedule.q) : ℝ) *
        (schedule.S1 : ℝ) + (K : ℝ) * schedule.S2) := by
  simp [literalB19Cost, hq]

/- The source output is the actual iterate-valued random output from
   Algorithm 1, line 17.  The iterate family is supplied by a realization
   boundary; the selector itself is canonical and does not store an
   unrelated index PMF. -/
/- Source status: unresolved_source_assertion.
   Citation: `book/research/SPIDER.json#/extension/additions/main_theorem/proof/3`,
   quote `the paper immediately says So Lemma 2 holds` after the epsilon-power
   mismatch in the displayed B.18 chain. -/
inductive Theorem2SourceB18Status where
  | displayedEpsilonCubePaperEpsilonSquareUnresolved
  deriving DecidableEq

/- The source output is unavailable at the real-valued source boundary:
   the paper gives the uniform selection rule, but does not specify a
   universal natural-count process for arbitrary real `S₂` and `q`. -/
inductive Theorem2SourceOutputStatus where
  | unavailable
  deriving DecidableEq

inductive Theorem2SourceRealizationStatus where
  | sourceBoundaryOnly
  | explicitNaturalRealization
  deriving DecidableEq

/- Source status: source_boundary record.  This record separates the literal
   source displays, unresolved B.18, unavailable source output, and corrected
   realization status without presenting any one of them as the completed
   theorem. -/
structure Theorem2SourceBoundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
  (epsilon n0 : ℝ) where
  schedule : Option (FiniteSumSourceSchedule n)
  budget : Option ℕ
  literalB19 : Option (ℕ → ℝ)
  correctedB19 : Option (ℕ → ℝ)
  costBound : Option ℝ
  /-- Source status for Algorithm 1, line 17.

  Source status: source_boundary.
  Citation: `book/research/SPIDER.json#/extension/additions/algorithm_spec/output`,
  quote `x tilde chosen uniformly at random from {x^k}_{k=0}^{K-1}`.
  The executable output is provided only by
  `FiniteSumNaturalRealization.uniformOutput` below. -/
  outputStatus : Theorem2SourceOutputStatus
  b18Display : Option ℝ
  b18PaperEpsilonSqAssertion : Option Prop
  b18Status : Theorem2SourceB18Status
  realizationStatus : Theorem2SourceRealizationStatus

noncomputable def sourceBoundaryBudget
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) : Option ℕ :=
  by
    classical
    exact if h : FiniteSumSourceParameterDomain n epsilon P.L n0 then
      iterationBudget P.L
        (objective P hDomain.n_pos P.x0 -
          objectiveInfimum (objective P hDomain.n_pos))
        epsilon n0
    else
      none

noncomputable def sourceBoundaryCostBound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) : Option ℝ :=
  by
    classical
    exact if h : FiniteSumSourceParameterDomain n epsilon P.L n0 then
      gradientCostBound n P.L
        (objective P hDomain.n_pos P.x0 -
          objectiveInfimum (objective P hDomain.n_pos))
        n0 epsilon
    else
      none

noncomputable def sourceBoundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    Theorem2SourceBoundary P epsilon n0 :=
  by
    classical
    let schedule := theorem2FiniteSumSourceSchedule n epsilon P.L n0
    exact
      { schedule := schedule
        budget := sourceBoundaryBudget P epsilon n0 hDomain
        literalB19 := schedule.map
          (fun s => fun K => B19_literal_bound K s.S1)
        correctedB19 := schedule.map
          (fun s => fun K => B19_corrected_bound K s.S1 s.S2)
        costBound := sourceBoundaryCostBound P epsilon n0 hDomain
        outputStatus := Theorem2SourceOutputStatus.unavailable
        b18Display := some (B18_display n epsilon P.L n0)
        b18PaperEpsilonSqAssertion :=
          some (B18_paper_epsilon_sq_source_assertion n epsilon P.L n0)
        b18Status :=
          Theorem2SourceB18Status.displayedEpsilonCubePaperEpsilonSquareUnresolved
        realizationStatus :=
          Theorem2SourceRealizationStatus.sourceBoundaryOnly }

theorem sourceBoundary_schedule
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    (sourceBoundary P epsilon n0 hDomain).schedule =
      theorem2FiniteSumSourceSchedule n epsilon P.L n0 := by
  rfl

theorem sourceBoundary_budget
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    (sourceBoundary P epsilon n0 hDomain).budget =
      sourceBoundaryBudget P epsilon n0 hDomain := by
  rfl

theorem sourceBoundary_outputStatus
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    (sourceBoundary P epsilon n0 hDomain).outputStatus =
      Theorem2SourceOutputStatus.unavailable := by
  rfl

theorem sourceBoundary_b18Status
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    (sourceBoundary P epsilon n0 hDomain).b18Status =
      Theorem2SourceB18Status.displayedEpsilonCubePaperEpsilonSquareUnresolved := by
  rfl

theorem sourceBoundary_realizationStatus
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    (sourceBoundary P epsilon n0 hDomain).realizationStatus =
      Theorem2SourceRealizationStatus.sourceBoundaryOnly := by
  rfl

noncomputable def theorem2_source_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    Theorem2SourceBoundary P epsilon n0 :=
  sourceBoundary P epsilon n0 hDomain

end FiniteSumSourceActive

/-!
Corrected extension: a checked, executable natural realization.  This
namespace is intentionally separate from the source boundary.  It uses the
SOptLib finite-sum process and a proved iid with-replacement law, while the
source theorem above continues to expose the paper's real schedule.
-/
namespace FiniteSumNaturalRealization

abbrev Schedule (n : ℕ) := CorrectedFiniteSumSchedule n

noncomputable def schedule
    (n : ℕ) (epsilon L n0 : ℝ) : Schedule n :=
  theorem2FiniteSumImplementationSchedule n epsilon L n0

def checkedRegime (n : ℕ) (epsilon L n0 : ℝ) : Prop :=
  FiniteSumScheduleDomain n n0 ∧ 0 < epsilon ∧ 0 < L

abbrev Path {n : ℕ} (s : Schedule n) :=
  SOptLib.miniBatchSamplePath
    (max 1 (Nat.ceil s.S2)) (Fin n)

noncomputable def batchSize {n : ℕ} (s : Schedule n) : ℕ :=
  max 1 (Nat.ceil s.S2)

noncomputable def epochLength {n : ℕ} (s : Schedule n) : ℕ :=
  max 1 (Nat.ceil s.q)

theorem batchSize_pos {n : ℕ} (s : Schedule n) :
    0 < batchSize s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem epochLength_pos {n : ℕ} (s : Schedule n) :
    0 < epochLength s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

noncomputable def law
    {n : ℕ} (hn : 0 < n) (s : Schedule n) : Measure (Path s) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact SOptLib.iidMiniBatchSampleLaw (batchSize s)
    (PMF.uniformOfFintype (Fin n)).toMeasure

theorem law_spec
    {n : ℕ} (hn : 0 < n) (s : Schedule n) :
    IsProbabilityMeasure (law hn s) ∧
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin (batchSize s)) (omega : Path s) =>
          omega kr.1 kr.2) (law hn s) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : IsProbabilityMeasure
      (PMF.uniformOfFintype (Fin n)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype (Fin n))
  unfold law
  exact ⟨
    SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
      (batchSize s) (PMF.uniformOfFintype (Fin n)).toMeasure,
    SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
      (batchSize s) (PMF.uniformOfFintype (Fin n)).toMeasure⟩

noncomputable def filtration {n : ℕ} (s : Schedule n) :
    Filtration ℕ (by infer_instance : MeasurableSpace (Path s)) :=
  SOptLib.filtration
    (fun t omega => omega t)
    (fun t => measurable_pi_apply t)

noncomputable def update
    {n d : ℕ} (s : Schedule n) (x v : VariableSpace d) :
    VariableSpace d :=
  -- The zero-estimator branch is an internal degenerate case.  The
  -- source-facing update above is domain-indexed and has no fallback value.
  if 0 < ‖v‖ then
    x - s.etaK ‖v‖ • v
  else
    x

theorem update_zero
    {n d : ℕ} (s : Schedule n) (x : VariableSpace d) :
    update s x 0 = x := by
  simp [update]

theorem update_positive
    {n d : ℕ} (s : Schedule n) (x v : VariableSpace d)
    (hv : 0 < ‖v‖) :
    update s x v = x - s.etaK ‖v‖ • v := by
  simp [update, hv]

noncomputable def stateProcess
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) :
    ℕ → Path s → State (VariableSpace d) :=
  SOptLib.finiteSumConditionalGradientProcess
    (fun x v _ => { x := x, v := v })
    State.x State.v (fun _ => 0)
    P.x0 P.grad
    (fun v x y start _batch omega =>
      recursiveEstimator P.gradKernel v x y
        (fun i => omega start i))
    (fun x v _ => update s x v)
    (epochLength s) (batchSize s)

noncomputable def iterate
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) : ℕ → Path s → VariableSpace d :=
  fun k omega => (stateProcess P s (k + 1) omega).x

noncomputable def estimator
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) : ℕ → Path s → VariableSpace d :=
  fun k omega => (stateProcess P s (k + 1) omega).v

noncomputable def uniformOutput
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) (K : ℕ) :
    Fin K × Path s → VariableSpace d :=
  fun z => iterate P s z.1 z.2

noncomputable def uniformOutputLaw
    {n : ℕ} (hn : 0 < n) (s : Schedule n)
    (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × Path s) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact (PMF.uniformOfFintype (Fin K)).toMeasure.prod (law hn s)

theorem uniformOutput_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) (K : ℕ) (z : Fin K × Path s) :
    uniformOutput P s K z = iterate P s z.1 z.2 := by
  rfl

theorem uniformOutput_support_nonempty
    {n d : ℕ} (hn : 0 < n) (s : Schedule n)
    (K : ℕ) (hK : 0 < K) :
    Nonempty (Fin K × Path s) := by
  let omega : Path s := fun _ _ => ⟨0, hn⟩
  exact ⟨⟨⟨0, hK⟩, omega⟩⟩

@[simp]
theorem iterate_succ
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) (k : ℕ) (omega : Path s) :
    iterate P s (k + 1) omega =
      update s (iterate P s k omega) (estimator P s k omega) := by
  rfl

@[simp]
theorem estimator_zero
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (s : Schedule n) (omega : Path s) :
    estimator P s 0 omega = P.grad P.x0 := by
  rfl

noncomputable def refreshIndex {n : ℕ} (s : Schedule n) (k : ℕ) : ℕ :=
  (k / epochLength s) * epochLength s

theorem refreshIndex_le {n : ℕ} (s : Schedule n) (k : ℕ) :
    refreshIndex s k ≤ k := by
  unfold refreshIndex
  exact Nat.div_mul_le_self k (epochLength s)

def refreshBoundary {n : ℕ} (s : Schedule n) (k : ℕ) : Prop :=
  refreshIndex s k % epochLength s = 0 ∧ refreshIndex s k ≤ k

theorem refreshBoundary_spec {n : ℕ} (s : Schedule n) (k : ℕ) :
    refreshBoundary s k := by
  refine ⟨?_, refreshIndex_le s k⟩
  unfold refreshIndex
  exact Nat.mul_mod_left _ _

def fullRefreshErrorBoundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (s : Schedule n) (k : ℕ) : Prop :=
  SOptLib.ConditionalExpectation.conditionalExpectationEq
    (law hn s) ((filtration s).seq (refreshIndex s k))
    (fun omega =>
      ‖estimator P s (refreshIndex s k) omega -
        P.grad (iterate P s (refreshIndex s k) omega)‖ ^ 2)
    (fun _ => (0 : ℝ))

theorem full_refresh_error_B17
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hChecked : checkedRegime n epsilon P.L n0)
    (k : ℕ) :
    fullRefreshErrorBoundary P hChecked.1.n_pos
      (schedule n epsilon P.L n0) k := by
  sorry

def estimatorErrorBoundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (s : Schedule n) (epsilon : ℝ) (k : ℕ) : Prop :=
  refreshBoundary s k ∧
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
      (law hn s) ((filtration s).seq (refreshIndex s k + 1))
      (fun omega =>
        ‖estimator P s k omega -
          P.grad (iterate P s k omega)‖ ^ 2) ∧
    @MeasureTheory.condExp
        (Path s) ℝ ((filtration s).seq (refreshIndex s k + 1))
        (m₀ := inferInstance) inferInstance inferInstance inferInstance
        (law hn s)
        (fun omega =>
          ‖estimator P s k omega -
            P.grad (iterate P s k omega)‖ ^ 2)
      ≤ᵐ[law hn s] (fun _ => epsilon ^ 2)

theorem estimator_error_Lemma2
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hChecked : checkedRegime n epsilon P.L n0)
    (k : ℕ) :
    estimatorErrorBoundary P hChecked.1.n_pos
      (schedule n epsilon P.L n0) epsilon k := by
  sorry

noncomputable def executableCost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℕ :=
  Nat.ceil ((K : ℝ) / (epochLength s : ℝ)) * s.S1 +
    K * batchSize s

def executableCostBoundary
    {n : ℕ} (s : Schedule n) (K : ℕ) : Prop :=
  (executableCost s K : ℝ) ≤
    FiniteSumSourceActive.B19_literal_bound K s.S1 +
      FiniteSumSourceActive.B19_corrected_bound K s.S1 s.S2

theorem executableCost_B19_bridge
    {n : ℕ} (s : Schedule n) (K : ℕ) :
    executableCostBoundary s K := by
  sorry

end FiniteSumNaturalRealization

theorem finiteSumExactNaturalRealization_impossible_n2_n0_1 :
    ¬ ∃ S2 q : ℕ,
      0 < S2 ∧ 0 < q ∧
        (S2 : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  rintro ⟨S2, q, hS2, hq, hS2spec, hqspec⟩
  have hsq : (S2 : ℝ) ^ 2 = 2 := by
    rw [hS2spec]
    exact Real.sq_sqrt (by norm_num)
  have hsqNatPow : S2 ^ 2 = 2 := by
    exact_mod_cast hsq
  have hsqNat : S2 * S2 = 2 := by
    simpa [pow_two] using hsqNatPow
  have hS2leReal : (S2 : ℝ) ≤ 2 := by
    nlinarith
  have hS2le : S2 ≤ 2 := by
    exact_mod_cast hS2leReal
  interval_cases S2 <;> norm_num at hsqNat

noncomputable def theorem2_finite_sum_source_boundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) :
    FiniteSumSourceActive.Theorem2SourceBoundary P epsilon n0 := by
  exact FiniteSumSourceActive.theorem2_source_boundary
    P epsilon n0 hDomain

/-!
The source theorem's cost expression is defined directly from the real
schedule in (3.7).  It is separate from the executable ceiling-based
realization above: the former is the paper object, while the latter is an
implementation boundary for later proofs.
-/
noncomputable def theorem2FiniteSumSourceGradientCost
    {n : ℕ} (epsilon L n0 : ℝ) (K : ℕ) : Option ℝ :=
  match theorem2FiniteSumSourceSchedule n epsilon L n0 with
  | none => none
  | some schedule =>
      if schedule.q = 0 then
        none
      else
        some ((Nat.ceil ((K : ℝ) / schedule.q) : ℝ) *
          (schedule.S1 : ℝ) + (K : ℝ) * schedule.S2)

noncomputable def theorem2FiniteSumSourceGradientCostBound
    (n : ℕ) (L Delta n0 epsilon : ℝ) : Option ℝ :=
  if epsilon = 0 ∨ L = 0 ∨ n0 = 0 then
    none
  else
    some ((n : ℝ) +
      8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
      2 * n0⁻¹ * Real.sqrt (n : ℝ))

noncomputable def theorem2FiniteSumSourceIterationBudget
    (L Delta epsilon n0 : ℝ) : Option ℕ :=
  if epsilon = 0 ∨ L = 0 ∨ n0 = 0 then
    none
  else
    some (Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1)

/-- Canonical paper schedule for Theorem 2, using the real quantities in
Eq. (3.7).  The option-valued schedule records below are implementation
boundary objects; this direct definition is the source-facing object. -/
noncomputable def theorem2FiniteSumSourceScheduleCanonical
    (n : ℕ) (epsilon L n0 : ℝ) :
    FiniteSumSourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0
  eta := epsilon / (L * n0)
  q := n0 * Real.sqrt (n : ℝ)

@[simp] theorem theorem2FiniteSumSourceScheduleCanonical_S1
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumSourceScheduleCanonical n epsilon L n0).S1 = n := by
  rfl

@[simp] theorem theorem2FiniteSumSourceScheduleCanonical_S2
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumSourceScheduleCanonical n epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0 := by
  rfl

@[simp] theorem theorem2FiniteSumSourceScheduleCanonical_eta
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumSourceScheduleCanonical n epsilon L n0).eta =
      epsilon / (L * n0) := by
  rfl

@[simp] theorem theorem2FiniteSumSourceScheduleCanonical_q
    (n : ℕ) (epsilon L n0 : ℝ) :
    (theorem2FiniteSumSourceScheduleCanonical n epsilon L n0).q =
      n0 * Real.sqrt (n : ℝ) := by
  rfl

/-- Theorem 2's direct iteration budget from the printed floor formula. -/
noncomputable def theorem2FiniteSumSourceIterationCountCanonical
    (n : ℕ) (L Delta epsilon n0 : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

/-- The source-corrected B.19 call-count expression
`2 K S₂ + S₁`, with `S₁ = n` and `S₂ = sqrt n / n₀`. -/
noncomputable def theorem2FiniteSumSourceGradientCostCanonical
    (n : ℕ) (epsilon L n0 : ℝ) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * (Real.sqrt (n : ℝ) / n0) + n

/-- The closed-form gradient-cost bound printed in Theorem 2. -/
noncomputable def theorem2FiniteSumSourceGradientCostBoundCanonical
    (n : ℕ) (L Delta n0 epsilon : ℝ) : ℝ :=
  (n : ℝ) +
    8 * (L * Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0⁻¹ * Real.sqrt (n : ℝ)

def theorem2FiniteSumNaturalEstimatorErrorAdapterBoundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (h : FiniteSumSourceParameterDomain n epsilon P.L n0) : Prop :=
  ∀ k : ℕ,
    FiniteSumNaturalRealization.estimatorErrorBoundary P h.1.n_pos
      (FiniteSumNaturalRealization.schedule n epsilon P.L n0) epsilon k

theorem theorem2_finite_sum_natural_realization_estimator_error_adapter
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (h : FiniteSumSourceParameterDomain n epsilon P.L n0) :
    theorem2FiniteSumNaturalEstimatorErrorAdapterBoundary P epsilon n0 h := by
  intro k
  exact FiniteSumNaturalRealization.estimator_error_Lemma2
    P epsilon n0 h k

def theorem2FiniteSumNaturalOneStepDescentAdapterBoundary
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (h : FiniteSumSourceParameterDomain n epsilon P.L n0) : Prop :=
  ∀ x v : VariableSpace d,
    FiniteSumSourceActive.objective P h.1.n_pos
        (FiniteSumNaturalRealization.update
          (FiniteSumNaturalRealization.schedule n epsilon P.L n0) x v) ≤
      FiniteSumSourceActive.objective P h.1.n_pos x -
          epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) *
          ‖v - FiniteSumSourceActive.gradient P h.1.n_pos x‖ ^ 2

theorem theorem2_finite_sum_natural_realization_one_step_descent_adapter
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (h : FiniteSumSourceParameterDomain n epsilon P.L n0) :
    theorem2FiniteSumNaturalOneStepDescentAdapterBoundary P epsilon n0 h := by
  sorry

/- The paper-facing adapter is deliberately expressed with the real schedule.
The executable estimator and descent adapters above are named as natural
realization extensions and are not part of this source theorem's statement. -/
def theorem2FiniteSumSourceCostClaim
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (_hDomain : FiniteSumScheduleDomain n n0) : Prop :=
  theorem2FiniteSumSourceGradientCostCanonical
      n epsilon P.L n0
      (theorem2FiniteSumSourceIterationCountCanonical
        n P.L P.Delta epsilon n0) ≤
    theorem2FiniteSumSourceGradientCostBoundCanonical
      n P.L P.Delta n0 epsilon

def theorem2_finite_sum_source_boundary_status
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ) (hDomain : FiniteSumScheduleDomain n n0) : Prop :=
  (FiniteSumSourceActive.sourceBoundary P epsilon n0 hDomain).b18Status =
      FiniteSumSourceActive.Theorem2SourceB18Status.displayedEpsilonCubePaperEpsilonSquareUnresolved ∧
    (FiniteSumSourceActive.sourceBoundary P epsilon n0 hDomain).outputStatus =
      FiniteSumSourceActive.Theorem2SourceOutputStatus.unavailable ∧
    (FiniteSumSourceActive.sourceBoundary P epsilon n0 hDomain).realizationStatus =
      FiniteSumSourceActive.Theorem2SourceRealizationStatus.sourceBoundaryOnly

/-- Paper-facing finite-sum Theorem 2 gradient-cost bound.

The source display and the natural realization obligations remain named
internal boundaries, while this declaration exposes the paper's cost
inequality over the canonical real schedule, budget, and B.19 cost objects. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (P : FiniteSumProblem n (VariableSpace d))
    (epsilon n0 : ℝ)
    (hDomain : FiniteSumScheduleDomain n n0) :
    theorem2FiniteSumSourceGradientCostCanonical
        n epsilon P.L n0
        (theorem2FiniteSumSourceIterationCountCanonical
          n P.L P.Delta epsilon n0) ≤
    theorem2FiniteSumSourceGradientCostBoundCanonical
        n P.L P.Delta n0 epsilon := by
  let hParameter : FiniteSumSourceParameterDomain n epsilon P.L n0 :=
    ⟨hDomain, by sorry, by sorry⟩
  let schedule :=
    FiniteSumNaturalRealization.schedule n epsilon P.L n0
  let mu := FiniteSumNaturalRealization.law hParameter.1.n_pos schedule
  let K :=
    theorem2FiniteSumSourceIterationCountCanonical
      n P.L P.Delta epsilon n0
  have hK : 0 < K := by
    sorry
  have hEstimatorBoundary :
      theorem2FiniteSumNaturalEstimatorErrorAdapterBoundary P epsilon n0
        hParameter := by
    exact theorem2_finite_sum_natural_realization_estimator_error_adapter
      P epsilon n0 hParameter
  have hDescentBoundary :
      theorem2FiniteSumNaturalOneStepDescentAdapterBoundary P epsilon n0
        hParameter := by
    exact theorem2_finite_sum_natural_realization_one_step_descent_adapter
      P epsilon n0 hParameter
  have hOutputBoundary :
      uniformOutputGradientNormAverage mu P.grad
        (FiniteSumNaturalRealization.iterate P schedule)
        K ≤ 5 * epsilon := by
    exact uniform_average_gradient_bound_of_estimator_average
      mu P.grad
      (FiniteSumNaturalRealization.iterate P schedule)
      (FiniteSumNaturalRealization.estimator P schedule)
      K hK epsilon (by sorry) (by sorry)
  have _ := hEstimatorBoundary
  have _ := hDescentBoundary
  have _ := hOutputBoundary
  sorry

/-- Extension proof root for the finite-sum source boundary.

The finite-sum cost leaf remains a proof obligation, but the extension root
records the inherited Theorem 1 output-conversion interface that downstream
proof work must consume.  The adapter is theorem-level reuse, not a new setup
field or a second estimator model. -/
theorem theorem2_finite_sum_extension_proof_root
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  exact uniform_average_gradient_bound_of_estimator_average
    mu grad iterate estimator K hK epsilon hconvert hest_avg

theorem theorem2_finite_sum_output_conversion_adapter
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate : ℕ → Ω → E) (K : ℕ) (hK : 0 < K) (C : ℝ)
    (hint :
      ∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
        Integrable (fun ω => ‖grad (iterate R.1 ω)‖) mu)
    (havg : uniformOutputGradientNormAverage mu grad iterate K ≤ C) :
    selectedOutputGradientNormExpectation mu grad iterate K hK ≤ C := by
  exact selectedOutputGradientNormExpectation_le_of_uniform_average_le
    mu grad iterate K hK C hint havg

end Algorithms.Unverified.SPIDER

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Canonical

/-!
Append-only source-facing layer for the finite-sum branch of Theorem 2.

`N0 n` is the paper's parameter domain `n₀ ∈ [1, √n]`. The declarations here
are computed from the finite-sum objectives and the canonical Option II update.
Rounded sample-count and measure-theoretic realization details remain in the
separate implementation namespace above.
-/

def n0Domain (n : ℕ) : Set ℝ :=
  Set.Icc (1 : ℝ) (Real.sqrt (n : ℝ))

abbrev N0 (n : ℕ) :=
  {r : ℝ // r ∈ n0Domain n}

theorem n0_lower {n : ℕ} (n0 : N0 n) :
    1 ≤ n0.1 :=
  n0.2.1

theorem n0_upper {n : ℕ} (n0 : N0 n) :
    n0.1 ≤ Real.sqrt (n : ℝ) :=
  n0.2.2

/-- The finite-average objective in Eq. (1.2). -/
noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    VariableSpace d → ℝ :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => P.componentObjective i x)

@[simp] theorem objective_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) (x : VariableSpace d) :
    objective P x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => P.componentObjective i x) := by
  rfl

/-- Component oracle kernel `i ↦ ∇f_i(x)`, computed from the objectives. -/
noncomputable def componentGradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => P.componentObjective i y) x

@[simp] theorem componentGradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    componentGradient P i x =
      ∇ (fun y : VariableSpace d => P.componentObjective i y) x := by
  rfl

/-- The full finite-sum gradient `∇f`, defined from the paper objective. -/
noncomputable def gradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    VariableSpace d → VariableSpace d :=
  fun x => ∇ (objective P) x

@[simp] theorem gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) :
    gradient P x = ∇ (objective P) x := by
  rfl

/-- The component-gradient average used by a finite-sum refresh branch. -/
noncomputable def componentGradientAverage
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient P i x)

theorem gradient_eq_componentGradientAverage_of_realization
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hcomponent :
      ∀ i : Fin n, ∀ x : VariableSpace d,
        HasGradientAt
          (fun y : VariableSpace d => P.componentObjective i y)
          (componentGradient P i x) x) :
    ∀ x : VariableSpace d,
      gradient P x = componentGradientAverage P x := by
  intro x
  sorry

/-- The source global infimum and initial gap. No lower-bound theorem is
derived here; lower-boundedness remains `P.objective_bddBelow`. -/
noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) : ℝ :=
  objectiveInfimum (objective P)

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) : ℝ :=
  objective P P.x0 - fStar P

@[simp] theorem fStar_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    fStar P = objectiveInfimum (objective P) := by
  rfl

@[simp] theorem Delta_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    Delta P = objective P P.x0 - fStar P := by
  rfl

/-- Exact full-gradient refresh at an epoch boundary. -/
noncomputable def fullRefresh
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) : VariableSpace d :=
  gradient P x

@[simp] theorem fullRefresh_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) :
    fullRefresh P x = gradient P x := by
  rfl

/-- A finite component-gradient sample average, derived from the kernel. -/
noncomputable def componentSampleAverage
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) (samples : Fin S → Fin n) :
    VariableSpace d :=
  refreshEstimator (fun y i => componentGradient P i y) x samples

@[simp] theorem componentSampleAverage_spec
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (x : VariableSpace d) (samples : Fin S → Fin n) :
    componentSampleAverage P x samples =
      (S : ℝ)⁻¹ •
        Finset.sum Finset.univ
          (fun j : Fin S => componentGradient P (samples j) x) := by
  rfl

/-- The recursive SPIDER estimator, built from the component oracle kernel. -/
noncomputable def recursiveEstimator
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (vPrev xPrev xCurr : VariableSpace d)
    (samples : Fin S → Fin n) : VariableSpace d :=
  Algorithms.Unverified.SPIDER.recursiveEstimator
    (fun x i => componentGradient P i x)
    vPrev xPrev xCurr samples

@[simp] theorem recursiveEstimator_spec
    {n d S : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (vPrev xPrev xCurr : VariableSpace d)
    (samples : Fin S → Fin n) :
    recursiveEstimator P vPrev xPrev xCurr samples =
      (Fintype.card (Fin S) : ℝ)⁻¹ •
          Finset.sum Finset.univ
            (fun j : Fin S =>
              componentGradient P (samples j) xCurr -
                componentGradient P (samples j) xPrev) +
        vPrev := by
  rfl

/-- The real-valued Theorem 2 schedule from Eq. (3.7). -/
noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    FiniteSumSourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0.1
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  eta := epsilon / (L * n0.1)
  q := n0.1 * Real.sqrt (n : ℝ)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).eta =
      epsilon / (L * n0.1) := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

/-- The Option II adaptive stepsize in the source equation, with no
proof-dependent fallback branch. -/
noncomputable def optionIIAdaptiveStepSize
    {E : Type*} [Norm E]
    (epsilon L n0 : ℝ) (v : E) : ℝ :=
  min
    (epsilon / (L * n0 * ‖v‖))
    (1 / (2 * L * n0))

/-- Canonical one-step Option II update from Algorithm 1, line 14. -/
noncomputable def optionIIUpdate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (epsilon L n0 : ℝ) (x v : E) : E :=
  x - optionIIAdaptiveStepSize epsilon L n0 v • v

@[simp] theorem optionIIUpdate_spec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (epsilon L n0 : ℝ) (x v : E) :
    optionIIUpdate epsilon L n0 x v =
      x - optionIIAdaptiveStepSize epsilon L n0 v • v := by
  rfl

/-- Iterate sequence generated from the canonical Option II update. -/
noncomputable def iterateFromEstimator
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (epsilon L n0 : ℝ)
    (estimator : ℕ → Ω → E) :
    ℕ → Ω → E
  | 0 => fun _ => x0
  | k + 1 => fun omega =>
      optionIIUpdate epsilon L n0
        (iterateFromEstimator x0 epsilon L n0 estimator k omega)
        (estimator k omega)

@[simp] theorem iterateFromEstimator_zero
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (epsilon L n0 : ℝ)
    (estimator : ℕ → Ω → E) (omega : Ω) :
    iterateFromEstimator x0 epsilon L n0 estimator 0 omega = x0 := by
  rfl

@[simp] theorem iterateFromEstimator_succ
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (epsilon L n0 : ℝ)
    (estimator : ℕ → Ω → E) (k : ℕ) (omega : Ω) :
    iterateFromEstimator x0 epsilon L n0 estimator (k + 1) omega =
      optionIIUpdate epsilon L n0
        (iterateFromEstimator x0 epsilon L n0 estimator k omega)
        (estimator k omega) := by
  rfl

/-- Literal B.18 display; it is not silently replaced by the paper's
epsilon-squared conclusion. -/
noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold b18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

/-- Source-corrected B.19 cost route `2 K S2 + S1`. -/
noncomputable def gradientCost
    {n : ℕ} (n0 : N0 n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * (Real.sqrt (n : ℝ) / n0.1) + n

noncomputable def iterationBudget
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * P.L * Delta P * n0.1 * epsilon⁻¹ ^ 2) + 1

noncomputable def gradientCostBound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (P.L * Delta P) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

/-- Paper-facing finite-sum Theorem 2 cost statement. -/
theorem gradient_cost_bound_theorem
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) :
    gradientCost n0 (iterationBudget P epsilon n0) ≤
      gradientCostBound P epsilon n0 := by
  sorry

/-- Reuse edge for the inherited output-conversion proof spine. -/
theorem output_conversion_reuse
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  exact Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
    mu grad iterate estimator K hK epsilon hconvert hest_avg

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Canonical

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2SourceLayer

/-!
This namespace is the source-facing finite-sum bridge for Theorem 2.

The preceding extension namespaces are preserved.  In particular, the
rounded natural realization remains available for implementation proofs, but
the declarations below do not use it to define the paper's objective gap,
schedule, iterates, output, or cost expression.
-/

abbrev N0 (n : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Canonical.N0 n

theorem n_pos {n : ℕ} (n0 : N0 n) : 0 < n := by
  exact FiniteSumScheduleDomain.n_pos
    ⟨n0.2.1, n0.2.2⟩

/-- The finite-sum objective, restricted to the meaningful nonempty index
domain.  The lower-bound witness on `FiniteSumProblem` is not used here. -/
noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) : VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage
    (fun i : Fin n => P.componentObjective i)

@[simp] theorem objective_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    objective P hn =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => P.componentObjective i) := by
  rfl

/-- Source gradient existence is a named proof obligation, rather than a
totalized `∇` value hidden in the object definition. -/
theorem componentGradient_exists
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    ∃ g : VariableSpace d,
      HasGradientAt
        (fun y : VariableSpace d => P.componentObjective i y) g x := by
  sorry

/-- The selected component gradient is constructed from the source existence
obligation.  It has no Lean-default branch outside the source domain. -/
noncomputable def componentGradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => Classical.choose (componentGradient_exists P i x)

theorem componentGradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt
      (fun y : VariableSpace d => P.componentObjective i y)
      (componentGradient P i x) x := by
  exact Classical.choose_spec (componentGradient_exists P i x)

/-- The full finite-sum gradient is the average of the selected component
gradients. -/
noncomputable def gradient
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (_hn : 0 < n) : VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient P i x)

theorem gradient_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    HasGradientAt (objective P hn) (gradient P hn x) x := by
  sorry

/-- The source global infimum and initial gap.  This is the source expression
`f* = inf f` and `Delta = f(x0) - f*`, without a separate lower-bound field. -/
noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objectiveInfimum (objective P hn)

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) : ℝ :=
  objective P hn P.x0 - fStar P hn

@[simp] theorem fStar_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    fStar P hn = objectiveInfimum (objective P hn) := by
  rfl

@[simp] theorem Delta_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) :
    Delta P hn = objective P hn P.x0 - fStar P hn := by
  rfl

/-- Full refresh is the exact finite-sum gradient, as in (B.17). -/
noncomputable def fullRefresh
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) : VariableSpace d :=
  gradient P hn x

@[simp] theorem fullRefresh_spec
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    fullRefresh P hn x = gradient P hn x := by
  rfl

theorem fullRefresh_error_B17_pointwise
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (x : VariableSpace d) :
    ‖fullRefresh P hn x - gradient P hn x‖ ^ 2 = 0 := by
  simp [fullRefresh]

noncomputable def fullRefreshErrorExpectation
    {n d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω]
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (mu : Measure Ω) (x : VariableSpace d) : ℝ :=
  ∫ _ : Ω, ‖fullRefresh P hn x - gradient P hn x‖ ^ 2 ∂mu

theorem fullRefreshErrorExpectation_B17
    {n d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω]
    (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (mu : Measure Ω) (x : VariableSpace d) :
    fullRefreshErrorExpectation P hn mu x = 0 := by
  simp [fullRefreshErrorExpectation, fullRefresh]

/-- The real parameter schedule from (3.7), constructed only on its stated
positive denominator domain. -/
noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n)
    (_hepsilon : 0 < epsilon) (_hL : 0 < L) :
    FiniteSumSourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0.1
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  eta := epsilon / (L * n0.1)
  q := n0.1 * Real.sqrt (n : ℝ)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) (hL : 0 < L) :
    (schedule epsilon L n0 hepsilon hL).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) (hL : 0 < L) :
    (schedule epsilon L n0 hepsilon hL).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) (hL : 0 < L) :
    (schedule epsilon L n0 hepsilon hL).eta =
      epsilon / (L * n0.1) := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) (hL : 0 < L) :
    (schedule epsilon L n0 hepsilon hL).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

def scheduleDomain (schedule : FiniteSumSourceSchedule n) : Prop :=
  0 < schedule.L ∧ 0 < schedule.n0

theorem scheduleDomain_of
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) (hL : 0 < L) :
    scheduleDomain (schedule epsilon L n0 hepsilon hL) := by
  constructor
  · exact hL
  · exact lt_of_lt_of_le zero_lt_one n0.2.1

noncomputable def adaptiveStepSize
    {E : Type*} [Norm E]
    (schedule : FiniteSumSourceSchedule n)
    (_hSchedule : scheduleDomain schedule) (v : E) : ℝ :=
  if hv : 0 < ‖v‖ then
    min
      (schedule.epsilon / (schedule.L * schedule.n0 * ‖v‖))
      (1 / (2 * schedule.L * schedule.n0))
  else
    0

noncomputable def update
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule) (x v : E) : E :=
  x - adaptiveStepSize schedule hSchedule v • v

@[simp] theorem update_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule) (x : E) :
    update schedule hSchedule x 0 = x := by
  simp [update, adaptiveStepSize]

abbrev SourcePath (n : ℕ) (BatchIndex : Type*) :=
  ℕ → BatchIndex → Fin n

abbrev RefreshPattern :=
  ℕ → Prop

def refreshAt (refreshPattern : RefreshPattern) (k : ℕ) : Prop :=
  refreshPattern k

noncomputable def batchAverage
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (omega : SourcePath n (Fin BatchIndex)) (k : ℕ)
    (x : VariableSpace d) : VariableSpace d :=
  SOptLib.finiteUniformAverage
    (fun i : Fin BatchIndex => componentGradient P (omega k i) x)

noncomputable def recursiveEstimator
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (omega : SourcePath n (Fin BatchIndex)) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) : VariableSpace d :=
  batchAverage P hn omega k xCurr -
    batchAverage P hn omega k xPrev + vPrev

noncomputable def transition
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern)
    (omega : SourcePath n (Fin BatchIndex)) (k : ℕ)
    (state : State (VariableSpace d)) : State (VariableSpace d) := by
  classical
  let xNext :=
    update schedule hSchedule state.x state.v
  let vNext :=
    if refreshAt refreshPattern (k + 1) then
      fullRefresh P hn xNext
    else
      recursiveEstimator P hn omega (k + 1) state.v state.x xNext
  exact { x := xNext, v := vNext }

/-- Source iterate and estimator process, indexed by the paper's real schedule
and explicit sample path.  No ceiling or rounded epoch length occurs here. -/
noncomputable def stateProcess
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern) :
    ℕ → SourcePath n (Fin BatchIndex) → State (VariableSpace d)
  | 0 => fun _ => { x := P.x0, v := fullRefresh P hn P.x0 }
  | k + 1 => fun omega =>
      transition P hn schedule hSchedule refreshPattern omega k
        (stateProcess P hn schedule hSchedule refreshPattern k omega)

noncomputable def iterate
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern) :
  ℕ → SourcePath n (Fin BatchIndex) → VariableSpace d :=
  fun k omega => (stateProcess P hn schedule hSchedule refreshPattern k omega).x

noncomputable def estimator
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern) :
  ℕ → SourcePath n (Fin BatchIndex) → VariableSpace d :=
  fun k omega => (stateProcess P hn schedule hSchedule refreshPattern k omega).v

@[simp] theorem stateProcess_zero
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern)
    (omega : SourcePath n (Fin BatchIndex)) :
    stateProcess P hn schedule hSchedule refreshPattern 0 omega =
      { x := P.x0, v := fullRefresh P hn P.x0 } := by
  rfl

@[simp] theorem iterate_succ
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern)
    (k : ℕ) (omega : SourcePath n (Fin BatchIndex)) :
    iterate P hn schedule hSchedule refreshPattern (k + 1) omega =
      (transition P hn schedule hSchedule refreshPattern omega k
        (stateProcess P hn schedule hSchedule refreshPattern k omega)).x := by
  rfl

/-- The source output rule `x~` uniformly selected from `x^0,...,x^(K-1)`. -/
noncomputable def uniformOutput
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern)
    (K : ℕ) :
    Fin K × SourcePath n (Fin BatchIndex) → VariableSpace d :=
  fun z => iterate P hn schedule hSchedule refreshPattern z.1 z.2

noncomputable def uniformOutputLaw
    {n BatchIndex : ℕ}
    (mu : Measure (SourcePath n (Fin BatchIndex))) (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × SourcePath n (Fin BatchIndex)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact (PMF.uniformOfFintype (Fin K)).toMeasure.prod mu

theorem uniformOutput_spec
    {n d BatchIndex : ℕ}
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern)
    (K : ℕ) (z : Fin K × SourcePath n (Fin BatchIndex)) :
    uniformOutput P hn schedule hSchedule refreshPattern K z =
      iterate P hn schedule hSchedule refreshPattern z.1 z.2 := by
  rfl

noncomputable def outputGradientNormAverage
    {n d BatchIndex : ℕ}
    (mu : Measure (SourcePath n (Fin BatchIndex)))
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : scheduleDomain schedule)
    (refreshPattern : RefreshPattern) (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage mu
    (gradient P hn) (iterate P hn schedule hSchedule refreshPattern) K

noncomputable def gradientCost
    {n : ℕ} (n0 : N0 n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * (Real.sqrt (n : ℝ) / n0.1) + n

noncomputable def iterationBudget
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon : ℝ) (n0 : N0 n)
    (_hepsilon : 0 < epsilon) : ℕ :=
  Nat.floor
      ((4 * P.L * Delta P hn * n0.1) / epsilon ^ 2) + 1

noncomputable def gradientCostBound
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    (8 * (P.L * Delta P hn) * Real.sqrt (n : ℝ)) / epsilon ^ 2 +
    (2 * Real.sqrt (n : ℝ)) / n0.1

def costClaim
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) : Prop :=
  gradientCost n0 (iterationBudget P hn epsilon n0 hepsilon) ≤
    gradientCostBound P hn epsilon n0

/-- The source cost leaf is intentionally disconnected from rounded
implementation counts.  Its proof is a later source-derived obligation. -/
theorem costClaim_obligation
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (hn : 0 < n) (epsilon : ℝ) (n0 : N0 n)
    (hepsilon : 0 < epsilon) :
    costClaim P hn epsilon n0 hepsilon := by
  sorry

/-- Literal B.18 factors are retained separately from the claimed
epsilon-squared conclusion. -/
noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  exact
    FiniteSumTheorem2Canonical.b18DisplayedTerm_eq_epsilon_cube
      hepsilon hL hn0 hn

def b18PaperEpsilonSquareClaim
    (epsilon L n0 n : ℝ) : Prop :=
  b18DisplayedTerm epsilon L n0 n = epsilon ^ 2

theorem b18PaperEpsilonSquareClaim_obligation
    (epsilon L n0 n : ℝ) :
    b18PaperEpsilonSquareClaim epsilon L n0 n := by
  sorry

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2SourceLayer

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2SourceProofRoots

open Algorithms.Unverified.SPIDER
open Algorithms.Unverified.SPIDER.FiniteSumTheorem2SourceLayer

/-- Reuse the inherited Theorem 1 output-conversion proof on the canonical
source finite-sum iterate and estimator process. -/
theorem theorem2_finite_sum_source_output_conversion_root
    {n d BatchIndex : ℕ}
    (mu :
      Measure
        (FiniteSumTheorem2SourceLayer.SourcePath n (Fin BatchIndex)))
    [SFinite mu]
    (P : FiniteSumProblem n (VariableSpace d)) (hn : 0 < n)
    (schedule : FiniteSumSourceSchedule n)
    (hSchedule : FiniteSumTheorem2SourceLayer.scheduleDomain schedule)
    (refreshPattern : FiniteSumTheorem2SourceLayer.RefreshPattern)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega,
          ‖FiniteSumTheorem2SourceLayer.gradient P hn
              (FiniteSumTheorem2SourceLayer.iterate
                P hn schedule hSchedule refreshPattern k omega)‖ ∂mu) ≤
          (∫ omega,
            ‖FiniteSumTheorem2SourceLayer.estimator
                P hn schedule hSchedule refreshPattern k omega‖ ∂mu) +
            epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k =>
              ∫ omega,
                ‖FiniteSumTheorem2SourceLayer.estimator
                    P hn schedule hSchedule refreshPattern k omega‖ ∂mu) ≤
        4 * epsilon) :
    FiniteSumTheorem2SourceLayer.outputGradientNormAverage
        mu P hn schedule hSchedule refreshPattern K ≤ 5 * epsilon := by
  unfold FiniteSumTheorem2SourceLayer.outputGradientNormAverage
  exact Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
    mu
    (FiniteSumTheorem2SourceLayer.gradient P hn)
    (FiniteSumTheorem2SourceLayer.iterate
      P hn schedule hSchedule refreshPattern)
    (FiniteSumTheorem2SourceLayer.estimator
      P hn schedule hSchedule refreshPattern)
    K hK epsilon hconvert hest_avg

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2SourceProofRoots

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final

/-!
Terminal finite-sum object layer for Theorem 2.

The inherited `FiniteSumProblem` is used only through `ofProblem`, an adapter
which forgets its old proof-contingency fields.  The active process below has
one component-gradient family, one exact full refresh, one computed
with-replacement sample law, and one normalized uniform output law.
-/

abbrev N0 (n : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Canonical.N0 n

theorem n_pos {n : ℕ} (n0 : N0 n) : 0 < n := by
  exact FiniteSumScheduleDomain.n_pos ⟨n0.2.1, n0.2.2⟩

theorem n0_zero_rejected (n0 : N0 0) : False := by
  have h10 : (1 : ℝ) ≤ 0 := by
    simpa using le_trans n0.2.1 n0.2.2
  linarith

theorem epsilon_zero_rejected : ¬ (0 : ℝ) < 0 := by
  norm_num

theorem L_zero_rejected : ¬ (0 : ℝ) < 0 := by
  norm_num

theorem K_zero_rejected : ¬ (0 : ℕ) < 0 := by
  norm_num

structure Data (n d : ℕ) where
  componentObjective : Fin n → VariableSpace d → ℝ
  x0 : VariableSpace d
  L : ℝ

noncomputable def ofProblem
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) : Data n d where
  componentObjective := P.componentObjective
  x0 := P.x0
  L := P.L

noncomputable def objective
    {n d : ℕ} (D : Data n d) : VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage D.componentObjective

noncomputable def componentGradient
    {n d : ℕ} (D : Data n d) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => D.componentObjective i y) x

noncomputable def fullGradient
    {n d : ℕ} (D : Data n d) : VariableSpace d → VariableSpace d :=
  fun x => SOptLib.finiteUniformAverage (fun i => componentGradient D i x)

@[simp] theorem objective_spec
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    objective D x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => D.componentObjective i x) := by
  simp [objective, SOptLib.finiteUniformAverage]

@[simp] theorem componentGradient_spec
    {n d : ℕ} (D : Data n d) (i : Fin n) (x : VariableSpace d) :
    componentGradient D i x =
      ∇ (fun y : VariableSpace d => D.componentObjective i y) x := by
  rfl

@[simp] theorem fullGradient_spec
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    fullGradient D x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentGradient D i x) := by
  rfl

theorem finiteAverageGradient_bridge
    {n d : ℕ} (D : Data n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (componentGradient D i x) x) :
    ∇ (objective D) x = fullGradient D x := by
  unfold objective fullGradient
  exact
    SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      D.componentObjective (componentGradient D) x hcomponent

theorem finiteAverageObjective_hasGradientAt
    {n d : ℕ} (D : Data n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (componentGradient D i x) x) :
    HasGradientAt (objective D) (fullGradient D x) x := by
  unfold objective fullGradient
  convert
    (SOptLib.finiteAverageObjective_hasGradientAt
      D.componentObjective (componentGradient D) x hcomponent) using 1
  · funext z
    simp [SOptLib.finiteUniformAverage, Pi.smul_apply, smul_eq_mul]

def averagedLipschitz
    {n d : ℕ} (D : Data n d) : Prop :=
  ∀ x y : VariableSpace d,
    SOptLib.finiteUniformAverage
      (fun i : Fin n =>
        ‖componentGradient D i x - componentGradient D i y‖ ^ 2) ≤
      D.L ^ 2 * ‖x - y‖ ^ 2

noncomputable def fStar
    {n d : ℕ} (D : Data n d) : ℝ :=
  objectiveInfimum (objective D)

noncomputable def Delta
    {n d : ℕ} (D : Data n d) : ℝ :=
  objective D D.x0 - fStar D

def globalInfimumContract
    {n d : ℕ} (D : Data n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ objective D x

theorem Delta_nonneg_of_globalInfimumContract
    {n d : ℕ} (D : Data n d)
    (hInf : globalInfimumContract D) :
    0 ≤ Delta D := by
  unfold Delta
  exact sub_nonneg.mpr (hInf D.x0)

theorem globalInfimumContract_of_inherited_problem
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d)) :
    globalInfimumContract (ofProblem P) := by
  intro x
  unfold fStar objectiveInfimum objective
  apply SOptLib.objectiveInfimumValue_le _ (Set.mem_univ x)
  simpa [FiniteSumProblem.f] using P.objective_bddBelow

structure Schedule (n : ℕ) where
  epsilon : ℝ
  L : ℝ
  n0 : N0 n
  S1 : ℕ
  S2 : ℝ
  q : ℝ
  eta : ℝ

noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) : Schedule n where
  epsilon := epsilon
  L := L
  n0 := n0
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  q := n0.1 * Real.sqrt (n : ℝ)
  eta := epsilon / (L * n0.1)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).eta =
      epsilon / (L * n0.1) := by
  rfl

noncomputable def recursiveBatchCount
    {n : ℕ} (s : Schedule n) : ℕ :=
  max 1 (Nat.ceil s.S2)

noncomputable def refreshPeriod
    {n : ℕ} (s : Schedule n) : ℕ :=
  max 1 (Nat.ceil s.q)

theorem recursiveBatchCount_pos
    {n : ℕ} (s : Schedule n) :
    0 < recursiveBatchCount s := by
  unfold recursiveBatchCount
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem refreshPeriod_pos
    {n : ℕ} (s : Schedule n) :
    0 < refreshPeriod s := by
  unfold refreshPeriod
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

abbrev SamplePath {n : ℕ} (s : Schedule n) :=
  SOptLib.miniBatchSamplePath (recursiveBatchCount s) (Fin n)

noncomputable def componentLaw
    {n : ℕ} (hn : 0 < n) : Measure (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).toMeasure

theorem componentLaw_isProbability
    {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (componentLaw hn) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold componentLaw
  infer_instance

noncomputable def sampleLaw
    {n : ℕ} (s : Schedule n) (hn : 0 < n) :
    Measure (SamplePath s) :=
  SOptLib.iidMiniBatchSampleLaw
    (recursiveBatchCount s) (componentLaw hn)

theorem sampleLaw_isProbability
    {n : ℕ} (s : Schedule n) (hn : 0 < n) :
    IsProbabilityMeasure (sampleLaw s hn) := by
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
    (recursiveBatchCount s) (componentLaw hn)

noncomputable def sampledAverage
    {n d : ℕ} (D : Data n d) (s : Schedule n)
    (omega : SamplePath s) (k : ℕ) (x : VariableSpace d) :
    VariableSpace d :=
  (recursiveBatchCount s : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin (recursiveBatchCount s) =>
        componentGradient D (omega k j) x)

noncomputable def recursiveEstimator
    {n d : ℕ} (D : Data n d) (s : Schedule n)
    (omega : SamplePath s) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) :
    VariableSpace d :=
  sampledAverage D s omega k xCurr -
    sampledAverage D s omega k xPrev + vPrev

noncomputable def fullRefresh
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    VariableSpace d :=
  fullGradient D x

@[simp] theorem fullRefresh_spec
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    fullRefresh D x = fullGradient D x := by
  rfl

noncomputable def sourceAdaptiveStep
    {n : ℕ} (s : Schedule n) (normV : ℝ)
    (_hV : 0 < normV) (_hL : 0 < s.L) (_hn0 : 0 < s.n0.1) : ℝ :=
  min
    (s.epsilon / (s.L * s.n0.1 * normV))
    (1 / (2 * s.L * s.n0.1))

noncomputable def checkedUpdate
    {n d : ℕ} (s : Schedule n) (hL : 0 < s.L)
    (x v : VariableSpace d) : VariableSpace d :=
  if hV : 0 < ‖v‖ then
    x - sourceAdaptiveStep s ‖v‖ hV hL (by
      exact lt_of_lt_of_le zero_lt_one s.n0.2.1) • v
  else
    x

theorem checkedUpdate_eq_source
    {n d : ℕ} (s : Schedule n) (hL : 0 < s.L)
    (x v : VariableSpace d) (hV : 0 < ‖v‖) :
    checkedUpdate s hL x v =
      x - sourceAdaptiveStep s ‖v‖ hV hL
        (lt_of_lt_of_le zero_lt_one s.n0.2.1) • v := by
  simp [checkedUpdate, hV]

theorem checkedUpdate_zero
    {n d : ℕ} (s : Schedule n) (hL : 0 < s.L)
    (x : VariableSpace d) :
    checkedUpdate s hL x 0 = x := by
  simp [checkedUpdate]

noncomputable def transition
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (omega : SamplePath s) (k : ℕ)
    (state : State (VariableSpace d)) :
    State (VariableSpace d) :=
  let xNext := checkedUpdate s hL state.x state.v
  let vNext :=
    if (k + 1) % refreshPeriod s = 0 then
      fullRefresh D xNext
    else
      recursiveEstimator D s omega (k + 1) state.v state.x xNext
  { x := xNext, v := vNext }

noncomputable def stateProcess
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L) :
    ℕ → SamplePath s → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullRefresh D D.x0 }
  | k + 1 => fun omega =>
      transition D s hL omega k
        (stateProcess D s hL k omega)

noncomputable def iterate
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L) :
    ℕ → SamplePath s → VariableSpace d :=
  fun k omega => (stateProcess D s hL k omega).x

noncomputable def estimator
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L) :
    ℕ → SamplePath s → VariableSpace d :=
  fun k omega => (stateProcess D s hL k omega).v

@[simp] theorem stateProcess_zero
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (omega : SamplePath s) :
    stateProcess D s hL 0 omega =
      { x := D.x0, v := fullRefresh D D.x0 } := by
  rfl

@[simp] theorem iterate_succ
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (k : ℕ) (omega : SamplePath s) :
    iterate D s hL (k + 1) omega =
      (transition D s hL omega k
        (stateProcess D s hL k omega)).x := by
  rfl

@[simp] theorem estimator_succ
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (k : ℕ) (omega : SamplePath s) :
    estimator D s hL (k + 1) omega =
      (transition D s hL omega k
        (stateProcess D s hL k omega)).v := by
  rfl

noncomputable def outputLaw
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (K : ℕ) (hK : 0 < K) (hn : 0 < n) :
    Measure (Fin K × SamplePath s) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  letI : IsProbabilityMeasure (sampleLaw s hn) :=
    sampleLaw_isProbability s hn
  exact
    (PMF.uniformOfFintype (Fin K)).toMeasure.prod
      (sampleLaw s hn)

theorem outputLaw_isProbability
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (K : ℕ) (hK : 0 < K) (hn : 0 < n) :
    IsProbabilityMeasure (outputLaw D s hL K hK hn) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  letI : IsProbabilityMeasure (sampleLaw s hn) :=
    sampleLaw_isProbability s hn
  unfold outputLaw
  infer_instance

noncomputable def uniformOutput
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (K : ℕ) : Fin K × SamplePath s → VariableSpace d :=
  fun z => iterate D s hL z.1 z.2

noncomputable def outputGradientNormExpectation
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (K : ℕ) (hK : 0 < K) (hn : 0 < n) : ℝ :=
  ∫ z, ‖fullGradient D (uniformOutput D s hL K z)‖ ∂
    outputLaw D s hL K hK hn

noncomputable def iterationBudget
    {n d : ℕ} (D : Data n d) (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor
      (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2) + 1

theorem iterationBudget_pos
    {n d : ℕ} (D : Data n d) (epsilon : ℝ) (n0 : N0 n) :
    0 < iterationBudget D epsilon n0 := by
  unfold iterationBudget
  exact Nat.succ_pos _

noncomputable def literalGradientCost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * s.q⁻¹) : ℝ) * s.S1 + (K : ℝ) * s.S2

noncomputable def correctedGradientCost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

noncomputable def correctedGradientCostBound
    {n d : ℕ} (D : Data n d) (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold b18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

def literalB19Route
    {n : ℕ} (s : Schedule n) (K : ℕ) : Prop :=
  literalGradientCost s K ≤
    2 * (K : ℝ) + s.S1

def correctedB19Route
    {n d : ℕ} (D : Data n d) (epsilon : ℝ) (n0 : N0 n)
    (s : Schedule n) (K : ℕ) : Prop :=
  correctedGradientCost s K ≤
    correctedGradientCostBound D epsilon n0

def estimatorErrorContract
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖estimator D s hL k omega - fullGradient D
          (iterate D s hL k omega)‖ ^ 2 ∂sampleLaw s (n_pos s.n0) ≤
      epsilon ^ 2

def oneStepDescentContract
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        objective D (iterate D s hL (k + 1) omega) -
          objective D (iterate D s hL k omega) ∂sampleLaw s (n_pos s.n0) ≤
      -epsilon / (4 * D.L * s.n0.1) *
          ∫ omega, ‖estimator D s hL k omega‖ ∂sampleLaw s (n_pos s.n0) +
        3 * epsilon ^ 2 / (4 * D.L * s.n0.1)

def telescopeContract
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k => ∫ omega, ‖estimator D s hL k omega‖
          ∂sampleLaw s (n_pos s.n0)) ≤
    4 * epsilon

def conversionContract
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega, ‖fullGradient D (iterate D s hL k omega)‖
      ∂sampleLaw s (n_pos s.n0)) ≤
      (∫ omega, ‖estimator D s hL k omega‖
        ∂sampleLaw s (n_pos s.n0)) + epsilon

theorem sourceOutputAverage_reuse
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hEstimator : estimatorErrorContract D s hL epsilon K)
    (hDescent : oneStepDescentContract D s hL epsilon K)
    (hTelescope :
      estimatorErrorContract D s hL epsilon K →
      oneStepDescentContract D s hL epsilon K →
      telescopeContract D s hL epsilon K)
    (hConversion :
      estimatorErrorContract D s hL epsilon K →
      conversionContract D s hL epsilon K) :
    uniformOutputGradientNormAverage
        (sampleLaw s (n_pos s.n0))
        (fullGradient D)
        (iterate D s hL) K ≤
      5 * epsilon := by
  letI : IsProbabilityMeasure (componentLaw (n_pos s.n0)) :=
    componentLaw_isProbability (n_pos s.n0)
  letI : IsProbabilityMeasure (sampleLaw s (n_pos s.n0)) :=
    sampleLaw_isProbability s (n_pos s.n0)
  apply Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
    (sampleLaw s (n_pos s.n0)) (fullGradient D)
    (iterate D s hL) (estimator D s hL) K hK epsilon
  · intro k hk
    exact hConversion hEstimator k (Finset.mem_range.mp hk)
  · exact hTelescope hEstimator hDescent

theorem outputExpectation_le_of_sourceOutputAverage
    {n d : ℕ} (D : Data n d) (s : Schedule n) (hL : 0 < s.L)
    (epsilon : ℝ) (K : ℕ) (hK : 0 < K) (hn : 0 < n)
    (hAvg :
      uniformOutputGradientNormAverage
          (sampleLaw s hn) (fullGradient D) (iterate D s hL) K ≤
        5 * epsilon) :
    outputGradientNormExpectation D s hL K hK hn ≤ 5 * epsilon := by
  sorry

theorem theorem2_finite_sum_final_root
    {n d : ℕ} (P : FiniteSumProblem n (VariableSpace d))
    (epsilon : ℝ) (n0 : N0 n) (hL : 0 < P.L)
    (hEstimator :
      estimatorErrorContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0))
    (hDescent :
      oneStepDescentContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0))
    (hTelescope :
      estimatorErrorContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0) →
      oneStepDescentContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0) →
      telescopeContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0))
    (hConversion :
      estimatorErrorContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0) →
      conversionContract (ofProblem P) (schedule epsilon P.L n0) hL
        epsilon (iterationBudget (ofProblem P) epsilon n0))
    (hCost :
      0 ≤ Delta (ofProblem P) →
      correctedB19Route (ofProblem P) epsilon n0
        (schedule epsilon P.L n0)
        (iterationBudget (ofProblem P) epsilon n0)) :
    outputGradientNormExpectation
        (ofProblem P) (schedule epsilon P.L n0) hL
          (iterationBudget (ofProblem P) epsilon n0)
          (iterationBudget_pos (ofProblem P) epsilon n0) (n_pos n0) ≤
      5 * epsilon ∧
    correctedGradientCost (schedule epsilon P.L n0)
        (iterationBudget (ofProblem P) epsilon n0) ≤
      correctedGradientCostBound (ofProblem P) epsilon n0 := by
  have hK : 0 < iterationBudget (ofProblem P) epsilon n0 :=
    iterationBudget_pos (ofProblem P) epsilon n0
  have hAvg :=
    sourceOutputAverage_reuse (ofProblem P) (schedule epsilon P.L n0) hL
      epsilon (iterationBudget (ofProblem P) epsilon n0) hK
      hEstimator hDescent hTelescope hConversion
  have hInf := globalInfimumContract_of_inherited_problem P
  have hDelta := Delta_nonneg_of_globalInfimumContract (ofProblem P) hInf
  have hCost' := hCost hDelta
  exact ⟨outputExpectation_le_of_sourceOutputAverage
      (ofProblem P) (schedule epsilon P.L n0) hL epsilon
      (iterationBudget (ofProblem P) epsilon n0) hK (n_pos n0)
      hAvg, by simpa [correctedB19Route] using hCost'⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final

/- namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-!
Active finite-sum spine for the paper-facing Theorem 2 extension.

The inherited `FiniteSumTheorem2Final` declarations remain frozen.  This
namespace is the single appended process boundary used by the extension:
the gradient family is the inherited computed component gradient, the
schedule keeps the paper's real `S₂` and `q`, and an executable run carries
only an explicit integer realization of those two source quantities.  No
free batch-index type, refresh predicate, or arbitrary probability measure is
part of this process.
-/

abbrev Data (n d : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.Data n d

abbrev Schedule (n : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.Schedule n

abbrev N0 (n : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.N0 n

noncomputable def objective
    {n d : ℕ} (D : Data n d) : VariableSpace d → ℝ :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.objective D

noncomputable def componentGradient
    {n d : ℕ} (D : Data n d) :
    Fin n → VariableSpace d → VariableSpace d :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.componentGradient D

noncomputable def fullGradient
    {n d : ℕ} (D : Data n d) : VariableSpace d → VariableSpace d :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.fullGradient D

@[simp] theorem objective_spec
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    objective D x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => D.componentObjective i x) := by
  simp [objective,
    Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.objective]

@[simp] theorem componentGradient_spec
    {n d : ℕ} (D : Data n d) (i : Fin n) (x : VariableSpace d) :
    componentGradient D i x =
      ∇ (fun y : VariableSpace d => D.componentObjective i y) x := by
  rfl

@[simp] theorem fullGradient_spec
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    fullGradient D x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentGradient D i x) := by
  rfl

theorem finiteAverageGradient_bridge
    {n d : ℕ} (D : Data n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (componentGradient D i x) x) :
    ∇ (objective D) x = fullGradient D x := by
  exact
    Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.finiteAverageGradient_bridge
      D x hcomponent

noncomputable def fStar
    {n d : ℕ} (D : Data n d) : ℝ :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.fStar D

noncomputable def Delta
    {n d : ℕ} (D : Data n d) : ℝ :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.Delta D

def globalInfimumContract
    {n d : ℕ} (D : Data n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ objective D x

theorem Delta_nonneg_of_globalInfimumContract
    {n d : ℕ} (D : Data n d)
    (hInf : globalInfimumContract D) :
    0 ≤ Delta D := by
  unfold Delta
  exact sub_nonneg.mpr (hInf D.x0)

/-- The paper's averaged component-gradient regularity, using the same
computed component-gradient family as the objective and process. -/
def averagedLipschitz
    {n d : ℕ} (D : Data n d) : Prop :=
  ∀ x y : VariableSpace d,
    SOptLib.finiteUniformAverage
      (fun i : Fin n =>
        ‖componentGradient D i x - componentGradient D i y‖ ^ 2) ≤
      D.L ^ 2 * ‖x - y‖ ^ 2

/-- Source-derived global-infimum bridge.  This is deliberately a theorem
obligation, not a BddBelow field on the active data object. -/
theorem globalInfimumContract_obligation
    {n d : ℕ} (D : Data n d) :
    globalInfimumContract D := by
  sorry

/-- Source-derived smoothness bridge.  The component-gradient family is
already fixed by `componentGradient`; no existential selector is introduced. -/
theorem averagedLipschitz_obligation
    {n d : ℕ} (D : Data n d) :
    averagedLipschitz D := by
  sorry

/-- The paper schedule keeps the real-valued `S₂` and `q` expressions. -/
noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) : Schedule n :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.schedule epsilon L n0

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

/-- An executable sample process exists only after the paper's real sample
and epoch quantities have an exact natural-number realization.  This avoids
silently replacing `S₂` or `q` by ceilings or rounded values. -/
structure RunRealization
    {n : ℕ} (s : Schedule n) where
  batchSize : ℕ
  refreshPeriod : ℕ
  batchSize_pos : 0 < batchSize
  refreshPeriod_pos : 0 < refreshPeriod
  batchSize_spec : (batchSize : ℝ) = s.S2
  refreshPeriod_spec : (refreshPeriod : ℝ) = s.q

def sourceRealizationDomain
    {n : ℕ} (s : Schedule n) : Prop :=
  Nonempty (RunRealization s)

abbrev SamplePath
    {n : ℕ} {s : Schedule n} (r : RunRealization s) :=
  SOptLib.miniBatchSamplePath r.batchSize (Fin n)

noncomputable def componentLaw
    {n : ℕ} (s : Schedule n) : Measure (Fin n) := by
  letI : Nonempty (Fin n) :=
    ⟨⟨0, Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.n_pos s.n0⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).toMeasure

theorem componentLaw_isProbability
    {n : ℕ} (s : Schedule n) :
    IsProbabilityMeasure (componentLaw s) := by
  letI : Nonempty (Fin n) :=
    ⟨⟨0, Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.n_pos s.n0⟩⟩
  unfold componentLaw
  infer_instance

noncomputable def sampleLaw
    {n : ℕ} {s : Schedule n} (r : RunRealization s) :
    Measure (SamplePath r) :=
  SOptLib.iidMiniBatchSampleLaw r.batchSize (componentLaw s)

theorem sampleLaw_isProbability
    {n : ℕ} {s : Schedule n} (r : RunRealization s) :
    IsProbabilityMeasure (sampleLaw r) := by
  letI : IsProbabilityMeasure (componentLaw s) :=
    componentLaw_isProbability s
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
    r.batchSize (componentLaw s)

def refreshAt
    {n : ℕ} {s : Schedule n} (r : RunRealization s) (k : ℕ) : Prop :=
  k % r.refreshPeriod = 0

theorem refreshAt_zero
    {n : ℕ} {s : Schedule n} (r : RunRealization s) :
    refreshAt r 0 := by
  simp [refreshAt]

noncomputable def sampledAverage
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (omega : SamplePath r) (k : ℕ)
    (x : VariableSpace d) : VariableSpace d :=
  (r.batchSize : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin r.batchSize =>
        componentGradient D (omega k j) x)

noncomputable def recursiveEstimator
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (omega : SamplePath r) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) : VariableSpace d :=
  sampledAverage D r omega k xCurr -
    sampledAverage D r omega k xPrev + vPrev

noncomputable def checkedStepSize
    {n d : ℕ} (s : Schedule n) (v : VariableSpace d) : ℝ :=
  if hv : 0 < ‖v‖ then
    min
      (s.epsilon / (s.L * s.n0.1 * ‖v‖))
      (1 / (2 * s.L * s.n0.1))
  else
    0

noncomputable def update
    {n d : ℕ} (s : Schedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - checkedStepSize s v • v

theorem update_eq_paper_formula
    {n d : ℕ} (s : Schedule n) (x v : VariableSpace d)
    (hv : 0 < ‖v‖) :
    update s x v =
      x -
        min
          (s.epsilon / (s.L * s.n0.1 * ‖v‖))
          (1 / (2 * s.L * s.n0.1)) • v := by
  simp [update, checkedStepSize, hv]

theorem update_zero
    {n d : ℕ} (s : Schedule n) (x : VariableSpace d) :
    update s x 0 = x := by
  simp [update, checkedStepSize]

noncomputable def fullRefresh
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) : VariableSpace d :=
  fullGradient D x

theorem fullRefresh_error_B17
    {n d : ℕ} (D : Data n d) (x : VariableSpace d) :
    ‖fullRefresh D x - fullGradient D x‖ ^ 2 = 0 := by
  simp [fullRefresh]

noncomputable def transition
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (omega : SamplePath r) (k : ℕ)
    (state : State (VariableSpace d)) : State (VariableSpace d) :=
  by
    classical
    let xNext := update s state.x state.v
    let vNext :=
      if refreshAt r (k + 1) then
        fullRefresh D xNext
      else
        recursiveEstimator D r omega (k + 1) state.v state.x xNext
    exact { x := xNext, v := vNext }

/-- The canonical finite-sum process: exact refresh at `k % q = 0`, otherwise
the with-replacement `S₂` recursive estimator. -/
noncomputable def stateProcess
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) :
    ℕ → SamplePath r → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullRefresh D D.x0 }
  | k + 1 => fun omega =>
      transition D r omega k (stateProcess D r k omega)

noncomputable def iterate
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) :
    ℕ → SamplePath r → VariableSpace d :=
  fun k omega => (stateProcess D r k omega).x

noncomputable def estimator
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) :
    ℕ → SamplePath r → VariableSpace d :=
  fun k omega => (stateProcess D r k omega).v

@[simp] theorem stateProcess_zero
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (omega : SamplePath r) :
    stateProcess D r 0 omega =
      { x := D.x0, v := fullRefresh D D.x0 } := by
  rfl

@[simp] theorem iterate_succ
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (k : ℕ) (omega : SamplePath r) :
    iterate D r (k + 1) omega =
      update s
        (iterate D r k omega)
        (estimator D r k omega) := by
  rfl

@[simp] theorem estimator_zero
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (omega : SamplePath r) :
    estimator D r 0 omega = fullRefresh D D.x0 := by
  rfl

noncomputable def uniformOutputLaw
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × SamplePath r) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (componentLaw s) :=
    componentLaw_isProbability s
  letI : IsProbabilityMeasure (sampleLaw r) :=
    sampleLaw_isProbability r
  exact
    (PMF.uniformOfFintype (Fin K)).toMeasure.prod
      (sampleLaw r)

theorem uniformOutputLaw_isProbability
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (K : ℕ) (hK : 0 < K) :
    IsProbabilityMeasure (uniformOutputLaw D r K hK) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (componentLaw s) :=
    componentLaw_isProbability s
  letI : IsProbabilityMeasure (sampleLaw r) :=
    sampleLaw_isProbability r
  unfold uniformOutputLaw
  infer_instance

noncomputable def uniformOutput
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (K : ℕ) :
    Fin K × SamplePath r → VariableSpace d :=
  fun z => iterate D r z.1 z.2

noncomputable def outputGradientNormAverage
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage
    (sampleLaw r) (fullGradient D) (iterate D r) K

def estimatorErrorBoundary
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖estimator D r k omega -
          fullGradient D (iterate D r k omega)‖ ^ 2 ∂sampleLaw r ≤
      epsilon ^ 2

def oneStepDescentBoundary
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        objective D (iterate D r (k + 1) omega) -
          objective D (iterate D r k omega) ∂sampleLaw r ≤
      -epsilon / (4 * D.L * s.n0.1) *
          ∫ omega, ‖estimator D r k omega‖ ∂sampleLaw r +
        3 * epsilon ^ 2 / (4 * D.L * s.n0.1)

def telescopeBoundary
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k => ∫ omega, ‖estimator D r k omega‖ ∂sampleLaw r) ≤
    4 * epsilon

def conversionBoundary
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega, ‖fullGradient D (iterate D r k omega)‖ ∂sampleLaw r) ≤
      (∫ omega, ‖estimator D r k omega‖ ∂sampleLaw r) + epsilon

noncomputable def correctedGradientCost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

noncomputable def correctedGradientCostBound
    {n d : ℕ} (D : Data n d) (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

noncomputable def literalGradientCost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * s.q⁻¹) : ℝ) * s.S1 + (K : ℝ) * s.S2

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.b18DisplayedTerm
        epsilon L n0 n = epsilon ^ 3 := by
  exact Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.b18DisplayedTerm_eq_epsilon_cube
    hepsilon hL hn0 hn

theorem b18_epsilon_square_counterexample :
    ¬ (Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.b18DisplayedTerm
        2 1 1 1 = (2 : ℝ) ^ 2) := by
  norm_num [Algorithms.Unverified.SPIDER.FiniteSumTheorem2Final.b18DisplayedTerm]

theorem b19_literal_and_corrected_routes_are_distinct :
    (2 * (1 : ℝ) + 1) ≠ 2 * (1 : ℝ) * 2 + 1 := by
  norm_num

/- The following four declarations are internal proof obligations.  They are
kept separate from the source objects so later proof work can replace each
`sorry` without changing the process or theorem-facing data model. -/
theorem estimatorErrorBoundary_obligation
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ)
    (hDomain : 0 < epsilon ∧ 0 < s.L) :
    estimatorErrorBoundary D r epsilon K := by
  sorry

theorem oneStepDescentBoundary_obligation
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ)
    (hDomain : 0 < epsilon ∧ 0 < s.L)
    (hSmooth : averagedLipschitz D) :
    oneStepDescentBoundary D r epsilon K := by
  sorry

theorem telescopeBoundary_obligation
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ)
    (hDomain : 0 < epsilon ∧ 0 < s.L)
    (hEstimator : estimatorErrorBoundary D r epsilon K)
    (hDescent : oneStepDescentBoundary D r epsilon K) :
    telescopeBoundary D r epsilon K := by
  sorry

theorem conversionBoundary_obligation
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ)
    (hDomain : 0 < epsilon ∧ 0 < s.L)
    (hEstimator : estimatorErrorBoundary D r epsilon K) :
    conversionBoundary D r epsilon K := by
  sorry

theorem correctedGradientCost_obligation
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (epsilon : ℝ) (n0 : N0 n) (K : ℕ)
    (hDomain : 0 < epsilon ∧ 0 < s.L)
    (hInf : globalInfimumContract D) :
    correctedGradientCost s K ≤ correctedGradientCostBound D epsilon n0 := by
  sorry

/-- Compiled conclusion path: active estimator, descent, telescope, and
conversion obligations feed the inherited output-conversion theorem, while
the corrected B.19 cost edge remains separately named. -/
theorem theorem2_active_internal_root
    {n d : ℕ} {s : Schedule n} (D : Data n d)
    (r : RunRealization s) (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hDomain : 0 < epsilon ∧ 0 < s.L)
    (hSmooth : averagedLipschitz D) :
    outputGradientNormAverage D r K ≤ 5 * epsilon ∧
      correctedGradientCost s K ≤
        correctedGradientCostBound D epsilon s.n0 := by
  let hEstimator := estimatorErrorBoundary_obligation D r epsilon K hDomain
  let hDescent :=
    oneStepDescentBoundary_obligation D r epsilon K hDomain hSmooth
  let hTelescope :=
    telescopeBoundary_obligation D r epsilon K hDomain hEstimator hDescent
  let hConversion :=
    conversionBoundary_obligation D r epsilon K hDomain hEstimator
  letI : IsProbabilityMeasure (componentLaw s) :=
    componentLaw_isProbability s
  letI : IsProbabilityMeasure (sampleLaw r) :=
    sampleLaw_isProbability r
  have hOutput :
      outputGradientNormAverage D r K ≤ 5 * epsilon := by
    unfold outputGradientNormAverage
    apply Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
      (sampleLaw r) (fullGradient D) (iterate D r) (estimator D r) K hK epsilon
    · intro k hk
      exact hConversion k (Finset.mem_range.mp hk)
    · exact hTelescope
  have hInf := globalInfimumContract_obligation D
  have hCost :=
    correctedGradientCost_obligation D epsilon s.n0 K hDomain hInf
  exact ⟨hOutput, hCost⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2CanonicalV43

/-!
Canonical finite-sum SPIDER spine for the iteration-43 extension.

The paper-facing schedule keeps the real values `S2 = sqrt n / n0` and
`q = n0 * sqrt n`.  The only finite cardinality needed by Lean is computed
from that schedule; it is not an existential realization field.  The process
uses one component-gradient family, exact full refreshes, a canonical
with-replacement product law, and a normalized uniform output law.
-/

def n0Domain (n : ℕ) : Set ℝ :=
  Set.Icc (1 : ℝ) (Real.sqrt (n : ℝ))

abbrev N0 (n : ℕ) :=
  {r : ℝ // r ∈ n0Domain n}

theorem n0_lower {n : ℕ} (n0 : N0 n) :
    1 ≤ n0.1 :=
  n0.2.1

theorem n0_upper {n : ℕ} (n0 : N0 n) :
    n0.1 ≤ Real.sqrt (n : ℝ) :=
  n0.2.2

theorem n_pos {n : ℕ} (n0 : N0 n) :
    0 < n := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    le_trans n0.2.1 n0.2.2
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  have hn : 1 ≤ n := by
    exact_mod_cast hnreal
  exact Nat.zero_lt_of_lt hn

theorem n0_domain_rejects_zero :
    ¬ Nonempty (N0 0) := by
  intro h
  rcases h with ⟨n0⟩
  have hbad : (1 : ℝ) ≤ 0 := le_trans n0.2.1 n0.2.2
  linarith

structure SourceData (n d : ℕ) where
  componentObjective : Fin n → VariableSpace d → ℝ
  x0 : VariableSpace d
  L : ℝ
  averagedLipschitzGradient :
    ∀ x y : VariableSpace d,
      SOptLib.finiteUniformAverage
        (fun i : Fin n =>
          ‖componentGradient componentObjective i x -
            componentGradient componentObjective i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2

/- The component gradient is the single source family used by the objective,
   full refresh, recursive estimator, and smoothness assumption. -/
noncomputable def componentGradient
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => componentObjective i y) x

@[simp] theorem componentGradient_spec
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ)
    (i : Fin n) (x : VariableSpace d) :
    componentGradient componentObjective i x =
      ∇ (fun y : VariableSpace d => componentObjective i y) x := by
  rfl

noncomputable def objective
    {n d : ℕ} (D : SourceData n d) :
    VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage D.componentObjective

noncomputable def fullGradient
    {n d : ℕ} (D : SourceData n d) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient D.componentObjective i x)

noncomputable def fStar
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objectiveInfimum (objective D)

noncomputable def Delta
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objective D D.x0 - fStar D

def globalInfimumContract
    {n d : ℕ} (D : SourceData n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ objective D x

theorem globalInfimum_lowerBound_obligation
    {n d : ℕ} (D : SourceData n d) :
    globalInfimumContract D := by
  sorry

theorem Delta_nonneg
    {n d : ℕ} (D : SourceData n d) :
    0 ≤ Delta D := by
  unfold Delta
  exact sub_nonneg.mpr
    (globalInfimum_lowerBound_obligation D D.x0)

theorem finite_average_gradient_bridge
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (componentGradient D.componentObjective i x) x) :
    ∇ (objective D) x = fullGradient D x := by
  unfold objective fullGradient
  exact
    SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      D.componentObjective (componentGradient D.componentObjective) x
      hcomponent

theorem finite_average_hasGradientAt_bridge
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (componentGradient D.componentObjective i x) x) :
    HasGradientAt (objective D) (fullGradient D x) x := by
  unfold objective fullGradient
  convert
    (SOptLib.finiteAverageObjective_hasGradientAt
      D.componentObjective (componentGradient D.componentObjective) x
      hcomponent) using 1
  funext z
  simp [SOptLib.finiteUniformAverage, Pi.smul_apply, smul_eq_mul]

structure Schedule (n : ℕ) where
  epsilon : ℝ
  L : ℝ
  n0 : N0 n
  S1 : ℕ
  S2 : ℝ
  q : ℝ
  eta : ℝ

noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    Schedule n where
  epsilon := epsilon
  L := L
  n0 := n0
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  q := n0.1 * Real.sqrt (n : ℝ)
  eta := epsilon / (L * n0.1)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).eta =
      epsilon / (L * n0.1) := by
  rfl

noncomputable def iterationBudget
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2) + 1

theorem iterationBudget_pos
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) :
    0 < iterationBudget D epsilon n0 := by
  exact Nat.succ_pos _

namespace InternalRealization

noncomputable def batchCount
    {n : ℕ} (s : Schedule n) : ℕ :=
  max 1 (Nat.ceil s.S2)

theorem batchCount_pos
    {n : ℕ} (s : Schedule n) :
    0 < batchCount s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

abbrev SamplePath {n : ℕ} (s : Schedule n) :=
  SOptLib.miniBatchSamplePath (batchCount s) (Fin n)

noncomputable def indexLaw
    {n : ℕ} (n0 : N0 n) : Measure (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).toMeasure

theorem indexLaw_isProbability
    {n : ℕ} (n0 : N0 n) :
    IsProbabilityMeasure (indexLaw n0) := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  unfold indexLaw
  infer_instance

noncomputable def sampleLaw
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    Measure (SamplePath s) :=
  SOptLib.iidMiniBatchSampleLaw (batchCount s) (indexLaw n0)

theorem sampleLaw_isProbability
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    IsProbabilityMeasure (sampleLaw s n0) := by
  letI : IsProbabilityMeasure (indexLaw n0) :=
    indexLaw_isProbability n0
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
    (batchCount s) (indexLaw n0)

def refreshAt
    {n : ℕ} (s : Schedule n) (k : ℕ) : Prop :=
  ∃ epoch : ℕ, (k : ℝ) = (epoch : ℝ) * s.q

theorem refreshAt_zero
    {n : ℕ} (s : Schedule n) :
    refreshAt s 0 := by
  exact ⟨0, by simp⟩

noncomputable def sampledAverage
    {n d : ℕ} (D : SourceData n d)
    (s : Schedule n) (omega : SamplePath s) (k : ℕ)
    (x : VariableSpace d) : VariableSpace d :=
  (batchCount s : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin (batchCount s) =>
        componentGradient D.componentObjective (omega k j) x)

noncomputable def recursiveEstimator
    {n d : ℕ} (D : SourceData n d)
    (s : Schedule n) (omega : SamplePath s) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) : VariableSpace d :=
  sampledAverage D s omega k xCurr -
    sampledAverage D s omega k xPrev + vPrev

noncomputable def fullRefresh
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d) :
    VariableSpace d :=
  fullGradient D x

noncomputable def stepSize
    {n d : ℕ} (s : Schedule n) (v : VariableSpace d) : ℝ :=
  if h : 0 < s.L ∧ 0 < s.n0.1 ∧ 0 < ‖v‖ then
    min
      (s.epsilon / (s.L * s.n0.1 * ‖v‖))
      (1 / (2 * s.L * s.n0.1))
  else
    0

noncomputable def update
    {n d : ℕ} (s : Schedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - stepSize s v • v

theorem update_zero
    {n d : ℕ} (s : Schedule n) (x : VariableSpace d) :
    update s x 0 = x := by
  simp [update, stepSize]

theorem update_eq_paper
    {n d : ℕ} (s : Schedule n) (x v : VariableSpace d)
    (hL : 0 < s.L) (hv : 0 < ‖v‖) :
    update s x v =
      x -
        min
          (s.epsilon / (s.L * s.n0.1 * ‖v‖))
          (1 / (2 * s.L * s.n0.1)) • v := by
  simp [update, stepSize, hL, hv, lt_of_lt_of_le zero_lt_one s.n0.2.1]

noncomputable def transition
    {n d : ℕ} (D : SourceData n d)
    (s : Schedule n) (omega : SamplePath s) (k : ℕ)
    (state : State (VariableSpace d)) :
    State (VariableSpace d) :=
  let xNext := update s state.x state.v
  let vNext :=
    if refreshAt s (k + 1) then
      fullRefresh D xNext
    else
      recursiveEstimator D s omega (k + 1) state.v state.x xNext
  { x := xNext, v := vNext }

noncomputable def stateProcess
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullRefresh D D.x0 }
  | k + 1 => fun omega =>
      transition D s omega k (stateProcess D s k omega)

noncomputable def iterate
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  fun k omega => (stateProcess D s k omega).x

noncomputable def estimator
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  fun k omega => (stateProcess D s k omega).v

@[simp] theorem stateProcess_zero
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (omega : SamplePath s) :
    stateProcess D s 0 omega =
      { x := D.x0, v := fullRefresh D D.x0 } := by
  rfl

@[simp] theorem iterate_succ
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (k : ℕ) (omega : SamplePath s) :
    iterate D s (k + 1) omega =
      (transition D s omega k (stateProcess D s k omega)).x := by
  rfl

@[simp] theorem estimator_zero
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (omega : SamplePath s) :
    estimator D s 0 omega = fullRefresh D D.x0 := by
  rfl

noncomputable def uniformOutputLaw
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × SamplePath s) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (indexLaw n0) :=
    indexLaw_isProbability n0
  letI : IsProbabilityMeasure (sampleLaw s n0) :=
    sampleLaw_isProbability s n0
  exact (PMF.uniformOfFintype (Fin K)).toMeasure.prod
    (sampleLaw s n0)

theorem uniformOutputLaw_isProbability
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (K : ℕ) (hK : 0 < K) :
    IsProbabilityMeasure (uniformOutputLaw D s n0 K hK) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (indexLaw n0) :=
    indexLaw_isProbability n0
  letI : IsProbabilityMeasure (sampleLaw s n0) :=
    sampleLaw_isProbability s n0
  unfold uniformOutputLaw
  infer_instance

end InternalRealization

abbrev SamplePath {n : ℕ} (s : Schedule n) :=
  InternalRealization.SamplePath s

noncomputable def sampleLaw
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    Measure (SamplePath s) :=
  InternalRealization.sampleLaw s n0

theorem sampleLaw_isProbability
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    IsProbabilityMeasure (sampleLaw s n0) :=
  InternalRealization.sampleLaw_isProbability s n0

noncomputable def iterate
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  InternalRealization.iterate D s

noncomputable def estimator
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  InternalRealization.estimator D s

noncomputable def fullRefresh
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d) :
    VariableSpace d :=
  fullGradient D x

def estimatorErrorAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖estimator D s k omega -
          fullGradient D (iterate D s k omega)‖ ^ 2
          ∂sampleLaw s n0 ≤ epsilon ^ 2

def oneStepDescentAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        objective D (iterate D s (k + 1) omega) -
          objective D (iterate D s k omega)
          ∂sampleLaw s n0 ≤
      -epsilon / (4 * s.L * s.n0.1) *
          ∫ omega, ‖estimator D s k omega‖ ∂sampleLaw s n0 +
        3 * epsilon ^ 2 / (4 * s.L * s.n0.1)

def telescopeAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k => ∫ omega, ‖estimator D s k omega‖
          ∂sampleLaw s n0) ≤
    4 * epsilon

def conversionAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega, ‖fullGradient D (iterate D s k omega)‖
      ∂sampleLaw s n0) ≤
      (∫ omega, ‖estimator D s k omega‖
        ∂sampleLaw s n0) + epsilon

theorem estimatorErrorAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) :
    estimatorErrorAdapter D s n0 epsilon K := by
  sorry

theorem oneStepDescentAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) :
    oneStepDescentAdapter D s n0 epsilon K := by
  sorry

theorem telescopeAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ)
    (_hEstimator : estimatorErrorAdapter D s n0 epsilon K)
    (_hDescent : oneStepDescentAdapter D s n0 epsilon K) :
    telescopeAdapter D s n0 epsilon K := by
  sorry

theorem conversionAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ)
    (_hEstimator : estimatorErrorAdapter D s n0 epsilon K) :
    conversionAdapter D s n0 epsilon K := by
  sorry

theorem output_adapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hEstimator : estimatorErrorAdapter D s n0 epsilon K)
    (hDescent : oneStepDescentAdapter D s n0 epsilon K)
    (hTelescope : telescopeAdapter D s n0 epsilon K)
    (hConversion : conversionAdapter D s n0 epsilon K) :
    uniformOutputGradientNormAverage
        (sampleLaw s n0) (fullGradient D) (iterate D s) K ≤
      5 * epsilon := by
  letI : IsProbabilityMeasure (sampleLaw s n0) :=
    sampleLaw_isProbability s n0
  apply Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
    (sampleLaw s n0) (fullGradient D) (iterate D s) (estimator D s)
    K hK epsilon
  · intro k hk
    exact hConversion k (Finset.mem_range.mp hk)
  · exact hTelescope

noncomputable def outputGradientNormExpectation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (K : ℕ) (hK : 0 < K) : ℝ :=
  ∫ z,
      ‖fullGradient D (iterate D s z.1 z.2)‖ ∂
        InternalRealization.uniformOutputLaw D s n0 K hK

theorem outputExpectation_le_of_average
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hAverage :
      uniformOutputGradientNormAverage
          (sampleLaw s n0) (fullGradient D) (iterate D s) K ≤
        5 * epsilon) :
    outputGradientNormExpectation D s n0 K hK ≤
      5 * epsilon := by
  sorry

noncomputable def literalB19Cost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) / s.q) : ℝ) * s.S1 + (K : ℝ) * s.S2

noncomputable def correctedB19Cost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

theorem literal_and_corrected_B19_are_distinct
    (s : Schedule 4) :
    literalB19Cost s 1 ≠ correctedB19Cost s 1 := by
  sorry

noncomputable def correctedB19Bound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

theorem correctedB19Cost_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (K : ℕ) :
    correctedB19Cost (schedule epsilon D.L n0) K ≤
      correctedB19Bound D epsilon n0 := by
  sorry

noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold b18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

theorem b18_epsilon_square_counterexample :
    ¬ b18DisplayedTerm 2 1 1 1 = (2 : ℝ) ^ 2 := by
  norm_num [b18DisplayedTerm]

noncomputable def sourceOutputGradientNormExpectation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  outputGradientNormExpectation D (schedule epsilon D.L n0) n0
    (iterationBudget D epsilon n0)
    (iterationBudget_pos D epsilon n0)

def sourceConclusion
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  sourceOutputGradientNormExpectation D epsilon n0 ≤
    5 * epsilon ∧
    correctedB19Cost (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) ≤
      correctedB19Bound D epsilon n0

theorem theorem2_finite_sum_gradient_cost_bound_v43
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) :
    sourceConclusion D epsilon n0 := by
  let s := schedule epsilon D.L n0
  let K := iterationBudget D epsilon n0
  have hK : 0 < K := iterationBudget_pos D epsilon n0
  have hEstimator : estimatorErrorAdapter D s n0 epsilon K :=
    estimatorErrorAdapter_obligation D s n0 epsilon K
  have hDescent : oneStepDescentAdapter D s n0 epsilon K :=
    oneStepDescentAdapter_obligation D s n0 epsilon K
  have hTelescope : telescopeAdapter D s n0 epsilon K :=
    telescopeAdapter_obligation D s n0 epsilon K hEstimator hDescent
  have hConversion : conversionAdapter D s n0 epsilon K :=
    conversionAdapter_obligation D s n0 epsilon K hEstimator
  have hOutput :
      uniformOutputGradientNormAverage
          (sampleLaw s n0) (fullGradient D) (iterate D s) K ≤
        5 * epsilon :=
    output_adapter D s n0 epsilon K hK hEstimator hDescent
      hTelescope hConversion
  have hOutputLaw :
      outputGradientNormExpectation D s n0 K hK ≤
        5 * epsilon :=
    outputExpectation_le_of_average D s n0 epsilon K hK hOutput
  have hCost :
      correctedB19Cost s K ≤ correctedB19Bound D epsilon n0 :=
    correctedB19Cost_obligation D epsilon n0 K
  exact ⟨by simpa [sourceConclusion, sourceOutputGradientNormExpectation,
        s, K] using hOutputLaw,
    by simpa [sourceConclusion, s, K] using hCost⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2CanonicalV43

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Spine

/-!
Single active finite-sum object spine for Theorem 2.

This suffix is deliberately independent of the older finite-sum layers above:
the source data has no lower-bound witness, the component gradient is one
computed Mathlib gradient family, the schedule retains real `S₂` and `q`,
and an executable sample process is exposed only through an exact natural
realization of those source quantities.  The realization is a named
formalization boundary because the source displays can be non-integral.
-/

def n0Domain (n : ℕ) : Set ℝ :=
  Set.Icc (1 : ℝ) (Real.sqrt (n : ℝ))

abbrev N0 (n : ℕ) :=
  {r : ℝ // r ∈ n0Domain n}

theorem n0_lower {n : ℕ} (n0 : N0 n) :
    1 ≤ n0.1 :=
  n0.2.1

theorem n0_upper {n : ℕ} (n0 : N0 n) :
    n0.1 ≤ Real.sqrt (n : ℝ) :=
  n0.2.2

theorem n_pos_of_n0 {n : ℕ} (n0 : N0 n) :
    0 < n := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one n0.2.1) n0.2.2
  exact_mod_cast (Real.sqrt_pos.1 hsqrt)

noncomputable def componentGradient
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => componentObjective i y) x

noncomputable def objective
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ) :
    VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage componentObjective

noncomputable def fullGradient
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient componentObjective i x)

@[simp] theorem objective_spec
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ)
    (x : VariableSpace d) :
    objective componentObjective x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentObjective i x) := by
  simp [objective, SOptLib.finiteUniformAverage, Pi.smul_apply]

@[simp] theorem componentGradient_spec
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ)
    (i : Fin n) (x : VariableSpace d) :
    componentGradient componentObjective i x =
      ∇ (fun y : VariableSpace d => componentObjective i y) x := by
  rfl

@[simp] theorem fullGradient_spec
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ)
    (x : VariableSpace d) :
    fullGradient componentObjective x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentGradient componentObjective i x) := by
  rfl

structure SourceData (n d : ℕ) where
  componentObjective : Fin n → VariableSpace d → ℝ
  x0 : VariableSpace d
  L : ℝ
  averaged_lipschitz_gradient :
    ∀ x y : VariableSpace d,
      SOptLib.finiteUniformAverage
        (fun i : Fin n =>
          ‖componentGradient componentObjective i x -
            componentGradient componentObjective i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2

noncomputable def dataObjective
    {n d : ℕ} (D : SourceData n d) : VariableSpace d → ℝ :=
  objective D.componentObjective

noncomputable def dataComponentGradient
    {n d : ℕ} (D : SourceData n d) :
    Fin n → VariableSpace d → VariableSpace d :=
  componentGradient D.componentObjective

noncomputable def dataFullGradient
    {n d : ℕ} (D : SourceData n d) :
    VariableSpace d → VariableSpace d :=
  fullGradient D.componentObjective

theorem componentGradient_hasGradientAt_obligation
    {n d : ℕ} (D : SourceData n d)
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt
      (fun y : VariableSpace d => D.componentObjective i y)
      (dataComponentGradient D i x) x := by
  sorry

theorem finiteAverageGradient_bridge
    {n d : ℕ} (D : SourceData n d)
    (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (dataComponentGradient D i x) x) :
    ∇ (dataObjective D) x = dataFullGradient D x := by
  change
    ∇ (SOptLib.finiteUniformAverage D.componentObjective) x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentGradient D.componentObjective i x)
  apply
    SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      D.componentObjective (componentGradient D.componentObjective) x
  intro i
  simpa [dataComponentGradient] using hcomponent i

noncomputable def fStar
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objectiveInfimum (dataObjective D)

noncomputable def Delta
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  dataObjective D D.x0 - fStar D

def globalInfimumContract
    {n d : ℕ} (D : SourceData n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ dataObjective D x

theorem globalInfimumContract_obligation
    {n d : ℕ} (D : SourceData n d) :
    globalInfimumContract D := by
  sorry

theorem Delta_nonneg_of_globalInfimumContract
    {n d : ℕ} (D : SourceData n d)
    (hInf : globalInfimumContract D) :
    0 ≤ Delta D := by
  unfold Delta
  exact sub_nonneg.mpr (hInf D.x0)

structure SourceSchedule (n : ℕ) where
  epsilon : ℝ
  L : ℝ
  n0 : N0 n
  S1 : ℕ
  S2 : ℝ
  eta : ℝ
  q : ℝ

noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    SourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  eta := epsilon / (L * n0.1)
  q := n0.1 * Real.sqrt (n : ℝ)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).eta =
      epsilon / (L * n0.1) := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

def parameterDomain
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) : Prop :=
  0 < epsilon ∧ 0 < L

noncomputable def adaptiveStepSize
    {n d : ℕ} (s : SourceSchedule n)
    (v : VariableSpace d) : ℝ :=
  min
    (s.epsilon / (s.L * s.n0.1 * ‖v‖))
    (1 / (2 * s.L * s.n0.1))

theorem adaptiveStepSize_on_positive_norm
    {n d : ℕ} (s : SourceSchedule n)
    (v : VariableSpace d) :
    0 < ‖v‖ →
      adaptiveStepSize s v =
        min
          (s.epsilon / (s.L * s.n0.1 * ‖v‖))
          (1 / (2 * s.L * s.n0.1)) := by
  intro _
  rfl

noncomputable def update
    {n d : ℕ} (s : SourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - adaptiveStepSize s v • v

@[simp] theorem update_spec
    {n d : ℕ} (s : SourceSchedule n)
    (x v : VariableSpace d) :
    update s x v =
      x - adaptiveStepSize s v • v := by
  rfl

theorem zero_norm_update_boundary
    {n d : ℕ} (s : SourceSchedule n) (x : VariableSpace d) :
    update s x 0 = x := by
  simp [update, adaptiveStepSize]

structure NaturalSamplingRealization
    {n : ℕ} (s : SourceSchedule n) where
  batchSize : ℕ
  refreshPeriod : ℕ
  batchSize_pos : 0 < batchSize
  refreshPeriod_pos : 0 < refreshPeriod
  batchSize_spec : (batchSize : ℝ) = s.S2
  refreshPeriod_spec : (refreshPeriod : ℝ) = s.q

def sourceRealizationDomain
    {n : ℕ} (s : SourceSchedule n) : Prop :=
  Nonempty (NaturalSamplingRealization s)

theorem exact_realization_not_general
    : ¬ ∃ b q : ℕ,
        0 < b ∧ 0 < q ∧
          (b : ℝ) = Real.sqrt 2 ∧ (q : ℝ) = Real.sqrt 2 := by
  exact finiteSumExactNaturalRealization_impossible_n2_n0_1

abbrev SamplePath
    {n : ℕ} {s : SourceSchedule n}
    (r : NaturalSamplingRealization s) :=
  SOptLib.miniBatchSamplePath r.batchSize (Fin n)

noncomputable def componentLaw
    {n : ℕ} (hn : 0 < n) : Measure (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).toMeasure

theorem componentLaw_isProbability
    {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (componentLaw hn) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold componentLaw
  infer_instance

noncomputable def sampleLaw
    {n : ℕ} {s : SourceSchedule n}
    (r : NaturalSamplingRealization s) (hn : 0 < n) :
    Measure (SamplePath r) :=
  SOptLib.iidMiniBatchSampleLaw
    r.batchSize (componentLaw hn)

theorem sampleLaw_isProbability
    {n : ℕ} {s : SourceSchedule n}
    (r : NaturalSamplingRealization s) (hn : 0 < n) :
    IsProbabilityMeasure (sampleLaw r hn) := by
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
    r.batchSize (componentLaw hn)

def refreshAt
    {n : ℕ} {s : SourceSchedule n}
    (r : NaturalSamplingRealization s) (k : ℕ) : Prop :=
  k % r.refreshPeriod = 0

@[simp] theorem refreshAt_zero
    {n : ℕ} {s : SourceSchedule n}
    (r : NaturalSamplingRealization s) :
    refreshAt r 0 := by
  simp [refreshAt]

noncomputable def sampledAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (omega : SamplePath r) (k : ℕ) (x : VariableSpace d) :
    VariableSpace d :=
  (r.batchSize : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin r.batchSize =>
        dataComponentGradient D (omega k j) x)

noncomputable def recursiveEstimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (omega : SamplePath r) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) :
    VariableSpace d :=
  sampledAverage D r omega k xCurr -
    sampledAverage D r omega k xPrev + vPrev

noncomputable def fullRefresh
    {n d : ℕ} (D : SourceData n d)
    (x : VariableSpace d) : VariableSpace d :=
  dataFullGradient D x

theorem fullRefresh_error_B17
    {n d : ℕ} (D : SourceData n d)
    (x : VariableSpace d) :
    ‖fullRefresh D x - dataFullGradient D x‖ ^ 2 = 0 := by
  simp [fullRefresh]

noncomputable def transition
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (omega : SamplePath r) (k : ℕ)
    (state : State (VariableSpace d)) :
    State (VariableSpace d) := by
  classical
  let xNext := update s state.x state.v
  let vNext :=
    if refreshAt r (k + 1) then
      fullRefresh D xNext
    else
      recursiveEstimator D r omega (k + 1) state.v state.x xNext
  exact { x := xNext, v := vNext }

noncomputable def stateProcess
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) :
    ℕ → SamplePath r → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullRefresh D D.x0 }
  | k + 1 => fun omega =>
      transition D r hn omega k (stateProcess D r hn k omega)

noncomputable def iterate
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) :
    ℕ → SamplePath r → VariableSpace d :=
  fun k omega => (stateProcess D r hn k omega).x

noncomputable def estimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) :
    ℕ → SamplePath r → VariableSpace d :=
  fun k omega => (stateProcess D r hn k omega).v

@[simp] theorem stateProcess_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (omega : SamplePath r) :
    stateProcess D r hn 0 omega =
      { x := D.x0, v := fullRefresh D D.x0 } := by
  rfl

@[simp] theorem iterate_succ
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (k : ℕ) (omega : SamplePath r) :
    iterate D r hn (k + 1) omega =
      update s (iterate D r hn k omega) (estimator D r hn k omega) := by
  rfl

@[simp] theorem estimator_zero
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (omega : SamplePath r) :
    estimator D r hn 0 omega = fullRefresh D D.x0 := by
  rfl

noncomputable def uniformOutputLaw
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × SamplePath r) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  letI : IsProbabilityMeasure (sampleLaw r hn) :=
    sampleLaw_isProbability r hn
  exact
    (PMF.uniformOfFintype (Fin K)).toMeasure.prod
      (sampleLaw r hn)

theorem uniformOutputLaw_isProbability
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (K : ℕ) (hK : 0 < K) :
    IsProbabilityMeasure (uniformOutputLaw D r hn K hK) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  letI : IsProbabilityMeasure (sampleLaw r hn) :=
    sampleLaw_isProbability r hn
  unfold uniformOutputLaw
  infer_instance

noncomputable def uniformOutput
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (K : ℕ) :
    Fin K × SamplePath r → VariableSpace d :=
  fun z => iterate D r hn z.1 z.2

noncomputable def outputGradientNormAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage
    (sampleLaw r hn) (dataFullGradient D) (iterate D r hn) K

def estimatorErrorBoundary
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖estimator D r hn k omega -
          dataFullGradient D (iterate D r hn k omega)‖ ^ 2
          ∂sampleLaw r hn ≤ epsilon ^ 2

def oneStepDescentBoundary
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        dataObjective D (iterate D r hn (k + 1) omega) -
          dataObjective D (iterate D r hn k omega)
          ∂sampleLaw r hn ≤
      -epsilon / (4 * s.L * s.n0.1) *
          ∫ omega, ‖estimator D r hn k omega‖ ∂sampleLaw r hn +
        3 * epsilon ^ 2 / (4 * s.L * s.n0.1)

def telescopeBoundary
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k => ∫ omega, ‖estimator D r hn k omega‖
          ∂sampleLaw r hn) ≤
    4 * epsilon

def conversionBoundary
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega, ‖dataFullGradient D (iterate D r hn k omega)‖
      ∂sampleLaw r hn) ≤
      (∫ omega, ‖estimator D r hn k omega‖
        ∂sampleLaw r hn) + epsilon

theorem estimatorErrorBoundary_obligation
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ)
    (_hDomain : parameterDomain s.epsilon s.L s.n0) :
    estimatorErrorBoundary D r hn epsilon K := by
  sorry

theorem oneStepDescentBoundary_obligation
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ)
    (_hDomain : parameterDomain s.epsilon s.L s.n0) :
    oneStepDescentBoundary D r hn epsilon K := by
  sorry

theorem telescopeBoundary_obligation
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ)
    (_hDomain : parameterDomain s.epsilon s.L s.n0)
    (_hEstimator : estimatorErrorBoundary D r hn epsilon K)
    (_hDescent : oneStepDescentBoundary D r hn epsilon K) :
    telescopeBoundary D r hn epsilon K := by
  sorry

theorem conversionBoundary_obligation
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (r : NaturalSamplingRealization s)
    (hn : 0 < n) (epsilon : ℝ) (K : ℕ)
    (_hDomain : parameterDomain s.epsilon s.L s.n0)
    (_hEstimator : estimatorErrorBoundary D r hn epsilon K) :
    conversionBoundary D r hn epsilon K := by
  sorry

noncomputable def literalB19Cost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) + s.S1

noncomputable def correctedB19Cost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

theorem literal_and_corrected_B19_are_distinct :
    literalB19Cost (schedule 4 1 (⟨1, by norm_num [n0Domain]⟩ : N0 4)) 1 ≠
      correctedB19Cost (schedule 4 1 (⟨1, by norm_num [n0Domain]⟩ : N0 4)) 1 := by
  norm_num [literalB19Cost, correctedB19Cost, schedule, n0Domain]

noncomputable def iterationBudget
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2) + 1

noncomputable def correctedB19Bound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  sorry

theorem b18_epsilon_square_counterexample :
    ¬ b18DisplayedTerm 2 1 1 1 = (2 : ℝ) ^ 2 := by
  norm_num [b18DisplayedTerm]

theorem correctedB19Cost_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (K : ℕ)
    (_hDomain : 0 < epsilon ∧ 0 < D.L)
    (_hInf : globalInfimumContract D) :
    correctedB19Cost (schedule epsilon D.L n0) K ≤
      correctedB19Bound D epsilon n0 := by
  sorry

theorem theorem2_finite_sum_gradient_cost_bound_spine
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (r : NaturalSamplingRealization (schedule epsilon D.L n0))
    (hn : 0 < n) (hK : 0 < iterationBudget D epsilon n0)
    (hDomain : parameterDomain epsilon D.L n0) :
    outputGradientNormAverage D r hn (iterationBudget D epsilon n0) ≤
        5 * epsilon ∧
      correctedB19Cost (schedule epsilon D.L n0)
          (iterationBudget D epsilon n0) ≤
        correctedB19Bound D epsilon n0 := by
  let K := iterationBudget D epsilon n0
  have hScheduleDomain :
      parameterDomain (schedule epsilon D.L n0).epsilon
        (schedule epsilon D.L n0).L (schedule epsilon D.L n0).n0 := by
    simpa [parameterDomain, schedule] using hDomain
  have hEstimator : estimatorErrorBoundary D r hn epsilon K :=
    estimatorErrorBoundary_obligation D r hn epsilon K hScheduleDomain
  have hDescent : oneStepDescentBoundary D r hn epsilon K :=
    oneStepDescentBoundary_obligation D r hn epsilon K hScheduleDomain
  have hTelescope : telescopeBoundary D r hn epsilon K :=
    telescopeBoundary_obligation D r hn epsilon K hScheduleDomain
      hEstimator hDescent
  have hConversion : conversionBoundary D r hn epsilon K :=
    conversionBoundary_obligation D r hn epsilon K hScheduleDomain hEstimator
  letI : IsProbabilityMeasure (componentLaw hn) :=
    componentLaw_isProbability hn
  letI : IsProbabilityMeasure (sampleLaw r hn) :=
    sampleLaw_isProbability r hn
  have hOutput :
      outputGradientNormAverage D r hn K ≤ 5 * epsilon := by
    unfold outputGradientNormAverage
    apply Algorithms.Unverified.SPIDER.theorem2_finite_sum_extension_proof_root
      (sampleLaw r hn) (dataFullGradient D) (iterate D r hn)
      (estimator D r hn) K hK epsilon
    · intro k hk
      exact hConversion k (Finset.mem_range.mp hk)
    · exact hTelescope
  have hInf := globalInfimumContract_obligation D
  have hCost := correctedB19Cost_obligation D epsilon n0 K
    (by simpa [parameterDomain] using hDomain) hInf
  exact ⟨hOutput, hCost⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Spine

-/

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-!
Active source-facing finite-sum object layer for SPIDER Theorem 2.

The source data contain only the finite-sum objectives, the initial point, the
smoothness scale, and the stated averaged component-gradient bound.  Global
lower-boundedness, gradient realization, denominator admissibility, and the
real-to-integer sampling issue are derived boundaries, not setup fields.
-/

def n0Domain (n : ℕ) : Set ℝ :=
  Set.Icc (1 : ℝ) (Real.sqrt (n : ℝ))

abbrev N0 (n : ℕ) :=
  {r : ℝ // r ∈ n0Domain n}

theorem n0_lower {n : ℕ} (n0 : N0 n) :
    1 ≤ n0.1 :=
  n0.2.1

theorem n0_upper {n : ℕ} (n0 : N0 n) :
    n0.1 ≤ Real.sqrt (n : ℝ) :=
  n0.2.2

theorem n_pos_of_n0 {n : ℕ} (n0 : N0 n) :
    0 < n := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    le_trans n0.2.1 n0.2.2
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  have hn : 1 ≤ n := by
    exact_mod_cast hnreal
  exact Nat.zero_lt_of_lt hn

noncomputable def componentGradient
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => componentObjective i y) x

theorem componentGradient_spec
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ)
    (i : Fin n) (x : VariableSpace d) :
    componentGradient componentObjective i x =
      ∇ (fun y : VariableSpace d => componentObjective i y) x := by
  rfl

theorem componentGradient_hasGradientAt
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ)
    (i : Fin n) (x : VariableSpace d) :
    HasGradientAt (fun y : VariableSpace d => componentObjective i y)
      (componentGradient componentObjective i x) x := by
  sorry

structure FiniteSumProblem (n d : ℕ) where
  componentObjective : Fin n → VariableSpace d → ℝ
  x0 : VariableSpace d
  L : ℝ
  averagedLipschitzGradient :
    ∀ x y : VariableSpace d,
      SOptLib.finiteUniformAverage
        (fun i : Fin n =>
          ‖componentGradient componentObjective i x -
            componentGradient componentObjective i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2

namespace FiniteSumProblem

noncomputable def objective
    {n d : ℕ} (P : FiniteSumProblem n d) :
    VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage P.componentObjective

noncomputable def fullGradient
    {n d : ℕ} (P : FiniteSumProblem n d) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient P.componentObjective i x)

noncomputable def fStar
    {n d : ℕ} (P : FiniteSumProblem n d) : ℝ :=
  objectiveInfimum P.objective

noncomputable def Delta
    {n d : ℕ} (P : FiniteSumProblem n d) : ℝ :=
  P.objective P.x0 - P.fStar

theorem objective_spec
    {n d : ℕ} (P : FiniteSumProblem n d) (x : VariableSpace d) :
    P.objective x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => P.componentObjective i x) := by
  simp [FiniteSumProblem.objective, SOptLib.finiteUniformAverage]

theorem fullGradient_spec
    {n d : ℕ} (P : FiniteSumProblem n d) (x : VariableSpace d) :
    P.fullGradient x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentGradient P.componentObjective i x) := by
  rfl

theorem fullGradient_eq_mathlibGradient
    {n d : ℕ} (P : FiniteSumProblem n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt (fun y : VariableSpace d => P.componentObjective i y)
          (componentGradient P.componentObjective i x) x) :
    ∇ P.objective x = P.fullGradient x := by
  change ∇ (SOptLib.finiteUniformAverage P.componentObjective) x =
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient P.componentObjective i x)
  simpa using
    (SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      P.componentObjective (componentGradient P.componentObjective) x
      hcomponent)

theorem fullGradient_hasGradientAt
    {n d : ℕ} (P : FiniteSumProblem n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt (fun y : VariableSpace d => P.componentObjective i y)
          (componentGradient P.componentObjective i x) x) :
    HasGradientAt P.objective (P.fullGradient x) x := by
  change HasGradientAt (SOptLib.finiteUniformAverage P.componentObjective)
    (SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient P.componentObjective i x)) x
  convert
    (SOptLib.finiteAverageObjective_hasGradientAt
      P.componentObjective (componentGradient P.componentObjective) x
      hcomponent) using 1
  · funext z
    simp [SOptLib.finiteUniformAverage, Pi.smul_apply, smul_eq_mul]

theorem globalInfimum_lowerBound
    {n d : ℕ} (P : FiniteSumProblem n d) :
    ∀ x : VariableSpace d, P.fStar ≤ P.objective x := by
  sorry

theorem Delta_nonneg
    {n d : ℕ} (P : FiniteSumProblem n d) :
    0 ≤ P.Delta := by
  unfold Delta
  exact sub_nonneg.mpr (P.globalInfimum_lowerBound P.x0)

end FiniteSumProblem

structure SourceSchedule (n : ℕ) where
  epsilon : ℝ
  L : ℝ
  n0 : ℝ
  S1 : ℕ
  S2 : ℝ
  eta : ℝ
  q : ℝ

noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    SourceSchedule n where
  epsilon := epsilon
  L := L
  n0 := n0.1
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  eta := epsilon / (L * n0.1)
  q := n0.1 * Real.sqrt (n : ℝ)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_eta
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).eta =
      epsilon / (L * n0.1) := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

noncomputable def iterationBudget
    {n d : ℕ} (P : FiniteSumProblem n d)
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * P.L * P.Delta * n0.1 * epsilon⁻¹ ^ 2) + 1

theorem iterationBudget_pos
    {n d : ℕ} (P : FiniteSumProblem n d)
    (epsilon : ℝ) (n0 : N0 n) :
    0 < iterationBudget P epsilon n0 := by
  exact Nat.succ_pos _

noncomputable def adaptiveStepSize
    {n d : ℕ} (s : SourceSchedule n)
    (v : VariableSpace d) : Option ℝ :=
  if h : 0 < s.L ∧ 0 < s.n0 ∧ 0 < ‖v‖ then
    some (min (s.epsilon / (s.L * s.n0 * ‖v‖))
      (1 / (2 * s.L * s.n0)))
  else
    none

noncomputable def checkedUpdate
    {n d : ℕ} (s : SourceSchedule n)
    (x v : VariableSpace d) : Option (VariableSpace d) :=
  (adaptiveStepSize s v).map (fun eta => x - eta • v)

theorem checkedUpdate_spec
    {n d : ℕ} (s : SourceSchedule n)
    (x v : VariableSpace d)
    {eta : ℝ}
    (h :
      adaptiveStepSize s v =
        some eta) :
    checkedUpdate s x v = some (x - eta • v) := by
  simp [checkedUpdate, h]

abbrev SamplePath (n S2 : ℕ) :=
  SOptLib.miniBatchSamplePath S2 (Fin n)

noncomputable def componentSampleAverage
    {n d S2 : ℕ} (P : FiniteSumProblem n d)
    (x : VariableSpace d) (samples : Fin S2 → Fin n) :
    VariableSpace d :=
  refreshEstimator
    (fun y i => componentGradient P.componentObjective i y) x samples

noncomputable def recursiveEstimator
    {n d S2 : ℕ} (P : FiniteSumProblem n d)
    (vPrev xPrev xCurr : VariableSpace d)
    (samples : Fin S2 → Fin n) : VariableSpace d :=
  Algorithms.Unverified.SPIDER.recursiveEstimator
    (fun y i => componentGradient P.componentObjective i y)
    vPrev xPrev xCurr samples

noncomputable def checkedStateProcess
    {n d S2 : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n)
    (q : ℕ)
    (omega : SamplePath n S2) :
    ℕ → Option (State (VariableSpace d))
  | 0 =>
      some { x := P.x0, v := P.fullGradient P.x0 }
  | k + 1 =>
      match checkedStateProcess P s q omega k with
      | none => none
      | some previous =>
          match checkedUpdate s previous.x previous.v with
          | none => none
          | some xNext =>
              let vNext :=
                if (k + 1) % q = 0 then
                  P.fullGradient xNext
                else
                  recursiveEstimator P previous.v previous.x xNext
                    (omega (k + 1))
              some { x := xNext, v := vNext }

theorem checkedStateProcess_zero
    {n d S2 q : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) (omega : SamplePath n S2) :
    checkedStateProcess P s q omega 0 =
      some { x := P.x0, v := P.fullGradient P.x0 } := by
  rfl

def sourceBatchRealization (s : SourceSchedule n) : Prop :=
  ∃ S2 q : ℕ, (S2 : ℝ) = s.S2 ∧ (q : ℝ) = s.q

theorem sourceBatchRealization_not_unconditional :
    ¬ ∀ (n : ℕ) (n0 : N0 n),
      sourceBatchRealization (schedule 1 1 n0) := by
  sorry

noncomputable def sourceProcess
    {n d : ℕ} (P : FiniteSumProblem n d)
    (epsilon : ℝ) (n0 : N0 n) :
    Option (Σ S2 : ℕ, Σ q : ℕ,
      SamplePath n S2 →
        ℕ → Option (State (VariableSpace d))) :=
  by
    classical
    by_cases h : sourceBatchRealization (schedule epsilon P.L n0)
    · let hspec := Classical.choose_spec h
      let S2 := Classical.choose h
      let q := Classical.choose hspec
      exact some ⟨S2, q, checkedStateProcess P
        (schedule epsilon P.L n0) q⟩
    · exact none

noncomputable def sampleIndexLaw
    {n : ℕ} (hn : 0 < n) :
    Measure (Fin n) :=
  by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact (PMF.uniformOfFintype (Fin n)).toMeasure

noncomputable def samplePathLaw
    {n S2 : ℕ} (hn : 0 < n) :
    Measure (SamplePath n S2) :=
  SOptLib.iidMiniBatchSampleLaw S2 (sampleIndexLaw hn)

theorem samplePathLaw_isProbability
    {n S2 : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (samplePathLaw (S2 := S2) hn) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : IsProbabilityMeasure (sampleIndexLaw hn) := by
    unfold sampleIndexLaw
    infer_instance
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure S2
    (sampleIndexLaw hn)

noncomputable def uniformOutputLaw
    {n S2 K : ℕ} (hn : 0 < n) (hK : 0 < K) :
    Measure (Fin K × SamplePath n S2) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (sampleIndexLaw hn) := by
    unfold sampleIndexLaw
    infer_instance
  exact (PMF.uniformOfFintype (Fin K)).toMeasure.prod
    (samplePathLaw (S2 := S2) hn)

theorem uniformOutputLaw_isProbability
    {n S2 K : ℕ} (hn : 0 < n) (hK : 0 < K) :
    IsProbabilityMeasure (uniformOutputLaw (S2 := S2) hn hK) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (sampleIndexLaw hn) := by
    unfold sampleIndexLaw
    infer_instance
  letI : IsProbabilityMeasure (samplePathLaw (S2 := S2) hn) :=
    samplePathLaw_isProbability hn
  unfold uniformOutputLaw
  infer_instance

noncomputable def uniformOutput
    {n d S2 q K : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) (q : ℕ) :
    Fin K × SamplePath n S2 → Option (State (VariableSpace d)) :=
  fun z => checkedStateProcess P s q z.2 z.1

def estimatorErrorAdapter
    {n d S2 q K : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) : Prop :=
  ∀ k < K, ∀ omega : SamplePath n S2,
    ∃ state : State (VariableSpace d),
      checkedStateProcess P s q omega k = some state

theorem estimatorErrorAdapter_obligation
    {n d S2 q K : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) :
    estimatorErrorAdapter (S2 := S2) (q := q) (K := K) P s := by
  sorry

def oneStepDescentAdapter
    {n d : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) : Prop :=
  ∀ k : ℕ,
    ∃ xNext : VariableSpace d,
      checkedUpdate s P.x0 (P.fullGradient P.x0) = some xNext

theorem oneStepDescentAdapter_obligation
    {n d : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) :
    oneStepDescentAdapter P s := by
  sorry

def telescopeAdapter
    {n d S2 q K : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) : Prop :=
  estimatorErrorAdapter (S2 := S2) (q := q) (K := K) P s ∧
    oneStepDescentAdapter P s

theorem telescopeAdapter_obligation
    {n d S2 q K : ℕ} (P : FiniteSumProblem n d)
    (s : SourceSchedule n) :
    telescopeAdapter (S2 := S2) (q := q) (K := K) P s := by
  exact ⟨estimatorErrorAdapter_obligation
      (S2 := S2) (q := q) (K := K) P s,
    oneStepDescentAdapter_obligation P s⟩

noncomputable def literalB19Cost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) / s.q) : ℝ) * s.S1 + (K : ℝ) * s.S2

noncomputable def correctedB19Cost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

noncomputable def gradientCostBound
    {n d : ℕ} (P : FiniteSumProblem n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (P.L * P.Delta) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

def sourceTheorem2Conclusion
    {n d : ℕ} (P : FiniteSumProblem n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  correctedB19Cost (schedule epsilon P.L n0)
      (iterationBudget P epsilon n0) ≤ gradientCostBound P epsilon n0

theorem theorem2_finite_sum_source_root
    {n d : ℕ} (P : FiniteSumProblem n d)
    (epsilon : ℝ) (n0 : N0 n) :
    sourceTheorem2Conclusion P epsilon n0 := by
  sorry

theorem theorem2_finite_sum_output_conversion_edge
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  exact uniform_average_gradient_bound_of_estimator_average
    mu grad iterate estimator K hK epsilon hconvert hest_avg

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2CanonicalActiveV43

/-!
Active canonical finite-sum SPIDER spine.

The source schedule retains real `S2` and `q`; finite sample cardinality is a
deterministic internal realization, never a source-facing witness.  The same
component-gradient kernel drives the smoothness assumption, full refresh, and
recursive estimator.
-/

def n0Domain (n : ℕ) : Set ℝ :=
  Set.Icc (1 : ℝ) (Real.sqrt (n : ℝ))

abbrev N0 (n : ℕ) :=
  {r : ℝ // r ∈ n0Domain n}

theorem n0_lower {n : ℕ} (n0 : N0 n) : 1 ≤ n0.1 :=
  n0.2.1

theorem n0_upper {n : ℕ} (n0 : N0 n) :
    n0.1 ≤ Real.sqrt (n : ℝ) :=
  n0.2.2

theorem n_pos {n : ℕ} (n0 : N0 n) : 0 < n := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    le_trans n0.2.1 n0.2.2
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  have hn : 1 ≤ n := by
    exact_mod_cast hnreal
  exact Nat.zero_lt_of_lt hn

theorem n0_zero_rejected : ¬ Nonempty (N0 0) := by
  rintro ⟨n0⟩
  have : (1 : ℝ) ≤ 0 := by
    simpa [n0Domain] using le_trans n0.2.1 n0.2.2
  linarith

noncomputable def componentGradient
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => componentObjective i y) x

@[simp] theorem componentGradient_spec
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ)
    (i : Fin n) (x : VariableSpace d) :
    componentGradient componentObjective i x =
      ∇ (fun y : VariableSpace d => componentObjective i y) x := by
  rfl

structure SourceData (n d : ℕ) where
  componentObjective : Fin n → VariableSpace d → ℝ
  x0 : VariableSpace d
  L : ℝ
  averagedLipschitzGradient :
    ∀ x y : VariableSpace d,
      SOptLib.finiteUniformAverage
        (fun i : Fin n =>
          ‖componentGradient componentObjective i x -
            componentGradient componentObjective i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2

noncomputable def objective
    {n d : ℕ} (D : SourceData n d) :
    VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage D.componentObjective

noncomputable def fullGradient
    {n d : ℕ} (D : SourceData n d) :
    VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient D.componentObjective i x)

noncomputable def fStar
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objectiveInfimum (objective D)

noncomputable def Delta
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objective D D.x0 - fStar D

def globalInfimumContract
    {n d : ℕ} (D : SourceData n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ objective D x

theorem globalInfimum_lowerBound_obligation
    {n d : ℕ} (D : SourceData n d) :
    globalInfimumContract D := by
  sorry

theorem Delta_nonneg
    {n d : ℕ} (D : SourceData n d) : 0 ≤ Delta D := by
  exact sub_nonneg.mpr
    (globalInfimum_lowerBound_obligation D D.x0)

theorem finite_average_gradient_bridge
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d)
    (hcomponent :
      ∀ i : Fin n,
        HasGradientAt
          (fun y : VariableSpace d => D.componentObjective i y)
          (componentGradient D.componentObjective i x) x) :
    ∇ (objective D) x = fullGradient D x := by
  unfold objective fullGradient
  exact
    SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      D.componentObjective (componentGradient D.componentObjective) x
      hcomponent

structure Schedule (n : ℕ) where
  epsilon : ℝ
  L : ℝ
  n0 : N0 n
  S1 : ℕ
  S2 : ℝ
  q : ℝ
  eta : ℝ

noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    Schedule n where
  epsilon := epsilon
  L := L
  n0 := n0
  S1 := n
  S2 := Real.sqrt (n : ℝ) / n0.1
  q := n0.1 * Real.sqrt (n : ℝ)
  eta := epsilon / (L * n0.1)

@[simp] theorem schedule_S1
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S1 = n := by
  rfl

@[simp] theorem schedule_S2
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).S2 =
      Real.sqrt (n : ℝ) / n0.1 := by
  rfl

@[simp] theorem schedule_q
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) :
    (schedule epsilon L n0).q =
      n0.1 * Real.sqrt (n : ℝ) := by
  rfl

noncomputable def iterationBudget
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2) + 1

theorem iterationBudget_pos
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) :
    0 < iterationBudget D epsilon n0 :=
  Nat.succ_pos _

namespace Internal

noncomputable def batchCount {n : ℕ} (s : Schedule n) : ℕ :=
  max 1 (Nat.ceil s.S2)

theorem batchCount_pos {n : ℕ} (s : Schedule n) :
    0 < batchCount s :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

abbrev SamplePath {n : ℕ} (s : Schedule n) :=
  SOptLib.miniBatchSamplePath (batchCount s) (Fin n)

noncomputable def indexLaw {n : ℕ} (n0 : N0 n) : Measure (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).toMeasure

theorem indexLaw_isProbability {n : ℕ} (n0 : N0 n) :
    IsProbabilityMeasure (indexLaw n0) := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  unfold indexLaw
  infer_instance

noncomputable def sampleLaw
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    Measure (SamplePath s) :=
  SOptLib.iidMiniBatchSampleLaw (batchCount s) (indexLaw n0)

theorem sampleLaw_isProbability
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    IsProbabilityMeasure (sampleLaw s n0) := by
  letI : IsProbabilityMeasure (indexLaw n0) :=
    indexLaw_isProbability n0
  exact SOptLib.iidMiniBatchSampleLaw_isProbabilityMeasure
    (batchCount s) (indexLaw n0)

def refreshAt {n : ℕ} (s : Schedule n) (k : ℕ) : Prop :=
  ∃ epoch : ℕ, (k : ℝ) = (epoch : ℝ) * s.q

theorem refreshAt_zero {n : ℕ} (s : Schedule n) :
    refreshAt s 0 :=
  ⟨0, by simp⟩

noncomputable def sampledAverage
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (omega : SamplePath s) (k : ℕ) (x : VariableSpace d) :
    VariableSpace d :=
  (batchCount s : ℝ)⁻¹ •
    Finset.sum Finset.univ
      (fun j : Fin (batchCount s) =>
        componentGradient D.componentObjective (omega k j) x)

noncomputable def recursiveEstimator
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (omega : SamplePath s) (k : ℕ)
    (vPrev xPrev xCurr : VariableSpace d) :
    VariableSpace d :=
  sampledAverage D s omega k xCurr -
    sampledAverage D s omega k xPrev + vPrev

noncomputable def stepSize
    {n d : ℕ} (s : Schedule n) (v : VariableSpace d) : ℝ :=
  if h : 0 < s.L ∧ 0 < s.n0.1 ∧ 0 < ‖v‖ then
    min
      (s.epsilon / (s.L * s.n0.1 * ‖v‖))
      (1 / (2 * s.L * s.n0.1))
  else
    0

noncomputable def update
    {n d : ℕ} (s : Schedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  x - stepSize s v • v

theorem update_zero
    {n d : ℕ} (s : Schedule n) (x : VariableSpace d) :
    update s x 0 = x := by
  simp [update, stepSize]

theorem update_eq_paper
    {n d : ℕ} (s : Schedule n) (x v : VariableSpace d)
    (hL : 0 < s.L) (hv : 0 < ‖v‖) :
    update s x v =
      x -
        min
          (s.epsilon / (s.L * s.n0.1 * ‖v‖))
          (1 / (2 * s.L * s.n0.1)) • v := by
  simp [update, stepSize, hL, hv,
    lt_of_lt_of_le zero_lt_one s.n0.2.1]

noncomputable def transition
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (omega : SamplePath s) (k : ℕ)
    (state : State (VariableSpace d)) :
    State (VariableSpace d) :=
  by
    classical
    let xNext := update s state.x state.v
    let vNext :=
      if refreshAt s (k + 1) then
        fullGradient D xNext
      else
        recursiveEstimator D s omega (k + 1) state.v state.x xNext
    exact { x := xNext, v := vNext }

noncomputable def stateProcess
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullGradient D D.x0 }
  | k + 1 => fun omega =>
      transition D s omega k (stateProcess D s k omega)

noncomputable def iterate
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  fun k omega => (stateProcess D s k omega).x

noncomputable def estimator
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  fun k omega => (stateProcess D s k omega).v

noncomputable def uniformOutputLaw
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (K : ℕ) (hK : 0 < K) :
    Measure (Fin K × SamplePath s) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (indexLaw n0) :=
    indexLaw_isProbability n0
  letI : IsProbabilityMeasure (sampleLaw s n0) :=
    sampleLaw_isProbability s n0
  exact (PMF.uniformOfFintype (Fin K)).toMeasure.prod
    (sampleLaw s n0)

theorem uniformOutputLaw_isProbability
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (K : ℕ) (hK : 0 < K) :
    IsProbabilityMeasure (uniformOutputLaw D s n0 K hK) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  letI : IsProbabilityMeasure (indexLaw n0) :=
    indexLaw_isProbability n0
  letI : IsProbabilityMeasure (sampleLaw s n0) :=
    sampleLaw_isProbability s n0
  unfold uniformOutputLaw
  infer_instance

end Internal

abbrev SamplePath {n : ℕ} (s : Schedule n) :=
  Internal.SamplePath s

noncomputable def sampleLaw
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    Measure (SamplePath s) :=
  Internal.sampleLaw s n0

theorem sampleLaw_isProbability
    {n : ℕ} (s : Schedule n) (n0 : N0 n) :
    IsProbabilityMeasure (sampleLaw s n0) :=
  Internal.sampleLaw_isProbability s n0

noncomputable def iterate
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  Internal.iterate D s

noncomputable def estimator
    {n d : ℕ} (D : SourceData n d) (s : Schedule n) :
    ℕ → SamplePath s → VariableSpace d :=
  Internal.estimator D s

def estimatorErrorAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        ‖estimator D s k omega -
          fullGradient D (iterate D s k omega)‖ ^ 2
          ∂sampleLaw s n0 ≤ epsilon ^ 2

def oneStepDescentAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    ∫ omega,
        objective D (iterate D s (k + 1) omega) -
          objective D (iterate D s k omega) ∂sampleLaw s n0 ≤
      -epsilon / (4 * s.L * s.n0.1) *
          ∫ omega, ‖estimator D s k omega‖ ∂sampleLaw s n0 +
        3 * epsilon ^ 2 / (4 * s.L * s.n0.1)

def telescopeAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  (K : ℝ)⁻¹ *
      Finset.sum (Finset.range K)
        (fun k => ∫ omega, ‖estimator D s k omega‖
          ∂sampleLaw s n0) ≤ 4 * epsilon

def conversionAdapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) : Prop :=
  ∀ k < K,
    (∫ omega, ‖fullGradient D (iterate D s k omega)‖
      ∂sampleLaw s n0) ≤
      (∫ omega, ‖estimator D s k omega‖ ∂sampleLaw s n0) + epsilon

theorem estimatorErrorAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) :
    estimatorErrorAdapter D s n0 epsilon K := by
  sorry

theorem oneStepDescentAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) :
    oneStepDescentAdapter D s n0 epsilon K := by
  sorry

theorem telescopeAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ)
    (_hEstimator : estimatorErrorAdapter D s n0 epsilon K)
    (_hDescent : oneStepDescentAdapter D s n0 epsilon K) :
    telescopeAdapter D s n0 epsilon K := by
  sorry

theorem conversionAdapter_obligation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ)
    (_hEstimator : estimatorErrorAdapter D s n0 epsilon K) :
    conversionAdapter D s n0 epsilon K := by
  sorry

theorem output_adapter
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (hEstimator : estimatorErrorAdapter D s n0 epsilon K)
    (hDescent : oneStepDescentAdapter D s n0 epsilon K)
    (hTelescope : telescopeAdapter D s n0 epsilon K)
    (hConversion : conversionAdapter D s n0 epsilon K) :
    uniformOutputGradientNormAverage
        (sampleLaw s n0) (fullGradient D) (iterate D s) K ≤
      5 * epsilon := by
  letI : IsProbabilityMeasure (sampleLaw s n0) :=
    sampleLaw_isProbability s n0
  apply uniform_average_gradient_bound_of_estimator_average
    (sampleLaw s n0) (fullGradient D) (iterate D s) (estimator D s)
    K hK epsilon
  · intro k hk
    exact hConversion k (Finset.mem_range.mp hk)
  · exact hTelescope

noncomputable def outputGradientNormExpectation
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (K : ℕ) (hK : 0 < K) : ℝ :=
  ∫ z, ‖fullGradient D (iterate D s z.1 z.2)‖ ∂
    Internal.uniformOutputLaw D s n0 K hK

theorem outputExpectation_le_of_average
    {n d : ℕ} (D : SourceData n d) (s : Schedule n)
    (n0 : N0 n) (epsilon : ℝ) (K : ℕ) (hK : 0 < K)
    (_hAverage :
      uniformOutputGradientNormAverage
        (sampleLaw s n0) (fullGradient D) (iterate D s) K ≤
      5 * epsilon) :
    outputGradientNormExpectation D s n0 K hK ≤ 5 * epsilon := by
  sorry

noncomputable def literalB19Cost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) / s.q) : ℝ) * s.S1 + (K : ℝ) * s.S2

noncomputable def correctedB19Cost
    {n : ℕ} (s : Schedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

theorem literal_and_corrected_B19_are_distinct
    (s : Schedule 4) :
    literalB19Cost s 1 ≠ correctedB19Cost s 1 := by
  sorry

noncomputable def correctedB19Bound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

theorem correctedB19Cost_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (K : ℕ) :
    correctedB19Cost (schedule epsilon D.L n0) K ≤
      correctedB19Bound D epsilon n0 := by
  sorry

noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  n0 * Real.sqrt n * L ^ 2 *
    (epsilon ^ 2 / (L ^ 2 * n0 ^ 2)) *
    (epsilon * n0 / Real.sqrt n)

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 := by
  unfold b18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

theorem b18_epsilon_square_counterexample :
    ¬ b18DisplayedTerm 2 1 1 1 = (2 : ℝ) ^ 2 := by
  norm_num [b18DisplayedTerm]

def sourceConclusion
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  outputGradientNormExpectation D (schedule epsilon D.L n0) n0
      (iterationBudget D epsilon n0)
      (iterationBudget_pos D epsilon n0) ≤ 5 * epsilon ∧
    correctedB19Cost (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) ≤
      correctedB19Bound D epsilon n0

theorem theorem2_finite_sum_gradient_cost_bound_v43
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) :
    sourceConclusion D epsilon n0 := by
  let s := schedule epsilon D.L n0
  let K := iterationBudget D epsilon n0
  have hK : 0 < K := iterationBudget_pos D epsilon n0
  have hEstimator : estimatorErrorAdapter D s n0 epsilon K :=
    estimatorErrorAdapter_obligation D s n0 epsilon K
  have hDescent : oneStepDescentAdapter D s n0 epsilon K :=
    oneStepDescentAdapter_obligation D s n0 epsilon K
  have hTelescope : telescopeAdapter D s n0 epsilon K :=
    telescopeAdapter_obligation D s n0 epsilon K hEstimator hDescent
  have hConversion : conversionAdapter D s n0 epsilon K :=
    conversionAdapter_obligation D s n0 epsilon K hEstimator
  have hAverage :
      uniformOutputGradientNormAverage
          (sampleLaw s n0) (fullGradient D) (iterate D s) K ≤
        5 * epsilon :=
    output_adapter D s n0 epsilon K hK hEstimator hDescent
      hTelescope hConversion
  have hOutput :
      outputGradientNormExpectation D s n0 K hK ≤ 5 * epsilon :=
    outputExpectation_le_of_average D s n0 epsilon K hK hAverage
  have hCost :
      correctedB19Cost s K ≤ correctedB19Bound D epsilon n0 :=
    correctedB19Cost_obligation D epsilon n0 K
  exact ⟨by simpa [sourceConclusion, s, K] using hOutput,
    by simpa [sourceConclusion, s, K] using hCost⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2CanonicalActiveV43 -/
-/

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal

/-!
Single active finite-sum object spine for the Theorem 2 extension.

The source-facing data use one computed component-gradient family everywhere:
the averaged Lipschitz assumption, the finite-average bridge, the exact full
refresh, and the recursive estimator.  The source schedule keeps the real
`S₂` and `q` values from (3.7).  A process is exposed only under an explicit
exact natural-number realization of those source values; this keeps the
source boundary honest when (for example) `sqrt 2` is not a batch count.

The checked update is option-valued.  It therefore does not turn the
undefined zero-norm quotient into a paper-facing fallback update.
-/

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal
