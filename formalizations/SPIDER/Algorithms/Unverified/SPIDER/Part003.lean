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
import Algorithms.Unverified.SPIDER.Part002

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

end Algorithms.Unverified.SPIDER
namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal

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

theorem n0_zero_rejected :
    ¬ Nonempty (N0 0) := by
  rintro ⟨n0⟩
  have hupper : n0.1 ≤ (0 : ℝ) := by
    simpa [n0Domain] using n0.2.2
  have hbad : (1 : ℝ) ≤ 0 := le_trans n0.2.1 hupper
  linarith

noncomputable def componentGradient
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => componentObjective i y) x

@[simp] theorem componentGradient_spec
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ)
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

@[simp] theorem objective_spec
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d) :
    objective D x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => D.componentObjective i x) := by
  simp [objective, SOptLib.finiteUniformAverage, Pi.smul_apply]

@[simp] theorem fullGradient_spec
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d) :
    fullGradient D x =
      SOptLib.finiteUniformAverage
        (fun i : Fin n => componentGradient D.componentObjective i x) := by
  rfl

theorem finiteAverageGradient_bridge
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

theorem finiteAverage_hasGradientAt_bridge
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

noncomputable def fStar
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objectiveInfimum (objective D)

noncomputable def Delta
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objective D D.x0 - fStar D

def globalInfimumContract
    {n d : ℕ} (D : SourceData n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ objective D x

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

theorem sqrt_two_not_nat (m : ℕ) :
    (m : ℝ) ≠ Real.sqrt 2 := by
  intro hm
  have hsq : (m : ℝ) ^ 2 = 2 := by
    rw [hm]
    norm_num
  have hmleReal : (m : ℝ) ≤ 2 := by
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by
      positivity
    nlinarith [hmnonneg,
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have hmle : m ≤ 2 := by
    exact_mod_cast hmleReal
  interval_cases m <;> norm_num at hsq

noncomputable def literalB19Cost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) / s.q) : ℝ) * s.S1 + (K : ℝ) * s.S2

noncomputable def correctedB19Cost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

theorem literal_and_corrected_B19_are_distinct :
    literalB19Cost (schedule 4 1 (⟨1, by norm_num [n0Domain]⟩ : N0 4)) 1 ≠
      correctedB19Cost (schedule 4 1 (⟨1, by norm_num [n0Domain]⟩ : N0 4)) 1 := by
  have hceil : Nat.ceil ((1 : ℝ) / 2) = 1 := by
    apply
      (Nat.ceil_eq_iff (R := ℝ) (a := (1 : ℝ) / 2) (n := 1)
        (by norm_num)).2
    norm_num
  simp only [literalB19Cost, correctedB19Cost, schedule]
  norm_num [n0Domain, hceil]

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
  unfold b18DisplayedTerm
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  field_simp [ne_of_gt hepsilon, ne_of_gt hL, ne_of_gt hn0,
    ne_of_gt hsqrt_pos]

theorem b18_epsilon_square_counterexample :
    ¬ b18DisplayedTerm 2 1 1 1 = (2 : ℝ) ^ 2 := by
  norm_num [b18DisplayedTerm]

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-!
Active source boundary for finite-sum Theorem 2.

This layer keeps the printed real-valued schedule as the public object and
models the algorithmic spine as a relation.  In particular, no exact-natural
realization of `S₂` or `q`, no arbitrary batch-index type, and no zero-norm
fallback update is exported as the source process.

The theorem root below is deliberately not a completed proof of the paper
theorem: it states the actual corrected B.19 gradient-cost claim and leaves the
source-boundary proof obligation visible.  The surrounding theorems record the
recurring blockers from the source text: the real batch/period sizes, the
undefined zero-estimator denominator in Option II, and the B.18 epsilon-power
mismatch.
-/

abbrev N0 (n : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.N0 n

/- The paper's component gradient is the canonical Mathlib gradient selector;
   SourceData keeps only the source-level differentiability certificate. -/
noncomputable def componentGradient
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  fun i x => ∇ (fun y : VariableSpace d => componentObjective i y) x

@[simp] theorem componentGradient_spec
    {n d : ℕ}
    (componentObjective : Fin n → VariableSpace d → ℝ)
    (i : Fin n) (x : VariableSpace d) :
    componentGradient componentObjective i x =
      ∇ (fun y : VariableSpace d => componentObjective i y) x := by
  rfl

structure SourceData (n d : ℕ) where
  componentObjective : Fin n → VariableSpace d → ℝ
  x0 : VariableSpace d
  L : ℝ
  componentGradient_realizes :
    ∀ i : Fin n, ∀ x : VariableSpace d,
      HasGradientAt
        (fun y : VariableSpace d => componentObjective i y)
        (componentGradient componentObjective i x) x
  averagedLipschitzGradient :
    ∀ x y : VariableSpace d,
      SOptLib.finiteUniformAverage
        (fun i : Fin n =>
          ‖componentGradient componentObjective i x -
            componentGradient componentObjective i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2

abbrev SourceSchedule (n : ℕ) :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.SourceSchedule n

noncomputable abbrev totalizedComponentGradient
    {n d : ℕ} (componentObjective : Fin n → VariableSpace d → ℝ) :
    Fin n → VariableSpace d → VariableSpace d :=
  componentGradient componentObjective

noncomputable abbrev objective
    {n d : ℕ} (D : SourceData n d) : VariableSpace d → ℝ :=
  SOptLib.finiteUniformAverage D.componentObjective

noncomputable abbrev fullGradient
    {n d : ℕ} (D : SourceData n d) : VariableSpace d → VariableSpace d :=
  fun x =>
    SOptLib.finiteUniformAverage
      (fun i : Fin n => componentGradient D.componentObjective i x)

noncomputable abbrev fStar
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objectiveInfimum (objective D)

noncomputable abbrev Delta
    {n d : ℕ} (D : SourceData n d) : ℝ :=
  objective D D.x0 - fStar D

def globalInfimumContract
    {n d : ℕ} (D : SourceData n d) : Prop :=
  ∀ x : VariableSpace d, fStar D ≤ objective D x

/-- Source boundary for Assumption 1(i): `f*` is the global infimum value
and `Delta = f(x0)-f*` is the finite initial gap.  Since Lean's `ℝ` values
are finite, the nontrivial object-layer content is the global-infimum
contract for the named `fStar`. -/
def finiteInitialGapBoundary
    {n d : ℕ} (D : SourceData n d) : Prop :=
  globalInfimumContract D

theorem Delta_nonneg_of_globalInfimumContract
    {n d : ℕ} (D : SourceData n d)
    (hInf : globalInfimumContract D) :
    0 ≤ Delta D := by
  unfold Delta
  exact sub_nonneg.mpr (hInf D.x0)

theorem Delta_nonneg_of_finiteInitialGapBoundary
    {n d : ℕ} (D : SourceData n d)
    (hGap : finiteInitialGapBoundary D) :
    0 ≤ Delta D :=
  Delta_nonneg_of_globalInfimumContract D hGap

def scalarDomain
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (_n0 : N0 n) : Prop :=
  0 < epsilon ∧ 0 < D.L

noncomputable def schedule
    {n : ℕ} (epsilon L : ℝ) (n0 : N0 n) : SourceSchedule n :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.schedule
    epsilon L n0

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

theorem n_pos {n : ℕ} (n0 : N0 n) : 0 < n :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n_pos n0

theorem n0_pos {n : ℕ} (n0 : N0 n) : 0 < n0.1 := by
  linarith [n0.2.1]

theorem sqrt_n_pos {n : ℕ} (n0 : N0 n) :
    0 < Real.sqrt (n : ℝ) := by
  exact Real.sqrt_pos.2 (Nat.cast_pos.2 (n_pos n0))

theorem schedule_q_pos
    {n : ℕ} {epsilon L : ℝ} (n0 : N0 n)
    (hScalar : 0 < epsilon ∧ 0 < L) :
    0 < (schedule epsilon L n0).q := by
  simp [schedule, Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.schedule]
  exact mul_pos (n0_pos n0) (sqrt_n_pos n0)

theorem schedule_S2_pos
    {n : ℕ} {epsilon L : ℝ} (n0 : N0 n)
    (_hScalar : 0 < epsilon ∧ 0 < L) :
    0 < (schedule epsilon L n0).S2 := by
  simp [schedule, Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.schedule]
  exact div_pos (sqrt_n_pos n0) (n0_pos n0)

theorem schedule_denominators_ne_zero
    {n : ℕ} {epsilon L : ℝ} (n0 : N0 n)
    (hScalar : 0 < epsilon ∧ 0 < L) :
    (schedule epsilon L n0).q ≠ 0 ∧
      (schedule epsilon L n0).S2 ≠ 0 ∧
      L * n0.1 ≠ 0 := by
  refine ⟨ne_of_gt (schedule_q_pos n0 hScalar),
    ne_of_gt (schedule_S2_pos n0 hScalar), ?_⟩
  exact mul_ne_zero (ne_of_gt hScalar.2) (ne_of_gt (n0_pos n0))

theorem fullGradient_eq_total_gradient_of_component_realization
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d) :
    fullGradient D x = ∇ (objective D) x := by
  unfold fullGradient objective
  exact
    Eq.symm
      (SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
        D.componentObjective (componentGradient D.componentObjective) x
        (fun i => D.componentGradient_realizes i x))

theorem objective_hasGradientAt_fullGradient
    {n d : ℕ} (D : SourceData n d) (x : VariableSpace d) :
    HasGradientAt (objective D) (fullGradient D x) x := by
  unfold objective fullGradient
  convert
    (SOptLib.finiteAverageObjective_hasGradientAt
      D.componentObjective (componentGradient D.componentObjective) x
      (fun i => D.componentGradient_realizes i x)) using 1
  funext z
  simp [SOptLib.finiteUniformAverage, Pi.smul_apply, smul_eq_mul]

/-- Concrete recursive mini-batch count used to realize the paper's
with-replacement sampling law.  The paper prints the real parameter `S₂`;
Lean's path space needs a natural coordinate set, so exact equality with the
real parameter remains a separate corrected/source-boundary obligation. -/
noncomputable def sourceBatchCount {n : ℕ} (s : SourceSchedule n) : ℕ :=
  max 1 (Nat.ceil s.S2)

theorem sourceBatchCount_pos {n : ℕ} (s : SourceSchedule n) :
    0 < sourceBatchCount s := by
  unfold sourceBatchCount
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

abbrev SourceBatch {n : ℕ} (s : SourceSchedule n) :=
  Fin (sourceBatchCount s) → Fin n

abbrev SourcePath {n : ℕ} (s : SourceSchedule n) :=
  SOptLib.miniBatchSamplePath (sourceBatchCount s) (Fin n)

theorem sourceBatchCount_exact_realization_not_unconditional :
    ¬ ∀ (n : ℕ) (n0 : N0 n),
      ∃ b : ℕ, (b : ℝ) = (schedule 1 1 n0).S2 := by
  intro h
  let n0 : N0 2 :=
    ⟨1, by
      constructor <;> norm_num [Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0Domain]⟩
  rcases h 2 n0 with ⟨b, hb⟩
  have hsqrt : (b : ℝ) = Real.sqrt 2 := by
    simpa [schedule, n0] using hb
  exact
    Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.sqrt_two_not_nat
      b hsqrt

def realPeriodicRefresh {n : ℕ} (s : SourceSchedule n) (k : ℕ) : Prop :=
  ∃ m : ℕ, (k : ℝ) = (m : ℝ) * s.q

theorem realPeriodicRefresh_zero {n : ℕ} (s : SourceSchedule n) :
    realPeriodicRefresh s 0 := by
  exact ⟨0, by simp [realPeriodicRefresh]⟩

def paperStepSizeRel
    {n d : ℕ} (s : SourceSchedule n)
    (v : VariableSpace d) (eta : ℝ) : Prop :=
  0 < ‖v‖ ∧
    eta =
      min
        (s.epsilon / (s.L * s.n0.1 * ‖v‖))
        (1 / (2 * s.L * s.n0.1))

def paperUpdateRel
    {n d : ℕ} (s : SourceSchedule n)
    (x v xNext : VariableSpace d) : Prop :=
  ∃ eta : ℝ, paperStepSizeRel s v eta ∧ xNext = x - eta • v

theorem paperUpdateRel_rejects_zero_norm
    {n d : ℕ} (s : SourceSchedule n) (x xNext : VariableSpace d) :
    ¬ paperUpdateRel s x 0 xNext := by
  rintro ⟨eta, heta, _⟩
  simpa using heta.1

noncomputable def batchAverage
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (b : SourceBatch s)
    (x : VariableSpace d) : VariableSpace d :=
  ((sourceBatchCount s : ℝ)⁻¹) •
    Finset.sum Finset.univ
      (fun j : Fin (sourceBatchCount s) =>
        componentGradient D.componentObjective (b j) x)

noncomputable def recursiveEstimator
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (b : SourceBatch s)
    (vPrev xPrev xCurr : VariableSpace d) : VariableSpace d :=
  batchAverage D b xCurr - batchAverage D b xPrev + vPrev

def transition
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (path : SourcePath s) (k : ℕ)
    (state next : State (VariableSpace d)) : Prop := by
  classical
  exact
    paperUpdateRel s state.x state.v next.x ∧
      next.v =
        if realPeriodicRefresh s (k + 1) then
          fullGradient D next.x
        else
          recursiveEstimator D (path (k + 1)) state.v state.x next.x

def sourceProcess
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (path : SourcePath s)
    (state : ℕ → State (VariableSpace d)) : Prop :=
  state 0 = { x := D.x0, v := fullGradient D D.x0 } ∧
    ∀ k : ℕ, transition D path k (state k) (state (k + 1))

theorem sourceProcess_initial
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} {path : SourcePath s}
    {state : ℕ → State (VariableSpace d)}
    (h : sourceProcess D path state) :
    state 0 = { x := D.x0, v := fullGradient D D.x0 } :=
  h.1

theorem sourceProcess_step
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} {path : SourcePath s}
    {state : ℕ → State (VariableSpace d)}
    (h : sourceProcess D path state) (k : ℕ) :
    transition D path k (state k) (state (k + 1)) :=
  h.2 k

noncomputable def sourceIndexLaw
    {n : ℕ} (n0 : N0 n) : Measure (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  exact (PMF.uniformOfFintype (Fin n)).toMeasure

theorem sourceIndexLaw_isProbability
    {n : ℕ} (n0 : N0 n) :
    IsProbabilityMeasure (sourceIndexLaw n0) := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  unfold sourceIndexLaw
  infer_instance

private theorem sourceIndexLaw_integral_eq_finiteUniformAverage
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (n0 : N0 n) (g : Fin n → F) :
    (∫ i, g i ∂sourceIndexLaw n0) =
      SOptLib.finiteUniformAverage g := by
  classical
  unfold sourceIndexLaw SOptLib.finiteUniformAverage
  rw [MeasureTheory.integral_fintype .of_finite]
  simp [PMF.toMeasure_apply_singleton,
    PMF.uniformOfFintype_apply, measureReal_def, Finset.smul_sum]

private theorem sourceIndexLaw_singleton_real
    {n : ℕ} (n0 : N0 n) (i : Fin n) :
    (sourceIndexLaw n0).real ({i} : Set (Fin n)) =
      (Fintype.card (Fin n) : ℝ)⁻¹ := by
  letI : Nonempty (Fin n) := ⟨⟨0, n_pos n0⟩⟩
  unfold sourceIndexLaw
  simp [measureReal_def, PMF.uniformOfFintype_apply]

/-- Canonical Algorithm 1 recursive mini-batch law: every recursive branch
draws finite-sum component indices with replacement. -/
noncomputable def withReplacementSourceLaw
    {n : ℕ} (s : SourceSchedule n) : Measure (SourcePath s) :=
  SOptLib.iidMiniBatchSampleLaw (sourceBatchCount s) (sourceIndexLaw s.n0)

def WithReplacementSourceLawBoundary {n : ℕ} (s : SourceSchedule n) : Prop :=
  SOptLib.miniBatchIidLawSpec
    (sourceBatchCount s) (sourceIndexLaw s.n0) (withReplacementSourceLaw s)

theorem withReplacementSourceLaw_spec
    {n : ℕ} (s : SourceSchedule n) :
    WithReplacementSourceLawBoundary s := by
  letI : IsProbabilityMeasure (sourceIndexLaw s.n0) :=
    sourceIndexLaw_isProbability s.n0
  unfold WithReplacementSourceLawBoundary withReplacementSourceLaw
  exact SOptLib.iidMiniBatchSampleLaw_spec
    (sourceBatchCount s) (sourceIndexLaw s.n0)

theorem withReplacementSourceLaw_isProbability
    {n : ℕ} (s : SourceSchedule n) :
    IsProbabilityMeasure (withReplacementSourceLaw s) :=
  (withReplacementSourceLaw_spec s).1

def normalizedUniformOutputBoundary
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : Prop :=
  0 < K ∧ ∃ μ : Measure (Fin K), IsProbabilityMeasure μ

theorem normalizedUniformOutputBoundary_holds
    {n : ℕ} (s : SourceSchedule n) {K : ℕ} (hK : 0 < K) :
    normalizedUniformOutputBoundary s K := by
  classical
  refine ⟨hK, ?_⟩
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact ⟨(PMF.uniformOfFintype (Fin K)).toMeasure, by infer_instance⟩

noncomputable def iterationBudget
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℕ :=
  Nat.floor (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2) + 1

noncomputable def correctedCostBound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    8 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    2 * n0.1⁻¹ * Real.sqrt (n : ℝ)

/-- The literal first B.19 cost route printed before the source's corrected
closed form.  It is retained only as a boundary object; the active cost claim
uses the corrected `2 K S₂ + S₁` route below. -/
noncomputable def literalGradientCost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) / s.q) : ℝ) * s.S1 + (K : ℝ) * s.S2

/-- The source-corrected B.19 route which yields the theorem's displayed
closed-form finite-sum gradient-cost bound. -/
noncomputable def correctedGradientCost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2 + s.S1

noncomputable def fullRefreshCallCount
    {n : ℕ} (s : SourceSchedule n) (_K : ℕ) : ℝ :=
  s.S1

noncomputable def recursiveGradientCallCount
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  2 * (K : ℝ) * s.S2

/-- Corrected B.19 call-count object: one full finite-sum refresh plus the
source-corrected recursive-gradient count `2 K S₂`. -/
noncomputable def correctedB19CallCount
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  recursiveGradientCallCount s K + fullRefreshCallCount s K

theorem correctedGradientCost_eq_correctedB19CallCount
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) :
    correctedGradientCost s K = correctedB19CallCount s K := by
  unfold correctedGradientCost correctedB19CallCount
    recursiveGradientCallCount fullRefreshCallCount
  ring

def correctedB19CostClaim
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  scalarDomain D epsilon n0 ∧
    finiteInitialGapBoundary D ∧
    correctedB19CallCount (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) ≤
      correctedCostBound D epsilon n0

/-- Corrected B.19 cost statement at the paper budget, derived from the
call-count object rather than an existential cost wrapper.

This is a source-boundary obligation for the corrected cost route.  It is not
advertised as a completed proof of literal Theorem 2, because the source still
has independent real-batch, zero-denominator, and B.18 epsilon-power gaps. -/
theorem correctedB19CallCount_le_bound_at_budget
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    correctedB19CallCount (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) ≤
      correctedCostBound D epsilon n0 := by
  rcases hScalar with ⟨hepsilon, hL⟩
  have hDelta : 0 ≤ Delta D :=
    Delta_nonneg_of_finiteInitialGapBoundary D hGap
  have hn0pos : 0 < n0.1 := n0_pos n0
  have hA_nonneg : 0 ≤ 4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 := by
    positivity
  have hK : (iterationBudget D epsilon n0 : ℝ) ≤
      4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1 := by
    unfold iterationBudget
    rw [Nat.cast_add]
    simpa [add_comm] using (add_le_add_right (Nat.floor_le hA_nonneg) (1 : ℝ))
  have hfactor : 0 ≤ 2 * (Real.sqrt (n : ℝ) / n0.1) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hK hfactor
  have hscaled' :
      2 * (iterationBudget D epsilon n0 : ℝ) *
          (Real.sqrt (n : ℝ) / n0.1) ≤
        2 * (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1) *
          (Real.sqrt (n : ℝ) / n0.1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  calc
    correctedB19CallCount (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) =
        2 * (iterationBudget D epsilon n0 : ℝ) *
            (Real.sqrt (n : ℝ) / n0.1) + (n : ℝ) := by
      simp only [correctedB19CallCount, recursiveGradientCallCount,
        fullRefreshCallCount, schedule_S1, schedule_S2]
    _ ≤ 2 * (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1) *
          (Real.sqrt (n : ℝ) / n0.1) + (n : ℝ) := by
      simpa [add_comm] using (add_le_add_right hscaled' (n : ℝ))
    _ = correctedCostBound D epsilon n0 := by
      unfold correctedCostBound
      field_simp [ne_of_gt hn0pos]
      ring

theorem correctedB19CostClaim_of_call_count
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    correctedB19CostClaim D epsilon n0 := by
  exact ⟨hScalar, hGap,
    correctedB19CallCount_le_bound_at_budget D epsilon n0 hScalar hGap⟩

/-- A source-path-indexed Algorithm 1 run: for every concrete sample path,
the state sequence satisfies the finite-sum SPIDER transition relation. -/
def sourceRunProcessBoundary
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n}
    (state : ℕ → SourcePath s → State (VariableSpace d)) : Prop :=
  ∀ path : SourcePath s, sourceProcess D path (fun k => state k path)

noncomputable def sourceIterate
    {n d : ℕ} {s : SourceSchedule n}
    (state : ℕ → SourcePath s → State (VariableSpace d)) :
    ℕ → SourcePath s → VariableSpace d :=
  fun k path => (state k path).x

noncomputable def sourceEstimator
    {n d : ℕ} {s : SourceSchedule n}
    (state : ℕ → SourcePath s → State (VariableSpace d)) :
    ℕ → SourcePath s → VariableSpace d :=
  fun k path => (state k path).v

theorem sourceRunProcessBoundary_initial
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n}
    {state : ℕ → SourcePath s → State (VariableSpace d)}
    (hProcess : sourceRunProcessBoundary D state)
    (path : SourcePath s) :
    state 0 path = { x := D.x0, v := fullGradient D D.x0 } :=
  sourceProcess_initial D (hProcess path)

theorem sourceRunProcessBoundary_step
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n}
    {state : ℕ → SourcePath s → State (VariableSpace d)}
    (hProcess : sourceRunProcessBoundary D state)
    (path : SourcePath s) (k : ℕ) :
    transition D path k (state k path) (state (k + 1) path) :=
  sourceProcess_step D (hProcess path) k

def estimatorErrorAdapterEdge
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  ∀ {s : SourceSchedule n}
    (state : ℕ → SourcePath s → State (VariableSpace d)),
    s = schedule epsilon D.L n0 →
    sourceRunProcessBoundary D state →
    (∀ path k0,
        realPeriodicRefresh s k0 →
          sourceEstimator state k0 path =
            fullGradient D (sourceIterate state k0 path)) ∧
    Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.b18DisplayedTerm
      epsilon D.L n0.1 (n : ℝ) = epsilon ^ 3

def oneStepDescentAdapterEdge
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  ∀ {s : SourceSchedule n}
    (state : ℕ → SourcePath s → State (VariableSpace d)),
    s = schedule epsilon D.L n0 →
    sourceRunProcessBoundary D state →
    ∀ path k,
      objective D (sourceIterate state (k + 1) path) ≤
        objective D (sourceIterate state k path) -
          epsilon * ‖sourceEstimator state k path‖ / (4 * D.L * n0.1) +
          epsilon ^ 2 / (2 * n0.1 * D.L) +
          (1 / (4 * D.L * n0.1)) *
            ‖sourceEstimator state k path -
              fullGradient D (sourceIterate state k path)‖ ^ 2

def outputConversionAdapterEdge : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ),
    (∀ k ∈ Finset.range K,
        (∫ omega, ‖grad (iterate k omega)‖ ∂mu) ≤
          (∫ omega, ‖estimator k omega‖ ∂mu) + epsilon) →
    ((K : ℝ)⁻¹ *
        Finset.sum (Finset.range K)
          (fun k => ∫ omega, ‖estimator k omega‖ ∂mu) ≤
      4 * epsilon) →
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon

theorem outputConversionAdapterEdge_from_inherited :
    outputConversionAdapterEdge := by
  intro Ω E _ _ mu _ grad iterate estimator K hK epsilon hconvert hest_avg
  exact uniform_average_gradient_bound_of_estimator_average
    mu grad iterate estimator K hK epsilon hconvert hest_avg

def selectedOutputConversionAdapterEdge : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E)
    (iterate : ℕ → Ω → E) (K : ℕ) (hK : 0 < K) (C : ℝ),
    (∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
      Integrable (fun ω => ‖grad (iterate R.1 ω)‖) mu) →
    uniformOutputGradientNormAverage mu grad iterate K ≤ C →
    selectedOutputGradientNormExpectation mu grad iterate K hK ≤ C

theorem selectedOutputConversionAdapterEdge_from_inherited :
    selectedOutputConversionAdapterEdge := by
  intro Ω E _ _ mu _ grad iterate K hK C hint havg
  exact selectedOutputGradientNormExpectation_le_of_uniform_average_le
    mu grad iterate K hK C hint havg

noncomputable def sourceUniformOutputGradientNormAverage
    {n d : ℕ} {s : SourceSchedule n} [MeasurableSpace (SourcePath s)]
    (mu : Measure (SourcePath s)) (D : SourceData n d)
    (state : ℕ → SourcePath s → State (VariableSpace d)) (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage mu (fullGradient D) (sourceIterate state) K

noncomputable def sourceSelectedOutputGradientNormExpectation
    {n d : ℕ} {s : SourceSchedule n} [MeasurableSpace (SourcePath s)]
    (mu : Measure (SourcePath s)) (D : SourceData n d)
    (state : ℕ → SourcePath s → State (VariableSpace d))
    (K : ℕ) (hK : 0 < K) : ℝ :=
  selectedOutputGradientNormExpectation mu (fullGradient D)
    (sourceIterate state) K hK

def sourceOutputConversionAdapterEdge
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  ∀ {s : SourceSchedule n} [MeasurableSpace (SourcePath s)]
    (mu : Measure (SourcePath s)) [SFinite mu]
    (state : ℕ → SourcePath s → State (VariableSpace d)),
    s = schedule epsilon D.L n0 →
    sourceRunProcessBoundary D state →
    ∀ K : ℕ, 0 < K →
    (∀ k ∈ Finset.range K,
        (∫ path, ‖fullGradient D (sourceIterate state k path)‖ ∂mu) ≤
          (∫ path, ‖sourceEstimator state k path‖ ∂mu) + epsilon) →
    ((K : ℝ)⁻¹ *
        Finset.sum (Finset.range K)
          (fun k => ∫ path, ‖sourceEstimator state k path‖ ∂mu) ≤
      4 * epsilon) →
    sourceUniformOutputGradientNormAverage mu D state K ≤ 5 * epsilon

theorem sourceOutputConversionAdapterEdge_from_inherited
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) :
    sourceOutputConversionAdapterEdge D epsilon n0 := by
  intro s _ mu _ state _hSchedule _hProcess K hK hconvert hest_avg
  exact uniform_average_gradient_bound_of_estimator_average
    mu (fullGradient D) (sourceIterate state) (sourceEstimator state)
    K hK epsilon hconvert hest_avg

def sourceSelectedOutputConversionAdapterEdge
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  ∀ {s : SourceSchedule n} [MeasurableSpace (SourcePath s)]
    (mu : Measure (SourcePath s)) [SFinite mu]
    (state : ℕ → SourcePath s → State (VariableSpace d)),
    s = schedule epsilon D.L n0 →
    sourceRunProcessBoundary D state →
    ∀ (K : ℕ) (hK : 0 < K) (C : ℝ),
    (∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
      Integrable
        (fun path => ‖fullGradient D (sourceIterate state R.1 path)‖) mu) →
    sourceUniformOutputGradientNormAverage mu D state K ≤ C →
    sourceSelectedOutputGradientNormExpectation mu D state K hK ≤ C

theorem sourceSelectedOutputConversionAdapterEdge_from_inherited
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) :
    sourceSelectedOutputConversionAdapterEdge D epsilon n0 := by
  intro s _ mu _ state _hSchedule _hProcess K hK C hint havg
  exact selectedOutputGradientNormExpectation_le_of_uniform_average_le
    mu (fullGradient D) (sourceIterate state) K hK C hint havg

noncomputable def b18DisplayedTerm
    (epsilon L n0 n : ℝ) : ℝ :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.b18DisplayedTerm
    epsilon L n0 n

theorem b18DisplayedTerm_eq_epsilon_cube
    {epsilon L n0 n : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 < L)
    (hn0 : 0 < n0) (hn : 0 < n) :
    b18DisplayedTerm epsilon L n0 n = epsilon ^ 3 :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.b18DisplayedTerm_eq_epsilon_cube
    hepsilon hL hn0 hn

theorem b18_epsilon_square_counterexample :
    ¬ b18DisplayedTerm 2 1 1 1 = (2 : ℝ) ^ 2 :=
  Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.b18_epsilon_square_counterexample

theorem literal_and_corrected_B19_are_distinct :
    literalGradientCost (schedule 4 1 (⟨1, by norm_num [Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0Domain]⟩ : N0 4)) 1 ≠
      correctedGradientCost (schedule 4 1 (⟨1, by norm_num [Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0Domain]⟩ : N0 4)) 1 := by
  exact
    Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.literal_and_corrected_B19_are_distinct

/-- Public non-completion record for the source-boundary gaps that prevent the
active root from being reported as a completed literal proof of Theorem 2. -/
def theorem2FiniteSumSourceBoundaryGaps : Prop :=
  (¬ ∀ (n : ℕ) (n0 : N0 n),
      ∃ b : ℕ, (b : ℝ) = (schedule 1 1 n0).S2) ∧
    (∀ {n d : ℕ} (s : SourceSchedule n)
      (x xNext : VariableSpace d), ¬ paperUpdateRel s x 0 xNext) ∧
    (¬ b18DisplayedTerm 2 1 1 1 = (2 : ℝ) ^ 2) ∧
    literalGradientCost (schedule 4 1 (⟨1, by norm_num [Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0Domain]⟩ : N0 4)) 1 ≠
      correctedGradientCost (schedule 4 1 (⟨1, by norm_num [Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0Domain]⟩ : N0 4)) 1

theorem theorem2_finite_sum_source_boundary_gaps :
    theorem2FiniteSumSourceBoundaryGaps := by
  refine ⟨sourceBatchCount_exact_realization_not_unconditional, ?_, ?_, ?_⟩
  · intro n d s x xNext
    exact paperUpdateRel_rejects_zero_norm s x xNext
  · exact b18_epsilon_square_counterexample
  · exact literal_and_corrected_B19_are_distinct

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-- Live corrected total convention for the zero-estimator branch of Option II.
For `0 < ‖v‖` it is exactly the paper update; for `v = 0` it stays put rather
than evaluating the paper's undefined quotient. -/
noncomputable def liveCorrectedOptionIIUpdate
    {n d : ℕ} (s : SourceSchedule n)
    (x v : VariableSpace d) : VariableSpace d :=
  if hv : 0 < ‖v‖ then
    x -
      min
        (s.epsilon / (s.L * s.n0.1 * ‖v‖))
        (1 / (2 * s.L * s.n0.1)) • v
  else
    x

theorem liveCorrectedOptionIIUpdate_zero
    {n d : ℕ} (s : SourceSchedule n)
    (x : VariableSpace d) :
    liveCorrectedOptionIIUpdate s x 0 = x := by
  simp [liveCorrectedOptionIIUpdate]

/-- Corrected natural refresh period for the executable finite-sum run.

The paper prints the real value `q = n₀ sqrt n`; the actual path recursion
needs a natural modulus.  This definition keeps the literal real schedule
available as source evidence while using a total, positive rounded period for
the corrected run. -/
noncomputable def roundedRefreshPeriod {n : ℕ} (s : SourceSchedule n) : ℕ :=
  max 1 (Nat.floor s.q)

theorem roundedRefreshPeriod_pos {n : ℕ} (s : SourceSchedule n) :
    0 < roundedRefreshPeriod s := by
  unfold roundedRefreshPeriod
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

def roundedRefreshAt {n : ℕ} (s : SourceSchedule n) (k : ℕ) : Prop :=
  k % roundedRefreshPeriod s = 0

theorem roundedRefreshAt_zero {n : ℕ} (s : SourceSchedule n) :
    roundedRefreshAt s 0 := by
  simp [roundedRefreshAt]

/-- Corrected total transition for the finite-sum run.

At zero estimator norm this uses `liveCorrectedOptionIIUpdate`, so the run stays
defined instead of requiring the paper's undefined quotient.  Refreshes use the
rounded natural period above; recursive branches use the canonical iid
with-replacement batch coordinates. -/
noncomputable def correctedTransition
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (path : SourcePath s) (k : ℕ)
    (state : State (VariableSpace d)) : State (VariableSpace d) := by
  classical
  let xNext := liveCorrectedOptionIIUpdate s state.x state.v
  let vNext :=
    if roundedRefreshAt s (k + 1) then
      fullGradient D xNext
    else
      recursiveEstimator D (path (k + 1)) state.v state.x xNext
  exact { x := xNext, v := vNext }

noncomputable def correctedStateProcess
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) :
    ℕ → SourcePath s → State (VariableSpace d)
  | 0 => fun _ => { x := D.x0, v := fullGradient D D.x0 }
  | k + 1 => fun path =>
      correctedTransition D path k (correctedStateProcess D s k path)

noncomputable def correctedIterate
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) :
    ℕ → SourcePath s → VariableSpace d :=
  fun k path => (correctedStateProcess D s k path).x

noncomputable def correctedEstimator
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) :
    ℕ → SourcePath s → VariableSpace d :=
  fun k path => (correctedStateProcess D s k path).v

@[simp] theorem correctedIterate_zero
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) (path : SourcePath s) :
    correctedIterate D s 0 path = D.x0 := by
  rfl

@[simp] theorem correctedEstimator_zero
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) (path : SourcePath s) :
    correctedEstimator D s 0 path = fullGradient D D.x0 := by
  rfl

theorem correctedTransition_zero_estimator_stays_put
    {n d : ℕ} (D : SourceData n d)
    {s : SourceSchedule n} (path : SourcePath s) (k : ℕ)
    (x : VariableSpace d) :
    (correctedTransition D path k { x := x, v := 0 }).x = x := by
  simp [correctedTransition, liveCorrectedOptionIIUpdate_zero]

noncomputable def correctedUniformOutputGradientAverage
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) (K : ℕ) : ℝ :=
  uniformOutputGradientNormAverage
    (withReplacementSourceLaw s)
    (fullGradient D) (correctedIterate D s) K

noncomputable def correctedSelectedOutputGradientNormExpectation
    {n d : ℕ} (D : SourceData n d)
    (s : SourceSchedule n) (K : ℕ) (hK : 0 < K) : ℝ :=
  selectedOutputGradientNormExpectation
    (withReplacementSourceLaw s)
    (fullGradient D) (correctedIterate D s) K hK

/-- Integrability is derived for the concrete finite-prefix run; it is not
an additional source hypothesis. -/
theorem correctedRunGradientNorm_integrable
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) (k : ℕ) :
    Integrable
      (fun path => ‖fullGradient D (correctedIterate D (schedule epsilon D.L n0) k path)‖)
      (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  let s := schedule epsilon D.L n0
  letI : IsProbabilityMeasure (withReplacementSourceLaw s) :=
    withReplacementSourceLaw_isProbability s
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  have h_transition_congr :
      ∀ m, m + 1 ≤ k → ∀ ⦃path path' : SourcePath s⦄,
        correctedStateProcess D s m path =
            correctedStateProcess D s m path' →
        xi (1 + m) path = xi (1 + m) path' →
        correctedStateProcess D s (m + 1) path =
            correctedStateProcess D s (m + 1) path' := by
    intro m hm path path' hstate hbatch
    have hbatch' : path (m + 1) = path' (m + 1) := by
      simpa [xi, Nat.add_comm] using hbatch
    simp only [correctedStateProcess]
    simp [correctedTransition, hstate, hbatch']
  have h_prefix_state_eq :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 k path =
            SOptLib.sampleWindow xi 1 k path' →
        correctedStateProcess D s k path =
            correctedStateProcess D s k path' := by
    intro path path' hprefix
    apply SOptLib.recursive_process_eq_of_driver_prefix_eq
      xi (correctedStateProcess D s) 1 k k
      { x := D.x0, v := fullGradient D D.x0 }
    · intro path''
      rfl
    · exact h_transition_congr
    · exact le_rfl
    · exact hprefix
  apply integrable_of_finiteSampleWindow_factor_aestrongly
    xi 1 k
  · intro j
    exact measurable_pi_apply j
  · intro path path' hwindow
    have hprefix :
        SOptLib.sampleWindow xi 1 k path =
            SOptLib.sampleWindow xi 1 k path' := by
      simpa [SOptLib.sampleWindow] using hwindow
    have hstate := h_prefix_state_eq hprefix
    exact congrArg
      (fun state : State (VariableSpace d) => ‖fullGradient D state.x‖)
      hstate

private theorem corrected_state_prefix_eq
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    (path path' : SourcePath (schedule epsilon D.L n0))
    (hprefix :
      SOptLib.sampleWindow
          (fun j path => path j) 1 k path =
        SOptLib.sampleWindow
          (fun j path => path j) 1 k path') :
    correctedStateProcess D (schedule epsilon D.L n0) k path =
      correctedStateProcess D (schedule epsilon D.L n0) k path' := by
  let s := schedule epsilon D.L n0
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  have h_transition_congr :
      ∀ m, m + 1 ≤ k → ∀ ⦃path path' : SourcePath s⦄,
        correctedStateProcess D s m path =
            correctedStateProcess D s m path' →
        xi (1 + m) path = xi (1 + m) path' →
        correctedStateProcess D s (m + 1) path =
            correctedStateProcess D s (m + 1) path' := by
    intro m hm path path' hstate hbatch
    have hbatch' : path (m + 1) = path' (m + 1) := by
      simpa [xi, Nat.add_comm] using hbatch
    simp only [correctedStateProcess]
    simp [correctedTransition, hstate, hbatch']
  apply SOptLib.recursive_process_eq_of_driver_prefix_eq
    xi (correctedStateProcess D s) 1 k k
    { x := D.x0, v := fullGradient D D.x0 }
  · intro path''
    rfl
  · exact h_transition_congr
  · exact le_rfl
  · exact hprefix

private theorem corrected_factor_measurable_under_window
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (Z : SourcePath (schedule epsilon D.L n0) → β)
    (hconst :
      ∀ ⦃path path' : SourcePath (schedule epsilon D.L n0)⦄,
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path =
          SOptLib.sampleWindow
            (fun j path => path j) 1 k path' →
        Z path = Z path') :
    @Measurable (SourcePath (schedule epsilon D.L n0)) β
      (MeasurableSpace.comap
        (SOptLib.sampleWindow
          (fun j path => path j) 1 k)
        (by infer_instance)) (by infer_instance) Z := by
  let window :
      SourcePath (schedule epsilon D.L n0) →
        Fin k → SourceBatch (schedule epsilon D.L n0) :=
    SOptLib.sampleWindow (fun j path => path j) 1 k
  let mWindow : MeasurableSpace
      (SourcePath (schedule epsilon D.L n0)) :=
    MeasurableSpace.comap window (by infer_instance)
  letI : MeasurableSpace
      (SourcePath (schedule epsilon D.L n0)) := mWindow
  have hwindow : Measurable window :=
    Measurable.of_comap_le le_rfl
  have hwindow_range : (Set.range window).Finite := by
    exact Set.Finite.subset Set.finite_univ (by
      intro z hz
      exact Set.mem_univ z)
  exact measurable_of_finite_range_fiber_const
    hwindow hwindow_range (by
      intro path path' hwindow'
      exact hconst hwindow')

private theorem corrected_prefix_key_current_indep
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (Z : SourcePath (schedule epsilon D.L n0) → β)
    (hconst :
      ∀ ⦃path path' : SourcePath (schedule epsilon D.L n0)⦄,
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path =
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path' →
        Z path = Z path')
    (current : Fin (sourceBatchCount (schedule epsilon D.L n0))) :
    ProbabilityTheory.IndepFun Z
        (fun path => path (k + 1) current)
        (withReplacementSourceLaw (schedule epsilon D.L n0)) ∧
      ∀ peer, peer ≠ current →
        ProbabilityTheory.IndepFun
          (fun path => (Z path, path (k + 1) peer))
          (fun path => path (k + 1) current)
          (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let coord : (ℕ × Fin (sourceBatchCount s)) →
      SourcePath s → Fin n :=
    fun kr path => path kr.1 kr.2
  let pastSet : Set (ℕ × Fin (sourceBatchCount s)) :=
    {kr | 1 ≤ kr.1 ∧ kr.1 < k + 1}
  have hcoord_meas : ∀ kr, Measurable (coord kr) := by
    intro kr
    exact (measurable_pi_apply kr.2).comp (measurable_pi_apply kr.1)
  have hiIndep : ProbabilityTheory.iIndepFun coord μ := by
    letI : IsProbabilityMeasure (sourceIndexLaw s.n0) :=
      sourceIndexLaw_isProbability s.n0
    simpa [coord, μ, withReplacementSourceLaw] using
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
        (sourceBatchCount s) (sourceIndexLaw s.n0))
  have hbatch_le_coords :
      ∀ j : ℕ,
        MeasurableSpace.comap
            (fun path : SourcePath s => path j) (by infer_instance) ≤
          ⨆ r : Fin (sourceBatchCount s),
            MeasurableSpace.comap (coord (j, r)) (by infer_instance) := by
    intro j
    let mCoords : MeasurableSpace (SourcePath s) :=
      ⨆ r : Fin (sourceBatchCount s),
        MeasurableSpace.comap (coord (j, r)) (by infer_instance)
    letI : MeasurableSpace (SourcePath s) := mCoords
    have hbatch : Measurable (fun path : SourcePath s => path j) := by
      refine measurable_pi_lambda _ ?_
      intro r
      exact Measurable.of_comap_le (le_iSup
        (fun r : Fin (sourceBatchCount s) =>
          MeasurableSpace.comap (coord (j, r)) (by infer_instance)) r)
    exact hbatch.comap_le
  have hstrict_le :
      MeasurableSpace.comap
          (SOptLib.sampleWindow
            (fun (j : ℕ) (path : SourcePath s) => path j) 1 k)
            (by infer_instance) ≤
        ⨆ kr ∈ pastSet,
          MeasurableSpace.comap (coord kr) (by infer_instance) := by
    have hwindow_eq :
        (⨆ (j : ℕ) (_hj : 1 ≤ j ∧ j < k + 1),
            MeasurableSpace.comap
              (fun (path : SourcePath s) => path j)
              (by infer_instance)) =
          MeasurableSpace.comap
            (SOptLib.sampleWindow
              (fun (j : ℕ) (path : SourcePath s) => path j) 1 k)
            (by infer_instance) := by
      simpa only [Nat.add_sub_cancel] using
        (SOptLib.sampleWindowMeasurableSpace_eq_comap
          (fun (j : ℕ) (path : SourcePath s) => path j) 1 (k + 1))
    rw [← hwindow_eq]
    refine iSup_le ?_
    intro j
    refine iSup_le ?_
    intro hj
    have hj' : 1 ≤ j ∧ j < k + 1 := hj
    calc
      MeasurableSpace.comap
          (fun path : SourcePath s => path j) (by infer_instance)
          ≤ ⨆ r : Fin (sourceBatchCount s),
              MeasurableSpace.comap (coord (j, r)) (by infer_instance) :=
        hbatch_le_coords j
      _ ≤ ⨆ kr ∈ pastSet,
          MeasurableSpace.comap (coord kr) (by infer_instance) := by
        refine iSup_le ?_
        intro r
        have hmem : (j, r) ∈ pastSet := by
          exact ⟨hj'.1, by omega⟩
        exact le_iSup_of_le (j, r) (le_iSup_of_le hmem le_rfl)
  have hindep :=
    indepFun_prefixKey_current_of_iIndepFun
      (sampleCoord := coord) (μ := μ)
      (current := (k + 1, current))
      hcoord_meas hiIndep
      (hprefixKey_meas :=
        corrected_factor_measurable_under_window
          D epsilon n0 k Z hconst)
      (hstrict_le := hstrict_le)
      (hpast_current_disj := by
        rw [Set.disjoint_singleton_right]
        intro hq
        simp [pastSet] at hq)
  refine ⟨hindep.1, ?_⟩
  intro peer hpeer
  apply hindep.2 (k + 1, peer)
  rw [Set.disjoint_singleton_right]
  intro hq
  rcases hq with hq | hq
  · simp [pastSet] at hq
  · have hqpeer : (k + 1, current) = (k + 1, peer) :=
      Set.mem_singleton_iff.mp hq
    have hpeer_eq : current = peer :=
      by simpa using congrArg Prod.snd hqpeer
    exact hpeer hpeer_eq.symm

private theorem corrected_prefix_sq_integrable
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    {V : Type*} [NormedAddCommGroup V]
    (Y : SourcePath (schedule epsilon D.L n0) → V)
    (hconst :
      ∀ ⦃path path' : SourcePath (schedule epsilon D.L n0)⦄,
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path =
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path' →
        Y path = Y path') :
    Integrable
      (fun path => ‖Y path‖ ^ 2)
      (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  letI : IsProbabilityMeasure μ :=
    withReplacementSourceLaw_isProbability s
  apply integrable_of_finiteSampleWindow_factor_aestrongly xi 1 k
  · intro j
    exact measurable_pi_apply j
  · intro path path' hwindow
    exact congrArg (fun v => ‖v‖ ^ 2) (hconst (by simpa [xi] using hwindow))

private theorem corrected_residual_sq_integrable
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ) :
    Integrable
      (fun path =>
        ‖correctedEstimator D (schedule epsilon D.L n0) k path -
          fullGradient D
            (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2)
      (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  apply corrected_prefix_sq_integrable D epsilon n0 k
    (fun path =>
      correctedEstimator D (schedule epsilon D.L n0) k path -
        fullGradient D
          (correctedIterate D (schedule epsilon D.L n0) k path))
  intro path path' hwindow
  have hstate := corrected_state_prefix_eq D epsilon n0 k path path' hwindow
  simp [correctedEstimator, correctedIterate, hstate]

private theorem corrected_step_sq_integrable
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ) :
    Integrable
      (fun path =>
        ‖correctedIterate D (schedule epsilon D.L n0) (k + 1) path -
          correctedIterate D (schedule epsilon D.L n0) k path‖ ^ 2)
      (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  let s := schedule epsilon D.L n0
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  apply corrected_prefix_sq_integrable D epsilon n0 (k + 1)
    (fun path =>
      correctedIterate D s (k + 1) path -
        correctedIterate D s k path)
  intro path path' hwindow
  have hprev_window :
      SOptLib.sampleWindow xi 1 k path =
        SOptLib.sampleWindow xi 1 k path' := by
    funext r
    have hcoord := congrFun hwindow ⟨r.1, by omega⟩
    simpa [xi, SOptLib.sampleWindow] using hcoord
  have hprev := corrected_state_prefix_eq D epsilon n0 k path path'
    (by simpa [xi] using hprev_window)
  have hcurr :
      correctedStateProcess D s (k + 1) path =
        correctedStateProcess D s (k + 1) path' := by
    have hbatch := congrFun hwindow ⟨k, Nat.lt_succ_self k⟩
    have hbatch' : path (k + 1) = path' (k + 1) := by
      simpa [xi, SOptLib.sampleWindow, Nat.add_comm] using hbatch
    rw [show correctedStateProcess D s (k + 1) path =
        correctedTransition D path k (correctedStateProcess D s k path) by
          rfl]
    rw [show correctedStateProcess D s (k + 1) path' =
        correctedTransition D path' k (correctedStateProcess D s k path') by
          rfl]
    simp only [correctedTransition]
    dsimp [s]
    rw [hprev]
    simp [hbatch']
  have hcurrx :
      correctedIterate D s (k + 1) path =
        correctedIterate D s (k + 1) path' :=
    congrArg (fun state : State (VariableSpace d) => state.x) hcurr
  have hprevx :
      correctedIterate D s k path =
        correctedIterate D s k path' :=
    congrArg (fun state : State (VariableSpace d) => state.x) hprev
  rw [hcurrx, hprevx]

private theorem corrected_residual_zero_of_refresh
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    (hrefresh : roundedRefreshAt (schedule epsilon D.L n0) k) :
    ∀ path : SourcePath (schedule epsilon D.L n0),
      correctedEstimator D (schedule epsilon D.L n0) k path -
        fullGradient D
          (correctedIterate D (schedule epsilon D.L n0) k path) = 0 := by
  intro path
  cases k with
  | zero =>
      simp
  | succ m =>
      have hprev :
          roundedRefreshAt (schedule epsilon D.L n0) (m + 1) := by
        simpa [Nat.succ_eq_add_one] using hrefresh
      change
        (correctedStateProcess D (schedule epsilon D.L n0) (m + 1) path).v -
            fullGradient D
              (correctedStateProcess D (schedule epsilon D.L n0) (m + 1) path).x = 0
      rw [show correctedStateProcess D (schedule epsilon D.L n0) (m + 1) path =
          correctedTransition D path m
            (correctedStateProcess D (schedule epsilon D.L n0) m path) by
            rfl]
      simp only [correctedTransition]
      simp [hprev]

private theorem corrected_fresh_scalar_integral_eq_sourceIndex
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (Z : SourcePath (schedule epsilon D.L n0) → β)
    (hconst :
      ∀ ⦃path path' : SourcePath (schedule epsilon D.L n0)⦄,
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path =
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path' →
        Z path = Z path')
    (i : Fin (sourceBatchCount (schedule epsilon D.L n0)))
    (G : β → Fin n → ℝ)
    (hG_int :
      ∀ j : Fin n,
        Integrable
          (fun path => G (Z path) j)
          (withReplacementSourceLaw (schedule epsilon D.L n0)))
    (hsample_int :
      Integrable
        (fun path =>
          G (Z path) (path (k + 1) i))
        (withReplacementSourceLaw (schedule epsilon D.L n0))) :
    (∫ path,
        G (Z path) (path (k + 1) i) ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) =
      ∫ path, ∫ j, G (Z path) j ∂sourceIndexLaw n0 ∂
        (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  classical
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let ν := sourceIndexLaw s.n0
  letI : IsProbabilityMeasure μ :=
    withReplacementSourceLaw_isProbability s
  let window : SourcePath s → Fin k → SourceBatch s :=
    SOptLib.sampleWindow (fun j path => path j) 1 k
  have hwindow_range : (Set.range window).Finite := by
    exact Set.Finite.subset Set.finite_univ (by
      intro z hz
      exact Set.mem_univ z)
  have hZ_range : (Set.range Z).Finite := by
    apply Set.Finite.range_of_finite_range_fiber_const hwindow_range
    intro path path' hwindow
    exact hconst hwindow
  let W := {z : β // z ∈ Set.range Z}
  letI : Fintype W := hZ_range.fintype
  let Z' : SourcePath s → W := fun path =>
    ⟨Z path, ⟨path, rfl⟩⟩
  let G' : W → Fin n → ℝ := fun z j => G z.1 j
  have hZ'const :
      ∀ ⦃path path' : SourcePath s⦄,
        window path = window path' → Z' path = Z' path' := by
    intro path path' hwindow
    apply Subtype.ext
    exact hconst hwindow
  have hwindow_meas : Measurable window := by
    refine measurable_pi_lambda _ ?_
    intro r
    exact measurable_pi_apply (1 + r.1)
  have hZ'_meas : Measurable Z' := by
    exact measurable_of_finite_range_fiber_const
      hwindow_meas hwindow_range hZ'const
  have hG'_meas :
      Measurable (fun p : W × Fin n => G' p.1 p.2) :=
    measurable_of_finite _
  have hcoord_meas :
      Measurable
        (fun path : SourcePath s => path (k + 1) i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply (k + 1))
  have h_indep :
      ProbabilityTheory.IndepFun Z'
        (fun path : SourcePath s => path (k + 1) i) μ := by
    exact
      (corrected_prefix_key_current_indep
        D epsilon n0 k Z' hZ'const i).1
  have hmap :
      Measure.map (fun path : SourcePath s => path (k + 1) i) μ = ν := by
    letI : IsProbabilityMeasure ν := sourceIndexLaw_isProbability s.n0
    simpa [μ, ν, withReplacementSourceLaw] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval
        (sourceBatchCount s) (sourceIndexLaw s.n0) (k + 1) i)
  have hidx_uniform :
      ∀ j : Fin n,
        (Measure.map (fun path : SourcePath s => path (k + 1) i) μ).real
            ({j} : Set (Fin n)) =
          (Fintype.card (Fin n) : ℝ)⁻¹ := by
    intro j
    rw [hmap]
    exact sourceIndexLaw_singleton_real s.n0 j
  have hG'_int :
      ∀ j : Fin n, Integrable (fun path => G' (Z' path) j) μ := by
    intro j
    simpa [G', Z', μ] using hG_int j
  have hsample'_int :
      Integrable
        (fun path => G' (Z' path) (path (k + 1) i)) μ := by
    simpa [G', Z', μ] using hsample_int
  have hsum :=
    SOptLib.integral_comp_indep_finite_uniform_eq_integral_inv_card_sum
      (P := μ)
      (idx := fun path : SourcePath s => path (k + 1) i)
      (Z := Z') G' hZ'_meas hcoord_meas h_indep hidx_uniform hG'_meas
      hG'_int
  have hpoint :
      ∀ path : SourcePath s,
        (∫ j, G (Z path) j ∂ν) =
          (Fintype.card (Fin n) : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun j : Fin n => G (Z path) j) := by
    intro path
    simpa [ν, SOptLib.finiteUniformAverage, smul_eq_mul] using
      (sourceIndexLaw_integral_eq_finiteUniformAverage
        s.n0 (fun j : Fin n => G (Z path) j))
  calc
    (∫ path, G (Z path) (path (k + 1) i) ∂μ) =
        ∫ path, G' (Z' path) (path (k + 1) i) ∂μ := by
          rfl
    _ = ∫ path,
        (Fintype.card (Fin n) : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun j : Fin n => G' (Z' path) j) ∂μ := hsum
    _ = ∫ path, ∫ j, G (Z path) j ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with path
      rw [hpoint path]

private theorem corrected_fresh_vector_integral_eq_zero
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    {β V : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [SecondCountableTopology V] [OpensMeasurableSpace V]
    (Z : SourcePath (schedule epsilon D.L n0) → β)
    (hconst :
      ∀ ⦃path path' : SourcePath (schedule epsilon D.L n0)⦄,
        SOptLib.sampleWindow
            (fun j path => path j) 1 k path =
          SOptLib.sampleWindow
            (fun j path => path j) 1 k path' →
        Z path = Z path')
    (i : Fin (sourceBatchCount (schedule epsilon D.L n0)))
    (G : β → Fin n → V)
    (hG_int :
      ∀ j : Fin n,
        Integrable
          (fun path => G (Z path) j)
          (withReplacementSourceLaw (schedule epsilon D.L n0)))
    (hsample_int :
      Integrable
        (fun path =>
          G (Z path) (path (k + 1) i))
        (withReplacementSourceLaw (schedule epsilon D.L n0)))
    (hcenter : ∀ z, ∫ j, G z j ∂sourceIndexLaw n0 = 0) :
    (∫ path,
        G (Z path) (path (k + 1) i) ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) = 0 := by
  classical
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let ν := sourceIndexLaw s.n0
  letI : IsProbabilityMeasure μ :=
    withReplacementSourceLaw_isProbability s
  let window : SourcePath s → Fin k → SourceBatch s :=
    SOptLib.sampleWindow (fun j path => path j) 1 k
  have hwindow_range : (Set.range window).Finite := by
    exact Set.Finite.subset Set.finite_univ (by
      intro z hz
      exact Set.mem_univ z)
  have hZ_range : (Set.range Z).Finite := by
    exact Set.Finite.range_of_finite_range_fiber_const
      hwindow_range (by
        intro path path' hwindow
        exact hconst hwindow)
  let W := {z : β // z ∈ Set.range Z}
  letI : Fintype W := hZ_range.fintype
  let Z' : SourcePath s → W := fun path =>
    ⟨Z path, ⟨path, rfl⟩⟩
  let G' : W → Fin n → V := fun z j => G z.1 j
  have hZ'const :
      ∀ ⦃path path' : SourcePath s⦄,
        window path = window path' → Z' path = Z' path' := by
    intro path path' hwindow
    apply Subtype.ext
    exact hconst hwindow
  have hwindow_meas : Measurable window := by
    refine measurable_pi_lambda _ ?_
    intro r
    exact measurable_pi_apply (1 + r.1)
  have hZ'_meas : Measurable Z' :=
    measurable_of_finite_range_fiber_const
      hwindow_meas hwindow_range hZ'const
  have hcoord_meas :
      Measurable
        (fun path : SourcePath s => path (k + 1) i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply (k + 1))
  have h_indep :
      ProbabilityTheory.IndepFun Z'
        (fun path : SourcePath s => path (k + 1) i) μ :=
    (corrected_prefix_key_current_indep
      D epsilon n0 k Z' hZ'const i).1
  have hmap :
      Measure.map (fun path : SourcePath s => path (k + 1) i) μ = ν := by
    letI : IsProbabilityMeasure ν := sourceIndexLaw_isProbability s.n0
    simpa [μ, ν, withReplacementSourceLaw] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval
        (sourceBatchCount s) (sourceIndexLaw s.n0) (k + 1) i)
  have hG'_int :
      ∀ j : Fin n, Integrable (fun path => G' (Z' path) j) μ := by
    intro j
    simpa [G', Z', μ] using hG_int j
  have hsample'_int :
      Integrable
        (fun path => G' (Z' path) (path (k + 1) i)) μ := by
    simpa [G', Z', μ] using hsample_int
  have hfixed_zero : ∀ z : W, ∫ j, G' z j ∂ν = 0 := by
    intro z
    simpa [G', ν] using hcenter z.1
  have hkernel_meas :
      Measurable (fun p : W × Fin n => G' p.1 p.2) :=
    measurable_of_finite _
  exact
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := μ) (ν := ν) (φ := G')
      (X := Z') (Y := fun path : SourcePath s => path (k + 1) i)
      (hφ_prod := hkernel_meas.aestronglyMeasurable)
      hZ'_meas.aemeasurable hcoord_meas.aemeasurable h_indep hmap
      hsample'_int hfixed_zero

private theorem corrected_fresh_scalar_integral_eq_zero
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) (k : ℕ)
    {β : Type*} [MeasurableSpace β]
    (X : SourcePath (schedule epsilon D.L n0) → β)
    (hX_meas : Measurable X)
    (i : Fin (sourceBatchCount (schedule epsilon D.L n0)))
    (G : β → Fin n → ℝ)
    (hG_meas : Measurable (fun p : β × Fin n => G p.1 p.2))
    (hsample_int :
      Integrable
        (fun path =>
          G (X path) (path (k + 1) i))
        (withReplacementSourceLaw (schedule epsilon D.L n0)))
    (h_indep :
      ProbabilityTheory.IndepFun X
        (fun path => path (k + 1) i)
        (withReplacementSourceLaw (schedule epsilon D.L n0)))
    (hcenter : ∀ z, ∫ j, G z j ∂sourceIndexLaw n0 = 0) :
    (∫ path,
        G (X path) (path (k + 1) i) ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) = 0 := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let ν := sourceIndexLaw s.n0
  letI : IsProbabilityMeasure μ :=
    withReplacementSourceLaw_isProbability s
  have hcoord_meas :
      Measurable (fun path : SourcePath s => path (k + 1) i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply (k + 1))
  have hmap :
      Measure.map (fun path : SourcePath s => path (k + 1) i) μ = ν := by
    letI : IsProbabilityMeasure ν := sourceIndexLaw_isProbability s.n0
    simpa [μ, ν, withReplacementSourceLaw] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval
        (sourceBatchCount s) (sourceIndexLaw s.n0) (k + 1) i)
  have hfixed_zero : ∀ z, ∫ j, G z j ∂ν = 0 := by
    simpa [ν] using hcenter
  exact
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := μ) (ν := ν) (φ := G) (X := X)
      (Y := fun path : SourcePath s => path (k + 1) i)
      (hφ_prod := hG_meas.aestronglyMeasurable)
      hX_meas.aemeasurable hcoord_meas.aemeasurable h_indep hmap
      (by simpa [μ] using hsample_int) hfixed_zero

private theorem corrected_step_bound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (k : ℕ) (path : SourcePath (schedule epsilon D.L n0)) :
    ‖correctedIterate D (schedule epsilon D.L n0) (k + 1) path -
        correctedIterate D (schedule epsilon D.L n0) k path‖ ≤
      epsilon / (D.L * n0.1) := by
  rcases hScalar with ⟨hepsilon, hL⟩
  have hn0pos : 0 < (n0.1 : ℝ) := n0_pos n0
  have hLn0 : 0 < D.L * n0.1 := mul_pos hL hn0pos
  let s := schedule epsilon D.L n0
  let state := correctedStateProcess D s k path
  have hlive :
      liveCorrectedOptionIIUpdate s state.x state.v =
        optionIIUpdate epsilon D.L n0.1 state.x state.v := by
    by_cases hv : 0 < ‖state.v‖
    · unfold liveCorrectedOptionIIUpdate
      simp [optionIIUpdate, optionIIStepSize, s, schedule,
        FiniteSumTheorem2ImplementationInternal.schedule, div_eq_mul_inv, hv] <;>
        congr 2 <;> ring
    · have hv0 : ‖state.v‖ = 0 := by
        exact le_antisymm (not_lt.mp hv) (norm_nonneg _)
      have hvv : state.v = 0 := norm_eq_zero.mp hv0
      unfold liveCorrectedOptionIIUpdate
      simp only [hv]
      simp [optionIIUpdate, optionIIStepSize, s, schedule,
        FiniteSumTheorem2ImplementationInternal.schedule, hv0, hvv]
  change
    ‖(correctedTransition D path k
        (correctedStateProcess D s k path)).x -
        (correctedStateProcess D s k path).x‖ ≤
      epsilon / (D.L * n0.1)
  change
    ‖liveCorrectedOptionIIUpdate s
        (correctedStateProcess D s k path).x
        (correctedStateProcess D s k path).v -
        (correctedStateProcess D s k path).x‖ ≤
      epsilon / (D.L * n0.1)
  rw [hlive]
  simpa [div_eq_mul_inv] using
    (optionII_step_bound_obligation
      (E := VariableSpace d)
      (epsilon := epsilon) (L := D.L) (n0 := n0.1)
      (x := (correctedStateProcess D s k path).x)
      (v := (correctedStateProcess D s k path).v)
      (le_of_lt hepsilon) hLn0)

private theorem corrected_rounded_epoch_budget
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) :
    ((roundedRefreshPeriod (schedule epsilon D.L n0) - 1 : ℝ) *
        (D.L ^ 2 / (sourceBatchCount (schedule epsilon D.L n0) : ℝ)) *
        (epsilon / (D.L * n0.1)) ^ 2) ≤
      epsilon ^ 2 := by
  rcases hScalar with ⟨hepsilon, hL⟩
  let s := schedule epsilon D.L n0
  have hn0pos : 0 < n0.1 := n0_pos n0
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := sqrt_n_pos n0
  have hq_pos : 0 < s.q := by
    simpa [s] using schedule_q_pos n0 ⟨hepsilon, hL⟩
  have hS2_pos : 0 < s.S2 := by
    simpa [s] using schedule_S2_pos n0 ⟨hepsilon, hL⟩
  have hrefresh_le : (roundedRefreshPeriod s - 1 : ℝ) ≤ s.q := by
    unfold roundedRefreshPeriod
    by_cases hfloor : 1 ≤ Nat.floor s.q
    · have hmax : max 1 (Nat.floor s.q) = Nat.floor s.q := max_eq_right hfloor
      rw [hmax]
      have hsub : Nat.floor s.q - 1 ≤ Nat.floor s.q :=
        Nat.sub_le _ _
      exact le_trans (by exact_mod_cast hsub)
        (Nat.floor_le (le_of_lt hq_pos))
    · have hfloor_zero : Nat.floor s.q = 0 := by omega
      simp [hfloor_zero]
      positivity
  have hbatch_ge : s.S2 ≤ (sourceBatchCount s : ℝ) := by
    unfold sourceBatchCount
    have hceil : s.S2 ≤ (Nat.ceil s.S2 : ℝ) := by
      exact_mod_cast Nat.le_ceil s.S2
    exact le_trans hceil (by
      exact_mod_cast Nat.le_max_right 1 (Nat.ceil s.S2))
  have hbatch_pos : 0 < (sourceBatchCount s : ℝ) := by
    exact_mod_cast sourceBatchCount_pos s
  have hratio :
      D.L ^ 2 / (sourceBatchCount s : ℝ) ≤ D.L ^ 2 / s.S2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg D.L) hS2_pos hbatch_ge
  have hbase :
      (s.q * (D.L ^ 2 / s.S2) *
          (epsilon / (D.L * n0.1)) ^ 2) = epsilon ^ 2 := by
    rw [schedule_q, schedule_S2]
    field_simp [ne_of_gt hL, ne_of_gt hn0pos, ne_of_gt hsqrt_pos]
  have hnonneg :
      0 ≤ (roundedRefreshPeriod s - 1 : ℝ) ∧
        0 ≤ D.L ^ 2 / (sourceBatchCount s : ℝ) ∧
        0 ≤ (epsilon / (D.L * n0.1)) ^ 2 := by
    have hperiod_one : 1 ≤ (roundedRefreshPeriod s : ℝ) := by
      exact_mod_cast roundedRefreshPeriod_pos s
    refine ⟨by linarith,
      div_nonneg (sq_nonneg _) (le_of_lt hbatch_pos), sq_nonneg _⟩
  calc
    (roundedRefreshPeriod s - 1 : ℝ) *
          (D.L ^ 2 / (sourceBatchCount s : ℝ)) *
          (epsilon / (D.L * n0.1)) ^ 2
        ≤ s.q * (D.L ^ 2 / s.S2) *
          (epsilon / (D.L * n0.1)) ^ 2 := by
            gcongr
    _ = epsilon ^ 2 := hbase

private theorem corrected_nonrefresh_residual_decomposition
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (k : ℕ) (path : SourcePath (schedule epsilon D.L n0))
    (hrefresh :
      ¬ roundedRefreshAt (schedule epsilon D.L n0) (k + 1)) :
    correctedEstimator D (schedule epsilon D.L n0) (k + 1) path -
        fullGradient D
          (correctedIterate D (schedule epsilon D.L n0) (k + 1) path) =
      correctedEstimator D (schedule epsilon D.L n0) k path -
        fullGradient D
          (correctedIterate D (schedule epsilon D.L n0) k path) +
      batchAverage D (path (k + 1))
          (correctedIterate D (schedule epsilon D.L n0) (k + 1) path) -
        batchAverage D (path (k + 1))
          (correctedIterate D (schedule epsilon D.L n0) k path) -
        (fullGradient D
          (correctedIterate D (schedule epsilon D.L n0) (k + 1) path) -
          fullGradient D
            (correctedIterate D (schedule epsilon D.L n0) k path)) := by
  let s := schedule epsilon D.L n0
  let state := correctedStateProcess D s k path
  let xNext := liveCorrectedOptionIIUpdate s state.x state.v
  have hstate :
      correctedStateProcess D s (k + 1) path =
        correctedTransition D path k (correctedStateProcess D s k path) := by
    rfl
  have hvNext :
      (correctedStateProcess D s (k + 1) path).v =
        recursiveEstimator D (path (k + 1)) state.v state.x xNext := by
    rw [hstate]
    simp [correctedTransition, state, xNext, s, hrefresh]
  have hxNext :
      (correctedStateProcess D s (k + 1) path).x = xNext := by
    rw [hstate]
    rfl
  rw [show correctedEstimator D s (k + 1) path =
      recursiveEstimator D (path (k + 1)) state.v state.x xNext by
        simpa [correctedEstimator, state] using hvNext]
  rw [show correctedIterate D s (k + 1) path = xNext by
        simpa [correctedIterate] using hxNext]
  simp only [correctedEstimator, correctedIterate, state]
  unfold recursiveEstimator
  simp only [s, neg_one_smul, sub_eq_add_neg]
  abel

set_option maxHeartbeats 800000 in
private theorem corrected_nonrefresh_residual_second_moment_step
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (k : ℕ)
    (hrefresh :
      ¬ roundedRefreshAt (schedule epsilon D.L n0) (k + 1)) :
    (∫ path,
        ‖correctedEstimator D (schedule epsilon D.L n0) (k + 1) path -
          fullGradient D
            (correctedIterate D (schedule epsilon D.L n0) (k + 1) path)‖ ^ 2 ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) ≤
      (∫ path,
        ‖correctedEstimator D (schedule epsilon D.L n0) k path -
          fullGradient D
            (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2 ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) +
        (D.L ^ 2 / (sourceBatchCount (schedule epsilon D.L n0) : ℝ)) *
          (∫ path,
            ‖correctedIterate D (schedule epsilon D.L n0) (k + 1) path -
              correctedIterate D (schedule epsilon D.L n0) k path‖ ^ 2 ∂
            (withReplacementSourceLaw (schedule epsilon D.L n0))) := by
  classical
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let b := sourceBatchCount s
  let xPrev : SourcePath s → VariableSpace d :=
    fun path => correctedIterate D s k path
  let xCurr : SourcePath s → VariableSpace d :=
    fun path => correctedIterate D s (k + 1) path
  let Z : SourcePath s → VariableSpace d × VariableSpace d :=
    fun path => (xCurr path, xPrev path)
  let deltaPrev : SourcePath s → VariableSpace d :=
    fun path => correctedEstimator D s k path - fullGradient D (xPrev path)
  let deltaNext : SourcePath s → VariableSpace d :=
    fun path =>
      correctedEstimator D s (k + 1) path - fullGradient D (xCurr path)
  let eps : Fin b → SourcePath s → VariableSpace d :=
    fun r path =>
      componentGradient D.componentObjective (path (k + 1) r) (xCurr path) -
          componentGradient D.componentObjective (path (k + 1) r) (xPrev path) -
        (fullGradient D (xCurr path) - fullGradient D (xPrev path))
  let inc : SourcePath s → VariableSpace d :=
    fun path =>
      batchAverage D (path (k + 1)) (xCurr path) -
          batchAverage D (path (k + 1)) (xPrev path) -
        (fullGradient D (xCurr path) - fullGradient D (xPrev path))
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  letI : IsProbabilityMeasure μ :=
    withReplacementSourceLaw_isProbability s
  have hbpos : 0 < b := by
    simpa [b] using sourceBatchCount_pos s
  have hprefix_succ_to_prev :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 (k + 1) path =
          SOptLib.sampleWindow xi 1 (k + 1) path' →
        SOptLib.sampleWindow xi 1 k path =
          SOptLib.sampleWindow xi 1 k path' := by
    intro path path' hwindow
    funext r
    have hcoord := congrFun hwindow ⟨r.1, by omega⟩
    simpa [xi, SOptLib.sampleWindow] using hcoord
  have hstate_prefix :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 k path =
          SOptLib.sampleWindow xi 1 k path' →
        correctedStateProcess D s k path =
          correctedStateProcess D s k path' :=
    corrected_state_prefix_eq D epsilon n0 k
  have hZ_const :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 k path =
          SOptLib.sampleWindow xi 1 k path' →
        Z path = Z path' := by
    intro path path' hwindow
    have hstate := hstate_prefix hwindow
    have hnextx :
        correctedIterate D s (k + 1) path =
          correctedIterate D s (k + 1) path' := by
      simp [xCurr, correctedIterate, correctedStateProcess,
        correctedTransition, hstate]
    exact Prod.ext hnextx (by
      simpa [xPrev] using congrArg
        (fun state : State (VariableSpace d) => state.x) hstate)
  have hdeltaPrev_const :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 k path =
          SOptLib.sampleWindow xi 1 k path' →
        deltaPrev path = deltaPrev path' := by
    intro path path' hwindow
    have hstate := hstate_prefix hwindow
    simp [deltaPrev, xPrev, correctedEstimator, correctedIterate, hstate]
  have hcurrent_batch_eq :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 (k + 1) path =
          SOptLib.sampleWindow xi 1 (k + 1) path' →
        path (k + 1) = path' (k + 1) := by
    intro path path' hwindow
    have hcoord := congrFun hwindow ⟨k, Nat.lt_succ_self k⟩
    simpa [xi, SOptLib.sampleWindow, Nat.add_comm] using hcoord
  have hnext_state_const :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 (k + 1) path =
          SOptLib.sampleWindow xi 1 (k + 1) path' →
        correctedStateProcess D s (k + 1) path =
          correctedStateProcess D s (k + 1) path' := by
    intro path path' hwindow
    have hstate := hstate_prefix (hprefix_succ_to_prev hwindow)
    have hbatch := hcurrent_batch_eq hwindow
    simp [correctedStateProcess, correctedTransition, hstate, hbatch,
      hrefresh]
  have heps_const :
      ∀ r : Fin b, ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 (k + 1) path =
          SOptLib.sampleWindow xi 1 (k + 1) path' →
        eps r path = eps r path' := by
    intro r path path' hwindow
    have hZ := hZ_const (hprefix_succ_to_prev hwindow)
    have hbatch := hcurrent_batch_eq hwindow
    have hsample : path (k + 1) r = path' (k + 1) r :=
      congrFun hbatch r
    have hnextx : xCurr path = xCurr path' :=
      congrArg Prod.fst hZ
    have hprevx : xPrev path = xPrev path' :=
      congrArg Prod.snd hZ
    simp [eps, Z, xCurr, xPrev, hsample, hnextx, hprevx]
  have hdeltaNext_const :
      ∀ ⦃path path' : SourcePath s⦄,
        SOptLib.sampleWindow xi 1 (k + 1) path =
          SOptLib.sampleWindow xi 1 (k + 1) path' →
        deltaNext path = deltaNext path' := by
    intro path path' hwindow
    have hstate := hnext_state_const hwindow
    simp [deltaNext, xCurr, correctedEstimator, correctedIterate, hstate]
  have hprev_sq :
      Integrable (fun path => ‖deltaPrev path‖ ^ 2) μ := by
    apply integrable_of_finiteSampleWindow_factor_aestrongly xi 1 k
    · intro j
      exact measurable_pi_apply j
    · intro path path' hwindow
      exact congrArg (fun v => ‖v‖ ^ 2) (hdeltaPrev_const hwindow)
  have hprev_meas : AEStronglyMeasurable deltaPrev μ := by
    have hdeltaPrev_meas : Measurable deltaPrev := by
      have hwindow_meas :
          Measurable (SOptLib.sampleWindow xi 1 k) := by
        refine measurable_pi_lambda _ ?_
        intro r
        exact measurable_pi_apply (1 + r.1)
      have hle :
          MeasurableSpace.comap
              (SOptLib.sampleWindow
                (fun j path => path j) 1 k)
              (by infer_instance) ≤
            (inferInstance : MeasurableSpace (SourcePath s)) := by
        simpa [xi] using hwindow_meas.comap_le
      have hfactor :
          @Measurable (SourcePath s) (VariableSpace d)
            (MeasurableSpace.comap
              (SOptLib.sampleWindow
                (fun j path => path j) 1 k)
              (by infer_instance)) (by infer_instance) deltaPrev :=
        corrected_factor_measurable_under_window
          D epsilon n0 k deltaPrev hdeltaPrev_const
      exact hfactor.mono hle le_rfl
    exact hdeltaPrev_meas.aestronglyMeasurable
  have heps_sq :
      ∀ r : Fin b, Integrable (fun path => ‖eps r path‖ ^ 2) μ := by
    intro r
    apply integrable_of_finiteSampleWindow_factor_aestrongly xi 1 (k + 1)
    · intro j
      exact measurable_pi_apply j
    · intro path path' hwindow
      exact congrArg (fun v => ‖v‖ ^ 2) (heps_const r hwindow)
  have heps_meas :
      ∀ r : Fin b, AEStronglyMeasurable (eps r) μ := by
    intro r
    have hwindow_meas :
        Measurable (SOptLib.sampleWindow xi 1 (k + 1)) := by
      refine measurable_pi_lambda _ ?_
      intro q
      exact measurable_pi_apply (1 + q.1)
    have hle :
        MeasurableSpace.comap (SOptLib.sampleWindow xi 1 (k + 1))
            (by infer_instance) ≤
          (inferInstance : MeasurableSpace (SourcePath s)) := by
      simpa [xi] using hwindow_meas.comap_le
    have hfactor :
        @Measurable (SourcePath s) (VariableSpace d)
          (MeasurableSpace.comap
            (SOptLib.sampleWindow
              (fun j path => path j) 1 (k + 1))
            (by infer_instance)) (by infer_instance) (eps r) :=
      corrected_factor_measurable_under_window
        D epsilon n0 (k + 1) (eps r) (heps_const r)
    exact (hfactor.mono hle le_rfl).aestronglyMeasurable
  have hinc_eq :
      inc = fun path => ((b : ℝ)⁻¹) •
        Finset.sum Finset.univ (fun r => eps r path) := by
    funext path
    have hbne : (b : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hbpos)
    have hcoef (z : VariableSpace d) :
        ((sourceBatchCount s : ℝ)⁻¹) •
            (sourceBatchCount s : ℝ) • z = z := by
      rw [smul_smul, inv_mul_cancel₀]
      · exact one_smul ℝ z
      · exact_mod_cast (Nat.ne_of_gt (sourceBatchCount_pos s))
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (n_pos n0))
    have hfull (x : VariableSpace d) :
        (Finset.sum Finset.univ
            (fun j : Fin n =>
              (n : ℝ)⁻¹ •
                componentGradient D.componentObjective j x)) =
          Finset.sum Finset.univ
            (fun j : Fin n =>
              (b : ℝ)⁻¹ • (b : ℝ) •
                (n : ℝ)⁻¹ •
                  componentGradient D.componentObjective j x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hbne, hn_ne]
    simp [inc, eps, batchAverage, SOptLib.finiteUniformAverage,
      Finset.smul_sum, smul_sub, Finset.sum_sub_distrib, Finset.sum_const,
      hbne, hcoef, Finset.mul_sum]
    have hfull' (x : VariableSpace d) :
        (Finset.sum Finset.univ
            (fun j : Fin n =>
              (n : ℝ)⁻¹ •
                ∇ (fun y : VariableSpace d => D.componentObjective j y) x)) =
          Finset.sum Finset.univ
            (fun j : Fin n =>
              (sourceBatchCount s : ℝ)⁻¹ • (sourceBatchCount s : ℝ) •
                (n : ℝ)⁻¹ •
                  ∇ (fun y : VariableSpace d => D.componentObjective j y) x) := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa [componentGradient] using
        (hcoef ((n : ℝ)⁻¹ •
          ∇ (fun y : VariableSpace d => D.componentObjective j y) x)).symm
    dsimp [b]
    rw [hfull' (xCurr path), hfull' (xPrev path)]
    simp [b, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hrec :
      Filter.EventuallyEq (ae μ) deltaNext
        (fun path => deltaPrev path + inc path) := by
    filter_upwards [] with path
    have hdecomp := corrected_nonrefresh_residual_decomposition
      D epsilon n0 k path hrefresh
    calc
      deltaNext path =
          correctedEstimator D s (k + 1) path -
            fullGradient D (xCurr path) := by
              rfl
      _ = correctedEstimator D s k path -
            fullGradient D (xPrev path) +
            batchAverage D (path (k + 1)) (xCurr path) -
            batchAverage D (path (k + 1)) (xPrev path) -
            (fullGradient D (xCurr path) - fullGradient D (xPrev path)) := by
              simpa [s, xCurr, xPrev] using hdecomp
      _ = deltaPrev path + inc path := by
              simp [deltaPrev, inc]
              abel
  have hdiag :
      ∀ r : Fin b, Integrable (fun path => ‖eps r path‖ ^ 2) μ ∧
        ∫ path, ‖eps r path‖ ^ 2 ∂μ ≤
          D.L ^ 2 * ∫ path, ‖xCurr path - xPrev path‖ ^ 2 ∂μ := by
    intro r
    refine ⟨heps_sq r, ?_⟩
    let G : (VariableSpace d × VariableSpace d) → Fin n → ℝ :=
      fun q j =>
        ‖componentGradient D.componentObjective j q.1 -
            componentGradient D.componentObjective j q.2 -
          (fullGradient D q.1 - fullGradient D q.2)‖ ^ 2
    have hG_int :
        ∀ j : Fin n, Integrable (fun path => G (Z path) j) μ := by
      intro j
      apply integrable_of_finiteSampleWindow_factor_aestrongly xi 1 k
      · intro t
        exact measurable_pi_apply t
      · intro path path' hwindow
        have hwindow' :
            SOptLib.sampleWindow xi 1 k path =
              SOptLib.sampleWindow xi 1 k path' := by
          simpa [xi] using hwindow
        exact congrArg (fun q => G q j) (hZ_const hwindow')
    have hsample_int :
        Integrable
          (fun path => G (Z path) (path (k + 1) r)) μ := by
      simpa [G, Z, eps] using heps_sq r
    have hsample_avg :=
      corrected_fresh_scalar_integral_eq_sourceIndex
        D epsilon n0 k Z hZ_const r G hG_int hsample_int
    have hpoint :
        ∀ path : SourcePath s,
          (∫ j, G (Z path) j ∂sourceIndexLaw s.n0) ≤
            D.L ^ 2 * ‖xCurr path - xPrev path‖ ^ 2 := by
      intro path
      rw [sourceIndexLaw_integral_eq_finiteUniformAverage]
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (n_pos n0))
      have hvar :
          SOptLib.finiteUniformAverage (fun j : Fin n => G (Z path) j) ≤
            SOptLib.finiteUniformAverage
              (fun j : Fin n =>
                ‖componentGradient D.componentObjective j (xCurr path) -
                    componentGradient D.componentObjective j (xPrev path)‖ ^ 2) := by
        have hvar' :
            Finset.sum Finset.univ
                (fun j : Fin n =>
                  (Fintype.card (Fin n) : ℝ)⁻¹ *
                    ‖componentGradient D.componentObjective j (xCurr path) -
                        componentGradient D.componentObjective j (xPrev path) -
                      (fullGradient D (xCurr path) -
                        fullGradient D (xPrev path))‖ ^ 2) ≤
              Finset.sum Finset.univ
                (fun j : Fin n =>
                  (Fintype.card (Fin n) : ℝ)⁻¹ *
                    ‖componentGradient D.componentObjective j (xCurr path) -
                      componentGradient D.componentObjective j (xPrev path)‖ ^ 2) := by
          refine Finset.weighted_variance_le_second_moment
              (s := Finset.univ)
              (q := fun _ : Fin n => (Fintype.card (Fin n) : ℝ)⁻¹)
              (a := fun j : Fin n =>
                componentGradient D.componentObjective j (xCurr path) -
                  componentGradient D.componentObjective j (xPrev path))
              (μ := fullGradient D (xCurr path) - fullGradient D (xPrev path))
              ?_ ?_
          · simp [Fintype.card_fin, hn_ne]
          · simp [fullGradient, SOptLib.finiteUniformAverage, Finset.smul_sum,
              smul_sub, Fintype.card_fin, hn_ne]
        simpa [G, Z, SOptLib.finiteUniformAverage, smul_eq_mul,
          Finset.mul_sum, Fintype.card_fin, hn_ne] using hvar'
      exact hvar.trans (D.averagedLipschitzGradient
        (xCurr path) (xPrev path))
    calc
      ∫ path, ‖eps r path‖ ^ 2 ∂μ =
          ∫ path, ∫ j, G (Z path) j ∂sourceIndexLaw s.n0 ∂μ := hsample_avg
      _ ≤ ∫ path, D.L ^ 2 * ‖xCurr path - xPrev path‖ ^ 2 ∂μ := by
        have hdist_sq :
            Integrable (fun path => ‖xCurr path - xPrev path‖ ^ 2) μ := by
          have hdist_const :
              ∀ ⦃path path' : SourcePath s⦄,
                SOptLib.sampleWindow xi 1 (k + 1) path =
                    SOptLib.sampleWindow xi 1 (k + 1) path' →
                ‖xCurr path - xPrev path‖ ^ 2 =
                  ‖xCurr path' - xPrev path'‖ ^ 2 := by
            intro path path' hwindow
            have hprev_window := hprefix_succ_to_prev hwindow
            have hprev := hstate_prefix hprev_window
            have hcurr := hnext_state_const hwindow
            have hcurrx : xCurr path = xCurr path' := by
              dsimp [xCurr]
              exact congrArg
                (fun state : State (VariableSpace d) => state.x) hcurr
            have hprevx : xPrev path = xPrev path' := by
              dsimp [xPrev]
              exact congrArg
                (fun state : State (VariableSpace d) => state.x) hprev
            rw [hcurrx, hprevx]
          have hfactor :=
            corrected_factor_measurable_under_window
              D epsilon n0 (k + 1)
              (fun path => ‖xCurr path - xPrev path‖ ^ 2)
              hdist_const
          have hwindow_meas :
              Measurable (SOptLib.sampleWindow xi 1 (k + 1)) := by
            refine measurable_pi_lambda _ ?_
            intro j
            exact measurable_pi_apply (1 + j.1)
          have hle :
              MeasurableSpace.comap (SOptLib.sampleWindow xi 1 (k + 1))
                  (by infer_instance) ≤
                (inferInstance : MeasurableSpace (SourcePath s)) := by
            simpa [xi] using hwindow_meas.comap_le
          have hmeas :
              Measurable (fun path => ‖xCurr path - xPrev path‖ ^ 2) :=
            hfactor.mono hle le_rfl
          have hbound :
              ∀ path, ‖xCurr path - xPrev path‖ ^ 2 ≤
                (epsilon / (D.L * n0.1)) ^ 2 := by
            intro path
            have hstep := corrected_step_bound D epsilon n0 hScalar k path
            change ‖xCurr path - xPrev path‖ ≤
              epsilon / (D.L * n0.1) at hstep
            have hpos : 0 ≤ epsilon / (D.L * n0.1) := by
              rcases hScalar with ⟨hepsilon, hL⟩
              exact le_of_lt
                (div_pos hepsilon (mul_pos hL (n0_pos n0)))
            exact (sq_le_sq₀ (norm_nonneg _) hpos).2 hstep
          refine MeasureTheory.Integrable.of_bound
            hmeas.aestronglyMeasurable
            ((epsilon / (D.L * n0.1)) ^ 2) ?_
          filter_upwards [] with path
          simpa [Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg (‖xCurr path - xPrev path‖))]
            using hbound path
        have hleft :
            Integrable
              (fun path => ∫ j, G (Z path) j ∂sourceIndexLaw s.n0) μ := by
          have hsum :
              Integrable
                (fun path =>
                  Finset.sum Finset.univ (fun j : Fin n => G (Z path) j)) μ :=
            MeasureTheory.integrable_finset_sum Finset.univ
              (fun j _hj => hG_int j)
          have hscaled := hsum.const_mul
            (Fintype.card (Fin n) : ℝ)⁻¹
          refine hscaled.congr ?_
          filter_upwards [] with path
          rw [sourceIndexLaw_integral_eq_finiteUniformAverage]
          rfl
        have hright :
            Integrable
              (fun path => D.L ^ 2 * ‖xCurr path - xPrev path‖ ^ 2) μ :=
          hdist_sq.const_mul _
        exact integral_mono_ae hleft hright (by
          filter_upwards [] with path
          exact hpoint path)
      _ = D.L ^ 2 * ∫ path, ‖xCurr path - xPrev path‖ ^ 2 ∂μ := by
        rw [integral_const_mul]
  have hcross :
      ∀ r ∈ (Finset.univ : Finset (Fin b)),
        ∀ r' ∈ (Finset.univ : Finset (Fin b)), r ≠ r' →
          (MeasureTheory.integral μ
              (fun path => inner ℝ (eps r path) (eps r' path))) = 0 := by
    intro r hr r' hr' hrr'
    let window : SourcePath s → Fin k → SourceBatch s :=
      SOptLib.sampleWindow (fun j path => path j) 1 k
    have hwindow_range : (Set.range window).Finite := by
      exact Set.Finite.subset Set.finite_univ (by
        intro z hz
        exact Set.mem_univ z)
    have hZ_range : (Set.range Z).Finite := by
      exact Set.Finite.range_of_finite_range_fiber_const
        hwindow_range (by
          intro path path' hwindow
          exact hZ_const hwindow)
    let W := {z : VariableSpace d × VariableSpace d // z ∈ Set.range Z}
    letI : Fintype W := hZ_range.fintype
    let Z' : SourcePath s → W := fun path =>
      ⟨Z path, ⟨path, rfl⟩⟩
    have hZ'const :
        ∀ ⦃path path' : SourcePath s⦄,
          window path = window path' → Z' path = Z' path' := by
      intro path path' hwindow
      apply Subtype.ext
      exact hZ_const hwindow
    have hwindow_meas : Measurable window := by
      refine measurable_pi_lambda _ ?_
      intro q
      exact measurable_pi_apply (1 + q.1)
    have hZ'_meas : Measurable Z' :=
      measurable_of_finite_range_fiber_const
        hwindow_meas hwindow_range hZ'const
    let X : SourcePath s → W × Fin n :=
      fun path => (Z' path, path (k + 1) r')
    have hX_meas : Measurable X :=
      hZ'_meas.prodMk
        ((measurable_pi_apply r').comp (measurable_pi_apply (k + 1)))
    have hindep :
      ProbabilityTheory.IndepFun X
          (fun path : SourcePath s => path (k + 1) r) μ :=
      (corrected_prefix_key_current_indep
        D epsilon n0 k Z' hZ'const r).2 r' hrr'.symm
    let G : (W × Fin n) → Fin n → ℝ := fun q j =>
      inner ℝ
        (componentGradient D.componentObjective j q.1.1.1 -
          componentGradient D.componentObjective j q.1.1.2 -
          (fullGradient D q.1.1.1 - fullGradient D q.1.1.2))
        (componentGradient D.componentObjective q.2 q.1.1.1 -
          componentGradient D.componentObjective q.2 q.1.1.2 -
          (fullGradient D q.1.1.1 - fullGradient D q.1.1.2))
    have hG_meas : Measurable (fun p : (W × Fin n) × Fin n => G p.1 p.2) :=
      measurable_of_finite _
    have hsample_int :
        Integrable
          (fun path : SourcePath s => G (X path) (path (k + 1) r)) μ := by
      simpa [G, X, Z', eps] using
        (integrable_inner_of_integrable_sq_norm
          (heps_meas r) (heps_meas r') (heps_sq r) (heps_sq r'))
    have hcenter : ∀ q : W × Fin n, ∫ j, G q j ∂sourceIndexLaw s.n0 = 0 := by
      intro q
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (n_pos n0))
      let R : Fin n → VariableSpace d := fun j =>
        componentGradient D.componentObjective j q.1.1.1 -
          componentGradient D.componentObjective j q.1.1.2 -
          (fullGradient D q.1.1.1 - fullGradient D q.1.1.2)
      let v : VariableSpace d :=
        componentGradient D.componentObjective q.2 q.1.1.1 -
          componentGradient D.componentObjective q.2 q.1.1.2 -
          (fullGradient D q.1.1.1 - fullGradient D q.1.1.2)
      have hR_int :
          Integrable R (sourceIndexLaw s.n0) := by
        letI : IsProbabilityMeasure (sourceIndexLaw s.n0) :=
          sourceIndexLaw_isProbability s.n0
        exact integrable_of_finite_range
          (measurable_of_finite R).aestronglyMeasurable (Set.finite_range R)
      have hR_zero : (∫ j, R j ∂sourceIndexLaw s.n0) = 0 := by
        rw [sourceIndexLaw_integral_eq_finiteUniformAverage]
        simp [R, SOptLib.finiteUniformAverage, fullGradient, componentGradient,
          Finset.smul_sum, smul_sub, Finset.sum_sub_distrib,
          ← Nat.cast_smul_eq_nsmul ℝ, hn_ne] <;>
          field_simp [hn_ne] <;> module
      have hlin :=
        ContinuousLinearMap.integral_comp_comm
          (L := (innerSL ℝ) v) hR_int
      calc
        ∫ j, G q j ∂sourceIndexLaw s.n0 =
            ∫ j, ((innerSL ℝ) v) (R j) ∂sourceIndexLaw s.n0 := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro j
              change inner ℝ (R j) v = inner ℝ v (R j)
              exact real_inner_comm _ _
        _ = ((innerSL ℝ) v) (∫ j, R j ∂sourceIndexLaw s.n0) := hlin
        _ = 0 := by simp [hR_zero]
    simpa [s, X, Z', G, eps, componentGradient] using
      corrected_fresh_scalar_integral_eq_zero
        D epsilon n0 k X hX_meas r G hG_meas hsample_int hindep hcenter
  have hprev_increment_cross :
      (MeasureTheory.integral μ
          (fun path => inner ℝ (deltaPrev path) (inc path))) = 0 := by
    let window : SourcePath s → Fin k → SourceBatch s :=
      SOptLib.sampleWindow (fun j path => path j) 1 k
    have hwindow_range : (Set.range window).Finite := by
      exact Set.Finite.subset Set.finite_univ (by
        intro z hz
        exact Set.mem_univ z)
    let Q : SourcePath s →
        (VariableSpace d × VariableSpace d) × VariableSpace d :=
      fun path => (Z path, deltaPrev path)
    have hQconst :
        ∀ ⦃path path' : SourcePath s⦄,
          window path = window path' → Q path = Q path' := by
      intro path path' hwindow
      exact Prod.ext (hZ_const hwindow) (hdeltaPrev_const hwindow)
    have hQ_range : (Set.range Q).Finite := by
      exact Set.Finite.range_of_finite_range_fiber_const
        hwindow_range hQconst
    let W := {z : ((VariableSpace d × VariableSpace d) × VariableSpace d) //
      z ∈ Set.range Q}
    letI : Fintype W := hQ_range.fintype
    let Q' : SourcePath s → W := fun path =>
      ⟨Q path, ⟨path, rfl⟩⟩
    have hQ'const :
        ∀ ⦃path path' : SourcePath s⦄,
          window path = window path' → Q' path = Q' path' := by
      intro path path' hwindow
      apply Subtype.ext
      exact hQconst hwindow
    have hwindow_meas : Measurable window := by
      refine measurable_pi_lambda _ ?_
      intro q
      exact measurable_pi_apply (1 + q.1)
    have hQ'_meas : Measurable Q' :=
      measurable_of_finite_range_fiber_const
        hwindow_meas hwindow_range hQ'const
    have hcross_one :
        ∀ r : Fin b,
          MeasureTheory.integral μ
              (fun path => inner ℝ (deltaPrev path) (eps r path)) = 0 := by
      intro r
      let G : W → Fin n → ℝ := fun z j =>
        inner ℝ z.1.2
          (componentGradient D.componentObjective j z.1.1.1 -
            componentGradient D.componentObjective j z.1.1.2 -
            (fullGradient D z.1.1.1 - fullGradient D z.1.1.2))
      have hG_meas : Measurable (fun p : W × Fin n => G p.1 p.2) :=
        measurable_of_finite _
      have hsample_int :
          Integrable
            (fun path : SourcePath s => G (Q' path) (path (k + 1) r)) μ := by
        simpa [G, Q', Q, eps] using
          (integrable_inner_of_integrable_sq_norm
            hprev_meas (heps_meas r) hprev_sq (heps_sq r))
      have hindep :
          ProbabilityTheory.IndepFun Q'
            (fun path : SourcePath s => path (k + 1) r) μ :=
        (corrected_prefix_key_current_indep
          D epsilon n0 k Q' hQ'const r).1
      have hcenter : ∀ z : W, ∫ j, G z j ∂sourceIndexLaw s.n0 = 0 := by
        intro z
        have hn_ne : (n : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (n_pos n0))
        let R : Fin n → VariableSpace d := fun j =>
          componentGradient D.componentObjective j z.1.1.1 -
            componentGradient D.componentObjective j z.1.1.2 -
            (fullGradient D z.1.1.1 - fullGradient D z.1.1.2)
        have hR_int :
            Integrable R (sourceIndexLaw s.n0) := by
          letI : IsProbabilityMeasure (sourceIndexLaw s.n0) :=
            sourceIndexLaw_isProbability s.n0
          exact integrable_of_finite_range
            (measurable_of_finite R).aestronglyMeasurable (Set.finite_range R)
        have hR_zero : (∫ j, R j ∂sourceIndexLaw s.n0) = 0 := by
          rw [sourceIndexLaw_integral_eq_finiteUniformAverage]
          simp [R, SOptLib.finiteUniformAverage, fullGradient, componentGradient,
            Finset.smul_sum, smul_sub, Finset.sum_sub_distrib,
            ← Nat.cast_smul_eq_nsmul ℝ, hn_ne] <;>
            field_simp [hn_ne] <;> module
        have hlin :=
          ContinuousLinearMap.integral_comp_comm
            (L := (innerSL ℝ) z.1.2) hR_int
        calc
          ∫ j, G z j ∂sourceIndexLaw s.n0 =
              ∫ j, ((innerSL ℝ) z.1.2) (R j) ∂sourceIndexLaw s.n0 := by
                rfl
          _ = ((innerSL ℝ) z.1.2)
              (∫ j, R j ∂sourceIndexLaw s.n0) := hlin
          _ = 0 := by simp [hR_zero]
      exact
        corrected_fresh_scalar_integral_eq_zero
          D epsilon n0 k Q' hQ'_meas r G hG_meas hsample_int hindep hcenter
    rw [hinc_eq]
    exact
      pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
        μ (Finset.univ : Finset (Fin b)) b deltaPrev eps
        hprev_meas
        (by
          intro i hi
          exact heps_meas i)
        hprev_sq
        (by
          intro i hi
          exact (heps_sq i))
        (by
          intro i hi
          exact hcross_one i)
  exact
    recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch
      μ (Finset.univ : Finset (Fin b)) b deltaPrev deltaNext inc eps
      xPrev xCurr D.L
      hbpos (by simp) hprev_meas
      (by
        intro i hi
        exact heps_meas i)
      hprev_sq
      (by
        intro i hi
        exact hdiag i)
      hinc_eq hrec
      (by
          intro i hi j hj hne
          exact hcross i hi j hj hne)
      hprev_increment_cross

private theorem corrected_fullGradient_lipschitz
    {n d : ℕ} (D : SourceData n d)
    (n0 : N0 n) (hL : 0 < D.L) :
    ∀ x y : VariableSpace d,
      ‖fullGradient D x - fullGradient D y‖ ≤
        D.L * ‖x - y‖ := by
  intro x y
  let f : Fin n → VariableSpace d :=
    fun i =>
      componentGradient D.componentObjective i x -
        componentGradient D.componentObjective i y
  have hnpos : 0 < Fintype.card (Fin n) := by
    simpa using n_pos n0
  have hsq :
      ‖fullGradient D x - fullGradient D y‖ ^ 2 ≤
        D.L ^ 2 * ‖x - y‖ ^ 2 := by
    calc
      ‖fullGradient D x - fullGradient D y‖ ^ 2
          ≤ (Fintype.card (Fin n) : ℝ)⁻¹ *
              ∑ i : Fin n, ‖f i‖ ^ 2 := by
            simpa [fullGradient, f, SOptLib.finiteUniformAverage,
              Finset.smul_sum, Finset.sum_sub_distrib, smul_sub] using
              (norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq
                (s := (Finset.univ : Finset (Fin n))) f hnpos)
      _ ≤ D.L ^ 2 * ‖x - y‖ ^ 2 := by
        simpa [f, SOptLib.finiteUniformAverage] using
          D.averagedLipschitzGradient x y
  have hright_nonneg : 0 ≤ D.L * ‖x - y‖ :=
    mul_nonneg (le_of_lt hL) (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp (by
    simpa [mul_pow] using hsq)

set_option maxHeartbeats 800000 in
private theorem corrected_one_step_descent_B8_pathwise
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) (k : ℕ)
    (path : SourcePath (schedule epsilon D.L n0)) :
    objective D (correctedIterate D (schedule epsilon D.L n0) (k + 1) path) ≤
      objective D (correctedIterate D (schedule epsilon D.L n0) k path) -
        epsilon *
            ‖correctedEstimator D (schedule epsilon D.L n0) k path‖ /
              (4 * D.L * n0.1) +
        epsilon ^ 2 / (2 * n0.1 * D.L) +
        (1 / (4 * D.L * n0.1)) *
          ‖correctedEstimator D (schedule epsilon D.L n0) k path -
            fullGradient D
              (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2 := by
  rcases hScalar with ⟨hepsilon, hL⟩
  let s := schedule epsilon D.L n0
  let x := correctedIterate D s k path
  let v := correctedEstimator D s k path
  let eta : ℝ := optionIIStepSize epsilon D.L n0.1 v
  let y : VariableSpace d := liveCorrectedOptionIIUpdate s x v
  have hn0_pos : 0 < n0.1 := n0_pos n0
  have hH_pos : 0 < D.L * n0.1 := mul_pos hL hn0_pos
  have htwoH_pos : 0 < 2 * D.L * n0.1 := by nlinarith [hH_pos]
  have heta_nonneg : 0 ≤ eta := by
    dsimp [eta, optionIIStepSize]
    exact le_min
      (mul_nonneg (le_of_lt hepsilon)
        (inv_nonneg.mpr (mul_nonneg (le_of_lt hH_pos) (norm_nonneg v))))
      (inv_nonneg.mpr (le_of_lt htwoH_pos))
  have heta_le_twoH : eta ≤ (2 * D.L * n0.1)⁻¹ := by
    dsimp [eta, optionIIStepSize]
    exact min_le_right _ _
  have hdenL_pos : 0 < 2 * D.L := by nlinarith [hL]
  have hinv_le : (2 * D.L * n0.1)⁻¹ ≤ (2 * D.L)⁻¹ := by
    field_simp [hdenL_pos.ne', htwoH_pos.ne']
    nlinarith [n0.2.1, hL]
  have heta_le_twoL : eta ≤ (2 * D.L)⁻¹ :=
    le_trans heta_le_twoH hinv_le
  have hLeta_le : D.L * eta ≤ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left heta_le_twoL (le_of_lt hL)
    field_simp [hL.ne'] at hmul
    linarith
  have hgrad_lipschitz :
      ∀ z w : VariableSpace d,
        ‖fullGradient D w - fullGradient D z‖ ≤
          D.L * ‖w - z‖ :=
    by
      intro z w
      exact corrected_fullGradient_lipschitz D n0 hL w z
  have hsmooth :
      objective D y ≤ objective D x +
        inner ℝ (fullGradient D x) (y - x) +
        (D.L / 2) * ‖y - x‖ ^ 2 := by
    have h :=
      smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
        (Set.univ : Set (VariableSpace d)) (objective D) (fullGradient D) D.L
        convex_univ
        (by
          intro z _hz
          exact objective_hasGradientAt_fullGradient D z)
        (by
          intro z _hz w _hw
          simpa using hgrad_lipschitz w z)
        (Set.mem_univ x) (Set.mem_univ y)
    simpa using h
  have hlive :
      liveCorrectedOptionIIUpdate s x v =
        optionIIUpdate epsilon D.L n0.1 x v := by
    by_cases hv : 0 < ‖v‖
    · unfold liveCorrectedOptionIIUpdate
      simp [optionIIUpdate, optionIIStepSize, s, schedule,
        FiniteSumTheorem2ImplementationInternal.schedule, hv] <;>
        congr 2 <;> ring
    · have hv0 : ‖v‖ = 0 := by
        exact le_antisymm (not_lt.mp hv) (norm_nonneg _)
      have hvv : v = 0 := norm_eq_zero.mp hv0
      unfold liveCorrectedOptionIIUpdate
      simp only [hv]
      simp [optionIIUpdate, optionIIStepSize, s, schedule,
        FiniteSumTheorem2ImplementationInternal.schedule, hv0, hvv]
  have hy_sub : y - x = -eta • v := by
    rw [show y = optionIIUpdate epsilon D.L n0.1 x v by
      simpa [y] using hlive]
    simp [eta, optionIIUpdate, optionIIStepSize, sub_eq_add_neg,
      neg_smul]
  have hmodel :
      objective D y ≤ objective D x - eta * inner ℝ (fullGradient D x) v +
        (D.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) := by
    calc
      objective D y ≤ objective D x +
          inner ℝ (fullGradient D x) (y - x) +
          (D.L / 2) * ‖y - x‖ ^ 2 := hsmooth
      _ = objective D x - eta * inner ℝ (fullGradient D x) v +
          (D.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) := by
            rw [hy_sub]
            simp [inner_smul_right, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg heta_nonneg]
            ring
  let err : VariableSpace d := v - fullGradient D x
  have hinner_decomp :
      inner ℝ (fullGradient D x) v =
        ‖v‖ ^ 2 - inner ℝ err v := by
    have hg : fullGradient D x = v - err := by simp [err]
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
      objective D y ≤ objective D x - eta / 4 * ‖v‖ ^ 2 +
        eta / 2 * ‖err‖ ^ 2 := by
    have hsq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hmodel_err :
        objective D y ≤ objective D x - eta * ‖v‖ ^ 2 +
          eta * inner ℝ err v +
          (D.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) := by
      nlinarith [hmodel, hinner_decomp]
    have hpre1 :
        objective D y ≤ objective D x - eta / 2 * ‖v‖ ^ 2 +
          (D.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) +
          eta / 2 * ‖err‖ ^ 2 := by
      nlinarith [hmodel_err, hyoung1]
    have hcoeff_quad : (D.L / 2) * eta ^ 2 ≤ eta / 4 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hLeta_le (show 0 ≤ eta / 2 by positivity)
      nlinarith [hmul]
    have hquad_scaled :
        (D.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) ≤
          eta / 4 * ‖v‖ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoeff_quad hsq
      nlinarith [hmul]
    nlinarith [hpre1, hquad_scaled]
  have hmin_raw :=
    optionII_min_stepsize_norm_sq_lower
      (epsilon := epsilon) (H := D.L * n0.1) (a := ‖v‖)
      hepsilon hH_pos (norm_nonneg v)
  have hmin_eta :
      eta * ‖v‖ ^ 2 ≥
        epsilon * ‖v‖ * (D.L * n0.1)⁻¹ -
          2 * epsilon ^ 2 * (D.L * n0.1)⁻¹ := by
    simpa [eta, optionIIStepSize, mul_assoc] using hmin_raw
  have hdescent_inv :
      -eta / 4 * ‖v‖ ^ 2 ≤
        -(1 / 4) *
          (epsilon * ‖v‖ * (D.L * n0.1)⁻¹ -
            2 * epsilon ^ 2 * (D.L * n0.1)⁻¹) := by
    have hmul :=
      mul_le_mul_of_nonpos_left hmin_eta (show (-(1 / 4) : ℝ) ≤ 0 by norm_num)
    calc
      -eta / 4 * ‖v‖ ^ 2 =
          -(1 / 4) * (eta * ‖v‖ ^ 2) := by ring
      _ ≤
          -(1 / 4) *
            (epsilon * ‖v‖ * (D.L * n0.1)⁻¹ -
              2 * epsilon ^ 2 * (D.L * n0.1)⁻¹) := hmul
  have hdescent_eq :
      -(1 / 4) *
          (epsilon * ‖v‖ * (D.L * n0.1)⁻¹ -
            2 * epsilon ^ 2 * (D.L * n0.1)⁻¹) =
        -epsilon * ‖v‖ / (4 * D.L * n0.1) +
          epsilon ^ 2 / (2 * n0.1 * D.L) := by
    field_simp [hL.ne', hn0_pos.ne']
    ring
  have hdescent_term :
      -eta / 4 * ‖v‖ ^ 2 ≤
        -epsilon * ‖v‖ / (4 * D.L * n0.1) +
          epsilon ^ 2 / (2 * n0.1 * D.L) :=
    hdescent_inv.trans_eq hdescent_eq
  have herr_coeff :
      eta / 2 * ‖err‖ ^ 2 ≤
        (1 / (4 * D.L * n0.1)) * ‖err‖ ^ 2 := by
    have hcoeff0 : eta / 2 ≤ (2 * D.L * n0.1)⁻¹ / 2 := by
      exact div_le_div_of_nonneg_right heta_le_twoH
        (by norm_num : (0 : ℝ) ≤ 2)
    have hcoeff_eq :
        (2 * D.L * n0.1)⁻¹ / 2 =
          (1 / (4 * D.L * n0.1) : ℝ) := by
      field_simp [hL.ne', hn0_pos.ne']
      ring
    have hcoeff : eta / 2 ≤ (1 / (4 * D.L * n0.1) : ℝ) :=
      hcoeff0.trans_eq hcoeff_eq
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  have hsum_terms :
      -eta / 4 * ‖v‖ ^ 2 + eta / 2 * ‖err‖ ^ 2 ≤
        (-epsilon * ‖v‖ / (4 * D.L * n0.1) +
          epsilon ^ 2 / (2 * n0.1 * D.L)) +
          (1 / (4 * D.L * n0.1)) * ‖err‖ ^ 2 :=
    add_le_add hdescent_term herr_coeff
  have hfinal :
      objective D y ≤ objective D x -
        epsilon * ‖v‖ / (4 * D.L * n0.1) +
        epsilon ^ 2 / (2 * n0.1 * D.L) +
        (1 / (4 * D.L * n0.1)) * ‖err‖ ^ 2 := by
    calc
      objective D y
          ≤ objective D x +
              (-eta / 4 * ‖v‖ ^ 2 + eta / 2 * ‖err‖ ^ 2) :=
            hpre.trans_eq (by ring)
      _ ≤ objective D x +
          ((-epsilon * ‖v‖ / (4 * D.L * n0.1) +
            epsilon ^ 2 / (2 * n0.1 * D.L)) +
            (1 / (4 * D.L * n0.1)) * ‖err‖ ^ 2) :=
            add_le_add_right hsum_terms (objective D x)
      _ = objective D x -
          epsilon * ‖v‖ / (4 * D.L * n0.1) +
          epsilon ^ 2 / (2 * n0.1 * D.L) +
          (1 / (4 * D.L * n0.1)) * ‖err‖ ^ 2 := by
            ring
  have hsucc :
      correctedIterate D s (k + 1) path = y := by
    change liveCorrectedOptionIIUpdate s x v = y
    rfl
  simpa [s, x, v, y, err, hsucc] using hfinal

private theorem corrected_step_sq_integral_le
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) (k : ℕ) :
    (∫ path,
        ‖correctedIterate D (schedule epsilon D.L n0) (k + 1) path -
          correctedIterate D (schedule epsilon D.L n0) k path‖ ^ 2 ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) ≤
      (epsilon / (D.L * n0.1)) ^ 2 := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  letI : IsProbabilityMeasure μ :=
    withReplacementSourceLaw_isProbability s
  have hleft :
      Integrable
        (fun path =>
          ‖correctedIterate D s (k + 1) path -
            correctedIterate D s k path‖ ^ 2) μ :=
    corrected_step_sq_integrable D epsilon n0 k
  have hright :
      Integrable (fun _ : SourcePath s =>
        (epsilon / (D.L * n0.1)) ^ 2) μ := by
    exact integrable_const _
  have hpoint :
      ∀ path : SourcePath s,
        ‖correctedIterate D s (k + 1) path -
            correctedIterate D s k path‖ ^ 2 ≤
          (epsilon / (D.L * n0.1)) ^ 2 := by
    intro path
    have hstep := corrected_step_bound D epsilon n0 hScalar k path
    rcases hScalar with ⟨hepsilon, hL⟩
    have hnonneg :
        0 ≤ epsilon / (D.L * n0.1) :=
      le_of_lt (div_pos hepsilon (mul_pos hL (n0_pos n0)))
    exact (sq_le_sq₀ (norm_nonneg _) hnonneg).2 hstep
  simpa [s, μ] using integral_mono hleft hright hpoint

private theorem corrected_residual_mse_mod_bound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) :
    ∀ k : ℕ,
      Integrable
        (fun path =>
          ‖correctedEstimator D (schedule epsilon D.L n0) k path -
            fullGradient D
              (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2)
        (withReplacementSourceLaw (schedule epsilon D.L n0)) ∧
      (∫ path,
        ‖correctedEstimator D (schedule epsilon D.L n0) k path -
          fullGradient D
            (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2 ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) ≤
        ((k % roundedRefreshPeriod (schedule epsilon D.L n0) : ℕ) : ℝ) *
          (D.L ^ 2 /
            (sourceBatchCount (schedule epsilon D.L n0) : ℝ)) *
          (epsilon / (D.L * n0.1)) ^ 2 := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let R := roundedRefreshPeriod s
  let c : ℝ := D.L ^ 2 / (sourceBatchCount s : ℝ)
  let u : ℝ := (epsilon / (D.L * n0.1)) ^ 2
  have hRpos : 0 < R := by
    simpa [R] using roundedRefreshPeriod_pos s
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (sq_nonneg _) (by
      exact_mod_cast (Nat.zero_le (sourceBatchCount s)))
  have hu : 0 ≤ u := by
    dsimp [u]
    exact sq_nonneg _
  intro k
  induction k with
  | zero =>
      have hz := corrected_residual_zero_of_refresh D epsilon n0 0
        (by simpa [s, R] using roundedRefreshAt_zero s)
      refine ⟨corrected_residual_sq_integrable D epsilon n0 0, ?_⟩
      have hz' :
          (fun path : SourcePath s =>
              ‖correctedEstimator D s 0 path -
                fullGradient D (correctedIterate D s 0 path)‖ ^ 2) =
            (fun _ => 0) := by
        funext path
        have hz_path := hz path
        simpa [s] using congrArg norm hz_path
      rw [hz']
      change (∫ x : SourcePath s, (0 : ℝ) ∂μ) ≤
        ((0 % R : ℕ) : ℝ) * c * u
      simp
  | succ k ih =>
      by_cases hrefresh : roundedRefreshAt s (k + 1)
      · have hz := corrected_residual_zero_of_refresh D epsilon n0 (k + 1)
          (by simpa [s] using hrefresh)
        refine ⟨corrected_residual_sq_integrable D epsilon n0 (k + 1), ?_⟩
        have hz' :
            (fun path : SourcePath s =>
                ‖correctedEstimator D s (k + 1) path -
                  fullGradient D (correctedIterate D s (k + 1) path)‖ ^ 2) =
            (fun _ => 0) := by
          funext path
          have hz_path := hz path
          simpa [s] using congrArg norm hz_path
        rw [hz']
        have hzero : (k + 1) % R = 0 := by
          simpa [roundedRefreshAt, R] using hrefresh
        rw [integral_zero]
        have hzero' :
            (((k + 1) % roundedRefreshPeriod
              (schedule epsilon D.L n0) : ℕ) : ℝ) = 0 := by
          exact_mod_cast (by simpa [R] using hzero)
        rw [hzero']
        norm_num
      · have hstep := corrected_nonrefresh_residual_second_moment_step
          D epsilon n0 hScalar k (by simpa [s] using hrefresh)
        have hstep_int := corrected_step_sq_integral_le
          D epsilon n0 hScalar k
        have hmod_formula : (k + 1) % R = (k % R + 1) % R := by
          simpa [Nat.add_comm] using Nat.add_mod k 1 R
        have hmod_lt : k % R < R := Nat.mod_lt _ hRpos
        have hmod_ne : (k + 1) % R ≠ 0 := by
          intro hzero
          apply hrefresh
          simpa [roundedRefreshAt, R] using hzero
        have hsum_lt : k % R + 1 < R := by
          by_contra hnot
          have heq : k % R + 1 = R := by omega
          apply hmod_ne
          rw [hmod_formula, heq]
          exact Nat.mod_self R
        have hmod : (k + 1) % R = k % R + 1 := by
          rw [hmod_formula, Nat.mod_eq_of_lt hsum_lt]
        refine ⟨corrected_residual_sq_integrable D epsilon n0 (k + 1), ?_⟩
        have hrec' :
            (∫ path,
                ‖correctedEstimator D s (k + 1) path -
                  fullGradient D (correctedIterate D s (k + 1) path)‖ ^ 2 ∂μ) ≤
              (∫ path,
                ‖correctedEstimator D s k path -
                  fullGradient D (correctedIterate D s k path)‖ ^ 2 ∂μ) +
                c *
                  (∫ path,
                    ‖correctedIterate D s (k + 1) path -
                      correctedIterate D s k path‖ ^ 2 ∂μ) := by
          simpa [s, μ, c] using hstep
        have hprev' :
            (∫ path,
                ‖correctedEstimator D s k path -
                  fullGradient D (correctedIterate D s k path)‖ ^ 2 ∂μ) ≤
              ((k % R : ℕ) : ℝ) * c * u := by
          simpa [s, μ, R, c, u] using ih.2
        have hstep' :
            (∫ path,
                ‖correctedIterate D s (k + 1) path -
                  correctedIterate D s k path‖ ^ 2 ∂μ) ≤ u := by
          simpa [s, μ, u] using hstep_int
        calc
          (∫ path,
              ‖correctedEstimator D s (k + 1) path -
                fullGradient D (correctedIterate D s (k + 1) path)‖ ^ 2 ∂μ)
              ≤
            (∫ path,
              ‖correctedEstimator D s k path -
                fullGradient D (correctedIterate D s k path)‖ ^ 2 ∂μ) +
              c *
                (∫ path,
                  ‖correctedIterate D s (k + 1) path -
                    correctedIterate D s k path‖ ^ 2 ∂μ) := hrec'
          _ ≤
            ((k % R : ℕ) : ℝ) *
                c * u + c * u := by
              have hmul_step := mul_le_mul_of_nonneg_left hstep' hc
              have hmul_prev :=
                add_le_add_right hprev'
                  (c * (∫ path,
                    ‖correctedIterate D s (k + 1) path -
                      correctedIterate D s k path‖ ^ 2 ∂μ))
              linarith
          _ =
            ((k % R + 1 : ℕ) : ℝ) *
                c * u := by
              push_cast
              ring
          _ =
            (((k + 1) % R : ℕ) : ℝ) *
                c * u := by
              rw [hmod]

private theorem correctedFiniteSumB17B18EstimatorMSEAdapter
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) :
    ∀ k : ℕ,
      Integrable
        (fun path =>
          ‖correctedEstimator D (schedule epsilon D.L n0) k path -
            fullGradient D
              (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2)
        (withReplacementSourceLaw (schedule epsilon D.L n0)) ∧
      (∫ path,
        ‖correctedEstimator D (schedule epsilon D.L n0) k path -
          fullGradient D
            (correctedIterate D (schedule epsilon D.L n0) k path)‖ ^ 2 ∂
          (withReplacementSourceLaw (schedule epsilon D.L n0))) ≤
        epsilon ^ 2 := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let R := roundedRefreshPeriod s
  let c : ℝ := D.L ^ 2 / (sourceBatchCount s : ℝ)
  let u : ℝ := (epsilon / (D.L * n0.1)) ^ 2
  have hbudget :
      (R - 1 : ℝ) * c * u ≤ epsilon ^ 2 := by
    simpa [s, R, c, u] using
      corrected_rounded_epoch_budget D epsilon n0 hScalar
  have hRpos : 0 < R := by
    simpa [R] using roundedRefreshPeriod_pos s
  have hcu_nonneg : 0 ≤ c * u := by
    exact mul_nonneg
      (div_nonneg (sq_nonneg D.L) (by
        exact_mod_cast (Nat.zero_le (sourceBatchCount s))))
      (sq_nonneg _)
  have hu : 0 ≤ u := by
    exact sq_nonneg _
  intro k
  have hmod := corrected_residual_mse_mod_bound D epsilon n0 hScalar k
  have hmod_nat : k % R ≤ R - 1 := by
    have hlt : k % R < R := Nat.mod_lt _ hRpos
    omega
  have hmod_real_nat :
      ((k % R : ℕ) : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := by
    exact_mod_cast hmod_nat
  have hmod_real : ((k % R : ℕ) : ℝ) ≤ (R - 1 : ℝ) := by
    calc
      ((k % R : ℕ) : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := hmod_real_nat
      _ = (R - 1 : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  refine ⟨hmod.1, ?_⟩
  have hscale :
      ((k % R : ℕ) : ℝ) * c * u ≤ (R - 1 : ℝ) * c * u := by
    have hc_scale :
        ((k % R : ℕ) : ℝ) * c ≤ (R - 1 : ℝ) * c :=
      mul_le_mul_of_nonneg_right hmod_real
        (by
          exact div_nonneg (sq_nonneg D.L) (by
            exact_mod_cast (Nat.zero_le (sourceBatchCount s))))
    have hcu_scale := mul_le_mul_of_nonneg_right hc_scale hu
    simpa [mul_assoc] using hcu_scale
  have hbound :
      (∫ path,
        ‖correctedEstimator D s k path -
          fullGradient D (correctedIterate D s k path)‖ ^ 2 ∂μ) ≤
        (R - 1 : ℝ) * c * u :=
    (by
      calc
        (∫ path,
          ‖correctedEstimator D s k path -
            fullGradient D (correctedIterate D s k path)‖ ^ 2 ∂μ)
            ≤ ((k % R : ℕ) : ℝ) * c * u := by
              simpa [s, μ, R, c, u] using hmod.2
        _ ≤ (R - 1 : ℝ) * c * u := hscale)
  exact hbound.trans hbudget

private theorem correctedRunObjective_integrable
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) (k : ℕ) :
    Integrable
      (fun path =>
        objective D (correctedIterate D (schedule epsilon D.L n0) k path))
      (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  let s := schedule epsilon D.L n0
  letI : IsProbabilityMeasure (withReplacementSourceLaw s) :=
    withReplacementSourceLaw_isProbability s
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  apply integrable_of_finiteSampleWindow_factor_aestrongly xi 1 k
  · intro j
    exact measurable_pi_apply j
  · intro path path' hwindow
    have hprefix :
        SOptLib.sampleWindow xi 1 k path =
            SOptLib.sampleWindow xi 1 k path' := by
      simpa [SOptLib.sampleWindow] using hwindow
    exact congrArg
      (fun state : State (VariableSpace d) => objective D state.x)
      (corrected_state_prefix_eq D epsilon n0 k path path' hprefix)

private theorem correctedRunEstimator_integrable
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0) (k : ℕ) :
    Integrable
      (fun path =>
        correctedEstimator D (schedule epsilon D.L n0) k path)
      (withReplacementSourceLaw (schedule epsilon D.L n0)) := by
  let s := schedule epsilon D.L n0
  letI : IsProbabilityMeasure (withReplacementSourceLaw s) :=
    withReplacementSourceLaw_isProbability s
  let xi : ℕ → SourcePath s → SourceBatch s := fun j path => path j
  apply integrable_of_finiteSampleWindow_factor_aestrongly xi 1 k
  · intro j
    exact measurable_pi_apply j
  · intro path path' hwindow
    have hprefix :
        SOptLib.sampleWindow xi 1 k path =
            SOptLib.sampleWindow xi 1 k path' := by
      simpa [SOptLib.sampleWindow] using hwindow
    exact congrArg
      (fun state : State (VariableSpace d) => state.v)
      (corrected_state_prefix_eq D epsilon n0 k path path' hprefix)

set_option maxHeartbeats 800000 in
private theorem correctedB13DescentAdapter
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    (iterationBudget D epsilon n0 : ℝ)⁻¹ *
        Finset.sum (Finset.range (iterationBudget D epsilon n0))
          (fun k =>
            ∫ path,
              ‖correctedEstimator D (schedule epsilon D.L n0) k path‖ ∂
                (withReplacementSourceLaw (schedule epsilon D.L n0))) ≤
      4 * epsilon := by
  rcases hScalar with ⟨hepsilon, hL⟩
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let K := iterationBudget D epsilon n0
  letI : IsProbabilityMeasure μ := withReplacementSourceLaw_isProbability s
  have hK_pos : 0 < K := by
    dsimp [K, iterationBudget]
    exact Nat.succ_pos _
  have hDelta : 0 ≤ Delta D :=
    Delta_nonneg_of_finiteInitialGapBoundary D hGap
  have hmse_all :
      ∀ k,
        Integrable
            (fun path =>
              ‖correctedEstimator D s k path -
                fullGradient D (correctedIterate D s k path)‖ ^ 2) μ ∧
          (∫ path,
            ‖correctedEstimator D s k path -
              fullGradient D (correctedIterate D s k path)‖ ^ 2 ∂μ) ≤
            epsilon ^ 2 := by
    intro k
    simpa [s, μ] using
      correctedFiniteSumB17B18EstimatorMSEAdapter D epsilon n0
        ⟨hepsilon, hL⟩ k
  have hobj_int :
      ∀ k, Integrable
        (fun path => objective D (correctedIterate D s k path)) μ := by
    intro k
    simpa [s, μ] using
      correctedRunObjective_integrable D epsilon n0 ⟨hepsilon, hL⟩ k
  have hdrop_int :
      ∀ k, Integrable
        (fun path =>
          objective D (correctedIterate D s k path) -
            objective D (correctedIterate D s (k + 1) path)) μ := by
    intro k
    exact (hobj_int k).sub (hobj_int (k + 1))
  have hest_norm_int :
      ∀ k ∈ Finset.range K,
        Integrable
          (fun path =>
            ‖correctedEstimator D s k path‖) μ := by
    intro k hk
    have hmse := hmse_all k
    have herr_nonneg :
        ∀ᵐ path ∂μ,
          0 ≤ ‖correctedEstimator D s k path -
            fullGradient D (correctedIterate D s k path)‖ :=
      Filter.Eventually.of_forall (fun path => norm_nonneg _)
    have herr_norm_int :
        Integrable
          (fun path =>
            ‖correctedEstimator D s k path -
              fullGradient D (correctedIterate D s k path)‖) μ :=
      (integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
        (C := epsilon ^ 2) hmse.1 herr_nonneg hmse.2).1
    have htarget_int :
        Integrable
          (fun path => ‖fullGradient D (correctedIterate D s k path)‖) μ := by
      simpa [s, μ] using
        correctedRunGradientNorm_integrable D epsilon n0
          ⟨hepsilon, hL⟩ k
    have hest_int :
        Integrable (fun path => correctedEstimator D s k path) μ := by
      simpa [s, μ] using
        correctedRunEstimator_integrable D epsilon n0
          ⟨hepsilon, hL⟩ k
    exact hest_int.norm
  have hB9 :
      ∀ k ∈ Finset.range K,
        (epsilon / (4 * D.L * n0.1)) *
            ∫ path, ‖correctedEstimator D s k path‖ ∂μ ≤
          ∫ path,
              objective D (correctedIterate D s k path) -
                objective D (correctedIterate D s (k + 1) path) ∂μ +
            3 * epsilon ^ 2 / (4 * D.L * n0.1) := by
    intro k hk
    let gap : SourcePath s → ℝ :=
      fun path => ‖correctedEstimator D s k path‖
    let drop : SourcePath s → ℝ :=
      fun path =>
        objective D (correctedIterate D s k path) -
          objective D (correctedIterate D s (k + 1) path)
    let deltaSq : SourcePath s → ℝ :=
      fun path =>
        ‖correctedEstimator D s k path -
          fullGradient D (correctedIterate D s k path)‖ ^ 2
    let alpha : ℝ := epsilon / (4 * D.L * n0.1)
    let cDelta : ℝ := 1 / (4 * D.L * n0.1)
    let c0 : ℝ := epsilon ^ 2 / (2 * n0.1 * D.L)
    have hpoint :
        ∀ path, alpha * gap path ≤
          drop path + cDelta * deltaSq path + c0 := by
      intro path
      have hraw := corrected_one_step_descent_B8_pathwise
        D epsilon n0 ⟨hepsilon, hL⟩ k path
      have hraw' :
          objective D (correctedIterate D s (k + 1) path) ≤
            objective D (correctedIterate D s k path) -
              epsilon * ‖correctedEstimator D s k path‖ /
                (4 * D.L * n0.1) +
              epsilon ^ 2 / (2 * n0.1 * D.L) +
              (1 / (4 * D.L * n0.1)) *
                ‖correctedEstimator D s k path -
                  fullGradient D (correctedIterate D s k path)‖ ^ 2 := by
        simpa [s] using hraw
      simp only [alpha, gap, drop, deltaSq, cDelta, c0]
      have hraw'' :
          epsilon * ‖correctedEstimator D s k path‖ /
                (4 * D.L * n0.1) ≤
            objective D (correctedIterate D s k path) -
              objective D (correctedIterate D s (k + 1) path) +
              epsilon ^ 2 / (2 * n0.1 * D.L) +
              (1 / (4 * D.L * n0.1)) *
                ‖correctedEstimator D s k path -
                  fullGradient D (correctedIterate D s k path)‖ ^ 2 := by
        linarith [hraw']
      convert hraw'' using 1 <;> ring
    have hbase :
        alpha * ∫ path, gap path ∂μ ≤
          ∫ path, drop path ∂μ +
            cDelta * ∫ path, deltaSq path ∂μ + c0 :=
      integral_one_step_gap_bound_of_pointwise
        μ gap drop deltaSq alpha cDelta c0
        (by simpa [gap] using hest_norm_int k hk)
        (by simpa [drop] using hdrop_int k)
        (by simpa [deltaSq] using (hmse_all k).1)
        hpoint
    have hcDelta_nonneg : 0 ≤ cDelta := by
      dsimp [cDelta]
      have hden : 0 < 4 * D.L * n0.1 :=
        mul_pos (mul_pos (by norm_num) hL) (n0_pos n0)
      exact le_of_lt (one_div_pos.mpr hden)
    have hdelta_scaled :
        cDelta * ∫ path, deltaSq path ∂μ ≤ cDelta * epsilon ^ 2 :=
      mul_le_mul_of_nonneg_left
        (by simpa [deltaSq] using (hmse_all k).2)
        hcDelta_nonneg
    have hconst :
        cDelta * epsilon ^ 2 + c0 =
          3 * epsilon ^ 2 / (4 * D.L * n0.1) := by
      dsimp [cDelta, c0]
      field_simp [hL.ne', (n0_pos n0).ne']
      ring
    calc
      (epsilon / (4 * D.L * n0.1)) *
          ∫ path, ‖correctedEstimator D s k path‖ ∂μ =
        alpha * ∫ path, gap path ∂μ := by rfl
      _ ≤ ∫ path, drop path ∂μ +
            cDelta * ∫ path, deltaSq path ∂μ + c0 := hbase
      _ ≤ ∫ path, drop path ∂μ +
            cDelta * epsilon ^ 2 + c0 := by
        have htmp :
            (∫ path, drop path ∂μ) +
                cDelta * ∫ path, deltaSq path ∂μ ≤
              (∫ path, drop path ∂μ) + cDelta * epsilon ^ 2 :=
          add_le_add_right hdelta_scaled _
        have htmp' := add_le_add_right htmp c0
        simpa [add_comm, add_left_comm, add_assoc] using htmp'
      _ = (∫ path, drop path ∂μ) +
            (cDelta * epsilon ^ 2 + c0) := by
        ring
      _ = ∫ path,
              objective D (correctedIterate D s k path) -
                objective D (correctedIterate D s (k + 1) path) ∂μ +
            3 * epsilon ^ 2 / (4 * D.L * n0.1) := by
        rw [hconst]
  have hdrop_sum_le :
      Finset.sum (Finset.range K)
          (fun k =>
            ∫ path,
              objective D (correctedIterate D s k path) -
                objective D (correctedIterate D s (k + 1) path) ∂μ) ≤
        Delta D := by
    exact
      (integral_sum_telescope_bound_of_pointwise_lower_bound
        (times := Finset.range K)
        (drop := fun k path =>
          objective D (correctedIterate D s k path) -
            objective D (correctedIterate D s (k + 1) path))
        (terminal := fun path =>
          objective D (correctedIterate D s K path))
        (initial := objective D D.x0)
        (lower := fStar D)
        (by
          intro k hk
          exact hdrop_int k)
        (by
          intro path
          have htel :=
            Finset.sum_range_sub' (fun k => objective D
              (correctedIterate D s k path)) K
          simpa [correctedIterate_zero] using htel)
        (by
          intro path
          exact hGap (correctedIterate D s K path))).trans_eq (by
            unfold Delta
            rfl)
  have hB13 :
      (epsilon / (4 * D.L * n0.1)) *
          Finset.sum (Finset.range K)
            (fun k =>
              ∫ path, ‖correctedEstimator D s k path‖ ∂μ) ≤
        Delta D +
          (K : ℝ) * (3 * epsilon ^ 2 / (4 * D.L * n0.1)) := by
    have hsum_raw :
        Finset.sum (Finset.range K)
            (fun k =>
              (epsilon / (4 * D.L * n0.1)) *
                ∫ path, ‖correctedEstimator D s k path‖ ∂μ) ≤
          Finset.sum (Finset.range K)
            (fun k =>
              (∫ path,
                objective D (correctedIterate D s k path) -
                  objective D (correctedIterate D s (k + 1) path) ∂μ) +
                3 * epsilon ^ 2 / (4 * D.L * n0.1)) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      simpa using hB9 k hk
    calc
      (epsilon / (4 * D.L * n0.1)) *
          Finset.sum (Finset.range K)
            (fun k =>
              ∫ path, ‖correctedEstimator D s k path‖ ∂μ) =
        Finset.sum (Finset.range K)
          (fun k =>
            (epsilon / (4 * D.L * n0.1)) *
              ∫ path, ‖correctedEstimator D s k path‖ ∂μ) := by
          rw [Finset.mul_sum]
      _ ≤
        Finset.sum (Finset.range K)
          (fun k =>
            (∫ path,
              objective D (correctedIterate D s k path) -
                objective D (correctedIterate D s (k + 1) path) ∂μ) +
              3 * epsilon ^ 2 / (4 * D.L * n0.1)) := hsum_raw
      _ =
        Finset.sum (Finset.range K)
            (fun k =>
              ∫ path,
                objective D (correctedIterate D s k path) -
                  objective D (correctedIterate D s (k + 1) path) ∂μ) +
          (K : ℝ) * (3 * epsilon ^ 2 / (4 * D.L * n0.1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
          ring
      _ ≤
        Delta D + (K : ℝ) * (3 * epsilon ^ 2 / (4 * D.L * n0.1)) := by
          have h :=
            add_le_add_right hdrop_sum_le
              ((K : ℝ) * (3 * epsilon ^ 2 / (4 * D.L * n0.1)))
          simpa [add_comm, add_left_comm, add_assoc] using h
  have hfinal :=
    optionII_average_estimator_norm_le_four_epsilon_of_B13_budget
      (Finset.sum (Finset.range K)
        (fun k => ∫ path, ‖correctedEstimator D s k path‖ ∂μ))
      D.L (Delta D) n0.1 epsilon hL hDelta (n0_pos n0) hepsilon
      (by
        simpa [K, iterationBudget, theorem1Budget] using hB13)
  simpa [K, s, μ] using hfinal

/-- Finite-sum estimator/descent/telescope analysis for the actual corrected
run, at the finite-gap iteration budget of Theorem 2. -/
theorem correctedUniformOutputGradientAverage_bound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    correctedUniformOutputGradientAverage D (schedule epsilon D.L n0)
      (iterationBudget D epsilon n0) ≤ 5 * epsilon := by
  let s := schedule epsilon D.L n0
  let μ := withReplacementSourceLaw s
  let K := iterationBudget D epsilon n0
  letI : IsProbabilityMeasure μ := withReplacementSourceLaw_isProbability s
  have hK_pos : 0 < K := by
    dsimp [K, iterationBudget]
    exact Nat.succ_pos _
  have hconvert :
      ∀ k ∈ Finset.range K,
        (∫ path, ‖fullGradient D (correctedIterate D s k path)‖ ∂μ) ≤
          (∫ path, ‖correctedEstimator D s k path‖ ∂μ) + epsilon := by
    intro k hk
    have hmse :=
      correctedFiniteSumB17B18EstimatorMSEAdapter D epsilon n0 hScalar k
    have htarget_int :
        Integrable
          (fun path => ‖fullGradient D (correctedIterate D s k path)‖) μ := by
      simpa [s, μ] using
        correctedRunGradientNorm_integrable D epsilon n0 hScalar k
    have hestimator_aesm :
        AEStronglyMeasurable
          (fun path => correctedEstimator D s k path) μ := by
      have hest_int :
          Integrable (fun path => correctedEstimator D s k path) μ := by
        simpa [s, μ] using
          correctedRunEstimator_integrable D epsilon n0 hScalar k
      exact hest_int.aestronglyMeasurable
    have herr_def :
        ∀ path,
          (correctedEstimator D s k path -
            fullGradient D (correctedIterate D s k path)) =
            correctedEstimator D s k path -
              fullGradient D (correctedIterate D s k path) := by
      intro path
      rfl
    simpa [s, μ] using
      (integral_target_norm_le_estimator_norm_add_of_error_secondMoment
        (target := fun path =>
          fullGradient D (correctedIterate D s k path))
        (estimator := fun path => correctedEstimator D s k path)
        (err := fun path =>
          correctedEstimator D s k path -
            fullGradient D (correctedIterate D s k path))
        (epsilon := epsilon)
        (le_of_lt hScalar.1)
        htarget_int hestimator_aesm herr_def hmse)
  have hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ path, ‖correctedEstimator D s k path‖ ∂μ) ≤
        4 * epsilon := by
    simpa [s, μ, K] using
      correctedB13DescentAdapter D epsilon n0 hScalar hGap
  have hfinal :=
    uniform_average_gradient_bound_of_estimator_average
      μ (fullGradient D) (correctedIterate D s) (correctedEstimator D s)
      K hK_pos epsilon hconvert hest_avg
  simpa [correctedUniformOutputGradientAverage, s, μ, K] using hfinal

/-- Reuse the inherited B.15 selected-output conversion for the corrected run. -/
theorem correctedSelectedOutputStationarityBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    correctedSelectedOutputGradientNormExpectation
        D (schedule epsilon D.L n0) (iterationBudget D epsilon n0)
        (by
          unfold iterationBudget
          exact Nat.succ_pos _) ≤
      5 * epsilon := by
  letI : IsProbabilityMeasure (withReplacementSourceLaw (schedule epsilon D.L n0)) :=
    withReplacementSourceLaw_isProbability _
  apply selectedOutputGradientNormExpectation_le_of_uniform_average_le
  · intro R
    exact correctedRunGradientNorm_integrable D epsilon n0 hScalar R.1
  · exact correctedUniformOutputGradientAverage_bound D epsilon n0 hScalar hGap

/-- Number of full-gradient refresh events used by the rounded corrected run,
including the initial full refresh at time `0`. -/
noncomputable def roundedFullRefreshCount
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℕ := by
  classical
  exact ((Finset.range (K + 1)).filter (fun k => roundedRefreshAt s k)).card

/-- Number of recursive mini-batch updates among the `K` generated steps. -/
noncomputable def roundedRecursiveStepCount
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℕ := by
  classical
  exact ((Finset.range K).filter (fun k => ¬ roundedRefreshAt s (k + 1))).card

/-- Actual component-gradient call count for the rounded corrected finite-sum
run: full refreshes cost `S₁ = n`, while each recursive sample uses two
component-gradient evaluations per sampled index. -/
noncomputable def roundedGradientCost
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) : ℝ :=
  (roundedFullRefreshCount s K : ℝ) * s.S1 +
    2 * (roundedRecursiveStepCount s K : ℝ) * (sourceBatchCount s : ℝ)

/-- Conservative closed-form cost envelope for the rounded corrected run.

This is intentionally separated from the literal B.19 display: it counts the
same rounded run as `roundedGradientCost`, while the paper's real-valued B.19
route remains source-boundary evidence. The constants account for rounding:
`floor q ≥ q / 2` for `q ≥ 1`, and `ceil S₂ ≤ 2 S₂` for `S₂ ≥ 1`,
give `cost ≤ n + 6 K sqrt(n) / n₀`; inserting the iteration budget gives this
bound. Its order matches Theorem 2, with explicitly corrected constants. -/
noncomputable def roundedConservativeCostBound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : ℝ :=
  (n : ℝ) +
    24 * (D.L * Delta D) * Real.sqrt (n : ℝ) * epsilon⁻¹ ^ 2 +
    6 * n0.1⁻¹ * Real.sqrt (n : ℝ)

def roundedCorrectedGradientCostRoute
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  let s := schedule epsilon D.L n0
  let K := iterationBudget D epsilon n0
  roundedGradientCost s K ≤ roundedConservativeCostBound D epsilon n0

private theorem roundedFullRefreshCount_le_div_add_one
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) :
    roundedFullRefreshCount s K ≤
      K / roundedRefreshPeriod s + 1 := by
  classical
  let R := roundedRefreshPeriod s
  let A : Finset ℕ :=
    (Finset.range (K + 1)).filter (fun k => roundedRefreshAt s k)
  let B : Finset ℕ := Finset.range (K / R + 1)
  have hcard : A.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun k => k / R)
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkK, _⟩
      apply Finset.mem_range.mpr
      have hdiv : k / R ≤ K / R :=
        Nat.div_le_div_right (Nat.le_of_lt_succ (Finset.mem_range.mp hkK))
      exact Nat.lt_succ_of_le hdiv
    · intro a ha b hb hab
      rcases Finset.mem_filter.mp ha with ⟨_, haR⟩
      rcases Finset.mem_filter.mp hb with ⟨_, hbR⟩
      have haR' : a % R = 0 := by
        simpa [roundedRefreshAt, R] using haR
      have hbR' : b % R = 0 := by
        simpa [roundedRefreshAt, R] using hbR
      have ha_eq : a / R * R = a := by
        simpa [haR', Nat.add_zero, Nat.mul_comm] using
          (Nat.div_add_mod a R)
      have hb_eq : b / R * R = b := by
        simpa [hbR', Nat.add_zero, Nat.mul_comm] using
          (Nat.div_add_mod b R)
      have hab' : a / R = b / R := by
        simpa only using hab
      calc
        a = a / R * R := ha_eq.symm
        _ = b / R * R := by rw [hab']
        _ = b := hb_eq
  simpa [roundedFullRefreshCount, A, B, R] using hcard

private theorem roundedRecursiveStepCount_le_budget
    {n : ℕ} (s : SourceSchedule n) (K : ℕ) :
    roundedRecursiveStepCount s K ≤ K := by
  classical
  simpa [roundedRecursiveStepCount] using
    (Finset.card_filter_le (Finset.range K)
      (fun k => ¬ roundedRefreshAt s (k + 1)))

theorem roundedCorrectedGradientCostRoute_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    roundedCorrectedGradientCostRoute D epsilon n0 := by
  rcases hScalar with ⟨hepsilon, hL⟩
  let s := schedule epsilon D.L n0
  let K := iterationBudget D epsilon n0
  let R := roundedRefreshPeriod s
  let B := sourceBatchCount s
  have hDelta : 0 ≤ Delta D :=
    Delta_nonneg_of_finiteInitialGapBoundary D hGap
  have hn0pos : 0 < n0.1 := n0_pos n0
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := sqrt_n_pos n0
  have hnreal : 0 ≤ (n : ℝ) := by positivity
  have hq_pos : 0 < s.q := by
    simpa [s] using schedule_q_pos n0 ⟨hepsilon, hL⟩
  have hS2_pos : 0 < s.S2 := by
    simpa [s] using schedule_S2_pos n0 ⟨hepsilon, hL⟩
  have hS2_one : 1 ≤ s.S2 := by
    rw [schedule_S2]
    simpa using
      (le_div_iff₀ hn0pos).2
        (by
          simpa [one_mul] using
            (Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0_upper n0))
  have hR_pos : 0 < R := by
    simpa [R] using roundedRefreshPeriod_pos s
  have hfloor_ge_one : 1 ≤ Nat.floor s.q := by
    have hn0_one :
        (1 : ℝ) ≤ n0.1 :=
      Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0_lower n0
    have hsqrt_one : (1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
      le_trans hn0_one
        (Algorithms.Unverified.SPIDER.FiniteSumTheorem2ImplementationInternal.n0_upper n0)
    have hq_one : (1 : ℝ) ≤ s.q := by
      rw [schedule_q]
      have hmul :=
        mul_le_mul hn0_one hsqrt_one (by norm_num) (by positivity)
      nlinarith
    exact Nat.le_floor (by simpa using hq_one)
  have hR_eq_floor : R = Nat.floor s.q := by
    simp [R, roundedRefreshPeriod, hfloor_ge_one]
  have hq_le_twoR : s.q ≤ 2 * (R : ℝ) := by
    rw [hR_eq_floor]
    have hfloor_lt : s.q < (Nat.floor s.q : ℝ) + 1 :=
      Nat.lt_floor_add_one s.q
    have hfloor_one : (1 : ℝ) ≤ (Nat.floor s.q : ℝ) := by
      exact_mod_cast hfloor_ge_one
    nlinarith
  have hR_real_pos : 0 < (R : ℝ) := by
    exact_mod_cast hR_pos
  have hS2_nonneg : 0 ≤ s.S2 := le_of_lt hS2_pos
  have hqS2 :
      s.q * s.S2 = (n : ℝ) := by
    rw [schedule_q, schedule_S2]
    field_simp [ne_of_gt hn0pos, ne_of_gt hsqrt_pos]
    exact Real.sq_sqrt (by positivity)
  have hn_div_R_le : (n : ℝ) / (R : ℝ) ≤ 2 * s.S2 := by
    rw [← hqS2]
    apply (div_le_iff₀ hR_real_pos).2
    have hmul := mul_le_mul_of_nonneg_right hq_le_twoR hS2_nonneg
    nlinarith
  have hS2_batch : (B : ℝ) ≤ 2 * s.S2 := by
    have hceil_ge_one : 1 ≤ Nat.ceil s.S2 := by
      have hceil_ge_one_real :
          (1 : ℝ) ≤ (Nat.ceil s.S2 : ℝ) :=
        le_trans hS2_one (Nat.le_ceil s.S2)
      exact_mod_cast hceil_ge_one_real
    have hB_eq : B = Nat.ceil s.S2 := by
      simp [B, sourceBatchCount, max_eq_right hceil_ge_one]
    rw [hB_eq]
    have hceil_lt : (Nat.ceil s.S2 : ℝ) < s.S2 + 1 :=
      Nat.ceil_lt_add_one (le_of_lt hS2_pos)
    have hS2_one' : (1 : ℝ) ≤ s.S2 := hS2_one
    nlinarith
  have hfull_nat :
      roundedFullRefreshCount s K ≤ K / R + 1 := by
    simpa [R] using roundedFullRefreshCount_le_div_add_one s K
  have hrec_nat : roundedRecursiveStepCount s K ≤ K :=
    roundedRecursiveStepCount_le_budget s K
  have hfull :
      (roundedFullRefreshCount s K : ℝ) ≤ (K : ℝ) / (R : ℝ) + 1 := by
    have hfull_cast :
        (roundedFullRefreshCount s K : ℝ) ≤
          ((K / R : ℕ) : ℝ) + 1 := by
      exact_mod_cast hfull_nat
    have hdiv_real : ((K / R : ℕ) : ℝ) ≤ (K : ℝ) / (R : ℝ) := by
      apply (le_div_iff₀ hR_real_pos).2
      exact_mod_cast Nat.div_mul_le_self K R
    exact hfull_cast.trans (by nlinarith [hdiv_real])
  have hrec :
      (roundedRecursiveStepCount s K : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hrec_nat
  have hK_nonneg : 0 ≤ (K : ℝ) := by positivity
  have hfull_cost :
      (roundedFullRefreshCount s K : ℝ) * (n : ℝ) ≤
        (n : ℝ) + 2 * (K : ℝ) * s.S2 := by
    calc
      (roundedFullRefreshCount s K : ℝ) * (n : ℝ) ≤
          ((K : ℝ) / (R : ℝ) + 1) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hfull hnreal
      _ = (K : ℝ) * ((n : ℝ) / (R : ℝ)) + (n : ℝ) := by
        field_simp [ne_of_gt hR_real_pos]
      _ ≤ (K : ℝ) * (2 * s.S2) + (n : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hn_div_R_le hK_nonneg]
      _ = (n : ℝ) + 2 * (K : ℝ) * s.S2 := by ring
  have hrecursive_cost :
      2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) ≤
        4 * (K : ℝ) * s.S2 := by
    have hstep :
        2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) ≤
          2 * (K : ℝ) * (B : ℝ) := by
      calc
        2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) =
            (roundedRecursiveStepCount s K : ℝ) * (2 * (B : ℝ)) := by ring
        _ ≤ (K : ℝ) * (2 * (B : ℝ)) :=
          mul_le_mul_of_nonneg_right hrec (by positivity)
        _ = 2 * (K : ℝ) * (B : ℝ) := by ring
    calc
      2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) ≤
          2 * (K : ℝ) * (B : ℝ) := hstep
      _ ≤ 2 * (K : ℝ) * (2 * s.S2) :=
        mul_le_mul_of_nonneg_left hS2_batch (by positivity)
      _ = 4 * (K : ℝ) * s.S2 := by ring
  have hA_nonneg :
      0 ≤ 4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 := by
    positivity
  have hK :
      (K : ℝ) ≤
        4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1 := by
    unfold K iterationBudget
    rw [Nat.cast_add]
    simpa [add_comm] using
      (add_le_add_right (Nat.floor_le hA_nonneg) (1 : ℝ))
  have hcost_budget :
      (n : ℝ) + 6 * (K : ℝ) * s.S2 ≤
        roundedConservativeCostBound D epsilon n0 := by
    have hscaled :
        6 * (K : ℝ) * s.S2 ≤
          6 * (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1) * s.S2 := by
      calc
        6 * (K : ℝ) * s.S2 =
            (K : ℝ) * (6 * s.S2) := by ring
        _ ≤
            (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1) *
              (6 * s.S2) :=
          mul_le_mul_of_nonneg_right hK (by positivity)
        _ = 6 * (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1) * s.S2 := by
          ring
    calc
      (n : ℝ) + 6 * (K : ℝ) * s.S2 ≤
          (n : ℝ) +
            6 * (4 * D.L * Delta D * n0.1 * epsilon⁻¹ ^ 2 + 1) * s.S2 :=
        by nlinarith [hscaled]
      _ = roundedConservativeCostBound D epsilon n0 := by
        dsimp [s]
        rw [schedule_S2]
        unfold roundedConservativeCostBound
        field_simp [ne_of_gt hepsilon, ne_of_gt hn0pos,
          ne_of_gt hsqrt_pos]
        ring
  change roundedGradientCost s K ≤ roundedConservativeCostBound D epsilon n0
  calc
    roundedGradientCost s K =
        (roundedFullRefreshCount s K : ℝ) * s.S1 +
          2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) := by
      rfl
    _ = (roundedFullRefreshCount s K : ℝ) * (n : ℝ) +
          2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) := by
      rw [schedule_S1]
    _ ≤ (n : ℝ) + 6 * (K : ℝ) * s.S2 := by
      calc
        (roundedFullRefreshCount s K : ℝ) * (n : ℝ) +
              2 * (roundedRecursiveStepCount s K : ℝ) * (B : ℝ) ≤
            ((n : ℝ) + 2 * (K : ℝ) * s.S2) +
              4 * (K : ℝ) * s.S2 :=
          add_le_add hfull_cost hrecursive_cost
        _ = (n : ℝ) + 6 * (K : ℝ) * s.S2 := by ring
    _ ≤ roundedConservativeCostBound D epsilon n0 := hcost_budget

/-- Live full corrected B.19 route required by the audit: the literal printed
call count is kept as the first inequality before the corrected closed form. -/
def liveCorrectedB19FullCostRoute
    {n d : ℕ}
    (D : SourceData n d) (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) : Prop :=
  literalGradientCost (schedule epsilon D.L n0)
      (iterationBudget D epsilon n0) ≤
    correctedB19CallCount (schedule epsilon D.L n0)
      (iterationBudget D epsilon n0) ∧
  correctedB19CallCount (schedule epsilon D.L n0)
      (iterationBudget D epsilon n0) ≤
    correctedCostBound D epsilon n0

theorem liveLiteralGradientCost_le_correctedB19CallCount_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    literalGradientCost (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) ≤
      correctedB19CallCount (schedule epsilon D.L n0)
        (iterationBudget D epsilon n0) := by
  rcases hScalar with ⟨hepsilon, hL⟩
  have hq_pos := schedule_q_pos n0 ⟨hepsilon, hL⟩
  have hS1_nonneg : 0 ≤ ((schedule epsilon D.L n0).S1 : ℝ) := by
    rw [schedule_S1]
    positivity
  have hqinvS1 :
      (schedule epsilon D.L n0).q⁻¹ *
          ((schedule epsilon D.L n0).S1 : ℝ) =
        (schedule epsilon D.L n0).S2 := by
    rw [schedule_q, schedule_S1, schedule_S2]
    have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp [ne_of_gt (n0_pos n0), ne_of_gt (sqrt_n_pos n0)]
    nlinarith [hsquare]
  have hceil :=
    Algorithms.Unverified.SPIDER.ceil_epoch_refresh_cost_bound
      (iterationBudget D epsilon n0) hq_pos hS1_nonneg hqinvS1
  simpa [literalGradientCost, correctedB19CallCount,
    recursiveGradientCallCount, fullRefreshCallCount, div_eq_mul_inv] using hceil

theorem liveCorrectedB19FullCostRoute_of_bound
    {n d : ℕ}
    (D : SourceData n d) (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    liveCorrectedB19FullCostRoute D epsilon n0 hScalar hGap := by
  exact ⟨
    liveLiteralGradientCost_le_correctedB19CallCount_obligation
      D epsilon n0 hScalar hGap,
    correctedB19CallCount_le_bound_at_budget
      D epsilon n0 hScalar hGap⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

namespace Algorithms.Unverified.SPIDER.FiniteSumTheorem2PaperBoundaryV59

/-!
Selected-output boundary for the registered finite-sum Theorem 2 root.

The source B.15 conclusion is the Algorithm 1 line-17 selected-output
expectation, not a universal statement over arbitrary measures and source
processes.
-/

open Algorithms.Unverified.SPIDER.FiniteSumTheorem2Active

/-- Paper-facing selected-output stationarity boundary for finite-sum Theorem 2.

The proposition uses the canonical with-replacement source law and the
corrected total rounded run.  It is intentionally not an existential statement
over the old positive-norm relational process: the zero-estimator branch is
defined by staying put, and the real refresh period is rounded to a positive
natural modulus for the actual run. -/
def paperSelectedOutputStationarityBound
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n) : Prop :=
  let s := schedule epsilon D.L n0
  WithReplacementSourceLawBoundary s ∧
    correctedSelectedOutputGradientNormExpectation
      D s (iterationBudget D epsilon n0)
      (by
        unfold iterationBudget
        exact Nat.succ_pos _) ≤
      5 * epsilon

/-- Source-boundary proof obligation for the B.13--B.15 selected-output route.

Later proof work must prove the selected-output bound for the concrete iid
with-replacement law and corrected total rounded run, using the finite-sum
estimator, descent, telescope, and output-conversion edges. -/
theorem paperSelectedOutputStationarityBound_obligation
    {n d : ℕ} (D : SourceData n d)
    (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    paperSelectedOutputStationarityBound D epsilon n0 := by
  dsimp [paperSelectedOutputStationarityBound]
  exact ⟨
    withReplacementSourceLaw_spec (schedule epsilon D.L n0),
    correctedSelectedOutputStationarityBound_obligation
      D epsilon n0 hScalar hGap⟩

/-- Corrected/source-boundary finite-sum Theorem 2 object.

This is the intended corrected paper-facing boundary: selected-output
stationarity for the canonical corrected run, rounded-run gradient-cost
accounting and the explicit source-gap record.  It is still a corrected/source-boundary statement, not the literal
unqualified printed theorem. -/
def correctedFiniteSumTheorem2Boundary
    {n d : ℕ}
    (D : SourceData n d) (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) : Prop :=
  paperSelectedOutputStationarityBound D epsilon n0 ∧
    roundedCorrectedGradientCostRoute D epsilon n0 ∧
    theorem2FiniteSumSourceBoundaryGaps

theorem correctedFiniteSumTheorem2Boundary_of_source
    {n d : ℕ}
    (D : SourceData n d) (epsilon : ℝ) (n0 : N0 n)
    (hScalar : scalarDomain D epsilon n0)
    (hGap : finiteInitialGapBoundary D) :
    correctedFiniteSumTheorem2Boundary D epsilon n0 hScalar hGap := by
  exact ⟨
    paperSelectedOutputStationarityBound_obligation
      D epsilon n0 hScalar hGap,
    roundedCorrectedGradientCostRoute_obligation
      D epsilon n0 hScalar hGap,
    theorem2_finite_sum_source_boundary_gaps⟩

end Algorithms.Unverified.SPIDER.FiniteSumTheorem2PaperBoundaryV59

namespace Algorithms.Unverified.SPIDER

/-- Registered corrected/source-boundary finite-sum Theorem 2 root.

This is the JSON-selected extension root.  Its conclusion includes the B.15
selected-output stationarity bound `≤ 5 * epsilon` and the corrected B.19 cost
route, while preserving the explicit source-boundary gap record. -/
theorem theorem2_finite_sum_gradient_cost_bound
    {n d : ℕ}
    (D : FiniteSumTheorem2Active.SourceData n d)
    (epsilon : ℝ) (n0 : FiniteSumTheorem2Active.N0 n)
    (hScalar : FiniteSumTheorem2Active.scalarDomain D epsilon n0)
    (hGap : FiniteSumTheorem2Active.finiteInitialGapBoundary D) :
    FiniteSumTheorem2PaperBoundaryV59.correctedFiniteSumTheorem2Boundary
      D epsilon n0 hScalar hGap :=
  FiniteSumTheorem2PaperBoundaryV59.correctedFiniteSumTheorem2Boundary_of_source
    D epsilon n0 hScalar hGap

end Algorithms.Unverified.SPIDER
