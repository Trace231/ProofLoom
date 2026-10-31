import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.NetworkMatrix
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

/-!
# Time-varying push-pull: object layer

This file records the canonical objects from the time-varying push-pull paper:
the finite-average objective, the sampled gradient table `G_t`, the one-step
push-pull recursion, and the generated iterate process. The recurrence is not a
field of `Setup`; it is a definition built from the paper data and a noise
sample path.
-/

open scoped BigOperators
open scoped Gradient
open scoped InnerProductSpace
open scoped Topology

open MeasureTheory
open ProbabilityTheory
open Filter

namespace Algorithms.Unverified.TimeVaryingPushPull

universe uΩ

variable {Node E : Type*}
variable [Fintype Node] [Nonempty Node]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/-- Matrix-shaped distributed state `R^{n × d}`: one vector row per node. The
ambient finite-dimensional inner-product space `E` models the paper's `R^d`
without fixing coordinates. -/
abbrev State (Node E : Type*) := Node → E

/-- Scalar row vector indexed by nodes. -/
abbrev RowVector (Node : Type*) := Node → ℝ

/-- Scalar node matrix indexed by row and column nodes. -/
abbrev NodeMatrix (Node : Type*) := Node → Node → ℝ

/-- Time-indexed oracle-noise sample path `ε_t`. -/
abbrev NoisePath (Node E : Type*) := ℕ → State Node E

/-- Random oracle-noise sample path. -/
abbrev RandomNoisePath (Ω Node E : Type*) := Ω → NoisePath Node E

/-- Zero-sum distributed states, the source subspace
`S = {W : 1^T W = 0}` on which the corrected lift is defined. -/
abbrev ZeroSumState (Node E : Type*) [Fintype Node] [AddCommMonoid E] :=
  FiniteNetwork.ZeroSumState Node E

/-- Canonical finite-average objective from component objectives. -/
noncomputable def finiteAverageObjectiveOf
    (componentObjective : Node → E → ℝ) (x : E) : ℝ :=
  SOptLib.finiteUniformAverage (fun i : Node => componentObjective i x)

/-- Global `L`-smoothness, represented as a global Lipschitz-gradient bound for
Mathlib's gradient selector together with differentiability, so the totalized
gradient is not silently used outside the paper's smooth setting. -/
def IsLSmoothFunction (L : ℝ) (φ : E → ℝ) : Prop :=
  Differentiable ℝ φ ∧
    ∀ x y : E, ‖∇ φ x - ∇ φ y‖ ≤ L * ‖x - y‖

/-- Row-stochastic matrix predicate: nonnegative entries and row sums one. -/
def RowStochastic (A : NodeMatrix Node) : Prop :=
  (∀ i j : Node, 0 ≤ A i j) ∧ ∀ i : Node, ∑ j : Node, A i j = 1

/-- Column-stochastic matrix predicate: nonnegative entries and column sums one. -/
def ColumnStochastic (A : NodeMatrix Node) : Prop :=
  (∀ i j : Node, 0 ≤ A i j) ∧ ∀ j : Node, ∑ i : Node, A i j = 1

/-- Positive diagonal predicate for a node matrix. -/
def PositiveDiagonal (A : NodeMatrix Node) : Prop :=
  FiniteNetwork.PositiveDiagonal A

/-- Uniform lower bound on every positive matrix entry. -/
def PositiveEntriesLowerBounded (a : ℝ) (A : NodeMatrix Node) : Prop :=
  ∀ i j : Node, 0 < A i j → a ≤ A i j

/-- Strong connectivity of the directed graph induced by positive entries. -/
def StronglyConnectedPositiveGraph (A : NodeMatrix Node) : Prop :=
  FiniteNetwork.IsStronglyConnectedPositiveSupport A

/-- Paper setup data for the finite-sum objective and deterministic network
schedule. The primitive fields are exactly the paper's stated data and
assumptions:
`#/assumptions/0` gives `f=n^{-1}sum_i f_i`; `#/assumptions/2` gives `x_0`;
`#/assumptions/4` gives global `L`-smoothness, lower boundedness, and
`0 < Delta < infinity`; `#/assumptions/6` gives the oracle variance scale
`sigma`; `#/assumptions/1` gives the constant stepsize and the matrices
`R_t,C_t`; `#/assumptions/8` gives fixed exogenous `p`-periodic row/column
stochastic networks with positive diagonal, minimum positive weight `a>0`, and
strong connectivity. The iterate arrays, gradient table, and recursion are
canonical definitions below, not witness fields. -/
structure Setup (Node E : Type*) [Fintype Node] [Nonempty Node]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  /-- Component objectives `f_i : R^d -> R`. -/
  componentObjective : Node → E → ℝ
  /-- Common initial vector `x_0`. -/
  x0 : E
  /-- Global smoothness constant `L`. -/
  L : ℝ
  /-- The smoothness constant is positive in the theorem's stepsize ceiling. -/
  L_pos : 0 < L
  /-- Each component objective is globally `L`-smooth. -/
  component_lsmooth : ∀ i : Node, IsLSmoothFunction (E := E) L (componentObjective i)
  /-- The finite-average objective is bounded below. -/
  objective_bddBelow : BddBelow (Set.range (finiteAverageObjectiveOf
    (Node := Node) (E := E) componentObjective))
  /-- Source lower-gap assumption `0 < Delta := f(x_0) - inf f`. -/
  Delta_pos : 0 <
    finiteAverageObjectiveOf (Node := Node) (E := E) componentObjective x0 -
      SOptLib.objectiveInfimumValue (Set.univ : Set E)
        (finiteAverageObjectiveOf (Node := Node) (E := E) componentObjective)
  /-- Oracle variance scale `σ`. -/
  sigma : ℝ
  /-- The variance scale `σ` is a nonnegative standard-deviation parameter. -/
  sigma_nonneg : 0 ≤ sigma
  /-- Constant stepsize `α`. -/
  alpha : ℝ
  /-- Fixed network period `p`. -/
  period : ℕ
  /-- Period is nonzero: `p ≥ 1`. -/
  period_pos : 0 < period
  /-- Uniform positive-entry lower bound `a`. -/
  minPositiveWeight : ℝ
  /-- The positive-entry lower bound satisfies `a > 0`. -/
  minPositiveWeight_pos : 0 < minPositiveWeight
  /-- Row-stochastic push matrices `R_t`, represented by their entries. -/
  R : ℕ → NodeMatrix Node
  /-- Column-stochastic pull matrices `C_t`, represented by their entries. -/
  C : ℕ → NodeMatrix Node
  /-- Periodic push schedule `R_{t+p}=R_t`. -/
  R_periodic : ∀ t : ℕ, R (t + period) = R t
  /-- Periodic pull schedule `C_{t+p}=C_t`. -/
  C_periodic : ∀ t : ℕ, C (t + period) = C t
  /-- Every `R_t` is row-stochastic. -/
  R_rowStochastic : ∀ t : ℕ, RowStochastic (Node := Node) (R t)
  /-- Every `C_t` is column-stochastic. -/
  C_columnStochastic : ∀ t : ℕ, ColumnStochastic (Node := Node) (C t)
  /-- Every `R_t` has positive diagonal. -/
  R_positiveDiagonal : ∀ t : ℕ, PositiveDiagonal (Node := Node) (R t)
  /-- Every `C_t` has positive diagonal. -/
  C_positiveDiagonal : ∀ t : ℕ, PositiveDiagonal (Node := Node) (C t)
  /-- Positive entries of every `R_t` are at least `a`. -/
  R_positiveEntriesLowerBounded :
    ∀ t : ℕ, PositiveEntriesLowerBounded (Node := Node) minPositiveWeight (R t)
  /-- Positive entries of every `C_t` are at least `a`. -/
  C_positiveEntriesLowerBounded :
    ∀ t : ℕ, PositiveEntriesLowerBounded (Node := Node) minPositiveWeight (C t)
  /-- The positive-entry graph of every `R_t` is strongly connected. -/
  R_stronglyConnected : ∀ t : ℕ, StronglyConnectedPositiveGraph (Node := Node) (R t)
  /-- The positive-entry graph of every `C_t` is strongly connected. -/
  C_stronglyConnected : ∀ t : ℕ, StronglyConnectedPositiveGraph (Node := Node) (C t)

/-- Number of nodes `n`. -/
def nodeCount : ℕ := Fintype.card Node

/-- The paper node count is positive because the node index type is nonempty. -/
theorem nodeCount_pos : 0 < nodeCount (Node := Node) := by
  classical
  simpa [nodeCount] using (Fintype.card_pos : 0 < Fintype.card Node)

/-- Real nonzero denominator certificate for quotients by `n`. -/
theorem nodeCount_real_ne_zero : (nodeCount (Node := Node) : ℝ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (nodeCount_pos (Node := Node)))

theorem sq_sum_eq_card_mul_sum_sq_iff_pairwise_eq
    {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∑ i : ι, f i) ^ 2 =
        (Fintype.card ι : ℝ) * ∑ i : ι, (f i) ^ 2 ↔
      ∀ i j : ι, f i = f j := by
  exact _root_.sq_sum_eq_card_mul_sum_sq_iff_pairwise_eq f

namespace Setup

variable (setup : Setup Node E)

/-- Finite-average objective `f(x) = n^{-1} * sum_i f_i(x)`. -/
noncomputable def objective (x : E) : ℝ :=
  finiteAverageObjectiveOf (Node := Node) (E := E) setup.componentObjective x

/-- Source-form unfolding of the finite-average objective. -/
theorem objective_eq_finite_average (x : E) :
    setup.objective x =
      ((nodeCount (Node := Node) : ℝ)⁻¹) *
        ∑ i : Node, setup.componentObjective i x := by
  simp [objective, finiteAverageObjectiveOf, SOptLib.finiteUniformAverage, nodeCount]

/-- Infimum value of the unconstrained finite-average objective. -/
noncomputable def objectiveInfimum : ℝ :=
  SOptLib.objectiveInfimumValue (Set.univ : Set E) setup.objective

/-- Paper objective gap `Delta = f(x_0) - inf f`. -/
noncomputable def Delta : ℝ :=
  setup.objective setup.x0 - setup.objectiveInfimum

/-- The source lower-gap assumption gives `0 < Delta`. -/
theorem Delta_positive : 0 < setup.Delta := by
  simpa [Delta, objectiveInfimum, objective] using setup.Delta_pos

/-- The stochastic variance scale is nonnegative. -/
theorem sigma_nonneg_source : 0 ≤ setup.sigma :=
  setup.sigma_nonneg

/-- The finite-average objective is bounded below. -/
theorem objective_bddBelow_source : BddBelow (Set.range setup.objective) := by
  simpa [objective] using setup.objective_bddBelow

/-- Component objectives are differentiable as part of global smoothness. -/
theorem componentObjective_differentiable (i : Node) :
    Differentiable ℝ (setup.componentObjective i) :=
  (setup.component_lsmooth i).1

/-- Component gradients satisfy the global `L`-Lipschitz bound. -/
theorem componentGradient_lipschitz_bound (i : Node) (x y : E) :
    ‖∇ (setup.componentObjective i) x - ∇ (setup.componentObjective i) y‖ ≤
      setup.L * ‖x - y‖ :=
  (setup.component_lsmooth i).2 x y

/-- Canonical component gradient `∇ f_i(x)`. -/
noncomputable def componentGradient (i : Node) (x : E) : E :=
  ∇ (setup.componentObjective i) x

/-- Average gradient selector for the finite-average objective. -/
noncomputable def averageGradient (x : E) : E :=
  ∇ (setup.objective) x

/-- The average-gradient selector realizes the finite average of component
gradients under the usual calculus hypotheses. Left as a proof obligation for
the prover phase. -/
theorem averageGradient_eq_componentGradient_average (x : E) :
    setup.averageGradient x =
      ((nodeCount (Node := Node) : ℝ)⁻¹) •
        ∑ i : Node, setup.componentGradient i x := by
  have hcomp : ∀ i : Node,
      HasGradientAt (setup.componentObjective i)
        (setup.componentGradient i x) x := by
    intro i
    simpa [componentGradient] using
      (setup.componentObjective_differentiable i x).hasGradientAt
  have hobj :
      setup.objective =
        SOptLib.finiteUniformAverage setup.componentObjective := by
    funext z
    simp [objective, finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
  rw [averageGradient, hobj]
  simpa [SOptLib.finiteUniformAverage, nodeCount] using
    (SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      setup.componentObjective setup.componentGradient x hcomp)

/-- Identity node matrix. -/
noncomputable def identityMatrix : NodeMatrix Node := by
  classical
  exact fun i j => if i = j then 1 else 0

/-- Matrix addition for node matrices. -/
def matrixAdd (A B : NodeMatrix Node) : NodeMatrix Node :=
  fun i j => A i j + B i j

/-- Matrix subtraction for node matrices. -/
def matrixSub (A B : NodeMatrix Node) : NodeMatrix Node :=
  fun i j => A i j - B i j

/-- Matrix multiplication for node matrices. -/
noncomputable def matrixMul (A B : NodeMatrix Node) : NodeMatrix Node :=
  fun i k => ∑ j : Node, A i j * B j k

/-- Natural powers of node matrices, used for the paper's stable propagator
bound `F(α)^j`. -/
noncomputable def matrixPower (A : NodeMatrix Node) : ℕ → NodeMatrix Node
  | 0 => identityMatrix (Node := Node)
  | j + 1 => matrixMul (Node := Node) (matrixPower A j) A

/-- Left multiplication of a row vector by a node matrix. -/
noncomputable def rowMulMatrix (w : RowVector Node) (A : NodeMatrix Node) :
    RowVector Node :=
  fun j => ∑ i : Node, w i * A i j

/-- Multiplication of a node matrix by a column vector. -/
noncomputable def matrixMulVector (A : NodeMatrix Node) (v : RowVector Node) :
    RowVector Node :=
  fun i => ∑ j : Node, A i j * v j

/-- Row vector applied to a distributed state, the product `w^T X`. -/
noncomputable def weightedState (w : RowVector Node) (X : State Node E) : E :=
  ∑ i : Node, w i • X i

/-- Sum of row-vector entries, the product `w^T 1`. -/
noncomputable def rowSum (w : RowVector Node) : ℝ :=
  ∑ i : Node, w i

/-- Dot product of scalar node vectors, used for left/right eigenvector
normalizations and the derivative formula in Lemma A.1. -/
noncomputable def rowDot (w v : RowVector Node) : ℝ :=
  ∑ i : Node, w i * v i

/-- Euclidean squared norm of a finite scalar row vector. -/
noncomputable def rowNormSq (w : RowVector Node) : ℝ :=
  ∑ i : Node, (w i) ^ 2

/-- Frobenius squared norm of a distributed matrix-shaped state. -/
noncomputable def frobeniusNormSq (X : State Node E) : ℝ :=
  ∑ i : Node, ‖X i‖ ^ 2

/-- Nonnegativity of every push-matrix entry. -/
theorem R_entry_nonneg (t : ℕ) (i j : Node) : 0 ≤ setup.R t i j :=
  (setup.R_rowStochastic t).1 i j

/-- Row sums of push matrices are one. -/
theorem R_row_sum (t : ℕ) (i : Node) :
    ∑ j : Node, setup.R t i j = 1 :=
  (setup.R_rowStochastic t).2 i

/-- Nonnegativity of every pull-matrix entry. -/
theorem C_entry_nonneg (t : ℕ) (i j : Node) : 0 ≤ setup.C t i j :=
  (setup.C_columnStochastic t).1 i j

/-- Column sums of pull matrices are one. -/
theorem C_column_sum (t : ℕ) (j : Node) :
    ∑ i : Node, setup.C t i j = 1 :=
  (setup.C_columnStochastic t).2 j

/-- Left multiplication of a node matrix into a distributed state. This is the
paper product `A X` for `A in R^{n × n}` and `X in R^{n × d}`. -/
noncomputable def leftMul (A : Node → Node → ℝ) (X : State Node E) :
    State Node E :=
  fun i => Matrix.smulVec A X i

/-- Defining equation for left multiplication. -/
theorem leftMul_apply (A : Node → Node → ℝ) (X : State Node E) (i : Node) :
    leftMul (Node := Node) (E := E) A X i =
      ∑ j : Node, A i j • X j := by
  rfl

/-- Pull-matrix product `C_{t+j-1:t}` used in the corrected-lift series.
The zero-length product is the identity. -/
noncomputable def pullLiftProduct (t : ℕ) : ℕ → NodeMatrix Node
  | 0 => identityMatrix (Node := Node)
  | j + 1 => matrixMul (Node := Node) (setup.C (t + j))
      (pullLiftProduct t j)

/-- Push-matrix product `R_{t+j-1:t}` used in the row-stochastic contraction
estimate. The zero-length product is the identity. -/
noncomputable def pushLiftProduct (t : ℕ) : ℕ → NodeMatrix Node
  | 0 => identityMatrix (Node := Node)
  | j + 1 => matrixMul (Node := Node) (setup.R (t + j))
      (pushLiftProduct t j)

/-- Consecutive products for a generic time-varying matrix schedule.  This is
the reusable product underlying `pushLiftProduct` and `pullLiftProduct` and the
generic arbitrary-window contraction theorem below. -/
noncomputable def consecutiveProduct (A : ℕ → NodeMatrix Node)
    (t : ℕ) : ℕ → NodeMatrix Node
  | 0 => identityMatrix (Node := Node)
  | j + 1 => matrixMul (Node := Node) (A (t + j))
      (consecutiveProduct A t j)

private theorem consecutiveProduct_eq_finiteNetwork
    [DecidableEq Node] (A : ℕ → NodeMatrix Node) (t k : ℕ) :
    consecutiveProduct (Node := Node) A t k =
      let matrixSchedule : ℕ → Matrix Node Node ℝ := A
      FiniteNetwork.consecutiveProduct matrixSchedule t k := by
  classical
  let matrixSchedule : ℕ → Matrix Node Node ℝ := A
  change consecutiveProduct (Node := Node) A t k =
    FiniteNetwork.consecutiveProduct matrixSchedule t k
  induction k with
  | zero =>
      simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
      unfold identityMatrix
      funext u v
      by_cases h : u = v <;> simp [Matrix.one_apply, h]
  | succ k ih =>
      simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
      rw [ih]
      unfold matrixMul
      funext u v
      rw [Matrix.mul_apply]

/-- Lemma 4.2 window length `ell = max {1, n-1}`. -/
def contractionWindow : ℕ :=
  max 1 (nodeCount (Node := Node) - 1)

/-- Lemma 4.2 contraction block factor
`delta = max {1/2, 1 - n a^ell}`. -/
noncomputable def contractionDelta : ℝ :=
  max (1 / 2)
    (1 - (nodeCount (Node := Node) : ℝ) *
      setup.minPositiveWeight ^ contractionWindow (Node := Node))

/-- Lemma 4.2 per-step contraction rate `r_* = delta^(1/ell)`. -/
noncomputable def contractionRate : ℝ :=
  Real.rpow setup.contractionDelta
    ((contractionWindow (Node := Node) : ℝ)⁻¹)

/-- Lemma 4.2 column-product contraction constant `M_C = sqrt(n)/delta`. -/
noncomputable def columnContractionConstant : ℝ :=
  Real.sqrt (nodeCount (Node := Node) : ℝ) / setup.contractionDelta

theorem contractionDelta_pos : 0 < setup.contractionDelta := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  exact hhalf.trans_le (le_max_left _ _)

theorem contractionDelta_lt_one : setup.contractionDelta < 1 := by
  have hn : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast nodeCount_pos (Node := Node)
  have ha : 0 < setup.minPositiveWeight ^ contractionWindow (Node := Node) :=
    pow_pos setup.minPositiveWeight_pos _
  rw [contractionDelta]
  apply max_lt
  · norm_num
  · nlinarith

theorem contractionRate_nonneg : 0 ≤ setup.contractionRate := by
  exact Real.rpow_nonneg setup.contractionDelta_pos.le _

theorem contractionRate_lt_one : setup.contractionRate < 1 := by
  have hwindow_pos : 0 < contractionWindow (Node := Node) := by
    simp [contractionWindow]
  have hwindow_real_pos : 0 < (contractionWindow (Node := Node) : ℝ) := by
    exact_mod_cast hwindow_pos
  exact Real.rpow_lt_one setup.contractionDelta_pos.le setup.contractionDelta_lt_one
    (inv_pos.mpr hwindow_real_pos)

theorem pushLiftProduct_eq_consecutiveProduct (t j : ℕ) :
    setup.pushLiftProduct t j =
      consecutiveProduct (Node := Node) setup.R t j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pushLiftProduct, consecutiveProduct, ih]

theorem pullLiftProduct_eq_consecutiveProduct (t j : ℕ) :
    setup.pullLiftProduct t j =
      consecutiveProduct (Node := Node) setup.C t j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pullLiftProduct, consecutiveProduct, ih]

/-- The four Perron equations from
`book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9`:
`pi_{t+1}^T R_t = pi_t^T`, `pi_t^T 1 = 1`, `v_{t+1}=C_t v_t`,
`1^T v_t=1`, before positivity, periodicity, and uniqueness are imposed. -/
def PerronSequencesEquations (seqs : (ℕ → RowVector Node) × (ℕ → RowVector Node)) :
    Prop :=
  FiniteNetwork.PushPullPerronEquations setup.R setup.C seqs
    (rowMul := rowMulMatrix (Node := Node))
    (mulVec := matrixMulVector (Node := Node))
    (mass := rowSum (Node := Node))

/-- Positivity and `p`-periodicity of the absolute-probability/Perron
sequences associated with the fixed periodic network in
`#/assumptions/8` and the Perron equations in `#/assumptions/9`. -/
def PerronSequencesPositivePeriodic
    (seqs : (ℕ → RowVector Node) × (ℕ → RowVector Node)) : Prop :=
  (∀ (t : ℕ) (i : Node), 0 < seqs.1 t i) ∧
    (∀ (t : ℕ) (i : Node), 0 < seqs.2 t i) ∧
    (∀ t : ℕ, seqs.1 (t + setup.period) = seqs.1 t) ∧
    (∀ t : ℕ, seqs.2 (t + setup.period) = seqs.2 t)

/-- Specification of the unique positive periodic left/right Perron sequences
from `#/assumptions/8` and `#/assumptions/9`. -/
def PerronSequencesSpec (seqs : (ℕ → RowVector Node) × (ℕ → RowVector Node)) :
    Prop :=
  FiniteNetwork.UniquePositivePeriodicPushPullPerronSequences
    setup.R setup.C setup.period seqs
    (rowMul := rowMulMatrix (Node := Node))
    (mulVec := matrixMulVector (Node := Node))
    (mass := rowSum (Node := Node))

theorem identityMatrix_rowStochastic :
    RowStochastic (Node := Node) (identityMatrix (Node := Node)) := by
  classical
  constructor
  · intro i j
    simp only [identityMatrix]
    split_ifs <;> norm_num
  · intro i
    simp [identityMatrix]

theorem identityMatrix_columnStochastic :
    ColumnStochastic (Node := Node) (identityMatrix (Node := Node)) := by
  classical
  constructor
  · intro i j
    simp only [identityMatrix]
    split_ifs <;> norm_num
  · intro j
    simp [identityMatrix]

theorem identityMatrix_positiveDiagonal :
    PositiveDiagonal (Node := Node) (identityMatrix (Node := Node)) := by
  classical
  intro i
  simp [identityMatrix]

theorem matrixMul_rowStochastic {A B : NodeMatrix Node}
    (hA : RowStochastic (Node := Node) A)
    (hB : RowStochastic (Node := Node) B) :
    RowStochastic (Node := Node) (matrixMul (Node := Node) A B) := by
  classical
  constructor
  · intro i k
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA.1 i j) (hB.1 j k)
  · intro i
    calc
      (∑ k : Node, matrixMul (Node := Node) A B i k) =
          ∑ j : Node, ∑ k : Node, A i j * B j k := by
            simp only [matrixMul]
            rw [Finset.sum_comm]
      _ = ∑ j : Node, A i j * ∑ k : Node, B j k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ j : Node, A i j * 1 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hB.2 j]
      _ = 1 := by simpa using hA.2 i

theorem matrixMul_columnStochastic {A B : NodeMatrix Node}
    (hA : ColumnStochastic (Node := Node) A)
    (hB : ColumnStochastic (Node := Node) B) :
    ColumnStochastic (Node := Node) (matrixMul (Node := Node) A B) := by
  classical
  constructor
  · intro i k
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA.1 i j) (hB.1 j k)
  · intro k
    calc
      (∑ i : Node, matrixMul (Node := Node) A B i k) =
          ∑ j : Node, ∑ i : Node, A i j * B j k := by
            simp only [matrixMul]
            rw [Finset.sum_comm]
      _ = ∑ j : Node, (∑ i : Node, A i j) * B j k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
      _ = ∑ j : Node, 1 * B j k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hA.2 j]
      _ = 1 := by simpa using hB.2 k

theorem matrixMul_positiveDiagonal {A B : NodeMatrix Node}
    (hA_nonneg : ∀ i j : Node, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Node, 0 ≤ B i j)
    (hA_diag : PositiveDiagonal (Node := Node) A)
    (hB_diag : PositiveDiagonal (Node := Node) B) :
    PositiveDiagonal (Node := Node) (matrixMul (Node := Node) A B) := by
  simpa only [PositiveDiagonal, matrixMul, Matrix.mul_apply] using
    FiniteNetwork.PositiveDiagonal.mul hA_nonneg hB_nonneg hA_diag hB_diag

/-- A path from outside a finite reached set to a node in the set has a first
edge entering it.  This is the graph-theoretic step used in the paper's proof
that a positive diagonal, strongly connected schedule expands reachability at
every time. -/
theorem exists_positive_edge_into_finset
    (A : NodeMatrix Node)
    (hconn : StronglyConnectedPositiveGraph (Node := Node) A)
    (S : Finset Node) (hS : S.Nonempty) (hS_ne : S ≠ Finset.univ) :
    ∃ i u : Node, i ∉ S ∧ u ∈ S ∧ 0 < A i u := by
  exact FiniteNetwork.IsStronglyConnectedPositiveSupport.exists_edge_into
    A hconn S hS hS_ne

theorem consecutiveProduct_entry_nonneg
    (A : ℕ → NodeMatrix Node)
    (hA : ∀ s : ℕ, ∀ i j : Node, 0 ≤ A s i j)
    (t k : ℕ) (i j : Node) :
    0 ≤ consecutiveProduct (Node := Node) A t k i j := by
  classical
  let matrixSchedule : ℕ → Matrix Node Node ℝ := A
  have hproduct : consecutiveProduct (Node := Node) A t k =
      FiniteNetwork.consecutiveProduct matrixSchedule t k := by
    induction k with
    | zero =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        unfold identityMatrix
        funext u v
        rw [Matrix.one_apply]
    | succ k ih =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        rw [ih]
        unfold matrixMul
        funext u v
        rw [Matrix.mul_apply]
  rw [hproduct]
  exact FiniteNetwork.consecutiveMatrixProduct_entry_nonneg
    matrixSchedule t k (fun s _ => hA (t + s)) i j

/-- The block-minorization core of Lemma 4.2.  Under exactly the paper's
positive-diagonal, uniform-positive-weight, and per-time strong-connectivity
hypotheses, every entry of a `max 1 (n-1)` consecutive product is at least
`a ^ max 1 (n-1)`. -/
theorem windowProduct_entry_lowerBound
    (A : ℕ → NodeMatrix Node) (a : ℝ)
    (ha : 0 < a)
    (hA_nonneg : ∀ s : ℕ, ∀ i j : Node, 0 ≤ A s i j)
    (hA_diag : ∀ s : ℕ, PositiveDiagonal (Node := Node) (A s))
    (hA_lower : ∀ s : ℕ, PositiveEntriesLowerBounded (Node := Node) a (A s))
    (hA_conn : ∀ s : ℕ, StronglyConnectedPositiveGraph (Node := Node) (A s))
    (t : ℕ) (i j : Node) :
    a ^ max 1 (nodeCount (Node := Node) - 1) ≤
      consecutiveProduct (Node := Node) A t
        (max 1 (nodeCount (Node := Node) - 1)) i j := by
  classical
  simpa only [nodeCount, PositiveDiagonal, PositiveEntriesLowerBounded,
    StronglyConnectedPositiveGraph, consecutiveProduct_eq_finiteNetwork] using
      FiniteNetwork.consecutiveMatrixProduct_entry_lowerBound_of_stronglyConnected
        A a (le_of_lt ha) t
        (fun q _ => hA_nonneg (t + q))
        (fun q _ => hA_diag (t + q))
        (fun q _ => hA_lower (t + q))
        (fun q _ => hA_conn (t + q)) i j

/-- Direct pull-product consumer of `windowProduct_entry_lowerBound`. -/
theorem pullLiftProduct_window_entry_lowerBound (t : ℕ) (i j : Node) :
    setup.minPositiveWeight ^ max 1 (nodeCount (Node := Node) - 1) ≤
      setup.pullLiftProduct t (max 1 (nodeCount (Node := Node) - 1)) i j := by
  rw [setup.pullLiftProduct_eq_consecutiveProduct]
  exact windowProduct_entry_lowerBound setup.C setup.minPositiveWeight
    setup.minPositiveWeight_pos
    (fun s => (setup.C_columnStochastic s).1)
    setup.C_positiveDiagonal setup.C_positiveEntriesLowerBounded
    setup.C_stronglyConnected t i j

/-- Direct push-product consumer of `windowProduct_entry_lowerBound`. -/
theorem pushLiftProduct_window_entry_lowerBound (t : ℕ) (i j : Node) :
    setup.minPositiveWeight ^ max 1 (nodeCount (Node := Node) - 1) ≤
      setup.pushLiftProduct t (max 1 (nodeCount (Node := Node) - 1)) i j := by
  rw [setup.pushLiftProduct_eq_consecutiveProduct]
  exact windowProduct_entry_lowerBound setup.R setup.minPositiveWeight
    setup.minPositiveWeight_pos
    (fun s => (setup.R_rowStochastic s).1)
    setup.R_positiveDiagonal setup.R_positiveEntriesLowerBounded
    setup.R_stronglyConnected t i j

theorem matrixMul_stronglyConnected_of_left
    {A B : NodeMatrix Node}
    (hA_nonneg : ∀ i j : Node, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Node, 0 ≤ B i j)
    (hA_conn : StronglyConnectedPositiveGraph (Node := Node) A)
    (hB_diag : PositiveDiagonal (Node := Node) B) :
    StronglyConnectedPositiveGraph (Node := Node)
      (matrixMul (Node := Node) A B) := by
  simpa only [StronglyConnectedPositiveGraph, PositiveDiagonal, matrixMul,
    Matrix.mul_apply] using
    FiniteNetwork.IsStronglyConnectedPositiveSupport.mul_of_right_positiveDiagonal
      hA_nonneg hB_nonneg hA_conn hB_diag

theorem pushLiftProduct_network_spec (t j : ℕ) :
    RowStochastic (Node := Node) (setup.pushLiftProduct t j) ∧
      PositiveDiagonal (Node := Node) (setup.pushLiftProduct t j) := by
  induction j with
  | zero =>
      exact ⟨identityMatrix_rowStochastic, identityMatrix_positiveDiagonal⟩
  | succ j ih =>
      rw [pushLiftProduct]
      exact ⟨matrixMul_rowStochastic (setup.R_rowStochastic (t + j)) ih.1,
        matrixMul_positiveDiagonal
          (setup.R_rowStochastic (t + j)).1 ih.1.1
          (setup.R_positiveDiagonal (t + j)) ih.2⟩

theorem pullLiftProduct_network_spec (t j : ℕ) :
    ColumnStochastic (Node := Node) (setup.pullLiftProduct t j) ∧
      PositiveDiagonal (Node := Node) (setup.pullLiftProduct t j) := by
  induction j with
  | zero =>
      exact ⟨identityMatrix_columnStochastic, identityMatrix_positiveDiagonal⟩
  | succ j ih =>
      rw [pullLiftProduct]
      exact ⟨matrixMul_columnStochastic (setup.C_columnStochastic (t + j)) ih.1,
        matrixMul_positiveDiagonal
          (setup.C_columnStochastic (t + j)).1 ih.1.1
          (setup.C_positiveDiagonal (t + j)) ih.2⟩

theorem period_products_network_spec (t : ℕ) :
    RowStochastic (Node := Node) (setup.pushLiftProduct t setup.period) ∧
      StronglyConnectedPositiveGraph (Node := Node)
        (setup.pushLiftProduct t setup.period) ∧
      ColumnStochastic (Node := Node) (setup.pullLiftProduct t setup.period) ∧
      StronglyConnectedPositiveGraph (Node := Node)
        (setup.pullLiftProduct t setup.period) := by
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt setup.period_pos)
  rw [hp]
  have hpush := setup.pushLiftProduct_network_spec t p
  have hpull := setup.pullLiftProduct_network_spec t p
  simp only [pushLiftProduct, pullLiftProduct]
  refine ⟨matrixMul_rowStochastic (setup.R_rowStochastic (t + p)) hpush.1, ?_,
    matrixMul_columnStochastic (setup.C_columnStochastic (t + p)) hpull.1, ?_⟩
  · exact matrixMul_stronglyConnected_of_left
      (setup.R_rowStochastic (t + p)).1 hpush.1.1
      (setup.R_stronglyConnected (t + p)) hpush.2
  · exact matrixMul_stronglyConnected_of_left
      (setup.C_columnStochastic (t + p)).1 hpull.1.1
      (setup.C_stronglyConnected (t + p)) hpull.2

theorem rowMulMatrix_mem_stdSimplex {A : NodeMatrix Node}
    (hA : RowStochastic (Node := Node) A) {w : RowVector Node}
    (hw : w ∈ stdSimplex ℝ Node) :
    rowMulMatrix (Node := Node) w A ∈ stdSimplex ℝ Node := by
  classical
  simpa only [rowMulMatrix, Matrix.vecMul, dotProduct] using
    Matrix.vecMul_mem_stdSimplex_of_mem_rowStochastic
      ((Matrix.mem_rowStochastic_iff_sum).2 hA) hw

theorem rowStochastic_exists_normalized_nonnegative_stationary
    (A : NodeMatrix Node) (hA : RowStochastic (Node := Node) A) :
    ∃ w : RowVector Node,
      w ∈ stdSimplex ℝ Node ∧ rowMulMatrix (Node := Node) w A = w := by
  classical
  simpa only [rowMulMatrix, Matrix.vecMul, dotProduct] using
    Matrix.exists_mem_stdSimplex_vecMul_eq_self_of_mem_rowStochastic A
      ((Matrix.mem_rowStochastic_iff_sum).2 hA)

theorem stationary_mem_stdSimplex_strictlyPositive
    (A : NodeMatrix Node)
    (hA : RowStochastic (Node := Node) A)
    (hconn : StronglyConnectedPositiveGraph (Node := Node) A)
    {w : RowVector Node} (hw : w ∈ stdSimplex ℝ Node)
    (hstationary : rowMulMatrix (Node := Node) w A = w) :
    ∀ i : Node, 0 < w i := by
  classical
  exact Matrix.strictlyPositive_of_mem_stdSimplex_vecMul_eq_self_of_irreducible
    A hA.1 hconn hw (by simpa [rowMulMatrix, Matrix.vecMul, dotProduct] using hstationary)

theorem stationary_nonnegative_eq_zero_of_zero_coordinate
    (A : NodeMatrix Node)
    (hA : RowStochastic (Node := Node) A)
    (hconn : StronglyConnectedPositiveGraph (Node := Node) A)
    {d : RowVector Node} (hd_nonneg : ∀ i : Node, 0 ≤ d i)
    (hstationary : rowMulMatrix (Node := Node) d A = d)
    {i0 : Node} (hi0 : d i0 = 0) : d = 0 := by
  classical
  exact Matrix.eq_zero_of_nonnegative_vecMul_eq_self_of_irreducible_of_apply_eq_zero
    A hA.1 hconn hd_nonneg
      (by simpa [rowMulMatrix, Matrix.vecMul, dotProduct] using hstationary) hi0

theorem stationary_mem_stdSimplex_unique
    (A : NodeMatrix Node)
    (hA : RowStochastic (Node := Node) A)
    (hconn : StronglyConnectedPositiveGraph (Node := Node) A)
    {w z : RowVector Node} (hw : w ∈ stdSimplex ℝ Node)
    (hz : z ∈ stdSimplex ℝ Node)
    (hwstationary : rowMulMatrix (Node := Node) w A = w)
    (hzstationary : rowMulMatrix (Node := Node) z A = z) : w = z := by
  classical
  exact Matrix.eq_of_mem_stdSimplex_vecMul_eq_self_of_irreducible
    A hA.1 hconn hw hz
    (by simpa [rowMulMatrix, Matrix.vecMul, dotProduct] using hwstationary)
    (by simpa [rowMulMatrix, Matrix.vecMul, dotProduct] using hzstationary)

theorem rowStochastic_stronglyConnected_existsUnique_positive_stationary
    (A : NodeMatrix Node)
    (hA : RowStochastic (Node := Node) A)
    (hconn : StronglyConnectedPositiveGraph (Node := Node) A) :
    ∃! w : RowVector Node,
      (∀ i : Node, 0 < w i) ∧ rowSum (Node := Node) w = 1 ∧
        rowMulMatrix (Node := Node) w A = w := by
  classical
  simpa only [rowSum, rowMulMatrix, Matrix.vecMul, dotProduct] using
    Matrix.existsUnique_strictlyPositive_normalized_vecMul_eq_self_of_irreducible
      A ((Matrix.mem_rowStochastic_iff_sum).2 hA) hconn

theorem columnStochastic_stronglyConnected_existsUnique_positive_stationary
    (A : NodeMatrix Node)
    (hA : ColumnStochastic (Node := Node) A)
    (hconn : StronglyConnectedPositiveGraph (Node := Node) A) :
    ∃! v : RowVector Node,
      (∀ i : Node, 0 < v i) ∧ rowSum (Node := Node) v = 1 ∧
        matrixMulVector (Node := Node) A v = v := by
  classical
  simpa only [rowSum, matrixMulVector, Matrix.mulVec, dotProduct] using
    Matrix.existsUnique_strictlyPositive_normalized_mulVec_eq_self_of_irreducible
      A ((Matrix.mem_colStochastic_iff_sum).2 hA) hconn

theorem phase_stationary_vectors_direct :
    (∀ t : ℕ, ∃! w : RowVector Node,
      (∀ i : Node, 0 < w i) ∧ rowSum (Node := Node) w = 1 ∧
        rowMulMatrix (Node := Node) w
          (setup.pushLiftProduct t setup.period) = w) ∧
    (∀ t : ℕ, ∃! v : RowVector Node,
      (∀ i : Node, 0 < v i) ∧ rowSum (Node := Node) v = 1 ∧
        matrixMulVector (Node := Node)
          (setup.pullLiftProduct t setup.period) v = v) := by
  constructor
  · intro t
    exact rowStochastic_stronglyConnected_existsUnique_positive_stationary
      (setup.pushLiftProduct t setup.period)
      (setup.period_products_network_spec t).1
      (setup.period_products_network_spec t).2.1
  · intro t
    exact columnStochastic_stronglyConnected_existsUnique_positive_stationary
      (setup.pullLiftProduct t setup.period)
      (setup.period_products_network_spec t).2.2.1
      (setup.period_products_network_spec t).2.2.2

theorem matrixMul_identity_left (A : NodeMatrix Node) :
    matrixMul (Node := Node) (identityMatrix (Node := Node)) A = A := by
  classical
  funext i j
  simp [matrixMul, identityMatrix]

theorem matrixMul_identity_right (A : NodeMatrix Node) :
    matrixMul (Node := Node) A (identityMatrix (Node := Node)) = A := by
  classical
  funext i j
  simp [matrixMul, identityMatrix]

theorem matrixMul_assoc_local (A B C : NodeMatrix Node) :
    matrixMul (Node := Node) A (matrixMul (Node := Node) B C) =
      matrixMul (Node := Node) (matrixMul (Node := Node) A B) C := by
  classical
  funext i l
  simp only [matrixMul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rowMulMatrix_matrixMul (w : RowVector Node) (A B : NodeMatrix Node) :
    rowMulMatrix (Node := Node) (rowMulMatrix (Node := Node) w A) B =
      rowMulMatrix (Node := Node) w (matrixMul (Node := Node) A B) := by
  classical
  funext k
  simp only [rowMulMatrix, matrixMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixMulVector_matrixMul (A B : NodeMatrix Node) (v : RowVector Node) :
    matrixMulVector (Node := Node) (matrixMul (Node := Node) A B) v =
      matrixMulVector (Node := Node) A (matrixMulVector (Node := Node) B v) := by
  classical
  funext i
  simp only [matrixMulVector, matrixMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem pushLiftProduct_succ_eq_right (t j : ℕ) :
    setup.pushLiftProduct t (j + 1) =
      matrixMul (Node := Node) (setup.pushLiftProduct (t + 1) j) (setup.R t) := by
  induction j with
  | zero =>
      simp [pushLiftProduct, matrixMul_identity_left, matrixMul_identity_right]
  | succ j ih =>
      change matrixMul (Node := Node) (setup.R (t + (j + 1)))
          (setup.pushLiftProduct t (j + 1)) =
        matrixMul (Node := Node)
          (matrixMul (Node := Node) (setup.R (t + 1 + j))
            (setup.pushLiftProduct (t + 1) j)) (setup.R t)
      rw [ih]
      rw [← matrixMul_assoc_local]
      congr 2
      omega

theorem pullLiftProduct_succ_eq_right (t j : ℕ) :
    setup.pullLiftProduct t (j + 1) =
      matrixMul (Node := Node) (setup.pullLiftProduct (t + 1) j) (setup.C t) := by
  induction j with
  | zero =>
      simp [pullLiftProduct, matrixMul_identity_left, matrixMul_identity_right]
  | succ j ih =>
      change matrixMul (Node := Node) (setup.C (t + (j + 1)))
          (setup.pullLiftProduct t (j + 1)) =
        matrixMul (Node := Node)
          (matrixMul (Node := Node) (setup.C (t + 1 + j))
            (setup.pullLiftProduct (t + 1) j)) (setup.C t)
      rw [ih]
      rw [← matrixMul_assoc_local]
      congr 2
      omega

theorem pullLiftProduct_add (t j k : ℕ) :
    setup.pullLiftProduct t (j + k) =
      matrixMul (Node := Node) (setup.pullLiftProduct (t + j) k)
        (setup.pullLiftProduct t j) := by
  induction k with
  | zero => simp [pullLiftProduct, matrixMul_identity_left]
  | succ k ih =>
      rw [Nat.add_succ, pullLiftProduct, ih, matrixMul_assoc_local]
      rw [pullLiftProduct]
      congr 2
      congr 1
      omega

theorem columnStochastic_leftMul_sum_eq_sum
    {A : NodeMatrix Node} (hA : ColumnStochastic (Node := Node) A)
    (X : State Node E) :
    ∑ i : Node, leftMul (Node := Node) (E := E) A X i =
      ∑ j : Node, X j := by
  classical
  exact Matrix.sum_smulVec_of_mem_colStochastic X (Matrix.mem_colStochastic_iff_sum.mpr hA)

theorem pullLiftProduct_leftMul_zeroSum
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    (t j : ℕ) (W : ZeroSumState Node F) :
    ∑ i : Node,
        leftMul (Node := Node) (E := F) (setup.pullLiftProduct t j) W.1 i = 0 := by
  classical
  exact FiniteNetwork.ZeroSumState.smulVec_mem_of_mem_colStochastic W
    (Matrix.mem_colStochastic_iff_sum.mpr (setup.pullLiftProduct_network_spec t j).1)

/- The finite `ℓ¹` norm used in the column Dobrushin argument from Lemma 4.2. -/
noncomputable def stateL1Norm
    {E : Type*} [NormedAddCommGroup E] (X : State Node E) : ℝ :=
  FiniteNetwork.stateL1Norm X

/- A column-stochastic matrix is nonexpansive for the state `ℓ¹` norm. -/
theorem columnStochastic_stateL1Norm_leftMul_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    {A : NodeMatrix Node}
    (hA : ColumnStochastic (Node := Node) A) (X : State Node F) :
    stateL1Norm (Node := Node)
        (leftMul (Node := Node) (E := F) A X) ≤
      stateL1Norm (Node := Node) X := by
  classical
  exact Matrix.stateL1Norm_smulVec_le_of_mem_colStochastic X (Matrix.mem_colStochastic_iff_sum.mpr hA)

/- Dobrushin decomposition on the zero-sum subspace for a column-minorized
matrix.  This is the column counterpart of the source-facing row theorem. -/
theorem columnMinorized_stateL1Norm_contraction
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    {A : NodeMatrix Node} {β : ℝ}
    (hA : ColumnStochastic (Node := Node) A)
    (hβ : ∀ i j : Node, β ≤ A i j)
    (W : ZeroSumState Node F) :
    stateL1Norm (Node := Node)
        (leftMul (Node := Node) (E := F) A W.1) ≤
      (1 - (nodeCount (Node := Node) : ℝ) * β) *
        stateL1Norm (Node := Node) W.1 := by
  classical
  simpa only [stateL1Norm, leftMul, nodeCount] using
    Matrix.stateL1Norm_smulVec_le_one_sub_card_mul_of_mem_colStochastic_of_minorized
      (A := A) (beta := β) (Matrix.mem_colStochastic_iff_sum.mpr hA) hβ W

theorem pullLiftProduct_window_stateL1Norm_contraction
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    (t : ℕ) (W : ZeroSumState Node F) :
    stateL1Norm (Node := Node)
        (leftMul (Node := Node) (E := F)
          (setup.pullLiftProduct t (contractionWindow (Node := Node))) W.1) ≤
      setup.contractionDelta * stateL1Norm (Node := Node) W.1 := by
  have hminor := columnMinorized_stateL1Norm_contraction
    (Node := Node)
    (setup.pullLiftProduct_network_spec t (contractionWindow (Node := Node))).1
    (by
      intro i j
      simpa [contractionWindow] using
        setup.pullLiftProduct_window_entry_lowerBound t i j)
    W
  exact hminor.trans (mul_le_mul_of_nonneg_right
    (le_max_right (1 / 2)
      (1 - (nodeCount (Node := Node) : ℝ) *
        setup.minPositiveWeight ^ contractionWindow (Node := Node)))
    (by exact Finset.sum_nonneg fun _ _ => norm_nonneg _))

/-- A product of node matrices acts by successive left actions. -/
theorem leftMul_matrixMul
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    (A B : NodeMatrix Node) (X : State Node F) :
    leftMul (Node := Node) (E := F) (matrixMul (Node := Node) A B) X =
      leftMul (Node := Node) (E := F) A
        (leftMul (Node := Node) (E := F) B X) := by
  classical
  funext i
  simp only [leftMul, Matrix.smulVec_apply, matrixMul, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

theorem pullLiftProduct_stateL1Norm_rate
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    (hdelta_pos : 0 < setup.contractionDelta)
    (hdelta_lt : setup.contractionDelta < 1) :
    ∀ (t j : ℕ) (W : ZeroSumState Node F),
      stateL1Norm (Node := Node)
          (leftMul (Node := Node) (E := F) (setup.pullLiftProduct t j) W.1) ≤
        setup.contractionDelta⁻¹ * setup.contractionRate ^ j *
          stateL1Norm (Node := Node) W.1 := by
  classical
  simpa only [leftMul, setup.pullLiftProduct_eq_consecutiveProduct,
    consecutiveProduct_eq_finiteNetwork] using
    (FiniteNetwork.consecutiveMatrixProduct_stateL1Norm_le_geometric_of_block_contraction
      (A := setup.C) (ell := contractionWindow (Node := Node))
      (delta := setup.contractionDelta) (rate := setup.contractionRate)
      (by simp [contractionWindow]) hdelta_pos hdelta_lt.le
      setup.contractionRate_nonneg
      (by
        rw [contractionRate]
        exact Real.rpow_inv_natCast_pow hdelta_pos.le
          (Nat.ne_of_gt (by simp [contractionWindow])))
      (fun s => Matrix.mem_colStochastic_iff_sum.mpr (setup.C_columnStochastic s))
      (by
        intro s W
        simpa only [leftMul, setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork] using
          setup.pullLiftProduct_window_stateL1Norm_contraction s W))

theorem pushLiftProduct_cyclic (t : ℕ) :
    matrixMul (Node := Node) (setup.R t)
        (setup.pushLiftProduct t setup.period) =
      matrixMul (Node := Node) (setup.pushLiftProduct (t + 1) setup.period)
        (setup.R t) := by
  classical
  funext i k
  simpa only [matrixMul, setup.pushLiftProduct_eq_consecutiveProduct,
    consecutiveProduct_eq_finiteNetwork, Matrix.mul_apply] using
      congrFun (congrFun
        (FiniteNetwork.mul_consecutiveProduct_eq_consecutiveProduct_succ_mul_of_endpoint_eq
          (M := Matrix Node Node ℝ) setup.R setup.period t
          (setup.R_periodic t)) i) k

theorem pullLiftProduct_cyclic (t : ℕ) :
    matrixMul (Node := Node) (setup.C t)
        (setup.pullLiftProduct t setup.period) =
      matrixMul (Node := Node) (setup.pullLiftProduct (t + 1) setup.period)
        (setup.C t) := by
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt setup.period_pos)
  rw [hp, setup.pullLiftProduct_succ_eq_right t p]
  simp only [pullLiftProduct]
  have hC := setup.C_periodic t
  rw [hp] at hC
  have hC' : setup.C (t + 1 + p) = setup.C t := by
    rw [show t + 1 + p = t + (p + 1) by omega]
    exact hC
  rw [hC']
  rw [matrixMul_assoc_local]

theorem pushLiftProduct_periodic_start (t j : ℕ) :
    setup.pushLiftProduct (t + setup.period) j = setup.pushLiftProduct t j := by
  classical
  simpa only [setup.pushLiftProduct_eq_consecutiveProduct,
    consecutiveProduct_eq_finiteNetwork] using
      (FiniteNetwork.consecutiveProduct_add_period_eq_of_periodic
        (M := Matrix Node Node ℝ) setup.R setup.period t j setup.R_periodic)

theorem pullLiftProduct_periodic_start (t j : ℕ) :
    setup.pullLiftProduct (t + setup.period) j = setup.pullLiftProduct t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pullLiftProduct]
      rw [ih]
      have hC := setup.C_periodic (t + j)
      rw [show t + setup.period + j = t + j + setup.period by omega]
      rw [hC]

theorem matrixMulVector_mem_stdSimplex {A : NodeMatrix Node}
    (hA : ColumnStochastic (Node := Node) A) {v : RowVector Node}
    (hv : v ∈ stdSimplex ℝ Node) :
    matrixMulVector (Node := Node) A v ∈ stdSimplex ℝ Node := by
  classical
  simpa only [matrixMulVector, Matrix.mulVec, dotProduct] using
    Matrix.mulVec_mem_stdSimplex_of_mem_colStochastic
      (Matrix.mem_colStochastic_iff_sum.mpr hA) hv

theorem competitor_push_product (w : ℕ → RowVector Node)
    (hEq : ∀ (t : ℕ),
      rowMulMatrix (Node := Node) (w (t + 1)) (setup.R t) = w t)
    (t j : ℕ) :
    rowMulMatrix (Node := Node) (w (t + j)) (setup.pushLiftProduct t j) = w t := by
  classical
  let A : ℕ → Matrix Node Node ℝ := setup.R
  have hproduct : setup.pushLiftProduct t j =
      FiniteNetwork.consecutiveProduct A t j := by
    induction j with
    | zero =>
        simp only [pushLiftProduct, FiniteNetwork.consecutiveProduct]
        unfold identityMatrix
        funext i k
        rw [Matrix.one_apply]
    | succ j ih =>
        simp only [pushLiftProduct, FiniteNetwork.consecutiveProduct]
        rw [ih]
        unfold matrixMul
        funext i k
        rw [Matrix.mul_apply]
  rw [hproduct]
  unfold rowMulMatrix
  simpa only [Matrix.vecMul, dotProduct] using
    (FiniteNetwork.vecMul_consecutiveMatrixProduct_eq_of_step
      A w t j (fun k _ => hEq (t + k)))

theorem competitor_pull_product (v : ℕ → RowVector Node)
    (hEq : ∀ (t : ℕ),
      matrixMulVector (Node := Node) (setup.C t) (v t) = v (t + 1))
    (t j : ℕ) :
    matrixMulVector (Node := Node) (setup.pullLiftProduct t j) (v t) = v (t + j) := by
  classical
  let A : ℕ → Matrix Node Node ℝ := setup.C
  have hproduct : setup.pullLiftProduct t j =
      FiniteNetwork.consecutiveProduct A t j := by
    induction j with
    | zero =>
        simp only [pullLiftProduct, FiniteNetwork.consecutiveProduct]
        unfold identityMatrix
        funext i k
        rw [Matrix.one_apply]
    | succ j ih =>
        simp only [pullLiftProduct, FiniteNetwork.consecutiveProduct]
        rw [ih]
        unfold matrixMul
        funext i k
        rw [Matrix.mul_apply]
  rw [hproduct]
  unfold matrixMulVector
  simpa only [Matrix.mulVec, dotProduct] using
    (FiniteNetwork.consecutiveProduct_mulVec_eq_of_step
      A v t j (fun k _ => hEq (t + k)))

theorem competitor_phase_stationary
    (other : (ℕ → RowVector Node) × (ℕ → RowVector Node))
    (hEq : setup.PerronSequencesEquations other)
    (hPer : setup.PerronSequencesPositivePeriodic other) :
    (∀ t : ℕ, rowMulMatrix (Node := Node) (other.1 t)
        (setup.pushLiftProduct t setup.period) = other.1 t) ∧
      (∀ t : ℕ, matrixMulVector (Node := Node)
        (setup.pullLiftProduct t setup.period) (other.2 t) = other.2 t) := by
  classical
  have hproduct (A : ℕ → Matrix Node Node ℝ) (t j : ℕ) :
      consecutiveProduct (Node := Node) A t j =
        FiniteNetwork.consecutiveProduct A t j := by
    induction j with
    | zero =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        unfold identityMatrix
        funext i k
        rw [Matrix.one_apply]
    | succ j ih =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        rw [ih]
        unfold matrixMul
        funext i k
        rw [Matrix.mul_apply]
  have h := FiniteNetwork.periodProduct_fixedPoints_of_step_recurrences_of_periodic
    setup.R setup.C setup.period other
    (fun t => funext (hEq.1 t)) (fun t => funext (hEq.2.2.1 t))
    hPer.2.2.1 hPer.2.2.2
  constructor
  · intro t
    rw [setup.pushLiftProduct_eq_consecutiveProduct, hproduct]
    unfold rowMulMatrix
    funext j
    simpa only [Matrix.vecMul, dotProduct] using congrFun (h.1 t) j
  · intro t
    rw [setup.pullLiftProduct_eq_consecutiveProduct, hproduct]
    unfold matrixMulVector
    funext i
    simpa only [Matrix.mulVec, dotProduct] using congrFun (h.2 t) i

/-- Source-derived existence of the unique positive periodic Perron sequences.
This is derived from the fixed exogenous periodic network in `#/assumptions/8`
and the Perron equations stated in `#/assumptions/9`; the proof is left to the
prover phase. -/
theorem exists_perronSequences :
    ∃ seqs : (ℕ → RowVector Node) × (ℕ → RowVector Node),
      setup.PerronSequencesSpec seqs := by
  classical
  obtain ⟨seqs, hseqs⟩ :=
    FiniteNetwork.exists_unique_positive_periodic_push_pull_perron_sequences
      setup.R setup.C setup.period setup.period_pos
      (fun t => Matrix.mem_rowStochastic_iff_sum.mpr (setup.R_rowStochastic t))
      (fun t => Matrix.mem_colStochastic_iff_sum.mpr (setup.C_columnStochastic t))
      setup.R_positiveDiagonal setup.C_positiveDiagonal
      setup.R_stronglyConnected setup.C_stronglyConnected
      setup.R_periodic setup.C_periodic
  have hspec : setup.PerronSequencesSpec seqs := by
    simpa only [PerronSequencesSpec, rowMulMatrix, matrixMulVector, rowSum,
      Matrix.vecMul, Matrix.mulVec, dotProduct] using hseqs
  refine ⟨seqs, hspec.1, ?_, hspec.2.2⟩
  refine ⟨?_, ?_, hspec.2.1.2.2⟩
  intro t j
  rw [← hspec.1.1 t j]
  have hqpos := Matrix.vecMul_pos_of_nonneg_of_pos_diagonal
      (setup.R t) (seqs.1 (t + 1))
      (setup.R_rowStochastic t).1 (setup.R_positiveDiagonal t)
      (hspec.2.1.1 (t + 1))
  simpa only [rowMulMatrix] using hqpos j
  intro t i
  cases t with
  | zero => exact hspec.2.1.2.1 0 i
  | succ t =>
      rw [← hspec.1.2.2.1 t i]
      have hqpos := Matrix.mulVec_pos_of_nonneg_of_pos_diagonal
        (setup.C t) (seqs.2 t)
        (setup.C_columnStochastic t).1 (setup.C_positiveDiagonal t)
        (hspec.2.1.2.1 t)
      simpa only [matrixMulVector, Matrix.mulVec, dotProduct] using hqpos i

/-- Canonically selected periodic Perron sequences from
`#/assumptions/9`, chosen from the source-derived unique positive periodic
solution. -/
noncomputable def perronSequences :
    (ℕ → RowVector Node) × (ℕ → RowVector Node) :=
  FiniteNetwork.periodicPushPullPerronSequences
    setup.R setup.C setup.period setup.exists_perronSequences

/-- Left absolute-probability sequence `π_t`. -/
noncomputable def perronLeft (t : ℕ) : RowVector Node :=
  setup.perronSequences.1 t

/-- Right Perron sequence `v_t`. -/
noncomputable def perronRight (t : ℕ) : RowVector Node :=
  setup.perronSequences.2 t

/-- The selected Perron sequences satisfy their defining equations. -/
theorem perronSequences_spec :
    setup.PerronSequencesSpec setup.perronSequences :=
  Classical.choose_spec setup.exists_perronSequences

/-- The defining left-Perron equation `π_{t+1}^T R_t = π_t^T`. -/
theorem perronLeft_mul_R (t : ℕ) (j : Node) :
    rowMulMatrix (Node := Node) (setup.perronLeft (t + 1)) (setup.R t) j =
      setup.perronLeft t j := by
  exact setup.perronSequences_spec.1.1 t j

/-- The defining normalization `π_t^T 1 = 1`. -/
theorem perronLeft_sum (t : ℕ) :
    rowSum (Node := Node) (setup.perronLeft t) = 1 := by
  exact setup.perronSequences_spec.1.2.1 t

/-- The defining right-Perron equation `v_{t+1}=C_t v_t`. -/
theorem C_mul_perronRight (t : ℕ) (i : Node) :
    matrixMulVector (Node := Node) (setup.C t) (setup.perronRight t) i =
      setup.perronRight (t + 1) i := by
  exact setup.perronSequences_spec.1.2.2.1 t i

/-- The defining normalization `1^T v_t = 1`. -/
theorem perronRight_sum (t : ℕ) :
    rowSum (Node := Node) (setup.perronRight t) = 1 := by
  exact setup.perronSequences_spec.1.2.2.2 t

/-- Positivity of the selected left absolute-probability sequence. -/
theorem perronLeft_pos (t : ℕ) (i : Node) :
    0 < setup.perronLeft t i := by
  exact setup.perronSequences_spec.2.1.1 t i

theorem perronLeft_weightedState_norm_le_stateL1Norm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [FiniteDimensional ℝ F]
    (t : ℕ) (X : State Node F) :
    ‖weightedState (Node := Node) (E := F) (setup.perronLeft t) X‖ ≤
      stateL1Norm (Node := Node) (E := F) X := by
  exact norm_finset_sum_smul_le_sum_norm_of_mem_stdSimplex
    (setup.perronLeft t) X
    ⟨fun i => (setup.perronLeft_pos t i).le,
      by simpa [rowSum] using setup.perronLeft_sum t⟩

/-- Positivity of the selected right Perron sequence. -/
theorem perronRight_pos (t : ℕ) (i : Node) :
    0 < setup.perronRight t i := by
  exact setup.perronSequences_spec.2.1.2.1 t i

/-- Periodicity of the selected left absolute-probability sequence. -/
theorem perronLeft_periodic (t : ℕ) :
    setup.perronLeft (t + setup.period) = setup.perronLeft t := by
  exact setup.perronSequences_spec.2.1.2.2.1 t

/-- Periodicity of the selected right Perron sequence. -/
theorem perronRight_periodic (t : ℕ) :
    setup.perronRight (t + setup.period) = setup.perronRight t := by
  exact setup.perronSequences_spec.2.1.2.2.2 t

/-- Uniqueness of the source Perron object among positive periodic solutions of
(4.1). -/
theorem perronSequences_unique
    (other : (ℕ → RowVector Node) × (ℕ → RowVector Node))
    (heq : setup.PerronSequencesEquations other)
    (hposper : setup.PerronSequencesPositivePeriodic other) :
    other = setup.perronSequences := by
  exact setup.perronSequences_spec.2.2 other heq hposper

/-- Pull-matrix product `C_{r+j-1:r+1}` used in the influence series from
`#/assumptions/11` (`eq:bdef / (4.5)`). The zero-length product is the
identity; successor length appends the next time-indexed pull matrix on the
left. -/
noncomputable def pullWindowProduct (r : ℕ) : ℕ → NodeMatrix Node
  | 0 => identityMatrix (Node := Node)
  | j + 1 => matrixMul (Node := Node) (setup.C (r + j + 1))
      (pullWindowProduct r j)

/- The pull product in the influence tail is based one time step later. -/
theorem pullWindowProduct_eq_pullLiftProduct_succ (t j : ℕ) :
    setup.pullWindowProduct t j = setup.pullLiftProduct (t + 1) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pullWindowProduct, pullLiftProduct]
      rw [ih]
      congr 2
      omega

/-- The `j`th tail term in the influence-vector series from
`#/assumptions/11`, with source index `j+1`. -/
noncomputable def influenceSeriesTerm (r j : ℕ) : RowVector Node :=
  by classical exact FiniteNetwork.periodicInfluenceSeriesTerm setup.C setup.perronLeft r j

theorem influenceSeriesTerm_apply_as_weighted_column
    (r j : ℕ) (i : Node) :
    setup.influenceSeriesTerm r j i =
      weightedState (Node := Node) (E := ℝ) (setup.perronLeft (r + j + 2))
        (leftMul (Node := Node) (E := ℝ) (setup.pullLiftProduct (r + 1) j)
          (fun k : Node => setup.C r k i - identityMatrix (Node := Node) k i)) := by
  classical
  simpa only [influenceSeriesTerm,
    ← consecutiveProduct_eq_finiteNetwork (Node := Node) setup.C (r + 1) j,
    ← setup.pullLiftProduct_eq_consecutiveProduct (r + 1) j, dotProduct,
    weightedState, leftMul, Matrix.mulVec, Matrix.smulVec_apply, smul_eq_mul,
    identityMatrix, Matrix.one_apply] using
    (FiniteNetwork.periodicInfluenceSeriesTerm_apply setup.C setup.perronLeft r j i)

/-- Periodic influence vector `b_r` from
`#/assumptions/11`: `b_r^T := pi_{r+1}^T + sum_{j>=1} pi_{r+j+1}^T
C_{r+j-1:r+1}(C_r-I)`. -/
noncomputable def influence (r : ℕ) : RowVector Node :=
  setup.perronLeft (r + 1) + ∑' j : ℕ, setup.influenceSeriesTerm r j

/-- Source-derived absolute convergence of the influence series. -/
theorem influenceSeries_summable (r : ℕ) :
    Summable (fun j : ℕ => setup.influenceSeriesTerm r j) := by
  classical
  simpa only [influenceSeriesTerm] using
    (FiniteNetwork.periodicInfluenceSeries_summable_of_geometric_contraction
      setup.C setup.perronLeft setup.contractionDelta setup.contractionRate r
      (setup.C_column_sum r)
      (fun j => ⟨fun i => (setup.perronLeft_pos (r + j + 2) i).le,
        by simpa [rowSum] using setup.perronLeft_sum (r + j + 2)⟩)
      setup.contractionRate_nonneg setup.contractionRate_lt_one
      (fun j W => by
        have h := pullLiftProduct_stateL1Norm_rate (setup := setup) (F := ℝ)
          setup.contractionDelta_pos setup.contractionDelta_lt_one (r + 1) j W
        rw [setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork] at h
        simpa only [stateL1Norm, leftMul] using h))

/-- Influence vector source-form unfolding. -/
theorem influence_eq_perron_add_tsum (r : ℕ) :
    setup.influence r =
      setup.perronLeft (r + 1) + ∑' j : ℕ, setup.influenceSeriesTerm r j := by
  rfl


/-- Average squared influence `q = p^{-1} sum_r ||b_r||^2` from
`#/assumptions/12` (`eq:neff / (4.6)`). -/
noncomputable def influenceSecondMoment : ℝ :=
  by
    let _backfill := FiniteNetwork.periodicInfluenceSecondMoment
      (fun r : Fin setup.period => setup.influence r.1)
    exact ((setup.period : ℝ)⁻¹) *
      ∑ r : Fin setup.period,
        rowNormSq (Node := Node) (setup.influence r.1)

/-- Effective-node count `n_eff = h^2 / q` from
`#/assumptions/12` (`eq:neff / (4.6)`). -/
noncomputable def effectiveNodeCount : ℝ :=
  FiniteNetwork.effectiveNodeCount (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) setup.influenceSecondMoment

/-- Perron overlap
`κ = p^{-1} sum_{r=0}^{p-1} π_{r+1}^T v_r` from Lemma 4.4. -/
noncomputable def averagePerronOverlap : ℝ :=
  FiniteNetwork.averagePeriodicPerronOverlap (p := setup.period) setup.perronLeft setup.perronRight

/-- Period-average influence row
`p^{-1} sum_{r=0}^{p-1} b_r^T`. -/
noncomputable def averageInfluence : RowVector Node :=
  fun i =>
    ((setup.period : ℝ)⁻¹) *
      ∑ r : Fin setup.period, setup.influence r.1 i

/-- Strict positivity of the phase-averaged Perron overlap in Lemma 4.4. -/
theorem averagePerronOverlap_pos :
    0 < setup.averagePerronOverlap := by
  simpa only [averagePerronOverlap] using
    (FiniteNetwork.averagePeriodicPerronOverlap_pos
      setup.perronLeft setup.perronRight setup.period_pos
      (fun r i => setup.perronLeft_pos (r.1 + 1) i)
      (fun r i => setup.perronRight_pos r.1 i))

/-- The scalar gain is the sum of the entries of the average influence row. -/
theorem influenceGain_eq_nodeCount_mul_averagePerronOverlap
    (havg : setup.averageInfluence =
      (fun _ : Node => setup.averagePerronOverlap)) :
    (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) =
      (nodeCount (Node := Node) : ℝ) * setup.averagePerronOverlap := by
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    div_eq_mul_inv, mul_comm, averageInfluence, rowSum, nodeCount] using
    (FiniteNetwork.periodicInfluenceGain_eq_card_mul_of_average_eq_const
      (b := fun r : Fin setup.period => setup.influence r.1)
      setup.averagePerronOverlap havg)

/-- Equality condition in Lemma 4.4: all `pn` entries `(b_r)_i` are equal. -/
def influenceEntriesAllEqual : Prop :=
  ∀ r s : Fin setup.period, ∀ i j : Node,
    setup.influence r.1 i = setup.influence s.1 j

/-- The `j`th term `π_{t+j+1}^T C_{t+j-1:t} W` in the corrected-lift series. -/
noncomputable def correctedLiftSeriesTerm (t j : ℕ)
    (W : ZeroSumState Node E) : E :=
  by
    classical
    exact FiniteNetwork.periodicCorrectedLiftSeriesTerm
      setup.C setup.perronLeft t j W

/-- Source-form unfolding of a corrected-lift summand. -/
theorem correctedLiftSeriesTerm_eq_weightedState (t j : ℕ)
    (W : ZeroSumState Node E) :
    setup.correctedLiftSeriesTerm t j W =
      weightedState (Node := Node) (E := E) (setup.perronLeft (t + j + 1))
        (leftMul (Node := Node) (E := E) (setup.pullLiftProduct t j) W.1) := by
  classical
  unfold correctedLiftSeriesTerm FiniteNetwork.periodicCorrectedLiftSeriesTerm
  rw [← consecutiveProduct_eq_finiteNetwork (Node := Node) setup.C t j]
  rw [← setup.pullLiftProduct_eq_consecutiveProduct t j]
  rfl

/-- Source-derived absolute convergence of the corrected-lift series on
`S = {W : 1^T W = 0}`. -/
theorem correctedLiftSeries_summable (t : ℕ) (W : ZeroSumState Node E) :
    Summable (fun j : ℕ => setup.correctedLiftSeriesTerm t j W) := by
  classical
  exact FiniteNetwork.periodicCorrectedLiftSeries_summable_of_geometric_contraction
    setup.C setup.perronLeft setup.contractionDelta setup.contractionRate t W
    (fun j => ⟨fun i => (setup.perronLeft_pos (t + j + 1) i).le,
      by simpa [rowSum] using setup.perronLeft_sum (t + j + 1)⟩)
    setup.contractionRate_nonneg setup.contractionRate_lt_one
    (fun j => by
      have h := pullLiftProduct_stateL1Norm_rate (setup := setup) (F := E)
        setup.contractionDelta_pos setup.contractionDelta_lt_one t j W
      rw [setup.pullLiftProduct_eq_consecutiveProduct,
        consecutiveProduct_eq_finiteNetwork] at h
      simpa only [stateL1Norm, leftMul] using h)

/-- Corrected lift `D_t^T W` from (5.1), defined only on the zero-sum
subspace `S`. -/
noncomputable def correctedLift (t : ℕ) (W : ZeroSumState Node E) : E :=
  by
    classical
    exact FiniteNetwork.periodicCorrectedLift setup.perronLeft
      (fun s j => FiniteNetwork.consecutiveProduct setup.C s j) t W

/-- Source-form unfolding of the corrected lift. -/
theorem correctedLift_eq_tsum (t : ℕ) (W : ZeroSumState Node E) :
    setup.correctedLift t W =
      ∑' j : ℕ, setup.correctedLiftSeriesTerm t j W := by
  rfl

/-- The corrected lift is bounded by the geometric product-contraction
majorant.  This is the analytic bridge used to transport finite-horizon `L²`
regularity through the infinite-series lift. -/
theorem correctedLift_norm_le_geometric
    (t : ℕ) (W : ZeroSumState Node E) :
    ‖setup.correctedLift t W‖ ≤
      (setup.contractionDelta⁻¹ *
          stateL1Norm (Node := Node) (E := E) W.1) *
        ∑' j : ℕ, setup.contractionRate ^ j := by
  classical
  simpa only [correctedLift, correctedLiftSeriesTerm,
    FiniteNetwork.periodicCorrectedLift_def,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm_def] using
    (FiniteNetwork.norm_periodicCorrectedLift_le_geometric
      setup.C setup.perronLeft setup.contractionDelta setup.contractionRate t W
      (fun j => ⟨fun i => (setup.perronLeft_pos (t + j + 1) i).le,
        by simpa [rowSum] using setup.perronLeft_sum (t + j + 1)⟩)
      setup.contractionRate_nonneg setup.contractionRate_lt_one
      (fun j => by
        have h := pullLiftProduct_stateL1Norm_rate (setup := setup) (F := E)
          setup.contractionDelta_pos setup.contractionDelta_lt_one t j W
        rw [setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork] at h
        simpa only [stateL1Norm, leftMul] using h))

theorem correctedLift_sub (t : ℕ)
    (W V : ZeroSumState Node E) :
    setup.correctedLift t
        ⟨W.1 - V.1, by
          change ∑ i : Node, (W.1 i - V.1 i) = 0
          rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩ =
      setup.correctedLift t W - setup.correctedLift t V := by
  classical
  simpa only [correctedLift, correctedLiftSeriesTerm,
    FiniteNetwork.periodicCorrectedLift_def,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm_def] using
    (FiniteNetwork.periodicCorrectedLift_sub setup.C setup.perronLeft t W V
      (by simpa only [correctedLiftSeriesTerm] using
        setup.correctedLiftSeries_summable t W)
      (by simpa only [correctedLiftSeriesTerm] using
        setup.correctedLiftSeries_summable t V))

/-- The corrected lift is Lipschitz on its zero-sum carrier.  This packages
the infinite-series regularity needed for finite-horizon `L²` transport. -/
theorem correctedLift_exists_lipschitz (t : ℕ) :
    ∃ K : NNReal, LipschitzWith K (setup.correctedLift t) := by
  classical
  simpa only [correctedLift, correctedLiftSeriesTerm,
    FiniteNetwork.periodicCorrectedLift_def,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm_def] using
    (FiniteNetwork.exists_lipschitzWith_periodicCorrectedLift
      setup.C setup.perronLeft setup.contractionDelta setup.contractionRate t
      (fun j => ⟨fun i => (setup.perronLeft_pos (t + j + 1) i).le,
        by simpa [rowSum] using setup.perronLeft_sum (t + j + 1)⟩)
      setup.contractionDelta_pos.le setup.contractionRate_nonneg
      setup.contractionRate_lt_one
      (fun W j => by
        have h := pullLiftProduct_stateL1Norm_rate (setup := setup) (F := E)
          setup.contractionDelta_pos setup.contractionDelta_lt_one t j W
        rw [setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork] at h
        simpa only [stateL1Norm, leftMul] using h))

/-- Coordinatewise `L²` regularity of a zero-sum random state is transported
through the corrected lift. -/
theorem correctedLift_comp_memLp_of_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} (t : ℕ) {W : Ω → ZeroSumState Node E}
    (hW : ∀ i : Node, MemLp (fun ω => (W ω).1 i) 2 μ) :
    MemLp (fun ω => setup.correctedLift t (W ω)) 2 μ := by
  obtain ⟨K, hK⟩ := setup.correctedLift_exists_lipschitz t
  exact memLp_comp_lipschitz_subtype_pi_of_coordinate_memLp
    μ _ W (setup.correctedLift t) 2 K (by
      change ∑ _i : Node, (0 : E) = 0
      simp) hW hK (by
      simp [correctedLift, correctedLiftSeriesTerm, weightedState, leftMul])

/-- The identity node matrix acts trivially on a distributed state. -/
theorem leftMul_identity (X : State Node E) :
    leftMul (Node := Node) (E := E) (identityMatrix (Node := Node)) X = X := by
  classical
  funext i
  simp [leftMul, identityMatrix]

/- Column-stochastic pull matrices preserve total mass. -/
theorem C_leftMul_sum_eq_sum (t : ℕ) (X : State Node E) :
    ∑ i : Node, leftMul (Node := Node) (E := E) (setup.C t) X i =
      ∑ j : Node, X j := by
  simp only [leftMul_apply]
  rw [Finset.sum_comm]
  calc
    ∑ j : Node, ∑ i : Node, setup.C t i j • X j =
        ∑ j : Node, (∑ i : Node, setup.C t i j) • X j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_smul]
    _ = ∑ j : Node, X j := by
      simp only [setup.C_column_sum t, one_smul]

/-- Column-stochastic pull matrices preserve the zero-sum subspace `S`. -/
theorem C_leftMul_zeroSum (t : ℕ) (W : ZeroSumState Node E) :
    ∑ i : Node, leftMul (Node := Node) (E := E) (setup.C t) W.1 i = 0 := by
  rw [setup.C_leftMul_sum_eq_sum t W.1]
  exact W.2

/-- Removing the first pull matrix from a positive-length corrected-lift
product transports the summand to the next time step. -/
theorem correctedLiftSeriesTerm_succ_transport
    (t j : ℕ) (W : ZeroSumState Node E) :
    setup.correctedLiftSeriesTerm t (j + 1) W =
      setup.correctedLiftSeriesTerm (t + 1) j
        ⟨leftMul (Node := Node) (E := E) (setup.C t) W.1,
          setup.C_leftMul_zeroSum t W⟩ := by
  classical
  exact FiniteNetwork.periodicCorrectedLiftSeriesTerm_succ_transport
    setup.C setup.perronLeft t j W (setup.C_leftMul_zeroSum t W)

/-- Poisson identity (5.2) for the corrected lift. -/
theorem correctedLift_poisson (t : ℕ) (W : ZeroSumState Node E) :
    setup.correctedLift t W =
      weightedState (Node := Node) (E := E) (setup.perronLeft (t + 1)) W.1 +
        setup.correctedLift (t + 1)
          ⟨leftMul (Node := Node) (E := E) (setup.C t) W.1,
            setup.C_leftMul_zeroSum t W⟩ := by
  classical
  simpa only [correctedLift, correctedLiftSeriesTerm, weightedState, leftMul,
    FiniteNetwork.periodicCorrectedLift_def,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm_def] using
    (FiniteNetwork.periodicCorrectedLift_poisson setup.C setup.perronLeft t W
      (setup.C_leftMul_zeroSum t W)
      (by simpa only [correctedLiftSeriesTerm] using
        setup.correctedLiftSeries_summable t W))

/- The difference between the phase-`t` right Perron vector and a coordinate
unit vector is a zero-sum state. -/
noncomputable def perronCoordinateError (t : ℕ) (i : Node) :
    ZeroSumState Node ℝ := by
  classical
  exact FiniteNetwork.normalizedCoordinateError (setup.perronRight t) i
    (by simpa [rowSum] using setup.perronRight_sum t)


/- Scalar specialization of the corrected-lift summand.  This is separate
from `correctedLiftSeriesTerm` because that public API is tied to the setup's
optimization space `E`, whereas influence coordinates are real-valued. -/
noncomputable def scalarCorrectedLiftSeriesTerm
    (t j : ℕ) (W : ZeroSumState Node ℝ) : ℝ :=
  weightedState (Node := Node) (E := ℝ) (setup.perronLeft (t + j + 1))
    (leftMul (Node := Node) (E := ℝ) (setup.pullLiftProduct t j) W.1)

theorem scalarCorrectedLiftSeries_summable
    (t : ℕ) (W : ZeroSumState Node ℝ) :
    Summable (fun j : ℕ => setup.scalarCorrectedLiftSeriesTerm t j W) := by
  have hgeom : Summable (fun j : ℕ => setup.contractionRate ^ j) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg setup.contractionRate_nonneg]
      exact setup.contractionRate_lt_one)
  apply Summable.of_norm_bounded
    (Summable.mul_left
      (setup.contractionDelta⁻¹ * stateL1Norm (Node := Node) (E := ℝ) W.1)
      hgeom)
  intro j
  unfold scalarCorrectedLiftSeriesTerm
  calc
    ‖weightedState (Node := Node) (E := ℝ) (setup.perronLeft (t + j + 1))
        (leftMul (Node := Node) (E := ℝ) (setup.pullLiftProduct t j) W.1)‖ ≤
      stateL1Norm (Node := Node) (E := ℝ)
        (leftMul (Node := Node) (E := ℝ) (setup.pullLiftProduct t j) W.1) :=
      setup.perronLeft_weightedState_norm_le_stateL1Norm _ _
    _ ≤ setup.contractionDelta⁻¹ * setup.contractionRate ^ j *
          stateL1Norm (Node := Node) (E := ℝ) W.1 :=
      pullLiftProduct_stateL1Norm_rate (setup := setup) (F := ℝ)
        setup.contractionDelta_pos setup.contractionDelta_lt_one t j W
    _ = (setup.contractionDelta⁻¹ *
          stateL1Norm (Node := Node) (E := ℝ) W.1) *
          setup.contractionRate ^ j := by ring

/- Scalar corrected lift used by the exact constant-input DC-gain bridge. -/
noncomputable def scalarCorrectedLift
    (t : ℕ) (W : ZeroSumState Node ℝ) : ℝ :=
  ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t j W

theorem scalarCorrectedLift_eq_tsum
    (t : ℕ) (W : ZeroSumState Node ℝ) :
    setup.scalarCorrectedLift t W =
      ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t j W := by
  rfl

theorem C_leftMul_zeroSum_real
    (t : ℕ) (W : ZeroSumState Node ℝ) :
    ∑ i : Node, leftMul (Node := Node) (E := ℝ) (setup.C t) W.1 i = 0 := by
  classical
  simp only [leftMul, Matrix.smulVec_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  calc
    ∑ j : Node, ∑ i : Node, setup.C t i j * W.1 j =
        ∑ j : Node, (∑ i : Node, setup.C t i j) * W.1 j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ j : Node, W.1 j := by
      simp only [setup.C_column_sum t, one_mul]
    _ = 0 := W.2

theorem scalarCorrectedLiftSeriesTerm_succ_transport
    (t j : ℕ) (W : ZeroSumState Node ℝ) :
    setup.scalarCorrectedLiftSeriesTerm t (j + 1) W =
      setup.scalarCorrectedLiftSeriesTerm (t + 1) j
        ⟨leftMul (Node := Node) (E := ℝ) (setup.C t) W.1,
          setup.C_leftMul_zeroSum_real t W⟩ := by
  unfold scalarCorrectedLiftSeriesTerm
  rw [setup.pullLiftProduct_succ_eq_right t j, leftMul_matrixMul]
  congr 2
  omega

theorem scalarCorrectedLift_poisson
    (t : ℕ) (W : ZeroSumState Node ℝ) :
    setup.scalarCorrectedLift t W =
      weightedState (Node := Node) (E := ℝ) (setup.perronLeft (t + 1)) W.1 +
        setup.scalarCorrectedLift (t + 1)
          ⟨leftMul (Node := Node) (E := ℝ) (setup.C t) W.1,
            setup.C_leftMul_zeroSum_real t W⟩ := by
  have hhead :
      setup.scalarCorrectedLiftSeriesTerm t 0 W =
        weightedState (Node := Node) (E := ℝ)
          (setup.perronLeft (t + 1)) W.1 := by
    classical
    unfold scalarCorrectedLiftSeriesTerm
    have hid : leftMul (Node := Node) (E := ℝ)
        (identityMatrix (Node := Node)) W.1 = W.1 := by
      funext i
      simp [leftMul, identityMatrix]
    change weightedState (Node := Node) (E := ℝ)
      (setup.perronLeft (t + 1))
      (leftMul (Node := Node) (E := ℝ)
        (identityMatrix (Node := Node)) W.1) = _
    rw [hid]
  calc
    setup.scalarCorrectedLift t W =
        ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t j W :=
      setup.scalarCorrectedLift_eq_tsum t W
    _ = setup.scalarCorrectedLiftSeriesTerm t 0 W +
          ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t (j + 1) W :=
      (setup.scalarCorrectedLiftSeries_summable t W).tsum_eq_zero_add
    _ = weightedState (Node := Node) (E := ℝ)
          (setup.perronLeft (t + 1)) W.1 +
          ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm (t + 1) j
            ⟨leftMul (Node := Node) (E := ℝ) (setup.C t) W.1,
              setup.C_leftMul_zeroSum_real t W⟩ := by
      rw [hhead]
      congr 1
      apply tsum_congr
      intro j
      exact setup.scalarCorrectedLiftSeriesTerm_succ_transport t j W
    _ = weightedState (Node := Node) (E := ℝ)
          (setup.perronLeft (t + 1)) W.1 +
          setup.scalarCorrectedLift (t + 1)
            ⟨leftMul (Node := Node) (E := ℝ) (setup.C t) W.1,
              setup.C_leftMul_zeroSum_real t W⟩ := by
      rw [setup.scalarCorrectedLift_eq_tsum]

theorem scalarCorrectedLift_sub (t : ℕ)
    (W V : ZeroSumState Node ℝ) :
    setup.scalarCorrectedLift t
        ⟨W.1 - V.1, by
          change ∑ i : Node, (W.1 i - V.1 i) = 0
          rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩ =
      setup.scalarCorrectedLift t W - setup.scalarCorrectedLift t V := by
  rw [setup.scalarCorrectedLift_eq_tsum, setup.scalarCorrectedLift_eq_tsum,
    setup.scalarCorrectedLift_eq_tsum]
  calc
    ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t j
        ⟨W.1 - V.1, by
          change ∑ i : Node, (W.1 i - V.1 i) = 0
          rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩ =
        ∑' j : ℕ, (setup.scalarCorrectedLiftSeriesTerm t j W -
          setup.scalarCorrectedLiftSeriesTerm t j V) := by
      apply tsum_congr
      intro j
      unfold scalarCorrectedLiftSeriesTerm weightedState leftMul Matrix.smulVec
      simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
    _ = (∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t j W) -
        ∑' j : ℕ, setup.scalarCorrectedLiftSeriesTerm t j V := by
      exact Summable.tsum_sub
        (setup.scalarCorrectedLiftSeries_summable t W)
        (setup.scalarCorrectedLiftSeries_summable t V)

theorem scalarCorrectedLift_periodic
    (t : ℕ) (W : ZeroSumState Node ℝ) :
    setup.scalarCorrectedLift (t + setup.period) W =
      setup.scalarCorrectedLift t W := by
  rw [setup.scalarCorrectedLift_eq_tsum, setup.scalarCorrectedLift_eq_tsum]
  apply tsum_congr
  intro j
  unfold scalarCorrectedLiftSeriesTerm
  rw [setup.pullLiftProduct_periodic_start t j]
  rw [show t + setup.period + j + 1 = t + j + 1 + setup.period by omega]
  rw [setup.perronLeft_periodic (t + j + 1)]

section PullColumnInnovation

noncomputable local instance : DecidableEq Node := Classical.decEq Node

/- Coordinate form of `b_t^T = π_{t+1}^T + D_{t+1}^T(C_t-I)`. -/
theorem influence_apply_eq_perron_add_scalarCorrectedLift
    (t : ℕ) (i : Node) :
    setup.influence t i = setup.perronLeft (t + 1) i +
      setup.scalarCorrectedLift (t + 1)
        (FiniteNetwork.normalizedCoordinateError (fun k => setup.C t k i) i
          (setup.C_column_sum t i)) := by
  simpa only [influence, influenceSeriesTerm, FiniteNetwork.periodicInfluence_def,
    scalarCorrectedLift, scalarCorrectedLiftSeriesTerm, weightedState, leftMul,
    FiniteNetwork.periodicCorrectedLift_def, setup.pullLiftProduct_eq_consecutiveProduct,
    consecutiveProduct_eq_finiteNetwork,
    FiniteNetwork.normalizedCoordinateError, Matrix.one_apply] using
    (FiniteNetwork.periodicInfluence_apply_eq_perron_add_correctedLift_normalizedColumnError
      setup.C setup.perronLeft t i
      (by simpa only [influenceSeriesTerm] using setup.influenceSeries_summable t)
      (setup.C_column_sum t i))

theorem normalizedCoordinateError_column_eq_error_sub_transport
    (t : ℕ) (i : Node) :
    (FiniteNetwork.normalizedCoordinateError (fun k => setup.C t k i) i
      (setup.C_column_sum t i)).1 =
      (setup.perronCoordinateError (t + 1) i).1 -
        leftMul (Node := Node) (E := ℝ) (setup.C t)
          (setup.perronCoordinateError t i).1 := by
  simpa only [perronCoordinateError, leftMul] using
    FiniteNetwork.columnInnovation_eq_normalizedCoordinateError_sub_smulVec
      (setup.C t) (setup.perronRight t) (setup.perronRight (t + 1)) i
      (setup.C_column_sum t i)
      (by simpa [rowSum] using setup.perronRight_sum t)
      (by simpa [rowSum] using setup.perronRight_sum (t + 1))
      (by
        funext k
        simpa only [Matrix.smulVec_apply, smul_eq_mul, matrixMulVector] using
          setup.C_mul_perronRight t k)

theorem weightedState_perronCoordinateError
    (t : ℕ) (i : Node) :
    weightedState (Node := Node) (E := ℝ) (setup.perronLeft (t + 1))
        (setup.perronCoordinateError t i).1 =
      (∑ k : Node,
        setup.perronLeft (t + 1) k * setup.perronRight t k) -
        setup.perronLeft (t + 1) i := by
  simpa only [weightedState, perronCoordinateError, smul_eq_mul] using
    FiniteNetwork.weightedState_normalizedCoordinateError
      (setup.perronLeft (t + 1)) (setup.perronRight t) i
      (by simpa [rowSum] using setup.perronRight_sum t)

/- For a constant coordinate input, the influence coefficient is the Perron
overlap plus a corrected-lift coboundary. -/
theorem influence_apply_eq_overlap_add_coboundary
    (t : ℕ) (i : Node) :
    setup.influence t i =
      (∑ k : Node,
        setup.perronLeft (t + 1) k * setup.perronRight t k) +
        setup.scalarCorrectedLift (t + 1)
          (setup.perronCoordinateError (t + 1) i) -
        setup.scalarCorrectedLift t (setup.perronCoordinateError t i) := by
  simpa only [influence, influenceSeriesTerm, FiniteNetwork.periodicInfluence_def,
    scalarCorrectedLift, scalarCorrectedLiftSeriesTerm, weightedState, leftMul,
    FiniteNetwork.periodicCorrectedLift_def,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm_def,
    setup.pullLiftProduct_eq_consecutiveProduct,
    consecutiveProduct_eq_finiteNetwork, perronCoordinateError] using
    (FiniteNetwork.periodicInfluence_apply_eq_overlap_add_correctedLift_coboundary
      setup.C setup.perronLeft setup.perronRight t i
      (by simpa only [influenceSeriesTerm] using setup.influenceSeries_summable t)
      (setup.C_column_sum t)
      (by simpa [rowSum] using setup.perronRight_sum t)
      (by simpa [rowSum] using setup.perronRight_sum (t + 1))
      (by
        funext k
        simpa only [Matrix.smulVec_apply, smul_eq_mul, matrixMulVector] using
          setup.C_mul_perronRight t k)
      (by
        simpa only [scalarCorrectedLiftSeriesTerm, weightedState, leftMul,
          FiniteNetwork.periodicCorrectedLiftSeriesTerm_def,
          setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork, perronCoordinateError] using
          setup.scalarCorrectedLiftSeries_summable t
            (setup.perronCoordinateError t i))
      (by
        simpa only [scalarCorrectedLiftSeriesTerm, weightedState, leftMul,
          FiniteNetwork.periodicCorrectedLiftSeriesTerm_def,
          setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork, perronCoordinateError] using
          setup.scalarCorrectedLiftSeries_summable (t + 1)
            (setup.perronCoordinateError (t + 1) i)))

end PullColumnInnovation

theorem perronCoordinateError_periodic (t : ℕ) (i : Node) :
    setup.perronCoordinateError (t + setup.period) i =
      setup.perronCoordinateError t i := by
  classical
  apply Subtype.ext
  funext k
  change setup.perronRight (t + setup.period) k -
      (if k = i then 1 else 0) =
    setup.perronRight t k - (if k = i then 1 else 0)
  rw [setup.perronRight_periodic t]

/- Source-granularity DC-gain identity: averaging the exact coboundary over a
period leaves only the phase-averaged Perron overlap. -/
theorem averageInfluence_eq_averagePerronOverlap :
    setup.averageInfluence =
      (fun _ : Node => setup.averagePerronOverlap) := by
  classical
  simpa only [averageInfluence, averagePerronOverlap, influence,
    influenceSeriesTerm, FiniteNetwork.periodicInfluence_def] using
    (FiniteNetwork.periodicInfluenceAverage_eq_averagePerronOverlap
      setup.C setup.perronLeft setup.perronRight setup.C_periodic
      setup.perronLeft_periodic
      (by simpa using setup.perronRight_periodic 0)
      (fun t _ => by
        simpa only [influenceSeriesTerm] using setup.influenceSeries_summable t)
      (fun t _ => setup.C_column_sum t)
      (fun t _ => by simpa [rowSum] using setup.perronRight_sum t)
      (fun t _ => by
        funext k
        simpa only [Matrix.smulVec_apply, smul_eq_mul, matrixMulVector] using
          setup.C_mul_perronRight t k)
      (fun t _ i => by
        simpa only [scalarCorrectedLiftSeriesTerm, weightedState, leftMul,
          FiniteNetwork.periodicCorrectedLiftSeriesTerm_def,
          setup.pullLiftProduct_eq_consecutiveProduct,
          consecutiveProduct_eq_finiteNetwork, perronCoordinateError] using
          setup.scalarCorrectedLiftSeries_summable t
            (setup.perronCoordinateError t i)))

/-- Source-derived positivity of the average influence gain. -/
theorem influenceGain_pos : 0 < (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) := by
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    div_eq_mul_inv, mul_comm, averageInfluence, rowSum] using
    (FiniteNetwork.periodic_influence_gain_pos_of_average_eq_const
      (b := fun r : Fin setup.period => setup.influence r.1)
      setup.averagePerronOverlap setup.averagePerronOverlap_pos
      setup.averageInfluence_eq_averagePerronOverlap)

/- Cauchy--Schwarz over the phase-node entries of the influence vectors. -/
theorem influenceGain_sq_le_nodeCount_mul_influenceSecondMoment :
    (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) ^ 2 ≤
      (nodeCount (Node := Node) : ℝ) * setup.influenceSecondMoment := by
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    div_eq_mul_inv, mul_comm, influenceSecondMoment,
    FiniteNetwork.periodicInfluenceSecondMoment, rowSum, rowNormSq,
    nodeCount] using
      (FiniteNetwork.periodicInfluenceGain_sq_le_card_mul_secondMoment
        (b := fun r : Fin setup.period => setup.influence r.1))

/-- Source-derived positivity of the influence second moment. -/
theorem influenceSecondMoment_pos : 0 < setup.influenceSecondMoment := by
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    div_eq_mul_inv, mul_comm, influenceSecondMoment,
    FiniteNetwork.periodicInfluenceSecondMoment, rowSum, rowNormSq] using
    (FiniteNetwork.periodic_influence_second_moment_pos_of_gain_pos
      (b := fun r : Fin setup.period => setup.influence r.1)
      (by
        simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
          div_eq_mul_inv, mul_comm, rowSum] using setup.influenceGain_pos))

/-- Source-derived bound `0 < n_eff <= n`. -/
theorem effectiveNodeCount_pos_and_le_nodeCount :
    0 < setup.effectiveNodeCount ∧
      setup.effectiveNodeCount ≤ (nodeCount (Node := Node) : ℝ) := by
  simpa only [effectiveNodeCount, FiniteNetwork.effectiveNodeCount,
    FiniteNetwork.effective_node_count_def, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, div_eq_mul_inv, mul_comm,
    influenceSecondMoment, FiniteNetwork.periodicInfluenceSecondMoment,
    rowSum, rowNormSq, nodeCount] using
    (FiniteNetwork.periodic_effective_node_count_pos_and_le_card
      (b := fun r : Fin setup.period => setup.influence r.1)
      (by
        simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
          div_eq_mul_inv, mul_comm, rowSum] using setup.influenceGain_pos.ne'))

theorem effectiveNodeCount_eq_nodeCount_iff_influenceEntriesAllEqual :
    setup.effectiveNodeCount = (nodeCount (Node := Node) : ℝ) ↔
      setup.influenceEntriesAllEqual := by
  classical
  simpa only [effectiveNodeCount, FiniteNetwork.effectiveNodeCount,
    Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_mul_inv, mul_comm,
    influenceSecondMoment, FiniteNetwork.periodicInfluenceSecondMoment,
    rowSum, rowNormSq, nodeCount,
    influenceEntriesAllEqual, FiniteNetwork.effective_node_count_def] using
      (FiniteNetwork.effective_node_count_eq_card_iff_influence_entries_all_equal
        (b := fun r : Fin setup.period => setup.influence r.1)
        setup.influenceSecondMoment_pos.ne')

theorem influenceEntriesAllEqual_of_period_eq_one :
    setup.period = 1 → setup.influenceEntriesAllEqual := by
  simpa only [influenceEntriesAllEqual] using
    (FiniteNetwork.influence_entry_eq_of_period_eq_one_of_average_eq_const
      (b := fun r : Fin setup.period => setup.influence r.1)
      setup.averagePerronOverlap
      (by simpa only [averageInfluence] using
        setup.averageInfluence_eq_averagePerronOverlap))

/-- Common initialization `X_0 = 1 x_0^T` from
`#/assumptions/2`. -/
def initialPrimal : State Node E :=
  fun _ => setup.x0

/-- Deterministic gradient table `Z_t`, evaluated row-by-row at the current
distributed state, from `#/assumptions/5`:
`(Z_t)_{i,:} = nabla f_i(x_{i,t})^T`. -/
noncomputable def gradientTable (X : State Node E) : State Node E :=
  fun i => setup.componentGradient i (X i)

/-- Sampled oracle table `G_t = Z_t + epsilon_t` from
`#/assumptions/5`, derived from the current state and noise path rather than
supplied as an independent process. -/
noncomputable def sampledGradient (noise : NoisePath Node E) (t : ℕ)
    (X : State Node E) : State Node E :=
  setup.gradientTable X + noise t

/-- The sampled oracle table unfolds to the paper's noise split `G_t = Z_t +
ε_t`. -/
theorem sampledGradient_eq_gradientTable_add_noise
    (noise : NoisePath Node E) (t : ℕ) (X : State Node E) :
    setup.sampledGradient noise t X = setup.gradientTable X + noise t := by
  rfl

/-- Algorithm state carrying the two recursively updated arrays `X_t` and
`Y_t`. The oracle table `G_t` is derived from `X_t` and the noise path. -/
abbrev AlgorithmState (Node E : Type*) := SOptLib.PushPullState Node E


/-- One push-pull step from `#/assumptions/1`:
`X_{t+1} = R_t X_t - α Y_t`,
`Y_{t+1} = C_t Y_t + G_{t+1} - G_t`, where `G_{t+1}` is evaluated at the newly
computed primal array. -/
noncomputable def oneStep (t : ℕ) (state : AlgorithmState Node E)
    (noise : NoisePath Node E) : AlgorithmState Node E :=
  SOptLib.pushPullStep (leftMul (Node := Node) (E := E)) setup.R setup.C
    (setup.alpha : ℝ) (setup.sampledGradient noise) t state

/-- Generated pathwise trajectory from the canonical one-step map in
`#/assumptions/1` and the common initialization in `#/assumptions/2`. The
SOptLib recursive-process primitive supplies the natural-number recursion; the
only external input is the oracle-noise sample path. -/
noncomputable def trajectory (noise : NoisePath Node E) :
    ℕ → AlgorithmState Node E :=
  fun t =>
    SOptLib.recursive_process_from_random_initial
      (fun noise =>
        { primal := setup.initialPrimal
          tracker := setup.sampledGradient noise 0 setup.initialPrimal })
      (fun k state noise => setup.oneStep k state noise) t noise

/-- Initial generated state. -/
theorem trajectory_zero (noise : NoisePath Node E) :
    setup.trajectory noise 0 = { primal := setup.initialPrimal, tracker := setup.sampledGradient noise 0 setup.initialPrimal } := by
  rfl

/-- Successor generated state. -/
theorem trajectory_succ (noise : NoisePath Node E) (t : ℕ) :
    setup.trajectory noise (t + 1) =
      setup.oneStep t (setup.trajectory noise t) noise := by
  rfl

/-- Generated primal array `X_t`. -/
noncomputable def primalState (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  (setup.trajectory noise t).primal

/-- Generated tracker array `Y_t`. -/
noncomputable def trackerState (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  (setup.trajectory noise t).tracker

/-- Generated sampled gradient table `G_t`, the source object in
`#/assumptions/5`. -/
noncomputable def oracleTable (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  setup.sampledGradient noise t (setup.primalState noise t)

/-- Initial primal array: `X_0 = 1 x_0^T`. -/
theorem primalState_zero (noise : NoisePath Node E) :
    setup.primalState noise 0 = setup.initialPrimal := by
  rfl

/-- Initial tracker array: `Y_0 = G_0`. -/
theorem trackerState_zero (noise : NoisePath Node E) :
    setup.trackerState noise 0 = setup.oracleTable noise 0 := by
  rfl

/-- Primal push recursion `X_{t+1}=R_t X_t - alpha Y_t` from
`#/assumptions/1`. -/
theorem primalState_succ (noise : NoisePath Node E) (t : ℕ) :
    setup.primalState noise (t + 1) =
      leftMul (Node := Node) (E := E) (setup.R t) (setup.primalState noise t) -
        (setup.alpha : ℝ) • setup.trackerState noise t := by
  rfl

/-- Gradient-tracking pull recursion
`Y_{t+1}=C_tY_t+G_{t+1}-G_t` from `#/assumptions/1`. -/
theorem trackerState_succ (noise : NoisePath Node E) (t : ℕ) :
    setup.trackerState noise (t + 1) =
      leftMul (Node := Node) (E := E) (setup.C t) (setup.trackerState noise t) +
        setup.oracleTable noise (t + 1) - setup.oracleTable noise t := by
  rfl

/-- Arithmetic average `bar x_t = n^{-1} 1^T X_t` from
`#/assumptions/3`. -/
noncomputable def arithmeticAverage (X : State Node E) : E :=
  ((nodeCount (Node := Node) : ℝ)⁻¹) • ∑ i : Node, X i

/-- Generated arithmetic average `bar x_t`. -/
noncomputable def averageIterate (noise : NoisePath Node E) (t : ℕ) : E :=
  arithmeticAverage (Node := Node) (E := E) (setup.primalState noise t)

/-- Source-form unfolding of `bar x_t = n^{-1} 1^T X_t`. -/
theorem averageIterate_eq_arithmeticAverage (noise : NoisePath Node E) (t : ℕ) :
    setup.averageIterate noise t =
      ((nodeCount (Node := Node) : ℝ)⁻¹) •
        ∑ i : Node, setup.primalState noise t i := by
  rfl

/-- Consensus-error projector `Pi = I - 11^T / n`, applied to a distributed
state as `Q_t = Pi X_t = X_t - 1 bar{x}_t^T`, from `#/assumptions/14`. -/
noncomputable def consensusError (X : State Node E) : State Node E :=
  let avg := arithmeticAverage (Node := Node) (E := E) X
  fun i => X i - avg

/-- Generated consensus-error state `Q_t = Π X_t`. -/
noncomputable def consensusState (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  consensusError (Node := Node) (E := E) (setup.primalState noise t)

/-- Source-form unfolding of `Q_t = X_t - 1 bar{x}_t^T`. -/
theorem consensusState_eq_state_sub_average (noise : NoisePath Node E) (t : ℕ) :
    setup.consensusState noise t =
      fun i => setup.primalState noise t i - setup.averageIterate noise t := by
  rfl

/-- Perron tracker residual `(I - v_t 1^T)W`, used in `H_0` and Section 6
joint coordinates. -/
noncomputable def perronResidual (t : ℕ) (W : State Node E) : State Node E :=
  fun i => W i - setup.perronRight t i • ∑ j : Node, W j

/-- Initial gradient heterogeneity `H_0 = ||(I-v_0 1^T)Z_0||_F` from
`#/assumptions/10`. -/
noncomputable def initialGradientHeterogeneity : ℝ :=
  FiniteNetwork.initialGradientHeterogeneity (setup.perronRight 0) (setup.gradientTable setup.initialPrimal)

/-- Nonnegativity of `H_0`. -/
theorem initialGradientHeterogeneity_nonneg :
    0 ≤ setup.initialGradientHeterogeneity := by
  exact Real.sqrt_nonneg _

/-- Tracker error `E_t = Y_t - G_t`. -/
noncomputable def trackerError (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  setup.trackerState noise t - setup.oracleTable noise t

/- The gradient-tracking recursion preserves the total oracle-table mass. -/
theorem trackerState_sum_eq_oracleTable_sum
    (noise : NoisePath Node E) (t : ℕ) :
    ∑ i : Node, setup.trackerState noise t i =
      ∑ i : Node, setup.oracleTable noise t i := by
  classical
  exact FiniteNetwork.tracker_sum_eq_oracle_sum_of_column_normalized setup.C
    (setup.trackerState noise) (setup.oracleTable noise)
    setup.C_column_sum
    (congrArg (fun X : Node → E => ∑ i : Node, X i)
      (setup.trackerState_zero noise))
    (setup.trackerState_succ noise) t

/-- Source-derived zero-sum invariant `1^T E_t = 0`. -/
theorem trackerError_zeroSum (noise : NoisePath Node E) (t : ℕ) :
    ∑ i : Node, setup.trackerError noise t i = 0 := by
  unfold trackerError
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib, setup.trackerState_sum_eq_oracleTable_sum noise t]
  exact sub_self _

/-- Tracker error as an element of the corrected-lift domain `S`. -/
noncomputable def trackerErrorZeroSum (noise : NoisePath Node E) (t : ℕ) :
    ZeroSumState Node E :=
  ⟨setup.trackerError noise t, setup.trackerError_zeroSum noise t⟩

/-- Mean-driven tracker-error recursion `E^Z_{t+1}=C_tE^Z_t+(C_t-I)Z_t`,
`E^Z_0=0`. -/
noncomputable def meanTrackerError (setup : Setup Node E)
    (noise : NoisePath Node E) :
    ℕ → State Node E :=
  FiniteNetwork.trackerInnovationResponse setup.C
    (fun k => setup.gradientTable (setup.primalState noise k))

/- The source-form successor equation exposed by the generalized response. -/
theorem meanTrackerError_succ (noise : NoisePath Node E) (t : ℕ) :
    setup.meanTrackerError noise (t + 1) =
      leftMul (Node := Node) (E := E) (setup.C t)
          (setup.meanTrackerError noise t) +
        leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.C t) (identityMatrix (Node := Node)))
          (setup.gradientTable (setup.primalState noise t)) := by
  classical
  simpa [meanTrackerError, leftMul, matrixSub, identityMatrix] using
    (FiniteNetwork.trackerInnovationResponse_succ_sub_one setup.C
      (fun k => setup.gradientTable (setup.primalState noise k)) t)

/-- Noise-driven tracker-error recursion
`E^ε_{t+1}=C_tE^ε_t+(C_t-I)ε_t`, `E^ε_0=0`. -/
noncomputable def noiseTrackerError (noise : NoisePath Node E) :
    ℕ → State Node E :=
  fun t =>
    SOptLib.recursiveIterateProcess (0 : State Node E)
      (fun k Ecur (_ : Unit) =>
        leftMul (Node := Node) (E := E) (setup.C k) Ecur +
          leftMul (Node := Node) (E := E)
            (matrixSub (Node := Node) (setup.C k) (identityMatrix (Node := Node)))
            (noise k)) t ()

/-- Section 6 mean joint coordinate
`Theta_t^Z = E_t^Z + (I-v_t 1^T)Z_t` from (6.2). -/
noncomputable def meanJointCoordinate
    (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  setup.meanTrackerError noise t +
    setup.perronResidual t
      (setup.gradientTable (setup.primalState noise t))

/-- Section 6 noise joint coordinate `J_t^epsilon = epsilon_t + E_t^epsilon`
from (6.2). -/
noncomputable def noiseJointCoordinate
    (noise : NoisePath Node E) (t : ℕ) : State Node E :=
  noise t + setup.noiseTrackerError noise t

/- Left multiplication is linear in the distributed state. -/
theorem leftMul_add_state (A : NodeMatrix Node) (X Y : State Node E) :
    leftMul (Node := Node) (E := E) A (X + Y) =
      leftMul (Node := Node) (E := E) A X +
        leftMul (Node := Node) (E := E) A Y := by
  funext i
  simp only [leftMul_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/- Left multiplication commutes with subtraction of distributed states. -/
theorem leftMul_sub_state (A : NodeMatrix Node) (X Y : State Node E) :
    leftMul (Node := Node) (E := E) A (X - Y) =
      leftMul (Node := Node) (E := E) A X -
        leftMul (Node := Node) (E := E) A Y := by
  funext i
  simp only [leftMul_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/- Matrix subtraction by the identity acts as subtraction on states. -/
theorem leftMul_sub_identity (A : NodeMatrix Node) (X : State Node E) :
    leftMul (Node := Node) (E := E)
        (matrixSub (Node := Node) A (identityMatrix (Node := Node))) X =
      leftMul (Node := Node) (E := E) A X - X := by
  classical
  simpa only [leftMul, matrixSub, identityMatrix] using
    (Matrix.sub_one_smulVec A X)

/- Every pull innovation `(C_t-I)X` has zero total mass. -/
theorem pull_innovation_sum_zero (t : ℕ) (X : State Node E) :
    ∑ i : Node,
        leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.C t) (identityMatrix (Node := Node))) X i =
      0 := by
  classical
  simpa only [leftMul, matrixSub, identityMatrix] using
    Matrix.sum_sub_one_smulVec_eq_zero_of_mem_colStochastic X
      (Matrix.mem_colStochastic_iff_sum.mpr (setup.C_columnStochastic t))

/-- Source-derived zero-sum invariant for `E_t^Z`. -/
theorem meanTrackerError_zeroSum (noise : NoisePath Node E) (t : ℕ) :
    ∑ i : Node, setup.meanTrackerError noise t i = 0 := by
  classical
  simpa only [meanTrackerError] using
    FiniteNetwork.trackerInnovationResponse_sum_eq_zero setup.C
      (fun k => setup.gradientTable (setup.primalState noise k)) t
      (fun k j => setup.C_column_sum k j)

/-- Source-derived zero-sum invariant for `E_t^ε`. -/
theorem noiseTrackerError_zeroSum (noise : NoisePath Node E) (t : ℕ) :
    ∑ i : Node, setup.noiseTrackerError noise t i = 0 := by
  classical
  induction t with
  | zero =>
      simp [noiseTrackerError, SOptLib.recursiveIterateProcess]
  | succ t ih =>
      change ∑ i : Node,
          (leftMul (Node := Node) (E := E) (setup.C t)
              (setup.noiseTrackerError noise t) +
            leftMul (Node := Node) (E := E)
              (matrixSub (Node := Node) (setup.C t)
                (identityMatrix (Node := Node))) (noise t)) i = 0
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [setup.C_leftMul_zeroSum t
        ⟨setup.noiseTrackerError noise t, ih⟩,
        setup.pull_innovation_sum_zero t (noise t)]
      simp

/-- The Section 6 mean joint coordinate belongs to the zero-sum pull
subspace, as required when applying Lemma 4.2 in (6.5). -/
theorem meanJointCoordinate_zeroSum (noise : NoisePath Node E) (t : ℕ) :
    ∑ i : Node, setup.meanJointCoordinate noise t i = 0 := by
  simpa only [meanJointCoordinate, perronResidual,
    FiniteNetwork.perronResidual_def] using
    (FiniteNetwork.sum_add_perronResidual_eq_zero
      (e := setup.meanTrackerError noise t)
      (W := setup.gradientTable (setup.primalState noise t))
      (v := setup.perronRight t)
      (setup.meanTrackerError_zeroSum noise t)
      (by simpa [rowSum] using setup.perronRight_sum t))

/-- Initial condition in (6.4): `Theta_0^Z = S_0 Z_0`. -/
theorem meanJointCoordinate_zero (noise : NoisePath Node E) :
    setup.meanJointCoordinate noise 0 =
      setup.perronResidual 0 (setup.gradientTable setup.initialPrimal) := by
  simp [meanJointCoordinate, meanTrackerError, primalState_zero,
    SOptLib.recursiveIterateProcess]

/-- Mean-driven tracker error as an element of `S`. -/
noncomputable def meanTrackerErrorZeroSum (noise : NoisePath Node E) (t : ℕ) :
    ZeroSumState Node E :=
  ⟨setup.meanTrackerError noise t, setup.meanTrackerError_zeroSum noise t⟩

/-- Noise-driven tracker error as an element of `S`. -/
noncomputable def noiseTrackerErrorZeroSum (noise : NoisePath Node E) (t : ℕ) :
    ZeroSumState Node E :=
  ⟨setup.noiseTrackerError noise t, setup.noiseTrackerError_zeroSum noise t⟩

/- The full tracker error obeys the common innovation recurrence. -/
theorem trackerError_succ_innovation
    (noise : NoisePath Node E) (t : ℕ) :
    setup.trackerError noise (t + 1) =
      leftMul (Node := Node) (E := E) (setup.C t)
          (setup.trackerError noise t) +
        leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.C t) (identityMatrix (Node := Node)))
          (setup.oracleTable noise t) := by
  classical
  simpa only [trackerError, leftMul, matrixSub, identityMatrix,
    Matrix.sub_apply, Matrix.one_apply] using
    (FiniteNetwork.gradientTrackingError_succ
      (C := setup.C) (Y := setup.trackerState noise)
      (G := setup.oracleTable noise) t (setup.trackerState_succ noise t))

/-- Algebraic split `E_t = E_t^Z + E_t^ε`. -/
theorem trackerError_eq_mean_add_noise (noise : NoisePath Node E) (t : ℕ) :
    setup.trackerError noise t =
      setup.meanTrackerError noise t + setup.noiseTrackerError noise t := by
  classical
  have hnoise : setup.noiseTrackerError noise t =
      FiniteNetwork.trackerInnovationResponse setup.C noise t := by
    induction t with
    | zero =>
        rw [FiniteNetwork.trackerInnovationResponse_zero]
        rfl
    | succ t ih =>
        change
          leftMul (setup.C t) (setup.noiseTrackerError noise t) +
              leftMul (matrixSub (setup.C t) identityMatrix) (noise t) = _
        rw [FiniteNetwork.trackerInnovationResponse_succ_sub_one, ih,
          leftMul_sub_identity, Matrix.sub_one_smulVec]
        rfl
  rw [meanTrackerError, hnoise]
  exact FiniteNetwork.gradientTrackingError_eq_innovationResponse_add
      (C := setup.C)
      (Z := fun k => setup.gradientTable (setup.primalState noise k))
      (eps := noise) (Y := setup.trackerError noise) t
      (by
        unfold trackerError
        rw [setup.trackerState_zero noise]
        exact sub_self _)
      (fun k => by
        rw [setup.trackerError_succ_innovation noise k]
        simp only [oracleTable, sampledGradient]
        rw [leftMul_sub_identity, Matrix.sub_one_smulVec]
        rfl)

/- Source equation (6.3): the generated tracker splits into the mean joint
coordinate, the Perron-aligned aggregate gradient, and the noise joint
coordinate. -/
theorem trackerState_eq_joint_decomposition_source
    (noise : NoisePath Node E) (t : ℕ) :
    setup.trackerState noise t =
      setup.meanJointCoordinate noise t +
      (fun i => setup.perronRight t i •
        ∑ j : Node, setup.gradientTable (setup.primalState noise t) j) +
      setup.noiseJointCoordinate noise t := by
  have htracker :
      setup.trackerState noise t =
        setup.trackerError noise t + setup.oracleTable noise t := by
    unfold trackerError
    abel
  rw [htracker, setup.trackerError_eq_mean_add_noise noise t]
  have horacle :
      setup.oracleTable noise t =
        setup.gradientTable (setup.primalState noise t) + noise t := by
    exact setup.sampledGradient_eq_gradientTable_add_noise noise t
      (setup.primalState noise t)
  rw [horacle]
  funext i
  simp only [meanJointCoordinate, noiseJointCoordinate, Pi.add_apply,
    perronResidual, FiniteNetwork.perronResidual_apply]
  abel

/-- Lifted center `nu_t = pi_t^T X_t - alpha D_t^T E_t` from
`#/key_lemmas/3` (Lemma 5.1 / (5.3)). -/
noncomputable def liftedCenter (noise : NoisePath Node E) (t : ℕ) : E :=
  FiniteNetwork.correctedWeightedCenter (setup.perronLeft t)
    (setup.primalState noise t) setup.alpha (setup.correctedLift t)
    (setup.trackerErrorZeroSum noise t)

/-- Block-start index `kp` from the block notation in `#/assumptions/13`. -/
def blockStart (k : ℕ) : ℕ :=
  k * setup.period

/-- Block-start hybrid center `chi_k = pi_0^T X_{kp}` from
`#/assumptions/13`. -/
noncomputable def blockStartHybridCenter (noise : NoisePath Node E) (k : ℕ) : E :=
  weightedState (Node := Node) (E := E) (setup.perronLeft 0)
    (setup.primalState noise (setup.blockStart k))

/-- Period gain `H = p h` from `#/assumptions/13`. -/
noncomputable def blockGain : ℝ :=
  (setup.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1)))

/-- Source-derived positivity of the period gain `H = ph`. -/
theorem blockGain_pos : 0 < setup.blockGain := by
  have hp : 0 < (setup.period : ℝ) := by
    exact_mod_cast setup.period_pos
  exact mul_pos hp setup.influenceGain_pos

/-- Block-start full gradient `bar g_k = nabla f(bar x_{kp})` from
`#/assumptions/13`. -/
noncomputable def blockAverageGradient (noise : NoisePath Node E) (k : ℕ) : E :=
  setup.averageGradient (setup.averageIterate noise (setup.blockStart k))

/-- Block lifted center `ν_k`, i.e. `ν_{kp}` at the start of block `k`. -/
noncomputable def blockLiftedCenter (noise : NoisePath Node E) (k : ℕ) : E :=
  setup.liftedCenter noise (setup.blockStart k)

/-- Block phase error `e_k = sum_r b_r^T Z_{kp+r} - H gbar_k` from
`#/key_lemmas/3/proof/3`. -/
noncomputable def blockPhaseError (noise : NoisePath Node E) (k : ℕ) : E :=
  (∑ r : Fin setup.period,
      weightedState (Node := Node) (E := E) (setup.influence r.1)
        (setup.gradientTable
          (setup.primalState noise (setup.blockStart k + r.1)))) -
    setup.blockGain • setup.blockAverageGradient noise k

/-- Block martingale noise `zeta_k = sum_r b_r^T epsilon_{kp+r}` from
`#/key_lemmas/3/proof/3`. -/
noncomputable def blockNoise (noise : NoisePath Node E) (k : ℕ) : E :=
  ∑ r : Fin setup.period,
    weightedState (Node := Node) (E := E) (setup.influence r.1)
      (noise (setup.blockStart k + r.1))

/-- Mean lift correction `tau_k^Z = D_0^T E_{kp}^Z` from
`#/key_lemmas/3/proof/5`. -/
noncomputable def meanLiftCorrection (noise : NoisePath Node E) (k : ℕ) : E :=
  setup.correctedLift 0
    (setup.meanTrackerErrorZeroSum noise (setup.blockStart k))

/-- Noise lift correction `eta_k = D_0^T E_{kp}^epsilon` from
`#/key_lemmas/3/proof/5`. -/
noncomputable def noiseLiftCorrection (noise : NoisePath Node E) (k : ℕ) : E :=
  setup.correctedLift 0
    (setup.noiseTrackerErrorZeroSum noise (setup.blockStart k))

/-- High-pass mean-tracker increment `rho_k = tau_{k+1}^Z - tau_k^Z`
from `#/key_lemmas/3/proof/5`. -/
noncomputable def highPassIncrement (noise : NoisePath Node E) (k : ℕ) : E :=
  setup.meanLiftCorrection noise (k + 1) - setup.meanLiftCorrection noise k

/-- Hybrid center `omega_k = chi_k - alpha eta_k`, equivalently
`omega_k = nu_k + alpha tau_k^Z`, from `#/key_lemmas/3/proof/6`
(`eq:omega / (5.11)`). -/
noncomputable def hybridCenter (noise : NoisePath Node E) (k : ℕ) : E :=
  setup.blockStartHybridCenter noise k -
    setup.alpha • setup.noiseLiftCorrection noise k

/-- Hybrid-center objective value `V_k = f(omega_k)` used in the one-block
descent; this is the potential whose endpoint facts are recorded in
`#/key_lemmas/3/proof/8`. -/
noncomputable def hybridPotential (noise : NoisePath Node E) (k : ℕ) : ℝ :=
  setup.objective (setup.hybridCenter noise k)

/- A periodic sequence returns to the same phase at every block start. -/
theorem perronLeft_blockStart_add (k t : ℕ) :
    setup.perronLeft (setup.blockStart k + t) = setup.perronLeft t := by
  induction k with
  | zero => simp [blockStart]
  | succ k ih =>
      calc
        setup.perronLeft (setup.blockStart (k + 1) + t) =
            setup.perronLeft ((setup.blockStart k + t) + setup.period) := by
          congr 1
          simp [blockStart, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]
        _ = setup.perronLeft (setup.blockStart k + t) :=
          setup.perronLeft_periodic (setup.blockStart k + t)
        _ = setup.perronLeft t := ih

/- The periodic pull schedule returns to the same phase at every block start. -/
theorem C_blockStart_add (k t : ℕ) :
    setup.C (setup.blockStart k + t) = setup.C t := by
  induction k with
  | zero => simp [blockStart]
  | succ k ih =>
      calc
        setup.C (setup.blockStart (k + 1) + t) =
            setup.C ((setup.blockStart k + t) + setup.period) := by
          congr 1
          simp [blockStart, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]
        _ = setup.C (setup.blockStart k + t) :=
          setup.C_periodic (setup.blockStart k + t)
        _ = setup.C t := ih

/- Influence-window pull products are periodic at block starts. -/
theorem pullWindowProduct_blockStart_add (k r j : ℕ) :
    setup.pullWindowProduct (setup.blockStart k + r) j =
      setup.pullWindowProduct r j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pullWindowProduct]
      rw [show setup.blockStart k + r + j + 1 =
          setup.blockStart k + (r + j + 1) by omega]
      rw [setup.C_blockStart_add k (r + j + 1), ih]

/- Every influence-series tail term returns to the same phase at a block
start. -/
theorem influenceSeriesTerm_blockStart_add (k r j : ℕ) :
    setup.influenceSeriesTerm (setup.blockStart k + r) j =
      setup.influenceSeriesTerm r j := by
  simpa only [influenceSeriesTerm, blockStart, Nat.mul_comm, Nat.add_comm] using
    (FiniteNetwork.periodicInfluenceSeriesTerm_add_period_mul setup.C
      setup.perronLeft setup.period r k j setup.C_periodic
      setup.perronLeft_periodic)

/- The influence row itself is periodic at every block phase. -/
theorem influence_blockStart_add (k r : ℕ) :
    setup.influence (setup.blockStart k + r) = setup.influence r := by
  simpa only [influence, influenceSeriesTerm, FiniteNetwork.periodicInfluence_def,
    blockStart, Nat.mul_comm, Nat.add_comm] using
    (FiniteNetwork.periodicInfluence_add_period_mul setup.C setup.perronLeft
      setup.period r k setup.C_periodic setup.perronLeft_periodic)

/- Pull products based at a block start agree with the phase-zero products. -/
theorem pullLiftProduct_blockStart (k j : ℕ) :
    setup.pullLiftProduct (setup.blockStart k) j = setup.pullLiftProduct 0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pullLiftProduct]
      rw [setup.C_blockStart_add k j, ih]
      simp

/- Every summand of the corrected lift is periodic in its base time. -/
theorem correctedLiftSeriesTerm_blockStart
    (k j : ℕ) (W : ZeroSumState Node E) :
    setup.correctedLiftSeriesTerm (setup.blockStart k) j W =
      setup.correctedLiftSeriesTerm 0 j W := by
  classical
  simpa only [correctedLiftSeriesTerm, blockStart, Nat.zero_add, Nat.mul_comm] using
    (FiniteNetwork.periodicCorrectedLiftSeriesTerm_add_period_mul setup.C
      setup.perronLeft setup.period 0 k j W setup.C_periodic
      setup.perronLeft_periodic)

/- The corrected lift at a block start is the phase-zero corrected lift. -/
theorem correctedLift_blockStart
    (k : ℕ) (W : ZeroSumState Node E) :
    setup.correctedLift (setup.blockStart k) W = setup.correctedLift 0 W := by
  classical
  simpa only [correctedLift, correctedLiftSeriesTerm, blockStart, Nat.zero_add,
    Nat.mul_comm, FiniteNetwork.periodicCorrectedLift_def,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm_def] using
    (FiniteNetwork.periodicCorrectedLift_add_period_mul setup.C setup.perronLeft
      setup.period 0 k W setup.C_periodic setup.perronLeft_periodic)

/- Weighted aggregation is additive in the distributed state. -/
theorem weightedState_add_state
    (w : RowVector Node) (X Y : State Node E) :
    weightedState (Node := Node) (E := E) w (X + Y) =
      weightedState (Node := Node) (E := E) w X +
        weightedState (Node := Node) (E := E) w Y := by
  unfold weightedState
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

/- The pointwise sum of two zero-sum states is again zero-sum. -/
theorem zeroSumState_add_mem (W V : ZeroSumState Node E) :
    ∑ i : Node, (W.1 + V.1) i = 0 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, W.2, V.2, add_zero]

/- Each corrected-lift series term is additive on the zero-sum subspace. -/
theorem correctedLiftSeriesTerm_add
    (t j : ℕ) (W V : ZeroSumState Node E) :
    setup.correctedLiftSeriesTerm t j
        ⟨W.1 + V.1, zeroSumState_add_mem W V⟩ =
      setup.correctedLiftSeriesTerm t j W +
        setup.correctedLiftSeriesTerm t j V := by
  simp_rw [setup.correctedLiftSeriesTerm_eq_weightedState]
  change weightedState (Node := Node) (E := E) (setup.perronLeft (t + j + 1))
      (leftMul (Node := Node) (E := E) (setup.pullLiftProduct t j)
        (W.1 + V.1)) = _
  rw [leftMul_add_state]
  exact weightedState_add_state _ _ _

/- The corrected lift is additive on its zero-sum domain. -/
theorem correctedLift_add
    (t : ℕ) (W V : ZeroSumState Node E) :
    setup.correctedLift t ⟨W.1 + V.1, zeroSumState_add_mem W V⟩ =
      setup.correctedLift t W + setup.correctedLift t V := by
  rw [setup.correctedLift_eq_tsum, setup.correctedLift_eq_tsum,
    setup.correctedLift_eq_tsum]
  calc
    ∑' j : ℕ, setup.correctedLiftSeriesTerm t j
        ⟨W.1 + V.1, zeroSumState_add_mem W V⟩ =
        ∑' j : ℕ, (setup.correctedLiftSeriesTerm t j W +
          setup.correctedLiftSeriesTerm t j V) := by
      apply tsum_congr
      intro j
      exact setup.correctedLiftSeriesTerm_add t j W V
    _ = (∑' j : ℕ, setup.correctedLiftSeriesTerm t j W) +
        ∑' j : ℕ, setup.correctedLiftSeriesTerm t j V := by
      exact Summable.tsum_add
        (setup.correctedLiftSeries_summable t W)
        (setup.correctedLiftSeries_summable t V)

/- Weighted aggregation is additive in its row coefficient. -/
theorem weightedState_add_weight
    (w v : RowVector Node) (X : State Node E) :
    weightedState (Node := Node) (E := E) (w + v) X =
      weightedState (Node := Node) (E := E) w X +
        weightedState (Node := Node) (E := E) v X := by
  unfold weightedState
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/- Applying a row after a node matrix agrees with applying the row to the
matrix action on the distributed state. -/
theorem weightedState_rowMulMatrix
    (w : RowVector Node) (A : NodeMatrix Node) (X : State Node E) :
    weightedState (Node := Node) (E := E)
        (rowMulMatrix (Node := Node) w A) X =
      weightedState (Node := Node) (E := E) w
        (leftMul (Node := Node) (E := E) A X) := by
  exact Matrix.sum_vecMul_smul_eq_sum_smul_smulVec w A X

/- Equation (5.1) identifies every influence-tail coefficient with the
corresponding corrected-lift action on the pull innovation. -/
theorem influenceSeriesTerm_weightedState
    (t j : ℕ) (X : State Node E) :
    weightedState (Node := Node) (E := E) (setup.influenceSeriesTerm t j) X =
      setup.correctedLiftSeriesTerm (t + 1) j
        ⟨leftMul (Node := Node) (E := E)
            (matrixSub (Node := Node) (setup.C t) (identityMatrix (Node := Node))) X,
          setup.pull_innovation_sum_zero t X⟩ := by
  classical
  simpa only [weightedState, influenceSeriesTerm, correctedLiftSeriesTerm,
    leftMul, matrixSub, identityMatrix, Matrix.sub_apply, Matrix.one_apply]
    using (FiniteNetwork.periodicInfluenceSeriesTerm_weightedState
      setup.C setup.perronLeft t j X (setup.pull_innovation_sum_zero t X))

/- The source coefficient identity
`b_t^T X = pi_{t+1}^T X + D_{t+1}^T (C_t-I)X`. -/
theorem influence_weightedState_identity
    (t : ℕ) (X : State Node E) :
    weightedState (Node := Node) (E := E) (setup.influence t) X =
      weightedState (Node := Node) (E := E) (setup.perronLeft (t + 1)) X +
        setup.correctedLift (t + 1)
          ⟨leftMul (Node := Node) (E := E)
              (matrixSub (Node := Node) (setup.C t)
                (identityMatrix (Node := Node))) X,
            setup.pull_innovation_sum_zero t X⟩ := by
  classical
  simpa only [influence, influenceSeriesTerm, weightedState, correctedLift,
    correctedLiftSeriesTerm, FiniteNetwork.periodicCorrectedLift_def,
    leftMul, matrixSub, identityMatrix] using
    (FiniteNetwork.periodicInfluence_weightedState_eq_perron_add_correctedLift
      setup.C setup.perronLeft t X
      (by simpa only [influenceSeriesTerm] using setup.influenceSeries_summable t)
      (by simpa only [leftMul, matrixSub, identityMatrix] using
        setup.pull_innovation_sum_zero t X))

/- The primal recursion after applying the next left Perron row. -/
theorem weightedPrimal_succ
    (noise : NoisePath Node E) (t : ℕ) :
    weightedState (Node := Node) (E := E) (setup.perronLeft (t + 1))
        (setup.primalState noise (t + 1)) =
      weightedState (Node := Node) (E := E) (setup.perronLeft t)
          (setup.primalState noise t) -
        setup.alpha • weightedState (Node := Node) (E := E)
          (setup.perronLeft (t + 1)) (setup.trackerState noise t) := by
  simpa only [weightedState, leftMul, rowMulMatrix] using
    weightedState_update_eq_of_left_weight_transport
      (R := setup.R t) (pi := setup.perronLeft t)
      (piNext := setup.perronLeft (t + 1))
      (X := setup.primalState noise t)
      (Xnext := setup.primalState noise (t + 1))
      (Y := setup.trackerState noise t) (alpha := setup.alpha)
      (setup.primalState_succ noise t)
      (by funext j; exact setup.perronLeft_mul_R t j)

/- Equation (5.4): the exact one-step lifted-center recursion. -/
theorem liftedCenter_succ
    (noise : NoisePath Node E) (t : ℕ) :
    setup.liftedCenter noise (t + 1) =
      setup.liftedCenter noise t -
        setup.alpha • weightedState (Node := Node) (E := E)
          (setup.influence t) (setup.oracleTable noise t) := by
  classical
  let transported : ZeroSumState Node E :=
    ⟨leftMul (Node := Node) (E := E) (setup.C t)
        (setup.trackerErrorZeroSum noise t).1,
      setup.C_leftMul_zeroSum t (setup.trackerErrorZeroSum noise t)⟩
  let innovation : ZeroSumState Node E :=
    ⟨leftMul (Node := Node) (E := E)
        (matrixSub (Node := Node) (setup.C t) (identityMatrix (Node := Node)))
        (setup.oracleTable noise t),
      setup.pull_innovation_sum_zero t (setup.oracleTable noise t)⟩
  apply FiniteNetwork.correctedWeightedCenter_succ_of_tracking_update
    (X := setup.primalState noise) (Y := setup.trackerState noise)
    (G := setup.oracleTable noise) (pi := setup.perronLeft)
    (influence := setup.influence) (error := setup.trackerErrorZeroSum noise)
    (D := setup.correctedLift) (alpha := setup.alpha) (t := t)
    (transported := transported) (innovation := innovation)
  · simpa only [weightedState] using setup.weightedPrimal_succ noise t
  · apply Subtype.ext
    simpa only [transported, innovation, FiniteNetwork.ZeroSumState.coe_add,
      trackerErrorZeroSum]
      using setup.trackerError_succ_innovation noise t
  · simp only [trackerErrorZeroSum]
    unfold trackerError
    abel
  · simpa only [transported, weightedState] using
      setup.correctedLift_poisson t (setup.trackerErrorZeroSum noise t)
  · simpa only [innovation, weightedState] using
      setup.influence_weightedState_identity t (setup.oracleTable noise t)
  · exact setup.correctedLift_add (t + 1) transported innovation

/- The ambient tracker decomposition is the same equality in `ZeroSumState`. -/
theorem trackerErrorZeroSum_eq_mean_add_noise
    (noise : NoisePath Node E) (t : ℕ) :
    setup.trackerErrorZeroSum noise t =
      ⟨(setup.meanTrackerErrorZeroSum noise t).1 +
          (setup.noiseTrackerErrorZeroSum noise t).1,
        zeroSumState_add_mem (setup.meanTrackerErrorZeroSum noise t)
          (setup.noiseTrackerErrorZeroSum noise t)⟩ := by
  apply Subtype.ext
  exact setup.trackerError_eq_mean_add_noise noise t

/- Summing (5.4) over one complete network period. -/
theorem liftedCenter_block_telescope
    (noise : NoisePath Node E) (k : ℕ) :
    setup.liftedCenter noise (setup.blockStart k + setup.period) =
      setup.liftedCenter noise (setup.blockStart k) -
        setup.alpha •
          ∑ r : Fin setup.period,
            weightedState (Node := Node) (E := E) (setup.influence r.1)
              (setup.oracleTable noise (setup.blockStart k + r.1)) := by
  have hprefix : ∀ m : ℕ,
      setup.liftedCenter noise (setup.blockStart k + m) =
        setup.liftedCenter noise (setup.blockStart k) -
          setup.alpha •
            ∑ r ∈ Finset.range m,
            weightedState (Node := Node) (E := E) (setup.influence r)
                (setup.oracleTable noise (setup.blockStart k + r)) := by
    intro m
    simpa only [setup.influence_blockStart_add k] using
      (sub_smul_sum_range_eq_of_succ_recurrence
        (x := setup.liftedCenter noise)
        (u := fun t => weightedState (Node := Node) (E := E)
          (setup.influence t) (setup.oracleTable noise t))
        setup.alpha (setup.blockStart k) m (setup.liftedCenter_succ noise))
  rw [hprefix setup.period]
  congr 2
  exact (Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    weightedState (Node := Node) (E := E) (setup.influence r)
      (setup.oracleTable noise (setup.blockStart k + r))) setup.period).symm

/-- Source-derived identity `ω_k = ν_k + ατ_k^Z`. -/
theorem hybridCenter_eq_lifted_add_meanLift (noise : NoisePath Node E) (k : ℕ) :
    setup.hybridCenter noise k =
      setup.blockLiftedCenter noise k + setup.alpha • setup.meanLiftCorrection noise k := by
  unfold hybridCenter blockStartHybridCenter noiseLiftCorrection
  unfold blockLiftedCenter liftedCenter FiniteNetwork.correctedWeightedCenter
    meanLiftCorrection
  change
    weightedState (Node := Node) (E := E) (setup.perronLeft 0)
          (setup.primalState noise (setup.blockStart k)) -
        setup.alpha • setup.correctedLift 0
          (setup.noiseTrackerErrorZeroSum noise (setup.blockStart k)) =
      weightedState (Node := Node) (E := E)
          (setup.perronLeft (setup.blockStart k))
          (setup.primalState noise (setup.blockStart k)) -
          setup.alpha • setup.correctedLift (setup.blockStart k)
            (setup.trackerErrorZeroSum noise (setup.blockStart k)) +
        setup.alpha • setup.correctedLift 0
          (setup.meanTrackerErrorZeroSum noise (setup.blockStart k))
  rw [show setup.perronLeft 0 = setup.perronLeft (setup.blockStart k) by
    symm
    simpa using setup.perronLeft_blockStart_add k 0]
  rw [setup.correctedLift_blockStart k (setup.trackerErrorZeroSum noise
    (setup.blockStart k))]
  rw [setup.trackerErrorZeroSum_eq_mean_add_noise noise (setup.blockStart k)]
  rw [setup.correctedLift_add]
  rw [smul_add]
  abel

/-- Block lifted-center recursion from `#/key_lemmas/3/proof/3`:
`nu_{k+1}=nu_k-alpha(H bar g_k+e_k+zeta_k)`. -/
theorem blockLiftedCenter_succ (noise : NoisePath Node E) (k : ℕ) :
    setup.blockLiftedCenter noise (k + 1) =
      setup.blockLiftedCenter noise k -
        setup.alpha •
          (setup.blockGain • setup.blockAverageGradient noise k +
            setup.blockPhaseError noise k + setup.blockNoise noise k) := by
  have hstart :
      setup.blockStart (k + 1) = setup.blockStart k + setup.period := by
    simp [blockStart, Nat.add_mul]
  have hsplit :
      (∑ r : Fin setup.period,
          weightedState (Node := Node) (E := E) (setup.influence r.1)
            (setup.oracleTable noise (setup.blockStart k + r.1))) =
        (∑ r : Fin setup.period,
          weightedState (Node := Node) (E := E) (setup.influence r.1)
            (setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r.1)))) +
        ∑ r : Fin setup.period,
          weightedState (Node := Node) (E := E) (setup.influence r.1)
            (noise (setup.blockStart k + r.1)) := by
    calc
      (∑ r : Fin setup.period,
          weightedState (Node := Node) (E := E) (setup.influence r.1)
            (setup.oracleTable noise (setup.blockStart k + r.1))) =
          ∑ r : Fin setup.period,
            (weightedState (Node := Node) (E := E) (setup.influence r.1)
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart k + r.1))) +
              weightedState (Node := Node) (E := E) (setup.influence r.1)
                (noise (setup.blockStart k + r.1))) := by
        apply Finset.sum_congr rfl
        intro r _
        unfold oracleTable
        rw [setup.sampledGradient_eq_gradientTable_add_noise]
        exact weightedState_add_state _ _ _
      _ = _ := Finset.sum_add_distrib
  unfold blockLiftedCenter
  rw [hstart, setup.liftedCenter_block_telescope noise k]
  rw [hsplit]
  unfold blockPhaseError blockNoise
  module

/-- Hybrid-center recursion from `#/key_lemmas/3/proof/7`
(`eq:omega-rec / (5.12)`). -/
theorem hybridCenter_succ (noise : NoisePath Node E) (k : ℕ) :
    setup.hybridCenter noise (k + 1) =
      setup.hybridCenter noise k -
        setup.alpha •
          (setup.blockGain • setup.blockAverageGradient noise k +
            setup.blockPhaseError noise k - setup.highPassIncrement noise k +
              setup.blockNoise noise k) := by
  rw [setup.hybridCenter_eq_lifted_add_meanLift noise (k + 1),
    setup.hybridCenter_eq_lifted_add_meanLift noise k,
    setup.blockLiftedCenter_succ noise k]
  unfold highPassIncrement
  module

/-- State-feedback energy
`B_k = H^2L^2||χ_k - xbar_{kp}||^2 + ||e_k||^2 + ||ρ_k||^2`. -/
noncomputable def stateFeedbackEnergy (noise : NoisePath Node E) (k : ℕ) : ℝ :=
  setup.blockGain ^ 2 * setup.L ^ 2 *
      ‖setup.blockStartHybridCenter noise k -
        setup.averageIterate noise (setup.blockStart k)‖ ^ 2 +
    ‖setup.blockPhaseError noise k‖ ^ 2 +
      ‖setup.highPassIncrement noise k‖ ^ 2

/-- Complete block horizon `N = Kp`. -/
def completeBlockHorizon (K : ℕ) : ℕ :=
  K * setup.period

/-- Replace only the constant stepsize, leaving all paper data and assumptions
unchanged. -/
def withStepsize (alphaT : ℝ) : Setup Node E :=
  { setup with alpha := alphaT }

/-- Oracle-noise process `ε_t`. This realizes the paper's random noise path as
a measurable stochastic process. The strict-past sigma-algebra below is
generated from the measured noise prefix. -/
structure OracleNoiseProcess (Ω Node E : Type*) [MeasurableSpace Ω]
    [MeasurableSpace E] where
  /-- Sample-path-valued oracle noise `ω ↦ ε(ω)`. -/
  noise : RandomNoisePath Ω Node E
  /-- The time-indexed oracle-noise tables are measurable random variables,
  so the strict-past history generates a genuine natural filtration. -/
  noise_measurable : ∀ t : ℕ, Measurable (fun ω : Ω => noise ω t)

namespace OracleNoiseProcess

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Time-indexed measurable noise-table stream. -/
noncomputable def noiseStream
    (oracle : OracleNoiseProcess Ω Node E) : ℕ → Ω → State Node E :=
  fun t ω => oracle.noise ω t

/-- Pointwise form of the canonical noise stream. -/
theorem noiseStream_apply
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) (ω : Ω) :
    oracle.noiseStream t ω = oracle.noise ω t := by
  rfl

/-- Measurability of the time-indexed noise-table stream. -/
theorem noiseStream_measurable
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) :
    Measurable (oracle.noiseStream t) := by
  simpa [noiseStream] using oracle.noise_measurable t

/-- Natural filtration generated by the measurable oracle-noise stream, using
SOptLib's canonical prefix-filtration primitive. -/
noncomputable def naturalFiltration
    (oracle : OracleNoiseProcess Ω Node E) :
    Filtration ℕ (by infer_instance : MeasurableSpace Ω) :=
  SOptLib.filtration oracle.noiseStream oracle.noiseStream_measurable

/-- Strict-past sigma-algebra generated by oracle-noise tables before time `t`.
This names the paper's `F_{t^-}` as the strict prefix of the natural
filtration generated by the oracle process.

Book JSON: `book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6`
uses `F_{t^-}` in the oracle law. PDF Section 2.1, equation (2.2) discussion:
`F_{t^-}` is the history before the `t`-th oracle sample. -/
noncomputable def strictPastMeasurableSpace
    (oracle : OracleNoiseProcess Ω Node E) :
    ℕ → MeasurableSpace Ω :=
  fun t => (oracle.naturalFiltration).seq t

/-- Source-form unfolding of the strict-past sigma-algebra. -/
theorem strictPastMeasurableSpace_eq
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) :
    oracle.strictPastMeasurableSpace t =
      ⨆ j < t,
        MeasurableSpace.comap (oracle.noiseStream j)
          (by infer_instance : MeasurableSpace (State Node E)) := by
  simp [strictPastMeasurableSpace, naturalFiltration]

end OracleNoiseProcess

section Stochastic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace E] [BorelSpace E]

/-- Indicator of the node-noise event `{ε_{i,t} ∈ event}`. -/
noncomputable def nodeNoiseEventIndicator
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) (i : Node)
    (event : Set E) (ω : Ω) : ℝ :=
  by
    classical
    exact if oracle.noise ω t i ∈ event then 1 else 0

/-- The same-time node-noise cylinder event
`{ω | ∀ i, ε_{i,t}(ω) ∈ events i}`. -/
def sameTimeNodeNoiseCylinder
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ)
    (events : Node → Set E) : Set Ω :=
  {ω | ∀ i : Node, oracle.noise ω t i ∈ events i}

/-- Indicator of the same-time node-noise cylinder
`{ω | ∀ i, ε_{i,t}(ω) ∈ B_i}`. -/
noncomputable def sameTimeNodeNoiseCylinderIndicator
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ)
    (events : Node → Set E) (ω : Ω) : ℝ :=
  by
    classical
    exact if ω ∈ sameTimeNodeNoiseCylinder (Node := Node) (E := E)
        oracle t events then 1 else 0

/-- Paper-local conditional mean-zero assertion
`E(ε_{i,t} | F_{t^-}) = 0`.

Book JSON: `book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6`;
PDF Section 2.1, equation (2.2) discussion, states
`E(ε_t | F_{t^-}) = 0`.

The clause is transparent and source-shaped: it records the first-moment
well-formedness implicit in the conditional expectation notation together with
the event-integral law over strict-past events. Sub-sigma witnesses,
sigma-finite trim facts, SOptLib bundled forms, and raw `condExp` equalities
are bridge theorem conclusions below, not primitive oracle assumptions. -/
def PaperConditionalMeanZeroGiven
    (μ : Measure Ω) (𝓕 : MeasurableSpace Ω)
    (ξ : Ω → E) : Prop :=
  Integrable ξ μ ∧
    ∀ A : Set Ω, @MeasurableSet Ω 𝓕 A →
      (∫ ω in A, ξ ω ∂μ) = 0

/-- Paper-local conditional second-moment bound
`E(||ε_{i,t}||^2 | F_{t^-}) <= σ^2`.

Book JSON: `book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6`;
PDF Section 2.1, equation (2.2) discussion, states that each node conditional
second moment is bounded by `σ^2`.

The clause is transparent and source-shaped: it records the L2
well-formedness implicit in the conditional second-moment notation together
with the event-integral second-moment inequality over strict-past events.
Sub-sigma witnesses, sigma-finite trim facts, raw `condExp` inequalities, and
SOptLib domain projections are bridge theorem conclusions below, not
source-facing oracle assumptions. -/
def PaperConditionalSecondMomentBoundGiven
    (μ : Measure Ω) (𝓕 : MeasurableSpace Ω)
    (ξ : Ω → E) (sigma : ℝ) : Prop :=
  Integrable (fun ω : Ω => ‖ξ ω‖ ^ 2) μ ∧
    ∀ A : Set Ω, @MeasurableSet Ω 𝓕 A →
      (∫ ω in A, ‖ξ ω‖ ^ 2 ∂μ) ≤ sigma ^ 2 * μ.real A

/-- A strict-past conditional-probability version for an event. This is the
event-integral characterization of `P(event | F_{t^-})`, with the
strict-past measurability required of a conditional-probability version. -/
def PaperConditionalProbabilityVersion
    (μ : Measure Ω) [IsFiniteMeasure μ] (𝓕 : MeasurableSpace Ω)
    (event : Set Ω) (prob : Ω → ℝ) : Prop :=
  Measurable[𝓕] prob ∧
    (∀ᵐ ω ∂μ, 0 ≤ prob ω ∧ prob ω ≤ 1) ∧
      ∀ A : Set Ω, @MeasurableSet Ω 𝓕 A →
        (∫ ω in A, prob ω ∂μ) = μ.real (A ∩ event)

/-- Integrability of a strict-past conditional-probability version is a
realization consequence of boundedness on a finite measure space, not a
primitive oracle clause. -/
theorem PaperConditionalProbabilityVersion.integrable
    (μ : Measure Ω) [IsFiniteMeasure μ] (𝓕 : MeasurableSpace Ω)
    (h𝓕 : 𝓕 ≤ mΩ)
    (event : Set Ω) (prob : Ω → ℝ)
    (_hprob : @PaperConditionalProbabilityVersion Ω mΩ μ _ 𝓕 event prob) :
    Integrable prob μ := by
  refine Integrable.of_bound (_hprob.1.mono h𝓕 le_rfl).aestronglyMeasurable 1 ?_
  filter_upwards [_hprob.2.1] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

/-- Event-integral characterization of a conditional-probability version,
projected from the transparent paper-local definition. -/
theorem PaperConditionalProbabilityVersion.setIntegral_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (𝓕 : MeasurableSpace Ω)
    (event : Set Ω) (prob : Ω → ℝ)
    (hprob : @PaperConditionalProbabilityVersion Ω mΩ μ _ 𝓕 event prob)
    (A : Set Ω) (hA : @MeasurableSet Ω 𝓕 A) :
    (∫ ω in A, prob ω ∂μ) = μ.real (A ∩ event) :=
  hprob.2.2 A hA

/-- Paper-local same-time cross-node conditional independence given the strict
past, stated on finite node-noise cylinders.

Book JSON: `book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6`;
PDF Section 2.1, equation (2.2) discussion, states same-time cross-node
conditional independence given `F_{t^-}`.

For every Borel node-event family, there are strict-past conditional
probability versions of the node events whose product is a conditional
probability version of the same-time cylinder. Raw `condExp` factorizations and
indicator well-definedness remain bridge obligations, not source-facing oracle
assumptions. -/
def PaperSameTimeNodeConditionallyIndependentGiven
    (μ : Measure Ω) [IsFiniteMeasure μ] (𝓕 : MeasurableSpace Ω)
    (oracle : @OracleNoiseProcess Ω Node E mΩ (by infer_instance)) (t : ℕ) : Prop := by
  letI : MeasurableSpace Ω := mΩ
  exact
    ∀ events : Node → Set E, (∀ i : Node, MeasurableSet (events i)) →
      ∃ condProb : Node → Ω → ℝ,
        (∀ i : Node,
          @PaperConditionalProbabilityVersion Ω mΩ μ _ 𝓕
            {ω : Ω | oracle.noise ω t i ∈ events i} (condProb i)) ∧
        @PaperConditionalProbabilityVersion Ω mΩ μ _ 𝓕
          {ω : Ω | ∀ i : Node, oracle.noise ω t i ∈ events i}
          (fun ω : Ω => ∏ i : Node, condProb i ω)

/-- The single paper-local stochastic oracle law stated in Section 2.1:
conditional unbiasedness, conditional second-moment bound, and same-time
cross-node conditional independence given the strict past.

Book JSON: `book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6`
states conditional mean zero, nodewise conditional second-moment bound, and
same-time cross-node conditional independence given `F_{t^-}`.

The predicate is the only source-facing oracle contract consumed by the paper
theorems in this file. Its transparent shape contains only the three source
clauses. Realization into SOptLib conditional-expectation wrappers, raw
indicator-domain facts, set-integral consequences, and finite-cylinder
`condExp` factorization is intentionally kept in bridge theorems below. Those
realization facts are source-derived proof obligations, not extra theorem-head
assumptions. -/
def StochasticOracleAssumptions (setup : Setup Node E)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) : Prop :=
  (∀ t : ℕ, ∀ i : Node,
    PaperConditionalMeanZeroGiven μ
      (oracle.strictPastMeasurableSpace t)
      (fun ω : Ω => oracle.noise ω t i)) ∧
  (∀ t : ℕ, ∀ i : Node,
    PaperConditionalSecondMomentBoundGiven μ
      (oracle.strictPastMeasurableSpace t)
      (fun ω : Ω => oracle.noise ω t i) setup.sigma) ∧
  (∀ t : ℕ,
    PaperSameTimeNodeConditionallyIndependentGiven
      (Node := Node) (E := E) μ (oracle.strictPastMeasurableSpace t) oracle t)

/-- The strict-past sigma-algebra is a genuine sub-sigma-algebra of the ambient
sample space. This is a Lean realization obligation for the natural-prefix
construction, not a primitive oracle assumption. -/
theorem strictPastMeasurableSpace_le
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) :
    oracle.strictPastMeasurableSpace t ≤ (by infer_instance : MeasurableSpace Ω) := by
  exact (oracle.naturalFiltration).le' t

/-- The finite-measure strict-past trim is sigma-finite. This is a realization
fact of the natural-prefix filtration and finite ambient measure, not a
primitive oracle assumption. -/
theorem strictPastMeasurableSpace_trim_sigmaFinite
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) :
    @SigmaFinite Ω (oracle.strictPastMeasurableSpace t)
      (μ.trim (strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t)) := by
  let hPast := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t
  letI : IsFiniteMeasure (μ.trim hPast) :=
    MeasureTheory.isFiniteMeasure_trim (μ := μ) hPast
  exact @MeasureTheory.IsFiniteMeasure.toSigmaFinite Ω
    (oracle.strictPastMeasurableSpace t) (μ.trim hPast) inferInstance

/-- Random generated primal array. -/
noncomputable def randomPrimalState (oracle : OracleNoiseProcess Ω Node E)
    (t : ℕ) (ω : Ω) : State Node E :=
  setup.primalState (oracle.noise ω) t

/-- Random arithmetic average `bar x_t`. -/
noncomputable def randomAverageIterate (oracle : OracleNoiseProcess Ω Node E)
    (t : ℕ) (ω : Ω) : E :=
  setup.averageIterate (oracle.noise ω) t

/-- Expected squared stationarity measure at the arithmetic average. -/
noncomputable def expectedGradientNormSq (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) : ℝ :=
  ∫ ω, ‖setup.averageGradient (setup.randomAverageIterate oracle t ω)‖ ^ 2 ∂μ

/-- Well-definedness of the paper expectation
`E ||grad f(bar x_t)||^2`: the stationarity integrand is integrable, so the
Bochner/Lebesgue integral above is not being used through Lean's fallback
value. The paper does not state this as an additional oracle assumption; it is
a realization obligation derived from the source setup and oracle law. -/
def expectedGradientNormSqWellDefined (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (t : ℕ) : Prop :=
  Integrable
    (fun ω : Ω => ‖setup.averageGradient (setup.randomAverageIterate oracle t ω)‖ ^ 2)
    μ

/-- Finite-horizon stationarity average
`T^{-1} sum_{t<T} E ||grad f(bar x_t)||^2`. -/
noncomputable def stationarityAverage (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T) fun t =>
      setup.expectedGradientNormSq μ oracle t

/-- Well-definedness of every expectation appearing in the finite-horizon
stationarity average. -/
def stationarityAverageWellDefined (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (T : ℕ) : Prop :=
  ∀ t : ℕ, t ∈ Finset.range T →
    setup.expectedGradientNormSqWellDefined μ oracle t

/-- Infimum over deterministic constant stepsizes used in Theorem 8.1. -/
noncomputable def infConstantStepsizeStationarity (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (T : ℕ) : ℝ :=
  sInf { value : ℝ |
    ∃ alpha : ℝ, 0 ≤ alpha ∧
      value = (setup.withStepsize alpha).stationarityAverage μ oracle T }

/-- The exact iid additive-noise oracle used by the matching lower bound:
the general Section 2.1 oracle laws plus iid coordinates, mean zero, and exact
variance `σ^2` at every node and time. -/
def ExactVarianceIidAdditiveNoise (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) : Prop :=
  setup.StochasticOracleAssumptions μ oracle ∧
    SOptLib.exactVarianceIidCenteredFamily μ
      (fun t i ω => oracle.noise ω t i) setup.sigma

/-- Expected consensus-energy sum `Q_N = sum_{t=0}^N E ||Q_t||_F^2`. -/
noncomputable def consensusEnergy (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun t =>
    ∫ ω, frobeniusNormSq (Node := Node) (E := E)
      (setup.consensusState (oracle.noise ω) t) ∂μ

/-- Expected displacement-energy sum
`D_N = sum_{t=0}^{N-1} E ||X_{t+1}-X_t||_F^2`. -/
noncomputable def displacementEnergy (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun t =>
    ∫ ω, frobeniusNormSq (Node := Node) (E := E)
      (setup.primalState (oracle.noise ω) (t + 1) -
        setup.primalState (oracle.noise ω) t) ∂μ

/-- Expected block-gradient sum
`G_K = sum_{k=0}^{K-1} E ||bar g_k||^2`. -/
noncomputable def blockGradientEnergy (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (K : ℕ) : ℝ :=
  Finset.sum (Finset.range K) fun k =>
    ∫ ω, ‖setup.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ

/-- Expected Section 6 feedback-energy sum `sum_{k<K} E B_k`. -/
noncomputable def stateFeedbackEnergySum (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node E) (K : ℕ) : ℝ :=
  Finset.sum (Finset.range K) fun k =>
    ∫ ω, setup.stateFeedbackEnergy (oracle.noise ω) k ∂μ

/-- Derived SOptLib-facing form of the source conditional mean-zero oracle law.
This is a projection from the single paper-local oracle law, not a separate
oracle assumption. -/
theorem conditionalMeanZero_conditionalExpectationEq
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    SOptLib.ConditionalExpectation.conditionalExpectationEq μ
      (oracle.strictPastMeasurableSpace t)
      (fun ω : Ω => oracle.noise ω t i) (fun _ => (0 : E)) := by
  let hmean := horacle.1 t i
  let hm := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t
  have hsf : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t) (μ.trim hm) := by
    exact strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t) (μ.trim hm) := hsf
  rw [SOptLib.ConditionalExpectation.conditionalExpectationEq_def]
  constructor
  · rw [SOptLib.ConditionalExpectation.conditionalExpectationWellDefined_def]
    exact ⟨hm, inferInstance, hmean.1⟩
  · have hzero :
        (fun _ : Ω => (0 : E)) =ᵐ[μ]
          condExp (oracle.strictPastMeasurableSpace t) μ
            (fun ω : Ω => oracle.noise ω t i) := by
      exact (condExp_eq_zero_of_setIntegral_eq_zero μ
        (oracle.strictPastMeasurableSpace t) hm
        (fun ω : Ω => oracle.noise ω t i) hmean.1
        (fun s hs _ => hmean.2 s hs)).symm
    exact hzero.symm

/-- Nodewise integrability required to realize the source mean-zero law as a
Mathlib conditional expectation. It is derived from the paper oracle law and
finite-measure natural-filtration realization, not assumed by the oracle
contract. -/
theorem conditionalMeanZero_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    Integrable (fun ω : Ω => oracle.noise ω t i) μ := by
  exact (horacle.1 t i).1

/-- Derived nonfallback domain for the conditional mean-zero expression.
This bridge is derived from the source oracle law plus finite-measure
strict-past realization facts, not projected from hidden source assumptions. -/
theorem conditionalMeanZero_wellDefined
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined μ
      (oracle.strictPastMeasurableSpace t)
      (fun ω : Ω => oracle.noise ω t i) := by
  exact ⟨strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t,
    strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t,
    setup.conditionalMeanZero_integrable μ oracle horacle t i⟩

/-- Derived raw conditional-expectation equality for the conditional mean-zero
law. This theorem exposes the Mathlib `condExp` form as a proof bridge from the
transparent paper-local oracle law. -/
theorem conditionalMeanZero_condExp
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    condExp (oracle.strictPastMeasurableSpace t) μ
        (fun ω : Ω => oracle.noise ω t i) =ᵐ[μ]
      fun _ => (0 : E) := by
  exact SOptLib.ConditionalExpectation.conditionalExpectationEq.ae_eq
    (setup.conditionalMeanZero_conditionalExpectationEq μ oracle horacle t i)

/-- Nodewise squared-integrability required to realize the source conditional
second-moment law as a Mathlib conditional expectation. It is a bridge theorem
conclusion, not a primitive oracle assumption. -/
theorem conditionalSecondMomentBound_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    Integrable (fun ω : Ω => ‖oracle.noise ω t i‖ ^ 2) μ := by
  exact (horacle.2.1 t i).1

/-- Derived nonfallback domain for the conditional second-moment expression.
This is derived from the single paper-local oracle law plus finite-measure
strict-past realization facts, not a separate oracle assumption. -/
theorem conditionalSecondMomentBound_wellDefined
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined μ
      (oracle.strictPastMeasurableSpace t)
      (fun ω : Ω => ‖oracle.noise ω t i‖ ^ 2) := by
  exact ⟨strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t,
    strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t,
    setup.conditionalSecondMomentBound_integrable μ oracle horacle t i⟩

/-- Derived conditional-expectation inequality form of the source conditional
second-moment oracle law. -/
theorem conditionalSecondMomentBound_condExp
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    condExp (oracle.strictPastMeasurableSpace t) μ
        (fun ω : Ω => ‖oracle.noise ω t i‖ ^ 2) ≤ᵐ[μ]
      fun _ => setup.sigma ^ 2 := by
  let hmoment := horacle.2.1 t i
  let hm := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t
  have hsf : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t) (μ.trim hm) := by
    exact strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t) (μ.trim hm) := hsf
  exact condExp_le_const_of_setIntegral_le μ
    (oracle.strictPastMeasurableSpace t)
    (fun ω : Ω => ‖oracle.noise ω t i‖ ^ 2) (setup.sigma ^ 2)
    hm hmoment.1 (fun A hA _hA_finite => by
      simpa [mul_comm] using hmoment.2 A hA)

/-- Derived nonfallback domain for same-time node-cylinder indicator
conditional expectations. This is a projection from the single paper-local
oracle law, not a separate oracle assumption. -/
theorem crossNodeCylinder_wellDefined
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ)
    (events : Node → Set E) (hevents : ∀ i : Node, MeasurableSet (events i)) :
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined μ
      (oracle.strictPastMeasurableSpace t)
      (sameTimeNodeNoiseCylinderIndicator (Node := Node) (E := E)
        oracle t events) := by
  classical
  rw [SOptLib.ConditionalExpectation.conditionalExpectationWellDefined_def]
  exact ⟨strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t,
    strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t,
    by
      simpa [sameTimeNodeNoiseCylinderIndicator, sameTimeNodeNoiseCylinder,
        Set.indicator] using
        (countableCylinderIndicator_integrable (μ := μ)
          (X := fun i ω => oracle.noise ω t i) (events := events)
          (fun i => by
            simpa [OracleNoiseProcess.noiseStream_apply] using
              (measurable_pi_apply i).comp (oracle.noiseStream_measurable t))
          hevents)⟩

/-- Derived nonfallback domain for one-node event-indicator conditional
expectations used in the same-time conditional-independence bridge. -/
theorem nodeNoiseEventIndicator_wellDefined
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node)
    (event : Set E) (_hevent : MeasurableSet event) :
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined μ
      (oracle.strictPastMeasurableSpace t)
      (nodeNoiseEventIndicator (Node := Node) (E := E)
        oracle t i event) := by
  classical
  have hcoord : Measurable (fun ω : Ω => oracle.noise ω t i) := by
    simpa [OracleNoiseProcess.noiseStream_apply] using
      (measurable_pi_apply i).comp (oracle.noiseStream_measurable t)
  have heventΩ : MeasurableSet {ω : Ω | oracle.noise ω t i ∈ event} :=
    _hevent.preimage hcoord
  have hind_meas :
      Measurable
        (nodeNoiseEventIndicator (Node := Node) (E := E) oracle t i event) := by
    unfold nodeNoiseEventIndicator
    exact measurable_const.ite heventΩ measurable_const
  have hind_int :
      Integrable
        (nodeNoiseEventIndicator (Node := Node) (E := E) oracle t i event) μ :=
    integrable_of_measurable_bounded_real hind_meas (C := 1) (by
      intro ω
      by_cases hω : oracle.noise ω t i ∈ event <;>
        simp [nodeNoiseEventIndicator, hω])
  rw [SOptLib.ConditionalExpectation.conditionalExpectationWellDefined_def]
  exact ⟨strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t,
    strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t,
    hind_int⟩

/-- Derived conditional-expectation factorization form of same-time
cross-node conditional independence. -/
theorem crossNodeConditionallyIndependent_condExp_factorization
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ)
    (events : Node → Set E) (hevents : ∀ i : Node, MeasurableSet (events i)) :
    condExp (oracle.strictPastMeasurableSpace t) μ
        (sameTimeNodeNoiseCylinderIndicator (Node := Node) (E := E)
          oracle t events) =ᵐ[μ]
      fun ω : Ω =>
        ∏ i : Node,
          condExp (oracle.strictPastMeasurableSpace t) μ
            (nodeNoiseEventIndicator (Node := Node) (E := E)
              oracle t i (events i)) ω := by
  classical
  obtain ⟨condProb, hnodeProb, hcylProb⟩ := horacle.2.2 t events hevents
  let hPast := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t
  have hsf : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t)
      (μ.trim hPast) := by
    exact strictPastMeasurableSpace_trim_sigmaFinite
      (Node := Node) (E := E) μ oracle t
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t)
      (μ.trim hPast) := hsf
  have hcoord : ∀ i : Node, Measurable (fun ω : Ω => oracle.noise ω t i) := by
    intro i
    simpa [OracleNoiseProcess.noiseStream_apply] using
      (measurable_pi_apply i).comp (oracle.noiseStream_measurable t)
  have hcyl_meas :
      MeasurableSet
        (sameTimeNodeNoiseCylinder (Node := Node) (E := E) oracle t events) := by
    rw [show sameTimeNodeNoiseCylinder (Node := Node) (E := E) oracle t events =
        ⋂ i : Node, {ω : Ω | oracle.noise ω t i ∈ events i} by
      ext ω
      simp [sameTimeNodeNoiseCylinder]]
    exact MeasurableSet.iInter (fun i => (hevents i).preimage (hcoord i))
  have hcyl_indicator_int :
      Integrable
        (sameTimeNodeNoiseCylinderIndicator (Node := Node) (E := E)
          oracle t events) μ :=
    (setup.crossNodeCylinder_wellDefined μ oracle horacle t events hevents).integrable
  have hcyl_prob_int : Integrable (fun ω : Ω => ∏ i : Node, condProb i ω) μ :=
    PaperConditionalProbabilityVersion.integrable μ
      (oracle.strictPastMeasurableSpace t) hPast
      (sameTimeNodeNoiseCylinder (Node := Node) (E := E) oracle t events)
      (fun ω : Ω => ∏ i : Node, condProb i ω) hcylProb
  have hcyl_prob_eq :
      (fun ω : Ω => ∏ i : Node, condProb i ω) =ᵐ[μ]
        condExp (oracle.strictPastMeasurableSpace t) μ
          (sameTimeNodeNoiseCylinderIndicator (Node := Node) (E := E)
            oracle t events) := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
      (μ := μ) (m := oracle.strictPastMeasurableSpace t)
      hPast hcyl_indicator_int ?_ ?_ ?_
    · intro s _hs _hfinite
      exact hcyl_prob_int.integrableOn
    · intro s hs _hfinite
      calc
        (∫ ω in s, ∏ i : Node, condProb i ω ∂μ) =
            μ.real (s ∩ sameTimeNodeNoiseCylinder (Node := Node) (E := E)
              oracle t events) :=
          PaperConditionalProbabilityVersion.setIntegral_eq μ
            (oracle.strictPastMeasurableSpace t)
            (sameTimeNodeNoiseCylinder (Node := Node) (E := E) oracle t events)
            (fun ω : Ω => ∏ i : Node, condProb i ω) hcylProb s hs
        _ = ∫ ω in s,
              sameTimeNodeNoiseCylinderIndicator (Node := Node) (E := E)
                oracle t events ω ∂μ := by
          symm
          change
            (∫ ω in s,
              (sameTimeNodeNoiseCylinder (Node := Node) (E := E)
                oracle t events).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) =
              μ.real (s ∩ sameTimeNodeNoiseCylinder (Node := Node) (E := E)
                oracle t events)
          rw [MeasureTheory.setIntegral_indicator hcyl_meas,
            MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    · exact hcylProb.1.aestronglyMeasurable
  have hcyl_condExp :
      condExp (oracle.strictPastMeasurableSpace t) μ
          (sameTimeNodeNoiseCylinderIndicator (Node := Node) (E := E)
            oracle t events) =ᵐ[μ]
        fun ω : Ω => ∏ i : Node, condProb i ω := by
    exact hcyl_prob_eq.symm
  have hnode_condExp : ∀ i : Node,
      condExp (oracle.strictPastMeasurableSpace t) μ
          (nodeNoiseEventIndicator (Node := Node) (E := E)
            oracle t i (events i)) =ᵐ[μ]
        condProb i := by
    intro i
    have hevent_i : MeasurableSet {ω : Ω | oracle.noise ω t i ∈ events i} :=
      (hevents i).preimage (hcoord i)
    have hindicator_i_int :
        Integrable
          (nodeNoiseEventIndicator (Node := Node) (E := E)
            oracle t i (events i)) μ :=
      (setup.nodeNoiseEventIndicator_wellDefined μ oracle horacle t i
        (events i) (hevents i)).integrable
    have hprob_i_int : Integrable (condProb i) μ :=
      PaperConditionalProbabilityVersion.integrable μ
        (oracle.strictPastMeasurableSpace t) hPast
        {ω : Ω | oracle.noise ω t i ∈ events i} (condProb i) (hnodeProb i)
    have hprob_i_eq :
        condProb i =ᵐ[μ]
          condExp (oracle.strictPastMeasurableSpace t) μ
            (nodeNoiseEventIndicator (Node := Node) (E := E)
              oracle t i (events i)) := by
      refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
        (μ := μ) (m := oracle.strictPastMeasurableSpace t)
        hPast hindicator_i_int ?_ ?_ ?_
      · intro s _hs _hfinite
        exact hprob_i_int.integrableOn
      · intro s hs _hfinite
        calc
          (∫ ω in s, condProb i ω ∂μ) =
              μ.real (s ∩ {ω : Ω | oracle.noise ω t i ∈ events i}) :=
            PaperConditionalProbabilityVersion.setIntegral_eq μ
              (oracle.strictPastMeasurableSpace t)
              {ω : Ω | oracle.noise ω t i ∈ events i}
              (condProb i) (hnodeProb i) s hs
          _ = ∫ ω in s,
                nodeNoiseEventIndicator (Node := Node) (E := E)
                  oracle t i (events i) ω ∂μ := by
            symm
            change
              (∫ ω in s,
                {ω : Ω | oracle.noise ω t i ∈ events i}.indicator
                  (fun _ : Ω => (1 : ℝ)) ω ∂μ) =
                μ.real (s ∩ {ω : Ω | oracle.noise ω t i ∈ events i})
            rw [MeasureTheory.setIntegral_indicator hevent_i,
              MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      · exact (hnodeProb i).1.aestronglyMeasurable
    exact hprob_i_eq.symm
  have hnode_all :
      ∀ᵐ ω ∂μ, ∀ i : Node,
        condExp (oracle.strictPastMeasurableSpace t) μ
            (nodeNoiseEventIndicator (Node := Node) (E := E)
              oracle t i (events i)) ω = condProb i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact hnode_condExp
  have hprod :
      (fun ω : Ω =>
        ∏ i : Node,
          condExp (oracle.strictPastMeasurableSpace t) μ
            (nodeNoiseEventIndicator (Node := Node) (E := E)
              oracle t i (events i)) ω) =ᵐ[μ]
        fun ω : Ω => ∏ i : Node, condProb i ω := by
    filter_upwards [hnode_all] with ω hω
    apply Finset.prod_congr rfl
    intro i _hi
    exact hω i
  exact hcyl_condExp.trans hprod.symm

/-- Direct finite-cylinder factorization supplied by the source same-time
conditional-independence clause. This is the transparent paper-local statement
from which raw `condExp` factorization is a later bridge theorem. -/
theorem crossNodeConditionallyIndependent_finiteCylinder_factorization
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ)
    (events : Node → Set E) (hevents : ∀ i : Node, MeasurableSet (events i)) :
    ∃ condProb : Node → Ω → ℝ,
      (∀ i : Node,
        @PaperConditionalProbabilityVersion Ω mΩ μ _
          (oracle.strictPastMeasurableSpace t)
          {ω : Ω | oracle.noise ω t i ∈ events i} (condProb i)) ∧
      @PaperConditionalProbabilityVersion Ω mΩ μ _
        (oracle.strictPastMeasurableSpace t)
        (sameTimeNodeNoiseCylinder (Node := Node) (E := E) oracle t events)
        (fun ω : Ω => ∏ i : Node, condProb i ω) := by
  exact horacle.2.2 t events hevents

/-- Event-integral form of conditional mean zero over strict-past events,
projected directly from the source-shaped oracle law. -/
theorem conditionalMeanZero_setIntegral_zero
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node)
    (A : Set Ω) (_hA : @MeasurableSet Ω (oracle.strictPastMeasurableSpace t) A) :
    (∫ ω in A, oracle.noise ω t i ∂μ) = 0 := by
  exact (horacle.1 t i).2 A _hA

/-- Event-integral form of the conditional second-moment bound over strict-past
events, projected directly from the source-shaped oracle law. -/
theorem conditionalSecondMomentBound_setIntegral_le
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node)
    (A : Set Ω) (_hA : @MeasurableSet Ω (oracle.strictPastMeasurableSpace t) A) :
    (∫ ω in A, ‖oracle.noise ω t i‖ ^ 2 ∂μ) ≤
      setup.sigma ^ 2 * μ.real A := by
  exact (horacle.2.1 t i).2 A _hA

/- A node noise coordinate is square-integrable. -/
theorem nodeNoise_memLp_two
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) (i : Node) :
    MemLp (fun ω : Ω => oracle.noise ω t i) 2 μ := by
  exact (memLp_two_iff_integrable_sq_norm
    ((oracle.noiseStream_measurable t).eval.aestronglyMeasurable)).2
    (setup.conditionalSecondMomentBound_integrable μ oracle horacle t i)

/- A deterministic row applied to one noise table is square-integrable. -/
theorem weightedNoise_memLp_two
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ)
    (w : RowVector Node) :
    MemLp (fun ω : Ω => weightedState (Node := Node) (E := E) w
      (oracle.noise ω t)) 2 μ := by
  unfold weightedState
  apply memLp_finset_sum Finset.univ
  intro i _hi
  exact (setup.nodeNoise_memLp_two μ oracle horacle t i).const_smul (w i)

/- Conditional expectations with respect to the sigma-algebra generated by
`Y` are determined by their integrals over measurable preimages under `Y`.
This is the `MeasurableSpace.comap` specialization of Mathlib's conditional
expectation uniqueness theorem. -/
theorem condExp_comap_eq_of_preimage_setIntegral_eq
    {S F : Type*} [MeasurableSpace S]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → S) (hY : Measurable Y) (f g : Ω → F)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hpre : ∀ C : Set S, MeasurableSet C →
      (∫ ω in Y ⁻¹' C, f ω ∂μ) = ∫ ω in Y ⁻¹' C, g ω ∂μ) :
    condExp (MeasurableSpace.comap Y inferInstance) μ f =ᵐ[μ]
      condExp (MeasurableSpace.comap Y inferInstance) μ g := by
  exact _root_.condExp_comap_eq_of_preimage_setIntegral_eq
    μ Y hY f g hf hg hpre

/- Event-level conditional factorization and strict-past centering imply zero
cross moment.  This is the generic monotone-class/Bochner bridge used below:
the event transfer first identifies `E[Y | sigma(X)]` as zero, after which the
standard adapted-inner-product cancellation closes the covariance. -/
theorem inner_integral_eq_zero_of_conditional_event_transfer
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (past : MeasurableSpace Ω) (hm : past ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    (X Y : Ω → F) (hX_meas : @Measurable Ω F mΩ _ X)
    (hY_meas : @Measurable Ω F mΩ _ Y)
    (hY_int : Integrable Y μ)
    (hinner_int : Integrable (fun ω => ⟪X ω, Y ω⟫_ℝ) μ)
    (hweightedEvent : ∀ B : Set F, MeasurableSet B →
      ∀ C : Set F, MeasurableSet C →
        (∫ ω in Y ⁻¹' C, (X ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
        ∫ ω in Y ⁻¹' C,
          condExp past μ ((X ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω ∂μ)
    (hpastCentered : ∀ B : Set F, MeasurableSet B → ∀ v : F,
      (∫ ω, condExp past μ ((X ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω *
        ⟪v, Y ω⟫_ℝ ∂μ) = 0) :
    (∫ ω, ⟪X ω, Y ω⟫_ℝ ∂μ) = 0 := by
  letI : MeasurableSpace Ω := mΩ
  have hX_aesm :
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] X μ :=
    (comap_measurable X).aestronglyMeasurable
  exact integral_inner_eq_zero_of_conditional_event_transfer μ past hm X Y hX_meas
    hX_aesm hY_meas hY_int hinner_int hweightedEvent hpastCentered

/- Distinct same-time node noises have zero cross covariance, by specializing
the finite-family conditional-factorization cancellation theorem. -/
theorem sameTime_distinctNode_inner_integral_eq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ)
    (i j : Node) (hij : i ≠ j) :
    (∫ ω, ⟪oracle.noise ω t i, oracle.noise ω t j⟫_ℝ ∂μ) = 0 := by
  classical
  let hm := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle t
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t) (μ.trim hm) :=
    strictPastMeasurableSpace_trim_sigmaFinite (Node := Node) (E := E) μ oracle t
  exact integral_inner_eq_zero_of_condExp_indicator_factorization_of_condExp_eq_zero
    μ (oracle.strictPastMeasurableSpace t) hm
    (fun l ω => oracle.noise ω t l)
    (by
      simpa [sameTimeNodeNoiseCylinderIndicator, sameTimeNodeNoiseCylinder,
        nodeNoiseEventIndicator, Set.indicator] using
        setup.crossNodeConditionallyIndependent_condExp_factorization
          μ oracle horacle t)
    i j hij
    (by
      simpa [OracleNoiseProcess.noiseStream_apply] using
        (measurable_pi_apply i).comp (oracle.noiseStream_measurable t))
    (by
      simpa [OracleNoiseProcess.noiseStream_apply] using
        (measurable_pi_apply j).comp (oracle.noiseStream_measurable t))
    (setup.conditionalMeanZero_condExp μ oracle horacle t j)
    (setup.nodeNoise_memLp_two μ oracle horacle t i)
    (setup.nodeNoise_memLp_two μ oracle horacle t j)

/- Sharp one-phase weighted-noise second moment, with all off-diagonal node
terms canceled rather than bounded by a node-count Cauchy--Schwarz factor. -/
theorem sameTime_weightedNoise_secondMoment_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ)
    (w : RowVector Node) :
    (∫ ω, ‖weightedState (Node := Node) (E := E) w
        (oracle.noise ω t)‖ ^ 2 ∂μ) ≤
      rowNormSq (Node := Node) w * setup.sigma ^ 2 := by
  classical
  simpa only [weightedState, rowNormSq] using
    (integral_norm_sq_finset_sum_smul_le_of_cross_zero
      μ Finset.univ w (fun i ω => oracle.noise ω t i) (setup.sigma ^ 2)
      (fun i _hi =>
        (setup.nodeNoise_memLp_two μ oracle horacle t i).aestronglyMeasurable)
      (fun i _hi =>
        (memLp_two_iff_integrable_sq_norm
          (setup.nodeNoise_memLp_two μ oracle horacle t i).aestronglyMeasurable).1
          (setup.nodeNoise_memLp_two μ oracle horacle t i))
      (fun i _hi j _hj hij =>
        setup.sameTime_distinctNode_inner_integral_eq_zero
          μ oracle horacle t i j hij)
      (fun i _hi => by
        have hi := setup.conditionalSecondMomentBound_setIntegral_le
          μ oracle horacle t i Set.univ MeasurableSet.univ
        simpa only [MeasureTheory.setIntegral_univ, MeasureTheory.probReal_univ,
          mul_one] using hi))

/- Weighted noises at distinct times are orthogonal by strict-past
measurability of the earlier sample and conditional centering of the later
sample. -/
theorem weightedNoise_crossTime_inner_integral_eq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (w v : RowVector Node) {s u : ℕ} (hsu : s < u) :
    (∫ ω, ⟪weightedState (Node := Node) (E := E) w (oracle.noise ω s),
        weightedState (Node := Node) (E := E) v (oracle.noise ω u)⟫_ℝ ∂μ) = 0 := by
  classical
  let X : Ω → E := fun ω =>
    weightedState (Node := Node) (E := E) w (oracle.noise ω s)
  have hXmem : MemLp X 2 μ := setup.weightedNoise_memLp_two μ oracle horacle s w
  have hXmeas : Measurable[oracle.strictPastMeasurableSpace u] X := by
    unfold X weightedState
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    have hs : Measurable[oracle.strictPastMeasurableSpace u]
        (oracle.noiseStream s) :=
      SOptLib.measurable_sample_of_lt_prefixFiltration
        oracle.noiseStream oracle.noiseStream_measurable hsu
    exact ((measurable_pi_apply i).comp hs).const_smul (w i)
  have hterm_zero (i : Node) :
      (∫ ω, ⟪X ω, oracle.noise ω u i⟫_ℝ ∂μ) = 0 := by
    have hnoise := setup.nodeNoise_memLp_two μ oracle horacle u i
    have hinner : Integrable (fun ω =>
        ⟪oracle.noise ω u i, X ω - (0 : E)⟫_ℝ) μ := by
      have hprod : Integrable (fun ω => ‖oracle.noise ω u i‖ * ‖X ω‖) μ := by
        simpa [Pi.mul_apply] using
          (MeasureTheory.MemLp.integrable_mul hnoise.norm hXmem.norm :
            Integrable ((fun ω => ‖oracle.noise ω u i‖) * (fun ω => ‖X ω‖)) μ)
      have hbase : Integrable (fun ω => ⟪oracle.noise ω u i, X ω⟫_ℝ) μ :=
        hprod.mono'
          (AEStronglyMeasurable.inner hnoise.aestronglyMeasurable
            hXmem.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun ω => by
            simpa [Real.norm_eq_abs] using
              abs_real_inner_le_norm (oracle.noise ω u i) (X ω))
      simpa using hbase
    let hm := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle u
    letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace u) (μ.trim hm) :=
      strictPastMeasurableSpace_trim_sigmaFinite
        (Node := Node) (E := E) μ oracle u
    have hzero := integral_inner_sub_const_eq_zero_of_condExp_eq_zero
      (P := μ) (m := oracle.strictPastMeasurableSpace u) hm hXmeas
      (setup.conditionalMeanZero_condExp μ oracle horacle u i)
      (setup.conditionalMeanZero_integrable μ oracle horacle u i) hinner
    simpa [X, real_inner_comm] using hzero
  have hterm_int (i : Node) : Integrable (fun ω =>
      v i * ⟪X ω, oracle.noise ω u i⟫_ℝ) μ := by
    have hnoise := setup.nodeNoise_memLp_two μ oracle horacle u i
    have hprod : Integrable (fun ω => ‖X ω‖ * ‖oracle.noise ω u i‖) μ := by
      simpa [Pi.mul_apply] using
        (MeasureTheory.MemLp.integrable_mul hXmem.norm hnoise.norm :
          Integrable ((fun ω => ‖X ω‖) *
            (fun ω => ‖oracle.noise ω u i‖)) μ)
    have hi : Integrable (fun ω => ⟪X ω, oracle.noise ω u i⟫_ℝ) μ :=
      hprod.mono'
        (AEStronglyMeasurable.inner hXmem.aestronglyMeasurable
          hnoise.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using
            abs_real_inner_le_norm (X ω) (oracle.noise ω u i))
    exact hi.const_mul _
  change (∫ ω, ⟪X ω,
      weightedState (Node := Node) (E := E) v (oracle.noise ω u)⟫_ℝ ∂μ) = 0
  simp only [weightedState, inner_sum, real_inner_smul_right]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i _hi
    rw [MeasureTheory.integral_const_mul, hterm_zero i, mul_zero]
  · exact fun i _hi => hterm_int i

/- The block noise is conditionally centered at the block-start sigma-algebra. -/
theorem blockNoise_conditionalExpectationEq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (k : ℕ) :
    SOptLib.ConditionalExpectation.conditionalExpectationEq μ
      (oracle.strictPastMeasurableSpace (setup.blockStart k))
      (fun ω : Ω => setup.blockNoise (oracle.noise ω) k)
      (fun _ => (0 : E)) := by
  classical
  let hm := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle
    (setup.blockStart k)
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace (setup.blockStart k))
      (μ.trim hm) := strictPastMeasurableSpace_trim_sigmaFinite
        (Node := Node) (E := E) μ oracle (setup.blockStart k)
  unfold blockNoise weightedState
  have hsum :
      (fun ω : Ω => ∑ ri ∈
        (Finset.univ.product Finset.univ : Finset (Fin setup.period × Node)),
          setup.influence ri.1.1 ri.2 •
            oracle.noise ω (setup.blockStart k + ri.1.1) ri.2) =
      (fun ω : Ω => ∑ r : Fin setup.period, ∑ i : Node,
        setup.influence r.1 i •
          oracle.noise ω (setup.blockStart k + r.1) i) := by
    funext ω
    exact Finset.sum_finset_product
      (Finset.univ.product Finset.univ) Finset.univ (fun _ => Finset.univ)
      (fun _ => by simp)
  rw [← hsum]
  exact condExp_finset_sum_eq_zero_of_filtration_mono μ oracle.naturalFiltration
      (setup.blockStart k)
      (Finset.univ.product Finset.univ : Finset (Fin setup.period × Node))
      (fun ri => setup.blockStart k + ri.1.1)
      (fun ri => setup.influence ri.1.1 ri.2)
      (fun ri ω => oracle.noise ω (setup.blockStart k + ri.1.1) ri.2)
      (fun ri _hri => Nat.le_add_right _ _)
      (fun ri _hri => setup.conditionalMeanZero_conditionalExpectationEq
        μ oracle horacle (setup.blockStart k + ri.1.1) ri.2)

/-- Source-derived conditional mean-zero and second-moment bound for the block
noise `ζ_k` in (5.8). -/
theorem blockNoise_conditional_mean_zero_and_secondMoment
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (_horacle : setup.StochasticOracleAssumptions μ oracle) (k : ℕ) :
    SOptLib.ConditionalExpectation.conditionalExpectationEq μ
        (oracle.strictPastMeasurableSpace (setup.blockStart k))
        (fun ω : Ω => setup.blockNoise (oracle.noise ω) k) (fun _ => (0 : E)) ∧
      ∫ ω, ‖setup.blockNoise (oracle.noise ω) k‖ ^ 2 ∂μ ≤
        setup.period * setup.influenceSecondMoment * setup.sigma ^ 2 := by
  classical
  let δ : Fin setup.period → Ω → E := fun r ω =>
    weightedState (Node := Node) (E := E) (setup.influence r.1)
      (oracle.noise ω (setup.blockStart k + r.1))
  have hmem (r : Fin setup.period) : MemLp (δ r) 2 μ :=
    setup.weightedNoise_memLp_two μ oracle _horacle
      (setup.blockStart k + r.1) (setup.influence r.1)
  have hsq (r : Fin setup.period) : Integrable (fun ω => ‖δ r ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hmem r).aestronglyMeasurable).1 (hmem r)
  have hcross (r : Fin setup.period) (_hr : r ∈ Finset.univ)
      (s : Fin setup.period) (_hs : s ∈ Finset.univ) (hrs : r ≠ s) :
      (∫ ω, ⟪δ r ω, δ s ω⟫_ℝ ∂μ) = 0 := by
    rcases lt_or_gt_of_ne hrs with hrs_lt | hsr_lt
    · exact setup.weightedNoise_crossTime_inner_integral_eq_zero
        μ oracle _horacle (setup.influence r.1) (setup.influence s.1)
        (Nat.add_lt_add_left hrs_lt (setup.blockStart k))
    · have hzero := setup.weightedNoise_crossTime_inner_integral_eq_zero
        μ oracle _horacle (setup.influence s.1) (setup.influence r.1)
        (Nat.add_lt_add_left hsr_lt (setup.blockStart k))
      simpa [δ, real_inner_comm] using hzero
  have hdiag := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    μ Finset.univ δ
    (fun r _hr => (hmem r).aestronglyMeasurable)
    (fun r _hr => hsq r) hcross
  have hmoment :
      (∫ ω, ‖setup.blockNoise (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        setup.period * setup.influenceSecondMoment * setup.sigma ^ 2 := by
    change (∫ ω, ‖∑ r : Fin setup.period, δ r ω‖ ^ 2 ∂μ) ≤ _
    rw [hdiag]
    calc
      (∑ r : Fin setup.period, ∫ ω, ‖δ r ω‖ ^ 2 ∂μ) ≤
          ∑ r : Fin setup.period,
            rowNormSq (Node := Node) (setup.influence r.1) * setup.sigma ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        exact setup.sameTime_weightedNoise_secondMoment_le μ oracle _horacle
          (setup.blockStart k + r.1) (setup.influence r.1)
      _ = setup.period * setup.influenceSecondMoment * setup.sigma ^ 2 := by
        have hp : (setup.period : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt setup.period_pos)
        unfold influenceSecondMoment FiniteNetwork.periodicInfluenceSecondMoment rowNormSq
        rw [← Finset.sum_mul]
        field_simp [hp]
  exact ⟨setup.blockNoise_conditionalExpectationEq_zero μ oracle _horacle k, hmoment⟩

end Stochastic

/-- Euclidean norm of a scalar node vector. -/
noncomputable def rowEuclideanNorm (w : RowVector Node) : ℝ :=
  Real.sqrt (rowNormSq (Node := Node) w)

/-- Frobenius norm of a distributed state. -/
noncomputable def stateFrobeniusNorm (X : State Node E) : ℝ :=
  Real.sqrt (frobeniusNormSq (Node := Node) (E := E) X)


theorem statePairwiseDistance_le_diameter (X : State Node E) (i j : Node) :
    ‖X i - X j‖ ≤ (Metric.diam ∘ Set.range) X := by
  simpa only [Function.comp_apply, dist_eq_norm] using
    Metric.dist_le_diam_of_mem (Set.finite_range X).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)

theorem statePairwiseDiameter_nonneg (X : State Node E) :
    0 ≤ (Metric.diam ∘ Set.range) X := by
  exact Metric.diam_nonneg

theorem norm_weightedState_sub_weightedState_le_statePairwiseDiameter
    (p q : RowVector Node)
    (hp : ∀ i : Node, 0 ≤ p i) (hq : ∀ i : Node, 0 ≤ q i)
    (hp_sum : ∑ i : Node, p i = 1) (hq_sum : ∑ i : Node, q i = 1)
    (X : State Node E) :
    ‖weightedState (Node := Node) (E := E) p X -
        weightedState (Node := Node) (E := E) q X‖ ≤
      (Metric.diam ∘ Set.range) X := by
  simpa only [weightedState, Function.comp_apply] using
    (FiniteNetwork.norm_sum_smul_sub_sum_smul_le_diam_range
      (iota := Node) (E := E) p q hp hq hp_sum hq_sum X)

/-- A row-stochastic matrix whose entries have the common lower bound `β`
contracts the pairwise diameter by the Dobrushin factor `1 - nβ`. -/
theorem rowMinorized_statePairwiseDiameter_contraction
    {A : NodeMatrix Node} {β : ℝ}
    (hA : RowStochastic (Node := Node) A)
    (hβ : ∀ i j : Node, β ≤ A i j) (X : State Node E) :
    (Metric.diam ∘ Set.range)
        (leftMul (Node := Node) (E := E) A X) ≤
      (1 - (nodeCount (Node := Node) : ℝ) * β) *
        (Metric.diam ∘ Set.range) X := by
  classical
  simpa only [Function.comp_apply, leftMul, nodeCount] using
    (Matrix.diam_range_smulVec_le_one_sub_card_mul_of_mem_rowStochastic_of_minorized
      (Node := Node) (E := E) (A := A) (beta := β)
      (Matrix.mem_rowStochastic_iff_sum.mpr hA) hβ X)

theorem rowStochastic_statePairwiseDiameter_leftMul_le
    {A : NodeMatrix Node} (hA : RowStochastic (Node := Node) A)
    (X : State Node E) :
    (Metric.diam ∘ Set.range)
        (leftMul (Node := Node) (E := E) A X) ≤
      (Metric.diam ∘ Set.range) X := by
  classical
  simpa only [Function.comp_apply, leftMul] using
    Matrix.diam_range_smulVec_le_of_mem_rowStochastic
      (A := A) (Matrix.mem_rowStochastic_iff_sum.mpr hA) X

theorem consecutiveProduct_rowStochastic
    (A : ℕ → NodeMatrix Node)
    (hA : ∀ s : ℕ, RowStochastic (Node := Node) (A s))
    (t j : ℕ) :
    RowStochastic (Node := Node) (consecutiveProduct (Node := Node) A t j) := by
  classical
  simpa only [RowStochastic, consecutiveProduct_eq_finiteNetwork,
    Matrix.mem_rowStochastic_iff_sum] using
      (FiniteNetwork.consecutiveMatrixProduct_mem_rowStochastic A t j
        (fun s _ => Matrix.mem_rowStochastic_iff_sum.mpr (hA (t + s))))

theorem consecutiveProduct_add
    (A : ℕ → NodeMatrix Node) (t j k : ℕ) :
    consecutiveProduct (Node := Node) A t (j + k) =
      matrixMul (Node := Node)
        (consecutiveProduct (Node := Node) A (t + j) k)
        (consecutiveProduct (Node := Node) A t j) := by
  let localMonoid : Monoid (NodeMatrix Node) := {
    one := identityMatrix (Node := Node)
    mul := matrixMul (Node := Node)
    one_mul := matrixMul_identity_left (Node := Node)
    mul_one := matrixMul_identity_right (Node := Node)
    mul_assoc := fun A B C => (matrixMul_assoc_local (Node := Node) A B C).symm
  }
  have hproduct :
      consecutiveProduct (Node := Node) A =
        @FiniteNetwork.consecutiveProduct (NodeMatrix Node) localMonoid A := by
    funext s n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        exact congrArg (matrixMul (Node := Node) (A (s + n))) ih
  simpa only [hproduct] using
    (@FiniteNetwork.consecutiveProduct_add (NodeMatrix Node) localMonoid A t j k)

theorem stateFrobeniusNorm_consensusError_le_sqrt_card_mul_diameter
    (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E) X) ≤
      Real.sqrt (nodeCount (Node := Node) : ℝ) *
        (Metric.diam ∘ Set.range) X := by
  simpa [stateFrobeniusNorm, frobeniusNormSq, consensusError,
    arithmeticAverage, nodeCount, Function.comp_apply,
    FiniteNetwork.consensusError_apply, FiniteNetwork.meanState,
    SOptLib.finiteUniformAverage, PiLp.norm_eq_of_L2] using
    (FiniteNetwork.consensusError_piLpNorm_le_sqrt_card_mul_statePairwiseDiameter
      (Node := Node) (E := E) X)

theorem norm_apply_le_stateFrobeniusNorm (X : State Node E) (i : Node) :
    ‖X i‖ ≤ stateFrobeniusNorm (Node := Node) (E := E) X := by
  classical
  have hsquare : ‖X i‖ ^ 2 ≤ ∑ j : Node, ‖X j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖X j‖) (Finset.mem_univ i)
  calc
    ‖X i‖ = Real.sqrt (‖X i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j : Node, ‖X j‖ ^ 2) := Real.sqrt_le_sqrt hsquare
    _ = stateFrobeniusNorm (Node := Node) (E := E) X := rfl

theorem statePairwiseDiameter_le_two_mul_consensusError_frobeniusNorm
    (X : State Node E) :
    (Metric.diam ∘ Set.range) X ≤
      2 * stateFrobeniusNorm (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E) X) := by
  simpa [stateFrobeniusNorm, frobeniusNormSq, consensusError,
    arithmeticAverage, nodeCount, Function.comp_apply,
    FiniteNetwork.consensusError_apply, FiniteNetwork.meanState,
    SOptLib.finiteUniformAverage, PiLp.norm_eq_of_L2] using
    (FiniteNetwork.statePairwiseDiameter_le_two_mul_consensusError_piLpNorm
      (Node := Node) (E := E) X)

/-- Generic arbitrary-window row-product estimate implementing the row half
of Lemma 4.2: compose products, contract every minorized complete block, use
row-stochastic nonexpansiveness on the remainder, and convert pairwise
diameter to and from the consensus Frobenius norm. -/
theorem rowConsecutiveProduct_consensusError_frobenius_rate_of_blockMinorization
    (A : ℕ → NodeMatrix Node) (β δ r : ℝ) (ell : ℕ)
    (hell : 0 < ell) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hr_nonneg : 0 ≤ r) (hr_ell : r ^ ell = δ)
    (hδ_block : 1 - (nodeCount (Node := Node) : ℝ) * β ≤ δ)
    (hrow : ∀ s : ℕ, RowStochastic (Node := Node) (A s))
    (hblock : ∀ (t : ℕ) (i j : Node),
      β ≤ consecutiveProduct (Node := Node) A t ell i j) :
    ∀ (t j : ℕ) (X : State Node E),
      stateFrobeniusNorm (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E)
              (consecutiveProduct (Node := Node) A t j) X)) ≤
        (2 * Real.sqrt (nodeCount (Node := Node) : ℝ) / δ) * r ^ j *
          stateFrobeniusNorm (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E) X) := by
  classical
  simpa [stateFrobeniusNorm, frobeniusNormSq, consensusError,
    arithmeticAverage, nodeCount, leftMul, consecutiveProduct_eq_finiteNetwork,
    FiniteNetwork.consensusError_apply, FiniteNetwork.meanState,
    SOptLib.finiteUniformAverage, PiLp.norm_eq_of_L2] using
    (FiniteNetwork.consensusError_piLpNorm_consecutiveMatrixProduct_le_geometric_of_blockMinorization
      (Node := Node) (E := E) A β δ r ell hell hδ_pos hδ_lt hr_nonneg
      hr_ell hδ_block
      (fun s => Matrix.mem_rowStochastic_iff_sum.mpr (hrow s))
      (by
        intro t i j
        simpa only [consecutiveProduct_eq_finiteNetwork] using hblock t i j))

/-- Operator two-norm of a scalar node matrix, modeled by its action on scalar
node vectors with the paper's Euclidean norm. -/
noncomputable def matrixEuclideanOperatorNorm (A : NodeMatrix Node) : ℝ :=
  sInf { c : ℝ | 0 ≤ c ∧
    ∀ x : RowVector Node,
      rowEuclideanNorm (Node := Node)
        (matrixMulVector (Node := Node) A x) ≤
          c * rowEuclideanNorm (Node := Node) x }

/-- Finite maximum over one network period, represented as the supremum of the
finite range. -/
noncomputable def periodMax (value : Fin setup.period → ℝ) : ℝ :=
  sSup (Set.range value)

/-- All-ones scalar row vector. -/
def oneRow : RowVector Node :=
  fun _ => 1


/-- Consensus projector matrix `Π = I - 11^T/n`. -/
noncomputable def consensusProjectorMatrix : NodeMatrix Node :=
  by classical exact FiniteNetwork.consensusProjectorMatrix (Node := Node)

/-- Perron residual matrix `S_t = I - v_t 1^T`. -/
noncomputable def perronResidualMatrix (t : ℕ) : NodeMatrix Node :=
  by classical exact FiniteNetwork.perronResidualMatrix (setup.perronRight t)

theorem leftMul_perronResidualMatrix (t : ℕ) (X : State Node E) :
    leftMul (Node := Node) (E := E) (setup.perronResidualMatrix t) X =
      setup.perronResidual t X := by
  classical
  simpa only [leftMul, perronResidualMatrix, perronResidual] using
    (FiniteNetwork.perronResidualMatrix_smulVec
      (v := setup.perronRight t) (W := X))

theorem leftMul_C_perronResidual (t : ℕ) (X : State Node E) :
    leftMul (Node := Node) (E := E) (setup.C t) (setup.perronResidual t X) =
      leftMul (Node := Node) (E := E) (setup.C t) X -
        (fun i => setup.perronRight (t + 1) i • ∑ j : Node, X j) := by
  simpa only [leftMul, perronResidual] using
    (FiniteNetwork.smulVec_perronResidual_eq_sub_rankOne_of_mulVec_eq
      (A := setup.C t) (v := setup.perronRight t)
      (vNext := setup.perronRight (t + 1)) (X := X)
      (by funext i; exact setup.C_mul_perronRight t i))

/- One-step source recurrence (6.4): the mean joint coordinate is propagated
by `C_t`, with the new gradient-table increment projected by `S_{t+1}`. -/
theorem meanJointCoordinate_succ (noise : NoisePath Node E) (t : ℕ) :
    setup.meanJointCoordinate noise (t + 1) =
      leftMul (Node := Node) (E := E) (setup.C t)
          (setup.meanJointCoordinate noise t) +
        leftMul (Node := Node) (E := E) (setup.perronResidualMatrix (t + 1))
          (setup.gradientTable (setup.primalState noise (t + 1)) -
            setup.gradientTable (setup.primalState noise t)) := by
  unfold meanJointCoordinate
  let Zt := setup.gradientTable (setup.primalState noise t)
  let Zn := setup.gradientTable (setup.primalState noise (t + 1))
  have hmean : setup.meanTrackerError noise (t + 1) =
      leftMul (Node := Node) (E := E) (setup.C t)
          (setup.meanTrackerError noise t) +
        leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.C t) (identityMatrix (Node := Node)))
          Zt := by
    exact setup.meanTrackerError_succ noise t
  rw [hmean, leftMul_add_state, setup.leftMul_C_perronResidual,
    setup.leftMul_perronResidualMatrix, leftMul_sub_identity]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, perronResidual,
    FiniteNetwork.perronResidual_apply, Zt, Zn, Finset.sum_sub_distrib, smul_sub]
  abel

theorem gradientTable_difference_frobeniusSq_le
    (X Y : State Node E) :
    frobeniusNormSq (Node := Node) (E := E)
        (setup.gradientTable X - setup.gradientTable Y) ≤
      setup.L ^ 2 * frobeniusNormSq (Node := Node) (E := E) (X - Y) := by
  simpa only [frobeniusNormSq, gradientTable, componentGradient, Pi.sub_apply] using
    (SOptLib.dependent_product_norm_sq_map_sub_le_of_pointwise_lipschitz
      (f := fun i => ∇ (setup.componentObjective i)) setup.L X Y setup.L_pos.le
      (fun i => setup.componentGradient_lipschitz_bound i (X i) (Y i)))

/-- Lemma 4.2 row-product contraction constant `M_R = 2 sqrt(n)/delta`. -/
noncomputable def rowContractionConstant : ℝ :=
  2 * Real.sqrt (nodeCount (Node := Node) : ℝ) / setup.contractionDelta

/-- Section 6 constant `s_* = max_r ||S_r||_2`. -/
noncomputable def perronResidualNormMax : ℝ :=
  setup.periodMax fun r =>
    matrixEuclideanOperatorNorm (Node := Node)
      (setup.perronResidualMatrix r.1)

/-- Section 6 constant `c_C = max_r ||C_r-I||_2`. -/
noncomputable def pullDeviationNormMax : ℝ :=
  setup.periodMax fun r =>
    matrixEuclideanOperatorNorm (Node := Node)
      (matrixSub (Node := Node) (setup.C r.1) (identityMatrix (Node := Node)))

/-- Section 6 constant `v_* = max_r ||v_r||_2`. -/
noncomputable def perronRightNormMax : ℝ :=
  setup.periodMax fun r =>
    rowEuclideanNorm (Node := Node) (setup.perronRight r.1)

/-- Section 6 constant `tilde v_* = max_r ||Π v_r||_2`. -/
noncomputable def projectedPerronRightNormMax : ℝ :=
  setup.periodMax fun r =>
    rowEuclideanNorm (Node := Node)
      (matrixMulVector (Node := Node) (consensusProjectorMatrix (Node := Node))
        (setup.perronRight r.1))

/-- Section 6 constant `kappa_R = max_r ||R_r-I||_2`. -/
noncomputable def pushDeviationNormMax : ℝ :=
  setup.periodMax fun r =>
    matrixEuclideanOperatorNorm (Node := Node)
      (matrixSub (Node := Node) (setup.R r.1) (identityMatrix (Node := Node)))

/-- Operator norm of the corrected lift on the zero-sum state subspace. -/
noncomputable def correctedLiftOperatorNorm (t : ℕ) : ℝ :=
  sInf { c : ℝ | 0 ≤ c ∧
    ∀ W : ZeroSumState Node E,
      ‖setup.correctedLift t W‖ ≤
        c * stateFrobeniusNorm (Node := Node) (E := E) W.1 }

/-- Section 6 constant `d_* = ||D_0||_2`. -/
noncomputable def correctedLiftNormZero : ℝ :=
  setup.correctedLiftOperatorNorm 0

/-- Section 6 constant `kappa_chi = ||pi_0 - 1/n||_2`. -/
noncomputable def hybridWeightDeviationNorm : ℝ :=
  rowEuclideanNorm (Node := Node)
    (setup.perronLeft 0 - RCLike.cWeight)

/-- Section 6 convolution constant `A_C = 2M_C^2/(1-r_*^2)`. -/
noncomputable def thetaInitialConstant : ℝ :=
  2 * setup.columnContractionConstant ^ 2 /
    (1 - setup.contractionRate ^ 2)

/-- Section 6 convolution constant
`B_C = 2M_C^2 s_*^2/(1-r_*)^2`. -/
noncomputable def thetaDisplacementConstant : ℝ :=
  2 * setup.columnContractionConstant ^ 2 *
    setup.perronResidualNormMax ^ 2 /
      (1 - setup.contractionRate) ^ 2

/-- Section 6 row-consensus convolution constant `G_R = M_R^2/(1-r_*)^2`. -/
noncomputable def sectionSixGradientResponseFormula : ℝ :=
  setup.rowContractionConstant ^ 2 / (1 - setup.contractionRate) ^ 2

/-- Section 6 noise-tracker constant `J_C = 1 + M_C^2 c_C^2/(1-r_*^2)`. -/
noncomputable def jointNoiseResidualConstant : ℝ :=
  1 + setup.columnContractionConstant ^ 2 * setup.pullDeviationNormMax ^ 2 /
    (1 - setup.contractionRate ^ 2)

/-- Centered influence `d_r = b_r - (h/n)1`. -/
noncomputable def centeredInfluence (r : ℕ) : RowVector Node :=
  setup.influence r -
    ((Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) / (nodeCount (Node := Node) : ℝ)) •
      oneRow (Node := Node)

/-- Abel partial sum `P_r = sum_{j=0}^r d_j`. -/
noncomputable def influencePartialSum (r : ℕ) : RowVector Node :=
  Finset.sum (Finset.range (r + 1)) fun j => setup.centeredInfluence j

/-- Section 6 Abel constant `P_d` from the phase-error estimate. -/
noncomputable def influenceAbelConstant : ℝ :=
  Finset.sum (Finset.range (setup.period - 1)) fun r =>
    rowNormSq (Node := Node) (setup.influencePartialSum r)

/-- Section 6 coefficient `C_{rho,0}` from (6.9). -/
noncomputable def rhoInitialConstant : ℝ :=
  12 * setup.correctedLiftNormZero ^ 2 *
      setup.columnContractionConstant ^ 2 /
    (1 - setup.contractionRate ^ 2)

/-- Section 6 coefficient `C_{rho,x}` from (6.9). -/
noncomputable def rhoDisplacementConstant : ℝ :=
  12 * setup.correctedLiftNormZero ^ 2 *
      setup.columnContractionConstant ^ 2 *
      setup.perronResidualNormMax ^ 2 /
      (1 - setup.contractionRate) ^ 2 +
    3 * (setup.period : ℝ) * setup.correctedLiftNormZero ^ 2 *
      matrixEuclideanOperatorNorm (Node := Node)
        (setup.perronResidualMatrix 0) ^ 2

/-- Phase-error consensus coefficient `E_Q = 3h^2p/n`. -/
noncomputable def phaseConsensusCoefficient : ℝ :=
  3 * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) ^ 2 * (setup.period : ℝ) /
    (nodeCount (Node := Node) : ℝ)

/-- Phase-error displacement coefficient `E_D = 3h^2p^3/n + 3P_d`. -/
noncomputable def phaseDisplacementCoefficient : ℝ :=
  3 * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) ^ 2 * (setup.period : ℝ) ^ 3 /
      (nodeCount (Node := Node) : ℝ) +
    3 * setup.influenceAbelConstant

/-- Section 6 combined feedback coefficient `A_B = H^2 kappa_chi^2 + E_Q`. -/
noncomputable def stateFeedbackConsensusCoefficient : ℝ :=
  setup.blockGain ^ 2 * setup.hybridWeightDeviationNorm ^ 2 +
    setup.phaseConsensusCoefficient

/-- Section 6 combined feedback coefficient `D_B = E_D + C_{rho,x}`. -/
noncomputable def stateFeedbackDisplacementCoefficient : ℝ :=
  setup.phaseDisplacementCoefficient + setup.rhoDisplacementConstant

/-- Projected tracker coefficient `a_0 = 3A_C`. -/
noncomputable def projectedTrackerInitialCoefficient : ℝ :=
  3 * setup.thetaInitialConstant

/-- Projected tracker coefficient `a_g = 12 tilde(v)_*^2 n^2 p`. -/
noncomputable def projectedTrackerGradientCoefficient : ℝ :=
  12 * setup.projectedPerronRightNormMax ^ 2 *
    (nodeCount (Node := Node) : ℝ) ^ 2 * (setup.period : ℝ)

/-- Projected tracker coefficient `a_D = 3B_C + 12 tilde(v)_*^2 n p^2`. -/
noncomputable def projectedTrackerDisplacementCoefficient : ℝ :=
  3 * setup.thetaDisplacementConstant +
    12 * setup.projectedPerronRightNormMax ^ 2 *
      (nodeCount (Node := Node) : ℝ) * (setup.period : ℝ) ^ 2

/-- Projected tracker coefficient `a_Q = 6 tilde(v)_*^2 n`. -/
noncomputable def projectedTrackerConsensusCoefficient : ℝ :=
  6 * setup.projectedPerronRightNormMax ^ 2 *
    (nodeCount (Node := Node) : ℝ)

/-- Projected tracker coefficient `a_sigma = 3J_C`. -/
noncomputable def projectedTrackerNoiseCoefficient : ℝ :=
  3 * setup.jointNoiseResidualConstant

/-- Unprojected tracker coefficient `d_0 = 6A_C`. -/
noncomputable def unprojectedTrackerInitialCoefficient : ℝ :=
  6 * setup.thetaInitialConstant

/-- Unprojected tracker coefficient `d_g = 24v_*^2n^2p`. -/
noncomputable def unprojectedTrackerGradientCoefficient : ℝ :=
  24 * setup.perronRightNormMax ^ 2 *
    (nodeCount (Node := Node) : ℝ) ^ 2 * (setup.period : ℝ)

/-- Unprojected tracker coefficient `d_D = 6B_C + 24v_*^2np^2`. -/
noncomputable def unprojectedTrackerDisplacementCoefficient : ℝ :=
  6 * setup.thetaDisplacementConstant +
    24 * setup.perronRightNormMax ^ 2 *
      (nodeCount (Node := Node) : ℝ) * (setup.period : ℝ) ^ 2

/-- Unprojected tracker coefficient `d_QL = 12v_*^2n`. -/
noncomputable def unprojectedTrackerConsensusCoefficient : ℝ :=
  12 * setup.perronRightNormMax ^ 2 *
    (nodeCount (Node := Node) : ℝ)

/-- Unprojected tracker coefficient `d_sigma = 6J_C`. -/
noncomputable def unprojectedTrackerNoiseCoefficient : ℝ :=
  6 * setup.jointNoiseResidualConstant

theorem stateFrobeniusNorm_le_stateL1Norm (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E) X ≤
      stateL1Norm (Node := Node) (E := E) X := by
  simpa only [stateFrobeniusNorm, frobeniusNormSq, stateL1Norm,
    FiniteNetwork.stateL1Norm_def, PiLp.norm_eq_of_L2] using
      (dependentProductL2Seminorm_le_sum_norm
        (ι := Node) (E := fun _ => E) X)

theorem stateL1Norm_le_sqrt_card_mul_stateFrobeniusNorm
    (X : State Node E) :
    stateL1Norm (Node := Node) (E := E) X ≤
      Real.sqrt (nodeCount (Node := Node) : ℝ) *
        stateFrobeniusNorm (Node := Node) (E := E) X := by
  simpa only [stateL1Norm, FiniteNetwork.stateL1Norm_def,
    stateFrobeniusNorm, frobeniusNormSq, nodeCount, PiLp.norm_eq_of_L2] using
      (sum_norm_le_sqrt_card_mul_dependentProductL2Seminorm
        (ι := Node) (E := fun _ => E) X)

/- The infimum in the paper's matrix two-norm is attained.  Keeping this
specification adjacent to the norm definition makes the later tensor action
bound depend only on a genuine scalar operator estimate. -/
theorem matrixEuclideanOperatorNorm_spec (A : NodeMatrix Node) :
    0 ≤ matrixEuclideanOperatorNorm (Node := Node) A ∧
      ∀ x : RowVector Node,
        rowEuclideanNorm (Node := Node)
            (matrixMulVector (Node := Node) A x) ≤
          matrixEuclideanOperatorNorm (Node := Node) A *
            rowEuclideanNorm (Node := Node) x := by
  classical
  let aSum : ℝ := ∑ i : Node, ∑ j : Node, |A i j|
  let c : ℝ := aSum * Real.sqrt (nodeCount (Node := Node) : ℝ)
  have haSum_nonneg : 0 ≤ aSum := by
    dsimp [aSum]
    positivity
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscalar (x : RowVector Node) :
      rowEuclideanNorm (Node := Node)
          (matrixMulVector (Node := Node) A x) ≤
        c * rowEuclideanNorm (Node := Node) x := by
    have hentry (j : Node) : |x j| ≤ stateL1Norm (Node := Node) (E := ℝ) x := by
      exact Finset.single_le_sum (fun i _ => abs_nonneg (x i))
        (Finset.mem_univ j)
    have hl1 :
        stateL1Norm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ) A x) ≤
          aSum * stateL1Norm (Node := Node) (E := ℝ) x := by
      calc
        stateL1Norm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ) A x) =
            ∑ i : Node, |∑ j : Node, A i j * x j| := by
              simp [stateL1Norm, leftMul, Real.norm_eq_abs]
        _ ≤ ∑ i : Node, ∑ j : Node, |A i j * x j| := by
              apply Finset.sum_le_sum
              intro i _
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Node, ∑ j : Node,
              |A i j| * stateL1Norm (Node := Node) (E := ℝ) x := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hentry j) (abs_nonneg _)
        _ = aSum * stateL1Norm (Node := Node) (E := ℝ) x := by
              dsimp [aSum]
              simp_rw [Finset.sum_mul]
    calc
      rowEuclideanNorm (Node := Node)
          (matrixMulVector (Node := Node) A x) =
          stateFrobeniusNorm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ) A x) := by
              simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
                frobeniusNormSq, matrixMulVector, leftMul, Real.norm_eq_abs,
                sq_abs]
      _ ≤ stateL1Norm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ) A x) :=
          stateFrobeniusNorm_le_stateL1Norm _
      _ ≤ aSum * stateL1Norm (Node := Node) (E := ℝ) x := hl1
      _ ≤ aSum * (Real.sqrt (nodeCount (Node := Node) : ℝ) *
            stateFrobeniusNorm (Node := Node) (E := ℝ) x) :=
          mul_le_mul_of_nonneg_left
            (stateL1Norm_le_sqrt_card_mul_stateFrobeniusNorm
              (Node := Node) (E := ℝ) x) haSum_nonneg
      _ = c * rowEuclideanNorm (Node := Node) x := by
          dsimp [c]
          simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
            frobeniusNormSq, Real.norm_eq_abs, sq_abs]
          ring
  let admissible : Set ℝ := { d : ℝ | 0 ≤ d ∧
    ∀ x : RowVector Node,
      rowEuclideanNorm (Node := Node)
          (matrixMulVector (Node := Node) A x) ≤
        d * rowEuclideanNorm (Node := Node) x }
  have hc_mem : c ∈ admissible := ⟨hc_nonneg, hscalar⟩
  have hadmissible_nonempty : admissible.Nonempty := ⟨c, hc_mem⟩
  have hinf : sInf admissible ∈ admissible := by
    simpa [admissible] using
      (sInf_mem_nonnegative_linear_majorant_set_of_nonempty
        (f := fun x : RowVector Node =>
          rowEuclideanNorm (Node := Node)
            (matrixMulVector (Node := Node) A x))
        (g := fun x : RowVector Node => rowEuclideanNorm (Node := Node) x)
        (by simpa [admissible] using hadmissible_nonempty))
  simpa [matrixEuclideanOperatorNorm, admissible] using hinf

/- The infimum defining the corrected-lift norm is attained.  This is the
deterministic operator interface needed to apply `D₀` to the noise-tracker
error without replacing the paper's sharp constant by its geometric
majorant. -/
theorem correctedLiftOperatorNorm_spec (t : ℕ) :
    0 ≤ setup.correctedLiftOperatorNorm t ∧
      ∀ W : ZeroSumState Node E,
        ‖setup.correctedLift t W‖ ≤
          setup.correctedLiftOperatorNorm t *
            stateFrobeniusNorm (Node := Node) (E := E) W.1 := by
  classical
  let geometricSum : ℝ := ∑' j : ℕ, setup.contractionRate ^ j
  let c : ℝ := setup.contractionDelta⁻¹ *
    Real.sqrt (nodeCount (Node := Node) : ℝ) * geometricSum
  have hinv_nonneg : 0 ≤ setup.contractionDelta⁻¹ :=
    inv_nonneg.mpr setup.contractionDelta_pos.le
  have hgeom_nonneg : 0 ≤ geometricSum := by
    dsimp [geometricSum]
    exact tsum_nonneg fun j => pow_nonneg setup.contractionRate_nonneg j
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscalar (W : ZeroSumState Node E) :
      ‖setup.correctedLift t W‖ ≤
        c * stateFrobeniusNorm (Node := Node) (E := E) W.1 := by
    calc
      ‖setup.correctedLift t W‖ ≤
          (setup.contractionDelta⁻¹ *
              stateL1Norm (Node := Node) (E := E) W.1) * geometricSum := by
        simpa [geometricSum] using setup.correctedLift_norm_le_geometric t W
      _ ≤ (setup.contractionDelta⁻¹ *
              (Real.sqrt (nodeCount (Node := Node) : ℝ) *
                stateFrobeniusNorm (Node := Node) (E := E) W.1)) *
              geometricSum :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (stateL1Norm_le_sqrt_card_mul_stateFrobeniusNorm W.1)
            hinv_nonneg) hgeom_nonneg
      _ = c * stateFrobeniusNorm (Node := Node) (E := E) W.1 := by
        dsimp [c]
        ring
  let admissible : Set ℝ := { d : ℝ | 0 ≤ d ∧
    ∀ W : ZeroSumState Node E,
      ‖setup.correctedLift t W‖ ≤
        d * stateFrobeniusNorm (Node := Node) (E := E) W.1 }
  have hc_mem : c ∈ admissible := ⟨hc_nonneg, hscalar⟩
  have hadmissible_nonempty : admissible.Nonempty := ⟨c, hc_mem⟩
  have hadmissible_bddBelow : BddBelow admissible := by
    refine ⟨0, ?_⟩
    intro d hd
    exact hd.1
  have hadmissible_closed : IsClosed admissible := by
    rw [show admissible = ({d : ℝ | 0 ≤ d} ∩
        ⋂ W : ZeroSumState Node E,
          {d : ℝ | ‖setup.correctedLift t W‖ ≤
            d * stateFrobeniusNorm (Node := Node) (E := E) W.1}) by
      ext d
      simp [admissible]]
    apply IsClosed.inter isClosed_Ici
    apply isClosed_iInter
    intro W
    exact isClosed_le continuous_const (continuous_id.mul continuous_const)
  have hinf : sInf admissible ∈ admissible :=
    hadmissible_closed.csInf_mem hadmissible_nonempty hadmissible_bddBelow
  simpa [correctedLiftOperatorNorm, admissible] using hinf

/- Scalar Euclidean operator control tensorizes to the paper's
`Node → E` Frobenius norm by expansion in a finite orthonormal basis of `E`. -/
theorem matrixEuclideanOperatorNorm_stateFrobenius_action
    (A : NodeMatrix Node) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) A X) ≤
      matrixEuclideanOperatorNorm (Node := Node) A *
        stateFrobeniusNorm (Node := Node) (E := E) X := by
  simpa [stateFrobeniusNorm, frobeniusNormSq, rowEuclideanNorm, rowNormSq,
    leftMul, matrixMulVector, SOptLib.dependentProductNormSq] using
    (Matrix.dependentProductL2Seminorm_mulVec_smul_le_of_scalar A
      (matrixEuclideanOperatorNorm (Node := Node) A) X
      (matrixEuclideanOperatorNorm_spec (Node := Node) A).1
      (by
        intro x
        simpa [rowEuclideanNorm, rowNormSq, matrixMulVector,
          SOptLib.dependentProductNormSq, Real.norm_eq_abs, sq_abs] using
          (matrixEuclideanOperatorNorm_spec (Node := Node) A).2 x))

/- Every phase value is below the finite-period supremum. -/
theorem le_periodMax (value : Fin setup.period → ℝ)
    (r : Fin setup.period) : value r ≤ setup.periodMax value := by
  unfold periodMax
  exact le_csSup (Set.finite_range value).bddAbove ⟨r, rfl⟩

theorem pushDeviationNormMax_nonneg :
    0 ≤ setup.pushDeviationNormMax := by
  let r : Fin setup.period := ⟨0, setup.period_pos⟩
  have hnorm : 0 ≤ matrixEuclideanOperatorNorm (Node := Node)
      (matrixSub (Node := Node) (setup.R r.1)
        (identityMatrix (Node := Node))) :=
    (matrixEuclideanOperatorNorm_spec (Node := Node) _).1
  exact hnorm.trans (by
    simpa [pushDeviationNormMax] using
      (setup.le_periodMax
        (fun q : Fin setup.period =>
          matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (setup.R q.1)
              (identityMatrix (Node := Node)))) r))

/- Uniform `R_t-I` action estimate with exactly the paper constant
`kappa_R`; periodic reduction is what connects the arbitrary time `t` to the
finite maximum. -/
theorem pushDeviation_stateFrobenius_action (t : ℕ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.R t)
            (identityMatrix (Node := Node))) X) ≤
      setup.pushDeviationNormMax *
        stateFrobeniusNorm (Node := Node) (E := E) X := by
  have hperiodicAction :=
    periodic_continuousLinearMap_apply_le_of_phase_bound
      setup.period
      (fun s => ContinuousLinearMap.lsmul ℝ ℝ
        (matrixEuclideanOperatorNorm (Node := Node)
          (matrixSub (Node := Node) (setup.R s)
            (identityMatrix (Node := Node)))))
      setup.pushDeviationNormMax setup.period_pos
      (by
        intro s
        exact congrArg
          (fun A => ContinuousLinearMap.lsmul ℝ ℝ
            (matrixEuclideanOperatorNorm (Node := Node)
              (matrixSub (Node := Node) A (identityMatrix (Node := Node)))))
          (setup.R_periodic s))
      (fun r =>
        (ContinuousLinearMap.opNorm_lsmul_apply_le _).trans (by
          rw [Real.norm_eq_abs, abs_of_nonneg
            (matrixEuclideanOperatorNorm_spec (Node := Node) _).1]
          simpa [pushDeviationNormMax] using
            (setup.le_periodMax
              (fun q : Fin setup.period =>
                matrixEuclideanOperatorNorm (Node := Node)
                  (matrixSub (Node := Node) (setup.R q.1)
                    (identityMatrix (Node := Node)))) r)))
      t (stateFrobeniusNorm (Node := Node) (E := E) X)
  have hstate_nonneg :
      0 ≤ stateFrobeniusNorm (Node := Node) (E := E) X :=
    Real.sqrt_nonneg _
  have hmajorant :
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixSub (Node := Node) (setup.R t)
            (identityMatrix (Node := Node))) *
          stateFrobeniusNorm (Node := Node) (E := E) X ≤
        setup.pushDeviationNormMax *
          stateFrobeniusNorm (Node := Node) (E := E) X := by
    simpa [ContinuousLinearMap.lsmul_apply, Real.norm_eq_abs,
      abs_of_nonneg (matrixEuclideanOperatorNorm_spec (Node := Node) _).1,
      abs_of_nonneg hstate_nonneg] using hperiodicAction
  calc
    stateFrobeniusNorm (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.R t)
            (identityMatrix (Node := Node))) X) ≤
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (setup.R t)
              (identityMatrix (Node := Node))) *
          stateFrobeniusNorm (Node := Node) (E := E) X :=
      matrixEuclideanOperatorNorm_stateFrobenius_action _ _
    _ ≤ setup.pushDeviationNormMax *
          stateFrobeniusNorm (Node := Node) (E := E) X := hmajorant

theorem pullDeviation_stateFrobenius_action (t : ℕ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.C t)
            (identityMatrix (Node := Node))) X) ≤
      setup.pullDeviationNormMax *
        stateFrobeniusNorm (Node := Node) (E := E) X := by
  let r : Fin setup.period := ⟨t % setup.period, Nat.mod_lt t setup.period_pos⟩
  have hphase :
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixSub (Node := Node) (setup.C r.1)
            (identityMatrix (Node := Node))) ≤
        setup.pullDeviationNormMax := by
    simpa [pullDeviationNormMax] using
      (setup.le_periodMax
        (fun q : Fin setup.period =>
          matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (setup.C q.1)
              (identityMatrix (Node := Node)))) r)
  have hCmod : setup.C r.1 = setup.C t := by
    exact (show Function.Periodic setup.C setup.period from setup.C_periodic).map_mod_nat t
  calc
    _ ≤ matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (setup.C t)
              (identityMatrix (Node := Node))) *
          stateFrobeniusNorm (Node := Node) (E := E) X :=
      matrixEuclideanOperatorNorm_stateFrobenius_action _ _
    _ = matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (setup.C r.1)
              (identityMatrix (Node := Node))) *
          stateFrobeniusNorm (Node := Node) (E := E) X := by rw [hCmod]
    _ ≤ _ := mul_le_mul_of_nonneg_right hphase (Real.sqrt_nonneg _)

theorem perronResidual_stateFrobenius_action (t : ℕ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) (setup.perronResidualMatrix t) X) ≤
      setup.perronResidualNormMax *
        stateFrobeniusNorm (Node := Node) (E := E) X := by
  let r : Fin setup.period := ⟨t % setup.period, Nat.mod_lt t setup.period_pos⟩
  have hphase :
      matrixEuclideanOperatorNorm (Node := Node)
          (setup.perronResidualMatrix r.1) ≤
        setup.perronResidualNormMax := by
    simpa [perronResidualNormMax] using
      (setup.le_periodMax
        (fun q : Fin setup.period =>
          matrixEuclideanOperatorNorm (Node := Node)
            (setup.perronResidualMatrix q.1)) r)
  have hvmod : setup.perronRight r.1 = setup.perronRight t := by
    exact (show Function.Periodic setup.perronRight setup.period from
      setup.perronRight_periodic).map_mod_nat t
  have hSmod : setup.perronResidualMatrix r.1 = setup.perronResidualMatrix t := by
    unfold perronResidualMatrix
    rw [hvmod]
  calc
    _ ≤ matrixEuclideanOperatorNorm (Node := Node)
            (setup.perronResidualMatrix t) *
          stateFrobeniusNorm (Node := Node) (E := E) X :=
      matrixEuclideanOperatorNorm_stateFrobenius_action _ _
    _ = matrixEuclideanOperatorNorm (Node := Node)
            (setup.perronResidualMatrix r.1) *
          stateFrobeniusNorm (Node := Node) (E := E) X := by rw [hSmod]
    _ ≤ _ := mul_le_mul_of_nonneg_right hphase (Real.sqrt_nonneg _)

theorem pullLiftProduct_frobenius_rate
    (hdelta_pos : 0 < setup.contractionDelta)
    (hdelta_lt : setup.contractionDelta < 1)
    (t j : ℕ) (W : ZeroSumState Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) (setup.pullLiftProduct t j) W.1) ≤
      setup.columnContractionConstant * setup.contractionRate ^ j *
        stateFrobeniusNorm (Node := Node) (E := E) W.1 := by
  simpa [stateFrobeniusNorm, frobeniusNormSq,
    SOptLib.dependentProductNormSq, columnContractionConstant, nodeCount,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (FiniteNetwork.dependentProductL2Seminorm_le_sqrt_card_mul_geometric_of_sum_norm_le
      (T := fun X => leftMul (Node := Node) (E := E)
        (setup.pullLiftProduct t j) X)
      (c := setup.contractionDelta⁻¹) (rate := setup.contractionRate) (j := j)
      (W := W.1)
      (mul_nonneg (inv_nonneg.mpr hdelta_pos.le)
        (pow_nonneg (Real.rpow_nonneg hdelta_pos.le _) _))
      (by
        simpa [stateL1Norm] using
          (setup.pullLiftProduct_stateL1Norm_rate hdelta_pos hdelta_lt t j W)))

/-- Section 6 `Lambda_Q = 2kappa_R^2 + d_QL`. -/
noncomputable def sectionSixLambdaQFormula : ℝ :=
  2 * setup.pushDeviationNormMax ^ 2 +
    setup.unprojectedTrackerConsensusCoefficient

/-- Lemma 4.2 / (4.3)-(4.4): periodic product contraction for pull products
on zero-sum states and push products after consensus projection. -/
theorem PeriodicProductContraction :
    0 < setup.contractionDelta ∧
      0 ≤ setup.contractionRate ∧ setup.contractionRate < 1 ∧
      (∀ (t j : ℕ) (W : ZeroSumState Node E),
        stateFrobeniusNorm (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E) (setup.pullLiftProduct t j) W.1) ≤
          setup.columnContractionConstant * setup.contractionRate ^ j *
            stateFrobeniusNorm (Node := Node) (E := E) W.1) ∧
      (∀ (t j : ℕ) (X : State Node E),
        stateFrobeniusNorm (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              (leftMul (Node := Node) (E := E) (setup.pushLiftProduct t j) X)) ≤
          setup.rowContractionConstant * setup.contractionRate ^ j *
            stateFrobeniusNorm (Node := Node) (E := E)
              (consensusError (Node := Node) (E := E) X)) := by
  have hpushBlock : ∀ (t : ℕ) (i j : Node),
      setup.minPositiveWeight ^ contractionWindow (Node := Node) ≤
        setup.pushLiftProduct t (contractionWindow (Node := Node)) i j := by
    intro t i j
    simpa [contractionWindow] using
      setup.pushLiftProduct_window_entry_lowerBound t i j
  have hdelta_pos : 0 < setup.contractionDelta := setup.contractionDelta_pos
  have hdelta_lt : setup.contractionDelta < 1 := setup.contractionDelta_lt_one
  have hwindow_pos : 0 < contractionWindow (Node := Node) := by
    simp [contractionWindow]
  have hrate_nonneg : 0 ≤ setup.contractionRate := setup.contractionRate_nonneg
  have hrate_lt : setup.contractionRate < 1 := setup.contractionRate_lt_one
  have hrate_window :
      setup.contractionRate ^ contractionWindow (Node := Node) =
        setup.contractionDelta := by
    rw [contractionRate]
    exact Real.rpow_inv_natCast_pow hdelta_pos.le (Nat.ne_of_gt hwindow_pos)
  refine ⟨hdelta_pos, hrate_nonneg, hrate_lt, ?_⟩
  refine ⟨?_, ?_⟩
  · intro t j W
    exact setup.pullLiftProduct_frobenius_rate hdelta_pos hdelta_lt t j W
  · intro t j X
    rw [setup.pushLiftProduct_eq_consecutiveProduct]
    simpa [rowContractionConstant] using
      (rowConsecutiveProduct_consensusError_frobenius_rate_of_blockMinorization
        (Node := Node) (E := E) setup.R
        (setup.minPositiveWeight ^ contractionWindow (Node := Node))
        setup.contractionDelta setup.contractionRate
        (contractionWindow (Node := Node)) hwindow_pos hdelta_pos hdelta_lt
        hrate_nonneg hrate_window
        (le_max_right (1 / 2)
          (1 - (nodeCount (Node := Node) : ℝ) *
            setup.minPositiveWeight ^ contractionWindow (Node := Node)))
        setup.R_rowStochastic
        (by
          intro s i k
          rw [← setup.pushLiftProduct_eq_consecutiveProduct]
          exact hpushBlock s i k)
        t j X)

/- Retained internal legacy specialization of the generic row-product estimate.
Source-facing and Section 6 consumers use `PeriodicProductContraction`. -/
theorem pushLiftProduct_consensusError_frobenius_rate_direct
    (t j : ℕ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.pushLiftProduct t j) X)) ≤
      setup.rowContractionConstant * setup.contractionRate ^ j *
        stateFrobeniusNorm (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E) X) := by
  have hdelta_pos : 0 < setup.contractionDelta := setup.contractionDelta_pos
  have hdelta_lt : setup.contractionDelta < 1 := setup.contractionDelta_lt_one
  have hwindow_pos : 0 < contractionWindow (Node := Node) := by
    simp [contractionWindow]
  have hrate_nonneg : 0 ≤ setup.contractionRate := setup.contractionRate_nonneg
  have hrate_window :
      setup.contractionRate ^ contractionWindow (Node := Node) =
        setup.contractionDelta := by
    rw [contractionRate]
    exact Real.rpow_inv_natCast_pow hdelta_pos.le (Nat.ne_of_gt hwindow_pos)
  rw [setup.pushLiftProduct_eq_consecutiveProduct]
  simpa [rowContractionConstant] using
    (rowConsecutiveProduct_consensusError_frobenius_rate_of_blockMinorization
      (Node := Node) (E := E) setup.R
      (setup.minPositiveWeight ^ contractionWindow (Node := Node))
      setup.contractionDelta setup.contractionRate
      (contractionWindow (Node := Node)) hwindow_pos hdelta_pos hdelta_lt
      hrate_nonneg hrate_window
      (le_max_right (1 / 2)
        (1 - (nodeCount (Node := Node) : ℝ) *
          setup.minPositiveWeight ^ contractionWindow (Node := Node)))
      setup.R_rowStochastic
      (by
        intro s i k
        rw [← setup.pushLiftProduct_eq_consecutiveProduct]
        exact setup.pushLiftProduct_window_entry_lowerBound s i k)
      t j X)

theorem consensusError_sub_state (X Y : State Node E) :
    consensusError (Node := Node) (E := E) (X - Y) =
      consensusError (Node := Node) (E := E) X -
        consensusError (Node := Node) (E := E) Y := by
  funext i
  simp only [consensusError, arithmeticAverage, Pi.sub_apply,
    Finset.sum_sub_distrib, smul_sub]
  abel

theorem consensusError_add_state (X Y : State Node E) :
    consensusError (Node := Node) (E := E) (X + Y) =
      consensusError (Node := Node) (E := E) X +
        consensusError (Node := Node) (E := E) Y := by
  funext i
  simp only [consensusError, arithmeticAverage, Pi.add_apply,
    Finset.sum_add_distrib, smul_add]
  abel

theorem consensusError_eq_self_of_sum_eq_zero
    (X : State Node E) (hX : ∑ i : Node, X i = 0) :
    consensusError (Node := Node) (E := E) X = X := by
  exact FiniteNetwork.consensusError_eq_self_of_sum_eq_zero X hX

/- Projected form of source equation (6.3).  The mean joint coordinate is
already zero-sum, while the Perron-gradient and noise-joint terms retain the
explicit consensus projector used in (6.19). -/
theorem projectedTrackerState_eq_joint_decomposition_source
    (noise : NoisePath Node E) (t : ℕ) :
    consensusError (Node := Node) (E := E) (setup.trackerState noise t) =
      setup.meanJointCoordinate noise t +
      consensusError (Node := Node) (E := E)
        (fun i => setup.perronRight t i •
          ∑ j : Node, setup.gradientTable (setup.primalState noise t) j) +
      consensusError (Node := Node) (E := E)
        (setup.noiseJointCoordinate noise t) := by
  rw [setup.trackerState_eq_joint_decomposition_source noise t,
    consensusError_add_state, consensusError_add_state,
    consensusError_eq_self_of_sum_eq_zero _
      (setup.meanJointCoordinate_zeroSum noise t)]

/- The arithmetic consensus projector is the orthogonal projection onto the
zero-sum state subspace, hence it cannot increase Frobenius energy. -/
theorem frobeniusNormSq_consensusError_le (X : State Node E) :
    frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E) X) ≤
      frobeniusNormSq (Node := Node) (E := E) X := by
  simpa [frobeniusNormSq, consensusError, arithmeticAverage, nodeCount,
    SOptLib.finiteUniformAverage] using
    (SOptLib.sum_norm_sq_sub_finiteUniformAverage_le_sum_norm_sq X)

/- Frobenius energy of a scalar rank-one state. -/
theorem frobeniusNormSq_rankOne (v : RowVector Node) (x : E) :
    frobeniusNormSq (Node := Node) (E := E) (fun i => v i • x) =
      rowEuclideanNorm (Node := Node) v ^ 2 * ‖x‖ ^ 2 := by
  simpa [frobeniusNormSq, rowEuclideanNorm, rowNormSq,
    Real.sq_sqrt (show 0 ≤ ∑ i, (v i) ^ 2 by positivity)] using
    (SOptLib.dependentProductNormSq_smul_const v x)

/- The consensus projection of a Perron rank-one state is the rank-one state
whose scalar coefficient is `Π v`. -/
theorem consensusError_rankOne (v : RowVector Node) (x : E) :
    consensusError (Node := Node) (E := E) (fun i => v i • x) =
      fun i => matrixMulVector (Node := Node)
        (consensusProjectorMatrix (Node := Node)) v i • x := by
  classical
  simpa [consensusError, arithmeticAverage, matrixMulVector,
    consensusProjectorMatrix, matrixSub, identityMatrix,
    FiniteNetwork.consensusError, FiniteNetwork.consensusState,
    FiniteNetwork.meanState, SOptLib.finiteUniformAverage, nodeCount,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Pi.sub_def,
    Fintype.sum_ite_eq] using
    (FiniteNetwork.consensusError_smul_const (Node := Node) (E := E) v x)

/- The standard three-term Hilbert-space square inequality, summed over rows. -/
theorem frobeniusNormSq_add_add_le_three
    (X Y Z : State Node E) :
    frobeniusNormSq (Node := Node) (E := E) (X + Y + Z) ≤
      3 * frobeniusNormSq (Node := Node) (E := E) X +
        3 * frobeniusNormSq (Node := Node) (E := E) Y +
          3 * frobeniusNormSq (Node := Node) (E := E) Z := by
  simpa only [frobeniusNormSq, SOptLib.dependentProductNormSq_def] using
    (SOptLib.dependentProductNormSq_add_add_le_three X Y Z)

theorem perronRightNorm_le_max (t : ℕ) :
    rowEuclideanNorm (Node := Node) (setup.perronRight t) ≤
      setup.perronRightNormMax := by
  let r : Fin setup.period := ⟨t % setup.period, Nat.mod_lt t setup.period_pos⟩
  have hvmod : setup.perronRight r.1 = setup.perronRight t :=
    (show Function.Periodic setup.perronRight setup.period from
      setup.perronRight_periodic).map_mod_nat t
  rw [← hvmod]
  simpa [perronRightNormMax] using
    (setup.le_periodMax
      (fun q : Fin setup.period =>
        rowEuclideanNorm (Node := Node) (setup.perronRight q.1)) r)

theorem projectedPerronRightNorm_le_max (t : ℕ) :
    rowEuclideanNorm (Node := Node)
        (matrixMulVector (Node := Node) (consensusProjectorMatrix (Node := Node))
          (setup.perronRight t)) ≤
      setup.projectedPerronRightNormMax := by
  let r : Fin setup.period := ⟨t % setup.period, Nat.mod_lt t setup.period_pos⟩
  have hvmod : setup.perronRight r.1 = setup.perronRight t :=
    (show Function.Periodic setup.perronRight setup.period from
      setup.perronRight_periodic).map_mod_nat t
  rw [← hvmod]
  simpa [projectedPerronRightNormMax] using
    (setup.le_periodMax
      (fun q : Fin setup.period => rowEuclideanNorm (Node := Node)
        (matrixMulVector (Node := Node)
          (consensusProjectorMatrix (Node := Node)) (setup.perronRight q.1))) r)

/- Source equations (6.3) and (6.17), before summing over time and taking
expectations.  This is the exact projected/unprojected tracker assembly step:
the only remaining source inputs are the aggregate-gradient, Theta, and J
energy estimates. -/
theorem trackerState_joint_pointwise_bounds (noise : NoisePath Node E) (t : ℕ) :
    let gsum := ∑ j : Node, setup.gradientTable (setup.primalState noise t) j
    frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState noise t)) ≤
      3 * frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate noise t) +
        3 * setup.projectedPerronRightNormMax ^ 2 * ‖gsum‖ ^ 2 +
          3 * frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseJointCoordinate noise t) ∧
    frobeniusNormSq (Node := Node) (E := E) (setup.trackerState noise t) ≤
      3 * frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate noise t) +
        3 * setup.perronRightNormMax ^ 2 * ‖gsum‖ ^ 2 +
          3 * frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseJointCoordinate noise t) := by
  classical
  dsimp only
  let gsum := ∑ j : Node, setup.gradientTable (setup.primalState noise t) j
  let projectedV := matrixMulVector (Node := Node)
    (consensusProjectorMatrix (Node := Node)) (setup.perronRight t)
  have hconsensus (X : State Node E) :
      FiniteNetwork.consensusError X =
        consensusError (Node := Node) (E := E) X := by
    rfl
  have hprojected :
      FiniteNetwork.consensusError (setup.trackerState noise t) =
        setup.meanJointCoordinate noise t + (fun i => projectedV i • gsum) +
          FiniteNetwork.consensusError (setup.noiseJointCoordinate noise t) := by
    rw [hconsensus, hconsensus,
      setup.projectedTrackerState_eq_joint_decomposition_source noise t,
      consensusError_rankOne]
  have hv : Real.sqrt (∑ i : Node, (setup.perronRight t i) ^ 2) ≤
      setup.perronRightNormMax := by
    simpa [rowEuclideanNorm, rowNormSq] using setup.perronRightNorm_le_max t
  have hprojectedV : Real.sqrt (∑ i : Node, (projectedV i) ^ 2) ≤
      setup.projectedPerronRightNormMax := by
    simpa [projectedV, rowEuclideanNorm, rowNormSq] using
      setup.projectedPerronRightNorm_le_max t
  simpa [frobeniusNormSq, hconsensus] using
    (FiniteNetwork.consensusError_and_state_rankOne_decomposition_energy_bounds
      (Y := setup.trackerState noise t)
      (Theta := setup.meanJointCoordinate noise t)
      (J := setup.noiseJointCoordinate noise t) (v := setup.perronRight t)
      (projectedV := projectedV) (g := gsum)
      (vMax := setup.perronRightNormMax)
      (projectedVMax := setup.projectedPerronRightNormMax) hprojected
      (setup.trackerState_eq_joint_decomposition_source noise t) hv hprojectedV)

/- Finite-horizon pathwise form of (6.17), obtained by summing the exact
pointwise joint-coordinate assembly above.  Expectations can therefore be
introduced termwise without reopening the tracker decomposition algebra. -/
theorem trackerState_joint_pathwise_energy_bounds
    (noise : NoisePath Node E) (N : ℕ) :
    let Theta := Finset.sum (Finset.range N) (fun t =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.meanJointCoordinate noise t))
    let Grad := Finset.sum (Finset.range N) (fun t =>
      ‖∑ j : Node, setup.gradientTable (setup.primalState noise t) j‖ ^ 2)
    let J := Finset.sum (Finset.range N) (fun t =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate noise t))
    let P := Finset.sum (Finset.range N) (fun t =>
      frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState noise t)))
    let Y := Finset.sum (Finset.range N) (fun t =>
      frobeniusNormSq (Node := Node) (E := E) (setup.trackerState noise t))
    P ≤ 3 * Theta + 3 * setup.projectedPerronRightNormMax ^ 2 * Grad + 3 * J ∧
      2 * Y ≤ 6 * Theta + 6 * setup.perronRightNormMax ^ 2 * Grad + 6 * J := by
  classical
  dsimp only
  have hprojected := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range N) =>
    (setup.trackerState_joint_pointwise_bounds noise t).1
  have hunprojected := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range N) =>
    (setup.trackerState_joint_pointwise_bounds noise t).2
  constructor
  · calc
      _ ≤ Finset.sum (Finset.range N) (fun t =>
            3 * frobeniusNormSq (Node := Node) (E := E)
                (setup.meanJointCoordinate noise t) +
              3 * setup.projectedPerronRightNormMax ^ 2 *
                ‖∑ j : Node,
                  setup.gradientTable (setup.primalState noise t) j‖ ^ 2 +
              3 * frobeniusNormSq (Node := Node) (E := E)
                (setup.noiseJointCoordinate noise t)) := hprojected
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  · calc
      2 * Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (setup.trackerState noise t)) ≤
        2 * Finset.sum (Finset.range N) (fun t =>
          3 * frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate noise t) +
            3 * setup.perronRightNormMax ^ 2 *
              ‖∑ j : Node,
                setup.gradientTable (setup.primalState noise t) j‖ ^ 2 +
            3 * frobeniusNormSq (Node := Node) (E := E)
              (setup.noiseJointCoordinate noise t)) :=
        mul_le_mul_of_nonneg_left hunprojected (by norm_num)
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring

/- Exact source identity preceding (6.20): row stochasticity removes the
consensus component from `(R_t-I)X_t`. -/
theorem primalDisplacement_eq_pushConsensus_sub_tracker_source
    (noise : NoisePath Node E) (t : ℕ) :
    setup.primalState noise (t + 1) - setup.primalState noise t =
      leftMul (Node := Node) (E := E)
        (matrixSub (Node := Node) (setup.R t) (identityMatrix (Node := Node)))
        (setup.consensusState noise t) -
      setup.alpha • setup.trackerState noise t := by
  classical
  simpa only [leftMul, matrixSub, identityMatrix, consensusState,
    consensusError, arithmeticAverage, FiniteNetwork.consensusError,
    FiniteNetwork.consensusState, FiniteNetwork.meanState,
    SOptLib.finiteUniformAverage, nodeCount] using
    (FiniteNetwork.displacement_eq_sub_one_smulVec_consensusError_sub_direction_of_sum_row_eq_one
      (A := setup.R t) (X := setup.primalState noise t)
      (Xnext := setup.primalState noise (t + 1))
      (Y := setup.trackerState noise t) (alpha := setup.alpha)
      (setup.R_rowStochastic t).2
      (by simpa only [leftMul] using setup.primalState_succ noise t))

theorem consensusError_smul_state (a : ℝ) (X : State Node E) :
    consensusError (Node := Node) (E := E) (a • X) =
      a • consensusError (Node := Node) (E := E) X := by
  funext i
  simp only [consensusError, arithmeticAverage, Pi.smul_apply,
    smul_sub]
  rw [← Finset.smul_sum, smul_smul]
  rw [mul_comm ((nodeCount (Node := Node) : ℝ)⁻¹) a]
  rw [← smul_smul]

theorem consensusError_zero_state :
    consensusError (Node := Node) (E := E) (0 : State Node E) = 0 := by
  funext i
  simp [consensusError, arithmeticAverage]

theorem consensusError_finset_sum_state
    {ι : Type*} (s : Finset ι) (X : ι → State Node E) :
    consensusError (Node := Node) (E := E) (∑ j ∈ s, X j) =
      ∑ j ∈ s, consensusError (Node := Node) (E := E) (X j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [consensusError_zero_state]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [consensusError_add_state, ih]

theorem leftMul_smul_state_local
    (A : NodeMatrix Node) (a : ℝ) (X : State Node E) :
    leftMul (Node := Node) (E := E) A (a • X) =
      a • leftMul (Node := Node) (E := E) A X := by
  funext i
  simp only [leftMul_apply, Pi.smul_apply]
  calc
    (∑ j : Node, A i j • a • X j) =
        ∑ j : Node, a • (A i j • X j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul, smul_smul, mul_comm]
    _ = a • ∑ j : Node, A i j • X j := by rw [Finset.smul_sum]

theorem leftMul_finset_sum_state
    {ι : Type*} (A : NodeMatrix Node) (s : Finset ι)
    (X : ι → State Node E) :
    leftMul (Node := Node) (E := E) A (∑ j ∈ s, X j) =
      ∑ j ∈ s, leftMul (Node := Node) (E := E) A (X j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext i
      simp [leftMul]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [leftMul_add_state, ih]

theorem consensusError_add_constant (X : State Node E) (x : E) :
    consensusError (Node := Node) (E := E) (X + fun _ => x) =
      consensusError (Node := Node) (E := E) X := by
  simpa [consensusError, arithmeticAverage, FiniteNetwork.consensusError,
    FiniteNetwork.consensusState, FiniteNetwork.meanState,
    SOptLib.finiteUniformAverage, nodeCount] using
    (FiniteNetwork.consensusError_add_const X x)

theorem consensusError_leftMul_consensusError
    {A : NodeMatrix Node} (hA : RowStochastic (Node := Node) A)
    (X : State Node E) :
    consensusError (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) A X) =
      consensusError (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) A
          (consensusError (Node := Node) (E := E) X)) := by
  classical
  simpa [leftMul, consensusError, arithmeticAverage,
    FiniteNetwork.consensusError, FiniteNetwork.consensusState,
    FiniteNetwork.meanState, SOptLib.finiteUniformAverage, nodeCount] using
    (FiniteNetwork.consensusError_smulVec_consensusError_of_sum_row_eq_one
      A X hA.2)

/- The pathwise consensus recursion used at the start of (6.18). -/
theorem consensusState_succ_source
    (noise : NoisePath Node E) (t : ℕ) :
    setup.consensusState noise (t + 1) =
      consensusError (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.R t)
            (setup.consensusState noise t)) -
        setup.alpha • consensusError (Node := Node) (E := E)
          (setup.trackerState noise t) := by
  unfold consensusState
  rw [setup.primalState_succ noise t]
  rw [consensusError_sub_state, consensusError_smul_state]
  rw [consensusError_leftMul_consensusError (setup.R_rowStochastic t)]

theorem consensusState_zero_source (noise : NoisePath Node E) :
    setup.consensusState noise 0 = 0 := by
  rw [consensusState, setup.primalState_zero]
  have hconstant := consensusError_add_constant
    (Node := Node) (E := E) (0 : State Node E) setup.x0
  simpa [initialPrimal, consensusError_zero_state] using hconstant

theorem pushLiftProduct_extend_source (j t : ℕ) (hjt : j < t) :
    setup.pushLiftProduct (j + 1) (t - j) =
      matrixMul (Node := Node) (setup.R t)
        (setup.pushLiftProduct (j + 1) (t - 1 - j)) := by
  have hlen : t - j = (t - 1 - j) + 1 := by omega
  rw [hlen, pushLiftProduct]
  congr 2
  omega

/- Exact source expansion preceding (6.18). -/
theorem consensusState_unroll_source
    (noise : NoisePath Node E) (t : ℕ) :
    setup.consensusState noise t =
      (-setup.alpha) •
        ∑ j ∈ Finset.range t,
          consensusError (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E)
              (setup.pushLiftProduct (j + 1) (t - 1 - j))
            (setup.trackerState noise j)) := by
  classical
  have hconsensus (Z : State Node E) :
      consensusError (Node := Node) (E := E) Z =
        FiniteNetwork.consensusError Z := by
    rfl
  have hleft (B : NodeMatrix Node) (Z : State Node E) :
      leftMul (Node := Node) (E := E) B Z =
        fun i => ∑ j, B i j • Z j := by
    rfl
  have hproduct (s k : Nat) :
      setup.pushLiftProduct s k =
        FiniteNetwork.consecutiveProduct
          (show Nat -> Matrix Node Node Real from setup.R) s k := by
    rw [setup.pushLiftProduct_eq_consecutiveProduct]
    simpa only using consecutiveProduct_eq_finiteNetwork setup.R s k
  simpa only [hconsensus, hleft, hproduct, Matrix.smulVec,
    Matrix.Module.smul_def] using
    (FiniteNetwork.consensusError_affine_matrix_recurrence_unroll
      (show Nat -> Matrix Node Node Real from setup.R)
      (setup.consensusState noise) (setup.trackerState noise) setup.alpha
      (fun k i => setup.R_row_sum k i)
      (setup.consensusState_zero_source noise)
      (fun k => by
        simpa only [hconsensus, hleft, Matrix.smulVec,
          Matrix.Module.smul_def] using
          setup.consensusState_succ_source noise k)
      t)

theorem stateFrobeniusNorm_eq_piLp_norm (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E) X =
      ‖(WithLp.toLp 2 X : PiLp 2 (fun _ : Node => E))‖ := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem stateFrobeniusNorm_smul
    (a : ℝ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E) (a • X) =
      |a| * stateFrobeniusNorm (Node := Node) (E := E) X := by
  rw [stateFrobeniusNorm_eq_piLp_norm,
    stateFrobeniusNorm_eq_piLp_norm]
  change ‖a • (WithLp.toLp 2 X : PiLp 2 (fun _ : Node => E))‖ = _
  rw [norm_smul, Real.norm_eq_abs]

theorem stateFrobeniusNorm_add_le
    (X Y : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E) (X + Y) ≤
      stateFrobeniusNorm (Node := Node) (E := E) X +
        stateFrobeniusNorm (Node := Node) (E := E) Y := by
  rw [stateFrobeniusNorm_eq_piLp_norm,
    stateFrobeniusNorm_eq_piLp_norm,
    stateFrobeniusNorm_eq_piLp_norm]
  change ‖(WithLp.toLp 2 X : PiLp 2 (fun _ : Node => E)) +
      WithLp.toLp 2 Y‖ ≤ _
  exact norm_add_le _ _

theorem stateFrobeniusNorm_finset_sum_le
    {ι : Type*} (s : Finset ι) (X : ι → State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E) (∑ j ∈ s, X j) ≤
      ∑ j ∈ s, stateFrobeniusNorm (Node := Node) (E := E) (X j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stateFrobeniusNorm, frobeniusNormSq]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (stateFrobeniusNorm_add_le _ _).trans (add_le_add le_rfl ih)

/- Pathwise geometric convolution obtained from the exact expansion and the
active row-minorization product rate. -/
theorem consensusState_norm_convolution_source
    (noise : NoisePath Node E) (halpha : 0 ≤ setup.alpha) (t : ℕ) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (setup.consensusState noise t) ≤
      ∑ j ∈ Finset.range t,
        setup.rowContractionConstant *
          setup.contractionRate ^ (t - 1 - j) *
            (setup.alpha * stateFrobeniusNorm (Node := Node) (E := E)
              (consensusError (Node := Node) (E := E)
                (setup.trackerState noise j))) := by
  classical
  have hconsensus (Z : State Node E) :
      consensusError (Node := Node) (E := E) Z =
        FiniteNetwork.consensusError Z := by
    rfl
  simpa only [stateFrobeniusNorm_eq_piLp_norm, ← hconsensus] using
    (FiniteNetwork.consensusError_affine_matrix_recurrence_norm_le_geometric_convolution
      setup.pushLiftProduct (setup.consensusState noise) (setup.trackerState noise)
      setup.alpha setup.rowContractionConstant setup.contractionRate t halpha
      (by
        simpa only [← hconsensus, leftMul] using
          setup.consensusState_unroll_source noise t)
      (by
        intro s k Z
        simpa only [stateFrobeniusNorm_eq_piLp_norm, ← hconsensus,
          leftMul] using
          setup.PeriodicProductContraction.2.2.2.2 s k Z))

/-- Lemma 4.4 / (4.6)-(4.7): average gain and effective-node facts for the
periodic influence vectors. -/
theorem AverageGainEffectiveNodes :
    (∀ r : ℕ, Summable fun j : ℕ => setup.influenceSeriesTerm r j) ∧
      setup.averageInfluence = (fun _ : Node => setup.averagePerronOverlap) ∧
      (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) =
        (nodeCount (Node := Node) : ℝ) * setup.averagePerronOverlap ∧
      0 < (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (Node := Node) (setup.influence r.1))) ∧
      0 < setup.influenceSecondMoment ∧
      0 < setup.effectiveNodeCount ∧
      setup.effectiveNodeCount ≤ (nodeCount (Node := Node) : ℝ) ∧
      (setup.effectiveNodeCount = (nodeCount (Node := Node) : ℝ) ↔
        setup.influenceEntriesAllEqual) ∧
      (setup.period = 1 → setup.effectiveNodeCount = (nodeCount (Node := Node) : ℝ)) := by
  have havg := setup.averageInfluence_eq_averagePerronOverlap
  have hgain :=
    setup.influenceGain_eq_nodeCount_mul_averagePerronOverlap havg
  have hbounds := setup.effectiveNodeCount_pos_and_le_nodeCount
  have heq :=
    setup.effectiveNodeCount_eq_nodeCount_iff_influenceEntriesAllEqual
  refine ⟨setup.influenceSeries_summable, havg, hgain,
    setup.influenceGain_pos, setup.influenceSecondMoment_pos,
    hbounds.1, hbounds.2, heq, ?_⟩
  intro hp
  exact heq.mpr (setup.influenceEntriesAllEqual_of_period_eq_one hp)

/-- A zero-initialized stable scalar filter has finite-horizon squared gain
bounded by the square of the geometric kernel's `ℓ¹` mass. -/
theorem finite_stable_recurrence_sq_sum_le
    {b w : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hb0 : b 0 = 0)
    (hstep : ∀ t : ℕ, b (t + 1) = r * b t + w t)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t => (b t) ^ 2) ≤
      (1 / (1 - r) ^ 2) *
        Finset.sum (Finset.range N) (fun t => (w t) ^ 2) := by
  exact _root_.finite_stable_recurrence_sq_sum_le hr0.le hr1 hb0 hstep N

/- Sharp zero-initial case of the geometric convolution estimate.  The factor
two in `SquareSummableGeometricConvolution` is only needed to split a nonzero
homogeneous response from the forcing response; (6.18) has `Q₀ = 0`. -/
theorem squareSummableGeometricConvolution_zeroInitial
    {u z : ℕ → ℝ} {M r : ℝ}
    (hu_nonneg : ∀ t : ℕ, 0 ≤ u t)
    (hz_nonneg : ∀ t : ℕ, 0 ≤ z t)
    (hM : 0 ≤ M) (hr0 : 0 < r) (hr1 : r < 1)
    (hrec : ∀ t : ℕ,
      u t ≤ Finset.sum (Finset.range t) fun j =>
        M * r ^ (t - 1 - j) * z j)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t => (u t) ^ 2) ≤
      (M ^ 2 / (1 - r) ^ 2) *
        Finset.sum (Finset.range N) (fun j => (z j) ^ 2) := by
  exact _root_.finite_sq_sum_le_of_le_geometric_convolution
    N (fun t _ => hu_nonneg t) hr0.le hr1 (fun t _ => hrec t)

theorem stateFrobeniusNorm_sq (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E) X ^ 2 =
      frobeniusNormSq (Node := Node) (E := E) X := by
  unfold stateFrobeniusNorm
  apply Real.sq_sqrt
  unfold frobeniusNormSq
  positivity

/- Pathwise sharp form of equation (6.18), before expectation. -/
theorem consensusState_sq_sum_convolution_source
    (noise : NoisePath Node E) (halpha : 0 ≤ setup.alpha) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.consensusState noise t)) ≤
      setup.alpha ^ 2 * setup.sectionSixGradientResponseFormula *
        Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              (setup.trackerState noise t))) := by
  have hM : 0 ≤ setup.rowContractionConstant := by
    rw [rowContractionConstant]
    exact div_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      setup.contractionDelta_pos.le
  have hr0 : 0 < setup.contractionRate := by
    rw [contractionRate]
    exact Real.rpow_pos_of_pos setup.contractionDelta_pos _
  have hr1 : setup.contractionRate < 1 := setup.contractionRate_lt_one
  have hconv := squareSummableGeometricConvolution_zeroInitial
    (u := fun t => stateFrobeniusNorm (Node := Node) (E := E)
      (setup.consensusState noise t))
    (z := fun t => setup.alpha *
      stateFrobeniusNorm (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState noise t)))
    (M := setup.rowContractionConstant) (r := setup.contractionRate)
    (fun _ => Real.sqrt_nonneg _)
    (fun _ => mul_nonneg halpha (Real.sqrt_nonneg _))
    hM hr0 hr1
    (fun t => setup.consensusState_norm_convolution_source noise halpha t) N
  calc
    Finset.sum (Finset.range (N + 1)) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.consensusState noise t)) =
      Finset.sum (Finset.range (N + 1)) (fun t =>
        stateFrobeniusNorm (Node := Node) (E := E)
          (setup.consensusState noise t) ^ 2) := by
        apply Finset.sum_congr rfl
        intro t _
        exact (stateFrobeniusNorm_sq _).symm
    _ ≤ (setup.rowContractionConstant ^ 2 /
          (1 - setup.contractionRate) ^ 2) *
        Finset.sum (Finset.range N) (fun t =>
          (setup.alpha * stateFrobeniusNorm (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              (setup.trackerState noise t))) ^ 2) := hconv
    _ = setup.alpha ^ 2 * setup.sectionSixGradientResponseFormula *
        Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              (setup.trackerState noise t))) := by
      rw [sectionSixGradientResponseFormula]
      have hscale :
          Finset.sum (Finset.range N) (fun t =>
            (setup.alpha * stateFrobeniusNorm (Node := Node) (E := E)
              (consensusError (Node := Node) (E := E)
                (setup.trackerState noise t))) ^ 2) =
            setup.alpha ^ 2 * Finset.sum (Finset.range N) (fun t =>
              frobeniusNormSq (Node := Node) (E := E)
                (consensusError (Node := Node) (E := E)
                  (setup.trackerState noise t))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        calc
          (setup.alpha * stateFrobeniusNorm (Node := Node) (E := E)
              (consensusError (Node := Node) (E := E)
                (setup.trackerState noise t))) ^ 2 =
              setup.alpha ^ 2 *
                stateFrobeniusNorm (Node := Node) (E := E)
                  (consensusError (Node := Node) (E := E)
                    (setup.trackerState noise t)) ^ 2 := by ring
          _ = setup.alpha ^ 2 *
              frobeniusNormSq (Node := Node) (E := E)
                (consensusError (Node := Node) (E := E)
                  (setup.trackerState noise t)) := by
            rw [stateFrobeniusNorm_sq]
      rw [hscale]
      ring

/- A Lipschitz map preserves `L²` on a finite measure space, without a
zero-at-zero assumption: subtract its value at zero, use the standard
`LipschitzWith.comp_memLp` theorem, and add the constant back. -/
theorem memLp_two_comp_lipschitz
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : E → E) (K : NNReal) (hf : LipschitzWith K f)
    {X : Ω → E} (hX : MemLp X 2 μ) :
    MemLp (fun ω => f (X ω)) 2 μ := by
  exact memLp_two_comp_lipschitz_of_finiteMeasure f K hf hX

/- Coordinatewise `L²` closure of the generated push-pull recursion.  This is
the induction core behind finite-horizon Bochner integrability. -/
theorem generated_pushpull_coordinate_memLp
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ t : ℕ,
      (∀ i : Node,
        MemLp (fun ω => setup.primalState (oracle.noise ω) t i) 2 μ) ∧
      (∀ i : Node,
        MemLp (fun ω => setup.trackerState (oracle.noise ω) t i) 2 μ) := by
  classical
  let K : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith K (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [K, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hnoise_l2 (t : ℕ) (i : Node) :
      MemLp (fun ω => oracle.noise ω t i) 2 μ := by
    have hmeas : Measurable (fun ω => oracle.noise ω t i) :=
      (oracle.noiseStream_measurable t).eval
    exact (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2
      (setup.conditionalSecondMomentBound_integrable μ oracle horacle t i)
  have horacleTable_l2 (t : ℕ)
      (hprimal : ∀ i : Node,
        MemLp (fun ω => setup.primalState (oracle.noise ω) t i) 2 μ) :
      ∀ i : Node,
        MemLp (fun ω => setup.oracleTable (oracle.noise ω) t i) 2 μ := by
    intro i
    have hgrad :
        MemLp
          (fun ω => setup.componentGradient i
            (setup.primalState (oracle.noise ω) t i)) 2 μ :=
      memLp_two_comp_lipschitz (setup.componentGradient i) K
        (hgradient_lipschitz i) (hprimal i)
    have hsum := hgrad.add (hnoise_l2 t i)
    refine MemLp.ae_eq ?_ hsum
    exact Filter.Eventually.of_forall fun ω => by
      simp [oracleTable, sampledGradient, gradientTable]
  intro t
  induction t with
  | zero =>
      constructor
      · intro i
        simpa [primalState_zero, initialPrimal] using
          (memLp_const setup.x0 : MemLp (fun _ : Ω => setup.x0) 2 μ)
      · intro i
        have hsum :=
          (memLp_const (setup.componentGradient i setup.x0) :
            MemLp (fun _ : Ω => setup.componentGradient i setup.x0) 2 μ).add
            (hnoise_l2 0 i)
        refine MemLp.ae_eq ?_ hsum
        exact Filter.Eventually.of_forall fun ω => by
          simp [trackerState_zero, oracleTable, sampledGradient, gradientTable,
            primalState_zero, initialPrimal]
  | succ t ih =>
      have hprimal_next (i : Node) :
          MemLp
            (fun ω => setup.primalState (oracle.noise ω) (t + 1) i) 2 μ := by
        have hraw :
            MemLp
              (fun ω =>
                (∑ j : Node,
                  setup.R t i j • setup.primalState (oracle.noise ω) t j) -
                  setup.alpha • setup.trackerState (oracle.noise ω) t i) 2 μ := by
          simpa [sub_eq_add_neg] using
            (memLp_matrix_smulVec_add_of_coordinate_memLp
              (μ := μ) (A := setup.R t)
              (X := fun j ω => setup.primalState (oracle.noise ω) t j)
              (U := fun i ω => (-setup.alpha) •
                setup.trackerState (oracle.noise ω) t i)
              (p := 2) i ih.1 ((ih.2 i).const_smul (-setup.alpha)))
        refine MemLp.ae_eq ?_ hraw
        exact Filter.Eventually.of_forall fun ω => by
          change
            (∑ j : Node,
                setup.R t i j • setup.primalState (oracle.noise ω) t j) -
                setup.alpha • setup.trackerState (oracle.noise ω) t i =
              setup.primalState (oracle.noise ω) (t + 1) i
          rw [setup.primalState_succ]
          rfl
      have horacle_next := horacleTable_l2 (t + 1) hprimal_next
      have horacle_cur := horacleTable_l2 t ih.1
      constructor
      · exact hprimal_next
      · intro i
        have hraw :
            MemLp
              (fun ω =>
                (∑ j : Node,
                  setup.C t i j • setup.trackerState (oracle.noise ω) t j) +
                  setup.oracleTable (oracle.noise ω) (t + 1) i -
                  setup.oracleTable (oracle.noise ω) t i) 2 μ := by
          simpa [sub_eq_add_neg, add_assoc] using
            (memLp_matrix_smulVec_add_of_coordinate_memLp
              (μ := μ) (A := setup.C t)
              (X := fun j ω => setup.trackerState (oracle.noise ω) t j)
              (U := fun i ω =>
                setup.oracleTable (oracle.noise ω) (t + 1) i -
                  setup.oracleTable (oracle.noise ω) t i)
              (p := 2) i ih.2 ((horacle_next i).sub (horacle_cur i)))
        refine MemLp.ae_eq ?_ hraw
        exact Filter.Eventually.of_forall fun ω => by
          change
            (∑ j : Node,
                setup.C t i j • setup.trackerState (oracle.noise ω) t j) +
                setup.oracleTable (oracle.noise ω) (t + 1) i -
                setup.oracleTable (oracle.noise ω) t i =
              setup.trackerState (oracle.noise ω) (t + 1) i
          rw [setup.trackerState_succ]
          rfl

/- The deterministic and noise tracker-error recursions inherit coordinatewise
`L²` regularity from the generated primal process and the oracle noise. -/
theorem splitTrackerErrors_coordinate_memLp
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ t : ℕ,
      (∀ i : Node, MemLp (fun ω =>
        setup.meanTrackerError (oracle.noise ω) t i) 2 μ) ∧
      (∀ i : Node, MemLp (fun ω =>
        setup.noiseTrackerError (oracle.noise ω) t i) 2 μ) := by
  classical
  let KL : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith KL (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hgrad (t : ℕ) (i : Node) :
      MemLp (fun ω => setup.gradientTable
        (setup.primalState (oracle.noise ω) t) i) 2 μ := by
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (setup.componentGradient i) KL
        (hgradient_lipschitz i)
        ((setup.generated_pushpull_coordinate_memLp μ oracle horacle t).1 i)
  have hnoise (t : ℕ) (i : Node) :
      MemLp (fun ω => oracle.noise ω t i) 2 μ := by
    have hmeas : Measurable (fun ω => oracle.noise ω t i) :=
      (oracle.noiseStream_measurable t).eval
    exact (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2
      (setup.conditionalSecondMomentBound_integrable μ oracle horacle t i)
  intro t
  induction t with
  | zero =>
      constructor <;> intro i
      · simpa [meanTrackerError, SOptLib.recursiveIterateProcess] using
          (memLp_const (0 : E) : MemLp (fun _ : Ω => (0 : E)) 2 μ)
      · simpa [noiseTrackerError, SOptLib.recursiveIterateProcess] using
          (memLp_const (0 : E) : MemLp (fun _ : Ω => (0 : E)) 2 μ)
  | succ t ih =>
      constructor
      · intro i
        have hleft : MemLp (fun ω => ∑ j : Node,
            setup.C t i j • setup.meanTrackerError (oracle.noise ω) t j) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro j _hj
          exact (ih.1 j).const_smul (setup.C t i j)
        have hinn : MemLp (fun ω => ∑ j : Node,
            matrixSub (Node := Node) (setup.C t)
                (identityMatrix (Node := Node)) i j •
              setup.gradientTable
                (setup.primalState (oracle.noise ω) t) j) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro j _hj
          exact (hgrad t j).const_smul
            (matrixSub (Node := Node) (setup.C t)
              (identityMatrix (Node := Node)) i j)
        have hraw := hleft.add hinn
        refine MemLp.ae_eq ?_ hraw
        exact Filter.Eventually.of_forall fun ω => by
          change
            (∑ j : Node,
                setup.C t i j • setup.meanTrackerError (oracle.noise ω) t j) +
              (∑ j : Node,
                matrixSub (Node := Node) (setup.C t)
                    (identityMatrix (Node := Node)) i j •
                  setup.gradientTable
                    (setup.primalState (oracle.noise ω) t) j) =
              setup.meanTrackerError (oracle.noise ω) (t + 1) i
          exact congrFun (setup.meanTrackerError_succ (oracle.noise ω) t) i |>.symm
      · intro i
        have hleft : MemLp (fun ω => ∑ j : Node,
            setup.C t i j • setup.noiseTrackerError (oracle.noise ω) t j) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro j _hj
          exact (ih.2 j).const_smul (setup.C t i j)
        have hinn : MemLp (fun ω => ∑ j : Node,
            matrixSub (Node := Node) (setup.C t)
                (identityMatrix (Node := Node)) i j • oracle.noise ω t j) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro j _hj
          exact (hnoise t j).const_smul
            (matrixSub (Node := Node) (setup.C t)
              (identityMatrix (Node := Node)) i j)
        have hraw := hleft.add hinn
        refine MemLp.ae_eq ?_ hraw
        exact Filter.Eventually.of_forall fun ω => by
          change
            (∑ j : Node,
                setup.C t i j • setup.noiseTrackerError (oracle.noise ω) t j) +
              (∑ j : Node,
                matrixSub (Node := Node) (setup.C t)
                    (identityMatrix (Node := Node)) i j • oracle.noise ω t j) =
              setup.noiseTrackerError (oracle.noise ω) (t + 1) i
          rfl

theorem meanLiftCorrection_memLp_two
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (k : ℕ) :
    MemLp (fun ω => setup.meanLiftCorrection (oracle.noise ω) k) 2 μ := by
  apply setup.correctedLift_comp_memLp_of_coordinate_memLp 0
  intro i
  simpa [meanLiftCorrection, meanTrackerErrorZeroSum] using
    (setup.splitTrackerErrors_coordinate_memLp μ oracle horacle
      (setup.blockStart k)).1 i

theorem noiseLiftCorrection_memLp_two
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (k : ℕ) :
    MemLp (fun ω => setup.noiseLiftCorrection (oracle.noise ω) k) 2 μ := by
  apply setup.correctedLift_comp_memLp_of_coordinate_memLp 0
  intro i
  simpa [noiseLiftCorrection, noiseTrackerErrorZeroSum] using
    (setup.splitTrackerErrors_coordinate_memLp μ oracle horacle
      (setup.blockStart k)).2 i

/- Every primal and tracker Frobenius square occurring in a finite generated
trajectory is integrable.  The horizon bound records the exact downstream
contract used when integrating (6.18). -/
theorem generated_pushpull_finite_horizon_l2
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (N : ℕ) :
    ∀ t ≤ N,
      (Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState (oracle.noise ω) t)) μ ∧
        Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
          (setup.trackerState (oracle.noise ω) t)) μ) ∧
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (setup.consensusState (oracle.noise ω) t)) μ ∧
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState (oracle.noise ω) t))) μ := by
  classical
  intro t _ht
  have hcoord := setup.generated_pushpull_coordinate_memLp μ oracle horacle t
  have hraw_and_centered_of_coordinate_l2
      (X : Ω → State Node E)
      (hX : ∀ i : Node, MemLp (fun ω => X ω i) 2 μ) :
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E) (X ω)) μ ∧
        Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E) (X ω))) μ := by
    simpa only [frobeniusNormSq, consensusError, arithmeticAverage, nodeCount,
      SOptLib.dependentProductNormSq_def, SOptLib.finiteUniformAverage_def] using
      (SOptLib.integrable_dependentProductNormSq_and_centered_of_coordinate_memLp
        (μ := μ) X hX)
  have hfrobenius_of_coordinate_l2
      (X : Ω → State Node E)
      (hX : ∀ i : Node, MemLp (fun ω => X ω i) 2 μ) :
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E) (X ω)) μ :=
    (hraw_and_centered_of_coordinate_l2 X hX).1
  have hconsensus_of_coordinate_l2
      (X : Ω → State Node E)
      (hX : ∀ i : Node, MemLp (fun ω => X ω i) 2 μ) :
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E) (X ω))) μ :=
    (hraw_and_centered_of_coordinate_l2 X hX).2
  constructor
  · exact ⟨hfrobenius_of_coordinate_l2 _ hcoord.1,
      hfrobenius_of_coordinate_l2 _ hcoord.2⟩
  constructor
  · simpa [consensusState] using
      hconsensus_of_coordinate_l2
        (fun ω => setup.primalState (oracle.noise ω) t) hcoord.1
  · exact hconsensus_of_coordinate_l2
      (fun ω => setup.trackerState (oracle.noise ω) t) hcoord.2

/- Source equation (6.20): the primal displacement is the sum of the
`R_t-I` consensus action and the tracker step. -/
theorem displacement_energy_le_consensus_tracker
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (N : ℕ) :
    setup.displacementEnergy μ oracle N ≤
      2 * setup.pushDeviationNormMax ^ 2 *
          setup.consensusEnergy μ oracle N +
        2 * setup.alpha ^ 2 *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.trackerState (oracle.noise ω) t) ∂μ) := by
  classical
  simpa only [displacementEnergy, consensusEnergy, frobeniusNormSq,
    SOptLib.dependentProductNormSq_def] using
    (SOptLib.finite_horizon_integral_displacement_sq_le_of_affine_update_and_operator_bound
      (μ := μ)
      (x := fun t ω => setup.primalState (oracle.noise ω) t)
      (err := fun t ω => setup.consensusState (oracle.noise ω) t)
      (dir := fun t ω => setup.trackerState (oracle.noise ω) t)
      (T := fun t X => leftMul (Node := Node) (E := E)
        (matrixSub (Node := Node) (setup.R t)
          (identityMatrix (Node := Node))) X)
      (kappa := setup.pushDeviationNormMax) (alpha := setup.alpha) (N := N)
      (hdisp_int := by
        intro t _ht
        unfold SOptLib.dependentProductNormSq
        apply integrable_finset_sum Finset.univ
        intro i _hi
        have hmem :=
          ((setup.generated_pushpull_coordinate_memLp μ oracle horacle
            (t + 1)).1 i).sub
            ((setup.generated_pushpull_coordinate_memLp μ oracle horacle t).1 i)
        simpa only [Pi.sub_apply] using
          (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem)
      (herr_int := by
        intro t ht
        simpa only [frobeniusNormSq, SOptLib.dependentProductNormSq_def] using
          (setup.generated_pushpull_finite_horizon_l2
            μ oracle horacle N t (Nat.le_of_lt ht)).2.1)
      (hdir_int := by
        intro t ht
        simpa only [frobeniusNormSq, SOptLib.dependentProductNormSq_def] using
          (setup.generated_pushpull_finite_horizon_l2
            μ oracle horacle N t (Nat.le_of_lt ht)).1.2)
      (h_update := by
        intro t _ht ω
        exact setup.primalDisplacement_eq_pushConsensus_sub_tracker_source
          (oracle.noise ω) t)
      setup.pushDeviationNormMax_nonneg
      (h_operator := by
        intro t _ht ω
        simpa only [stateFrobeniusNorm, frobeniusNormSq,
          SOptLib.dependentProductNormSq_def] using
          setup.pushDeviation_stateFrobenius_action t
            (setup.consensusState (oracle.noise ω) t)))

/- Expectation-level equation (6.18).  The pathwise convolution estimate is
integrated only after the generated finite-horizon `L²` theorem supplies both
finite-sum integrability premises. -/
theorem expectation_level_consensus_convolution
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (N : ℕ) :
    (setup.withStepsize alpha).consensusEnergy μ oracle N ≤
      alpha ^ 2 * setup.sectionSixGradientResponseFormula *
        Finset.sum (Finset.range N) (fun t =>
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              ((setup.withStepsize alpha).trackerState
                (oracle.noise ω) t)) ∂μ) := by
  classical
  let stepped := setup.withStepsize alpha
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hfinite :=
    stepped.generated_pushpull_finite_horizon_l2 μ oracle horacle_stepped N
  have hleft_int : ∀ t ∈ Finset.range (N + 1),
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (stepped.consensusState (oracle.noise ω) t)) μ := by
    intro t ht
    exact (hfinite t (by simpa [Finset.mem_range] using ht)).2.1
  have hright_int : ∀ t ∈ Finset.range N,
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (stepped.trackerState (oracle.noise ω) t))) μ := by
    intro t ht
    exact (hfinite t (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp ht))
      (Nat.le_refl N))).2.2
  have hmono :
      Finset.sum (Finset.range (N + 1)) (fun t =>
        ∫ ω,
          frobeniusNormSq (Node := Node) (E := E)
            (stepped.consensusState (oracle.noise ω) t) ∂μ) ≤
        (alpha ^ 2 * stepped.sectionSixGradientResponseFormula) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω,
            frobeniusNormSq (Node := Node) (E := E)
              (consensusError (Node := Node) (E := E)
                (stepped.trackerState (oracle.noise ω) t)) ∂μ) := by
    simpa [smul_eq_mul] using
      sum_integral_le_smul_sum_integral_of_ae_sum_le_smul_sum
        (mu := μ) (Finset.range (N + 1)) (Finset.range N)
        (fun t ω => frobeniusNormSq (Node := Node) (E := E)
          (stepped.consensusState (oracle.noise ω) t))
        (fun t ω => frobeniusNormSq (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E)
            (stepped.trackerState (oracle.noise ω) t)))
        (alpha ^ 2 * stepped.sectionSixGradientResponseFormula)
        hleft_int hright_int
        (Filter.Eventually.of_forall fun ω =>
          stepped.consensusState_sq_sum_convolution_source
            (oracle.noise ω) halpha_pos.le N)
  change stepped.consensusEnergy μ oracle N ≤ _
  unfold consensusEnergy
  exact hmono

/-- The finite squared mass of a scalar geometric response is bounded by the
corresponding infinite geometric mass. -/
theorem finite_geometric_sq_response_sum_le
    {M r x : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t => (M * r ^ t * x) ^ 2) ≤
      (M ^ 2 / (1 - r ^ 2)) * x ^ 2 := by
  have hr2_lt : r ^ 2 < 1 := by
    nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
  exact _root_.finite_geometric_sq_response_sum_le hr2_lt N

/-- Lemma B.1 / (B.1): finite square-sum bound for a geometrically weighted
convolution. -/
theorem SquareSummableGeometricConvolution
    {u z : ℕ → ℝ} {M r : ℝ}
    (hu_nonneg : ∀ t : ℕ, 0 ≤ u t)
    (hz_nonneg : ∀ t : ℕ, 0 ≤ z t)
    (hM : 0 ≤ M) (hr0 : 0 < r) (hr1 : r < 1)
    (hrec : ∀ t : ℕ,
      u t ≤ M * r ^ t * u 0 +
        Finset.sum (Finset.range t) fun j =>
          M * r ^ (t - 1 - j) * z j)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t => (u t) ^ 2) ≤
      (2 * M ^ 2 / (1 - r ^ 2)) * (u 0) ^ 2 +
        (2 * M ^ 2 / (1 - r) ^ 2) *
          Finset.sum (Finset.range N) (fun j => (z j) ^ 2) := by
  exact _root_.finite_sq_sum_le_of_le_geometric_initial_add_convolution N
    (fun t _ => hu_nonneg t) hr0.le hr1 (fun t _ => hrec t)

/- Extending a pull product by one time step puts the newest matrix on the
left.  This is the product identity used in the source expansions of both
joint coordinates. -/

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
