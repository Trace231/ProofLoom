import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import SOptLib.Model.Iterates
import SOptLib.Model.NetworkMatrix
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Selection
import SOptLib.Model.Stationarity
import SOptLib.Layer0.Objective

/-!
# PULM-DGD object layer

This file records the paper-facing objects for Pull-with-Memory decentralized
gradient descent before convergence proof work.  The algorithmic state is not a
witness supplied by `Setup`: local gradients, the PULM memory matrix, the
inner-loop `z` variables, the one-step outer update, and the generated iterate
sequence are all definitions.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

namespace PullWithMemoryDGD

variable {Node E : Type*}
variable [Fintype Node] [Nonempty Node] [DecidableEq Node]
variable [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable [FiniteDimensional Real E]

/-- Network-valued iterate: one `E`-valued vector at each node. -/
abbrev NodeState (Node E : Type*) := Node -> E


/-- The paper node count `n`.  The surrounding source-facing model assumes
`[Nonempty Node]`, so this is a positive finite population. -/
def nodeCount (Node : Type*) [Fintype Node] : Nat :=
  Fintype.card Node

/-- The reciprocal node count used in the paper's averages `n^{-1} sum_i`. -/
def invNodeCount (Node : Type*) [Fintype Node] : Real :=
  1 / (Fintype.card Node : Real)

/-- Positive real scalar, used for source parameters whose domain is explicitly
strictly positive. -/
abbrev PositiveReal := {a : Real // 0 < a}

/-- Canonical uniform finite average over the paper's node set. -/
def nodeAverage {V : Type*} [AddCommMonoid V] [Module Real V]
    (x : Node -> V) : V :=
  SOptLib.finiteUniformAverage x

omit [Nonempty Node] [DecidableEq Node] in
theorem nodeAverage_eq_invNodeCount_smul_sum
    {V : Type*} [AddCommMonoid V] [Module Real V] (x : Node -> V) :
    nodeAverage x = (invNodeCount Node) • Finset.univ.sum x := by
  rw [nodeAverage, SOptLib.finiteUniformAverage_def, invNodeCount, one_div]

private theorem nodeAverage_const (x : E) :
    nodeAverage (fun _i : Node => x) = x := by
  simpa [nodeAverage] using SOptLib.finiteUniformAverage_const (ι := Node) (V := E) x

/-- The rank-one averaging matrix `E_n = n^{-1} 1_n 1_n^T`. -/
def averageMatrix (Node : Type*) [Fintype Node] : _root_.Matrix Node Node Real :=
  fun _ _ => invNodeCount Node

/-- The standard basis row `e_i` used to initialize and correct the PULM memory
variable. -/
def basisRow (i j : Node) : Real :=
  if j = i then 1 else 0

/-- Matrix-vector multiplication with the row-stochastic convention used in the
paper. -/
def matrixVecMul (A : _root_.Matrix Node Node Real) (x : Node -> Real) : Node -> Real :=
  fun i => Finset.univ.sum (fun j => A i j * x j)

/-- Matrix action on vector-valued node states, with the same row convention as
`matrixVecMul`. -/
def matrixStateMul (A : _root_.Matrix Node Node Real) (x : NodeState Node E) : NodeState Node E :=
  fun i => Finset.univ.sum (fun j => A i j • x j)

/-- Finite matrix multiplication in the paper's row-stochastic convention. -/
private def matrixMul (A B : _root_.Matrix Node Node Real) : _root_.Matrix Node Node Real :=
  fun i j => Finset.univ.sum (fun ell => A i ell * B ell j)

/-- Matrix subtraction, kept as a named object for source-stage projected
operators. -/
private def matrixSub (A B : _root_.Matrix Node Node Real) : _root_.Matrix Node Node Real :=
  fun i j => A i j - B i j

/-- Scalar multiplication of a finite matrix. -/
private def matrixScale (c : Real) (A : _root_.Matrix Node Node Real) : _root_.Matrix Node Node Real :=
  fun i j => c * A i j

/-- The left projection `I - E_n` used in Appendix D's consensus estimates. -/
private def consensusProjectionMatrix (Node : Type*) [Fintype Node] [DecidableEq Node] :
    _root_.Matrix Node Node Real :=
  fun i j => basisRow i j - averageMatrix Node i j

/-- The operator two-norm of a finite node-indexed matrix, expressed as a
canonical supremum over the unit ball. -/
def matrixTwoNorm (A : _root_.Matrix Node Node Real) : Real :=
  sSup ((fun x : Node -> Real => ‖matrixVecMul A x‖) '' {x : Node -> Real | ‖x‖ <= 1})

private theorem matrixTwoNorm_eq_continuousLinearMap_norm
    (A : _root_.Matrix Node Node Real) :
    matrixTwoNorm A =
      ‖(({ toFun := matrixVecMul A
          , map_add' := by
              intro x y
              funext i
              simp [matrixVecMul, mul_add, Finset.sum_add_distrib]
          , map_smul' := by
              intro c x
              funext i
              simp [matrixVecMul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] } :
          (Node -> Real) →ₗ[Real] (Node -> Real)).toContinuousLinearMap)‖ := by
  let T : (Node -> Real) →L[Real] (Node -> Real) :=
    ({ toFun := matrixVecMul A
      , map_add' := by
          intro x y
          funext i
          simp [matrixVecMul, mul_add, Finset.sum_add_distrib]
      , map_smul' := by
          intro c x
          funext i
          simp [matrixVecMul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] } :
      (Node -> Real) →ₗ[Real] (Node -> Real)).toContinuousLinearMap
  change matrixTwoNorm A = ‖T‖
  rw [← ContinuousLinearMap.sSup_unitClosedBall_eq_norm T]
  unfold matrixTwoNorm T
  congr 1
  ext y
  simp [Metric.mem_closedBall, dist_eq_norm]

private theorem matrixTwoNorm_eq_matrix_norm
    (A : _root_.Matrix Node Node Real) :
    matrixTwoNorm A = ‖A‖ := by
  rw [matrixTwoNorm_eq_continuousLinearMap_norm (A := A)]
  simpa [matrixVecMul, _root_.Matrix.mulVec, dotProduct] using
    (_root_.Matrix.linfty_opNorm_eq_opNorm A).symm

private theorem matrixVecMul_norm_le_matrixTwoNorm_mul_norm
    (A : _root_.Matrix Node Node Real) (x : Node -> Real) :
    ‖matrixVecMul A x‖ <= matrixTwoNorm A * ‖x‖ := by
  simpa [matrixVecMul, _root_.Matrix.mulVec, dotProduct, matrixTwoNorm_eq_matrix_norm (A := A)]
    using (_root_.Matrix.linfty_opNorm_mulVec A x)

private theorem matrixStateMul_inner_coord
    (A : _root_.Matrix Node Node Real) (y : NodeState Node E) (v : E) (i : Node) :
    inner Real (matrixStateMul A y i) v =
      matrixVecMul A (fun j => inner Real (y j) v) i := by
  unfold matrixStateMul matrixVecMul
  rw [sum_inner]
  simp [real_inner_smul_left]

private theorem matrixTwoNorm_nonneg (A : _root_.Matrix Node Node Real) :
    0 <= matrixTwoNorm A := by
  rw [matrixTwoNorm_eq_matrix_norm (A := A)]
  exact norm_nonneg A

private theorem matrix_row_abs_sum_le_matrixTwoNorm
    (A : _root_.Matrix Node Node Real) (i : Node) :
    Finset.univ.sum (fun j => |A i j|) <= matrixTwoNorm A := by
  rw [matrixTwoNorm_eq_matrix_norm (A := A)]
  rw [_root_.Matrix.linfty_opNorm_def A]
  have hrow :
      ((Finset.univ.sum (fun j => ‖A i j‖₊) : NNReal) : ℝ) ≤
        ((Finset.univ.sup (fun i => Finset.univ.sum (fun j => ‖A i j‖₊)) : NNReal) :
          ℝ) := by
    exact
      Finset.le_sup
        (s := (Finset.univ : Finset Node))
        (f := fun i : Node => Finset.univ.sum (fun j : Node => ‖A i j‖₊))
        (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, NNReal.coe_sum] using hrow

private theorem matrixStateMul_norm_le_matrixTwoNorm_mul_norm
    (A : _root_.Matrix Node Node Real) (y : NodeState Node E) :
    ‖matrixStateMul A y‖ <= matrixTwoNorm A * ‖y‖ := by
  classical
  have htarget_nonneg : 0 <= matrixTwoNorm A * ‖y‖ := by
    exact mul_nonneg (matrixTwoNorm_nonneg (A := A)) (norm_nonneg y)
  rw [pi_norm_le_iff_of_nonneg htarget_nonneg]
  intro i
  have htri :
      ‖matrixStateMul A y i‖ <=
        Finset.univ.sum (fun j => ‖A i j • y j‖) := by
    unfold matrixStateMul
    exact norm_sum_le _ _
  have hsum_le :
      Finset.univ.sum (fun j => ‖A i j • y j‖) <=
        Finset.univ.sum (fun j => |A i j| * ‖y‖) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (f := y) j) (abs_nonneg (A i j))
  have hrow :=
    matrix_row_abs_sum_le_matrixTwoNorm (A := A) i
  have hrow_scale :
      Finset.univ.sum (fun j => |A i j| * ‖y‖) <= matrixTwoNorm A * ‖y‖ := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hrow (norm_nonneg y)
  exact le_trans htri (le_trans hsum_le hrow_scale)

private theorem matrixStateMul_matrixMul
    (A B : _root_.Matrix Node Node Real) (x : NodeState Node E) :
    matrixStateMul (matrixMul A B) x = matrixStateMul A (matrixStateMul B x) := by
  funext i
  unfold matrixStateMul matrixMul
  simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]

private theorem matrixStateMul_matrixSub
    (A B : _root_.Matrix Node Node Real) (x : NodeState Node E) :
    matrixStateMul (matrixSub A B) x = matrixStateMul A x - matrixStateMul B x := by
  funext i
  unfold matrixStateMul matrixSub
  simp only [Pi.sub_apply, sub_smul]
  rw [Finset.sum_sub_distrib]

private theorem matrixStateMul_matrixScale
    (c : Real) (A : _root_.Matrix Node Node Real) (x : NodeState Node E) :
    matrixStateMul (matrixScale c A) x = c • matrixStateMul A x := by
  funext i
  unfold matrixStateMul matrixScale
  simp only [mul_smul, Pi.smul_apply, Finset.smul_sum]

/-- Source data for Algorithm 3.  Gradients, averages, memory matrices, updates,
and iterates are intentionally absent as fields; they are defined below. -/
structure Setup (Node E : Type*) [Fintype Node] [DecidableEq Node]
    [Nonempty Node] [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [FiniteDimensional Real E] where
  /-- Component objective `f_i`. -/
  localObjective : Node -> E -> Real
  /-- Common initial value `x^(0)` used at every node. -/
  x0 : E
  /-- Constant stepsize `gamma > 0`. -/
  gamma : PositiveReal
  /-- Inner-loop communication budget `R_k`. -/
  innerRounds : Nat -> Nat
  /-- Time-varying broadcast edges `E^(t)` from the paper's single graph
  sequence.  The direction is `edge t j i` when node `j` sends to node `i`. -/
  edge : Nat -> Node -> Node -> Prop
  /-- Row-stochastic mixing weights `A^(t)` generated from the same single
  time-varying graph sequence. -/
  mixing : Nat -> _root_.Matrix Node Node Real

namespace Setup

/-- Canonical local gradient `grad f_i(x)`. -/
def localGradient (S : Setup Node E) (i : Node) (x : E) : E :=
  gradient (S.localObjective i) x

/-- The finite-average objective `f(x) = n^{-1} sum_i f_i(x)`. -/
def objective (S : Setup Node E) (x : E) : Real :=
  nodeAverage (fun i => S.localObjective i x)

/-- The finite-average gradient field at a centralized point. -/
def fullGradient (S : Setup Node E) (x : E) : E :=
  nodeAverage (fun i => localGradient S i x)

/-- The gradient of the paper objective `f(x)=n^{-1} sum_i f_i(x)`.  This is
the stationarity object appearing in Theorem 2. -/
def objectiveGradient (S : Setup Node E) (x : E) : E :=
  gradient S.objective x

/-- Nodewise deterministic gradients `g_i^(k) = grad f_i(x_i^(k))`. -/
def nodeGradient (S : Setup Node E) (x : NodeState Node E) : NodeState Node E :=
  fun i => localGradient S i (x i)

/-- Network mean `bar x = n^{-1} sum_i x_i`. -/
def meanState (_S : Setup Node E) (x : NodeState Node E) : E :=
  nodeAverage x

/-- Consensus state with every node set to the network mean. -/
def consensusState (S : Setup Node E) (x : NodeState Node E) : NodeState Node E :=
  fun _ => meanState S x

/-- Consensus error `Delta_x = x - E_n x`. -/
def consensusError (S : Setup Node E) (x : NodeState Node E) : NodeState Node E :=
  x - consensusState S x

/-- Paper-facing finite-network mean, consensus-state, and consensus-error API
backed by the staged reusable finite-network definitions. -/
theorem finiteNetworkConsensusState_model_api (S : Setup Node E) (x : NodeState Node E) :
    meanState S x = SOptLib.finiteUniformAverage x ∧
      consensusState S x = (fun _ => meanState S x) ∧
      consensusError S x = x - consensusState S x := by
  exact FiniteNetwork.consensusError_model_api (Node := Node) (E := E) x

/-- Initial node state `x_i^(0)=x^(0)`. -/
def initialState (S : Setup Node E) : NodeState Node E :=
  fun _ => S.x0

/-- Initial PULM memory matrix, whose `i`th row is `e_i`. -/
def initialMemoryMatrix (_S : Setup Node E) : _root_.Matrix Node Node Real :=
  1

/-- Flatten Algorithm 3's outer/inner counters to the paper's single
time-varying graph clock. -/
def communicationTime (S : Setup Node E) (k r : Nat) : Nat :=
  (Finset.range k).sum S.innerRounds + r

/-- One gossip application to a vector-valued node state. -/
def gossipState (S : Setup Node E) (k r : Nat) (z : NodeState Node E) : NodeState Node E :=
  fun i => Finset.univ.sum (fun j => (S.mixing (communicationTime S k r) i j) • z j)

/-- One gossip application to the PULM memory matrix. -/
def gossipMemory (S : Setup Node E) (k r : Nat) (W : _root_.Matrix Node Node Real) : _root_.Matrix Node Node Real :=
  fun i ell => Finset.univ.sum (fun j => S.mixing (communicationTime S k r) i j * W j ell)

/-- Diagonal correction `d_i^(k,r) = [w_i^(k,r+1/2)]_i - 1/n`. -/
def memoryCorrection (S : Setup Node E) (k r : Nat) (W : _root_.Matrix Node Node Real) (i : Node) : Real :=
  gossipMemory S k r W i i - invNodeCount Node

/-- The Algorithm 3 memory update
`w_i^(k,r+1) = w_i^(k,r+1/2) - d_i^(k,r) e_i`. -/
def memoryStep (S : Setup Node E) (k r : Nat) (W : _root_.Matrix Node Node Real) : _root_.Matrix Node Node Real :=
  let half := gossipMemory S k r W
  fun i ell => half i ell - (half i i - invNodeCount Node) * basisRow i ell

/-- The Algorithm 3 `z` update
`z_i^(k,r+1) = z_i^(k,r+1/2) - d_i^(k,r) g_i^(k)`. -/
def zStep (S : Setup Node E) (k r : Nat) (g z : NodeState Node E)
    (W : _root_.Matrix Node Node Real) : NodeState Node E :=
  let halfZ := gossipState S k r z
  let halfW := gossipMemory S k r W
  fun i => halfZ i - (halfW i i - invNodeCount Node) • g i

/-- Pull-with-memory matrix `W^(k,r)` generated by the paper's `w` recursion. -/
def pullMemoryMatrix (S : Setup Node E) (k : Nat) : Nat -> _root_.Matrix Node Node Real
  | 0 => initialMemoryMatrix S
  | r + 1 => memoryStep S k r (pullMemoryMatrix S k r)

/-- Initial inner-loop state `z_i^(k,0)=x_i^(k)-gamma g_i^(k)`. -/
def initialZ (S : Setup Node E) (x : NodeState Node E) : NodeState Node E :=
  fun i => x i - (S.gamma : Real) • nodeGradient S x i

/-- Parameter coefficient matrix in the exact Algorithm 3 decomposition of
`innerZ`.  It evolves only through the gossip part of the `z` update. -/
private def innerParameterMatrix (S : Setup Node E) (k : Nat) : Nat -> _root_.Matrix Node Node Real
  | 0 => initialMemoryMatrix S
  | r + 1 => gossipMemory S k r (innerParameterMatrix S k r)

/-- Gradient coefficient matrix in the exact Algorithm 3 decomposition of
`innerZ`.  The diagonal correction is divided by the outer stepsize so that the
decomposition keeps the paper's `-gamma * M g` form. -/
private def innerGradientMatrix (S : Setup Node E) (k : Nat) : Nat -> _root_.Matrix Node Node Real
  | 0 => initialMemoryMatrix S
  | r + 1 =>
      fun i ell =>
        gossipMemory S k r (innerGradientMatrix S k r) i ell +
          ((gossipMemory S k r (pullMemoryMatrix S k r) i i - invNodeCount Node) /
            (S.gamma : Real)) *
            basisRow i ell

/-- Inner-loop `z^(k,r)` generated by Algorithm 3 with the memory matrix above. -/
def innerZ (S : Setup Node E) (k : Nat) (x : NodeState Node E) : Nat -> NodeState Node E
  | 0 => initialZ S x
  | r + 1 => zStep S k r (nodeGradient S x) (innerZ S k x r) (pullMemoryMatrix S k r)

/-- The paper's one-step outer update `x_i^(k+1)=z_i^(k,R_k)`. -/
def outerUpdate (S : Setup Node E) (k : Nat) (x : NodeState Node E) : NodeState Node E :=
  innerZ S k x (S.innerRounds k)

/-- Deterministic outer transition, written in the `recursiveIterateProcess`
shape used by SOptLib. -/
def outerStep (S : Setup Node E) (k : Nat) (x : NodeState Node E) (_ : Unit) : NodeState Node E :=
  outerUpdate S k x

/-- Generated network iterates of Algorithm 3. -/
def iterateProcess (S : Setup Node E) : Nat -> Unit -> NodeState Node E :=
  SOptLib.recursiveIterateProcess (initialState S) (outerStep S)

/-- The deterministic node iterate `x^(k)`. -/
def iterate (S : Setup Node E) (k : Nat) : NodeState Node E :=
  iterateProcess S k ()

/-- Mean iterate `bar x^(k)`. -/
def meanIterate (S : Setup Node E) (k : Nat) : E :=
  meanState S (iterate S k)

/-- Average stationarity certificate `K^{-1} sum_{k=0}^{K-1} ||grad f(bar x^k)||^2`. -/
def averagedStationarity (S : Setup Node E) (K : Nat) : Real :=
  SOptLib.finiteAverageExactStationarity
    (fun k => objectiveGradient S (meanIterate S k)) K

/-- Total number of communication rounds through the first `K` outer steps. -/
def communicationRounds (S : Setup Node E) (K : Nat) : Nat :=
  (Finset.range K).sum S.innerRounds

/-- Positive outer-loop indices, used for source expressions involving
`ln(k)`.  The PDF prints a `k = 0` schedule but does not state a convention for
`ln(0)`. -/
abbrev PositiveOuterIndex := {k : Nat // 0 < k}

/-- Positive horizons, used for the displayed `1/K` stationarity averages. -/
abbrev PositiveHorizon := {K : Nat // 0 < K}

variable (S : Setup Node E)

theorem gamma_pos :
    0 < (S.gamma : Real) := by
  exact S.gamma.property

theorem localGradient_eq (i : Node) (x : E) :
    localGradient S i x = gradient (S.localObjective i) x := by
  rfl

theorem objective_eq (x : E) :
    objective S x = nodeAverage (fun i => S.localObjective i x) := by
  rfl

omit [DecidableEq Node] in
theorem nodeCount_pos :
    0 < nodeCount Node := by
  exact Fintype.card_pos

omit [Nonempty Node] [DecidableEq Node] in
theorem invNodeCount_eq :
    invNodeCount Node = (nodeCount Node : Real)⁻¹ := by
  rw [invNodeCount, nodeCount, one_div]

theorem nodeGradient_eq (x : NodeState Node E) (i : Node) :
    nodeGradient S x i = localGradient S i (x i) := by
  rfl

theorem pullMemoryMatrix_zero (k : Nat) :
    pullMemoryMatrix S k 0 = initialMemoryMatrix S := by
  rfl

theorem pullMemoryMatrix_succ (k r : Nat) :
    pullMemoryMatrix S k (Nat.succ r) = memoryStep S k r (pullMemoryMatrix S k r) := by
  rfl

theorem innerZ_zero (k : Nat) (x : NodeState Node E) :
    innerZ S k x 0 = initialZ S x := by
  rfl

theorem innerZ_succ (k r : Nat) (x : NodeState Node E) :
    innerZ S k x (Nat.succ r) =
      zStep S k r (nodeGradient S x) (innerZ S k x r) (pullMemoryMatrix S k r) := by
  rfl

private theorem innerParameterMatrix_zero (k : Nat) :
    innerParameterMatrix S k 0 = initialMemoryMatrix S := by
  rfl

private theorem innerParameterMatrix_succ (k r : Nat) :
    innerParameterMatrix S k (Nat.succ r) =
      gossipMemory S k r (innerParameterMatrix S k r) := by
  rfl

private theorem innerGradientMatrix_zero (k : Nat) :
    innerGradientMatrix S k 0 = initialMemoryMatrix S := by
  rfl

private theorem innerGradientMatrix_succ (k r : Nat) :
    innerGradientMatrix S k (Nat.succ r) =
      fun i ell =>
        gossipMemory S k r (innerGradientMatrix S k r) i ell +
          ((gossipMemory S k r (pullMemoryMatrix S k r) i i - invNodeCount Node) /
            (S.gamma : Real)) *
            basisRow i ell := by
  rfl

/-- Exact relation between the two Algorithm 3 coefficient matrices.

The gamma-scaled gradient coefficient is not an independent `M^(k,r)` object:
for the actual Lean recursion it is `(gamma + 1) A^(k,r) - W^(k,r)`.  This
identity is the object-model reason why the Appendix-D `M^(k)-E_n` rate cannot
be obtained by simply reusing the PULM `W` rate with the same constant. -/
private theorem matrixScale_innerGradientMatrix_eq_parameter_sub_pullMemoryMatrix
    (k r : Nat) :
    matrixScale (S.gamma : Real) (innerGradientMatrix S k r) =
      matrixSub
        (matrixScale ((S.gamma : Real) + 1) (innerParameterMatrix S k r))
        (pullMemoryMatrix S k r) := by
  induction r with
  | zero =>
      funext i j
      simp [matrixScale, matrixSub, innerGradientMatrix_zero,
        innerParameterMatrix_zero, pullMemoryMatrix_zero]
      ring
  | succ r ih =>
      funext i j
      have hij := congrFun (congrFun ih i) j
      rw [innerGradientMatrix_succ, innerParameterMatrix_succ, pullMemoryMatrix_succ]
      unfold matrixScale matrixSub memoryStep gossipMemory
      have hgamma_ne : (S.gamma : Real) ≠ 0 := ne_of_gt S.gamma.property
      calc
        (S.gamma : Real) *
            (Finset.univ.sum
                  (fun x => S.mixing (communicationTime S k r) i x *
                    innerGradientMatrix S k r x j) +
                ((Finset.univ.sum
                      (fun x => S.mixing (communicationTime S k r) i x *
                        pullMemoryMatrix S k r x i) -
                    invNodeCount Node) /
                  (S.gamma : Real)) *
                  basisRow i j) =
          (Finset.univ.sum
                (fun x => S.mixing (communicationTime S k r) i x *
                  ((S.gamma : Real) * innerGradientMatrix S k r x j))) +
            (Finset.univ.sum
                  (fun x => S.mixing (communicationTime S k r) i x *
                    pullMemoryMatrix S k r x i) -
                invNodeCount Node) *
              basisRow i j := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · apply Finset.sum_congr rfl
              intro x _hx
              ring
            · field_simp [hgamma_ne]
        _ =
          Finset.univ.sum
              (fun x =>
                S.mixing (communicationTime S k r) i x *
                  (((S.gamma : Real) + 1) * innerParameterMatrix S k r x j -
                    pullMemoryMatrix S k r x j)) +
            (Finset.univ.sum
                  (fun x => S.mixing (communicationTime S k r) i x *
                    pullMemoryMatrix S k r x i) -
                invNodeCount Node) *
              basisRow i j := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _hx
            rw [show (S.gamma : Real) * innerGradientMatrix S k r x j =
                ((S.gamma : Real) + 1) * innerParameterMatrix S k r x j -
                  pullMemoryMatrix S k r x j by
              simpa [matrixScale, matrixSub] using congrFun (congrFun ih x) j]
        _ =
          ((S.gamma : Real) + 1) *
              Finset.univ.sum
                (fun x =>
                  S.mixing (communicationTime S k r) i x *
                    innerParameterMatrix S k r x j) -
            (Finset.univ.sum
                (fun x =>
                  S.mixing (communicationTime S k r) i x *
                    pullMemoryMatrix S k r x j) -
              (Finset.univ.sum
                    (fun x => S.mixing (communicationTime S k r) i x *
                      pullMemoryMatrix S k r x i) -
                  invNodeCount Node) *
                basisRow i j) := by
            have hsplit :
                Finset.univ.sum
                    (fun x =>
                      S.mixing (communicationTime S k r) i x *
                        (((S.gamma : Real) + 1) * innerParameterMatrix S k r x j -
                          pullMemoryMatrix S k r x j)) =
                  Finset.univ.sum
                      (fun x =>
                        S.mixing (communicationTime S k r) i x *
                          ((S.gamma : Real) + 1) * innerParameterMatrix S k r x j) -
                    Finset.univ.sum
                      (fun x =>
                        S.mixing (communicationTime S k r) i x *
                          pullMemoryMatrix S k r x j) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro x _hx
              ring
            have hscale :
                Finset.univ.sum
                    (fun x =>
                      S.mixing (communicationTime S k r) i x *
                        ((S.gamma : Real) + 1) * innerParameterMatrix S k r x j) =
                  ((S.gamma : Real) + 1) *
                    Finset.univ.sum
                      (fun x =>
                        S.mixing (communicationTime S k r) i x *
                          innerParameterMatrix S k r x j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _hx
              ring
            rw [hsplit, hscale]
            ring

private theorem gossipState_memory_apply
    (k r : Nat) (W : _root_.Matrix Node Node Real) (y : NodeState Node E) :
    gossipState S k r (matrixStateMul W y) =
      matrixStateMul (gossipMemory S k r W) y := by
  funext i
  unfold gossipState gossipMemory matrixStateMul
  simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]

private theorem gossipState_sub
    (k r : Nat) (x y : NodeState Node E) :
    gossipState S k r (x - y) = gossipState S k r x - gossipState S k r y := by
  funext i
  unfold gossipState
  simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

private theorem gossipState_smul
    (k r : Nat) (c : Real) (x : NodeState Node E) :
    gossipState S k r (c • x) = c • gossipState S k r x := by
  funext i
  unfold gossipState
  simp only [Pi.smul_apply, Finset.smul_sum, smul_smul]
  congr 1
  ext j
  rw [mul_comm]

private theorem memory_correction_apply
    (H : _root_.Matrix Node Node Real) (d : Real) (y : NodeState Node E) (i : Node) :
    Finset.univ.sum (fun ell => (H i ell - d * basisRow i ell) • y ell) =
      Finset.univ.sum (fun ell => H i ell • y ell) - d • y i := by
  simpa [basisRow, _root_.Matrix.one_apply, eq_comm] using
    (_root_.Matrix.sum_sub_diagonal_smul_apply
      (R := Real) (Node := Node) (E := E) (H := H) (d := fun _ => d) (y := y) (i := i))

private theorem matrixStateMul_add_basisRow_apply
    (H : _root_.Matrix Node Node Real) (d : Node -> Real) (y : NodeState Node E) (i : Node) :
    matrixStateMul (fun i ell => H i ell + d i * basisRow i ell) y i =
      matrixStateMul H y i + d i • y i := by
  classical
  unfold matrixStateMul
  simp only [add_smul, mul_smul]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [basisRow]
  · intro b _hb hbi
    simp [basisRow, hbi]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem initialMemoryMatrix_apply (y : NodeState Node E) :
    (fun i => Finset.univ.sum (fun j => initialMemoryMatrix S i j • y j)) = y := by
  simpa [initialMemoryMatrix] using
    (_root_.Matrix.one_sum_smul
      (R := Real) (Node := Node) (E := E) (x := y))

private theorem matrixStateMul_initialMemoryMatrix (y : NodeState Node E) :
    matrixStateMul (initialMemoryMatrix S) y = y := by
  simpa [matrixStateMul] using initialMemoryMatrix_apply (S := S) y

private theorem innerZ_actual_matrix_decomposition
    (k r : Nat) (x : NodeState Node E) :
    innerZ S k x r =
      matrixStateMul (innerParameterMatrix S k r) x -
        (S.gamma : Real) •
          matrixStateMul (innerGradientMatrix S k r) (nodeGradient S x) := by
  induction r with
  | zero =>
      rw [innerZ_zero, innerParameterMatrix_zero, innerGradientMatrix_zero,
        matrixStateMul_initialMemoryMatrix, matrixStateMul_initialMemoryMatrix]
      rfl
  | succ r ih =>
      rw [innerZ_succ, ih]
      unfold zStep
      rw [gossipState_sub, gossipState_smul, gossipState_memory_apply,
        gossipState_memory_apply]
      rw [innerParameterMatrix_succ, innerGradientMatrix_succ]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [matrixStateMul_add_basisRow_apply]
      have hgamma_ne : (S.gamma : Real) ≠ 0 := ne_of_gt S.gamma.property
      have hcorr :
          (S.gamma : Real) •
              (((gossipMemory S k r (pullMemoryMatrix S k r) i i -
                    invNodeCount Node) /
                  (S.gamma : Real)) • nodeGradient S x i) =
            (gossipMemory S k r (pullMemoryMatrix S k r) i i -
                invNodeCount Node) • nodeGradient S x i := by
        rw [smul_smul]
        congr 1
        field_simp [hgamma_ne]
      rw [smul_add, hcorr]
      module

private theorem outerUpdate_actual_matrix_decomposition
    (k : Nat) (x : NodeState Node E) :
    outerUpdate S k x =
      matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) x -
        (S.gamma : Real) •
          matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
            (nodeGradient S x) := by
  unfold outerUpdate
  exact innerZ_actual_matrix_decomposition (S := S) k (S.innerRounds k) x

private theorem zStep_memory_apply_initialZ_residual
    (k r : Nat) (x : NodeState Node E) (W : _root_.Matrix Node Node Real) :
    zStep S k r (nodeGradient S x)
        (fun i => Finset.univ.sum (fun j => W i j • initialZ S x j)) W =
      fun i =>
        Finset.univ.sum (fun j => memoryStep S k r W i j • initialZ S x j) +
          (gossipMemory S k r W i i - invNodeCount Node) •
            (initialZ S x i - nodeGradient S x i) := by
  funext i
  unfold zStep
  rw [show
      gossipState S k r (fun i => Finset.univ.sum (fun j => W i j • initialZ S x j)) i =
        Finset.univ.sum (fun ell => gossipMemory S k r W i ell • initialZ S x ell) by
        exact congrFun (gossipState_memory_apply (S := S) k r W (initialZ S x)) i]
  unfold memoryStep
  change
    Finset.univ.sum (fun ell => gossipMemory S k r W i ell • initialZ S x ell) -
        (gossipMemory S k r W i i - invNodeCount Node) • nodeGradient S x i =
      Finset.univ.sum
          (fun ell =>
            (gossipMemory S k r W i ell -
                (gossipMemory S k r W i i - invNodeCount Node) * basisRow i ell) •
              initialZ S x ell) +
        (gossipMemory S k r W i i - invNodeCount Node) •
          (initialZ S x i - nodeGradient S x i)
  rw [memory_correction_apply]
  simp only [sub_smul]
  module

private theorem innerZ_one_memory_apply_initialZ_residual
    (k : Nat) (x : NodeState Node E) :
    innerZ S k x 1 =
      fun i =>
        Finset.univ.sum (fun j => pullMemoryMatrix S k 1 i j • initialZ S x j) +
          (gossipMemory S k 0 (initialMemoryMatrix S) i i - invNodeCount Node) •
            (initialZ S x i - nodeGradient S x i) := by
  rw [innerZ_succ, pullMemoryMatrix_zero]
  calc
    zStep S k 0 (nodeGradient S x) (innerZ S k x 0) (initialMemoryMatrix S) =
        zStep S k 0 (nodeGradient S x)
          (fun i => Finset.univ.sum (fun j => initialMemoryMatrix S i j • initialZ S x j))
          (initialMemoryMatrix S) := by
          rw [innerZ_zero, initialMemoryMatrix_apply]
    _ = (fun i =>
          Finset.univ.sum (fun j => pullMemoryMatrix S k 1 i j • initialZ S x j) +
            (gossipMemory S k 0 (initialMemoryMatrix S) i i - invNodeCount Node) •
              (initialZ S x i - nodeGradient S x i)) := by
          simpa [pullMemoryMatrix_succ, pullMemoryMatrix_zero]
            using zStep_memory_apply_initialZ_residual (S := S) k 0 x (initialMemoryMatrix S)

theorem outerUpdate_eq_innerZ (k : Nat) (x : NodeState Node E) :
    outerUpdate S k x = innerZ S k x (S.innerRounds k) := by
  rfl

theorem iterate_zero :
    iterate S 0 = initialState S := by
  rfl

theorem iterate_succ (k : Nat) :
    iterate S (k + 1) = outerUpdate S k (iterate S k) := by
  rfl

theorem meanIterate_eq (k : Nat) :
    meanIterate S k = meanState S (iterate S k) := by
  rfl

private theorem meanIterate_zero :
    meanIterate S 0 = S.x0 := by
  have havg : nodeAverage (initialState S) = S.x0 := by
    simpa [initialState] using nodeAverage_const (Node := Node) (E := E) S.x0
  simp [meanIterate, meanState, iterate_zero, havg]

private theorem consensusError_iterate_zero :
    consensusError S (iterate S 0) = 0 := by
  have havg : nodeAverage (initialState S) = S.x0 := by
    simpa [initialState] using nodeAverage_const (Node := Node) (E := E) S.x0
  funext i
  simp [consensusError, consensusState, meanState, iterate_zero, initialState,
    havg]

private theorem consensusError_sub (x y : NodeState Node E) :
    consensusError S (x - y) = consensusError S x - consensusError S y := by
  funext i
  unfold consensusError consensusState meanState nodeAverage SOptLib.finiteUniformAverage
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, smul_sub]
  abel

private theorem consensusError_smul (c : Real) (x : NodeState Node E) :
    consensusError S (c • x) = c • consensusError S x := by
  funext i
  unfold consensusError consensusState meanState nodeAverage SOptLib.finiteUniformAverage
  simp [Pi.sub_apply, Pi.smul_apply, Finset.smul_sum, smul_sub, smul_smul,
    mul_comm, mul_left_comm, mul_assoc]

private theorem consensusError_add (x y : NodeState Node E) :
    consensusError S (x + y) = consensusError S x + consensusError S y := by
  funext i
  unfold consensusError consensusState meanState nodeAverage SOptLib.finiteUniformAverage
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, smul_add]
  abel

private theorem matrixStateMul_consensusProjectionMatrix_eq_consensusError
    (x : NodeState Node E) :
    matrixStateMul (consensusProjectionMatrix Node) x = consensusError S x := by
  classical
  funext i
  unfold matrixStateMul consensusProjectionMatrix consensusError consensusState meanState
  rw [nodeAverage_eq_invNodeCount_smul_sum]
  simp only [sub_smul, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp [basisRow]
    · intro b _hb hbi
      simp [basisRow, hbi]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · rw [Finset.smul_sum]
    rfl

private theorem consensusError_consensusState_zero (x : NodeState Node E) :
    consensusError S (consensusState S x) = 0 := by
  have hmean : meanState S (consensusState S x) = meanState S x := by
    unfold meanState consensusState
    simpa using nodeAverage_const (Node := Node) (E := E) (meanState S x)
  funext i
  simp [consensusError, consensusState, hmean]

private theorem consensusError_idempotent (x : NodeState Node E) :
    consensusError S (consensusError S x) = consensusError S x := by
  change consensusError S (x - consensusState S x) = consensusError S x
  rw [consensusError_sub]
  rw [consensusError_consensusState_zero]
  simp

private theorem matrixStateMul_add
    (A : _root_.Matrix Node Node Real) (x y : NodeState Node E) :
    matrixStateMul A (x + y) = matrixStateMul A x + matrixStateMul A y := by
  funext i
  unfold matrixStateMul
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

private theorem meanState_norm_le (x : NodeState Node E) :
    ‖meanState S x‖ <= ‖x‖ := by
  have hcard_ne : (Fintype.card Node : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Node))
  have hinv_nonneg : 0 <= (Fintype.card Node : Real)⁻¹ := by
    positivity
  calc
    ‖meanState S x‖ =
        ‖(Fintype.card Node : Real)⁻¹ • Finset.univ.sum x‖ := by
          rfl
    _ = (Fintype.card Node : Real)⁻¹ * ‖Finset.univ.sum x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    _ <= (Fintype.card Node : Real)⁻¹ *
        Finset.univ.sum (fun i => ‖x i‖) := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hinv_nonneg
    _ <= (Fintype.card Node : Real)⁻¹ *
        Finset.univ.sum (fun _i : Node => ‖x‖) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun i _hi => norm_le_pi_norm (f := x) i))
            hinv_nonneg
    _ = ‖x‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp [hcard_ne]

private theorem consensusState_norm_le (x : NodeState Node E) :
    ‖consensusState S x‖ <= ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  exact meanState_norm_le (S := S) x

private theorem consensusError_norm_le_two_norm (x : NodeState Node E) :
    ‖consensusError S x‖ <= 2 * ‖x‖ := by
  calc
    ‖consensusError S x‖ = ‖x - consensusState S x‖ := by rfl
    _ <= ‖x‖ + ‖consensusState S x‖ := norm_sub_le x (consensusState S x)
    _ <= 2 * ‖x‖ := by
          linarith [consensusState_norm_le (S := S) x]

private theorem consensusError_iterate_succ_decomposition
    (hdecomp :
      forall k,
        iterate S (k + 1) =
          matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k) -
            (S.gamma : Real) •
              matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
                (nodeGradient S (iterate S k)))
    (k : Nat) :
    consensusError S (iterate S (k + 1)) =
      consensusError S
        (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k)) -
        consensusError S
          ((S.gamma : Real) •
            matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
              (nodeGradient S (iterate S k))) := by
  rw [hdecomp k]
  exact consensusError_sub (S := S)
    (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k))
    ((S.gamma : Real) •
      matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
        (nodeGradient S (iterate S k)))


private theorem matrixStateMul_averageMatrix_eq_consensusState
    (x : NodeState Node E) :
    matrixStateMul (averageMatrix Node) x = consensusState S x := by
  funext i
  unfold matrixStateMul averageMatrix consensusState meanState
  rw [nodeAverage_eq_invNodeCount_smul_sum]
  rw [Finset.smul_sum]

private theorem matrixStateMul_consensusState_of_rowStochastic
    (A : _root_.Matrix Node Node Real) (hA : A ∈ _root_.Matrix.rowStochastic Real Node) (x : NodeState Node E) :
    matrixStateMul A (consensusState S x) = consensusState S x := by
  funext i
  unfold matrixStateMul consensusState
  rw [← Finset.sum_smul]
  rw [_root_.Matrix.sum_row_of_mem_rowStochastic hA i, one_smul]

private theorem matrixStateMul_sub_average_eq_matrixStateMul_consensusError
    (A : _root_.Matrix Node Node Real) (hA : A ∈ _root_.Matrix.rowStochastic Real Node) (x : NodeState Node E) :
    matrixStateMul (fun i j => A i j - averageMatrix Node i j) x =
      matrixStateMul A (consensusError S x) := by
  funext i
  calc
    matrixStateMul (fun i j => A i j - averageMatrix Node i j) x i =
        matrixStateMul A x i - matrixStateMul (averageMatrix Node) x i := by
          unfold matrixStateMul
          simp only [sub_smul]
          rw [Finset.sum_sub_distrib]
    _ = matrixStateMul A x i - consensusState S x i := by
          rw [matrixStateMul_averageMatrix_eq_consensusState (S := S) x]
    _ = matrixStateMul A x i - matrixStateMul A (consensusState S x) i := by
          rw [matrixStateMul_consensusState_of_rowStochastic (S := S) A hA x]
    _ = matrixStateMul A (consensusError S x) i := by
          unfold matrixStateMul consensusError
          simp only [Pi.sub_apply, sub_smul]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [smul_sub]

private theorem matrixStateMul_norm_le_of_rowStochastic
    (A : _root_.Matrix Node Node Real) (hA : A ∈ _root_.Matrix.rowStochastic Real Node) (y : NodeState Node E) :
    ‖matrixStateMul A y‖ <= ‖y‖ := by
  classical
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg y)]
  intro i
  have htri :
      ‖matrixStateMul A y i‖ <=
        Finset.univ.sum (fun j => ‖A i j • y j‖) := by
    unfold matrixStateMul
    exact norm_sum_le _ _
  have hsum_le :
      Finset.univ.sum (fun j => ‖A i j • y j‖) <=
        Finset.univ.sum (fun j => A i j * ‖y‖) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hA.1 i j)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (f := y) j) (hA.1 i j)
  calc
    ‖matrixStateMul A y i‖ <=
        Finset.univ.sum (fun j => ‖A i j • y j‖) := htri
    _ <= Finset.univ.sum (fun j => A i j * ‖y‖) := hsum_le
    _ = (Finset.univ.sum (fun j => A i j)) * ‖y‖ := by
          rw [Finset.sum_mul]
    _ = ‖y‖ := by rw [_root_.Matrix.sum_row_of_mem_rowStochastic hA i, one_mul]

private theorem consensusError_matrixStateMul_eq_consensusError_matrixStateMul_consensusError
    (A : _root_.Matrix Node Node Real) (hA : A ∈ _root_.Matrix.rowStochastic Real Node) (x : NodeState Node E) :
    consensusError S (matrixStateMul A x) =
      consensusError S (matrixStateMul A (consensusError S x)) := by
  have hx : x = consensusState S x + consensusError S x := by
    funext i
    simp [consensusError]
  calc
    consensusError S (matrixStateMul A x) =
        consensusError S (matrixStateMul A (consensusState S x + consensusError S x)) := by
          exact congrArg (fun y => consensusError S (matrixStateMul A y)) hx
    _ = consensusError S
        (matrixStateMul A (consensusState S x) +
          matrixStateMul A (consensusError S x)) := by
          rw [matrixStateMul_add]
    _ = consensusError S
        (consensusState S x + matrixStateMul A (consensusError S x)) := by
          rw [matrixStateMul_consensusState_of_rowStochastic (S := S) A hA x]
    _ = consensusError S (consensusState S x) +
        consensusError S (matrixStateMul A (consensusError S x)) := by
          rw [consensusError_add]
    _ = consensusError S (matrixStateMul A (consensusError S x)) := by
          rw [consensusError_consensusState_zero]
          simp

private theorem gossipState_norm_le_of_rowStochastic
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (k r : Nat) (z : NodeState Node E) :
    ‖gossipState S k r z‖ <= ‖z‖ := by
  simpa [gossipState] using
    matrixStateMul_norm_le_of_rowStochastic
      (A := S.mixing (communicationTime S k r)) (hrow (communicationTime S k r)) z

private theorem initialMemoryMatrix_rowStochastic :
    (initialMemoryMatrix S) ∈ _root_.Matrix.rowStochastic Real Node := by
  simpa [initialMemoryMatrix] using
    (Submonoid.one_mem (_root_.Matrix.rowStochastic Real Node))

private theorem gossipMemory_rowStochastic
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (k r : Nat) {W : _root_.Matrix Node Node Real} (hW : W ∈ _root_.Matrix.rowStochastic Real Node) :
    (gossipMemory S k r W) ∈ _root_.Matrix.rowStochastic Real Node := by
  classical
  refine (_root_.Matrix.mem_rowStochastic_iff_sum
    (M := (gossipMemory S k r W : _root_.Matrix Node Node Real))).2 ?_
  constructor
  · intro i ell
    unfold gossipMemory
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg ((hrow (communicationTime S k r)).1 i j) (hW.1 j ell))
  · intro i
    unfold gossipMemory
    calc
      Finset.univ.sum
          (fun ell => Finset.univ.sum
            (fun j => S.mixing (communicationTime S k r) i j * W j ell)) =
          Finset.univ.sum
            (fun j => Finset.univ.sum
              (fun ell => S.mixing (communicationTime S k r) i j * W j ell)) := by
            rw [Finset.sum_comm]
      _ = Finset.univ.sum
            (fun j => S.mixing (communicationTime S k r) i j *
              Finset.univ.sum (fun ell => W j ell)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun j => S.mixing (communicationTime S k r) i j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [_root_.Matrix.sum_row_of_mem_rowStochastic hW j, mul_one]
      _ = 1 := _root_.Matrix.sum_row_of_mem_rowStochastic
        (hrow (communicationTime S k r)) i

private theorem innerParameterMatrix_rowStochastic
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (k r : Nat) :
    (innerParameterMatrix S k r) ∈ _root_.Matrix.rowStochastic Real Node := by
  induction r with
  | zero =>
      rw [innerParameterMatrix_zero]
      exact initialMemoryMatrix_rowStochastic (S := S)
  | succ r ih =>
      rw [innerParameterMatrix_succ]
      exact gossipMemory_rowStochastic (S := S) hrow k r ih

private theorem innerParameterMatrix_deviation_eq_consensusError
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (k r : Nat) (x : NodeState Node E) :
    matrixStateMul
        (fun i j => innerParameterMatrix S k r i j - averageMatrix Node i j) x =
      matrixStateMul (innerParameterMatrix S k r) (consensusError S x) := by
  exact matrixStateMul_sub_average_eq_matrixStateMul_consensusError (S := S)
    (innerParameterMatrix S k r) (innerParameterMatrix_rowStochastic (S := S) hrow k r) x

private theorem innerParameterMatrix_deviation_norm_le_consensusError
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (k r : Nat) (x : NodeState Node E) :
    ‖matrixStateMul
        (fun i j => innerParameterMatrix S k r i j - averageMatrix Node i j) x‖ <=
      ‖consensusError S x‖ := by
  rw [innerParameterMatrix_deviation_eq_consensusError (S := S) hrow k r x]
  exact matrixStateMul_norm_le_of_rowStochastic (innerParameterMatrix S k r)
    (innerParameterMatrix_rowStochastic (S := S) hrow k r) (consensusError S x)

private theorem innerParameterMatrix_sub_pullMemoryMatrix_succ
    (k r : Nat) :
    (fun i j =>
        innerParameterMatrix S k (r + 1) i j - pullMemoryMatrix S k (r + 1) i j) =
      fun i j =>
        gossipMemory S k r
            (fun p q => innerParameterMatrix S k r p q - pullMemoryMatrix S k r p q)
            i j +
          memoryCorrection S k r (pullMemoryMatrix S k r) i * basisRow i j := by
  funext i j
  rw [innerParameterMatrix_succ, pullMemoryMatrix_succ]
  unfold memoryStep memoryCorrection gossipMemory
  have hsum :
      Finset.univ.sum
          (fun p =>
            S.mixing (communicationTime S k r) i p *
              innerParameterMatrix S k r p j -
            S.mixing (communicationTime S k r) i p *
              pullMemoryMatrix S k r p j) =
        Finset.univ.sum
          (fun p =>
            S.mixing (communicationTime S k r) i p *
              (innerParameterMatrix S k r p j - pullMemoryMatrix S k r p j)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  rw [← hsum, Finset.sum_sub_distrib]
  ring

private theorem innerParameterMatrix_sub_pullMemoryMatrix_succ_state
    (k r : Nat) (x : NodeState Node E) :
    matrixStateMul
        (fun i j =>
          innerParameterMatrix S k (r + 1) i j - pullMemoryMatrix S k (r + 1) i j) x =
      matrixStateMul
          (gossipMemory S k r
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j)) x +
        fun i => memoryCorrection S k r (pullMemoryMatrix S k r) i • x i := by
  rw [innerParameterMatrix_sub_pullMemoryMatrix_succ (S := S) k r]
  funext i
  exact matrixStateMul_add_basisRow_apply
    (gossipMemory S k r
      (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j))
    (fun i => memoryCorrection S k r (pullMemoryMatrix S k r) i) x i

/-- Edge relation in the paper's `B`-step accumulated graph starting at the
single graph time `t`. -/
def AccumulatedEdge (S : Setup Node E) (t B : Nat) (source target : Node) : Prop :=
  TimeVaryingDigraph.AccumulatedEdge S.edge t B source target

/-- Assumption 1: there is a positive window length whose accumulated graph is
strongly connected, and every instantaneous graph has all self-loops. -/
def BStepStronglyConnected (S : Setup Node E) (B : Nat) : Prop :=
  TimeVaryingDigraph.BStepStronglyConnected S.edge B


/-- Uniform lower bound on all nonzero weights. -/
def LowerBoundedEntries (S : Setup Node E) (tau : Real) : Prop :=
  FiniteNetwork.LowerBoundedNonzeroEntries S.mixing tau

/-- The mathematical part of Assumptions 1--3 that is visible at the matrix
interface used by Algorithm 3.  The operational "single use / unknown
out-degree" condition from Assumption 2 has no additional mathematical payload
in this deterministic object layer. -/
def BroadcastNetworkAssumptions (S : Setup Node E) : Prop :=
  TimeVaryingDigraph.BroadcastNetworkAssumptions S.edge S.mixing

/-- Assumption 4: component gradients are globally `L`-Lipschitz and the
component initial gaps are bounded by `Delta`. -/
def componentInfimumValue (S : Setup Node E) (i : Node) : Real :=
  SOptLib.objectiveInfimumValue (Set.univ : Set E) (S.localObjective i)


theorem componentInfimumValue_le
    (h : (forall i, BddBelow ((S.localObjective i) '' (Set.univ : Set E)))) (i : Node) (x : E) :
    componentInfimumValue S i <= S.localObjective i x := by
  exact SOptLib.objectiveInfimumValue_le (h i) (by simp)

/-- Assumption 4: component gradients are globally `L`-Lipschitz and the
component initial gaps to the finite infimum values are bounded by `Delta`. -/
def SmoothnessAssumption (S : Setup Node E) (L Delta : Real) : Prop :=
  SOptLib.FiniteComponentSmoothnessAssumption (Set.univ : Set E)
    S.localObjective (localGradient S) S.x0 (fun _ : Node => L) Delta

/-- Under Assumption 4's component-gradient realization, the paper objective's
Mathlib gradient is the finite average of component gradients.  This is the
bridge from the earlier surrogate `n^{-1} sum_i grad f_i` representation to
the Theorem 2 stationarity certificate `grad f`. -/
theorem objectiveGradient_eq_fullGradient
    {L Delta : Real} (hsmooth : SmoothnessAssumption S L Delta) (x : E) :
    objectiveGradient S x = fullGradient S x := by
  have hgrad : forall i y, HasGradientAt (S.localObjective i) (localGradient S i y) y :=
    hsmooth.1.1
  unfold objectiveGradient objective fullGradient nodeAverage localGradient
  rw [show (fun z : E => SOptLib.finiteUniformAverage (fun i => S.localObjective i z)) =
      SOptLib.finiteUniformAverage S.localObjective by
    funext z
    simp [SOptLib.finiteUniformAverage]]
  exact SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
    S.localObjective (fun i y => gradient (S.localObjective i) y) x (fun i => hgrad i x)

private theorem objective_initial_gap_le_delta
    {L Delta : Real} (hsmooth : SmoothnessAssumption S L Delta) :
    objective S S.x0 - nodeAverage (fun i => componentInfimumValue S i) <= Delta := by
  classical
  rcases hsmooth with ⟨_hfamily, _hDelta_nonneg, _hwell, hgap⟩
  have hsum_le :
      Finset.univ.sum
          (fun i => S.localObjective i S.x0 - componentInfimumValue S i) <=
        Finset.univ.sum (fun _i : Node => Delta) := by
    exact Finset.sum_le_sum (fun i _hi => hgap i)
  have hinv_nonneg : 0 <= invNodeCount Node := by
    unfold invNodeCount
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
  have hcard_ne : (Fintype.card Node : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Node))
  calc
    objective S S.x0 - nodeAverage (fun i => componentInfimumValue S i)
        =
          invNodeCount Node *
            Finset.univ.sum
              (fun i => S.localObjective i S.x0 - componentInfimumValue S i) := by
          rw [objective, nodeAverage_eq_invNodeCount_smul_sum,
            nodeAverage_eq_invNodeCount_smul_sum]
          simp only [smul_eq_mul]
          rw [← mul_sub, ← Finset.sum_sub_distrib]
    _ <= invNodeCount Node * Finset.univ.sum (fun _i : Node => Delta) := hscaled
    _ = Delta := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold invNodeCount
          field_simp [hcard_ne]

private theorem objective_smooth_quadratic_upper_bound
    {L Delta : Real} (hsmooth : SmoothnessAssumption S L Delta) (x y : E) :
    objective S y <=
      objective S x + inner Real (fullGradient S x) (y - x) +
        (L / 2) * ‖y - x‖ ^ (2 : Nat) := by
  classical
  rcases hsmooth with ⟨hfamily, _hDelta_nonneg, _hwell, _hgap⟩
  have hgrad : forall i z, HasGradientAt (S.localObjective i) (localGradient S i z) z :=
    hfamily.1
  have hlip : forall i z w,
      ‖localGradient S i z - localGradient S i w‖ <= L * ‖z - w‖ :=
    hfamily.2.2
  have hL_average :
      L = (Fintype.card Node : Real)⁻¹ *
        Finset.univ.sum (fun _i : Node => L) := by
    have hcard_ne : (Fintype.card Node : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Node))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard_ne]
  have hsmooth_avg :=
    SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
      (X := Set.univ) (F := S.localObjective)
      (gradF := fun i z => localGradient S i z) (Lcomp := fun _i : Node => L) (L := L)
      convex_univ hL_average
      (fun i z _hz => hgrad i z)
      (fun i z w _hz _hw => hlip i z w)
      (x := x) (y := y) (by simp) (by simp)
  simpa [objective, fullGradient, nodeAverage] using hsmooth_avg

/-- The theorem-level PULM mixing-rate assumption
`||W^(k,r)-E_n||_2 <= C_W beta_W^r`. -/
def UniformPULMMixingRate (S : Setup Node E) (C_W beta_W : Real) : Prop :=
  FiniteNetwork.UniformGeometricMixingRate (matrixTwoNorm (Node := Node))
    (fun k r i j => pullMemoryMatrix S k r i j) (averageMatrix Node) C_W beta_W

private theorem uniformPULMMixingRate_matrixVecMul_bound
    {C_W beta_W : Real} (hmix : UniformPULMMixingRate S C_W beta_W)
    (k r : Nat) (x : Node -> Real) :
    ‖matrixVecMul
        (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) x‖ <=
      C_W * beta_W ^ r * ‖x‖ := by
  have hbase :=
    matrixVecMul_norm_le_matrixTwoNorm_mul_norm
      (A := fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) x
  have hrate :
      matrixTwoNorm
          (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) <=
        C_W * beta_W ^ r := hmix.2.2.2 k r
  have hscale := mul_le_mul_of_nonneg_right hrate (norm_nonneg x)
  linarith

private theorem uniformPULMMixingRate_matrixStateMul_bound
    {C_W beta_W : Real} (hmix : UniformPULMMixingRate S C_W beta_W)
    (k r : Nat) (y : NodeState Node E) :
    ‖matrixStateMul
        (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) y‖ <=
      C_W * beta_W ^ r * ‖y‖ := by
  have hbase :=
    matrixStateMul_norm_le_matrixTwoNorm_mul_norm
      (A := fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) y
  have hrate :
      matrixTwoNorm
          (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) <=
        C_W * beta_W ^ r := hmix.2.2.2 k r
  have hscale := mul_le_mul_of_nonneg_right hrate (norm_nonneg y)
  linarith

private theorem memoryCorrection_abs_le_pullMemoryMatrix_rate
    {C_W beta_W : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hmix : UniformPULMMixingRate S C_W beta_W)
    (k r : Nat) (i : Node) :
    |memoryCorrection S k r (pullMemoryMatrix S k r) i| <= C_W * beta_W ^ r := by
  classical
  let t := communicationTime S k r
  let a : Node -> Real := fun j => S.mixing t i j
  let err : Node -> Real :=
    fun j => pullMemoryMatrix S k r j i - invNodeCount Node
  have hrow_t : (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node := hrow t
  have ha_nonneg : forall j, 0 <= a j := by
    intro j
    exact hrow_t.1 i j
  have ha_sum : Finset.univ.sum a = 1 := by
    exact _root_.Matrix.sum_row_of_mem_rowStochastic hrow_t i
  have hrate_nonneg : 0 <= C_W * beta_W ^ r := by
    exact mul_nonneg (le_of_lt hmix.1) (pow_nonneg hmix.2.1 r)
  have hentry : forall j, |err j| <= C_W * beta_W ^ r := by
    intro j
    have hrow_abs :
        Finset.univ.sum
            (fun ell =>
              |(fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q)
                  j ell|) <=
          matrixTwoNorm
            (fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q) := by
      exact matrix_row_abs_sum_le_matrixTwoNorm
        (A := fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q) j
    have hrate :
        matrixTwoNorm
            (fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q) <=
          C_W * beta_W ^ r := hmix.2.2.2 k r
    have hsingle :
        |(fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q) j i| <=
          Finset.univ.sum
            (fun ell =>
              |(fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q)
                  j ell|) := by
      exact Finset.single_le_sum
        (fun ell _ => abs_nonneg
          ((fun p q => pullMemoryMatrix S k r p q - averageMatrix Node p q) j ell))
        (Finset.mem_univ i)
    simpa [err, averageMatrix] using le_trans hsingle (le_trans hrow_abs hrate)
  have hrewrite :
      memoryCorrection S k r (pullMemoryMatrix S k r) i =
        Finset.univ.sum (fun j => a j * err j) := by
    unfold memoryCorrection gossipMemory
    change
      Finset.univ.sum (fun j => a j * pullMemoryMatrix S k r j i) -
          invNodeCount Node =
        Finset.univ.sum (fun j => a j * err j)
    calc
      Finset.univ.sum (fun j => a j * pullMemoryMatrix S k r j i) -
          invNodeCount Node =
        Finset.univ.sum (fun j => a j * pullMemoryMatrix S k r j i) -
          (Finset.univ.sum a) * invNodeCount Node := by
            rw [ha_sum, one_mul]
      _ =
        Finset.univ.sum (fun j => a j * pullMemoryMatrix S k r j i) -
          Finset.univ.sum (fun j => a j * invNodeCount Node) := by
            rw [Finset.sum_mul]
      _ =
        Finset.univ.sum
          (fun j => a j * pullMemoryMatrix S k r j i - a j * invNodeCount Node) := by
            rw [Finset.sum_sub_distrib]
      _ = Finset.univ.sum (fun j => a j * err j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [err]
            ring
  rw [hrewrite]
  calc
    |Finset.univ.sum (fun j => a j * err j)| <=
        Finset.univ.sum (fun j => |a j * err j|) := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun j => a j * |err j|) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [abs_mul, abs_of_nonneg (ha_nonneg j)]
    _ <= Finset.univ.sum (fun j => a j * (C_W * beta_W ^ r)) := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact mul_le_mul_of_nonneg_left (hentry j) (ha_nonneg j)
    _ = (Finset.univ.sum a) * (C_W * beta_W ^ r) := by
          rw [Finset.sum_mul]
    _ = C_W * beta_W ^ r := by
          rw [ha_sum, one_mul]

private theorem scaled_innerGradientMatrix_update_decomposition
    (k r : Nat) (y : NodeState Node E) :
    (S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y =
      (S.gamma : Real) •
          matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y +
        fun i => memoryCorrection S k r (pullMemoryMatrix S k r) i • y i := by
  rw [innerGradientMatrix_succ]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [matrixStateMul_add_basisRow_apply]
  rw [smul_add]
  congr 1
  unfold memoryCorrection
  rw [smul_smul]
  congr 1
  have hgamma_ne : (S.gamma : Real) ≠ 0 := ne_of_gt S.gamma.property
  field_simp [hgamma_ne]

private theorem memoryCorrection_state_norm_le
    {C_W beta_W : Real}
    (hmemory_correction_bound :
      forall k r i,
        |memoryCorrection S k r (pullMemoryMatrix S k r) i| <= C_W * beta_W ^ r)
    (hrate_nonneg : forall r, 0 <= C_W * beta_W ^ r)
    (k r : Nat) (y : NodeState Node E) :
    ‖(fun i => memoryCorrection S k r (pullMemoryMatrix S k r) i • y i)‖ <=
      C_W * beta_W ^ r * ‖y‖ := by
  classical
  have htarget_nonneg : 0 <= C_W * beta_W ^ r * ‖y‖ :=
    mul_nonneg (hrate_nonneg r) (norm_nonneg y)
  rw [pi_norm_le_iff_of_nonneg htarget_nonneg]
  intro i
  calc
    ‖memoryCorrection S k r (pullMemoryMatrix S k r) i • y i‖ =
        |memoryCorrection S k r (pullMemoryMatrix S k r) i| * ‖y i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ <= (C_W * beta_W ^ r) * ‖y‖ := by
          exact mul_le_mul (hmemory_correction_bound k r i) (norm_le_pi_norm (f := y) i)
            (norm_nonneg (y i)) (hrate_nonneg r)

private theorem innerParameterMatrix_sub_pullMemoryMatrix_succ_state_norm_le
    {C_W beta_W : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hmemory_correction_bound :
      forall k r i,
        |memoryCorrection S k r (pullMemoryMatrix S k r) i| <= C_W * beta_W ^ r)
    (hrate_nonneg : forall r, 0 <= C_W * beta_W ^ r)
    (k r : Nat) (x : NodeState Node E) :
    ‖matrixStateMul
        (fun i j =>
          innerParameterMatrix S k (r + 1) i j - pullMemoryMatrix S k (r + 1) i j) x‖ <=
      ‖matrixStateMul
          (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) x‖ +
        C_W * beta_W ^ r * ‖x‖ := by
  rw [innerParameterMatrix_sub_pullMemoryMatrix_succ_state (S := S) k r x]
  calc
    ‖matrixStateMul
          (gossipMemory S k r
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j)) x +
        (fun i => memoryCorrection S k r (pullMemoryMatrix S k r) i • x i)‖
        <=
      ‖matrixStateMul
          (gossipMemory S k r
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j)) x‖ +
        ‖(fun i => memoryCorrection S k r (pullMemoryMatrix S k r) i • x i)‖ := by
          exact norm_add_le _ _
    _ <=
      ‖matrixStateMul
          (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) x‖ +
        C_W * beta_W ^ r * ‖x‖ := by
          exact add_le_add
            (by
              rw [← gossipState_memory_apply (S := S) k r
                (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) x]
              exact gossipState_norm_le_of_rowStochastic (S := S) hrow k r
                (matrixStateMul
                  (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) x))
            (memoryCorrection_state_norm_le (S := S)
              hmemory_correction_bound hrate_nonneg k r x)

private theorem innerParameterMatrix_sub_pullMemoryMatrix_state_norm_le_geometric_sum
    {C_W beta_W : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hmemory_correction_bound :
      forall k r i,
        |memoryCorrection S k r (pullMemoryMatrix S k r) i| <= C_W * beta_W ^ r)
    (hrate_nonneg : forall r, 0 <= C_W * beta_W ^ r)
    (k r : Nat) (x : NodeState Node E) :
    ‖matrixStateMul
        (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) x‖ <=
      ((Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖x‖ := by
  induction r with
  | zero =>
      rw [innerParameterMatrix_zero, pullMemoryMatrix_zero]
      have hzero : matrixStateMul (fun i j : Node => (0 : Real)) x = 0 := by
        funext i
        simp [matrixStateMul]
      simp [hzero]
  | succ r ih =>
      have hstep :=
        innerParameterMatrix_sub_pullMemoryMatrix_succ_state_norm_le (S := S)
          hrow hmemory_correction_bound hrate_nonneg k r x
      calc
        ‖matrixStateMul
            (fun i j =>
              innerParameterMatrix S k (Nat.succ r) i j -
                pullMemoryMatrix S k (Nat.succ r) i j) x‖
            <=
          ‖matrixStateMul
              (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) x‖ +
            C_W * beta_W ^ r * ‖x‖ := hstep
        _ <=
          ((Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖x‖ +
            C_W * beta_W ^ r * ‖x‖ := by
              exact add_le_add ih (le_refl _)
        _ =
          ((Finset.range (Nat.succ r)).sum (fun q => C_W * beta_W ^ q)) * ‖x‖ := by
              rw [Finset.sum_range_succ]
              ring

private theorem innerParameterMatrix_projected_norm_le_pull_rate_plus_memory_gap
    {C_W beta_W : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hmatrix_state_rate :
      forall k r (y : NodeState Node E),
        ‖matrixStateMul
            (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) y‖ <=
          C_W * beta_W ^ r * ‖y‖)
    (hinner_parameter_memory_gap_sum :
      forall k r (y : NodeState Node E),
        ‖matrixStateMul
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) y‖ <=
          ((Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖y‖)
    (k r : Nat) (x : NodeState Node E) :
    ‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ <=
      2 *
        ((C_W * beta_W ^ r + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
          ‖consensusError S x‖) := by
  let z : NodeState Node E := consensusError S x
  have hrow_inner : (innerParameterMatrix S k r) ∈ _root_.Matrix.rowStochastic Real Node :=
    innerParameterMatrix_rowStochastic (S := S) hrow k r
  have hreduce :
      consensusError S (matrixStateMul (innerParameterMatrix S k r) x) =
        consensusError S (matrixStateMul (innerParameterMatrix S k r) z) := by
    simpa [z] using
      consensusError_matrixStateMul_eq_consensusError_matrixStateMul_consensusError
        (S := S) (innerParameterMatrix S k r) hrow_inner x
  have hzdev :
      matrixStateMul (innerParameterMatrix S k r) z =
        matrixStateMul
          (fun i j => innerParameterMatrix S k r i j - averageMatrix Node i j) z := by
    have h :=
      matrixStateMul_sub_average_eq_matrixStateMul_consensusError (S := S)
        (innerParameterMatrix S k r) hrow_inner z
    rw [h, consensusError_idempotent]
  have hsplit_eq :
      matrixStateMul
          (fun i j => innerParameterMatrix S k r i j - averageMatrix Node i j) z =
        matrixStateMul
            (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) z +
          matrixStateMul
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) z := by
    funext i
    unfold matrixStateMul
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← add_smul]
    congr 1
    ring
  have hinner_norm :
      ‖matrixStateMul (innerParameterMatrix S k r) z‖ <=
        (C_W * beta_W ^ r +
            (Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖z‖ := by
    rw [hzdev, hsplit_eq]
    calc
      ‖matrixStateMul
            (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) z +
          matrixStateMul
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) z‖
          <=
        ‖matrixStateMul
            (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) z‖ +
          ‖matrixStateMul
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) z‖ := by
            exact norm_add_le _ _
      _ <=
        C_W * beta_W ^ r * ‖z‖ +
          ((Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖z‖ := by
            exact add_le_add (hmatrix_state_rate k r z)
              (hinner_parameter_memory_gap_sum k r z)
      _ =
        (C_W * beta_W ^ r +
            (Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖z‖ := by
            ring
  calc
    ‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ =
        ‖consensusError S (matrixStateMul (innerParameterMatrix S k r) z)‖ := by
          rw [hreduce]
    _ <= 2 * ‖matrixStateMul (innerParameterMatrix S k r) z‖ :=
          consensusError_norm_le_two_norm (S := S)
            (matrixStateMul (innerParameterMatrix S k r) z)
    _ <=
        2 *
          ((C_W * beta_W ^ r + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
            ‖z‖) := by
          exact mul_le_mul_of_nonneg_left hinner_norm (by norm_num)
    _ =
        2 *
          ((C_W * beta_W ^ r + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
            ‖consensusError S x‖) := by
          rfl

private theorem scaled_innerGradientMatrix_update_error_norm_le
    {C_W beta_W : Real}
    (hmemory_correction_bound :
      forall k r i,
        |memoryCorrection S k r (pullMemoryMatrix S k r) i| <= C_W * beta_W ^ r)
    (hrate_nonneg : forall r, 0 <= C_W * beta_W ^ r)
    (k r : Nat) (y : NodeState Node E) :
    ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y -
        (S.gamma : Real) • matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y‖ <=
      C_W * beta_W ^ r * ‖y‖ := by
  rw [scaled_innerGradientMatrix_update_decomposition (S := S) k r y]
  simpa [add_sub_cancel_left] using
    memoryCorrection_state_norm_le (S := S) hmemory_correction_bound hrate_nonneg k r y

private theorem scaled_innerGradientMatrix_norm_le_initial_gamma_plus_memory_gap
    {C_W beta_W : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hscaled_gradient_update_error_bound :
      forall k r (y : NodeState Node E),
        ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y -
            (S.gamma : Real) •
              matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y‖ <=
          C_W * beta_W ^ r * ‖y‖)
    (k r : Nat) (y : NodeState Node E) :
    ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y‖ <=
      ((S.gamma : Real) + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) * ‖y‖ := by
  induction r with
  | zero =>
      rw [innerGradientMatrix_zero, matrixStateMul_initialMemoryMatrix]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt S.gamma.property)]
      simp
  | succ r ih =>
      let current : NodeState Node E :=
        (S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y
      let mixed : NodeState Node E :=
        (S.gamma : Real) • matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y
      let next : NodeState Node E :=
        (S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y
      have hmixed_eq : mixed = gossipState S k r current := by
        dsimp [mixed, current]
        rw [← gossipState_memory_apply (S := S) k r (innerGradientMatrix S k r) y]
        rw [← gossipState_smul (S := S) k r (S.gamma : Real)
          (matrixStateMul (innerGradientMatrix S k r) y)]
      have hmixed_norm : ‖mixed‖ <= ‖current‖ := by
        rw [hmixed_eq]
        exact gossipState_norm_le_of_rowStochastic (S := S) hrow k r current
      have hstep :
          ‖next‖ <= ‖mixed‖ + C_W * beta_W ^ r * ‖y‖ := by
        have hnext_decomp : next = mixed + (next - mixed) := by
          abel
        calc
          ‖next‖ = ‖mixed + (next - mixed)‖ := by
            exact congrArg norm hnext_decomp
          _ <= ‖mixed‖ + ‖next - mixed‖ := norm_add_le _ _
          _ <= ‖mixed‖ + C_W * beta_W ^ r * ‖y‖ := by
            exact add_le_add (le_refl ‖mixed‖)
              (by
                change
                  ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y -
                      (S.gamma : Real) •
                        matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y‖ <=
                    C_W * beta_W ^ r * ‖y‖
                exact hscaled_gradient_update_error_bound k r y)
      have ih_current :
          ‖current‖ <=
            ((S.gamma : Real) + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
              ‖y‖ := by
        simpa [current] using ih
      calc
        ‖next‖ <= ‖mixed‖ + C_W * beta_W ^ r * ‖y‖ := hstep
        _ <= ‖current‖ + C_W * beta_W ^ r * ‖y‖ := by
          exact add_le_add hmixed_norm (le_refl _)
        _ <=
            ((S.gamma : Real) + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
                ‖y‖ +
              C_W * beta_W ^ r * ‖y‖ := by
          exact add_le_add ih_current (le_refl _)
        _ =
            ((S.gamma : Real) + (Finset.range (r + 1)).sum (fun q => C_W * beta_W ^ q)) *
              ‖y‖ := by
          rw [Finset.sum_range_succ]
          ring

private theorem projected_scaled_innerGradientMatrix_norm_le_initial_gamma_plus_memory_gap
    {C_W beta_W : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hscaled_gradient_update_error_bound :
      forall k r (y : NodeState Node E),
        ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y -
            (S.gamma : Real) •
              matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y‖ <=
          C_W * beta_W ^ r * ‖y‖)
    (k r : Nat) (y : NodeState Node E) :
    ‖consensusError S
        ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)‖ <=
      2 *
        (((S.gamma : Real) + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
          ‖y‖) := by
  calc
    ‖consensusError S
        ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)‖ <=
        2 * ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y‖ :=
          consensusError_norm_le_two_norm (S := S)
            ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)
    _ <=
        2 *
          (((S.gamma : Real) + (Finset.range r).sum (fun q => C_W * beta_W ^ q)) *
            ‖y‖) := by
          exact mul_le_mul_of_nonneg_left
            (scaled_innerGradientMatrix_norm_le_initial_gamma_plus_memory_gap (S := S)
              hrow hscaled_gradient_update_error_bound k r y)
            (by norm_num)

/-- The source-stage Appendix-D A-side projected rate that Lemma 5 uses after
equation (20).  This is an internal proof target, not an assumption: the
paper's Theorem 2 states only the PULM memory-matrix rate for `W`, while the
Appendix D proof locally uses a separate projected rate for
`A^(k)-A_infty^(k)`. -/
private def AppendixDProjectedParameterRate
    (S : Setup Node E) (C beta : Real) : Prop :=
  forall k r (x : NodeState Node E),
    ‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ <=
      C * beta ^ r * ‖consensusError S x‖

/-- The source-stage Appendix-D M-side projected rate that Lemma 5 uses after
equation (20).  This names the separate unprinted bridge from the actual
gamma-scaled Lean object to the paper's `M^(k)-E_n` projected operator. -/
private def AppendixDProjectedGradientRate
    (S : Setup Node E) (C beta : Real) : Prop :=
  forall k r (y : NodeState Node E),
    ‖consensusError S
        ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)‖ <=
      (S.gamma : Real) * C * beta ^ r * ‖y‖

/-- The source-stage Appendix-D projected rates that Lemma 5 uses after
equation (20), bundled only for consumers that need both sides. -/
private def AppendixDProjectedAMRate
    (S : Setup Node E) (C beta : Real) : Prop :=
  AppendixDProjectedParameterRate S C beta /\
    AppendixDProjectedGradientRate S C beta

/-- Separate-constant Appendix-D projected-rate interface.

Appendix D's Lemma 5 uses parameter-side constants `C_A,beta_A` and M-side
constants `C_M,beta_M`.  This private diagnostic interface records that source
granularity explicitly; it is not part of Theorem 2's public assumptions. -/
private def AppendixDSeparateProjectedAMRate
    (S : Setup Node E) (C_A beta_A C_M beta_M : Real) : Prop :=
  AppendixDProjectedParameterRate S C_A beta_A /\
    AppendixDProjectedGradientRate S C_M beta_M

/-- A family of source-stage limiting matrices `A_infty^(k)` for Appendix D.
The source proof uses this object inside `(I - E_n)(A^(k)-A_infty^(k))`.
It is indexed only by the outer iteration: allowing the limit to vary with the
inner-round counter would be a surrogate for the product-limit object used in
the paper.  It is kept private because Theorem 2 does not state it as setup
data. -/
abbrev AppendixDParameterLimitFamily (Node : Type*) [Fintype Node] :=
  Nat -> _root_.Matrix Node Node Real

/-- The projected parameter operator `(I - E_n)(A^(k,r)-A_infty^(k))`
appearing in Appendix D equation (20). -/
private def appendixDProjectedParameterMatrix
    (S : Setup Node E) (Ainf : AppendixDParameterLimitFamily Node)
    (k r : Nat) : _root_.Matrix Node Node Real :=
  matrixMul (consensusProjectionMatrix Node)
    (matrixSub (innerParameterMatrix S k r) (Ainf k))

/-- The projected gradient operator `(I - E_n)(gamma M^(k,r)-E_n)`.
The factor `gamma` is included because the Lean decomposition stores
`innerGradientMatrix` in the paper's `-gamma * M g` form. -/
private def appendixDProjectedGradientMatrix
    (S : Setup Node E) (k r : Nat) : _root_.Matrix Node Node Real :=
  matrixMul (consensusProjectionMatrix Node)
    (matrixSub (matrixScale (S.gamma : Real) (innerGradientMatrix S k r))
      (averageMatrix Node))

/-- Source-stage bridge asserting that the chosen `A_infty` is killed by
`I - E_n` and that the paper's projected A-rate holds for the actual
`innerParameterMatrix`.  This is the missing private object-model correction
target, not a public theorem assumption. -/
def AppendixDParameterProjectionBridge
    (S : Setup Node E) (C beta : Real)
    (Ainf : AppendixDParameterLimitFamily Node) : Prop :=
  (forall k i j,
    matrixMul (consensusProjectionMatrix Node) (Ainf k) i j = 0) /\
    forall k r,
      matrixTwoNorm (appendixDProjectedParameterMatrix S Ainf k r) <=
        C * beta ^ r

/-- Source-stage bridge for the paper's projected M-rate.  It names the
operator `(I - E_n)(gamma M^(k,r)-E_n)` rather than the Lean endpoint
`innerGradientMatrix` by itself. -/
def AppendixDGradientProjectionBridge
    (S : Setup Node E) (C beta : Real) : Prop :=
  forall k r,
    matrixTwoNorm (appendixDProjectedGradientMatrix S k r) <=
      (S.gamma : Real) * C * beta ^ r

/-- The M-side constant forced by the actual Lean identity
`gamma M = (gamma + 1) A - W`.

If the A-side product limit has constant `C_A` and the PULM memory matrix has
constant `C_W` with the same geometric rate, then the triangle route gives the
paper-shaped M bridge only with this larger constant.  This is a private
source-boundary diagnostic; Theorem 2 does not state this separate Appendix-D
constant. -/
private def appendixDForcedMConstant
    (S : Setup Node E) (C_A C_W : Real) : Real :=
  (((S.gamma : Real) + 1) * C_A + C_W) / (S.gamma : Real)

/-- Corrected private M-side projection bridge for the actual Lean objects.

The right-hand side is written in the paper's `gamma * C_M * beta^r` form, but
`C_M` is the forced diagnostic constant above, not Theorem 2's `C_W`. -/
private def AppendixDForcedGradientProjectionBridge
    (S : Setup Node E) (C_A C_W beta : Real) : Prop :=
  forall k r,
    matrixTwoNorm (appendixDProjectedGradientMatrix S k r) <=
      (S.gamma : Real) * appendixDForcedMConstant S C_A C_W * beta ^ r

/-- Same-constant mismatch forced by the actual M identity.

When the A-side and W-side constants are both `C`, the corrected private M
constant is strictly larger than `C`.  Thus the active same-`C_W` Appendix-D M
bridge cannot be treated as a routine consequence of the real Lean recursion. -/
private theorem appendixD_forced_M_constant_strictly_exceeds_same_constant
    {C : Real} (hC : 0 < C) :
    C < appendixDForcedMConstant S C C := by
  unfold appendixDForcedMConstant
  have hgamma_pos : 0 < (S.gamma : Real) := S.gamma.property
  rw [lt_div_iff₀ hgamma_pos]
  nlinarith

private theorem appendixD_forced_M_constant_not_same_constant
    {C : Real} (hC : 0 < C) :
    ¬ appendixDForcedMConstant S C C <= C := by
  exact not_le_of_gt
    (appendixD_forced_M_constant_strictly_exceeds_same_constant (S := S) hC)

/-- Source-boundary diagnostic for Theorem 2's same-constant Appendix-D route.

The paper states only a `W`-matrix rate with constant `C_W`.  For the actual
Lean `innerGradientMatrix`, the corrected M-side constant forced by
`gamma M = (gamma + 1) A - W` cannot be specialized back to the same constant.
Keeping this as a named private proposition makes the public theorem's
remaining source-boundary obligation explicit without adding any source-facing
hypothesis. -/
private def Theorem2SameConstantAppendixDSourceBoundary
    (S : Setup Node E) (C : Real) : Prop :=
  ¬ appendixDForcedMConstant S C C <= C

private theorem theorem2_same_constant_appendixD_source_boundary
    {C beta : Real} (hmix : UniformPULMMixingRate S C beta) :
    Theorem2SameConstantAppendixDSourceBoundary S C := by
  exact appendixD_forced_M_constant_not_same_constant (S := S) hmix.1

private theorem appendixDProjectedParameterMatrix_apply
    (Ainf : AppendixDParameterLimitFamily Node)
    (hkill :
      forall i j,
        matrixMul (consensusProjectionMatrix Node) (Ainf k) i j = 0)
    (x : NodeState Node E) :
    matrixStateMul (appendixDProjectedParameterMatrix S Ainf k r) x =
      consensusError S (matrixStateMul (innerParameterMatrix S k r) x) := by
  rw [appendixDProjectedParameterMatrix, matrixStateMul_matrixMul]
  have hsplit :
      matrixStateMul
          (matrixSub (innerParameterMatrix S k r) (Ainf k)) x =
        matrixStateMul (innerParameterMatrix S k r) x -
          matrixStateMul (Ainf k) x := by
    funext i
    unfold matrixStateMul matrixSub
    simp only [Pi.sub_apply, sub_smul]
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  have hproj_sub :
      matrixStateMul (consensusProjectionMatrix Node)
          (matrixStateMul (innerParameterMatrix S k r) x -
            matrixStateMul (Ainf k) x) =
        matrixStateMul (consensusProjectionMatrix Node)
            (matrixStateMul (innerParameterMatrix S k r) x) -
          matrixStateMul (consensusProjectionMatrix Node)
            (matrixStateMul (Ainf k) x) := by
    funext i
    unfold matrixStateMul
    simp only [Pi.sub_apply, smul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hproj_sub]
  have hkill_state :
      matrixStateMul (consensusProjectionMatrix Node)
          (matrixStateMul (Ainf k) x) = 0 := by
    rw [← matrixStateMul_matrixMul]
    funext i
    unfold matrixStateMul
    simp [hkill]
  rw [hkill_state, sub_zero]
  exact matrixStateMul_consensusProjectionMatrix_eq_consensusError (S := S)
    (matrixStateMul (innerParameterMatrix S k r) x)

private theorem appendixDProjectedGradientMatrix_apply
    (y : NodeState Node E) :
    matrixStateMul (appendixDProjectedGradientMatrix S k r) y =
      consensusError S
        ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y) := by
  rw [appendixDProjectedGradientMatrix, matrixStateMul_matrixMul]
  have hsplit :
      matrixStateMul
          (matrixSub (matrixScale (S.gamma : Real) (innerGradientMatrix S k r))
            (averageMatrix Node)) y =
        (S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y -
          matrixStateMul (averageMatrix Node) y := by
    funext i
    unfold matrixStateMul matrixSub matrixScale
    simp only [Pi.sub_apply, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
    rfl
  rw [hsplit]
  have hproj_avg :
      matrixStateMul (consensusProjectionMatrix Node)
          (matrixStateMul (averageMatrix Node) y) = 0 := by
    rw [matrixStateMul_averageMatrix_eq_consensusState (S := S) y]
    rw [matrixStateMul_consensusProjectionMatrix_eq_consensusError (S := S)]
    exact consensusError_consensusState_zero (S := S) y
  have hproj_sub :
      matrixStateMul (consensusProjectionMatrix Node)
          ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y -
            matrixStateMul (averageMatrix Node) y) =
        matrixStateMul (consensusProjectionMatrix Node)
            ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y) -
          matrixStateMul (consensusProjectionMatrix Node)
            (matrixStateMul (averageMatrix Node) y) := by
    funext i
    unfold matrixStateMul
    simp only [Pi.sub_apply, smul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hproj_sub, hproj_avg, sub_zero]
  exact matrixStateMul_consensusProjectionMatrix_eq_consensusError (S := S)
    ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)

/-- If the paper's projected `A_infty` bridge is available, it supplies the
A-side rate required by the active Appendix-D recurrence route. -/
private theorem appendixD_projected_parameter_rate_from_A_infty_bridge
    {C beta : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hbridge : AppendixDParameterProjectionBridge S C beta Ainf) :
    AppendixDProjectedParameterRate S C beta := by
  intro k r x
  let z : NodeState Node E := consensusError S x
  have hrow_inner : (innerParameterMatrix S k r) ∈ _root_.Matrix.rowStochastic Real Node :=
    innerParameterMatrix_rowStochastic (S := S) hrow k r
  have hreduce :
      consensusError S (matrixStateMul (innerParameterMatrix S k r) x) =
        consensusError S (matrixStateMul (innerParameterMatrix S k r) z) := by
    simpa [z] using
      consensusError_matrixStateMul_eq_consensusError_matrixStateMul_consensusError
        (S := S) (innerParameterMatrix S k r) hrow_inner x
  have happly :
      matrixStateMul (appendixDProjectedParameterMatrix S Ainf k r) z =
        consensusError S (matrixStateMul (innerParameterMatrix S k r) z) :=
    appendixDProjectedParameterMatrix_apply (S := S) (k := k) (r := r) Ainf
      (fun i j => hbridge.1 k i j) z
  calc
    ‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ =
        ‖matrixStateMul (appendixDProjectedParameterMatrix S Ainf k r) z‖ := by
          rw [hreduce, ← happly]
    _ <= matrixTwoNorm (appendixDProjectedParameterMatrix S Ainf k r) * ‖z‖ :=
          matrixStateMul_norm_le_matrixTwoNorm_mul_norm
            (A := appendixDProjectedParameterMatrix S Ainf k r) z
    _ <= C * beta ^ r * ‖z‖ := by
          exact mul_le_mul_of_nonneg_right (hbridge.2 k r) (norm_nonneg z)
    _ = C * beta ^ r * ‖consensusError S x‖ := rfl

/-- If the paper's projected `M^(k)-E_n` bridge is available, it supplies the
M-side rate required by the active Appendix-D recurrence route. -/
private theorem appendixD_projected_gradient_rate_from_M_minus_average_bridge
    {C beta : Real}
    (hbridge : AppendixDGradientProjectionBridge S C beta) :
    AppendixDProjectedGradientRate S C beta := by
  intro k r y
  have happly :
      matrixStateMul (appendixDProjectedGradientMatrix S k r) y =
        consensusError S
          ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y) :=
    appendixDProjectedGradientMatrix_apply (S := S) (k := k) (r := r) y
  calc
    ‖consensusError S
        ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)‖ =
        ‖matrixStateMul (appendixDProjectedGradientMatrix S k r) y‖ := by
          rw [← happly]
    _ <= matrixTwoNorm (appendixDProjectedGradientMatrix S k r) * ‖y‖ :=
          matrixStateMul_norm_le_matrixTwoNorm_mul_norm
            (A := appendixDProjectedGradientMatrix S k r) y
    _ <= ((S.gamma : Real) * C * beta ^ r) * ‖y‖ := by
          exact mul_le_mul_of_nonneg_right (hbridge k r) (norm_nonneg y)
    _ = (S.gamma : Real) * C * beta ^ r * ‖y‖ := by ring

private theorem appendixD_projected_gradient_rate_from_forced_bridge
    {C_A C_W beta : Real}
    (hbridge : AppendixDForcedGradientProjectionBridge S C_A C_W beta) :
    AppendixDProjectedGradientRate S (appendixDForcedMConstant S C_A C_W) beta := by
  have hold :
      AppendixDGradientProjectionBridge S
        (appendixDForcedMConstant S C_A C_W) beta := by
    intro k r
    exact hbridge k r
  exact appendixD_projected_gradient_rate_from_M_minus_average_bridge
    (S := S) hold

private theorem appendixD_gradient_projection_bridge_of_forced_bridge_and_constant_match
    {C_A C beta : Real} (hbeta : 0 <= beta)
    (hforced : AppendixDForcedGradientProjectionBridge S C_A C beta)
    (hconstant_match : appendixDForcedMConstant S C_A C <= C) :
    AppendixDGradientProjectionBridge S C beta := by
  intro k r
  have hbase :
      (S.gamma : Real) * appendixDForcedMConstant S C_A C <=
        (S.gamma : Real) * C := by
    exact mul_le_mul_of_nonneg_left hconstant_match (le_of_lt S.gamma.property)
  calc
    matrixTwoNorm (appendixDProjectedGradientMatrix S k r) <=
        (S.gamma : Real) * appendixDForcedMConstant S C_A C * beta ^ r :=
          hforced k r
    _ <= (S.gamma : Real) * C * beta ^ r := by
          exact mul_le_mul_of_nonneg_right hbase (pow_nonneg hbeta r)

private theorem appendixD_projected_AM_rate_from_source_projection_bridges
    {C beta : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hA : AppendixDParameterProjectionBridge S C beta Ainf)
    (hM : AppendixDGradientProjectionBridge S C beta) :
    AppendixDProjectedAMRate S C beta := by
  exact ⟨appendixD_projected_parameter_rate_from_A_infty_bridge
      (S := S) Ainf hrow hA,
    appendixD_projected_gradient_rate_from_M_minus_average_bridge
      (S := S) hM⟩

private theorem appendixD_separate_projected_AM_rate_from_source_projection_bridges
    {C_A beta_A C_M beta_M : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hA : AppendixDParameterProjectionBridge S C_A beta_A Ainf)
    (hM : AppendixDGradientProjectionBridge S C_M beta_M) :
    AppendixDSeparateProjectedAMRate S C_A beta_A C_M beta_M := by
  exact ⟨appendixD_projected_parameter_rate_from_A_infty_bridge
      (S := S) Ainf hrow hA,
    appendixD_projected_gradient_rate_from_M_minus_average_bridge
      (S := S) hM⟩

private theorem appendixD_plus_memory_gap_bound_strictly_exceeds_same_rate
    {C beta N : Real} (hC : 0 < C) (hbeta : 0 <= beta) (hN : 0 < N) (r : Nat) :
    C * beta ^ r * N <
      2 * ((C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q)) * N) := by
  have hpow_nonneg : forall q : Nat, 0 <= beta ^ q := fun q => pow_nonneg hbeta q
  have hterm_nonneg : forall q : Nat, 0 <= C * beta ^ q := by
    intro q
    exact mul_nonneg (le_of_lt hC) (hpow_nonneg q)
  have ha_nonneg : 0 <= C * beta ^ r := hterm_nonneg r
  have hsum_nonneg :
      0 <= (Finset.range r).sum (fun q => C * beta ^ q) := by
    exact Finset.sum_nonneg (fun q _hq => hterm_nonneg q)
  have hsum_pos_or_a_pos :
      0 < C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q) := by
    cases r with
    | zero =>
        simpa using hC
    | succ r =>
        have hzero_mem : 0 ∈ Finset.range (Nat.succ r) := by simp
        have hC_le_sum :
            C <= (Finset.range (Nat.succ r)).sum (fun q => C * beta ^ q) := by
          simpa using
            (Finset.single_le_sum
              (fun q _hq => hterm_nonneg q) hzero_mem)
        have hsum_pos :
            0 < (Finset.range (Nat.succ r)).sum (fun q => C * beta ^ q) :=
          lt_of_lt_of_le hC hC_le_sum
        exact add_pos_of_nonneg_of_pos (hterm_nonneg (Nat.succ r)) hsum_pos
  nlinarith [mul_pos hsum_pos_or_a_pos hN, mul_nonneg ha_nonneg (le_of_lt hN)]

private theorem appendixD_plus_memory_gap_bound_cannot_close_projected_rate
    {C beta N : Real} (hC : 0 < C) (hbeta : 0 <= beta) (hN : 0 < N) (r : Nat) :
    ¬
      2 * ((C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q)) * N) <=
        C * beta ^ r * N := by
  have hlt :=
    appendixD_plus_memory_gap_bound_strictly_exceeds_same_rate
      (C := C) (beta := beta) (N := N) hC hbeta hN r
  exact not_le_of_gt hlt

/-- Same-granularity typed obstruction for the Appendix-D A-side source route.

For the actual Lean object `innerParameterMatrix`, the currently derivable
route reaches only the PULM-rate term plus the accumulated memory-gap sum.
That bound cannot be normalized by scalar arithmetic into the source's
same-rate `C * beta^r` projected estimate whenever the input has nonzero
consensus error.  A proof of `AppendixDProjectedAMRate` therefore needs a
new source-object bridge for `A^(k)-A_infty^(k)`, not more algebra on this
plus-memory-gap estimate. -/
private theorem appendixD_parameter_rate_attempt_reaches_arithmetic_obstruction
    {C beta : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hmatrix_state_rate :
      forall k r (y : NodeState Node E),
        ‖matrixStateMul
            (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) y‖ <=
          C * beta ^ r * ‖y‖)
    (hinner_parameter_memory_gap_sum :
      forall k r (y : NodeState Node E),
        ‖matrixStateMul
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) y‖ <=
          ((Finset.range r).sum (fun q => C * beta ^ q)) * ‖y‖)
    (hC : 0 < C) (hbeta : 0 <= beta)
    (k r : Nat) (x : NodeState Node E)
    (hx : 0 < ‖consensusError S x‖) :
    (‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ <=
        2 *
          ((C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q)) *
            ‖consensusError S x‖)) /\
      ¬
        2 *
            ((C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q)) *
              ‖consensusError S x‖) <=
          C * beta ^ r * ‖consensusError S x‖ := by
  constructor
  · exact innerParameterMatrix_projected_norm_le_pull_rate_plus_memory_gap
      (S := S) hrow hmatrix_state_rate hinner_parameter_memory_gap_sum k r x
  · exact appendixD_plus_memory_gap_bound_cannot_close_projected_rate
      (C := C) (beta := beta) (N := ‖consensusError S x‖) hC hbeta hx r

/-- Exact-head diagnostic for the missing Appendix-D parameter projection
bridge.

If a genuine product-limit object `A_infty^(k)` satisfying
`AppendixDParameterProjectionBridge` were available, it would immediately give
the A-side projected rate.  The strongest endpoint derivable from the current
Theorem 2 assumptions about the actual Lean objects is instead the PULM
`W`-rate plus the accumulated memory-gap sum, and that scalar endpoint cannot
be compressed to the source same-rate target.  This theorem packages both facts
at the exact bridge head, rather than introducing another arbitrary `Ainf`
existence leaf. -/
private theorem appendixD_parameter_projection_bridge_current_endpoint_obstruction
    {C beta : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hmatrix_state_rate :
      forall k r (y : NodeState Node E),
        ‖matrixStateMul
            (fun i j => pullMemoryMatrix S k r i j - averageMatrix Node i j) y‖ <=
          C * beta ^ r * ‖y‖)
    (hinner_parameter_memory_gap_sum :
      forall k r (y : NodeState Node E),
        ‖matrixStateMul
            (fun i j => innerParameterMatrix S k r i j - pullMemoryMatrix S k r i j) y‖ <=
          ((Finset.range r).sum (fun q => C * beta ^ q)) * ‖y‖)
    (hC : 0 < C) (hbeta : 0 <= beta)
    (k r : Nat) (x : NodeState Node E)
    (hx : 0 < ‖consensusError S x‖) :
    (AppendixDParameterProjectionBridge S C beta Ainf ->
      ‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ <=
        C * beta ^ r * ‖consensusError S x‖) /\
      (‖consensusError S (matrixStateMul (innerParameterMatrix S k r) x)‖ <=
          2 *
            ((C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q)) *
              ‖consensusError S x‖)) /\
        ¬
          2 *
              ((C * beta ^ r + (Finset.range r).sum (fun q => C * beta ^ q)) *
                ‖consensusError S x‖) <=
            C * beta ^ r * ‖consensusError S x‖ := by
  constructor
  · intro hbridge
    exact appendixD_projected_parameter_rate_from_A_infty_bridge
      (S := S) Ainf hrow hbridge k r x
  · exact appendixD_parameter_rate_attempt_reaches_arithmetic_obstruction
      (S := S) hrow hmatrix_state_rate hinner_parameter_memory_gap_sum
      hC hbeta k r x hx

/-- Same-granularity typed endpoint for the Appendix-D M-side source route.

For the actual Lean object `innerGradientMatrix`, the current update semantics
yield a gamma-scaled initial term plus accumulated memory-correction errors.
This is the precise bound available before any unprinted
`M^(k)-E_n` projected-rate bridge. -/
private theorem appendixD_gradient_rate_attempt_reaches_initial_gamma_plus_memory_gap
    {C beta : Real}
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hscaled_gradient_update_error_bound :
      forall k r (y : NodeState Node E),
        ‖(S.gamma : Real) • matrixStateMul (innerGradientMatrix S k (r + 1)) y -
            (S.gamma : Real) •
              matrixStateMul (gossipMemory S k r (innerGradientMatrix S k r)) y‖ <=
          C * beta ^ r * ‖y‖)
    (k r : Nat) (y : NodeState Node E) :
    ‖consensusError S
        ((S.gamma : Real) • matrixStateMul (innerGradientMatrix S k r) y)‖ <=
      2 *
        (((S.gamma : Real) + (Finset.range r).sum (fun q => C * beta ^ q)) *
          ‖y‖) := by
  exact projected_scaled_innerGradientMatrix_norm_le_initial_gamma_plus_memory_gap
    (S := S) hrow hscaled_gradient_update_error_bound k r y

/-- Arithmetic obstruction exposed by the exact `gamma M = (gamma+1)A - W`
identity for the actual Lean object.

Even after supplying a product-limit rate for the parameter matrix and reusing
the PULM `W` rate, the natural triangle route for the projected gradient
operator carries an additional positive multiple of `C beta^r`; scalar algebra
cannot compress such a bound to the source target
`gamma * C * beta^r` on a nonzero vector. -/
private theorem appendixD_gradient_decomposition_coefficient_cannot_close_same_rate
    {C beta N : Real} (r : Nat) (hCbeta : 0 < C * beta ^ r) (hN : 0 < N) :
    ¬ (((S.gamma : Real) + 3) * (C * beta ^ r) * N <=
        (S.gamma : Real) * C * beta ^ r * N) := by
  have hpos : 0 < (C * beta ^ r) * N := mul_pos hCbeta hN
  have hgamma_pos : 0 < (S.gamma : Real) := S.gamma.property
  nlinarith

/-- Exact-head diagnostic for the same-constant M-side projection bridge.

The actual Lean identity `gamma M = (gamma + 1) A - W` supports the same-rate
M bridge only through the forced constant
`appendixDForcedMConstant S C C`.  Specializing that forced bridge back to
`AppendixDGradientProjectionBridge S C beta` requires the false constant
comparison recorded in the second component.  This keeps the tombstoned
same-`C_W` M route out of the public proof cone while naming the precise
missing bridge condition. -/
private theorem appendixD_gradient_projection_bridge_forced_same_constant_obstruction
    {C beta : Real} (hC : 0 < C) (hbeta : 0 <= beta) :
    (AppendixDForcedGradientProjectionBridge S C C beta ->
      appendixDForcedMConstant S C C <= C ->
        AppendixDGradientProjectionBridge S C beta) /\
      ¬ appendixDForcedMConstant S C C <= C := by
  constructor
  · intro hforced hconstant_match
    exact appendixD_gradient_projection_bridge_of_forced_bridge_and_constant_match
      (S := S) hbeta hforced hconstant_match
  · exact appendixD_forced_M_constant_not_same_constant (S := S) hC

/-- The positive-index part of the paper's logarithmic schedule. -/
def theorem2ScheduleLowerBound (C_W beta_W : Real) (k : PositiveOuterIndex) : Real :=
  positive_geometric_log_inner_round_lower_bound C_W beta_W k

/-- Corrected zero-index lower bound for Theorem 2's schedule.

Source boundary: `book/LiangSongYuan2025/PullWithMemoryDGD.json#/
main_theorem/statement_math` prints
`R_k >= max{ln(C_W)/(1-beta_W), ln(k)/(1-beta_W)}` over the zero-based
Theorem 2 window.  The PDF gives the same display in
`paper/2512.24483v1.pdf`, Theorem 2, lines 615-651, and gives no `ln(0)`
or `R_0` convention.  The corrected zero-index object therefore keeps only
the source-stated `ln(C_W)` branch. -/
def theorem2ZeroRoundLowerBound (C_W beta_W : Real) : Real :=
  zeroGeometricLogInnerRoundLowerBound C_W beta_W

/-- Corrected all-index schedule lower bound.  For positive `k` this is the
paper's displayed maximum; at `k = 0` it uses
`theorem2ZeroRoundLowerBound`, making the missing source convention explicit. -/
def theorem2CorrectedScheduleLowerBound (C_W beta_W : Real) (k : Nat) : Real :=
  geometric_log_inner_round_lower_bound C_W beta_W k

/-- Partial version of the displayed schedule term.  It is deliberately
undefined at `k = 0`, because the source prints `ln(k)` together with
`k >= 0` but gives no convention for `ln(0)`.

PDF source check: `paper/2512.24483v1.pdf`, Theorem 2, lines 631-651,
chooses `R_k = max{ln(C_W)/(1-beta_W), ln(k)/(1-beta_W)}` for all `k >= 0`
and later defines `T = sum_{k=0}^{K-1} R_k`. -/
def theorem2PrintedScheduleLowerBound (C_W beta_W : Real) (k : Nat) : Option Real :=
  if hk : 0 < k then
    some (theorem2ScheduleLowerBound C_W beta_W ⟨k, hk⟩)
  else
    none

theorem theorem2PrintedScheduleLowerBound_zero (C_W beta_W : Real) :
    theorem2PrintedScheduleLowerBound C_W beta_W 0 = none := by
  simp [theorem2PrintedScheduleLowerBound]

theorem theorem2PrintedScheduleLowerBound_pos (C_W beta_W : Real)
    (k : Nat) (hk : 0 < k) :
    theorem2PrintedScheduleLowerBound C_W beta_W k =
      some (theorem2ScheduleLowerBound C_W beta_W ⟨k, hk⟩) := by
  simp [theorem2PrintedScheduleLowerBound, hk]

/-- Well-formedness of the printed logarithmic schedule on the zero-based
Theorem 2 averaging window.  This names the source-boundary requirement rather
than filling `ln(0)` by a Lean default. -/
def Theorem2PrintedScheduleDefinedOnHorizon (C_W beta_W : Real)
    (K : PositiveHorizon) : Prop :=
  forall k, k ∈ Finset.range K.1 ->
    exists R, theorem2PrintedScheduleLowerBound C_W beta_W k = some R

/-- The printed `ln(k)` schedule is not defined on any positive zero-based
horizon because `0 ∈ range K` and the source gives no `ln(0)` convention. -/
theorem theorem2PrintedSchedule_not_defined_on_positive_horizon
    (C_W beta_W : Real) (K : PositiveHorizon) :
    ¬ Theorem2PrintedScheduleDefinedOnHorizon C_W beta_W K := by
  intro hdefined
  rcases hdefined 0 (Finset.mem_range.mpr K.2) with ⟨R, hR⟩
  simp [theorem2PrintedScheduleLowerBound] at hR

/-- The source-backed positive-index part of Theorem 2's schedule condition. -/
def Theorem2PositiveSchedule (S : Setup Node E) (L C_W beta_W : Real) : Prop :=
  (S.gamma : Real) <= 1 / (24 * (nodeCount Node : Real) * C_W ^ (2 : Nat) * L) /\
    forall k : PositiveOuterIndex,
      theorem2ScheduleLowerBound C_W beta_W k <= (S.innerRounds k.1 : Real)

/-- Corrected proof-ready schedule boundary for Theorem 2.  It keeps the
paper's stepsize condition and the positive-index logarithmic lower bound, and
adds the explicit `k = 0` branch that the source does not define.

Source quote: `book/LiangSongYuan2025/PullWithMemoryDGD.json#/
main_theorem/statement_math`, "When gamma <= 1/(24 n C_W^2 L) and
R_k >= max{ln(C_W)/(1-beta_W), ln(k)/(1-beta_W)}, we have ...".
The corrected zero-index branch is a source-boundary repair, not an added
paper assumption. -/
def Theorem2CorrectedSchedule (S : Setup Node E) (L C_W beta_W : Real) : Prop :=
  (S.gamma : Real) <= 1 / (24 * (nodeCount Node : Real) * C_W ^ (2 : Nat) * L) /\
    forall k : Nat,
      theorem2CorrectedScheduleLowerBound C_W beta_W k <= (S.innerRounds k : Real)

theorem Theorem2CorrectedSchedule.positive
    {L C_W beta_W : Real}
    (hschedule : Theorem2CorrectedSchedule S L C_W beta_W) :
    Theorem2PositiveSchedule S L C_W beta_W := by
  refine ⟨hschedule.1, ?_⟩
  intro k
  simpa [theorem2CorrectedScheduleLowerBound, theorem2ScheduleLowerBound, k.2]
    using hschedule.2 k.1

theorem Theorem2CorrectedSchedule.zero
    {L C_W beta_W : Real}
    (hschedule : Theorem2CorrectedSchedule S L C_W beta_W) :
    theorem2ZeroRoundLowerBound C_W beta_W <= (S.innerRounds 0 : Real) := by
  simpa [theorem2CorrectedScheduleLowerBound, theorem2ZeroRoundLowerBound]
    using hschedule.2 0

/-- The literal printed Theorem 2 schedule condition over the zero-based
averaging horizon.  It includes the well-formedness obligation for the printed
`ln(k)` expression instead of using Lean's totalized `Real.log 0` value as a
paper convention. -/
def Theorem2PrintedScheduleCondition (S : Setup Node E) (L C_W beta_W : Real)
    (K : PositiveHorizon) : Prop :=
  (S.gamma : Real) <= 1 / (24 * (nodeCount Node : Real) * C_W ^ (2 : Nat) * L) /\
    forall k, k ∈ Finset.range K.1 ->
      exists R, theorem2PrintedScheduleLowerBound C_W beta_W k = some R /\
        R <= (S.innerRounds k : Real)

theorem Theorem2PrintedScheduleCondition.not_realizable
    (L C_W beta_W : Real) (K : PositiveHorizon) :
    ¬ Theorem2PrintedScheduleCondition S L C_W beta_W K := by
  intro hschedule
  exact theorem2PrintedSchedule_not_defined_on_positive_horizon C_W beta_W K
    (fun k hk => by
      rcases hschedule.2 k hk with ⟨R, hR, _⟩
      exact ⟨R, hR⟩)

/-- The paper's chosen constant stepsize in Theorem 2. -/
def Theorem2ChosenStepsize (S : Setup Node E) (L C_W : Real) : Prop :=
  (S.gamma : Real) = inverse_geometric_mixing_step_size (nodeCount Node) 24 L C_W

/-- Minimal natural inner-loop count implementing the positive-index lower
bound.  This replaces the earlier exact `Nat`-to-`Real` equality, which would
have silently required the displayed real number to be an integer. -/
def theorem2ChosenPositiveInnerRounds (C_W beta_W : Real)
    (k : PositiveOuterIndex) : Nat :=
  Nat.ceil (theorem2ScheduleLowerBound C_W beta_W k)

theorem theorem2ChosenPositiveInnerRounds_spec (C_W beta_W : Real)
    (k : PositiveOuterIndex) :
    theorem2ScheduleLowerBound C_W beta_W k <=
      (theorem2ChosenPositiveInnerRounds C_W beta_W k : Real) := by
  exact Nat.le_ceil _

/-- Natural communication count for the corrected `k = 0` branch. -/
def theorem2ChosenZeroInnerRounds (C_W beta_W : Real) : Nat :=
  Nat.ceil (theorem2ZeroRoundLowerBound C_W beta_W)

theorem theorem2ChosenZeroInnerRounds_spec (C_W beta_W : Real) :
    theorem2ZeroRoundLowerBound C_W beta_W <=
      (theorem2ChosenZeroInnerRounds C_W beta_W : Real) := by
  exact Nat.le_ceil _

/-- Natural communication count for the corrected all-index schedule. -/
def theorem2ChosenCorrectedInnerRounds (C_W beta_W : Real) (k : Nat) : Nat :=
  geometricLogInnerRoundCeil C_W beta_W k

theorem theorem2ChosenCorrectedInnerRounds_spec (C_W beta_W : Real) (k : Nat) :
    theorem2CorrectedScheduleLowerBound C_W beta_W k <=
      (theorem2ChosenCorrectedInnerRounds C_W beta_W k : Real) := by
  simpa [theorem2CorrectedScheduleLowerBound, theorem2ScheduleLowerBound,
    theorem2ZeroRoundLowerBound, theorem2ChosenCorrectedInnerRounds]
    using geometricLogInnerRoundCeil_lower_bound C_W beta_W k

/-- The positive-index part of the chosen logarithmic inner-loop schedule,
implemented as the canonical natural ceiling of the displayed real lower
bound.  The printed `k = 0` clause remains a source-boundary gap recorded by
`theorem2PrintedScheduleLowerBound_zero`. -/
def Theorem2ChosenPositiveSchedule (S : Setup Node E) (C_W beta_W : Real) : Prop :=
  forall k : PositiveOuterIndex,
    S.innerRounds k.1 = theorem2ChosenPositiveInnerRounds C_W beta_W k


/-- Literal chosen-schedule version of the printed Theorem 2 statement over a
zero-based horizon.  The chosen natural count is represented by the canonical
ceiling of the displayed real expression, but the declaration still refuses to
invent a value for the missing `k = 0` logarithm. -/
def Theorem2ChosenPrintedScheduleCondition (S : Setup Node E) (L C_W beta_W : Real)
    (K : PositiveHorizon) : Prop :=
  Theorem2ChosenStepsize S L C_W /\
    forall k, k ∈ Finset.range K.1 ->
      exists R, theorem2PrintedScheduleLowerBound C_W beta_W k = some R /\
        S.innerRounds k = Nat.ceil R

theorem Theorem2ChosenPrintedScheduleCondition.not_realizable
    (L C_W beta_W : Real) (K : PositiveHorizon) :
    ¬ Theorem2ChosenPrintedScheduleCondition S L C_W beta_W K := by
  intro hschedule
  exact theorem2PrintedSchedule_not_defined_on_positive_horizon C_W beta_W K
    (fun k hk => by
      rcases hschedule.2 k hk with ⟨R, hR, _⟩
      exact ⟨R, hR⟩)

theorem Theorem2ChosenPositiveSchedule.lower_bound
    {C_W beta_W : Real}
    (hschedule : Theorem2ChosenPositiveSchedule S C_W beta_W)
    (k : PositiveOuterIndex) :
    theorem2ScheduleLowerBound C_W beta_W k <= (S.innerRounds k.1 : Real) := by
  rw [hschedule k]
  exact theorem2ChosenPositiveInnerRounds_spec C_W beta_W k

/-- Domain-safe wrapper for the displayed stationarity bound, with `K` carried
as a positive horizon rather than as a theorem-head side condition.

Source quote: `book/LiangSongYuan2025/PullWithMemoryDGD.json#/
main_theorem/statement_math`, `1/K sum_{k=0}^{K-1} ||grad f(bar x^(k))||^2
<= 18 Delta/(gamma K)`. -/
def Theorem2StationarityBound (S : Setup Node E) (Delta : Real)
    (K : PositiveHorizon) : Prop :=
  averagedStationarity S K.1 <= 18 * Delta / ((S.gamma : Real) * (K.1 : Real))

/-- Equation (5), the chosen-stepsize stationarity estimate in Theorem 2.

Source quote: `book/LiangSongYuan2025/PullWithMemoryDGD.json#/
main_theorem/statement_math`, `1/K sum_{k=0}^{K-1} ||grad f(bar x^(k))||^2
<= 432 n C_W^2 L Delta / K`. -/
def Theorem2ChosenStationarityBound (S : Setup Node E) (Delta L C_W : Real)
    (K : PositiveHorizon) : Prop :=
  averagedStationarity S K.1 <=
    432 * (nodeCount Node : Real) * C_W ^ (2 : Nat) * L * Delta / (K.1 : Real)

/-- The source-facing assumptions shared by Theorem 2's corrected targets:
Assumptions 1--3, Assumption 4, and the theorem's uniform PULM mixing-rate
premise.  This is a transparent conjunction, not an additional regularity
contract. -/
def Theorem2SourceAssumptions (S : Setup Node E) (L Delta C_W beta_W : Real) : Prop :=
  BroadcastNetworkAssumptions S /\
    SmoothnessAssumption S L Delta /\
      UniformPULMMixingRate S C_W beta_W

/-- Corrected general Theorem 2 assumptions: the paper's source assumptions
plus the explicit corrected all-index schedule boundary. -/
def Theorem2CorrectedGeneralAssumptions (S : Setup Node E)
    (L Delta C_W beta_W : Real) : Prop :=
  Theorem2SourceAssumptions S L Delta C_W beta_W /\
    Theorem2CorrectedSchedule S L C_W beta_W

/-- Corrected chosen Theorem 2 assumptions: the paper's source assumptions,
the chosen constant stepsize, and the corrected natural all-index schedule. -/
def Theorem2CorrectedChosenAssumptions (S : Setup Node E)
    (L Delta C_W beta_W : Real) : Prop :=
  Theorem2SourceAssumptions S L Delta C_W beta_W /\
    Theorem2ChosenStepsize S L C_W /\
      forall k : Nat, S.innerRounds k = theorem2ChosenCorrectedInnerRounds C_W beta_W k

/-- Appendix-D potential gap `Delta_k = f(bar x^(k)) - f^*`, with the paper's
`f^* = n^{-1} sum_i f_i^*` realized by the component infimum values. -/
private def appendixDObjectiveGapSeq (S : Setup Node E) : Nat -> Real :=
  fun k =>
    objective S (meanIterate S k) -
      nodeAverage (fun i => componentInfimumValue S i)

/-- The `S_k` part of the Lemma-6-ready Appendix-D recurrence, after dropping
the nonnegative mean-gradient term from the PDF display. -/
private def appendixDStationarityConsensusTerm (S : Setup Node E) : Nat -> Real :=
  fun k =>
    (S.gamma : Real) / 6 *
        ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) +
      24 / (S.gamma : Real) *
        ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat)

/-- The shifted consensus budget `F_k` that remains after applying Lemma 6. -/
private def appendixDConsensusBudgetTerm (S : Setup Node E) : Nat -> Real :=
  fun k =>
    8 / (S.gamma : Real) *
      ‖consensusError S (iterate S k)‖ ^ (2 : Nat)

/-- The multiplicative coefficient in the corrected Lemma-6 recurrence.  This
is the source/coarser interface coefficient selected by the audit route. -/
private def appendixDAbsorptionCoefficient
    (S : Setup Node E) (L C beta : Real) : Nat -> Real :=
  fun k =>
    (S.gamma : Real) * (8 * (nodeCount Node : Real) * C ^ (2 : Nat) * L) *
      beta ^ (2 * S.innerRounds k)

/-- The coefficient printed in Appendix D equation (21).  This is deliberately
separate from `appendixDAbsorptionCoefficient`: the scalar Lemma-6 route chosen
below uses `8 * n * C^2 * L`, while the PDF display at equation (21) prints
`40 * n * C^2 * L`. -/
private def appendixDPrintedEquation21Coefficient
    (S : Setup Node E) (L C beta : Real) : Nat -> Real :=
  fun k =>
    (S.gamma : Real) * (40 * (nodeCount Node : Real) * C ^ (2 : Nat) * L) *
      beta ^ (2 * S.innerRounds k)

/-- The consensus budget printed on the right-hand side of Appendix D
equation (21), before the later Lemma-6 substitution changes the coefficient
to `8 / gamma`. -/
private def appendixDPrintedEquation21ConsensusBudgetTerm (S : Setup Node E) :
    Nat -> Real :=
  fun k =>
    12 / (S.gamma : Real) *
      ‖consensusError S (iterate S k)‖ ^ (2 : Nat)

/-- Same-interface scalar obstruction for the Lemma-5-to-Lemma-6-ready route.

After multiplying Lemma 5 by `24 / gamma`, the objective-gap term contributed
by the consensus estimate is `24` times the coefficient used by the corrected
Lemma-6-ready recurrence.  For a positive coefficient and a positive objective
gap, this cannot be normalized to the single ready coefficient by scalar
algebra.  This records the first coefficient-normalization premise missing
from the source-stage one-step assembly. -/
private theorem appendixD_scaled_consensus_objective_coefficient_cannot_fit_ready
    {L C beta : Real} {k : Nat}
    (hcoeff_pos : 0 < appendixDAbsorptionCoefficient S L C beta k)
    (hgap_pos : 0 < appendixDObjectiveGapSeq S k) :
    ¬
      24 * appendixDAbsorptionCoefficient S L C beta k *
          appendixDObjectiveGapSeq S k <=
        appendixDAbsorptionCoefficient S L C beta k *
          appendixDObjectiveGapSeq S k := by
  have hprod_pos :
      0 <
        appendixDAbsorptionCoefficient S L C beta k *
          appendixDObjectiveGapSeq S k :=
    mul_pos hcoeff_pos hgap_pos
  nlinarith

/-- Same-interface scalar obstruction for using the literal printed
equation-(21) coefficient as the Lemma-6-ready coefficient.

The PDF display at equation (21) has the multiplier `40 n gamma L C^2`, while
the corrected absorption recurrence uses `8 n gamma L C^2`.  With a positive
coefficient and positive objective gap, the printed objective contribution
cannot be treated as if it had the smaller ready coefficient. -/
private theorem appendixD_printed_equation21_coefficient_cannot_fit_ready
    {L C beta : Real} {k : Nat}
    (hcoeff_pos : 0 < appendixDAbsorptionCoefficient S L C beta k)
    (hgap_pos : 0 < appendixDObjectiveGapSeq S k) :
    ¬
      appendixDPrintedEquation21Coefficient S L C beta k *
          appendixDObjectiveGapSeq S k <=
        appendixDAbsorptionCoefficient S L C beta k *
          appendixDObjectiveGapSeq S k := by
  unfold appendixDPrintedEquation21Coefficient appendixDAbsorptionCoefficient at *
  have hprod_pos :
      0 <
        ((S.gamma : Real) * (8 * (nodeCount Node : Real) * C ^ (2 : Nat) * L) *
            beta ^ (2 * S.innerRounds k)) *
          appendixDObjectiveGapSeq S k :=
    mul_pos hcoeff_pos hgap_pos
  nlinarith

/-- The source-boundary obstruction attached to Theorem 2's stationarity
claim under its current same-`C_W` public assumptions.

This is not a replacement assumption.  It is a proved diagnostic extracted
from the existing theorem hypotheses and the Appendix-D scalar interfaces:
the actual Lean `M` object forces a larger same-rate constant, and the printed
equation-(21) coefficient is not the Lemma-6-ready coefficient used by the
absorbed-budget route. -/
def Theorem2StationarityUnsupportedSourceBoundary
    (S : Setup Node E) (L C beta : Real) : Prop :=
  Theorem2SameConstantAppendixDSourceBoundary S C /\
    (forall k,
      0 < appendixDAbsorptionCoefficient S L C beta k ->
        0 < appendixDObjectiveGapSeq S k ->
          ¬
            appendixDPrintedEquation21Coefficient S L C beta k *
                appendixDObjectiveGapSeq S k <=
              appendixDAbsorptionCoefficient S L C beta k *
                appendixDObjectiveGapSeq S k) /\
      forall k,
        0 < appendixDAbsorptionCoefficient S L C beta k ->
          0 < appendixDObjectiveGapSeq S k ->
            ¬
              24 * appendixDAbsorptionCoefficient S L C beta k *
                  appendixDObjectiveGapSeq S k <=
                appendixDAbsorptionCoefficient S L C beta k *
                  appendixDObjectiveGapSeq S k

theorem theorem2_stationarity_unsupported_source_boundary
    {L Delta C beta : Real}
    (hsrc : Theorem2SourceAssumptions S L Delta C beta) :
    Theorem2StationarityUnsupportedSourceBoundary S L C beta := by
  rcases hsrc with ⟨_hnetwork, _hsmooth, hmix⟩
  refine ⟨theorem2_same_constant_appendixD_source_boundary (S := S) hmix, ?_, ?_⟩
  · intro k hcoeff_pos hgap_pos
    exact appendixD_printed_equation21_coefficient_cannot_fit_ready
      (S := S) (L := L) (C := C) (beta := beta) (k := k)
      hcoeff_pos hgap_pos
  · intro k hcoeff_pos hgap_pos
    exact appendixD_scaled_consensus_objective_coefficient_cannot_fit_ready
      (S := S) (L := L) (C := C) (beta := beta) (k := k)
      hcoeff_pos hgap_pos

/-- Literal Appendix-D equation-(21) recurrence shape from the PDF display.

This is a source-boundary object, not the proof-ready recurrence consumed by
the absorption helper.  The file keeps both objects so that the remaining
bridge is explicit: proving the printed display does not by itself supply the
Lemma-6-ready recurrence with the smaller `8 * n * C^2 * L` coefficient and
the `8 / gamma` shifted consensus budget. -/
private def AppendixDPrintedEquation21Recurrence
    (S : Setup Node E) (L C beta : Real) : Prop :=
  forall k,
    appendixDStationarityConsensusTerm S k <=
      (1 + appendixDPrintedEquation21Coefficient S L C beta k) *
          appendixDObjectiveGapSeq S k -
        appendixDObjectiveGapSeq S (k + 1) +
          appendixDPrintedEquation21ConsensusBudgetTerm S k

/-- Source-stage Appendix-D equation-(21) recurrence, in the exact shape needed
by the scalar absorption lemma.  It is a private proof obligation, not a new
source-facing assumption: proving it for the actual Lean objects requires the
paper's unprinted projected `A^(k)-A_infty^(k)` and `M^(k)-E_n` rate bridge. -/
private def AppendixDEquation21ReadyRecurrence
    (S : Setup Node E) (L C beta : Real) : Prop :=
  forall k,
    appendixDStationarityConsensusTerm S k <=
      (1 + appendixDAbsorptionCoefficient S L C beta k) *
          appendixDObjectiveGapSeq S k -
        appendixDObjectiveGapSeq S (k + 1) +
          appendixDConsensusBudgetTerm S k

/-- Private separate-constant version of the Lemma-6-ready Appendix-D
recurrence.

The A-side constants are retained in the interface because Lemma 5 obtains the
recurrence from both projected A and projected M rates.  The multiplicative
objective-gap coefficient is the M-side coefficient, matching the source's
Lemma-6 substitution with `c = 8 n C_M^2 L` and `beta = beta_M`. -/
def AppendixDSeparateEquation21ReadyRecurrence
    (S : Setup Node E) (L C_A beta_A C_M beta_M : Real) : Prop :=
  forall k,
    appendixDStationarityConsensusTerm S k <=
      (1 + appendixDAbsorptionCoefficient S L C_M beta_M k) *
          appendixDObjectiveGapSeq S k -
        appendixDObjectiveGapSeq S (k + 1) +
          appendixDConsensusBudgetTerm S k

/-- Same-target source issue for converting the literal printed equation (21)
to the Lemma-6-ready recurrence.

The printed display carries the `40 n gamma L C^2` objective coefficient, but
the absorption route consumes the smaller `8 n gamma L C^2` coefficient.  This
predicate records the exact scalar implication that would be needed to use the
printed equation as the ready recurrence on a positive objective gap. -/
private def AppendixDPrintedEquation21ReadyCoefficientObstruction
    (S : Setup Node E) (L C beta : Real) : Prop :=
  forall k,
    0 < appendixDAbsorptionCoefficient S L C beta k ->
      0 < appendixDObjectiveGapSeq S k ->
        ¬
          appendixDPrintedEquation21Coefficient S L C beta k *
              appendixDObjectiveGapSeq S k <=
            appendixDAbsorptionCoefficient S L C beta k *
              appendixDObjectiveGapSeq S k

/-- Same-target source issue for the corrected separate-constant ready
recurrence supplier.

Multiplying Lemma 5 by `24 / gamma` contributes `24` times the absorption
coefficient to the objective-gap term, while the Lemma-6-ready recurrence
contains only one copy of that coefficient.  Projection bridges alone cannot
prove this scalar compression on a positive objective gap. -/
private def AppendixDSeparateEquation21ReadyRecurrenceSourceIssue
    (S : Setup Node E) (L C_A beta_A C_M beta_M : Real) : Prop :=
  forall k,
    0 < appendixDAbsorptionCoefficient S L C_M beta_M k ->
      0 < appendixDObjectiveGapSeq S k ->
        ¬
          24 * appendixDAbsorptionCoefficient S L C_M beta_M k *
              appendixDObjectiveGapSeq S k <=
            appendixDAbsorptionCoefficient S L C_M beta_M k *
              appendixDObjectiveGapSeq S k

/-- Source-stage exact-head obstruction for the literal Appendix D equation
(21) route after the projected A/M objects have been supplied.

This declaration is intentionally placed at the exact recurrence head consumed
by the former source route.  It no longer claims the printed recurrence: the
source/PDF coefficient mismatch is the route blocker, and the theorem returns
the typed scalar obstruction at the same granularity instead. -/
private theorem appendixD_printed_equation21_recurrence_from_projection_bridges
    {L C beta : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hsmooth_objective :
      forall x y,
        objective S y <=
          objective S x + inner Real (fullGradient S x) (y - x) +
            (L / 2) * ‖y - x‖ ^ (2 : Nat))
    (hgrad_bridge :
      forall k,
        objectiveGradient S (meanIterate S k) = fullGradient S (meanIterate S k))
    (hconsensus_iterate_succ_decomposition :
      forall k,
            consensusError S (iterate S (k + 1)) =
          consensusError S
            (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k)) -
            consensusError S
              ((S.gamma : Real) •
                matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
                  (nodeGradient S (iterate S k))))
    (hA : AppendixDParameterProjectionBridge S C beta Ainf)
    (hM : AppendixDGradientProjectionBridge S C beta) :
    AppendixDPrintedEquation21ReadyCoefficientObstruction S L C beta := by
  have hAM : AppendixDProjectedAMRate S C beta :=
    appendixD_projected_AM_rate_from_source_projection_bridges
      (S := S) Ainf hrow hA hM
  intro k hcoeff_pos hgap_pos
  exact appendixD_printed_equation21_coefficient_cannot_fit_ready
    (S := S) (L := L) (C := C) (beta := beta) (k := k)
    hcoeff_pos hgap_pos

/-- Source-stage exact-head obstruction for the separate-constant
Lemma-6-ready Appendix-D recurrence.

This is the corrected private interface named by the source-boundary audit. It
does not assume a same-`C_W` transfer from Theorem 2's `W`-rate; instead it
starts from the already separated projected A/M-rate bundle.  The projected
rates are sufficient to expose the source coefficient problem, but they do not
supply the missing scalar compression from the Lemma-5 contribution to the
Lemma-6-ready coefficient. -/
private theorem appendixD_separate_equation21_ready_recurrence_from_projected_AM_rate
    {L C_A beta_A C_M beta_M : Real}
    (hsmooth_objective :
      forall x y,
        objective S y <=
          objective S x + inner Real (fullGradient S x) (y - x) +
            (L / 2) * ‖y - x‖ ^ (2 : Nat))
    (hgrad_bridge :
      forall k,
        objectiveGradient S (meanIterate S k) = fullGradient S (meanIterate S k))
    (hconsensus_iterate_succ_decomposition :
      forall k,
            consensusError S (iterate S (k + 1)) =
          consensusError S
            (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k)) -
            consensusError S
              ((S.gamma : Real) •
                matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
                  (nodeGradient S (iterate S k))))
    (hAM : AppendixDSeparateProjectedAMRate S C_A beta_A C_M beta_M) :
    AppendixDSeparateEquation21ReadyRecurrenceSourceIssue
      S L C_A beta_A C_M beta_M := by
  intro k hcoeff_pos hgap_pos
  have hA_rate_at_iterate :
      ‖consensusError S
          (matrixStateMul (innerParameterMatrix S k (S.innerRounds k))
            (iterate S k))‖ <=
        C_A * beta_A ^ S.innerRounds k *
          ‖consensusError S (iterate S k)‖ :=
    hAM.1 k (S.innerRounds k) (iterate S k)
  have hM_rate_at_gradient :
      ‖consensusError S
          ((S.gamma : Real) •
            matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
              (nodeGradient S (iterate S k)))‖ <=
        (S.gamma : Real) * C_M * beta_M ^ S.innerRounds k *
          ‖nodeGradient S (iterate S k)‖ :=
    hAM.2 k (S.innerRounds k) (nodeGradient S (iterate S k))
  have hdecomp := hconsensus_iterate_succ_decomposition k
  have hgrad := hgrad_bridge k
  have hsmooth_step :
      objective S (meanIterate S (k + 1)) <=
        objective S (meanIterate S k) +
          inner Real (fullGradient S (meanIterate S k))
            (meanIterate S (k + 1) - meanIterate S k) +
          (L / 2) *
            ‖meanIterate S (k + 1) - meanIterate S k‖ ^ (2 : Nat) :=
    hsmooth_objective (meanIterate S k) (meanIterate S (k + 1))
  exact appendixD_scaled_consensus_objective_coefficient_cannot_fit_ready
    (S := S) (L := L) (C := C_M) (beta := beta_M) (k := k)
    hcoeff_pos hgap_pos

/-- Source-bridge form of the separate-constant equation-(21) source issue.

This is the exact entrypoint requested by the refactor audit: it consumes the
Appendix-D `A_infty^(k)` parameter bridge and the projected M bridge, converts
them to the separated projected-rate bundle, and then exposes the coefficient
obstruction isolated in
`appendixD_separate_equation21_ready_recurrence_from_projected_AM_rate`. -/
private theorem appendixD_separate_equation21_ready_recurrence_from_source_projection_bridges
    {L C_A beta_A C_M beta_M : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hsmooth_objective :
      forall x y,
        objective S y <=
          objective S x + inner Real (fullGradient S x) (y - x) +
            (L / 2) * ‖y - x‖ ^ (2 : Nat))
    (hgrad_bridge :
      forall k,
        objectiveGradient S (meanIterate S k) = fullGradient S (meanIterate S k))
    (hconsensus_iterate_succ_decomposition :
      forall k,
        consensusError S (iterate S (k + 1)) =
          consensusError S
            (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k)) -
            consensusError S
              ((S.gamma : Real) •
                matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
                  (nodeGradient S (iterate S k))))
    (hA : AppendixDParameterProjectionBridge S C_A beta_A Ainf)
    (hM : AppendixDGradientProjectionBridge S C_M beta_M) :
    AppendixDSeparateEquation21ReadyRecurrenceSourceIssue
      S L C_A beta_A C_M beta_M := by
  have hAM : AppendixDSeparateProjectedAMRate S C_A beta_A C_M beta_M :=
    appendixD_separate_projected_AM_rate_from_source_projection_bridges
      (S := S) Ainf hrow hA hM
  exact appendixD_separate_equation21_ready_recurrence_from_projected_AM_rate
    (S := S) hsmooth_objective hgrad_bridge hconsensus_iterate_succ_decomposition
    hAM

/-- Same-constant source issue for the Lemma-6-ready Appendix-D recurrence
selected by the retired audit route.

The same-constant route remains tombstoned; this declaration now returns the
same coefficient obstruction as the separate-constant source issue instead of
claiming a supplier for the ready recurrence. -/
private theorem appendixD_equation21_ready_recurrence_from_projection_bridges
    {L C beta : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hsmooth_objective :
      forall x y,
        objective S y <=
          objective S x + inner Real (fullGradient S x) (y - x) +
            (L / 2) * ‖y - x‖ ^ (2 : Nat))
    (hgrad_bridge :
      forall k,
        objectiveGradient S (meanIterate S k) = fullGradient S (meanIterate S k))
    (hconsensus_iterate_succ_decomposition :
      forall k,
        consensusError S (iterate S (k + 1)) =
          consensusError S
            (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k)) -
            consensusError S
              ((S.gamma : Real) •
                matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
                  (nodeGradient S (iterate S k))))
    (hA : AppendixDParameterProjectionBridge S C beta Ainf)
    (hM : AppendixDGradientProjectionBridge S C beta) :
    AppendixDSeparateEquation21ReadyRecurrenceSourceIssue S L C beta C beta := by
  have hAM : AppendixDProjectedAMRate S C beta :=
    appendixD_projected_AM_rate_from_source_projection_bridges
      (S := S) Ainf hrow hA hM
  exact appendixD_separate_equation21_ready_recurrence_from_projected_AM_rate
    (S := S) hsmooth_objective hgrad_bridge hconsensus_iterate_succ_decomposition
    hAM

/-- Diagnostic migration of the ready-recurrence supplier to the corrected
M-side bridge.

For the same-constant Theorem 2 boundary this theorem exposes the exact extra
obligation: the forced M constant would have to be no larger than the theorem's
`C`.  The next theorem shows that obligation is false when the A and W
constants are both `C > 0`, so the old same-`C_W` M bridge must not remain the
active public route. -/
private theorem appendixD_equation21_ready_recurrence_from_forced_same_C_bridge
    {L C beta : Real} (Ainf : AppendixDParameterLimitFamily Node)
    (hrow : forall t, (S.mixing t) ∈ _root_.Matrix.rowStochastic Real Node)
    (hbeta : 0 <= beta)
    (hsmooth_objective :
      forall x y,
        objective S y <=
          objective S x + inner Real (fullGradient S x) (y - x) +
            (L / 2) * ‖y - x‖ ^ (2 : Nat))
    (hgrad_bridge :
      forall k,
        objectiveGradient S (meanIterate S k) = fullGradient S (meanIterate S k))
    (hconsensus_iterate_succ_decomposition :
      forall k,
        consensusError S (iterate S (k + 1)) =
          consensusError S
            (matrixStateMul (innerParameterMatrix S k (S.innerRounds k)) (iterate S k)) -
            consensusError S
              ((S.gamma : Real) •
                matrixStateMul (innerGradientMatrix S k (S.innerRounds k))
                  (nodeGradient S (iterate S k))))
    (hA : AppendixDParameterProjectionBridge S C beta Ainf)
    (hM_forced : AppendixDForcedGradientProjectionBridge S C C beta)
    (hconstant_match : appendixDForcedMConstant S C C <= C) :
    AppendixDSeparateEquation21ReadyRecurrenceSourceIssue S L C beta C beta := by
  have hM_same : AppendixDGradientProjectionBridge S C beta :=
    appendixD_gradient_projection_bridge_of_forced_bridge_and_constant_match
      (S := S) hbeta hM_forced hconstant_match
  exact appendixD_equation21_ready_recurrence_from_projection_bridges
    (S := S) Ainf hrow hsmooth_objective hgrad_bridge
    hconsensus_iterate_succ_decomposition hA hM_same

/-- The finite-horizon inverse-product weight conditions used by Lemma 6 after
the equation-(21) recurrence has been established. -/
def AppendixDAbsorptionWeightFloor
    (S : Setup Node E) (L C beta : Real) (K : PositiveHorizon)
    (W : Nat -> Real) : Prop :=
  W 0 = 1 /\
    (forall k, k < K.1 ->
      W (k + 1) * (1 + appendixDAbsorptionCoefficient S L C beta k) = W k) /\
    (forall k, k < K.1 -> (1 / 3 : Real) <= W (k + 1)) /\
    (forall k, k < K.1 -> W (k + 1) <= 1) /\
    0 <= W K.1 * appendixDObjectiveGapSeq S K.1

/-- Canonical inverse-product weights used in Lemma 6's telescoping proof. -/
private def appendixDInverseProductWeight
    (S : Setup Node E) (L C beta : Real) : Nat -> Real :=
  fun k =>
    ((Finset.range k).prod
      (fun j => 1 + appendixDAbsorptionCoefficient S L C beta j))⁻¹

private theorem appendixDObjectiveGapSeq_nonneg
    {L Delta : Real} (hsmooth : SmoothnessAssumption S L Delta) (k : Nat) :
    0 <= appendixDObjectiveGapSeq S k := by
  classical
  rcases hsmooth with ⟨_hfamily, _hDelta, hwell, _hgap⟩
  have hsum_le :
      Finset.univ.sum (fun i => componentInfimumValue S i) <=
        Finset.univ.sum (fun i => S.localObjective i (meanIterate S k)) := by
    exact Finset.sum_le_sum
      (fun i _hi => componentInfimumValue_le (S := S) hwell i (meanIterate S k))
  have hinv_nonneg : 0 <= invNodeCount Node := by
    unfold invNodeCount
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
  have havg_le :
      nodeAverage (fun i => componentInfimumValue S i) <=
        objective S (meanIterate S k) := by
    simpa [objective, nodeAverage_eq_invNodeCount_smul_sum, smul_eq_mul]
      using hscaled
  unfold appendixDObjectiveGapSeq
  linarith

/-- Construct the Lemma-6 weight-floor interface from inverse-product weights.

The remaining scalar source work is isolated in `hprod_le_three`: it is the
finite product estimate obtained from the schedule lower bound in Lemma 6. -/
private theorem appendixD_absorption_weight_floor_from_inverse_product
    {L Delta C beta : Real} (K : PositiveHorizon)
    (hsmooth : SmoothnessAssumption S L Delta)
    (hcoeff_nonneg :
      forall k, k < K.1 -> 0 <= appendixDAbsorptionCoefficient S L C beta k)
    (hprod_le_three :
      forall k, k < K.1 ->
        (Finset.range (k + 1)).prod
            (fun j => 1 + appendixDAbsorptionCoefficient S L C beta j) <=
          (3 : Real)) :
    AppendixDAbsorptionWeightFloor S L C beta K
      (appendixDInverseProductWeight S L C beta) := by
  classical
  let a : Nat -> Real := appendixDAbsorptionCoefficient S L C beta
  have hfactor_pos :
      forall k, k < K.1 -> 0 < 1 + a k := by
    intro k hk
    have hak : 0 <= a k := by simpa [a] using hcoeff_nonneg k hk
    linarith
  have hprod_pos :
      forall k, k <= K.1 ->
        0 < (Finset.range k).prod (fun j => 1 + a j) := by
    intro k hk
    refine Finset.prod_pos ?_
    intro j hj
    exact hfactor_pos j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  have hprod_ge_one :
      forall k, k <= K.1 ->
        (1 : Real) <= (Finset.range k).prod (fun j => 1 + a j) := by
    intro k hk
    refine Finset.one_le_prod ?_
    intro j hj
    have haj : 0 <= a j := by
      simpa [a] using hcoeff_nonneg j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [appendixDInverseProductWeight]
  · intro k hk
    have hk_le : k <= K.1 := le_of_lt hk
    have hPk_pos : 0 < (Finset.range k).prod (fun j => 1 + a j) :=
      hprod_pos k hk_le
    have hfactor_ne : 1 + a k ≠ 0 :=
      ne_of_gt (hfactor_pos k hk)
    have hPk_ne : (Finset.range k).prod (fun j => 1 + a j) ≠ 0 :=
      ne_of_gt hPk_pos
    calc
      appendixDInverseProductWeight S L C beta (k + 1) * (1 + a k) =
          (((Finset.range k).prod (fun j => 1 + a j) * (1 + a k))⁻¹) *
            (1 + a k) := by
            simp [appendixDInverseProductWeight, a, Finset.prod_range_succ]
      _ = ((Finset.range k).prod (fun j => 1 + a j))⁻¹ := by
            field_simp [hfactor_ne, hPk_ne]
      _ = appendixDInverseProductWeight S L C beta k := by
            simp [appendixDInverseProductWeight, a]
  · intro k hk
    have hP_pos :
        0 < (Finset.range (k + 1)).prod (fun j => 1 + a j) :=
      hprod_pos (k + 1) (Nat.succ_le_of_lt hk)
    have hP_le : (Finset.range (k + 1)).prod (fun j => 1 + a j) <= (3 : Real) := by
      simpa [a] using hprod_le_three k hk
    have hthird :
        (1 / (3 : Real)) <=
          ((Finset.range (k + 1)).prod (fun j => 1 + a j))⁻¹ := by
      simpa [one_div] using
        (one_div_le_one_div_of_le hP_pos hP_le)
    simpa [appendixDInverseProductWeight, a] using hthird
  · intro k hk
    have hP_pos :
        0 < (Finset.range (k + 1)).prod (fun j => 1 + a j) :=
      hprod_pos (k + 1) (Nat.succ_le_of_lt hk)
    have hP_ge_one :
        (1 : Real) <= (Finset.range (k + 1)).prod (fun j => 1 + a j) :=
      hprod_ge_one (k + 1) (Nat.succ_le_of_lt hk)
    have hone :
        ((Finset.range (k + 1)).prod (fun j => 1 + a j))⁻¹ <= (1 : Real) := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hP_ge_one)
    simpa [appendixDInverseProductWeight, a] using hone
  · have hW_nonneg :
        0 <= appendixDInverseProductWeight S L C beta K.1 := by
      have hP_pos :
          0 < (Finset.range K.1).prod (fun j => 1 + a j) :=
        hprod_pos K.1 (le_refl K.1)
      simp [appendixDInverseProductWeight, a, le_of_lt hP_pos]
    have hgap_nonneg :
        0 <= appendixDObjectiveGapSeq S K.1 :=
      appendixDObjectiveGapSeq_nonneg (S := S) hsmooth K.1
    exact mul_nonneg hW_nonneg hgap_nonneg

/-- The scalar side condition required to consume the literal printed
Appendix-D equation-(21) recurrence while still ending at the later
`8 / gamma` consensus budget used by the final cancellation.

The last budget field is deliberately explicit: the printed recurrence has
`12 / gamma`, so the absorption weights must themselves bridge the printed
budget to the smaller cancellation budget. -/
private def AppendixDPrintedEquation21AbsorptionSideCondition
    (S : Setup Node E) (L C beta : Real) (K : PositiveHorizon)
    (W : Nat -> Real) : Prop :=
  W 0 = 1 /\
    (forall k, k < K.1 ->
      W (k + 1) * (1 + appendixDPrintedEquation21Coefficient S L C beta k) =
        W k) /\
    (forall k, k < K.1 -> (1 / 3 : Real) <= W (k + 1)) /\
    (forall k, k < K.1 ->
      W (k + 1) * appendixDPrintedEquation21ConsensusBudgetTerm S k <=
        appendixDConsensusBudgetTerm S k) /\
    0 <= W K.1 * appendixDObjectiveGapSeq S K.1

/-- The printed equation-(21) absorption side condition carries an extra
scalar burden: at every nonzero consensus-budget term it forces the inverse
product weight below `2/3`.

This is the exact coefficient obstruction between the PDF display's
`12 / gamma` consensus term and the later cancellation budget `8 / gamma`.
It is not implied by the usual Lemma-6 lower floor `1/3 <= W(k+1)`; a supplier
for `AppendixDPrintedEquation21AbsorptionSideCondition` must also prove this
upper cap from the chosen product weights and coefficients. -/
private theorem appendixD_printed_absorption_side_condition_forces_weight_cap
    (L C beta : Real) (K : PositiveHorizon) (W : Nat -> Real)
    (hweights :
      AppendixDPrintedEquation21AbsorptionSideCondition S L C beta K W)
    {k : Nat} (hk : k < K.1)
    (hcons :
      0 <
        ‖consensusError S (iterate S k)‖ ^ (2 : Nat)) :
    W (k + 1) <= 2 / 3 := by
  rcases hweights with ⟨_hW0, _hW_succ, _hW_floor, hbudget, _hterminal⟩
  have hgamma_pos : 0 < (S.gamma : Real) := S.gamma.property
  have hbudget_k := hbudget k hk
  unfold appendixDPrintedEquation21ConsensusBudgetTerm appendixDConsensusBudgetTerm at hbudget_k
  let A : Real :=
    (1 / (S.gamma : Real)) *
      ‖consensusError S (iterate S k)‖ ^ (2 : Nat)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos (one_div_pos.mpr hgamma_pos) hcons
  have hbudget_A : W (k + 1) * (12 * A) <= 8 * A := by
    calc
      W (k + 1) * (12 * A) =
          W (k + 1) *
            (12 / (S.gamma : Real) *
              ‖consensusError S (iterate S k)‖ ^ (2 : Nat)) := by
            dsimp [A]
            ring
      _ <=
          8 / (S.gamma : Real) *
            ‖consensusError S (iterate S k)‖ ^ (2 : Nat) := hbudget_k
      _ = 8 * A := by
            dsimp [A]
            ring
  nlinarith [hbudget_A, hA_pos]

/-- Contrapositive form of
`appendixD_printed_absorption_side_condition_forces_weight_cap`.

If a candidate inverse-product weight is still larger than `2/3` at a
nonzero consensus term, then it cannot satisfy the printed equation-(21)
absorption side condition. -/
private theorem not_appendixD_printed_absorption_side_condition_of_weight_gt_two_thirds
    (L C beta : Real) (K : PositiveHorizon) (W : Nat -> Real)
    {k : Nat} (hk : k < K.1)
    (hcons :
      0 <
        ‖consensusError S (iterate S k)‖ ^ (2 : Nat))
    (hW_gt : 2 / 3 < W (k + 1)) :
    ¬ AppendixDPrintedEquation21AbsorptionSideCondition S L C beta K W := by
  intro hweights
  have hcap :=
    appendixD_printed_absorption_side_condition_forces_weight_cap
      (S := S) L C beta K W hweights hk hcons
  linarith

/-- Same-interface scalar obstruction for the literal printed equation-(21)
absorption route.

The printed side condition requires the inverse-product weights for the
`40 n gamma L C^2 beta^(2 R_k)` coefficient and also requires those same
weights to shrink the printed `12 / gamma` consensus budget to the later
`8 / gamma` cancellation budget.  If the first two printed coefficients are
small while the first positive consensus budget is nonzero, the product
equations force `W 2 > 2/3`, contradicting the budget cap forced by the
previous theorem.  Thus a supplier for the printed side condition needs a real
coefficient/product cap argument; it is not a routine consequence of the
usual Lemma-6 lower floor. -/
private theorem not_appendixD_printed_absorption_side_condition_of_two_small_coefficients
    (L C beta : Real) (K : PositiveHorizon) (W : Nat -> Real)
    (hK : 1 < K.1)
    (hcoef0_nonneg :
      0 <= appendixDPrintedEquation21Coefficient S L C beta 0)
    (hcoef0_le :
      appendixDPrintedEquation21Coefficient S L C beta 0 <= 1 / 5)
    (hcoef1_nonneg :
      0 <= appendixDPrintedEquation21Coefficient S L C beta 1)
    (hcoef1_le :
      appendixDPrintedEquation21Coefficient S L C beta 1 <= 1 / 5)
    (hcons1 :
      0 <
        ‖consensusError S (iterate S 1)‖ ^ (2 : Nat)) :
    ¬ AppendixDPrintedEquation21AbsorptionSideCondition S L C beta K W := by
  intro hweights
  have hcap :
      W 2 <= 2 / 3 :=
    appendixD_printed_absorption_side_condition_forces_weight_cap
      (S := S) L C beta K W hweights hK hcons1
  rcases hweights with ⟨hW0, hW_succ, hW_floor, _hbudget, _hterminal⟩
  let a0 := appendixDPrintedEquation21Coefficient S L C beta 0
  let a1 := appendixDPrintedEquation21Coefficient S L C beta 1
  have hzero_lt_K : 0 < K.1 := lt_trans Nat.zero_lt_one hK
  have hW1_eq : W 1 * (1 + a0) = 1 := by
    simpa [a0, hW0] using hW_succ 0 hzero_lt_K
  have hW2_step : W 2 * (1 + a1) = W 1 := by
    simpa [a1] using hW_succ 1 hK
  have hprod_eq : W 2 * ((1 + a1) * (1 + a0)) = 1 := by
    calc
      W 2 * ((1 + a1) * (1 + a0)) =
          (W 2 * (1 + a1)) * (1 + a0) := by ring
      _ = W 1 * (1 + a0) := by rw [hW2_step]
      _ = 1 := hW1_eq
  have ha0_nonneg : 0 <= a0 := by simpa [a0] using hcoef0_nonneg
  have ha0_le : a0 <= 1 / 5 := by simpa [a0] using hcoef0_le
  have ha1_nonneg : 0 <= a1 := by simpa [a1] using hcoef1_nonneg
  have ha1_le : a1 <= 1 / 5 := by simpa [a1] using hcoef1_le
  have hfactor_nonneg : 0 <= (1 + a1) * (1 + a0) := by nlinarith
  have hfactor_le : (1 + a1) * (1 + a0) <= 36 / 25 := by nlinarith
  have hprod_le :
      W 2 * ((1 + a1) * (1 + a0)) <= (2 / 3) * (36 / 25) :=
    mul_le_mul hcap hfactor_le hfactor_nonneg (by norm_num)
  nlinarith

/-- Exact-head existential obstruction for the active printed equation-(21)
absorption supplier.

The public theorem currently needs an inhabitant of
`exists W, AppendixDPrintedEquation21AbsorptionSideCondition ...` to consume
the literal PDF recurrence.  The preceding theorem shows each candidate `W`
is impossible when the first two printed coefficients are small and the first
consensus budget is nonzero; this theorem packages that result at the exact
existential head of the local `hweights` leaf. -/
private theorem not_exists_appendixD_printed_absorption_side_condition_of_two_small_coefficients
    (L C beta : Real) (K : PositiveHorizon)
    (hK : 1 < K.1)
    (hcoef0_nonneg :
      0 <= appendixDPrintedEquation21Coefficient S L C beta 0)
    (hcoef0_le :
      appendixDPrintedEquation21Coefficient S L C beta 0 <= 1 / 5)
    (hcoef1_nonneg :
      0 <= appendixDPrintedEquation21Coefficient S L C beta 1)
    (hcoef1_le :
      appendixDPrintedEquation21Coefficient S L C beta 1 <= 1 / 5)
    (hcons1 :
      0 <
        ‖consensusError S (iterate S 1)‖ ^ (2 : Nat)) :
    ¬ exists W : Nat -> Real,
      AppendixDPrintedEquation21AbsorptionSideCondition S L C beta K W := by
  rintro ⟨W, hW⟩
  exact not_appendixD_printed_absorption_side_condition_of_two_small_coefficients
    (S := S) L C beta K W hK hcoef0_nonneg hcoef0_le hcoef1_nonneg hcoef1_le hcons1 hW

/-- Scalar Appendix-D absorption core.

This is the product-weighted part of Lemma 6, separated from the algorithmic
PULM estimates and from the logarithmic schedule proof.  The weights `W` are
the inverse products used to telescope the extra `(1 + a_k)` factor. -/
private theorem appendixD_absorbing_extra_errors_from_weight_floor
    (K : Nat) (a DeltaSeq Sterm Fterm W : Nat -> Real)
    (hW0 : W 0 = 1)
    (hW_succ : forall k, k < K -> W (k + 1) * (1 + a k) = W k)
    (hW_floor : forall k, k < K -> (1 / 3 : Real) <= W (k + 1))
    (hW_le_one : forall k, k < K -> W (k + 1) <= 1)
    (hterminal_nonneg : 0 <= W K * DeltaSeq K)
    (hS_nonneg : forall k, k < K -> 0 <= Sterm k)
    (hF_nonneg : forall k, k < K -> 0 <= Fterm k)
    (hstep : forall k, k < K ->
      Sterm k <= (1 + a k) * DeltaSeq k - DeltaSeq (k + 1) + Fterm k) :
    (Finset.range K).sum Sterm <=
      3 * DeltaSeq 0 + 3 * (Finset.range K).sum Fterm := by
  classical
  let A : Nat -> Real := fun n => W n * Sterm (n - 1)
  let C : Nat -> Real := fun k => W (k + 1) * Fterm k
  have hweighted_full :
      (Finset.range K).sum (fun k => A (k + 1)) + W K * DeltaSeq K <=
        (Finset.range K).sum C + DeltaSeq 0 := by
    refine SOptLib.sum_range_succ_add_weighted_tail_le_sum_add_initial_of_step
      (T := K) (A := A) (B := DeltaSeq) (C := C) (W := W) hW0 ?_
    intro k hk
    have hWnext_nonneg : 0 <= W (k + 1) := by
      linarith [hW_floor k hk]
    have hmul :
        W (k + 1) * Sterm k <=
          W (k + 1) * ((1 + a k) * DeltaSeq k - DeltaSeq (k + 1) + Fterm k) :=
      mul_le_mul_of_nonneg_left (hstep k hk) hWnext_nonneg
    dsimp [A, C]
    rw [← hW_succ k hk]
    nlinarith
  have hweighted_sum :
      (Finset.range K).sum (fun k => W (k + 1) * Sterm k) <=
        DeltaSeq 0 + (Finset.range K).sum (fun k => W (k + 1) * Fterm k) := by
    have hfull :
        (Finset.range K).sum (fun k => W (k + 1) * Sterm k) +
            W K * DeltaSeq K <=
          (Finset.range K).sum (fun k => W (k + 1) * Fterm k) + DeltaSeq 0 := by
      simpa [A, C, add_comm, add_left_comm, add_assoc] using hweighted_full
    linarith
  have hfloor_sum :
      (1 / 3 : Real) * (Finset.range K).sum Sterm <=
        (Finset.range K).sum (fun k => W (k + 1) * Sterm k) := by
    calc
      (1 / 3 : Real) * (Finset.range K).sum Sterm =
          (Finset.range K).sum (fun k => (1 / 3 : Real) * Sterm k) := by
            rw [Finset.mul_sum]
      _ <= (Finset.range K).sum (fun k => W (k + 1) * Sterm k) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_right
              (hW_floor k (Finset.mem_range.mp hk))
              (hS_nonneg k (Finset.mem_range.mp hk))
  have hweighted_F :
      (Finset.range K).sum (fun k => W (k + 1) * Fterm k) <=
        (Finset.range K).sum Fterm := by
    refine Finset.sum_le_sum ?_
    intro k hk
    simpa using mul_le_mul_of_nonneg_right
      (hW_le_one k (Finset.mem_range.mp hk))
      (hF_nonneg k (Finset.mem_range.mp hk))
  have hcore :
      (1 / 3 : Real) * (Finset.range K).sum Sterm <=
        DeltaSeq 0 + (Finset.range K).sum Fterm := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : Real) <= 3)
  nlinarith

/-- Consume the audit-designated source/coarser Appendix-D recurrence through
the already-proved scalar absorption helper, producing the exact absorbed
budget required by the final stationarity cancellation. -/
private theorem appendixD_absorbed_budget_of_equation21_ready_recurrence
    (L C beta : Real) (K : PositiveHorizon)
    (hrecurrence : AppendixDEquation21ReadyRecurrence S L C beta)
    (W : Nat -> Real)
    (hweights : AppendixDAbsorptionWeightFloor S L C beta K W) :
    (Finset.range K.1).sum
        (fun k =>
          (S.gamma : Real) / 6 *
              ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) +
            24 / (S.gamma : Real) *
              ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat)) <=
      3 * (objective S (meanIterate S 0) -
            nodeAverage (fun i => componentInfimumValue S i)) +
        3 * (Finset.range K.1).sum
          (fun k =>
            8 / (S.gamma : Real) *
              ‖consensusError S (iterate S k)‖ ^ (2 : Nat)) := by
  rcases hweights with
    ⟨hW0, hW_succ, hW_floor, hW_le_one, hterminal_nonneg⟩
  have hS_nonneg :
      forall k, k < K.1 -> 0 <= appendixDStationarityConsensusTerm S k := by
    intro k _hk
    have hgamma_nonneg : 0 <= (S.gamma : Real) := le_of_lt S.gamma.property
    have hterm_grad :
        0 <=
          (S.gamma : Real) / 6 *
            ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) := by
      exact mul_nonneg (div_nonneg hgamma_nonneg (by norm_num)) (sq_nonneg _)
    have hterm_cons :
        0 <=
          24 / (S.gamma : Real) *
            ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat) := by
      exact mul_nonneg (div_nonneg (by norm_num) hgamma_nonneg) (sq_nonneg _)
    unfold appendixDStationarityConsensusTerm
    exact add_nonneg hterm_grad hterm_cons
  have hF_nonneg :
      forall k, k < K.1 -> 0 <= appendixDConsensusBudgetTerm S k := by
    intro k _hk
    have hgamma_nonneg : 0 <= (S.gamma : Real) := le_of_lt S.gamma.property
    have hterm :
        0 <=
          8 / (S.gamma : Real) *
            ‖consensusError S (iterate S k)‖ ^ (2 : Nat) := by
      exact mul_nonneg (div_nonneg (by norm_num) hgamma_nonneg) (sq_nonneg _)
    unfold appendixDConsensusBudgetTerm
    exact hterm
  have hbudget :=
    appendixD_absorbing_extra_errors_from_weight_floor
      (K := K.1)
      (a := appendixDAbsorptionCoefficient S L C beta)
      (DeltaSeq := appendixDObjectiveGapSeq S)
      (Sterm := appendixDStationarityConsensusTerm S)
      (Fterm := appendixDConsensusBudgetTerm S)
      (W := W)
      hW0 hW_succ hW_floor hW_le_one hterminal_nonneg hS_nonneg hF_nonneg
      (fun k _hk => hrecurrence k)
  simpa [appendixDStationarityConsensusTerm, appendixDObjectiveGapSeq,
    appendixDConsensusBudgetTerm] using hbudget

/-- Consume the private separate-constant Appendix-D recurrence through the
same scalar absorption kernel.

This is the corrected diagnostic route requested by the audit: the recurrence
may be stated with source-level A/M constants, while the absorption weights
only need the M-side coefficient that appears in Lemma 6. -/
theorem appendixD_absorbed_budget_of_separate_equation21_ready_recurrence
    (L C_A beta_A C_M beta_M : Real) (K : PositiveHorizon)
    (hrecurrence :
      AppendixDSeparateEquation21ReadyRecurrence S L C_A beta_A C_M beta_M)
    (W : Nat -> Real)
    (hweights : AppendixDAbsorptionWeightFloor S L C_M beta_M K W) :
    (Finset.range K.1).sum
        (fun k =>
          (S.gamma : Real) / 6 *
              ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) +
            24 / (S.gamma : Real) *
              ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat)) <=
      3 * (objective S (meanIterate S 0) -
            nodeAverage (fun i => componentInfimumValue S i)) +
        3 * (Finset.range K.1).sum
          (fun k =>
            8 / (S.gamma : Real) *
              ‖consensusError S (iterate S k)‖ ^ (2 : Nat)) := by
  exact appendixD_absorbed_budget_of_equation21_ready_recurrence
    (S := S) L C_M beta_M K hrecurrence W hweights

/-- Consume the literal printed Appendix-D equation-(21) recurrence through a
corrected scalar absorption interface.

Unlike `appendixD_absorbed_budget_of_equation21_ready_recurrence`, this theorem
does not silently replace the PDF's `40` coefficient by the Lemma-6-ready `8`
coefficient.  It uses the printed coefficient in the telescoping weights and
requires the exact weighted budget bridge needed to reach the later
`8 / gamma` cancellation term. -/
private theorem appendixD_absorbed_budget_of_printed_equation21_recurrence
    (L C beta : Real) (K : PositiveHorizon)
    (hrecurrence : AppendixDPrintedEquation21Recurrence S L C beta)
    (W : Nat -> Real)
    (hweights :
      AppendixDPrintedEquation21AbsorptionSideCondition S L C beta K W) :
    (Finset.range K.1).sum
        (fun k =>
          (S.gamma : Real) / 6 *
              ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) +
            24 / (S.gamma : Real) *
              ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat)) <=
      3 * (objective S (meanIterate S 0) -
            nodeAverage (fun i => componentInfimumValue S i)) +
        3 * (Finset.range K.1).sum
          (fun k =>
            8 / (S.gamma : Real) *
              ‖consensusError S (iterate S k)‖ ^ (2 : Nat)) := by
  rcases hweights with
    ⟨hW0, hW_succ, hW_floor, hW_budget, hterminal_nonneg⟩
  let A : Nat -> Real := fun n => W n * appendixDStationarityConsensusTerm S (n - 1)
  let Cseq : Nat -> Real :=
    fun k => W (k + 1) * appendixDPrintedEquation21ConsensusBudgetTerm S k
  have hweighted_full :
      (Finset.range K.1).sum (fun k => A (k + 1)) +
          W K.1 * appendixDObjectiveGapSeq S K.1 <=
        (Finset.range K.1).sum Cseq + appendixDObjectiveGapSeq S 0 := by
    refine SOptLib.sum_range_succ_add_weighted_tail_le_sum_add_initial_of_step
      (T := K.1) (A := A) (B := appendixDObjectiveGapSeq S) (C := Cseq)
      (W := W) hW0 ?_
    intro k hk
    have hWnext_nonneg : 0 <= W (k + 1) := by
      linarith [hW_floor k hk]
    have hmul :
        W (k + 1) * appendixDStationarityConsensusTerm S k <=
          W (k + 1) *
            ((1 + appendixDPrintedEquation21Coefficient S L C beta k) *
                appendixDObjectiveGapSeq S k -
              appendixDObjectiveGapSeq S (k + 1) +
                appendixDPrintedEquation21ConsensusBudgetTerm S k) :=
      mul_le_mul_of_nonneg_left (hrecurrence k) hWnext_nonneg
    dsimp [A, Cseq]
    rw [← hW_succ k hk]
    nlinarith
  have hweighted_sum :
      (Finset.range K.1).sum
          (fun k => W (k + 1) * appendixDStationarityConsensusTerm S k) <=
        appendixDObjectiveGapSeq S 0 +
          (Finset.range K.1).sum
            (fun k => W (k + 1) *
              appendixDPrintedEquation21ConsensusBudgetTerm S k) := by
    have hfull :
        (Finset.range K.1).sum
            (fun k => W (k + 1) * appendixDStationarityConsensusTerm S k) +
            W K.1 * appendixDObjectiveGapSeq S K.1 <=
          (Finset.range K.1).sum
              (fun k => W (k + 1) *
                appendixDPrintedEquation21ConsensusBudgetTerm S k) +
            appendixDObjectiveGapSeq S 0 := by
      simpa [A, Cseq, add_comm, add_left_comm, add_assoc] using hweighted_full
    linarith
  have hS_nonneg :
      forall k, k < K.1 -> 0 <= appendixDStationarityConsensusTerm S k := by
    intro k _hk
    have hgamma_nonneg : 0 <= (S.gamma : Real) := le_of_lt S.gamma.property
    have hterm_grad :
        0 <=
          (S.gamma : Real) / 6 *
            ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) := by
      exact mul_nonneg (div_nonneg hgamma_nonneg (by norm_num)) (sq_nonneg _)
    have hterm_cons :
        0 <=
          24 / (S.gamma : Real) *
            ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat) := by
      exact mul_nonneg (div_nonneg (by norm_num) hgamma_nonneg) (sq_nonneg _)
    unfold appendixDStationarityConsensusTerm
    exact add_nonneg hterm_grad hterm_cons
  have hfloor_sum :
      (1 / 3 : Real) *
          (Finset.range K.1).sum (appendixDStationarityConsensusTerm S) <=
        (Finset.range K.1).sum
          (fun k => W (k + 1) * appendixDStationarityConsensusTerm S k) := by
    calc
      (1 / 3 : Real) *
          (Finset.range K.1).sum (appendixDStationarityConsensusTerm S) =
          (Finset.range K.1).sum
            (fun k => (1 / 3 : Real) * appendixDStationarityConsensusTerm S k) := by
            rw [Finset.mul_sum]
      _ <=
          (Finset.range K.1).sum
            (fun k => W (k + 1) * appendixDStationarityConsensusTerm S k) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_right
              (hW_floor k (Finset.mem_range.mp hk))
              (hS_nonneg k (Finset.mem_range.mp hk))
  have hweighted_budget :
      (Finset.range K.1).sum
          (fun k => W (k + 1) *
            appendixDPrintedEquation21ConsensusBudgetTerm S k) <=
        (Finset.range K.1).sum (appendixDConsensusBudgetTerm S) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hW_budget k (Finset.mem_range.mp hk)
  have hcore :
      (1 / 3 : Real) *
          (Finset.range K.1).sum (appendixDStationarityConsensusTerm S) <=
        appendixDObjectiveGapSeq S 0 +
          (Finset.range K.1).sum (appendixDConsensusBudgetTerm S) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : Real) <= 3)
  simpa [appendixDStationarityConsensusTerm, appendixDObjectiveGapSeq,
    appendixDConsensusBudgetTerm, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm,
    mul_comm] using hscaled

private theorem sum_range_le_sum_range_succ_of_zero_terminal_nonneg
    (K : Nat) (C : Nat -> Real) (hC0 : C 0 = 0) (hterminal_nonneg : 0 <= C K) :
    (Finset.range K).sum C <= (Finset.range K).sum (fun k => C (k + 1)) := by
  cases K with
  | zero => simp
  | succ K =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ, hC0]
      linarith

/-- The equation-(23) cancellation step after Appendix D's scalar absorption.
It removes the shifted consensus budget using consensual initialization and
then divides by the positive constant stepsize. -/
private theorem appendixD_cancel_shifted_consensus_budget
    (Delta : Real) (K : PositiveHorizon)
    (hinitial_objective_gap :
      objective S S.x0 - nodeAverage (fun i => componentInfimumValue S i) <= Delta)
    (hmean_zero : meanIterate S 0 = S.x0)
    (hinitial_consensus : consensusError S (iterate S 0) = 0)
    (hbudget :
      (Finset.range K.1).sum
          (fun k =>
            (S.gamma : Real) / 6 *
                ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) +
              24 / (S.gamma : Real) *
                ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat)) <=
        3 * (objective S (meanIterate S 0) -
              nodeAverage (fun i => componentInfimumValue S i)) +
          3 * (Finset.range K.1).sum
            (fun k =>
              8 / (S.gamma : Real) *
                ‖consensusError S (iterate S k)‖ ^ (2 : Nat))) :
    (Finset.range K.1).sum
        (fun k => ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat)) <=
      18 * Delta / (S.gamma : Real) := by
  let G : Nat -> Real :=
    fun k => ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat)
  let C : Nat -> Real :=
    fun k => ‖consensusError S (iterate S k)‖ ^ (2 : Nat)
  have hgamma_pos : 0 < (S.gamma : Real) := S.gamma.property
  have hgamma_ne : (S.gamma : Real) ≠ 0 := ne_of_gt hgamma_pos
  have hC0 : C 0 = 0 := by
    simp [C, hinitial_consensus]
  have hterminal_nonneg : 0 <= C K.1 := by
    exact sq_nonneg _
  have hshift :
      (Finset.range K.1).sum C <=
        (Finset.range K.1).sum (fun k => C (k + 1)) :=
    sum_range_le_sum_range_succ_of_zero_terminal_nonneg
      (K := K.1) (C := C) hC0 hterminal_nonneg
  have hcons_coeff_nonneg : 0 <= 24 / (S.gamma : Real) := by positivity
  have hshift_scaled :
      24 / (S.gamma : Real) * (Finset.range K.1).sum C <=
        24 / (S.gamma : Real) *
          (Finset.range K.1).sum (fun k => C (k + 1)) :=
    mul_le_mul_of_nonneg_left hshift hcons_coeff_nonneg
  have hbudget' :
      (S.gamma : Real) / 6 * (Finset.range K.1).sum G +
          24 / (S.gamma : Real) *
            (Finset.range K.1).sum (fun k => C (k + 1)) <=
        3 * (objective S (meanIterate S 0) -
              nodeAverage (fun i => componentInfimumValue S i)) +
          24 / (S.gamma : Real) * (Finset.range K.1).sum C := by
    have hbudget_tmp :
        (S.gamma : Real) / 6 * (Finset.range K.1).sum G +
            24 / (S.gamma : Real) *
              (Finset.range K.1).sum (fun k => C (k + 1)) <=
          3 * (objective S (meanIterate S 0) -
                nodeAverage (fun i => componentInfimumValue S i)) +
            (Finset.range K.1).sum
              (fun k => 3 * (8 / (S.gamma : Real) * C k)) := by
      simpa [G, C, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm,
        mul_comm] using hbudget
    have hFsum :
        (Finset.range K.1).sum
            (fun k => 3 * (8 / (S.gamma : Real) * C k)) =
          24 / (S.gamma : Real) * (Finset.range K.1).sum C := by
      calc
        (Finset.range K.1).sum
            (fun k => 3 * (8 / (S.gamma : Real) * C k)) =
            3 * (Finset.range K.1).sum
              (fun k => 8 / (S.gamma : Real) * C k) := by
              rw [Finset.mul_sum]
        _ = 3 * (8 / (S.gamma : Real) * (Finset.range K.1).sum C) := by
              rw [← Finset.mul_sum]
        _ = 24 / (S.gamma : Real) * (Finset.range K.1).sum C := by
              ring
    simpa [hFsum] using hbudget_tmp
  have hDelta0_le :
      objective S (meanIterate S 0) -
          nodeAverage (fun i => componentInfimumValue S i) <= Delta := by
    simpa [hmean_zero] using hinitial_objective_gap
  have hcore :
      (S.gamma : Real) / 6 * (Finset.range K.1).sum G <= 3 * Delta := by
    linarith
  calc
    (Finset.range K.1).sum G =
        (6 / (S.gamma : Real)) *
          ((S.gamma : Real) / 6 * (Finset.range K.1).sum G) := by
          field_simp [hgamma_ne]
    _ <= (6 / (S.gamma : Real)) * (3 * Delta) := by
          exact mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 18 * Delta / (S.gamma : Real) := by
          ring

/-- The Theorem 2 stepsize supports the printed Lemma 6 coefficient
`8 n C_W^2 L`, while the coefficient visible in Appendix D equation (21) would
only be bounded by `5/3` under the same stepsize. -/
private theorem theorem2_stepsize_printed_and_equation21_coefficients
    {gamma n C L : Real}
    (hgamma_pos : 0 < gamma) (hn_pos : 0 < n) (hC_pos : 0 < C)
    (hL_nonneg : 0 <= L)
    (hstepsize : gamma <= 1 / (24 * n * C ^ (2 : Nat) * L)) :
    gamma * (8 * n * C ^ (2 : Nat) * L) <= 1 / 3 /\
      gamma * (40 * n * C ^ (2 : Nat) * L) <= 5 / 3 := by
  have hL_pos : 0 < L := by
    by_contra hnot
    have hL_zero : L = 0 := le_antisymm (le_of_not_gt hnot) hL_nonneg
    have hgamma_nonpos : gamma <= 0 := by
      simpa [hL_zero] using hstepsize
    linarith
  have hD_pos : 0 < 24 * n * C ^ (2 : Nat) * L := by positivity
  have hD_ne : 24 * n * C ^ (2 : Nat) * L ≠ 0 := ne_of_gt hD_pos
  constructor
  · have hfactor_nonneg : 0 <= 8 * n * C ^ (2 : Nat) * L := by positivity
    have hmul := mul_le_mul_of_nonneg_right hstepsize hfactor_nonneg
    field_simp [hD_ne] at hmul
    nlinarith
  · have hfactor_nonneg : 0 <= 40 * n * C ^ (2 : Nat) * L := by positivity
    have hmul := mul_le_mul_of_nonneg_right hstepsize hfactor_nonneg
    field_simp [hD_ne] at hmul
    nlinarith

/-- At the exact chosen Theorem 2 stepsize, the Lemma-6-ready coefficient
normalizes to `1/3`, but the coefficient printed in Appendix D equation (21)
normalizes to `5/3`.  This is the compiled scalar source-boundary obstruction:
the displayed equation-(21) coefficient cannot be silently used as the smaller
coefficient required by the active absorption route. -/
private theorem theorem2_chosen_stepsize_printed_equation21_coefficient_exact
    {gamma n C L : Real}
    (hn_pos : 0 < n) (hC_pos : 0 < C) (hL_pos : 0 < L)
    (hstepsize : gamma = 1 / (24 * n * C ^ (2 : Nat) * L)) :
    gamma * (8 * n * C ^ (2 : Nat) * L) = 1 / 3 /\
      gamma * (40 * n * C ^ (2 : Nat) * L) = 5 / 3 := by
  have hD_pos : 0 < 24 * n * C ^ (2 : Nat) * L := by positivity
  have hD_ne : 24 * n * C ^ (2 : Nat) * L ≠ 0 := ne_of_gt hD_pos
  constructor
  · rw [hstepsize]
    field_simp [hD_ne]
    ring
  · rw [hstepsize]
    field_simp [hD_ne]
    ring

private theorem theorem2_chosen_stepsize_printed_equation21_coefficient_too_large
    {gamma n C L : Real}
    (hn_pos : 0 < n) (hC_pos : 0 < C) (hL_pos : 0 < L)
    (hstepsize : gamma = 1 / (24 * n * C ^ (2 : Nat) * L)) :
    ¬ gamma * (40 * n * C ^ (2 : Nat) * L) <= 1 / 3 := by
  have hcoeff :=
    theorem2_chosen_stepsize_printed_equation21_coefficient_exact
      (gamma := gamma) (n := n) (C := C) (L := L)
      hn_pos hC_pos hL_pos hstepsize
  rw [hcoeff.2]
  norm_num

/-- Final scalar normalization from the Appendix-D stationarity sum estimate to
the positive-horizon averaged stationarity statement. -/
private theorem theorem2_stationarity_average_bound_of_sum_bound
    (Delta : Real) (K : PositiveHorizon)
    (hsum :
      (Finset.range K.1).sum
          (fun k => ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat)) <=
        18 * Delta / (S.gamma : Real)) :
    Theorem2StationarityBound S Delta K := by
  unfold Theorem2StationarityBound averagedStationarity
  have hK_pos : 0 < (K.1 : Real) := by exact_mod_cast K.2
  have hK_ne : (K.1 : Real) ≠ 0 := ne_of_gt hK_pos
  have hgamma_pos : 0 < (S.gamma : Real) := S.gamma.property
  have hgamma_ne : (S.gamma : Real) ≠ 0 := ne_of_gt hgamma_pos
  have hscale_nonneg : 0 <= (1 : Real) / (K.1 : Real) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hscale_nonneg
  calc
    (1 / (K.1 : Real)) *
        (Finset.range K.1).sum
          (fun k => ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat))
        <= (1 / (K.1 : Real)) * (18 * Delta / (S.gamma : Real)) := hmul
    _ = 18 * Delta / ((S.gamma : Real) * (K.1 : Real)) := by
          field_simp [hK_ne, hgamma_ne]

/-- Corrected separate-constant Appendix-D stationarity supplier.

This is the proof-ready replacement boundary for the unsupported same-`C_W`
Theorem 2 stationarity route. It keeps Theorem 2's source assumptions and
corrected schedule boundary, but consumes the Appendix-D objects at their
source granularity: a separate-constant Lemma-6-ready recurrence and the
corresponding M-side absorption weight floor. -/
theorem theorem2_corrected_separate_appendixD_stationarity_bound
    (L Delta C_W beta_W C_A beta_A C_M beta_M : Real)
    (h : Theorem2CorrectedGeneralAssumptions S L Delta C_W beta_W)
    (K : PositiveHorizon)
    (hrecurrence :
      AppendixDSeparateEquation21ReadyRecurrence S L C_A beta_A C_M beta_M)
    (W : Nat -> Real)
    (hweights : AppendixDAbsorptionWeightFloor S L C_M beta_M K W) :
    Theorem2StationarityBound S Delta K := by
  have hbudget :
      (Finset.range K.1).sum
          (fun k =>
            (S.gamma : Real) / 6 *
                ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat) +
              24 / (S.gamma : Real) *
                ‖consensusError S (iterate S (k + 1))‖ ^ (2 : Nat)) <=
        3 * (objective S (meanIterate S 0) -
              nodeAverage (fun i => componentInfimumValue S i)) +
          3 * (Finset.range K.1).sum
            (fun k =>
              8 / (S.gamma : Real) *
                ‖consensusError S (iterate S k)‖ ^ (2 : Nat)) :=
    appendixD_absorbed_budget_of_separate_equation21_ready_recurrence
      (S := S) L C_A beta_A C_M beta_M K hrecurrence W hweights
  have hsum :
      (Finset.range K.1).sum
          (fun k => ‖objectiveGradient S (meanIterate S k)‖ ^ (2 : Nat)) <=
        18 * Delta / (S.gamma : Real) :=
    appendixD_cancel_shifted_consensus_budget
      (S := S) Delta K
      (objective_initial_gap_le_delta (S := S) h.1.2.1)
      (meanIterate_zero (S := S))
      (consensusError_iterate_zero (S := S))
      hbudget
  exact theorem2_stationarity_average_bound_of_sum_bound (S := S) Delta K hsum

/-- The positive-index Theorem 2 schedule is strong enough to give the
standard contraction estimate `beta^R <= 1/k`.  This isolates the denominator
bridge from the paper's `1 - beta` schedule to the exact negative-log
contraction schedule used by scalar power lemmas. -/
private theorem theorem2_positive_schedule_beta_pow_le_inv
    {C beta : Real} {k R : Nat} (hk : 0 < k)
    (hbeta_pos : 0 < beta) (hbeta_lt : beta < 1)
    (hR : theorem2ScheduleLowerBound C beta ⟨k, hk⟩ <= (R : Real)) :
    beta ^ R <= (k : Real)⁻¹ := by
  have hk_real_pos : 0 < (k : Real) := by exact_mod_cast hk
  have hk_real_ge_one : 1 <= (k : Real) := by
    exact_mod_cast Nat.succ_le_of_lt hk
  have hlogk_nonneg : 0 <= Real.log (k : Real) := Real.log_nonneg hk_real_ge_one
  have hd_pos : 0 < 1 - beta := by linarith
  have hright :
      Real.log (k : Real) / (1 - beta) <= (R : Real) := by
    exact le_trans (le_max_right _ _) hR
  have hlog_beta_neg : Real.log beta < 0 :=
    (Real.log_neg_iff hbeta_pos).mpr hbeta_lt
  have hlog_beta_ne : Real.log beta ≠ 0 := ne_of_lt hlog_beta_neg
  have hneglog_pos : 0 < -Real.log beta := by linarith
  have hlog_le : Real.log beta <= beta - 1 :=
    Real.log_le_sub_one_of_pos hbeta_pos
  have hden_le : 1 - beta <= -Real.log beta := by linarith
  have hinv_le : (-Real.log beta)⁻¹ <= (1 - beta)⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hd_pos hden_le
  have hbridge_pos :
      Real.log (k : Real) / (-Real.log beta) <=
        Real.log (k : Real) / (1 - beta) := by
    have hmul := mul_le_mul_of_nonneg_left hinv_le hlogk_nonneg
    simpa [div_eq_mul_inv] using hmul
  have hbridge :
      -Real.log (k : Real) / Real.log beta <=
        Real.log (k : Real) / (1 - beta) := by
    calc
      -Real.log (k : Real) / Real.log beta =
          Real.log (k : Real) / (-Real.log beta) := by
            field_simp [hlog_beta_ne]
      _ <= Real.log (k : Real) / (1 - beta) := hbridge_pos
  exact pow_nat_le_inv_of_neg_log_div_log_le hbeta_pos hbeta_lt hk_real_pos
    (le_trans hbridge hright)

/-- Source-boundary replacement record for the unqualified Theorem 2
stationarity statement.

This helper has the same theorem-level inputs as the old unqualified
stationarity-bound endpoint, but it does not claim the stationarity bound.
Instead it exposes the compiled boundary obstruction
derivable from the printed Theorem 2 assumptions: the same-`C_W` Appendix-D
route forces a larger M-side constant, and the printed equation-(21)
coefficient does not match the Lemma-6-ready coefficient used by the absorption
step. -/
private theorem theorem2_corrected_general_stationarity_bound_unsupported_source_boundary
    (L Delta C_W beta_W : Real)
    (_h : Theorem2CorrectedGeneralAssumptions S L Delta C_W beta_W)
    (_K : PositiveHorizon) :
    Theorem2StationarityUnsupportedSourceBoundary S L C_W beta_W := by
  exact theorem2_stationarity_unsupported_source_boundary
    (S := S) (L := L) (Delta := Delta) (C := C_W) (beta := beta_W) _h.1

/-- Source-boundary replacement record for the chosen-stepsize Theorem 2
stationarity statement.

This is the chosen-schedule analogue of
`theorem2_corrected_general_stationarity_bound_unsupported_source_boundary`.
It is kept private so the public release cone uses the explicit
`theorem2_corrected_chosen_stationarity_source_gap` endpoint. -/
private theorem theorem2_corrected_chosen_stationarity_bound_unsupported_source_boundary
    (L Delta C_W beta_W : Real)
    (_h : Theorem2CorrectedChosenAssumptions S L Delta C_W beta_W)
    (_K : PositiveHorizon) :
    Theorem2StationarityUnsupportedSourceBoundary S L C_W beta_W := by
  exact theorem2_stationarity_unsupported_source_boundary
    (S := S) (L := L) (Delta := Delta) (C := C_W) (beta := beta_W) _h.1

/-- Source-boundary replacement record for the final `O(log T / T)` theorem.

The overall communication-rate conclusion depends on the chosen stationarity
estimate.  Under the current C_W-only theorem boundary, that estimate is
unsupported for the same Appendix-D reasons recorded here; this diagnostic
keeps the final theorem from depending transitively on the unsupported general
stationarity theorem while source approval is pending. -/
private theorem theorem2_corrected_overall_communication_rate_unsupported_source_boundary
    (L Delta C_W beta_W : Real)
    (_h : Theorem2CorrectedChosenAssumptions S L Delta C_W beta_W) :
    Theorem2StationarityUnsupportedSourceBoundary S L C_W beta_W := by
  exact theorem2_stationarity_unsupported_source_boundary
    (S := S) (L := L) (Delta := Delta) (C := C_W) (beta := beta_W) _h.1

/-- Source-gap endpoint for the unqualified corrected Theorem 2 stationarity
claim.

The same inputs previously led to the stationarity estimate, but the current
source/object model does not supply the Appendix-D projected A/M bridge or the
coefficient bridge needed for that estimate.  This public endpoint therefore
concludes the concrete unsupported-source-boundary proposition over the actual
Algorithm 3 setup and theorem constants. -/
theorem theorem2_corrected_general_stationarity_source_gap
    (L Delta C_W beta_W : Real)
    (_h : Theorem2CorrectedGeneralAssumptions S L Delta C_W beta_W)
    (K : PositiveHorizon) :
    Theorem2StationarityUnsupportedSourceBoundary S L C_W beta_W := by
  exact theorem2_corrected_general_stationarity_bound_unsupported_source_boundary
    (S := S) L Delta C_W beta_W _h K

/-- Source-gap endpoint for the chosen stationarity claim.

The corrected chosen assumptions still imply the same Appendix-D diagnostic,
but they do not prove the chosen stationarity estimate.  This public endpoint
exposes that gap directly instead of wrapping it in a theorem-like retirement
certificate. -/
theorem theorem2_corrected_chosen_stationarity_source_gap
    (L Delta C_W beta_W : Real)
    (_h : Theorem2CorrectedChosenAssumptions S L Delta C_W beta_W)
    (K : PositiveHorizon) :
    Theorem2StationarityUnsupportedSourceBoundary S L C_W beta_W := by
  exact theorem2_corrected_chosen_stationarity_bound_unsupported_source_boundary
    (S := S) L Delta C_W beta_W _h K

/-- Source-boundary record for the printed general Theorem 2 stationarity
claim.  The literal printed schedule condition is not realizable on the
zero-based averaging window, so this declaration intentionally does not
conclude the stationarity estimate. -/
theorem theorem2_printed_general_stationarity_schedule_gap
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (K : PositiveHorizon) :
    ¬ Theorem2PrintedScheduleCondition S L C_W beta_W K := by
  exact Theorem2PrintedScheduleCondition.not_realizable (S := S) L C_W beta_W K

/-- Source-boundary record for the printed chosen-schedule equation (5).
As above, the literal printed schedule is a non-realizable source boundary on
positive zero-based horizons, not a premise from which Lean should prove the
chosen stationarity estimate by contradiction. -/
theorem theorem2_printed_chosen_stationarity_schedule_gap
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (_hstepsize : Theorem2ChosenStepsize S L C_W)
    (K : PositiveHorizon) :
    ¬ Theorem2ChosenPrintedScheduleCondition S L C_W beta_W K := by
  exact Theorem2ChosenPrintedScheduleCondition.not_realizable (S := S) L C_W beta_W K

/-- Positive-index communication rounds from the displayed sum
`sum_{k=1}^{K-1}`.  This is separated from `communicationRounds`, which follows
the paper's total `sum_{k=0}^{K-1} R_k` and therefore includes the unresolved
`R_0` boundary. -/
def positiveCommunicationRounds (S : Setup Node E) (K : Nat) : Nat :=
  (Finset.Icc 1 (K - 1)).sum (fun k => S.innerRounds k)

/-- The number of positive-index schedule terms in the displayed
`sum_{k=1}^{K-1}` communication expression. -/
def positiveCommunicationTermCount (K : Nat) : Nat :=
  (Finset.Icc 1 (K - 1)).card

/-- Explicit overhead for replacing the paper's real-valued positive-index
schedule by natural communication counts.  The paper does not state this
rounding term; it is part of the corrected Lean boundary. -/
def positiveCommunicationCeilingOverhead (K : Nat) : Real :=
  2 * (positiveCommunicationTermCount K : Real)

/-- The real-valued logarithmic communication display printed after equation
(5), restricted to the positive-index sum that the PDF actually estimates.
The PDF display in `paper/2512.24483v1.pdf`, Theorem 2, lines 642-651, starts
the logarithmic sums at `k = 1` although the preceding total is
`sum_{k=0}^{K-1} R_k`. -/
def theorem2PositiveCommunicationDisplay (C_W beta_W : Real)
    (K : PositiveHorizon) : Real :=
  max ((K.1 : Real) * Real.log (K.1 : Real))
      ((K.1 : Real) * Real.log C_W) / (1 - beta_W)

/-- Scalar accounting for the positive-index natural ceiling schedule in
Theorem 2.  This is independent of the algorithmic `Setup`: the only analytic
input is the mixing-rate denominator condition `beta_W < 1`. -/
private theorem sum_ceil_theorem2_positive_schedule_le_display_add_overhead
    (C_W beta_W : Real) (K : PositiveHorizon) (hbeta_lt : beta_W < 1) :
    (((Finset.Icc 1 (K.1 - 1)).sum (fun k =>
      Nat.ceil (max (Real.log C_W / (1 - beta_W))
        (Real.log (k : Real) / (1 - beta_W)))) : Nat) : Real) <=
      theorem2PositiveCommunicationDisplay C_W beta_W K +
        positiveCommunicationCeilingOverhead K.1 := by
  let d : Real := 1 - beta_W
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  have hd_nonneg : 0 <= d := le_of_lt hd_pos
  have hK_nat_pos : 0 < K.1 := K.2
  have hK_nonneg : 0 <= (K.1 : Real) := by positivity
  have hK_ge_one : 1 <= (K.1 : Real) := by
    exact_mod_cast Nat.succ_le_of_lt hK_nat_pos
  have hlogK_nonneg : 0 <= Real.log (K.1 : Real) :=
    Real.log_nonneg hK_ge_one
  let M : Real := max (Real.log C_W / d) (Real.log (K.1 : Real) / d)
  have hM_nonneg : 0 <= M := by
    dsimp [M]
    have hbranch : 0 <= Real.log (K.1 : Real) / d :=
      div_nonneg hlogK_nonneg hd_nonneg
    exact le_trans hbranch (le_max_right _ _)
  have hpoint : ∀ k, k ∈ Finset.Icc 1 (K.1 - 1) ->
      (Nat.ceil (max (Real.log C_W / d) (Real.log (k : Real) / d)) : Real) <=
        M + 2 := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk_one, hk_le_pred⟩
    have hk_pos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk_one
    have hk_real_pos : 0 < (k : Real) := by exact_mod_cast hk_pos
    have hk_ge_one : 1 <= (k : Real) := by exact_mod_cast hk_one
    have hk_le_K : k <= K.1 := le_trans hk_le_pred (Nat.sub_le K.1 1)
    have hk_real_le_K : (k : Real) <= (K.1 : Real) := by exact_mod_cast hk_le_K
    have hlogk_nonneg : 0 <= Real.log (k : Real) :=
      Real.log_nonneg hk_ge_one
    have hlog_le : Real.log (k : Real) <= Real.log (K.1 : Real) :=
      Real.log_le_log hk_real_pos hk_real_le_K
    have hdiv_le : Real.log (k : Real) / d <= Real.log (K.1 : Real) / d :=
      div_le_div_of_nonneg_right hlog_le hd_nonneg
    have hy_nonneg :
        0 <= max (Real.log C_W / d) (Real.log (k : Real) / d) := by
      have hbranch : 0 <= Real.log (k : Real) / d :=
        div_nonneg hlogk_nonneg hd_nonneg
      exact le_trans hbranch (le_max_right _ _)
    have hy_le :
        max (Real.log C_W / d) (Real.log (k : Real) / d) <= M := by
      dsimp [M]
      exact max_le (le_max_left _ _) (le_trans hdiv_le (le_max_right _ _))
    have hceil :
        (Nat.ceil (max (Real.log C_W / d) (Real.log (k : Real) / d)) : Real) <=
          max (Real.log C_W / d) (Real.log (k : Real) / d) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one hy_nonneg)
    linarith
  have hsum_point :
      ((Finset.Icc 1 (K.1 - 1)).sum (fun k =>
        (Nat.ceil (max (Real.log C_W / d) (Real.log (k : Real) / d)) : Real))) <=
        ((Finset.Icc 1 (K.1 - 1)).card : Real) * (M + 2) := by
    calc
      ((Finset.Icc 1 (K.1 - 1)).sum (fun k =>
          (Nat.ceil (max (Real.log C_W / d) (Real.log (k : Real) / d)) : Real)))
          <= (Finset.Icc 1 (K.1 - 1)).sum (fun _ => M + 2) := by
            exact Finset.sum_le_sum hpoint
      _ = ((Finset.Icc 1 (K.1 - 1)).card : Real) * (M + 2) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
  have hcard_le_nat : (Finset.Icc 1 (K.1 - 1)).card <= K.1 := by
    have hsubset : Finset.Icc 1 (K.1 - 1) ⊆ Finset.range K.1 := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_of_le_pred hK_nat_pos (Finset.mem_Icc.mp hk).2)
    calc
      (Finset.Icc 1 (K.1 - 1)).card <= (Finset.range K.1).card :=
        Finset.card_le_card hsubset
      _ = K.1 := Finset.card_range K.1
  have hcard_le : ((Finset.Icc 1 (K.1 - 1)).card : Real) <= (K.1 : Real) := by
    exact_mod_cast hcard_le_nat
  have hM_eq : M = max (Real.log C_W) (Real.log (K.1 : Real)) / d := by
    dsimp [M]
    rw [max_div_div_right hd_nonneg]
  have hdisplay_dom :
      ((Finset.Icc 1 (K.1 - 1)).card : Real) * M <=
        theorem2PositiveCommunicationDisplay C_W beta_W K := by
    calc
      ((Finset.Icc 1 (K.1 - 1)).card : Real) * M <= (K.1 : Real) * M := by
        exact mul_le_mul_of_nonneg_right hcard_le hM_nonneg
      _ = (K.1 : Real) * (max (Real.log C_W) (Real.log (K.1 : Real)) / d) := by
        rw [hM_eq]
      _ = max ((K.1 : Real) * Real.log (K.1 : Real))
            ((K.1 : Real) * Real.log C_W) / d := by
        calc
          (K.1 : Real) * (max (Real.log C_W) (Real.log (K.1 : Real)) / d)
              = ((K.1 : Real) * max (Real.log C_W) (Real.log (K.1 : Real))) / d := by
                ring
          _ = max ((K.1 : Real) * Real.log C_W)
                ((K.1 : Real) * Real.log (K.1 : Real)) / d := by
                rw [mul_max_of_nonneg _ _ hK_nonneg]
          _ = max ((K.1 : Real) * Real.log (K.1 : Real))
                ((K.1 : Real) * Real.log C_W) / d := by
                rw [max_comm]
  calc
    (((Finset.Icc 1 (K.1 - 1)).sum (fun k =>
      Nat.ceil (max (Real.log C_W / (1 - beta_W))
        (Real.log (k : Real) / (1 - beta_W)))) : Nat) : Real)
        = ((Finset.Icc 1 (K.1 - 1)).sum (fun k =>
          (Nat.ceil (max (Real.log C_W / d) (Real.log (k : Real) / d)) : Real))) := by
          simp [d, Nat.cast_sum]
    _ <= ((Finset.Icc 1 (K.1 - 1)).card : Real) * (M + 2) := hsum_point
    _ = ((Finset.Icc 1 (K.1 - 1)).card : Real) * M +
        positiveCommunicationCeilingOverhead K.1 := by
          simp [positiveCommunicationCeilingOverhead, positiveCommunicationTermCount,
            mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc]
    _ <= theorem2PositiveCommunicationDisplay C_W beta_W K +
        positiveCommunicationCeilingOverhead K.1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hdisplay_dom (positiveCommunicationCeilingOverhead K.1)

/-- The paper's total communication count is the Algorithm 3 sum
`sum_{k=0}^{K-1} R_k`; for positive horizons it separates into the unresolved
`R_0` contribution plus the positive-index display used in the PDF. -/
theorem communicationRounds_eq_R0_add_positiveCommunicationRounds (K : PositiveHorizon) :
    communicationRounds S K.1 = S.innerRounds 0 + positiveCommunicationRounds S K.1 := by
  rcases K with ⟨K, hK⟩
  cases K with
  | zero => cases hK
  | succ n =>
      rw [communicationRounds, positiveCommunicationRounds, Nat.succ_sub_one, Finset.sum_range_succ',
        sum_Icc_one_eq_sum_range_succ]
      rw [add_comm]

/-- Under the chosen positive-index natural schedule, the positive
communication total is exactly the scalar ceiling sum used by the Theorem 2
display. -/
private theorem positive_schedule_rewrites_round_sum_to_scalar_ceil_sum
    (C_W beta_W : Real) (K : PositiveHorizon)
    (hschedule : Theorem2ChosenPositiveSchedule S C_W beta_W) :
    positiveCommunicationRounds S K.1 =
      (Finset.Icc 1 (K.1 - 1)).sum (fun k =>
        Nat.ceil (max (Real.log C_W / (1 - beta_W))
          (Real.log (k : Real) / (1 - beta_W)))) := by
  unfold positiveCommunicationRounds
  apply Finset.sum_congr rfl
  intro k hk
  have hk_pos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
  rw [hschedule ⟨k, hk_pos⟩]
  simp [theorem2ChosenPositiveInnerRounds, theorem2ScheduleLowerBound]

/-- The positive-index communication-round display following equation (5).
This predicate intentionally does not claim the full paper variable
`T = sum_{k=0}^{K-1} R_k`, because the source gives no `R_0` convention for the
chosen logarithmic schedule.

Source quote: `book/LiangSongYuan2025/PullWithMemoryDGD.json#/
main_theorem/statement_math`, `sum_{k=0}^{K-1} R_k <= max{
sum_{k=1}^{K-1} ln(k)/(1-beta_W), sum_{k=1}^{K-1} ln(C_W)/(1-beta_W)}`. -/
def Theorem2PositiveCommunicationRoundBound (S : Setup Node E) (C_W beta_W : Real)
    (K : PositiveHorizon) : Prop :=
  (positiveCommunicationRounds S K.1 : Real) <=
    theorem2PositiveCommunicationDisplay C_W beta_W K +
      positiveCommunicationCeilingOverhead K.1

/-- Corrected full communication-round bound: the source's zero-based total
`sum_{k=0}^{K-1} R_k` is the unresolved `R_0` contribution plus the
positive-index logarithmic display and the Nat-ceiling overhead absent from the
printed real-valued schedule.

Source boundary: the same JSON theorem statement defines the total as
`sum_{k=0}^{K-1} R_k`, but the displayed estimate starts its logarithmic sums
at `k=1`; this corrected object keeps the missing `R_0` contribution visible. -/
def Theorem2CorrectedCommunicationRoundBound (S : Setup Node E) (C_W beta_W : Real)
    (K : PositiveHorizon) : Prop :=
  (communicationRounds S K.1 : Real) <=
    (S.innerRounds 0 : Real) +
      (theorem2PositiveCommunicationDisplay C_W beta_W K +
        positiveCommunicationCeilingOverhead K.1)

/-- Corrected communication display theorem head for the positive-index
schedule.  This is the proof-ready replacement for treating the PDF's
zero-based total as if the `k = 0` logarithmic schedule were defined. -/
theorem theorem2_corrected_communication_round_bound
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (_hstepsize : Theorem2ChosenStepsize S L C_W)
    (_hschedule : Theorem2ChosenPositiveSchedule S C_W beta_W)
    (K : PositiveHorizon) :
    Theorem2CorrectedCommunicationRoundBound S C_W beta_W K := by
  have hpos :
      (positiveCommunicationRounds S K.1 : Real) <=
        theorem2PositiveCommunicationDisplay C_W beta_W K +
          positiveCommunicationCeilingOverhead K.1 := by
    rw [positive_schedule_rewrites_round_sum_to_scalar_ceil_sum (S := S) C_W beta_W K
      _hschedule]
    exact sum_ceil_theorem2_positive_schedule_le_display_add_overhead C_W beta_W K _hmix.2.2.1
  unfold Theorem2CorrectedCommunicationRoundBound
  rw [communicationRounds_eq_R0_add_positiveCommunicationRounds (S := S) K]
  simpa [Nat.cast_add] using hpos

/-- Positive-index communication display theorem head corresponding exactly to
the `sum_{k=1}^{K-1}` expression printed after equation (5). -/
theorem theorem2_positive_communication_round_bound
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (_hstepsize : Theorem2ChosenStepsize S L C_W)
    (_hschedule : Theorem2ChosenPositiveSchedule S C_W beta_W)
    (K : PositiveHorizon) :
    Theorem2PositiveCommunicationRoundBound S C_W beta_W K := by
  unfold Theorem2PositiveCommunicationRoundBound
  rw [positive_schedule_rewrites_round_sum_to_scalar_ceil_sum (S := S) C_W beta_W K
    _hschedule]
  exact sum_ceil_theorem2_positive_schedule_le_display_add_overhead C_W beta_W K _hmix.2.2.1

/-- Full corrected communication display under the corrected chosen natural
schedule.  This forwards the positive-index communication theorem through the
chosen all-index schedule, whose `k = 0` value is now explicit.  It also keeps
the source's missing `R_0` and natural-rounding overhead visible in the
conclusion.  The full contract includes the corrected chosen schedule, the
positive horizon, and the corrected communication-bound conclusion. -/
theorem theorem2_chosen_corrected_communication_round_bound
    (L Delta C_W beta_W : Real)
    (h : Theorem2CorrectedChosenAssumptions S L Delta C_W beta_W)
    (K : PositiveHorizon) :
    Theorem2CorrectedCommunicationRoundBound S C_W beta_W K := by
  exact theorem2_corrected_communication_round_bound (S := S) L Delta C_W beta_W
    h.1.1 h.1.2.1 h.1.2.2 h.2.1
    (by
      intro k
      rw [h.2.2 k.1]
      simp [theorem2ChosenCorrectedInnerRounds, k.2,
        theorem2ChosenPositiveInnerRounds, theorem2ScheduleLowerBound]) K

/-- The final communication-complexity rate envelope printed after Theorem 2. -/
def theorem2CommunicationRateEnvelope (T : Nat) : Real :=
  Real.log (T : Real) / (T : Real)

/-- The stationarity trace of the canonical Algorithm 3 iterates as a function
of the outer horizon. -/
def theorem2StationarityByOuterHorizon (S : Setup Node E) (K : Nat) : Real :=
  averagedStationarity S K

/-- The `O(ln(T)/T)` conclusion from Theorem 2 tied to Algorithm 3's own total
communication count `T_K = sum_{k=0}^{K-1} R_k`, rather than to an arbitrary
external rate function.

Source quote: `book/LiangSongYuan2025/PullWithMemoryDGD.json#/
main_theorem/rate`, `O(ln(T)/T) in total communication rounds T, via
K=O(T/ln(T)) and the O(1/K) averaged stationarity bound`. -/
def Theorem2OverallCommunicationRate (S : Setup Node E) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun K => theorem2StationarityByOuterHorizon S K)
    (fun K => theorem2CommunicationRateEnvelope (communicationRounds S K))

/-- Source-gap endpoint for the final communication-rate claim.

The final rate depends on the chosen stationarity estimate.  Since that
estimate is unsupported under the Appendix-D source boundary, this endpoint
returns the concrete stationarity source-gap proposition instead of asserting
the final asymptotic rate or a retirement wrapper. -/
theorem theorem2_corrected_overall_communication_rate_source_gap
    (L Delta C_W beta_W : Real)
    (_h : Theorem2CorrectedChosenAssumptions S L Delta C_W beta_W) :
    Theorem2StationarityUnsupportedSourceBoundary S L C_W beta_W := by
  exact theorem2_corrected_overall_communication_rate_unsupported_source_boundary
    (S := S) L Delta C_W beta_W _h

/-- Source-boundary replacement for the previous overall-rate theorem head.
The positive-index schedule does not supply the missing printed `R_0`
condition, so this declaration records the blocker instead of asserting the
paper's final rate. -/
theorem theorem2_overall_rate_missing_R0_boundary
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (_hstepsize : Theorem2ChosenStepsize S L C_W)
    (_hschedule : Theorem2ChosenPositiveSchedule S C_W beta_W)
    (K : PositiveHorizon) :
    ¬ Theorem2PrintedScheduleDefinedOnHorizon C_W beta_W K := by
  exact theorem2PrintedSchedule_not_defined_on_positive_horizon C_W beta_W K

/-- Source-boundary replacement for the previous positive-schedule stationarity
theorem: the positive-index schedule alone cannot be a source-faithful
Theorem 2 hypothesis over the zero-based averaging window, because that window
contains `k = 0`. -/
theorem theorem2_positive_schedule_missing_R0_boundary
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (_hschedule : Theorem2PositiveSchedule S L C_W beta_W)
    (K : PositiveHorizon) :
    ¬ Theorem2PrintedScheduleDefinedOnHorizon C_W beta_W K := by
  exact theorem2PrintedSchedule_not_defined_on_positive_horizon C_W beta_W K

/-- Source-boundary replacement for the previous chosen-positive-schedule
stationarity theorem.  The chosen natural ceiling realizes only the
positive-index part of the printed schedule, so it does not justify the
zero-based Theorem 2 stationarity window or the total communication variable. -/
theorem theorem2_chosen_positive_schedule_missing_R0_boundary
    (L Delta C_W beta_W : Real)
    (_hnetwork : BroadcastNetworkAssumptions S)
    (_hsmooth : SmoothnessAssumption S L Delta)
    (_hmix : UniformPULMMixingRate S C_W beta_W)
    (_hstepsize : Theorem2ChosenStepsize S L C_W)
    (_hschedule : Theorem2ChosenPositiveSchedule S C_W beta_W)
    (K : PositiveHorizon) :
    ¬ Theorem2PrintedScheduleDefinedOnHorizon C_W beta_W K := by
  exact theorem2PrintedSchedule_not_defined_on_positive_horizon C_W beta_W K

end Setup

end PullWithMemoryDGD
