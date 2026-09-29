import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Matrix.Stochastic
import SOptLib.Model.Selection

noncomputable section

open scoped BigOperators Matrix.Module

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: uniform positive lower bound for nonzero entries of a time-varying finite-network mixing matrix; orig was LowerBoundedEntries.
-- generality used: arbitrary node carrier, natural-time-indexed matrix stream over an ordered type with zero, and lower-bound constant; no finiteness, decidability, measure, convexity, smoothness, oracle, topology, normed-space, finite-dimensional hypotheses, or field operations.
-- portable call pattern: decentralized consensus, gossip, and broadcast-network convergence proofs call the same contract for a different time-varying mixing stream and lower-bound constant while the nonzero-entry conclusion stays unchanged.
-- counterargument checked: not paper-local because uniform positivity of nonzero mixing weights is a standard time-varying network assumption; not a pure wrapper because naming the contract keeps broadcast-network assumptions and later entrywise estimates readable.
-- coverage search: lean_search_symbols "time varying matrix nonzero entries lower bound positive tau", "uniform lower bound nonzero weights mixing matrix", and "FiniteNetwork LowerBoundedNonzeroEntries nonzero matrix entries positive lower bound" found only the local PullWithMemoryDGD declaration plus unrelated convex-analysis and schedule lower bounds; lean_leansearch "time varying matrix weights nonzero entries uniformly bounded below by positive tau" found matrix norm and stochastic-matrix upper-bound APIs, but no uniform nonzero-entry lower-bound predicate.
-- minimal hypotheses: all already minimal; the algorithm setup object was replaced by its `mixing` field and no node finiteness or algorithm-state assumptions remain.

/-- A time-varying network mixing stream has a uniform positive lower bound on
all nonzero entries.

`LowerBoundedNonzeroEntries mixing tau` records that `tau` is strictly positive
and every nonzero entry of every matrix `mixing t` is at least `tau`.

Layer: Model | Concept: finite-network nonzero mixing-entry lower bound
Proof: (definitional construction; positive scalar together with an entrywise lower-bound predicate over all times and ordered node pairs)
Source: Mathlib ordered real inequalities and finite-network mixing-matrix assumptions from decentralized optimization
Used in: broadcast-network assumptions for pull-with-memory decentralized gradient descent, where every nonzero row-stochastic communication weight must be uniformly bounded away from zero
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/3
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
def LowerBoundedNonzeroEntries {Node α : Type*} [Zero α] [Preorder α]
    (mixing : Nat -> Node -> Node -> α) (tau : α) : Prop :=
  0 < tau /\ forall t i j, mixing t i j ≠ 0 -> tau <= mixing t i j

/-- The lower-bounded-nonzero-entry contract unfolds to positivity of `tau`
and the pointwise lower bound for every nonzero entry.

Layer: Model | Gap: Level 0 (finite-network nonzero mixing-entry lower-bound unfolding)
Proof: by rfl after unfolding `FiniteNetwork.LowerBoundedNonzeroEntries`.
Source: Mathlib ordered real inequalities and finite-network mixing-matrix assumptions from decentralized optimization
Used in: rewriting broadcast-network weight assumptions into the explicit positive-scalar and entrywise clauses used by matrix-convergence arguments
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/3
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem LowerBoundedNonzeroEntries_def {Node α : Type*} [Zero α] [Preorder α]
    (mixing : Nat -> Node -> Node -> α) (tau : α) :
    LowerBoundedNonzeroEntries mixing tau <->
      0 < tau /\ forall t i j, mixing t i j ≠ 0 -> tau <= mixing t i j := by
  rfl

/-- A lower-bounded-nonzero-entry contract has a strictly positive lower-bound
constant.

Layer: Model | Gap: Level 0 (positive scalar from nonzero mixing-entry lower-bound contract)
Proof: project the first conjunct of `FiniteNetwork.LowerBoundedNonzeroEntries`.
Source: Mathlib ordered real inequalities and finite-network mixing-matrix assumptions from decentralized optimization
Used in: extracting the positive communication-weight floor before applying consensus or accumulated-product estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/3
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem LowerBoundedNonzeroEntries.positive_tau {Node α : Type*} [Zero α] [Preorder α]
    {mixing : Nat -> Node -> Node -> α} {tau : α}
    (h : LowerBoundedNonzeroEntries mixing tau) : 0 < tau :=
  h.1

/-- A lower-bounded-nonzero-entry contract lower-bounds each nonzero matrix
entry by the same positive scalar.

Layer: Model | Gap: Level 0 (entrywise lower bound from nonzero mixing-entry contract)
Proof: project the entrywise conjunct of `FiniteNetwork.LowerBoundedNonzeroEntries` and specialize it to the requested time and ordered node pair.
Source: Mathlib ordered real inequalities and finite-network mixing-matrix assumptions from decentralized optimization
Used in: converting nonzero communication weights in a broadcast-network proof into uniform `tau` lower bounds for consensus and mixing estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/3
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem LowerBoundedNonzeroEntries.entry_lower_bound {Node α : Type*} [Zero α] [Preorder α]
    {mixing : Nat -> Node -> Node -> α} {tau : α}
    (h : LowerBoundedNonzeroEntries mixing tau) (t : Nat) (i j : Node)
    (hij : mixing t i j ≠ 0) : tau <= mixing t i j :=
  h.2 t i j hij

/-- Every nonzero entry in a lower-bounded-nonzero-entry contract is positive.

Layer: Model | Gap: Level 0 (positive nonzero entry from a positive lower-bound contract)
Proof: compose positivity of the uniform lower bound with the entrywise lower-bound clause.
Source: Mathlib preorder transitivity for strict and non-strict inequalities and finite-network mixing-matrix assumptions from decentralized optimization
Used in: recovering strict positivity of active communication weights from a reusable lower-bounded-entry network assumption
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/3
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem LowerBoundedNonzeroEntries.entry_pos {Node α : Type*} [Zero α] [Preorder α]
    {mixing : Nat -> Node -> Node -> α} {tau : α}
    (h : LowerBoundedNonzeroEntries mixing tau) (t : Nat) (i j : Node)
    (hij : mixing t i j ≠ 0) : 0 < mixing t i j :=
  lt_of_lt_of_le h.positive_tau (h.entry_lower_bound t i j hij)

-- Generalization plan (G0):
-- concept/name: uniform geometric mixing rate for a two-parameter finite-network matrix family; orig was UniformPULMMixingRate.
-- generality used: arbitrary node carrier, an explicit real-valued matrix norm functional, a two-parameter matrix family, a limiting matrix, and real constants; no finiteness, decidability, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are needed by the predicate itself.
-- portable call pattern: decentralized consensus, push-pull, gossip, and pull-with-memory proofs call the same contract while changing the matrix family, limiting matrix, norm functional, and geometric constants.
-- counterargument checked: not paper-local because uniform geometric contraction of mixing-matrix error is a standard reusable network assumption; not a pure wrapper because it packages the positivity, contraction-factor, and all-time operator-bound clauses consumed together by consensus estimates.
-- coverage search: lean_search_symbols "uniform geometric matrix two norm bound mixing rate positive beta less than one", "matrixTwoNorm time varying matrix minus limit geometric rate C beta", and "UniformGeometricMixingRate uniform geometric mixing rate" found only the local PullWithMemoryDGD predicate plus unrelated geometric-rate algebra; lean_leansearch "uniform geometric mixing rate operator norm matrix product minus limiting matrix bounded by C beta to the r" found Mathlib analytic/geometric-series and matrix operator-norm facts but no finite-network mixing-rate predicate.
-- minimal hypotheses: the algorithm setup object was replaced by its matrix family and limiting matrix; the matrix norm is explicit to preserve caller-specific norm choices while avoiding any formula-equality hypothesis.

/-- A two-parameter finite-network matrix family converges to a limiting matrix
at a uniform geometric rate under a supplied matrix norm.

`UniformGeometricMixingRate matrixNorm W Ainf C beta` records that `C` is
positive, `beta` lies in `[0, 1)`, and every matrix error `W k r - Ainf` is
bounded by `C * beta ^ r`.

Layer: Model | Concept: finite-network uniform geometric mixing rate
Proof: (definitional construction; positive prefactor, nonnegative contraction factor below one, and a pointwise geometric matrix-error bound)
Source: finite-network consensus and matrix-product contraction assumptions from decentralized optimization
Used in: converting a pull-with-memory matrix convergence assumption into reusable vector and node-state consensus-error estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/definitions/2
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
def UniformGeometricMixingRate {Node : Type*}
    (matrixNorm : (Node -> Node -> Real) -> Real)
    (W : Nat -> Nat -> Node -> Node -> Real) (Ainf : Node -> Node -> Real)
    (C beta : Real) : Prop :=
  0 < C /\
    0 <= beta /\ beta < 1 /\
      forall k r, matrixNorm (fun i j => W k r i j - Ainf i j) <= C * beta ^ r

/-- The uniform-geometric-mixing-rate contract unfolds to positivity of the
prefactor, a contraction factor in `[0, 1)`, and the pointwise matrix-error
bound.

Layer: Model | Gap: Level 0 (finite-network geometric mixing-rate unfolding)
Proof: by rfl after unfolding `FiniteNetwork.UniformGeometricMixingRate`.
Source: finite-network consensus and matrix-product contraction assumptions from decentralized optimization
Used in: rewriting a network mixing-rate assumption into the scalar and pointwise clauses used by consensus estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/definitions/2
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem UniformGeometricMixingRate_def {Node : Type*}
    (matrixNorm : (Node -> Node -> Real) -> Real)
    (W : Nat -> Nat -> Node -> Node -> Real) (Ainf : Node -> Node -> Real)
    (C beta : Real) :
    UniformGeometricMixingRate matrixNorm W Ainf C beta <->
      0 < C /\
        0 <= beta /\ beta < 1 /\
          forall k r, matrixNorm (fun i j => W k r i j - Ainf i j) <= C * beta ^ r := by
  rfl

/-- A uniform-geometric-mixing-rate contract has a strictly positive prefactor.

Layer: Model | Gap: Level 0 (positive prefactor from geometric mixing-rate contract)
Proof: project the first conjunct of `FiniteNetwork.UniformGeometricMixingRate`.
Source: ordered real inequalities and finite-network matrix contraction assumptions from decentralized optimization
Used in: extracting the positive mixing-rate constant before communication-schedule and consensus-error estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/definitions/2
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem UniformGeometricMixingRate.positive_constant {Node : Type*}
    {matrixNorm : (Node -> Node -> Real) -> Real}
    {W : Nat -> Nat -> Node -> Node -> Real} {Ainf : Node -> Node -> Real}
    {C beta : Real} (h : UniformGeometricMixingRate matrixNorm W Ainf C beta) :
    0 < C :=
  h.1

/-- A uniform-geometric-mixing-rate contract has a nonnegative contraction
factor.

Layer: Model | Gap: Level 0 (nonnegative contraction factor from geometric mixing-rate contract)
Proof: project the nonnegativity conjunct of `FiniteNetwork.UniformGeometricMixingRate`.
Source: ordered real inequalities and finite-network matrix contraction assumptions from decentralized optimization
Used in: justifying nonnegativity of geometric powers in communication-mixing estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/definitions/2
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem UniformGeometricMixingRate.beta_nonneg {Node : Type*}
    {matrixNorm : (Node -> Node -> Real) -> Real}
    {W : Nat -> Nat -> Node -> Node -> Real} {Ainf : Node -> Node -> Real}
    {C beta : Real} (h : UniformGeometricMixingRate matrixNorm W Ainf C beta) :
    0 <= beta :=
  h.2.1

/-- A uniform-geometric-mixing-rate contract has a contraction factor strictly
below one.

Layer: Model | Gap: Level 0 (strict contraction factor from geometric mixing-rate contract)
Proof: project the strict upper-bound conjunct of `FiniteNetwork.UniformGeometricMixingRate`.
Source: ordered real inequalities and finite-network matrix contraction assumptions from decentralized optimization
Used in: extracting the denominator condition for logarithmic communication schedules and geometric-series bounds
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/definitions/2
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem UniformGeometricMixingRate.beta_lt_one {Node : Type*}
    {matrixNorm : (Node -> Node -> Real) -> Real}
    {W : Nat -> Nat -> Node -> Node -> Real} {Ainf : Node -> Node -> Real}
    {C beta : Real} (h : UniformGeometricMixingRate matrixNorm W Ainf C beta) :
    beta < 1 :=
  h.2.2.1

/-- A uniform-geometric-mixing-rate contract bounds every matrix error by the
same geometric envelope.

Layer: Model | Gap: Level 0 (pointwise matrix-error bound from geometric mixing-rate contract)
Proof: project the all-times geometric-bound conjunct of `FiniteNetwork.UniformGeometricMixingRate` and specialize it to the requested indices.
Source: ordered real inequalities and finite-network matrix contraction assumptions from decentralized optimization
Used in: bounding each pull-with-memory matrix error before multiplying it by a vector or vector-valued node state
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/definitions/2
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem UniformGeometricMixingRate.bound {Node : Type*}
    {matrixNorm : (Node -> Node -> Real) -> Real}
    {W : Nat -> Nat -> Node -> Node -> Real} {Ainf : Node -> Node -> Real}
    {C beta : Real} (h : UniformGeometricMixingRate matrixNorm W Ainf C beta)
    (k r : Nat) :
    matrixNorm (fun i j => W k r i j - Ainf i j) <= C * beta ^ r :=
  h.2.2.2 k r

-- Generalization plan (G0):
-- concept/name: finite-network consensus error; orig was finiteNetworkConsensusState_model_api over the paper-local `meanState`, `consensusState`, and `consensusError` fields.
-- generality used: arbitrary finite node carrier and additive real module state space; no measure, convexity, smoothness, oracle, topology, norm, inner-product, complete-space, or finite-dimensional assumptions are needed.
-- portable call pattern: distributed consensus, gradient-tracking, broadcast, push-pull, and pull-with-memory proofs instantiate the finite node type and state module while reusing the same uniform mean state, broadcast consensus state, and deviation-from-consensus object.
-- counterargument checked: Mathlib has `Fintype.balance`, a closely related function-minus-expectation object over `Finset.expect`; this API is still differentiated by using SOptLib's real-module `finiteUniformAverage` and by exposing the network mean/consensus/error triple used in distributed optimization goals.
-- coverage search: searched "finite network mean state consensus state consensus error definition projection", "consensus error equals state minus constant average state finite network", "consensus projection finite network average state deviation from consensus", and LeanSearch "finite network consensus error node state equals state minus constant uniform average"; top hits were local PullWithMemoryDGD definitions/private lemmas, `SOptLib.finiteUniformAverage`, staged `SOptLib.finiteUniformAverage_const`, and Mathlib `Fintype.balance`, with no SOptLib finite-network consensus-state API.
-- minimal hypotheses: `[Fintype Node]` is required by `finiteUniformAverage`; `[AddCommGroup E] [Module ℝ E]` are exactly needed for the finite mean and pointwise consensus deviation.

/-- The uniform mean of a finite node-indexed state.

For a finite network state `x : Node -> E`, this is the SOptLib
finite-uniform average over the node type.

Layer: Model | Concept: finite-network mean state
Proof: (definitional construction; finite uniform average over node-indexed state coordinates)
Source: Mathlib finite sums over finite types and SOptLib finite-uniform average
Used in: distributed optimization proofs that rewrite node-wise iterates or gradients through the network mean before consensus-error estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
def meanState {Node E : Type*} [Fintype Node] [AddCommGroup E] [Module ℝ E]
    (x : Node -> E) : E :=
  SOptLib.finiteUniformAverage x

/-- The finite-network mean state unfolds to the SOptLib finite-uniform average.

Layer: Model | Gap: Level 0 (finite-network mean state unfolding)
Proof: by rfl after unfolding `FiniteNetwork.meanState`.
Source: Mathlib finite sums over finite types and SOptLib finite-uniform average
Used in: specializing paper node-average notation to the reusable finite-network mean state
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
@[simp] theorem meanState_def {Node E : Type*} [Fintype Node]
    [AddCommGroup E] [Module ℝ E] (x : Node -> E) :
    meanState x = SOptLib.finiteUniformAverage x := by
  rfl

/-- The consensus state that assigns the finite-network mean to every node.

Layer: Model | Concept: finite-network consensus state
Proof: (definitional construction; constant node-indexed state with value `meanState x`)
Source: finite-dimensional consensus theory and Mathlib function spaces over finite node types
Used in: distributed optimization proofs that split node-wise states into consensus and disagreement components
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
def consensusState {Node E : Type*} [Fintype Node] [AddCommGroup E] [Module ℝ E]
    (x : Node -> E) : Node -> E :=
  fun _ => meanState x

/-- The finite-network consensus state unfolds to the constant mean state.

Layer: Model | Gap: Level 0 (finite-network consensus state unfolding)
Proof: by rfl after unfolding `FiniteNetwork.consensusState`.
Source: finite-dimensional consensus theory and Mathlib function spaces over finite node types
Used in: rewriting the consensus component of node-wise states as a constant network state
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
@[simp] theorem consensusState_def {Node E : Type*} [Fintype Node]
    [AddCommGroup E] [Module ℝ E] (x : Node -> E) :
    consensusState x = fun _ => meanState x := by
  rfl

/-- The finite-network consensus error, or deviation from the consensus state.

For a node-indexed state `x`, `consensusError x` subtracts the constant network
state whose value is the uniform node mean.

Layer: Model | Concept: finite-network consensus error
Proof: (definitional construction; pointwise subtraction of the consensus state from the original node state)
Source: finite-dimensional consensus theory, Mathlib pointwise function subtraction, and SOptLib finite-uniform average
Used in: consensus, gradient-tracking, and pull-with-memory estimates that project node-wise iterates or gradient states onto their disagreement component
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
def consensusError {Node E : Type*} [Fintype Node] [AddCommGroup E] [Module ℝ E]
    (x : Node -> E) : Node -> E :=
  x - consensusState x

/-- The finite-network consensus error unfolds to state minus consensus state.

Layer: Model | Gap: Level 0 (finite-network consensus error unfolding)
Proof: by rfl after unfolding `FiniteNetwork.consensusError`.
Source: finite-dimensional consensus theory, Mathlib pointwise function subtraction, and SOptLib finite-uniform average
Used in: specializing paper consensus-error notation to the reusable finite-network disagreement state
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
@[simp] theorem consensusError_def {Node E : Type*} [Fintype Node]
    [AddCommGroup E] [Module ℝ E] (x : Node -> E) :
    consensusError x = x - consensusState x := by
  rfl

/-- At a node, the consensus error is the state value minus the finite-network mean.

Layer: Model | Gap: Level 0 (finite-network consensus error coordinate formula)
Proof: unfold `consensusError` and `consensusState`; pointwise function subtraction is definitional.
Source: finite-dimensional consensus theory and Mathlib pointwise function algebra
Used in: coordinate-wise consensus and gradient-tracking estimates where a projected node state is expanded at a selected node
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
@[simp] theorem consensusError_apply {Node E : Type*} [Fintype Node]
    [AddCommGroup E] [Module ℝ E] (x : Node -> E) (i : Node) :
    consensusError x i = x i - meanState x := by
  rfl

/-- The finite-network mean, consensus state, and consensus error satisfy their
canonical model formulas.

This packages the three definitional identities used when a paper-facing
distributed algorithm keeps separate names for the network mean, consensus
state, and deviation from consensus.

Layer: Model | Gap: Level 0 (finite-network consensus state model API)
Proof: by rfl after unfolding `meanState`, `consensusState`, and `consensusError`.
Source: finite-dimensional consensus theory, Mathlib pointwise function algebra, and SOptLib finite-uniform average
Used in: source-facing distributed optimization models that backfill paper-local mean, consensus-state, and consensus-error declarations with the reusable finite-network API
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/algorithm_spec
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based decentralized gradient descent -/
theorem consensusError_model_api {Node E : Type*} [Fintype Node]
    [AddCommGroup E] [Module ℝ E] (x : Node -> E) :
    meanState x = SOptLib.finiteUniformAverage x ∧
      consensusState x = (fun _ => meanState x) ∧
      consensusError x = x - consensusState x := by
  exact ⟨rfl, rfl, rfl⟩

end FiniteNetwork

namespace Matrix

/-- Applying Mathlib's identity matrix by row sums leaves every module-valued
finite state unchanged.

Layer: Model | Gap: Level 0 (identity matrix row action)
Proof: collapse the row sum to the diagonal entry of `(1 : Matrix Node Node R)`.
Source: Mathlib identity matrices and finite module-valued row sums
Used in: base cases for finite-network memory or coefficient matrices initialized as `1` -/
theorem one_sum_smul
    {R Node E : Type*} [Semiring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [Module R E] (x : Node -> E) :
    (fun i => Finset.univ.sum (fun j => (1 : Matrix Node Node R) i j • x j)) = x := by
  classical
  funext i
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply]
    simp
  · intro b _hb hbi
    have hib : i ≠ b := fun hib => hbi hib.symm
    rw [Matrix.one_apply]
    simp [hib]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Subtracting a row-dependent scalar multiple of each identity row from a
matrix subtracts that scalar times the selected coordinate from the selected
coordinate of the row-sum action. -/
theorem sum_sub_diagonal_smul_apply
    {R Node E : Type*} [Ring R] [Fintype Node] [DecidableEq Node]
    [AddCommGroup E] [Module R E]
    (H : _root_.Matrix Node Node R) (d : Node -> R) (y : Node -> E) (i : Node) :
    Finset.univ.sum
        (fun j =>
          (((fun r ell => H r ell - d r * (1 : _root_.Matrix Node Node R) r ell) :
              _root_.Matrix Node Node R) i j) • y j) =
      Finset.univ.sum (fun j => H i j • y j) - d i • y i := by
  classical
  simp only [sub_smul]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _hb hbi
    simp [hbi.symm]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

end Matrix

namespace TimeVaryingDigraph

-- Generalization plan (G0):
-- concept/name: accumulated edge relation of a time-varying directed graph; orig was AccumulatedEdge.
-- generality used: arbitrary vertex carrier and a natural-time-indexed directed edge relation; no finiteness, decidability, measure, convexity, smoothness, oracle, topology, or finite-dimensional hypotheses.
-- portable call pattern: distributed optimization connectivity proofs call the same B-step accumulated relation while changing the graph stream, window length, and source/target vertices.
-- counterargument checked: not paper-local because B-step accumulated graphs are standard in time-varying digraph assumptions; not a pure caller expression because naming the relation keeps strong-connectivity and reachability assumptions readable.
-- coverage search: lean_search_symbols "time varying directed graph accumulated edge exists time in window edge relation" found only the local PullWithMemoryDGD declaration and unrelated time-window iterate APIs; lean_leansearch "time varying directed graph accumulated edge relation exists time in finite window" found Mathlib Digraph.Adj and Digraph.iSup_adj, which expose adjacency and graph supremum but not the Nat-window accumulated relation used by algorithm assumptions.
-- minimal hypotheses: all already minimal; the setup object was replaced by its edge field and no typeclass assumptions remain.

/-- The edge relation obtained by accumulating a time-varying directed graph over
a finite natural-time window.

For a graph stream `edge`, `AccumulatedEdge edge t B source target` means that
the edge from `source` to `target` appears at some offset `ell < B` from the
starting time `t`.

Layer: Model | Concept: time-varying digraph accumulated edge relation
Proof: (definitional construction; existential edge occurrence inside a natural-time window)
Source: Mathlib directed graph adjacency relations and finite natural-time window conventions
Used in: B-step strong-connectivity assumptions for time-varying broadcast networks in pull-based distributed optimization
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/0
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
def AccumulatedEdge {Node : Type*} (edge : Nat -> Node -> Node -> Prop)
    (t B : Nat) (source target : Node) : Prop :=
  exists ell : Nat, ell < B /\ edge (t + ell) source target

/-- The accumulated edge relation unfolds to existence of an edge occurrence in
the selected natural-time window.

Layer: Model | Gap: Level 0 (time-varying digraph accumulated-edge unfolding)
Proof: by rfl after unfolding `TimeVaryingDigraph.AccumulatedEdge`.
Source: Mathlib directed graph adjacency relations and finite natural-time window conventions
Used in: rewriting B-step accumulated broadcast-network reachability back to instantaneous graph edges
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/0
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem AccumulatedEdge_def {Node : Type*} (edge : Nat -> Node -> Node -> Prop)
    (t B : Nat) (source target : Node) :
    AccumulatedEdge edge t B source target <->
      exists ell : Nat, ell < B /\ edge (t + ell) source target := by
  rfl

/-- Accumulated edges are monotone in the window length: an edge occurrence
seen in a `B`-step window is still seen after enlarging the window.

Layer: Model | Gap: Level 0 (time-varying digraph accumulated-edge monotonicity)
Proof: keep the same witnessing offset and compose its strict upper bound with
the window-length inequality.
Source: natural-number order and finite natural-time window conventions
Used in: comparing B-step accumulated broadcast-network reachability assumptions
across enlarged communication windows in pull-based distributed optimization -/
theorem AccumulatedEdge.mono {Node : Type*} {edge : Nat -> Node -> Node -> Prop}
    {t B B' : Nat} {source target : Node}
    (h : AccumulatedEdge edge t B source target) (hBB' : B <= B') :
    AccumulatedEdge edge t B' source target := by
  rcases h with ⟨ell, hell, hedge⟩
  exact ⟨ell, lt_of_lt_of_le hell hBB', hedge⟩

-- Generalization plan (G0):
-- concept/name: B-step strong connectivity of a time-varying directed graph; orig was BStepStronglyConnected.
-- generality used: arbitrary vertex carrier and a natural-time-indexed directed edge relation; no finiteness, decidability, measure, convexity, smoothness, oracle, topology, or finite-dimensional hypotheses.
-- portable call pattern: time-varying distributed optimization connectivity assumptions call the same contract while changing the graph stream, connectivity window, and node carrier.
-- counterargument checked: not paper-local because B-step strong connectivity with self-loops is a standard time-varying network assumption; not a pure wrapper because it packages three recurring hypotheses that drive accumulated-graph reachability arguments.
-- coverage search: lean_search_symbols "time varying digraph accumulated edge reachability strongly connected self loops" and "B step strongly connected accumulated graph self loops" found only the local PullWithMemoryDGD declaration plus the already staged AccumulatedEdge; lean_leansearch "time varying directed graph B step strongly connected self loops accumulated graph" found Mathlib Quiver.IsStronglyConnected, which covers static quiver path connectivity but not the Nat-window accumulated graph with self-loops and positive window length.
-- minimal hypotheses: all already minimal; the algorithm setup object was replaced by its edge field and no typeclass assumptions remain.

/-- A time-varying directed graph is B-step strongly connected when the window
length is positive, every instantaneous graph has all self-loops, and every
accumulated graph over such a window is reachable between any ordered pair of
vertices.

Layer: Model | Concept: time-varying digraph B-step strong connectivity
Proof: (definitional construction; positive window, instantaneous self-loops, and reflexive-transitive reachability in the accumulated edge relation)
Source: Mathlib directed graph reachability via `Relation.ReflTransGen` and natural-time window conventions
Used in: broadcast-network assumptions for pull-with-memory decentralized gradient descent, where the graph stream changes over time but every B-step accumulated graph must be strongly connected
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/0
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
def BStepStronglyConnected {Node : Type*} (edge : Nat -> Node -> Node -> Prop)
    (B : Nat) : Prop :=
  0 < B /\
    (forall t i, edge t i i) /\
      forall t source target,
        Relation.ReflTransGen (AccumulatedEdge edge t B) source target

/-- The B-step strong-connectivity contract unfolds to positive window length,
instantaneous self-loops, and accumulated-graph reachability.

Layer: Model | Gap: Level 0 (time-varying digraph B-step strong-connectivity unfolding)
Proof: by rfl after unfolding `TimeVaryingDigraph.BStepStronglyConnected`.
Source: Mathlib directed graph reachability via `Relation.ReflTransGen` and natural-time window conventions
Used in: rewriting broadcast-network connectivity assumptions back to the explicit self-loop and accumulated-reachability clauses used by matrix-weight arguments
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/0
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem BStepStronglyConnected_def {Node : Type*}
    (edge : Nat -> Node -> Node -> Prop) (B : Nat) :
    BStepStronglyConnected edge B <->
      0 < B /\
        (forall t i, edge t i i) /\
          forall t source target,
            Relation.ReflTransGen (AccumulatedEdge edge t B) source target := by
  rfl

/-- A B-step strongly connected time-varying digraph has positive window
length. -/
theorem BStepStronglyConnected.positive_window {Node : Type*}
    {edge : Nat -> Node -> Node -> Prop} {B : Nat}
    (h : BStepStronglyConnected edge B) : 0 < B :=
  h.1

/-- Every instantaneous graph in a B-step strongly connected time-varying
digraph contains all self-loops. -/
theorem BStepStronglyConnected.self_loop {Node : Type*}
    {edge : Nat -> Node -> Node -> Prop} {B : Nat}
    (h : BStepStronglyConnected edge B) (t : Nat) (i : Node) :
    edge t i i :=
  h.2.1 t i

/-- The accumulated graph over each B-step window is reachable between every
ordered pair of vertices. -/
theorem BStepStronglyConnected.reachable {Node : Type*}
    {edge : Nat -> Node -> Node -> Prop} {B : Nat}
    (h : BStepStronglyConnected edge B) (t : Nat) (source target : Node) :
    Relation.ReflTransGen (AccumulatedEdge edge t B) source target :=
  h.2.2 t source target

/-- B-step strong connectivity is monotone under enlarging the accumulation
window. -/
theorem BStepStronglyConnected.mono {Node : Type*}
    {edge : Nat -> Node -> Node -> Prop} {B B' : Nat}
    (h : BStepStronglyConnected edge B) (hBB' : B <= B') :
    BStepStronglyConnected edge B' :=
  ⟨lt_of_lt_of_le (BStepStronglyConnected.positive_window h) hBB',
    BStepStronglyConnected.self_loop h,
    fun t source target =>
      Relation.ReflTransGen.mono
        (fun _ _ hab => AccumulatedEdge.mono hab hBB')
        (BStepStronglyConnected.reachable h t source target)⟩

-- Generalization plan (G0):
-- concept/name: broadcast-network assumptions for a time-varying digraph and row-stochastic mixing stream; orig was BroadcastNetworkAssumptions.
-- generality used: arbitrary finite node carrier with decidable equality, a natural-time-indexed directed edge relation, and a natural-time-indexed matrix stream over the ordered-semiring scalar envelope required by Mathlib row-stochastic matrices; no algorithm setup, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses.
-- portable call pattern: broadcast, push-sum, and push-pull distributed optimization convergence proofs call the same bundled network contract while changing only the graph stream, mixing stream, connectivity window witness, and lower-bound witness.
-- counterargument checked: not just paper traceability because this bundles the standard reusable network hypotheses needed before consensus and matrix-product estimates; not a duplicate of the already staged components because no existing declaration combines B-step connectivity, row-stochasticity, support compatibility, and uniform nonzero-entry lower bounds.
-- coverage search: lean_search_symbols "broadcast network assumptions time varying digraph row stochastic compatible mixing lower bounded entries" and "time varying row stochastic matrix graph support compatible lower bounded nonzero entries connected" found only the local source declaration plus the staged component predicates; lean_leansearch "time varying directed graph row stochastic matrix support compatible lower bounded nonzero entries broadcast network assumptions" found Mathlib row/doubly-stochastic matrix APIs, but no graph-support and lower-bound bundle.
-- minimal hypotheses: finite node carrier and decidable equality are required by Mathlib `Matrix.rowStochastic`; all algorithm `Setup` and Hilbert-space assumptions were removed.

/-- Bundled broadcast-network assumptions for a time-varying directed graph
and a compatible row-stochastic mixing-matrix stream.

The contract records an eventual B-step strong-connectivity witness,
row-stochasticity at every time, exact graph support of the mixing entries,
and a uniform positive lower bound for all nonzero entries.

Layer: Model | Concept: time-varying digraph broadcast-network assumptions
Proof: (definitional construction; conjunction of B-step strong connectivity, Mathlib row-stochastic matrix membership, support-compatible mixing, and finite-network nonzero-entry lower bound)
Source: Mathlib linear-algebra stochastic matrices together with finite-network matrix support and time-varying digraph reachability assumptions from decentralized optimization
Used in: establishing the deterministic network side conditions before applying pull-with-memory consensus and matrix-product estimates in broadcast distributed-gradient proofs
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
def BroadcastNetworkAssumptions {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    (edge : Nat -> Node -> Node -> Prop)
    (mixing : Nat -> _root_.Matrix Node Node R) : Prop :=
  (exists B : Nat, BStepStronglyConnected edge B) /\
    (forall t, (mixing t) ∈ _root_.Matrix.rowStochastic R Node) /\
      (forall t i j,
        (edge t j i -> 0 < mixing t i j) /\
          (Not (edge t j i) -> mixing t i j = 0)) /\
        exists tau : R,
          FiniteNetwork.LowerBoundedNonzeroEntries (fun t i j => mixing t i j) tau

/-- The broadcast-network assumption bundle unfolds to connectivity,
row-stochasticity, graph-support compatibility, and a nonzero-entry lower bound.

Layer: Model | Gap: Level 0 (broadcast-network assumption unfolding)
Proof: by rfl after unfolding `TimeVaryingDigraph.BroadcastNetworkAssumptions`.
Source: Mathlib linear-algebra stochastic matrices together with finite-network matrix support and time-varying digraph reachability assumptions from decentralized optimization
Used in: rewriting a broadcast-network contract into the explicit assumptions consumed by row-stochastic matrix and accumulated-graph arguments
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem BroadcastNetworkAssumptions_def {R Node : Type*}
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype Node] [DecidableEq Node]
    (edge : Nat -> Node -> Node -> Prop)
    (mixing : Nat -> _root_.Matrix Node Node R) :
    BroadcastNetworkAssumptions edge mixing <->
      (exists B : Nat, BStepStronglyConnected edge B) /\
        (forall t, (mixing t) ∈ _root_.Matrix.rowStochastic R Node) /\
          (forall t i j,
            (edge t j i -> 0 < mixing t i j) /\
              (Not (edge t j i) -> mixing t i j = 0)) /\
            exists tau : R,
              FiniteNetwork.LowerBoundedNonzeroEntries (fun t i j => mixing t i j) tau := by
  rfl

/-- A broadcast-network assumption bundle contains a B-step
strong-connectivity witness. -/
theorem BroadcastNetworkAssumptions.exists_b_step_strongly_connected
    {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    {edge : Nat -> Node -> Node -> Prop}
    {mixing : Nat -> _root_.Matrix Node Node R}
    (h : BroadcastNetworkAssumptions edge mixing) :
    exists B : Nat, BStepStronglyConnected edge B :=
  h.1

/-- Each mixing matrix in a broadcast-network assumption bundle is
row-stochastic. -/
theorem BroadcastNetworkAssumptions.row_stochastic
    {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    {edge : Nat -> Node -> Node -> Prop}
    {mixing : Nat -> _root_.Matrix Node Node R}
    (h : BroadcastNetworkAssumptions edge mixing) (t : Nat) :
    (mixing t) ∈ _root_.Matrix.rowStochastic R Node :=
  h.2.1 t

/-- A broadcast-network assumption bundle gives pointwise graph-support
compatibility for the mixing stream. -/
theorem BroadcastNetworkAssumptions.support_compatible
    {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    {edge : Nat -> Node -> Node -> Prop}
    {mixing : Nat -> _root_.Matrix Node Node R}
    (h : BroadcastNetworkAssumptions edge mixing) :
    forall t i j,
      (edge t j i -> 0 < mixing t i j) /\
        (Not (edge t j i) -> mixing t i j = 0) :=
  h.2.2.1

/-- A broadcast-network assumption bundle contains a uniform lower-bound
witness for all nonzero mixing entries. -/
theorem BroadcastNetworkAssumptions.exists_lower_bounded_nonzero_entries
    {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    {edge : Nat -> Node -> Node -> Prop}
    {mixing : Nat -> _root_.Matrix Node Node R}
    (h : BroadcastNetworkAssumptions edge mixing) :
    exists tau : R,
      FiniteNetwork.LowerBoundedNonzeroEntries (fun t i j => mixing t i j) tau :=
  h.2.2.2

/-- Graph edges have strictly positive entries in the compatible mixing stream
of a broadcast-network assumption bundle. -/
theorem BroadcastNetworkAssumptions.positive_of_edge
    {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    {edge : Nat -> Node -> Node -> Prop}
    {mixing : Nat -> _root_.Matrix Node Node R}
    (h : BroadcastNetworkAssumptions edge mixing) {t : Nat} {i j : Node}
    (hij : edge t j i) : 0 < mixing t i j :=
  (h.support_compatible t i j).1 hij

/-- Non-edges have zero entries in the compatible mixing stream of a
broadcast-network assumption bundle. -/
theorem BroadcastNetworkAssumptions.eq_zero_of_not_edge
    {R Node : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    {edge : Nat -> Node -> Node -> Prop}
    {mixing : Nat -> _root_.Matrix Node Node R}
    (h : BroadcastNetworkAssumptions edge mixing) {t : Nat} {i j : Node}
    (hij : Not (edge t j i)) : mixing t i j = 0 :=
  (h.support_compatible t i j).2 hij

end TimeVaryingDigraph
