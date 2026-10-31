import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Action
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import SOptLib.Model.Iterates
import SOptLib.Model.Selection
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis

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


/-! Promoted from Staging/AnalyticRankOneSpectralSplitting.lean. -/

-- Generalization plan (G0):
-- concept/name: analytic rank-one spectral splitting; orig was `PeriodicSpectralSplitting`.
-- generality used: an arbitrary real normed operator space, separate right- and left-mode carriers, an operator addition/composition/power/action interface, a left-right pairing, a rank-one Riesz-projection predicate, arbitrary base multiplier and stable-radius ceiling, and an explicit operator norm functional; no finiteness, measure, probability, convexity, smoothness, oracle, or algorithm setup assumptions are used.
-- portable call pattern: analytic perturbation proofs for periodic linearizations, finite-state Markov operators, and stochastic-approximation mean dynamics change the matrix family, base multiplier, spectral radii, eigenvectors, and norm while retaining the same slow-projector plus geometrically stable-remainder contract.
-- counterargument checked: this is not paper-local traceability or a one-line wrapper because it packages analytic branch regularity, a normalized rank-one isolated eigenprojection, the eigenvalue derivative pairing, exact complementary algebra, and a uniform all-powers bound; the existing rank-one Riesz API covers only the pointwise projector clause.
-- coverage search: `lean_search_symbols` queries “analytic operator family rank one Riesz projection stable complement geometric power bound derivative pairing” and “analytic rank one spectral splitting slow projection stable remainder power bound” found the source declaration and the pointwise `Module.End.IsRankOneRieszProjectionAt` API but no complete splitting contract; LeanSearch returned rank-one operators and analytic linear maps only, with no matching decomposition-and-power-bound definition.
-- minimal hypotheses: the operator carrier needs only the normed real-vector-space structure required by analyticity and differentiation; algebraic operations, the spectral-projection interface, and the norm used in the decay estimate are explicit so matrix, continuous-linear-map, and endomorphism representations can instantiate the same contract without conversion assumptions; the source-specific unit base multiplier and unit stability ceiling are generalized to `lambda0` and `rho`.
-- destination: SOptLib/Glue/Analysis.lean

/-- An analytic real operator family has a rank-one slow spectral branch and a
uniformly geometrically stable complementary branch.

The contract consumes a representation's named rank-one Riesz-projection,
composition, action, pairing, power, and norm interfaces. It records the
eigenvalue derivative through normalized left and right base modes, the exact
annihilating slow/stable decomposition, and a uniform power bound.

Layer: Glue | Concept: analytic rank-one slow-stable spectral splitting
Proof: (definitional construction; analytic eigenvalue and projector branches, a supplied isolated rank-one projection interface, derivative pairing, complementary-product identities, and a geometric power bound)
Source: analytic perturbation theory for a simple isolated eigenvalue, Riesz projections, and Cauchy-resolvent power estimates
Used in: separating a periodic linearization or stochastic-approximation mean operator into its one-dimensional slow mode and a uniformly decaying transient before asymptotic lower-bound estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def AnalyticRankOneSpectralSplitting
    {Operator RightMode LeftMode : Type*}
    [NormedAddCommGroup Operator] [NormedSpace ℝ Operator]
    (operatorAdd operatorMul : Operator → Operator → Operator)
    (operatorPower : Operator → ℕ → Operator)
    (operatorNorm : Operator → ℝ)
    (operatorAction : Operator → RightMode → RightMode)
    (pairing : LeftMode → RightMode → ℝ)
    (isRankOneRieszProjectionAt : Operator → ℝ → Operator → Prop)
    (A : ℝ → Operator) (lambda0 r0 alpha0 rho theta K : ℝ)
    (right : RightMode) (left : LeftMode) (gamma : ℝ → ℝ)
    (P F : ℝ → Operator) : Prop :=
  0 < alpha0 ∧ r0 < theta ∧ theta < rho ∧ 0 ≤ K ∧ gamma 0 = lambda0 ∧
    (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ gamma alpha) ∧
      (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ P alpha) ∧
        (∃ Aderiv : Operator,
          HasDerivAt A Aderiv 0 ∧
            HasDerivAt gamma (pairing left (operatorAction Aderiv right)) 0) ∧
          ∀ alpha : ℝ, |alpha| ≤ alpha0 →
            isRankOneRieszProjectionAt (A alpha) (gamma alpha) (P alpha) ∧
              A alpha = operatorAdd (gamma alpha • P alpha) (F alpha) ∧
                operatorMul (P alpha) (F alpha) = 0 ∧
                  operatorMul (F alpha) (P alpha) = 0 ∧
                    ∀ j : ℕ, operatorNorm (operatorPower (F alpha) j) ≤ K * theta ^ j

/-- The analytic rank-one spectral-splitting predicate unfolds to analytic
slow data, a normalized isolated rank-one projector, exact complementary
algebra, the normalized derivative formula, and uniform geometric decay.

Layer: Glue | Gap: Level 0 (analytic rank-one spectral-splitting unfolding)
Proof: by rfl after unfolding `AnalyticRankOneSpectralSplitting`.
Source: analytic perturbation theory for simple isolated eigenvalues and stable complementary propagators
Used in: exposing the individual analytic, spectral, derivative, algebraic, and power-bound clauses consumed by periodic linearization and stochastic-approximation proofs
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem analyticRankOneSpectralSplitting_def
    {Operator RightMode LeftMode : Type*}
    [NormedAddCommGroup Operator] [NormedSpace ℝ Operator]
    (operatorAdd operatorMul : Operator → Operator → Operator)
    (operatorPower : Operator → ℕ → Operator)
    (operatorNorm : Operator → ℝ)
    (operatorAction : Operator → RightMode → RightMode)
    (pairing : LeftMode → RightMode → ℝ)
    (isRankOneRieszProjectionAt : Operator → ℝ → Operator → Prop)
    (A : ℝ → Operator) (lambda0 r0 alpha0 rho theta K : ℝ)
    (right : RightMode) (left : LeftMode) (gamma : ℝ → ℝ)
    (P F : ℝ → Operator) :
    AnalyticRankOneSpectralSplitting operatorAdd operatorMul operatorPower
        operatorNorm operatorAction pairing isRankOneRieszProjectionAt
        A lambda0 r0 alpha0 rho theta K
        right left gamma P F ↔
      0 < alpha0 ∧ r0 < theta ∧ theta < rho ∧ 0 ≤ K ∧ gamma 0 = lambda0 ∧
        (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ gamma alpha) ∧
          (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ P alpha) ∧
            (∃ Aderiv : Operator,
              HasDerivAt A Aderiv 0 ∧
                HasDerivAt gamma (pairing left (operatorAction Aderiv right)) 0) ∧
              ∀ alpha : ℝ, |alpha| ≤ alpha0 →
                isRankOneRieszProjectionAt (A alpha) (gamma alpha) (P alpha) ∧
                  A alpha = operatorAdd (gamma alpha • P alpha) (F alpha) ∧
                    operatorMul (P alpha) (F alpha) = 0 ∧
                      operatorMul (F alpha) (P alpha) = 0 ∧
                        ∀ j : ℕ, operatorNorm (operatorPower (F alpha) j) ≤
                          K * theta ^ j := by
  rfl

/-- Increasing a nonnegative geometric factor and its nonnegative prefactor
preserves an analytic rank-one spectral splitting, provided the new factor
remains below the stability ceiling.

Layer: Glue | Gap: Level 1 (geometric-envelope weakening for a spectral splitting)
Proof: retain the analytic and algebraic clauses, then use monotonicity of
  natural powers and multiplication to weaken the stable power estimate.
Source: ordered real powers and the analytic rank-one spectral-splitting contract
Used in: reconciling a spectral decay factor with a larger common contraction
  factor and prefactor in perturbative operator or stochastic mean-dynamics proofs
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticRankOneSpectralSplitting_weaken_geometric_constants
    {Operator RightMode LeftMode : Type*}
    [NormedAddCommGroup Operator] [NormedSpace ℝ Operator]
    (operatorAdd operatorMul : Operator → Operator → Operator)
    (operatorPower : Operator → ℕ → Operator)
    (operatorNorm : Operator → ℝ)
    (operatorAction : Operator → RightMode → RightMode)
    (pairing : LeftMode → RightMode → ℝ)
    (isRankOneRieszProjectionAt : Operator → ℝ → Operator → Prop)
    (A : ℝ → Operator) (lambda0 r0 alpha0 rho theta K theta' K' : ℝ)
    (right : RightMode) (left : LeftMode) (gamma : ℝ → ℝ)
    (P F : ℝ → Operator)
    (hs :
      AnalyticRankOneSpectralSplitting operatorAdd operatorMul operatorPower
        operatorNorm operatorAction pairing isRankOneRieszProjectionAt
        A lambda0 r0 alpha0 rho theta K right left gamma P F)
    (htheta_nonneg : 0 ≤ theta)
    (htheta_le : theta ≤ theta')
    (htheta'_lt_rho : theta' < rho)
    (hK_le : K ≤ K') :
    AnalyticRankOneSpectralSplitting operatorAdd operatorMul operatorPower
      operatorNorm operatorAction pairing isRankOneRieszProjectionAt
      A lambda0 r0 alpha0 rho theta' K' right left gamma P F := by
  rcases hs with
    ⟨halpha0_pos, hr0_theta, _htheta_lt_rho, hK_nonneg, hgamma0,
      hgamma_analytic, hP_analytic, hderiv, hlocal⟩
  have hK'_nonneg : 0 ≤ K' := hK_nonneg.trans hK_le
  refine ⟨halpha0_pos, lt_of_lt_of_le hr0_theta htheta_le,
    htheta'_lt_rho, hK'_nonneg, hgamma0, hgamma_analytic, hP_analytic,
    hderiv, ?_⟩
  intro alpha halpha
  obtain ⟨hRiesz, hsplit, hPF, hFP, hpower⟩ := hlocal alpha halpha
  refine ⟨hRiesz, hsplit, hPF, hFP, ?_⟩
  intro j
  have hpow_le : theta ^ j ≤ theta' ^ j :=
    pow_le_pow_left₀ htheta_nonneg htheta_le j
  have hgeom_le : K * theta ^ j ≤ K' * theta' ^ j :=
    mul_le_mul hK_le hpow_le (pow_nonneg htheta_nonneg j) hK'_nonneg
  exact le_trans (hpower j) hgeom_le

/-! Promoted from Staging/FiniteNetwork_PushPullPerronEquations.lean. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: normalized paired Perron-sequence evolution equations for push-pull matrix schedules; orig was PerronSequencesEquations.
-- generality used: arbitrary finite node carrier, real row/column matrix schedules, and a pair of real node-vector sequences; optional representation hooks default to Mathlib matrix-vector multiplication and finite coordinate sum, and no decidable equality, nonemptiness, stochasticity, positivity, periodicity, uniqueness, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are used.
-- portable call pattern: push-pull, push-sum, and gradient-tracking developments change the finite node type, the row/column matrix schedules, and the chosen vector sequences while retaining the two evolution equations and unit-mass normalizations.
-- counterargument checked: although this is a definitional predicate, it is not paper-local bookkeeping or a caller-side expression because the four equations form the standard reusable compatibility contract between paired time-varying mixing schedules and their normalized Perron sequences; optional operation hooks are only a faithful notation bridge, with Mathlib operations as defaults, and the companion unfolding theorem provides the immediate API.
-- coverage search: lean_search_symbols queries "paired left right Perron sequence evolution normalized matrix schedules", "row vector matrix product equals previous sequence matrix vector equals next sequence unit sum", and "normalized left right eigenvector matrix sequence probability vector" found only the source-local Perron declarations; LeanSearch for paired normalized time-varying Perron vectors found only single-matrix doubly-stochastic facts such as `one_vecMul_of_mem_doublyStochastic`, so coverage is partial and does not duplicate this paired schedule contract.
-- minimal hypotheses: `[Fintype Node]` is exactly what the two finite matrix-vector products and normalization sums require; all ambient algorithm and finite-dimensional state-space assumptions were removed.

/-- A pair of unit-mass node-vector sequences obeys the left and right Perron
evolution equations for time-varying push and pull matrix schedules.

The left sequence evolves backward through the row schedule,
`pi_(t+1)^T R_t = pi_t^T`, while the right sequence evolves forward through
the column schedule, `C_t v_t = v_(t+1)`; both have coordinate sum one.

Layer: Model | Concept: normalized push-pull Perron-sequence equations
Proof: (definitional construction; conjunction of pointwise left and right matrix-vector evolution equations with unit-mass normalization at every time)
Source: finite-state nonhomogeneous Markov-chain absolute probability sequences and Perron eigenvector equations for time-varying stochastic matrices
Used in: selecting and reasoning about normalized left/right Perron sequences in push-pull, push-sum, and gradient-tracking analyses over changing directed-network schedules
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def PushPullPerronEquations {Node : Type*} [Fintype Node]
    (R C : Nat → Matrix Node Node Real)
    (seqs : (Nat → Node → Real) × (Nat → Node → Real))
    (rowMul : (Node → Real) → Matrix Node Node Real → Node → Real :=
      Matrix.vecMul)
    (mulVec : Matrix Node Node Real → (Node → Real) → Node → Real :=
      Matrix.mulVec)
    (mass : (Node → Real) → Real := fun w => ∑ i : Node, w i) : Prop :=
  (∀ (t : Nat) (j : Node),
      rowMul (seqs.1 (t + 1)) (R t) j = seqs.1 t j) ∧
    (∀ t : Nat, mass (seqs.1 t) = 1) ∧
    (∀ (t : Nat) (i : Node),
      mulVec (C t) (seqs.2 t) i = seqs.2 (t + 1) i) ∧
    (∀ t : Nat, mass (seqs.2 t) = 1)

/-- The normalized push-pull Perron contract unfolds to its two pointwise
evolution equations and two unit-mass equations.

Layer: Model | Gap: Level 0 (normalized paired Perron-equation predicate unfolding)
Proof: by rfl after unfolding `FiniteNetwork.PushPullPerronEquations`.
Source: Mathlib finite matrix-vector multiplication and finite sums over a finite node type
Used in: exposing the four Perron-sequence clauses needed separately by push-pull recursion, periodic-product, and consensus-weight arguments
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem PushPullPerronEquations_def {Node : Type*} [Fintype Node]
    (R C : Nat → Matrix Node Node Real)
    (seqs : (Nat → Node → Real) × (Nat → Node → Real))
    (rowMul : (Node → Real) → Matrix Node Node Real → Node → Real)
    (mulVec : Matrix Node Node Real → (Node → Real) → Node → Real)
    (mass : (Node → Real) → Real) :
    PushPullPerronEquations R C seqs rowMul mulVec mass ↔
      (∀ (t : Nat) (j : Node),
          rowMul (seqs.1 (t + 1)) (R t) j = seqs.1 t j) ∧
        (∀ t : Nat, mass (seqs.1 t) = 1) ∧
        (∀ (t : Nat) (i : Node),
          mulVec (C t) (seqs.2 t) i = seqs.2 (t + 1) i) ∧
        (∀ t : Nat, mass (seqs.2 t) = 1) := by
  rfl

/-- Shifting both matrix schedules and both Perron sequences by the same
amount preserves the normalized push-pull Perron contract.

Layer: Model | Gap: Level 1 (time-shift closure of normalized paired Perron equations)
Proof: specialize each evolution and mass equation at the shifted time index
Source: time translation of nonhomogeneous matrix evolution equations
Used in: restarting push-pull, push-sum, and gradient-tracking analyses at an arbitrary time
Book citation: not paper-specific
Origin algorithm: not paper-specific -/
theorem PushPullPerronEquations.time_shift {Node : Type*} [Fintype Node]
    {R C : Nat → Matrix Node Node Real}
    {seqs : (Nat → Node → Real) × (Nat → Node → Real)}
    {rowMul : (Node → Real) → Matrix Node Node Real → Node → Real}
    {mulVec : Matrix Node Node Real → (Node → Real) → Node → Real}
    {mass : (Node → Real) → Real}
    (h : PushPullPerronEquations R C seqs rowMul mulVec mass) (k : Nat) :
    PushPullPerronEquations
      (fun t => R (k + t)) (fun t => C (k + t))
      ((fun t => seqs.1 (k + t)), fun t => seqs.2 (k + t))
      rowMul mulVec mass := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t j
    simpa [Nat.add_assoc] using h.1 (k + t) j
  · intro t
    exact h.2.1 (k + t)
  · intro t i
    simpa [Nat.add_assoc] using h.2.2.1 (k + t) i
  · intro t
    exact h.2.2.2 (k + t)

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_UniquePositivePeriodicPushPullPerronSequences.lean. -/

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: unique strictly positive periodic normalized Perron sequences for paired push-pull matrix schedules; orig was PerronSequencesSpec.
-- generality used: arbitrary finite node carrier, real row/column matrix schedules, a natural period, and a candidate pair of real node-vector sequences; representation hooks default to Mathlib matrix-vector multiplication and finite coordinate sum, with no decidable equality, nonemptiness, stochasticity, schedule periodicity, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses.
-- portable call pattern: periodic push-pull, push-sum, and gradient-tracking developments change the finite node type, row and column schedules, period, and candidate sequences while using the same unique positive periodic normalized-solution boundary.
-- counterargument checked: the standalone positive-periodic conjunct is only a generic property bundle, but the full declaration relates that property to the paired Perron evolution equations and characterizes a unique solution; this is a standard reusable specification rather than paper-local traceability, a caller-side expression, or a pure wrapper.
-- coverage search: lean_search_symbols queries "unique positive periodic normalized Perron sequences push pull matrix schedules" and "pair unique solution equations positive periodic sequences" found the existing `FiniteNetwork.PushPullPerronEquations` dependency and only paper-local specification/caller declarations; LeanSearch for "unique positive periodic normalized Perron sequences for row and column stochastic matrix schedules" returned single-matrix doubly-stochastic facts but no paired time-varying uniqueness predicate, so coverage is partial and this declaration adds the missing specification boundary.
-- minimal hypotheses: `[Fintype Node]` is inherited exactly from the normalized Perron-equation dependency; strict positivity and periodicity need no additional typeclasses, and positivity/periodicity of the matrix schedules themselves are deliberately not assumed by this specification predicate.

/-- A pair of node-vector sequences is the unique strictly positive periodic
normalized solution of the left/right Perron equations for push-pull schedules.

The candidate must obey both normalized Perron evolutions, have strictly
positive coordinates and period `p`, and equal every other pair with those
same properties.

Layer: Model | Concept: unique positive periodic normalized push-pull Perron sequences
Proof: (definitional construction; conjunction of normalized paired Perron equations, coordinatewise strict positivity, period equations, and uniqueness among pairs satisfying the same contract)
Source: finite-state nonhomogeneous Markov-chain absolute probability sequences and Perron--Frobenius theory for periodic stochastic matrix products
Used in: canonically selecting the left absolute-probability and right Perron sequences used by periodic push-pull, push-sum, and gradient-tracking analyses
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def UniquePositivePeriodicPushPullPerronSequences
    {Node : Type*} [Fintype Node]
    (R C : Nat → Matrix Node Node Real) (p : Nat)
    (seqs : (Nat → Node → Real) × (Nat → Node → Real))
    (rowMul : (Node → Real) → Matrix Node Node Real → Node → Real :=
      Matrix.vecMul)
    (mulVec : Matrix Node Node Real → (Node → Real) → Node → Real :=
      Matrix.mulVec)
    (mass : (Node → Real) → Real := fun w => ∑ i : Node, w i) : Prop :=
  PushPullPerronEquations R C seqs rowMul mulVec mass ∧
    ((∀ (t : Nat) (i : Node), 0 < seqs.1 t i) ∧
      (∀ (t : Nat) (i : Node), 0 < seqs.2 t i) ∧
      (∀ t : Nat, seqs.1 (t + p) = seqs.1 t) ∧
      (∀ t : Nat, seqs.2 (t + p) = seqs.2 t)) ∧
    ∀ other : (Nat → Node → Real) × (Nat → Node → Real),
      PushPullPerronEquations R C other rowMul mulVec mass →
        ((∀ (t : Nat) (i : Node), 0 < other.1 t i) ∧
          (∀ (t : Nat) (i : Node), 0 < other.2 t i) ∧
          (∀ t : Nat, other.1 (t + p) = other.1 t) ∧
          (∀ t : Nat, other.2 (t + p) = other.2 t)) →
        other = seqs

/-- The unique positive periodic push-pull Perron specification unfolds to
its equation, positivity, periodicity, and uniqueness clauses.

Layer: Model | Gap: Level 0 (unique positive periodic paired Perron specification unfolding)
Proof: by rfl after unfolding `FiniteNetwork.UniquePositivePeriodicPushPullPerronSequences`.
Source: Mathlib finite matrix-vector multiplication and finite sums together with the normalized paired Perron-equation contract
Used in: exposing the evolution, normalization, positivity, periodicity, and competitor-uniqueness clauses of canonically selected push-pull Perron sequences
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem UniquePositivePeriodicPushPullPerronSequences_def
    {Node : Type*} [Fintype Node]
    (R C : Nat → Matrix Node Node Real) (p : Nat)
    (seqs : (Nat → Node → Real) × (Nat → Node → Real))
    (rowMul : (Node → Real) → Matrix Node Node Real → Node → Real)
    (mulVec : Matrix Node Node Real → (Node → Real) → Node → Real)
    (mass : (Node → Real) → Real) :
    UniquePositivePeriodicPushPullPerronSequences
        R C p seqs rowMul mulVec mass ↔
      PushPullPerronEquations R C seqs rowMul mulVec mass ∧
        ((∀ (t : Nat) (i : Node), 0 < seqs.1 t i) ∧
          (∀ (t : Nat) (i : Node), 0 < seqs.2 t i) ∧
          (∀ t : Nat, seqs.1 (t + p) = seqs.1 t) ∧
          (∀ t : Nat, seqs.2 (t + p) = seqs.2 t)) ∧
        ∀ other : (Nat → Node → Real) × (Nat → Node → Real),
          PushPullPerronEquations R C other rowMul mulVec mass →
            ((∀ (t : Nat) (i : Node), 0 < other.1 t i) ∧
              (∀ (t : Nat) (i : Node), 0 < other.2 t i) ∧
              (∀ t : Nat, other.1 (t + p) = other.1 t) ∧
              (∀ t : Nat, other.2 (t + p) = other.2 t)) →
            other = seqs := by
    rfl

/-- A uniquely specified positive periodic push-pull Perron pair satisfies the
normalized left and right Perron equations.

Layer: Model | Gap: Level 0 (equation projection from the unique positive periodic Perron specification)
Proof: project the Perron-equation clause from `FiniteNetwork.UniquePositivePeriodicPushPullPerronSequences`.
Source: normalized paired Perron equations for time-varying push-pull schedules
Used in: evolution and unit-mass arguments for canonically selected push-pull Perron sequences
Book citation: not paper-specific
Origin algorithm: not paper-specific -/
theorem UniquePositivePeriodicPushPullPerronSequences.equations
    {Node : Type*} [Fintype Node]
    {R C : Nat → Matrix Node Node Real} {p : Nat}
    {seqs : (Nat → Node → Real) × (Nat → Node → Real)}
    {rowMul : (Node → Real) → Matrix Node Node Real → Node → Real}
    {mulVec : Matrix Node Node Real → (Node → Real) → Node → Real}
    {mass : (Node → Real) → Real}
    (h : UniquePositivePeriodicPushPullPerronSequences
      R C p seqs rowMul mulVec mass) :
    PushPullPerronEquations R C seqs rowMul mulVec mass :=
  h.1

/-- Both sequences in a uniquely specified positive periodic push-pull Perron
pair are strictly positive at every time and node.

Layer: Model | Gap: Level 0 (positivity projection from the unique positive periodic Perron specification)
Proof: project the two coordinatewise strict-positivity clauses.
Source: strict positivity of normalized Perron sequences
Used in: weighted norms and coordinatewise divisions by canonical push-pull Perron sequences
Book citation: not paper-specific
Origin algorithm: not paper-specific -/
theorem UniquePositivePeriodicPushPullPerronSequences.positive
    {Node : Type*} [Fintype Node]
    {R C : Nat → Matrix Node Node Real} {p : Nat}
    {seqs : (Nat → Node → Real) × (Nat → Node → Real)}
    {rowMul : (Node → Real) → Matrix Node Node Real → Node → Real}
    {mulVec : Matrix Node Node Real → (Node → Real) → Node → Real}
    {mass : (Node → Real) → Real}
    (h : UniquePositivePeriodicPushPullPerronSequences
      R C p seqs rowMul mulVec mass) :
    (∀ (t : Nat) (i : Node), 0 < seqs.1 t i) ∧
      (∀ (t : Nat) (i : Node), 0 < seqs.2 t i) :=
  ⟨h.2.1.1, h.2.1.2.1⟩

/-- Both sequences in a uniquely specified positive periodic push-pull Perron
pair have the declared period.

Layer: Model | Gap: Level 0 (periodicity projection from the unique positive periodic Perron specification)
Proof: project the two period equations.
Source: periodic Perron sequences for periodic matrix schedules
Used in: finite-period reductions for canonical push-pull Perron sequences
Book citation: not paper-specific
Origin algorithm: not paper-specific -/
theorem UniquePositivePeriodicPushPullPerronSequences.periodic
    {Node : Type*} [Fintype Node]
    {R C : Nat → Matrix Node Node Real} {p : Nat}
    {seqs : (Nat → Node → Real) × (Nat → Node → Real)}
    {rowMul : (Node → Real) → Matrix Node Node Real → Node → Real}
    {mulVec : Matrix Node Node Real → (Node → Real) → Node → Real}
    {mass : (Node → Real) → Real}
    (h : UniquePositivePeriodicPushPullPerronSequences
      R C p seqs rowMul mulVec mass) :
    (∀ t : Nat, seqs.1 (t + p) = seqs.1 t) ∧
      (∀ t : Nat, seqs.2 (t + p) = seqs.2 t) :=
  ⟨h.2.1.2.2.1, h.2.1.2.2.2⟩

/-- Any other positive periodic pair satisfying the same normalized push-pull
Perron equations equals the uniquely specified pair.

Layer: Model | Gap: Level 1 (uniqueness elimination for positive periodic paired Perron sequences)
Proof: assemble the competing pair's positivity and periodicity clauses and apply the uniqueness field of `FiniteNetwork.UniquePositivePeriodicPushPullPerronSequences`.
Source: uniqueness of normalized positive periodic Perron sequences for paired matrix schedules
Used in: identifying independently constructed absolute-probability and right-Perron sequences with the canonical push-pull pair
Book citation: not paper-specific
Origin algorithm: not paper-specific -/
theorem UniquePositivePeriodicPushPullPerronSequences.eq_of_equations_positive_periodic
    {Node : Type*} [Fintype Node]
    {R C : Nat → Matrix Node Node Real} {p : Nat}
    {seqs other : (Nat → Node → Real) × (Nat → Node → Real)}
    {rowMul : (Node → Real) → Matrix Node Node Real → Node → Real}
    {mulVec : Matrix Node Node Real → (Node → Real) → Node → Real}
    {mass : (Node → Real) → Real}
    (h : UniquePositivePeriodicPushPullPerronSequences
      R C p seqs rowMul mulVec mass)
    (hother_eq : PushPullPerronEquations R C other rowMul mulVec mass)
    (hother_pos :
      (∀ (t : Nat) (i : Node), 0 < other.1 t i) ∧
        (∀ (t : Nat) (i : Node), 0 < other.2 t i))
    (hother_periodic :
      (∀ t : Nat, other.1 (t + p) = other.1 t) ∧
        (∀ t : Nat, other.2 (t + p) = other.2 t)) :
    other = seqs :=
  h.2.2 other hother_eq
    ⟨hother_pos.1, hother_pos.2, hother_periodic.1, hother_periodic.2⟩

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_PositiveDiagonal.lean. -/

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: positive diagonal of a square matrix; orig was PositiveDiagonal.
-- generality used: arbitrary node and ordered scalar types with `[Zero R] [Preorder R]`; no finiteness, decidable equality, field operations, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional assumptions.
-- portable call pattern: time-varying consensus, gossip, and push-pull proofs use the same predicate for self-weight-preserving mixing matrices while changing the node type, scalar type, and matrix schedule.
-- counterargument checked: although the body is a pointwise formula, it is not paper-local bookkeeping: positive diagonal is a standard named network-matrix contract used by setup fields, identity/product closure facts, reachability growth, and Perron-vector positivity arguments.
-- coverage search: lean_search_symbols "matrix every diagonal entry strictly positive", "positive diagonal square matrix predicate", and "FiniteNetwork PositiveDiagonal" found only the paper-local declaration and unrelated diagonal/positive-semidefinite results; LeanSearch found `Matrix.diag`, `Matrix.PosDef.diag_pos`, and `Matrix.posDef_diagonal_iff`, but no predicate equivalent at this generality.
-- minimal hypotheses: `[Zero R] [Preorder R]` are exactly the structure needed to state `0 < A i i`; all algorithm-level and finite-network cardinality assumptions were removed.

/-- A square matrix has a positive diagonal when every diagonal entry is strictly
positive.

Layer: Model | Concept: positive diagonal of a square matrix
Proof: (definitional construction; pointwise strict positivity of every self-entry)
Source: Mathlib square matrices as curried functions and ordered strict inequalities
Used in: time-varying push-pull and consensus network assumptions where positive self-weights preserve reached nodes, propagate positivity through matrix products, and support positive Perron weights
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def PositiveDiagonal {Node R : Type*} [Zero R] [Preorder R]
    (A : Matrix Node Node R) : Prop :=
  ∀ i : Node, 0 < A i i

/-- A square matrix has a positive diagonal exactly when each self-entry is
strictly positive.

Layer: Model | Gap: Level 0 (positive-diagonal predicate unfolding)
Proof: by rfl after unfolding `FiniteNetwork.PositiveDiagonal`.
Source: Mathlib square matrices as curried functions and ordered strict inequalities
Used in: exposing pointwise positive self-weights from reusable time-varying consensus and push-pull network assumptions
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem PositiveDiagonal_def {Node R : Type*} [Zero R] [Preorder R]
    (A : Matrix Node Node R) :
    PositiveDiagonal A ↔ ∀ i : Node, 0 < A i i := by
  rfl

/-- Positive diagonal is preserved when every diagonal entry is increased.

Layer: Model | Gap: Level 0 (positive-diagonal monotonicity)
Proof: compare each diagonal entry using transitivity of `<` and `≤`.
Source: Mathlib ordered strict inequalities applied to matrix diagonal entries
Used in: consensus and gossip arguments that compare mixing matrices on their self-weights -/
theorem PositiveDiagonal.mono {Node R : Type*} [Zero R] [Preorder R]
    {A B : Matrix Node Node R} (hA : PositiveDiagonal A)
    (hAB : ∀ i : Node, A i i ≤ B i i) :
    PositiveDiagonal B := by
  intro i
  exact lt_of_lt_of_le (hA i) (hAB i)

end FiniteNetwork

/-! Promoted from Staging/Matrix_IsNormalizedRankOneProjection.lean. -/

open scoped BigOperators Matrix

-- Generalization plan (G0):
-- concept/name: normalized rank-one matrix projection; orig was `RankOneProjection`.
-- generality used: arbitrary semiring, finite index type, and square matrix; no real order, norm, topology, measure, convexity, smoothness, oracle, algorithm setup, or finite-dimensional-space hypotheses.
-- portable call pattern: spectral splittings, consensus decompositions, and low-rank perturbation proofs change the scalar field, finite coordinate type, projection matrix, and normalized left/right factors while retaining idempotence and the formula for the projection's action on every vector.
-- counterargument checked: the contract is not merely paper traceability because it is the reusable witness-form interface between an abstract rank-one projection and downstream matrix-action calculations; the already-staged constructor from one-dimensional range proves this predicate but does not name or duplicate the predicate itself.
-- coverage search: `lean_search_symbols` searches for "normalized rank one projection idempotent matrix left right vectors dot product" and "matrix projection admits nonzero left right vectors normalized dot product factorization" found rank-many outer-product decompositions and the staged constructor `Matrix.isNormalizedRankOneProjection_of_mul_self_eq_and_finrank_range_eq_one`, but no Mathlib or SOptLib predicate with this signature; LeanSearch likewise found only forward facts about already-given rank-one operators.
-- minimal hypotheses: `[Semiring K]` and `[Fintype ι]` are exactly the scalar and finite-coordinate assumptions needed to state the matrix multiplication, dot product, normalization, and scalar-action contract. Stronger commutative-semiring or field assumptions occur only on API lemmas that need them.

/-- A finite square matrix is a normalized rank-one projection when it is
idempotent and acts through nonzero right and left vectors paired to one.

Layer: Model | Concept: normalized rank-one finite-matrix projection
Proof: (definitional construction; conjunction of matrix idempotence with a normalized nonzero left-right factorization of the matrix action)
Source: Mathlib finite matrix multiplication, matrix-vector multiplication, coordinate dot products, and Pi-module scalar actions
Used in: spectral and consensus splittings where a one-dimensional idempotent projection must expose normalized left and right modes for every projected vector
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def Matrix.IsNormalizedRankOneProjection
    {K ι : Type*} [Semiring K] [Fintype ι] (P : Matrix ι ι K) : Prop :=
  P * P = P ∧
    ∃ right left : ι → K,
      right ≠ 0 ∧ left ≠ 0 ∧ dotProduct left right = 1 ∧
        ∀ x : ι → K, P *ᵥ x = dotProduct left x • right

/-- The normalized rank-one projection predicate unfolds to idempotence and a
normalized nonzero left-right factorization of the action on every vector.

Layer: Model | Gap: Level 0 (normalized rank-one projection predicate unfolding)
Proof: by rfl after unfolding `Matrix.IsNormalizedRankOneProjection`.
Source: Mathlib finite matrix multiplication, matrix-vector multiplication, coordinate dot products, and Pi-module scalar actions
Used in: converting a named rank-one spectral or consensus projection contract into the witnesses and action identity consumed by matrix calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem Matrix.isNormalizedRankOneProjection_def
    {K ι : Type*} [Semiring K] [Fintype ι] (P : Matrix ι ι K) :
    Matrix.IsNormalizedRankOneProjection P ↔
      P * P = P ∧
        ∃ right left : ι → K,
          right ≠ 0 ∧ left ≠ 0 ∧ dotProduct left right = 1 ∧
            ∀ x : ι → K, P *ᵥ x = dotProduct left x • right := by
  rfl

/-- A normalized outer product is a normalized rank-one projection. -/
theorem Matrix.isNormalizedRankOneProjection_vecMulVec
    {K ι : Type*} [CommSemiring K] [Fintype ι]
    (right left : ι → K) (hright : right ≠ 0) (hleft : left ≠ 0)
    (hnormalized : dotProduct left right = 1) :
    Matrix.IsNormalizedRankOneProjection (Matrix.vecMulVec right left) := by
  rw [Matrix.isNormalizedRankOneProjection_def]
  refine ⟨?_, right, left, hright, hleft, hnormalized, ?_⟩
  · calc
      Matrix.vecMulVec right left * Matrix.vecMulVec right left =
          Matrix.vecMulVec right ((dotProduct left right) • left) :=
        Matrix.vecMulVec_mul_vecMulVec right left right left
      _ = Matrix.vecMulVec right left := by rw [hnormalized]; simp
  · intro x
    ext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, mul_comm]

/-- The action range of a normalized rank-one projection over a field has
dimension one. -/
theorem Matrix.IsNormalizedRankOneProjection.finrank_range_mulVecLin_eq_one
    {K ι : Type*} [Field K] [Fintype ι] {P : Matrix ι ι K}
    (hP : Matrix.IsNormalizedRankOneProjection P) :
    Module.finrank K
        (LinearMap.range
          (Matrix.mulVecLin P : (ι → K) →ₗ[K] (ι → K))) = 1 := by
  classical
  let L : (ι → K) →ₗ[K] (ι → K) := Matrix.mulVecLin P
  rcases hP with
    ⟨_hidempotent, right, left, hright_ne, _hleft_ne, hnormalized, haction⟩
  have hright_mem_range : right ∈ LinearMap.range L := by
    refine ⟨right, ?_⟩
    calc
      L right = P *ᵥ right := by rfl
      _ = dotProduct left right • right := haction right
      _ = right := by rw [hnormalized]; simp
  have hrange_eq :
      LinearMap.range L = (K ∙ right : Submodule K (ι → K)) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
      change P *ᵥ x ∈ K ∙ right
      rw [haction x]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self right)
    · intro y hy
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hc]
      exact Submodule.smul_mem _ c hright_mem_range
  rw [hrange_eq]
  exact finrank_span_singleton hright_ne

/-! Promoted from Staging/Matrix_SpectrumStrictlyInsideCircleOn.lean. -/

namespace Matrix

-- Generalization plan (G0):
-- concept/name: uniform strict spectral enclosure of a finite complex-matrix family on a parameter set; orig was `StableRemainderResolventDisk`.
-- generality used: arbitrary finite coordinate type, arbitrary parameter type and parameter set, a complex square-matrix family, and a real circle radius; no algorithm setup, parameter topology, continuity, analyticity, measure, convexity, smoothness, oracle, or finite-dimensional hypothesis beyond finite matrix coordinates is used.
-- portable call pattern: analytic spectral splitting, consensus, finite Markov-chain, and linear-recursion proofs vary the finite coordinates, parameter set, matrix family, and radius while reusing the same uniform strict spectral-disk contract before a contour-resolvent or matrix-power bound.
-- counterargument checked: although the contract is definitional, it is not paper-local traceability or a caller-side expression: it names the reusable uniform invariant passed between spectral upper-semicontinuity and compact-contour resolvent arguments, and its two projections form the stable API consumed by those arguments.
-- coverage search: `lean_search_symbols` queries "matrix spectrum uniformly strictly inside circle on parameter set" and "spectrum subset open ball matrix family set radius no eigenvalue boundary" found only paper-local spectral and Riesz-projection declarations; `lean_leansearch` query "matrix spectrum contained in open disk of radius and disjoint from boundary circle" found `Module.End.HasEigenvalue` and its finite-dimensional spectrum bridge but no uniform-on-a-set spectral-disk predicate.
-- minimal hypotheses: `[Fintype kappa]` is exactly what matrix-vector multiplication uses; `DecidableEq kappa`, `Nonempty kappa`, positivity of the radius, and regularity of the parameterized family are not needed to state the contract.

/-- Every right spectral value of every matrix in a parameterized family lies
strictly inside a fixed circle, and the boundary circle contains no right
spectral value.

The right spectral-value clauses are stated by a nonzero eigenvector witness.
For finite complex matrices this is equivalent to membership in Mathlib's
`spectrum`; the witness form avoids imposing decidable equality merely to state
the contract and is directly usable by matrix-vector arguments.

Layer: Model | Concept: uniform strict spectral-disk enclosure for finite matrix families
Proof: (definitional construction; a parameter-set-indexed conjunction of strict eigenvalue norm bounds and boundary exclusion)
Source: Mathlib finite matrix-vector multiplication, complex norms, and finite-dimensional spectrum/eigenvalue correspondence
Used in: analytic spectral splittings for consensus and push-pull transition families, between spectral upper-semicontinuity and a uniform contour-resolvent power estimate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def SpectrumStrictlyInsideCircleOn {kappa iota : Type*} [Fintype kappa]
    (F : iota -> Matrix kappa kappa Complex) (s : Set iota) (theta : Real) : Prop :=
  forall alpha, alpha ∈ s ->
    (forall z : Complex,
      (exists v : kappa -> Complex,
        v ≠ 0 /\ (F alpha).mulVec v = z • v) ->
        ‖z‖ < theta) /\
      forall z : Complex, ‖z‖ = theta ->
        Not (exists v : kappa -> Complex,
          v ≠ 0 /\ (F alpha).mulVec v = z • v)

/-- The uniform strict spectral-disk contract unfolds to its pointwise
eigenvalue bound and boundary-exclusion clauses.

Layer: Model | Gap: Level 0 (uniform finite-matrix spectral-disk contract unfolding)
Proof: by rfl after unfolding `Matrix.SpectrumStrictlyInsideCircleOn`.
Source: Mathlib finite matrix-vector multiplication and complex norms
Used in: exposing the pointwise spectral enclosure and contour-boundary resolvent hypotheses for a selected parameter
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem SpectrumStrictlyInsideCircleOn_def
    {kappa iota : Type*} [Fintype kappa]
    (F : iota -> Matrix kappa kappa Complex) (s : Set iota) (theta : Real) :
    SpectrumStrictlyInsideCircleOn F s theta <->
      forall alpha, alpha ∈ s ->
        (forall z : Complex,
          (exists v : kappa -> Complex,
            v ≠ 0 /\ (F alpha).mulVec v = z • v) ->
            ‖z‖ < theta) /\
          forall z : Complex, ‖z‖ = theta ->
            Not (exists v : kappa -> Complex,
              v ≠ 0 /\ (F alpha).mulVec v = z • v) := by
  rfl

/-- A right eigenvalue of a family member satisfying the uniform spectral-disk
contract has norm strictly below the fixed radius.

Layer: Model | Gap: Level 0 (pointwise strict spectral-radius bound from a uniform disk contract)
Proof: specialize the first projection of `Matrix.SpectrumStrictlyInsideCircleOn` to the parameter and eigenvector witness.
Source: Mathlib finite matrix-vector multiplication and complex norm inequalities
Used in: bounding stable spectral values before applying finite-matrix contour formulas or geometric power estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem SpectrumStrictlyInsideCircleOn.norm_lt
    {kappa iota : Type*} [Fintype kappa]
    {F : iota -> Matrix kappa kappa Complex} {s : Set iota} {theta : Real}
    (h : SpectrumStrictlyInsideCircleOn F s theta)
    {alpha : iota} (halpha : alpha ∈ s) {z : Complex}
    (hz : exists v : kappa -> Complex,
      v ≠ 0 /\ (F alpha).mulVec v = z • v) :
    ‖z‖ < theta :=
  (h alpha halpha).1 z hz

/-- No point on the boundary circle is a right eigenvalue of a family member
satisfying the uniform spectral-disk contract.

Layer: Model | Gap: Level 0 (boundary spectral exclusion from a uniform disk contract)
Proof: specialize the second projection of `Matrix.SpectrumStrictlyInsideCircleOn` to the parameter and boundary point.
Source: Mathlib finite matrix-vector multiplication and complex norm level sets
Used in: proving every point of a fixed contour belongs to the resolvent set uniformly over a parameter family
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem SpectrumStrictlyInsideCircleOn.not_hasRightEigenvalue_of_norm_eq
    {kappa iota : Type*} [Fintype kappa]
    {F : iota -> Matrix kappa kappa Complex} {s : Set iota} {theta : Real}
    (h : SpectrumStrictlyInsideCircleOn F s theta)
    {alpha : iota} (halpha : alpha ∈ s) {z : Complex}
    (hz : ‖z‖ = theta) :
    Not (exists v : kappa -> Complex,
      v ≠ 0 /\ (F alpha).mulVec v = z • v) :=
  (h alpha halpha).2 z hz

end Matrix


/-! Analytic rank constancy for finite-matrix projections. -/

namespace Matrix
namespace RankConstancyProof

open Filter
open scoped Topology

variable {Node : Type*} [Fintype Node] [Nonempty Node]

private abbrev NodeMatrix (Node : Type*) := Matrix Node Node ℝ
private abbrev RowVector (Node : Type*) := Node → ℝ

private noncomputable def matrixMul {Node : Type*} [Fintype Node]
    (A B : NodeMatrix Node) : NodeMatrix Node := A * B

private noncomputable def matrixMulVector {Node : Type*} [Fintype Node]
    (A : NodeMatrix Node) (v : RowVector Node) : RowVector Node :=
  fun i => ∑ j : Node, A i j * v j

private noncomputable def rowDot {Node : Type*} [Fintype Node]
    (w v : RowVector Node) : ℝ := ∑ j : Node, w j * v j

private def RankOneProjection {Node : Type*} [Fintype Node]
    (P : NodeMatrix Node) : Prop := Matrix.IsNormalizedRankOneProjection P

private theorem matrixMulVector_matrixMul {Node : Type*} [Fintype Node]
    (A B : NodeMatrix Node) (v : RowVector Node) :
    matrixMulVector (Node := Node) (matrixMul (Node := Node) A B) v =
      matrixMulVector (Node := Node) A (matrixMulVector (Node := Node) B v) := by
  classical
  unfold matrixMul matrixMulVector
  simpa only [Matrix.mulVec, dotProduct] using (Matrix.mulVec_mulVec v A B).symm

private theorem finrank_range_eq_of_idempotent_contracting_difference
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (p q : V →ₗ[ℝ] V)
    (hp : p.comp p = p) (hq : q.comp q = q)
    (hpq : ∀ x : V, x ≠ 0 → ‖(p - q) x‖ < ‖x‖)
    (hqp : ∀ x : V, x ≠ 0 → ‖(q - p) x‖ < ‖x‖) :
    Module.finrank ℝ (LinearMap.range p) =
      Module.finrank ℝ (LinearMap.range q) := by
  classical
  have hfix_p {x : V} (hx : x ∈ LinearMap.range p) : p x = x := by
    rcases hx with ⟨y, rfl⟩
    exact congrArg (fun f : V →ₗ[ℝ] V => f y) hp
  have hfix_q {x : V} (hx : x ∈ LinearMap.range q) : q x = x := by
    rcases hx with ⟨y, rfl⟩
    exact congrArg (fun f : V →ₗ[ℝ] V => f y) hq
  let qp : LinearMap.range p →ₗ[ℝ] LinearMap.range q :=
    LinearMap.codRestrict
      (p := LinearMap.range q)
      (q.comp (LinearMap.range p).subtype)
      (fun x => LinearMap.mem_range_self q x)
  have hqp_inj : Function.Injective qp := by
    intro x y hxy
    apply Subtype.ext
    let v : V := (x : V) - (y : V)
    have hvq : q v = 0 := by
      have hxy_val :
          q (x : V) = q (y : V) := by
        exact congrArg (fun z : LinearMap.range q => (z : V)) hxy
      simp [v, map_sub, hxy_val]
    have hvp : p v = v := by
      exact hfix_p (show v ∈ LinearMap.range p from
        Submodule.sub_mem _ x.property y.property)
    by_contra hv_ne
    have hv_ne_zero : v ≠ 0 := by
      intro hv_zero
      exact hv_ne (sub_eq_zero.mp hv_zero)
    have hlt := hpq v hv_ne_zero
    exact (lt_irrefl ‖v‖) (by
      simpa [v, LinearMap.sub_apply, hvp, hvq] using hlt)
  let pq : LinearMap.range q →ₗ[ℝ] LinearMap.range p :=
    LinearMap.codRestrict
      (p := LinearMap.range p)
      (p.comp (LinearMap.range q).subtype)
      (fun x => LinearMap.mem_range_self p x)
  have hpq_inj : Function.Injective pq := by
    intro x y hxy
    apply Subtype.ext
    let v : V := (x : V) - (y : V)
    have hvp : p v = 0 := by
      have hxy_val :
          p (x : V) = p (y : V) := by
        exact congrArg (fun z : LinearMap.range p => (z : V)) hxy
      simp [v, map_sub, hxy_val]
    have hvq : q v = v := by
      exact hfix_q (show v ∈ LinearMap.range q from
        Submodule.sub_mem _ x.property y.property)
    by_contra hv_ne
    have hv_ne_zero : v ≠ 0 := by
      intro hv_zero
      exact hv_ne (sub_eq_zero.mp hv_zero)
    have hlt := hqp v hv_ne_zero
    exact (lt_irrefl ‖v‖) (by
      simpa [v, LinearMap.sub_apply, hvq, hvp] using hlt)
  exact le_antisymm
    (LinearMap.finrank_le_finrank_of_injective hqp_inj)
    (LinearMap.finrank_le_finrank_of_injective hpq_inj)

/-- Operator-norm form of the local rank-preservation lemma for idempotent
finite-dimensional operators. -/
private theorem finrank_range_eq_of_idempotent_opNorm_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (p q : V →L[ℝ] V)
    (hp : p.comp p = p) (hq : q.comp q = q)
    (hclose : ‖p - q‖ < 1) :
    Module.finrank ℝ (LinearMap.range (p : V →ₗ[ℝ] V)) =
      Module.finrank ℝ (LinearMap.range (q : V →ₗ[ℝ] V)) := by
  classical
  have hp_lin :
      ((p : V →ₗ[ℝ] V).comp (p : V →ₗ[ℝ] V)) =
        (p : V →ₗ[ℝ] V) := by
    ext x
    exact congrArg (fun f : V →L[ℝ] V => f x) hp
  have hq_lin :
      ((q : V →ₗ[ℝ] V).comp (q : V →ₗ[ℝ] V)) =
        (q : V →ₗ[ℝ] V) := by
    ext x
    exact congrArg (fun f : V →L[ℝ] V => f x) hq
  have hclose_symm : ‖q - p‖ < 1 := by
    calc
      ‖q - p‖ = ‖-(q - p)‖ := by rw [norm_neg]
      _ = ‖p - q‖ := by rw [neg_sub]
      _ < 1 := hclose
  refine
    finrank_range_eq_of_idempotent_contracting_difference
      (p := (p : V →ₗ[ℝ] V)) (q := (q : V →ₗ[ℝ] V))
      hp_lin hq_lin ?_ ?_
  · intro x hx
    have hle : ‖(p - q) x‖ ≤ ‖p - q‖ * ‖x‖ :=
      (p - q).le_opNorm x
    have hlt : ‖p - q‖ * ‖x‖ < 1 * ‖x‖ :=
      mul_lt_mul_of_pos_right hclose (norm_pos_iff.mpr hx)
    exact lt_of_le_of_lt (by simpa using hle) (by simpa using hlt)
  · intro x hx
    have hle : ‖(q - p) x‖ ≤ ‖q - p‖ * ‖x‖ :=
      (q - p).le_opNorm x
    have hlt : ‖q - p‖ * ‖x‖ < 1 * ‖x‖ :=
      mul_lt_mul_of_pos_right hclose_symm (norm_pos_iff.mpr hx)
    exact lt_of_le_of_lt (by simpa using hle) (by simpa using hlt)

/-- Real matrix action as a continuous linear map on the finite node-vector
space. -/
private noncomputable def realMatrixContinuousLinearMap
    (A : NodeMatrix Node) :
    RowVector Node →L[ℝ] RowVector Node :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

/-- The map sending a real node matrix to its induced continuous linear
operator is continuous. -/
private theorem realMatrixContinuousLinearMap_continuous :
    Continuous
      (fun A : NodeMatrix Node =>
        realMatrixContinuousLinearMap (Node := Node) A) := by
  classical
  let L : NodeMatrix Node →ₗ[ℝ]
      (RowVector Node →L[ℝ] RowVector Node) :=
    { toFun := fun A => realMatrixContinuousLinearMap (Node := Node) A
      map_add' := by
        intro A B
        ext x i
        simp [realMatrixContinuousLinearMap, Matrix.mulVec, dotProduct,
          add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c A
        ext x i
        simp [realMatrixContinuousLinearMap, Matrix.mulVec, dotProduct,
          Finset.mul_sum, mul_assoc] }
  change Continuous L
  exact L.continuous_of_finiteDimensional

/-- Matrix-form local rank preservation for nearby idempotent node matrices. -/
private theorem finrank_range_mulVecLin_eq_of_idempotent_operator_close
    (P Q : NodeMatrix Node)
    (hP : matrixMul (Node := Node) P P = P)
    (hQ : matrixMul (Node := Node) Q Q = Q)
    (hclose :
      ‖realMatrixContinuousLinearMap (Node := Node) P -
          realMatrixContinuousLinearMap (Node := Node) Q‖ < 1) :
    Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin P :
            RowVector Node →ₗ[ℝ] RowVector Node)) =
      Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin Q :
            RowVector Node →ₗ[ℝ] RowVector Node)) := by
  classical
  let LP : RowVector Node →L[ℝ] RowVector Node :=
    realMatrixContinuousLinearMap (Node := Node) P
  let LQ : RowVector Node →L[ℝ] RowVector Node :=
    realMatrixContinuousLinearMap (Node := Node) Q
  have hP_idem : LP.comp LP = LP := by
    ext x i
    change
      matrixMulVector (Node := Node) P
          (matrixMulVector (Node := Node) P x) i =
        matrixMulVector (Node := Node) P x i
    rw [← matrixMulVector_matrixMul, hP]
  have hQ_idem : LQ.comp LQ = LQ := by
    ext x i
    change
      matrixMulVector (Node := Node) Q
          (matrixMulVector (Node := Node) Q x) i =
        matrixMulVector (Node := Node) Q x i
    rw [← matrixMulVector_matrixMul, hQ]
  have hrange :
      Module.finrank ℝ (LinearMap.range (LP : RowVector Node →ₗ[ℝ] RowVector Node)) =
        Module.finrank ℝ (LinearMap.range (LQ : RowVector Node →ₗ[ℝ] RowVector Node)) :=
    finrank_range_eq_of_idempotent_opNorm_lt_one
      (p := LP) (q := LQ) hP_idem hQ_idem (by simpa [LP, LQ] using hclose)
  simpa [LP, LQ, realMatrixContinuousLinearMap] using hrange

/-- The range dimension of a continuous idempotent node-matrix path is constant
on a connected closed interval. -/
private theorem finrank_range_mulVecLin_eq_on_Icc_of_continuous_idempotent
    (P : ℝ → NodeMatrix Node) (rho alpha beta : ℝ)
    (hP_cont : ContinuousOn P (Set.Icc (-rho) rho))
    (hidempotent :
      ∀ t : ℝ, t ∈ Set.Icc (-rho) rho →
        matrixMul (Node := Node) (P t) (P t) = P t)
    (halpha : alpha ∈ Set.Icc (-rho) rho)
    (hbeta : beta ∈ Set.Icc (-rho) rho) :
    Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin (P alpha) :
            RowVector Node →ₗ[ℝ] RowVector Node)) =
      Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin (P beta) :
            RowVector Node →ₗ[ℝ] RowVector Node)) := by
  classical
  let s : Set ℝ := Set.Icc (-rho) rho
  let rdim : s → ℕ := fun t =>
    Module.finrank ℝ
      (LinearMap.range
        (Matrix.mulVecLin (P (t : ℝ)) :
          RowVector Node →ₗ[ℝ] RowVector Node))
  have hlocal : IsLocallyConstant rdim := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hP_x : ContinuousWithinAt P s (x : ℝ) := hP_cont (x : ℝ) x.property
    have hL_x :
        ContinuousWithinAt
          (fun t : ℝ => realMatrixContinuousLinearMap (Node := Node) (P t))
          s (x : ℝ) :=
      (realMatrixContinuousLinearMap_continuous (Node := Node)).continuousAt.comp_continuousWithinAt
        hP_x
    have hball :
        {T : RowVector Node →L[ℝ] RowVector Node |
            ‖T - realMatrixContinuousLinearMap (Node := Node) (P (x : ℝ))‖ < 1} ∈
          𝓝 (realMatrixContinuousLinearMap (Node := Node) (P (x : ℝ))) := by
      refine mem_of_superset
        (Metric.ball_mem_nhds
          (realMatrixContinuousLinearMap (Node := Node) (P (x : ℝ)))
          (by norm_num : (0 : ℝ) < 1)) ?_
      intro T hT
      simpa [Metric.mem_ball, dist_eq_norm] using hT
    have hclose_within :
        {t : ℝ |
            ‖realMatrixContinuousLinearMap (Node := Node) (P t) -
                realMatrixContinuousLinearMap (Node := Node) (P (x : ℝ))‖ < 1} ∈
          𝓝[s] (x : ℝ) :=
      hL_x hball
    have hclose_sub :
        ∀ᶠ y : s in 𝓝 x,
          ‖realMatrixContinuousLinearMap (Node := Node) (P (y : ℝ)) -
              realMatrixContinuousLinearMap (Node := Node) (P (x : ℝ))‖ < 1 := by
      rw [nhdsWithin_eq_map_subtype_coe x.property] at hclose_within
      simpa [Filter.eventually_map] using hclose_within
    refine hclose_sub.mono ?_
    intro y hy
    exact
      finrank_range_mulVecLin_eq_of_idempotent_operator_close
        (Node := Node) (P (y : ℝ)) (P (x : ℝ))
        (hidempotent (y : ℝ) y.property)
        (hidempotent (x : ℝ) x.property)
        hy
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace isPreconnected_Icc
  have hconst :
      rdim ⟨alpha, halpha⟩ = rdim ⟨beta, hbeta⟩ :=
    hlocal.apply_eq_of_preconnectedSpace ⟨alpha, halpha⟩ ⟨beta, hbeta⟩
  simpa [rdim] using hconst

/-- Build the file's witness-form rank-one projection from a one-dimensional
range idempotent.

This is the purely algebraic half of the rank-constancy sentence in Appendix
A.  Once the analytic argument supplies that the range of the idempotent
contour projection still has finrank one, this lemma constructs the normalized
right/left vectors required by `RankOneProjection`. -/
private theorem rankOneProjection_of_idempotent_finrank_range_eq_one
    (P : NodeMatrix Node)
    (hidempotent : matrixMul (Node := Node) P P = P)
    (hrange_dim :
      Module.finrank ℝ
          (LinearMap.range
            (Matrix.mulVecLin P :
              RowVector Node →ₗ[ℝ] RowVector Node)) = 1) :
    RankOneProjection (Node := Node) P := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let L : RowVector Node →ₗ[ℝ] RowVector Node := Matrix.mulVecLin P
  have hL_apply :
      ∀ x : RowVector Node,
        L x = matrixMulVector (Node := Node) P x := by
    intro x
    ext i
    simp [L, matrixMulVector, Matrix.mulVecLin, Matrix.mulVec, dotProduct]
  have hL_idem : ∀ x : RowVector Node, L (L x) = L x := by
    intro x
    rw [hL_apply, hL_apply, ← matrixMulVector_matrixMul, hidempotent]
  obtain ⟨e⟩ :=
    Module.nonempty_linearEquiv_of_finrank_eq_one
      (R := ℝ) (M := LinearMap.range L) (by simpa [L] using hrange_dim)
  let right : RowVector Node := ((e (1 : ℝ) : LinearMap.range L) : RowVector Node)
  let left : RowVector Node := fun j : Node =>
    e.symm
      ⟨L (Pi.single j (1 : ℝ)),
        LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩
  have hright_sub_ne : e (1 : ℝ) ≠ (0 : LinearMap.range L) := by
    intro hzero
    have hscalar := congrArg e.symm hzero
    simpa using hscalar
  have hright_ne : right ≠ 0 := by
    intro hzero
    exact hright_sub_ne (Subtype.ext hzero)
  have hright_fixed : matrixMulVector (Node := Node) P right = right := by
    have hmem : right ∈ LinearMap.range L := (e (1 : ℝ)).property
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
    calc
      matrixMulVector (Node := Node) P right = L right := by
        rw [hL_apply]
      _ = L (L y) := by
        rw [hy]
      _ = L y := hL_idem y
      _ = right := hy
  have hnormalized : rowDot (Node := Node) left right = 1 := by
    have hright_col :
        (⟨L right, LinearMap.mem_range_self L right⟩ : LinearMap.range L) =
          e (1 : ℝ) := by
      ext i
      simpa [right, hL_apply] using congrFun hright_fixed i
    have hcoeff :
        e.symm
            (⟨L right, LinearMap.mem_range_self L right⟩ :
              LinearMap.range L) = 1 := by
      rw [hright_col]
      simp
    have hdecomp :
        (⟨L right, LinearMap.mem_range_self L right⟩ : LinearMap.range L) =
          ∑ j : Node,
            right j •
              (⟨L (Pi.single j (1 : ℝ)),
                LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                  LinearMap.range L) := by
      ext i
      simp [hL_apply, matrixMulVector, Pi.smul_apply, Finset.sum_apply,
        Pi.single_apply, mul_comm, mul_left_comm, mul_assoc]
    calc
      rowDot (Node := Node) left right =
          ∑ j : Node,
            right j *
              e.symm
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L) := by
            simp [left, rowDot, mul_comm, mul_left_comm, mul_assoc]
      _ =
          ∑ j : Node,
            e.symm
              (right j •
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
              (e.symm.map_smul (right j)
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L)).symm
      _ =
          e.symm
            (∑ j : Node,
              right j •
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L)) := by
            rw [map_sum]
      _ =
          e.symm
            (⟨L right, LinearMap.mem_range_self L right⟩ :
              LinearMap.range L) := by
            rw [← hdecomp]
      _ = 1 := hcoeff
  have hleft_ne : left ≠ 0 := by
    intro hleft_zero
    have : rowDot (Node := Node) left right = 0 := by
      simp [hleft_zero, rowDot]
    linarith
  refine ⟨hidempotent, right, left, hright_ne, hleft_ne, hnormalized, ?_⟩
  intro x
  let yx : LinearMap.range L :=
    ⟨L x, LinearMap.mem_range_self L x⟩
  have hspan (c : ℝ) :
      ((e c : LinearMap.range L) : RowVector Node) = c • right := by
    have hmap := congrArg Subtype.val (e.map_smul c (1 : ℝ))
    simpa [right] using hmap
  have hdecomp :
      yx =
        ∑ j : Node,
          x j •
            (⟨L (Pi.single j (1 : ℝ)),
              LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                LinearMap.range L) := by
    ext i
    simp [yx, hL_apply, matrixMulVector, Pi.smul_apply, Finset.sum_apply,
      Pi.single_apply, mul_comm, mul_left_comm, mul_assoc]
  have hcoeff :
      e.symm yx = rowDot (Node := Node) left x := by
    calc
      e.symm yx =
          e.symm
            (∑ j : Node,
              x j •
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L)) := by
            rw [hdecomp]
      _ =
          ∑ j : Node,
            e.symm
              (x j •
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L)) := by
            rw [map_sum]
      _ =
          rowDot (Node := Node) left x := by
            apply Finset.sum_congr rfl
            intro j _hj
            simpa [left, rowDot, smul_eq_mul, mul_comm, mul_left_comm,
              mul_assoc] using
              (e.symm.map_smul (x j)
                (⟨L (Pi.single j (1 : ℝ)),
                  LinearMap.mem_range_self L (Pi.single j (1 : ℝ))⟩ :
                    LinearMap.range L))
  calc
    matrixMulVector (Node := Node) P x = L x := by
      rw [hL_apply]
    _ = ((yx : LinearMap.range L) : RowVector Node) := rfl
    _ = ((e (e.symm yx) : LinearMap.range L) : RowVector Node) := by
      rw [LinearEquiv.apply_symm_apply]
    _ = e.symm yx • right := hspan (e.symm yx)
    _ = rowDot (Node := Node) left x • right := by
      rw [hcoeff]

end RankConstancyProof

/-- A continuous path of idempotent finite matrices that is rank one at the
base point remains rank one throughout a connected closed interval.

Layer: Model | Gap: Level 2 (analytic continuation and rank constancy of finite-matrix projections)
Proof: turn the matrix path into a continuous path of finite-dimensional operators; nearby idempotents at operator distance less than one have injective maps between their ranges, so range dimension is locally constant; connectedness propagates the base dimension one, from which normalized left/right witnesses are reconstructed.
Source: finite-dimensional analytic perturbation theory and connectedness of real intervals
Used in: constructing the slow rank-one spectral branch of an analytic family of finite network matrices before forming its stable complementary dynamics
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem isNormalizedRankOneProjection_on_Icc_of_continuous_idempotent
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ℝ → Matrix ι ι ℝ) (rho : ℝ)
    (hrho_pos : 0 < rho)
    (hP_cont : ContinuousOn P (Set.Icc (-rho) rho))
    (hP0 : Matrix.IsNormalizedRankOneProjection (P 0))
    (hidempotent : ∀ alpha : ℝ, |alpha| ≤ rho → P alpha * P alpha = P alpha) :
    ∀ alpha : ℝ, |alpha| ≤ rho →
      Matrix.IsNormalizedRankOneProjection (P alpha) := by
  classical
  intro alpha halpha
  apply RankConstancyProof.rankOneProjection_of_idempotent_finrank_range_eq_one
    (Node := ι) (P alpha) (by
      simpa [RankConstancyProof.matrixMul] using hidempotent alpha halpha)
  have hbaseRangeDim :
      Module.finrank ℝ
          (LinearMap.range
            (Matrix.mulVecLin (P 0) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 1 :=
    hP0.finrank_range_mulVecLin_eq_one
  have hrangeRankConst :
      Module.finrank ℝ
          (LinearMap.range
            (Matrix.mulVecLin (P alpha) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) =
        Module.finrank ℝ
          (LinearMap.range
            (Matrix.mulVecLin (P 0) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) := by
    have hP_idem :
        ∀ t : ℝ, t ∈ Set.Icc (-rho) rho → P t * P t = P t := by
      intro t ht
      exact hidempotent t (abs_le.mpr ht)
    have halphaIcc : alpha ∈ Set.Icc (-rho) rho := abs_le.mp halpha
    have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-rho) rho := by
      constructor <;> linarith
    simpa [RankConstancyProof.matrixMul] using
      RankConstancyProof.finrank_range_mulVecLin_eq_on_Icc_of_continuous_idempotent
        (Node := ι) P rho alpha 0 hP_cont (by
          intro t ht
          simpa [RankConstancyProof.matrixMul] using hP_idem t ht)
        halphaIcc hzeroIcc
  rw [hrangeRankConst, hbaseRangeDim]

end Matrix


noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Filter

namespace Matrix

-- Generalization plan (G0):
-- concept/name: finite real-matrix Riesz projection on a real-centered circle is idempotent and conjugation-fixed; orig was `complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary`.
-- generality used: arbitrary finite nonempty index type, a real square matrix, real contour center, and positive real radius; spectral separation is the pointwise determinant-nonvanishing condition on the circle, with no algorithm setup, measure, convexity, smoothness, oracle, normed-space, or extra finite-dimensional hypothesis.
-- portable call pattern: finite spectral perturbation, consensus, Markov-chain, and network-matrix proofs vary the matrix, real contour center, radius, and finite coordinate type while reusing idempotence and conjugation-fixedness of the circle Riesz projection.
-- counterargument checked: not paper-local because this is the standard finite-dimensional Riesz projection law; not a wrapper because Mathlib has circle integrals and matrix inverses but no matrix Riesz-projection construction or theorem combining its idempotence and real descent.
-- coverage search: `lean_search_symbols` queries "finite matrix Riesz projection circle idempotent spectrum disjoint" and "contour integral resolvent projection idempotent conjugation real entries" found only the source declaration and paper-local callers; `lean_leansearch` query "finite dimensional matrix Riesz projection contour integral is idempotent" found no matching Mathlib Riesz-projection API.
-- minimal hypotheses: `[Fintype ι] [Nonempty ι] [DecidableEq ι]`, positivity of the radius, and determinant nonvanishing at each boundary point are exactly what the contour and nonsingular-inverse proof uses; the source eigenvalue exclusion was weakened to its direct determinant form.

/-- The Riesz projection of a finite complex matrix obtained by integrating its
resolvent around a circle and normalizing by `(2πi)⁻¹`.

Layer: Model | Concept: finite complex-matrix Riesz projection on a circle
Proof: (definitional construction; entrywise normalized circle integral of the nonsingular inverse of `zI - A`)
Source: Mathlib `Matrix.inv` from `LinearAlgebra.Matrix.NonsingularInverse` and `circleIntegral` from `MeasureTheory.Integral.CircleIntegral`
Used in: fixed-contour spectral decompositions of finite Markov, consensus, and distributed-optimization transition matrices
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def rieszProjectionOnCircle {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (center : ℂ) (radius : ℝ) : Matrix ι ι ℂ := by
  classical
  exact fun i j =>
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (∮ z in C(center, radius),
        (@Inv.inv (Matrix ι ι ℂ)
          (@Matrix.inv ι ℂ _ (Classical.decEq ι) _)
          (fun k l : ι =>
            z * (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) k l -
              A k l)) i j)

/-- Each entry of the circle Riesz projection is its normalized resolvent integral.

Layer: Model | Gap: Level 0 (entrywise specification of the finite-matrix circle Riesz projection)
Proof: by rfl after unfolding `Matrix.rieszProjectionOnCircle`.
Source: Mathlib finite matrix nonsingular inversion and complex circle integration
Used in: unfolding a fixed-contour spectral projection before resolvent and residue calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem rieszProjectionOnCircle_apply {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (center : ℂ) (radius : ℝ) (i j : ι) :
    rieszProjectionOnCircle A center radius i j =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C(center, radius),
          (@Inv.inv (Matrix ι ι ℂ)
            (@Matrix.inv ι ℂ _ (Classical.decEq ι) _)
            (fun k l : ι =>
              z * (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) k l -
                A k l)) i j) := by
  rfl

end Matrix

/-! Promoted from Staging/Matrix_mul_rieszProjectionOnCircle_eq_rieszProjectionOnCircle_mul_of_spectrum_disjoint.lean. -/


noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Matrix

-- Generalization plan (G0):
-- concept/name: a finite complex matrix commutes with its circle Riesz projection when the contour is spectrally disjoint; orig was `complexRieszProjectionOnCircle_commutes_complexOfRealMatrix_of_no_boundary`.
-- generality used: arbitrary finite index type, complex square matrix, complex contour center, and nonnegative real radius; spectral separation is the pointwise determinant-nonvanishing condition on the circle, with no real-matrix, algorithm setup, measure, convexity, smoothness, oracle, normed-space, or additional finite-dimensional hypothesis.
-- portable call pattern: finite spectral perturbation, Markov-chain, consensus, and network-matrix proofs vary the complex matrix, contour center, radius, and finite coordinate type while reusing commutation of the matrix with its contour spectral projection.
-- counterargument checked: not paper-local because commutation with a holomorphic-functional-calculus spectral projection is a standard reusable spectral fact; not a wrapper because Mathlib has matrix inverses and circle integrals but no finite-matrix circle Riesz-projection commutation theorem.
-- coverage search: `lean_search_symbols` queries "matrix commutes with circle Riesz projection spectrum disjoint boundary resolvent" and "Riesz projection contour integral matrix multiplication commutes" found only the paper-local source theorem and the staged Riesz-projection definition/idempotence API; `lean_leansearch` query "A finite complex matrix commutes with the contour integral of its resolvent around a circle disjoint from the spectrum" found circle-integral and functional-calculus infrastructure but no matching matrix Riesz-projection theorem.
-- minimal hypotheses: `[Fintype ι] [DecidableEq ι]`, nonnegativity of the radius, and determinant nonvanishing at each boundary point are exactly what the entrywise contour-integrability and nonsingular-inverse commutation proof uses.

/-- A finite complex matrix commutes with its circle Riesz projection when the
circle is disjoint from the spectrum.

The determinant hypothesis says directly that every point of the contour is
in the resolvent set of `A`.

Layer: Model | Gap: Level 1 (finite-matrix circle Riesz-projection commutation)
Proof: move finite matrix multiplication through the entrywise circle integral, then use that `A` commutes with each nonsingular inverse of `zI - A` on the contour.
Source: finite-dimensional holomorphic functional calculus, Mathlib complex circle integrals, and Mathlib nonsingular matrix inverses
Used in: fixed-contour spectral splittings of finite consensus and push-pull transition matrices, where the transition matrix must preserve and commute with its isolated spectral subspace
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem mul_rieszProjectionOnCircle_eq_rieszProjectionOnCircle_mul_of_spectrum_disjoint
    {ι : Type*} [Fintype ι] [dec : DecidableEq ι]
    (A : Matrix ι ι ℂ) (center : ℂ) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hspectrum :
      ∀ z : ℂ, ‖z - center‖ = radius →
        Matrix.det (fun i j : ι =>
          z * (1 : Matrix ι ι ℂ) i j - A i j) ≠ 0) :
    A * rieszProjectionOnCircle A center radius =
      rieszProjectionOnCircle A center radius * A := by
  classical
  have hdec : dec = Classical.decEq ι := Subsingleton.elim _ _
  subst dec
  let M : ℂ → Matrix ι ι ℂ :=
    fun z i j => z * (1 : Matrix ι ι ℂ) i j - A i j
  let R : ℂ → Matrix ι ι ℂ := fun z => (M z)⁻¹
  let P : Matrix ι ι ℂ := rieszProjectionOnCircle A center radius
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  have hM_continuous : Continuous M := by
    change Continuous (fun z : ℂ => fun i : ι => fun j : ι =>
      z * (1 : Matrix ι ι ℂ) i j - A i j)
    fun_prop
  have hresolvent_entry_circleIntegrable :
      ∀ i j : ι, CircleIntegrable (fun z : ℂ => R z i j) center radius := by
    intro i j
    have hcont_sphere :
        ContinuousOn (fun z : ℂ => R z i j) (Metric.sphere center radius) := by
      intro z hz
      have hz_norm : ‖z - center‖ = radius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hdet : Matrix.det (M z) ≠ 0 := by
        simpa [M] using hspectrum z hz_norm
      have hadjugate_continuous :
          Continuous (fun w : ℂ => Matrix.adjugate (M w) i j) := by
        simp only [Matrix.adjugate_apply]
        apply (Continuous.matrix_det continuous_id).comp
        change Continuous (fun w : ℂ => (M w).updateRow j (Pi.single i (1 : ℂ)))
        change Continuous (fun w : ℂ => fun r : ι => fun s : ι =>
          (M w).updateRow j (Pi.single i (1 : ℂ)) r s)
        apply continuous_pi
        intro r
        apply continuous_pi
        intro s
        by_cases hrj : r = j
        · subst r
          simpa only [Matrix.updateRow_self] using
            (continuous_const :
              Continuous (fun _ : ℂ => (Pi.single i (1 : ℂ) : ι → ℂ) s))
        · simpa [Matrix.updateRow, hrj] using
            (((continuous_apply s).comp ((continuous_apply r).comp hM_continuous)))
      have hinv_det_at_matrix :
          ContinuousAt (fun N : Matrix ι ι ℂ => (Matrix.det N)⁻¹) (M z) :=
        (continuousAt_inv₀ hdet).comp
          (Continuous.matrix_det continuous_id).continuousAt
      have hinv_det : ContinuousAt (fun w : ℂ => (Matrix.det (M w))⁻¹) z :=
        hinv_det_at_matrix.comp hM_continuous.continuousAt
      have hentry :
          ContinuousAt
            (fun w : ℂ =>
              (Matrix.det (M w))⁻¹ * Matrix.adjugate (M w) i j) z :=
        hinv_det.mul hadjugate_continuous.continuousAt
      have hinv_entry : ContinuousAt (fun w : ℂ => R w i j) z := by
        simpa [R, Matrix.inv_def, Pi.smul_apply, smul_eq_mul,
          Ring.inverse_eq_inv'] using hentry
      exact hinv_entry.continuousWithinAt
    exact hcont_sphere.circleIntegrable hradius
  have hcomm (z : ℂ) (hz : ‖z - center‖ = radius) :
      A * R z = R z * A := by
    have hdet : Matrix.det (M z) ≠ 0 := by
      simpa [M] using hspectrum z hz
    have hunit : IsUnit (Matrix.det (M z)) := isUnit_iff_ne_zero.mpr hdet
    have hM_def : M z = algebraMap ℂ (Matrix ι ι ℂ) z - A := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [M, Matrix.algebraMap_eq_diagonal]
      · simp [M, Matrix.algebraMap_eq_diagonal, hij]
    have hscalar_comm :
        algebraMap ℂ (Matrix ι ι ℂ) z * A =
          A * algebraMap ℂ (Matrix ι ι ℂ) z := by
      ext i j
      simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul,
        Matrix.mul_diagonal, mul_comm]
    have hMA : M z * A = A * M z := by
      calc
        M z * A = (algebraMap ℂ (Matrix ι ι ℂ) z - A) * A := by rw [hM_def]
        _ = algebraMap ℂ (Matrix ι ι ℂ) z * A - A * A := by rw [sub_mul]
        _ = A * algebraMap ℂ (Matrix ι ι ℂ) z - A * A := by rw [hscalar_comm]
        _ = A * (algebraMap ℂ (Matrix ι ι ℂ) z - A) := by rw [mul_sub]
        _ = A * M z := by rw [hM_def]
    change A * (M z)⁻¹ = (M z)⁻¹ * A
    calc
      A * (M z)⁻¹ = ((M z)⁻¹ * M z) * (A * (M z)⁻¹) := by
        rw [Matrix.nonsing_inv_mul (M z) hunit]
        simp
      _ = (M z)⁻¹ * ((M z * A) * (M z)⁻¹) := by
        rw [Matrix.mul_assoc (M z)⁻¹ (M z) (A * (M z)⁻¹)]
        rw [← Matrix.mul_assoc (M z) A (M z)⁻¹]
      _ = (M z)⁻¹ * ((A * M z) * (M z)⁻¹) := by rw [hMA]
      _ = (M z)⁻¹ * (A * (M z * (M z)⁻¹)) := by rw [Matrix.mul_assoc]
      _ = (M z)⁻¹ * A := by
        rw [Matrix.mul_nonsing_inv (M z) hunit]
        simp
  ext i j
  have hleft_integrable :
      ∀ k ∈ (Finset.univ : Finset ι),
        CircleIntegrable (fun z : ℂ => A i k * R z k j) center radius := by
    intro k _hk
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hresolvent_entry_circleIntegrable k j).const_smul (a := A i k)
  have hright_integrable :
      ∀ k ∈ (Finset.univ : Finset ι),
        CircleIntegrable (fun z : ℂ => R z i k * A k j) center radius := by
    intro k _hk
    have hk : CircleIntegrable
        (fun z : ℂ => A k j * R z i k) center radius := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (hresolvent_entry_circleIntegrable i k).const_smul (a := A k j)
    simpa [mul_comm] using hk
  have hleft :
      (A * P) i j = c * (∮ z in C(center, radius), (A * R z) i j) := by
    calc
      (A * P) i j = ∑ k : ι, A i k * P k j := by simp [Matrix.mul_apply]
      _ = ∑ k : ι, A i k *
          (c * (∮ z in C(center, radius), R z k j)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hPkj : P k j = c * (∮ z in C(center, radius), R z k j) := by
          simpa [P, c, R, M, rieszProjectionOnCircle]
        rw [hPkj]
      _ = c * ∑ k : ι, A i k *
          (∮ z in C(center, radius), R z k j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = c * ∑ k : ι,
          (∮ z in C(center, radius), A i k * R z k j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _hk
        rw [circleIntegral.integral_const_mul]
      _ = c * (∮ z in C(center, radius),
          ∑ k : ι, A i k * R z k j) := by
        rw [circleIntegral.integral_fun_sum hleft_integrable]
      _ = c * (∮ z in C(center, radius), (A * R z) i j) := by
        simp [Matrix.mul_apply]
  have hright :
      (P * A) i j = c * (∮ z in C(center, radius), (R z * A) i j) := by
    calc
      (P * A) i j = ∑ k : ι, P i k * A k j := by simp [Matrix.mul_apply]
      _ = ∑ k : ι,
          (c * (∮ z in C(center, radius), R z i k)) * A k j := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hPik : P i k = c * (∮ z in C(center, radius), R z i k) := by
          simpa [P, c, R, M, rieszProjectionOnCircle]
        rw [hPik]
      _ = c * ∑ k : ι,
          (∮ z in C(center, radius), R z i k) * A k j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = c * ∑ k : ι,
          (∮ z in C(center, radius), R z i k * A k j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _hk
        simpa [smul_eq_mul] using
          (circleIntegral.integral_smul_const
            (fun z : ℂ => R z i k) (A k j) center radius).symm
      _ = c * (∮ z in C(center, radius),
          ∑ k : ι, R z i k * A k j) := by
        rw [circleIntegral.integral_fun_sum hright_integrable]
      _ = c * (∮ z in C(center, radius), (R z * A) i j) := by
        simp [Matrix.mul_apply]
  calc
    (A * P) i j = c * (∮ z in C(center, radius), (A * R z) i j) := hleft
    _ = c * (∮ z in C(center, radius), (R z * A) i j) := by
      congr 1
      refine circleIntegral.integral_congr hradius ?_
      intro z hz
      have hz_norm : ‖z - center‖ = radius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      exact congrArg (fun N : Matrix ι ι ℂ => N i j) (hcomm z hz_norm)
    _ = (P * A) i j := hright.symm

end Matrix

/-! Promoted from Staging/Matrix_rieszProjectionOnCircle_entry_eq_intervalIntegral.lean. -/


noncomputable section

open MeasureTheory

namespace Matrix

-- Generalization plan (G0):
-- concept/name: fixed-interval representation of a finite complex-matrix circle Riesz-projection entry; orig was `complexRieszProjectionOnCircle_entry_eq_Icc_integral`.
-- generality used: arbitrary finite index type, an arbitrary complex square matrix, a complex contour center, and a real radius; no real-matrix origin, nonempty carrier, measure, convexity, smoothness, oracle, spectral-separation, radius-positivity, decidable-equality, or ambient finite-dimensional hypotheses are needed.
-- portable call pattern: finite spectral perturbation, Markov-chain, and distributed-optimization proofs vary the matrix, contour center, radius, and selected entry while rewriting the public Riesz projection to a fixed real-interval integral for dominated, analytic, or conjugation arguments.
-- counterargument checked: although the proof is a short specialization of Mathlib's circle parametrization, it is not a pure rename: it is the fixed-interval companion API for the named matrix Riesz-projection object and exposes the corresponding resolvent entry needed by downstream proofs.
-- coverage search: `lean_search_symbols` queries "matrix Riesz projection on circle entry equals interval integral resolvent" and "Riesz projection interval integral circle map derivative entry" found `Matrix.rieszProjectionOnCircle_apply` only in the current staged defining module and no public interval-integral companion; `lean_leansearch` query "circle integral equals integral over Icc zero two pi derivative circle map times function" found the more general Mathlib theorem `circleIntegral_def_Icc`, which this result specializes after unfolding the matrix projection.
-- minimal hypotheses: `[Fintype ι]` is the sole coordinate assumption; the displayed nonsingular matrix inverse uses `Classical.decEq ι` locally, all remaining inputs are explicit, and no contour regularity hypothesis is required.

/-- An entry of a finite complex-matrix circle Riesz projection is the
normalized integral over `[0, 2π]` of the circle-map derivative times the
corresponding resolvent entry.

Layer: Model | Gap: Level 0 (fixed-interval entry representation for a finite-matrix circle Riesz projection)
Proof: unfold `Matrix.rieszProjectionOnCircle` and rewrite its contour integral with Mathlib's `circleIntegral_def_Icc` parametrization.
Source: Mathlib `circleIntegral_def_Icc`, `Complex.circleMap`, and finite-matrix nonsingular inversion
Used in: fixed-contour spectral perturbation arguments that pass a selected projection entry to real-interval analyticity, domination, or conjugation calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem rieszProjectionOnCircle_apply_eq_integral_Icc
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (center : ℂ) (radius : ℝ) (i j : ι) :
    rieszProjectionOnCircle A center radius i j =
      (letI : DecidableEq ι := Classical.decEq ι
       (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
         (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
           deriv (circleMap center radius) theta •
             (@Inv.inv (Matrix ι ι ℂ) Matrix.inv
               (fun k l : ι =>
                 circleMap center radius theta * (1 : Matrix ι ι ℂ) k l - A k l)) i j)) := by
  letI : DecidableEq ι := Classical.decEq ι
  rw [rieszProjectionOnCircle, circleIntegral_def_Icc]
  simp only [Matrix.one_apply, Matrix.diagonal_apply]

end Matrix

/-! Promoted from Staging/Matrix_rieszProjectionOnCircle_eq_of_spectrum_disjoint_annulus.lean. -/


noncomputable section

open MeasureTheory

namespace Matrix

-- Generalization plan (G0):
-- concept/name: contour independence of a finite-matrix Riesz projection across a spectrum-disjoint annulus; orig was `complexRieszProjectionOnCircle_eq_of_no_eigen_annulus`.
-- generality used: arbitrary finite index type, complex square matrix, complex contour center, and positive ordered real radii; the only spectral hypothesis is pointwise nonsingularity of `zI - A` on the closed annulus, with no real-matrix, algorithm, measure, convexity, smoothness, oracle, normed-space, or additional finite-dimensional assumptions.
-- portable call pattern: finite spectral decompositions for consensus, Markov, and distributed-optimization transition matrices vary the matrix, center, and radii while replacing one admissible contour by another through the same spectrum-free annulus.
-- counterargument checked: not paper-local because contour independence is a standard Riesz-projection property; not a one-line wrapper because Mathlib provides the annulus contour theorem and matrix inverse separately but no theorem proving holomorphy of inverse-resolvent entries and equality of the resulting matrix projections.
-- coverage search: `lean_search_symbols` queries "Riesz projection on circles equal spectrum disjoint annulus" and "circle integral resolvent equal no eigenvalue annulus" found only the paper-local declaration and a private specialized copy inside the staged idempotence proof; `lean_leansearch` query "Riesz projections contour independent when annulus contains no spectrum" found no matching Mathlib declaration.
-- minimal hypotheses: `[Fintype ι] [DecidableEq ι]`, positivity of the inner radius, radius ordering, and determinant nonvanishing throughout the annulus are exactly what the inverse-resolvent holomorphy and annulus contour theorem consume.

private theorem det_analyticAt_of_entry_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) {z₀ : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun z ↦ M z i j) z₀) :
    AnalyticAt ℂ (fun z ↦ det (M z)) z₀ := by
  classical
  simpa [det_apply'] using
    Finset.analyticAt_fun_sum
      (Finset.univ : Finset (Equiv.Perm ι)) (fun σ _ ↦
        analyticAt_const.mul
          (Finset.analyticAt_fun_prod Finset.univ (fun i _ ↦ hM (σ i) i)))

private theorem adjugate_entry_analyticAt_of_entry_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) {z₀ : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun z ↦ M z i j) z₀) (i j : ι) :
    AnalyticAt ℂ (fun z ↦ adjugate (M z) i j) z₀ := by
  classical
  simpa [adjugate_apply] using
    (det_analyticAt_of_entry_analyticAt
      (fun z ↦ (M z).updateRow j (Pi.single i (1 : ℂ)))
      (z₀ := z₀) (by
        intro r c
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow] using
            (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
              (v := ((Pi.single i (1 : ℂ) : ι → ℂ) c)) (x := z₀))
        · simpa [Matrix.updateRow, hr] using hM r c))

private theorem inv_entry_analyticAt_of_entry_analyticAt_of_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) {z₀ : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun z ↦ M z i j) z₀)
    (hdet : det (M z₀) ≠ 0) (i j : ι) :
    AnalyticAt ℂ (fun z ↦ (M z)⁻¹ i j) z₀ := by
  classical
  have hdet_analytic : AnalyticAt ℂ (fun z ↦ det (M z)) z₀ :=
    det_analyticAt_of_entry_analyticAt M hM
  have hinv_det : AnalyticAt ℂ (fun z ↦ (det (M z))⁻¹) z₀ :=
    AnalyticAt.comp_of_eq' (𝕜 := ℂ)
      (g := fun x : ℂ ↦ x⁻¹) (f := fun z ↦ det (M z))
      (y := det (M z₀)) (x := z₀) (analyticAt_inv hdet) hdet_analytic rfl
  have hentry :
      AnalyticAt ℂ (fun z ↦ (det (M z))⁻¹ * adjugate (M z) i j) z₀ :=
    hinv_det.mul (adjugate_entry_analyticAt_of_entry_analyticAt M hM i j)
  simpa [Matrix.inv_def, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using hentry

set_option maxHeartbeats 800000

/-- Riesz projections on two concentric circles are equal when the intervening
closed annulus is disjoint from the spectrum of the matrix.

Layer: Model | Gap: Level 1 (finite-matrix Riesz projection contour independence)
Proof: prove each inverse-resolvent entry holomorphic from the adjugate-over-determinant formula, then apply Mathlib's annulus circle-integral theorem entrywise and retain the common normalization factor.
Source: Mathlib `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`, finite-matrix determinant and adjugate formulas, and nonsingular matrix inversion
Used in: fixed-contour spectral splittings for periodic push-pull transition matrices, where a convenient inner or outer contour replaces the original circle without crossing an eigenvalue
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem rieszProjectionOnCircle_eq_of_spectrum_disjoint_annulus
    {ι : Type*} [Fintype ι] [decEq : DecidableEq ι]
    (A : Matrix ι ι ℂ) (center : ℂ) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hspectrum : ∀ z : ℂ, innerRadius ≤ ‖z - center‖ →
      ‖z - center‖ ≤ outerRadius →
        det (z • (1 : Matrix ι ι ℂ) - A) ≠ 0) :
    rieszProjectionOnCircle A center outerRadius =
      rieszProjectionOnCircle A center innerRadius := by
  classical
  have hdec : decEq = Classical.decEq ι := Subsingleton.elim _ _
  cases hdec
  ext i j
  simp only [rieszProjectionOnCircle_apply]
  apply congrArg (fun x : ℂ ↦ (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) * x)
  refine
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := center) hinner_pos hradii (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · intro z hz
    rcases hz with ⟨hzclosed, hznotball⟩
    have hlower : innerRadius ≤ ‖z - center‖ := by
      have hnotlt : ¬ dist z center < innerRadius := by
        intro hlt
        exact hznotball (Metric.mem_ball.2 hlt)
      simpa [dist_eq_norm] using le_of_not_gt hnotlt
    have hupper : ‖z - center‖ ≤ outerRadius := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp hzclosed
    exact
      ((inv_entry_analyticAt_of_entry_analyticAt_of_det_ne_zero
        (fun w : ℂ ↦ ((fun r c ↦
          w * diagonal (fun _ : ι ↦ (1 : ℂ)) r c - A r c) : Matrix ι ι ℂ))
        (z₀ := z) (by
          intro r c
          exact (analyticAt_id.mul analyticAt_const).sub analyticAt_const)
        (by
          simpa only [Pi.smul_apply, smul_eq_mul, Matrix.sub_apply] using
            (hspectrum z hlower hupper)) i j).differentiableAt).continuousAt.continuousWithinAt
  · intro z hz
    rcases hz with ⟨⟨hzball, hznotclosed⟩, _⟩
    have hlower : innerRadius ≤ ‖z - center‖ := by
      have hnotle : ¬ dist z center ≤ innerRadius := by
        intro hle
        exact hznotclosed (Metric.mem_closedBall.2 hle)
      exact le_of_lt (by simpa [dist_eq_norm] using lt_of_not_ge hnotle)
    have hupper : ‖z - center‖ ≤ outerRadius := by
      exact le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hzball)
    exact
      (inv_entry_analyticAt_of_entry_analyticAt_of_det_ne_zero
        (fun w : ℂ ↦ ((fun r c ↦
          w * diagonal (fun _ : ι ↦ (1 : ℂ)) r c - A r c) : Matrix ι ι ℂ))
        (z₀ := z) (by
          intro r c
          exact (analyticAt_id.mul analyticAt_const).sub analyticAt_const)
        (by
          simpa only [Pi.smul_apply, smul_eq_mul, Matrix.sub_apply] using
            (hspectrum z hlower hupper)) i j).differentiableAt

end Matrix

/-! Promoted from Staging/FiniteNetwork_consensusError_ne_zero_of_nonunit_eigenvector_of_rowStochastic.lean. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: nonunit eigendirections of a finite-network matrix whose rows sum to one lie outside the consensus subspace; orig was `complex_push_nonunit_eigen_consensus_error_norm_pos`.
-- generality used: an arbitrary finite nonempty node type, a real matrix whose rows sum to one, a complex eigenvalue, and a nonzero complex eigenvector; no algorithm setup, periodicity, connectivity, entrywise positivity, measure, convexity, smoothness, oracle, normed-space, or finite-dimensional-space hypotheses are used.
-- portable call pattern: consensus, push-sum, push-pull, and gossip spectral proofs change the finite node type, mixing matrix, complex eigenvalue, and eigenvector while reusing the conclusion that a nonunit eigendirection has nonzero disagreement.
-- counterargument checked: this is not paper-local traceability or a pure wrapper because it composes the row-sum-one fixed-consensus property with the finite-network consensus-error kernel characterization; the combination is absent from Mathlib and SOptLib and removes a recurring spectral contradiction proof.
-- coverage search: `lean_search_symbols` queries "nonunit eigenvector row stochastic matrix consensus error nonzero", "consensus error equals zero iff constant finite network state", and "row stochastic matrix constant vector eigenvalue one" found Mathlib `Matrix.rowStochastic`, SOptLib `FiniteNetwork.consensusError` and `FiniteNetwork.isAgreementState_iff_eq_consensusState`, but no theorem excluding nonunit eigenvectors from consensus; LeanSearch for the complete semantic statement likewise returned only stochastic-matrix and generic eigenvector infrastructure.
-- minimal hypotheses: `[Fintype Node] [Nonempty Node]` support the finite matrix sums and a selected coordinate; the matrix premise is exactly the row-sum-one property used by the proof.

/-- A nonzero eigenvector of a real matrix whose rows sum to one, at an
eigenvalue other than one, has nonzero finite-network consensus error after
complexification.

Layer: Model | Gap: Level 1 (nonunit row-sum-one eigendirection exclusion from consensus)
Proof: zero consensus error makes the eigenvector constant; row sums equal to one make every constant vector a unit eigenvector, so nonzeroness permits cancellation and contradicts the nonunit eigenvalue hypothesis.
Source: Mathlib finite matrices and finite-dimensional eigenspaces, together with SOptLib finite-network consensus error
Used in: the alpha-zero period-map spectral split for stochastic push-pull, and in consensus, push-sum, and gossip proofs that separate the unit consensus mode from all nonunit eigendirections
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusError_ne_zero_of_nonunit_eigenvector_of_sum_row_eq_one
    {Node : Type*} [Fintype Node] [Nonempty Node]
    (A : Matrix Node Node ℝ) (gamma : ℂ) (x : Node → ℂ)
    (hrow : ∀ i, ∑ j, A i j = 1)
    (hx_ne : x ≠ 0)
    (hx : Matrix.mulVec (fun i j => (A i j : ℂ)) x = gamma • x)
    (hgamma_ne_one : gamma ≠ 1) :
    consensusError x ≠ 0 := by
  classical
  intro herror
  let c : ℂ := meanState x
  have hx_const : x = fun _ : Node => c := by
    funext i
    have hi := congrFun herror i
    simpa [consensusError_apply, c] using sub_eq_zero.mp hi
  have hc_ne : c ≠ 0 := by
    intro hc
    apply hx_ne
    rw [hx_const]
    funext i
    simp [hc]
  have hleft :
      Matrix.mulVec (fun i j => (A i j : ℂ)) x = fun _ : Node => c := by
    funext i
    calc
      Matrix.mulVec (fun i j => (A i j : ℂ)) x i =
          ∑ j : Node, (A i j : ℂ) * c := by
            simp [Matrix.mulVec, dotProduct, hx_const]
      _ = ((∑ j : Node, A i j : ℝ) : ℂ) * c := by simp [Finset.sum_mul]
      _ = c := by rw [hrow i]; simp
  obtain ⟨i₀⟩ := ‹Nonempty Node›
  have hi := congrFun (hleft.symm.trans hx) i₀
  have hgamma_c : gamma * c = c := by
    simpa [Pi.smul_apply, smul_eq_mul, hx_const] using hi.symm
  apply hgamma_ne_one
  apply (mul_right_cancel₀ hc_ne)
  simpa using hgamma_c

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consecutiveProduct_add.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: newest-on-the-left consecutive product and its adjacent-window composition law; orig was consecutiveProduct_add over paper-local node matrices.
-- generality used: an arbitrary monoid-valued natural-time schedule; no matrix, finiteness, decidable-equality, scalar, order, topology, norm, measure, stochasticity, convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: switched-system, consensus, gossip, push-sum, and distributed-optimization proofs change the monoid-valued schedule, start time, and two window lengths while retaining the newest-on-the-left convention and the same concatenation equality.
-- counterargument checked: not paper-local or a caller-side expression because noncommutative factor order and the shifted start are theorem-critical; the earlier staged consecutiveMatrixProduct attempt was rolled back and was only matrix/semiring-specific, whereas this declaration is the underlying monoid law.
-- coverage search: lean_search_symbols queries "consecutive product monoid sequence concatenation equality later window times earlier window" and "product range add split sequence reverse order noncommutative monoid" found no applicable SOptLib or Mathlib declaration; LeanSearch returned commutative Finset product splitting results, which do not preserve this noncommutative newest-on-the-left order.
-- minimal hypotheses: `[Monoid M]` is exactly what supplies the empty product, multiplication, and associativity; all matrix and algorithm assumptions were removed.

/-- The product of a consecutive window in a monoid-valued schedule, ordered
with the newest term on the left.

The length-zero window is the identity, and extending a window multiplies the
newest schedule value on the left.

Layer: Model | Concept: newest-on-the-left consecutive monoid product
Proof: (definitional construction; primitive recursion on the window length with the monoid identity at zero and the newest schedule value multiplied on the left)
Source: Mathlib monoids and natural-number primitive recursion
Used in: finite propagation windows for time-varying switched systems, consensus, gossip, push-sum, and push-pull schedules
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def consecutiveProduct {M : Type*} [Monoid M]
    (A : Nat -> M) (t : Nat) : Nat -> M
  | 0 => 1
  | k + 1 => A (t + k) * consecutiveProduct A t k

/-- A zero-length consecutive monoid window is the identity.

Layer: Model | Gap: Level 0 (zero-length consecutive monoid product specification)
Proof: by rfl after unfolding `FiniteNetwork.consecutiveProduct` at zero.
Source: Mathlib monoid identity and natural-number primitive recursion
Used in: initializing finite propagation-window inductions for switched systems and time-varying networks
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem consecutiveProduct_zero {M : Type*} [Monoid M]
    (A : Nat -> M) (t : Nat) :
    consecutiveProduct A t 0 = 1 := by
  rfl

/-- Extending a consecutive monoid window multiplies its newest schedule value
on the left.

Layer: Model | Gap: Level 0 (successor consecutive monoid product specification)
Proof: by rfl after unfolding `FiniteNetwork.consecutiveProduct` at a successor length.
Source: Mathlib monoid multiplication and natural-number primitive recursion
Used in: successor steps for propagation, stochasticity, minorization, and contraction properties of time-varying network products
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem consecutiveProduct_succ {M : Type*} [Monoid M]
    (A : Nat -> M) (t k : Nat) :
    consecutiveProduct A t (k + 1) =
      A (t + k) * consecutiveProduct A t k := by
  rfl

/-- A consecutive product over two adjacent windows is the later window
product multiplied on the left of the earlier window product.

Layer: Model | Gap: Level 1 (adjacent-window composition for ordered monoid schedules)
Proof: induct on the later window length, unfold the successor equation, and use monoid associativity after normalizing the shifted natural-number index.
Source: Mathlib monoid associativity and natural-number addition
Used in: splitting time-varying switched-system and network propagation into complete contraction blocks and a residual window
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveProduct_add {M : Type*} [Monoid M]
    (A : Nat -> M) (t j k : Nat) :
    consecutiveProduct A t (j + k) =
      consecutiveProduct A (t + j) k * consecutiveProduct A t j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, consecutiveProduct_succ, ih,
        consecutiveProduct_succ, mul_assoc]
      rw [Nat.add_assoc]

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consecutiveMatrixProduct_mulVec_eq_of_step.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-window matrix evolution obtained by iterating a one-step time-varying linear recurrence; orig was competitor_pull_product.
-- generality used: arbitrary finite node type and scalar semiring, a natural-time-indexed square-matrix schedule, and a scalar-vector trajectory satisfying a pointwise one-step recurrence; no order, stochasticity, positivity, topology, norm, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses.
-- portable call pattern: push-sum, gradient-tracking, nonhomogeneous Markov, and switched-linear-system proofs change the matrix schedule, vector trajectory, start time, and window length while retaining `A s *ᵥ v s = v (s + 1)` and the same finite-window evolution equality.
-- counterargument checked: not paper-local because iterating a nonautonomous linear recurrence through an ordered transition product recurs across network and switched-system analyses; not a pure wrapper because Mathlib provides the identity and multiplication action laws but no theorem composing an arbitrary time-indexed one-step recurrence across a consecutive window.
-- coverage search: lean_search_symbols queries "consecutive product recurrence maps initial vector to final vector", "newest left ordered product mulVec one step equality", and "matrix product action vector one step evolution induction" found only `FiniteNetwork.consecutiveProduct_add` plus unrelated product and matrix-vector declarations; LeanSearch found `Matrix.mulVec_mulVec`, `Matrix.one_mulVec`, and linear-map action lemmas, but no finite-window recurrence theorem.
-- minimal hypotheses: `[Semiring R]` supplies square-matrix multiplication and scalar `mulVec`, while `[Fintype Node] [DecidableEq Node]` supply the finite contractions and identity matrix; the recurrence is pointwise in time and all algorithm-specific setup assumptions were removed.

/-- A newest-on-the-left consecutive matrix product carries a vector trajectory
across the corresponding time window when every one-step matrix action advances
that trajectory.

Layer: Model | Gap: Level 1 (finite-window evolution for a nonautonomous matrix recurrence)
Proof: induct on the window length; use `Matrix.one_mulVec` at zero and `Matrix.mulVec_mulVec` together with the one-step recurrence at the successor.
Source: Mathlib finite matrices, semiring matrix multiplication, `Matrix.one_mulVec`, and `Matrix.mulVec_mulVec`
Used in: propagating pull weights, push-sum masses, gradient-tracking weights, and nonhomogeneous finite-state linear evolutions across a consecutive communication window
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveProduct_mulVec_eq_of_step
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [Semiring R]
    (A : Nat -> Matrix Node Node R) (v : Nat -> Node -> R)
    (t j : Nat)
    (hstep : ∀ k < j,
      (A (t + k)).mulVec (v (t + k)) = v (t + k + 1)) :
    (consecutiveProduct A t j).mulVec (v t) = v (t + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [consecutiveProduct_succ, ← Matrix.mulVec_mulVec,
        ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk)),
        hstep j (Nat.lt_succ_self j)]
      congr 1

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_vecMul_consecutiveMatrixProduct_eq_of_step.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: backward finite-window row-vector evolution under a newest-on-the-left consecutive matrix product; orig was competitor_push_product.
-- generality used: arbitrary finite node type and scalar semiring, a natural-time-indexed square-matrix schedule, and a scalar row-vector trajectory satisfying a window-local backward one-step recurrence; no order, stochasticity, positivity, topology, norm, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses.
-- portable call pattern: absolute-probability-sequence, nonhomogeneous Markov-chain, push-sum, consensus, and switched-linear-system proofs change the matrix schedule, row-vector trajectory, start time, and window length while retaining `w (s + 1) ᵥ* A s = w s` and the same finite-window equality.
-- counterargument checked: not paper-local because backward propagation of row distributions through time-ordered transition products recurs across network and Markov-chain analyses; not a duplicate of the staged pull lemma because that theorem advances column vectors by left action, while this theorem propagates row vectors backward by right action and uses the opposite action-association step.
-- coverage search: lean_search_symbols queries "right row vector matrix consecutive product one step backward equality vecMul" and "Matrix vecMul matrix multiplication associativity" found the directionally distinct staged `FiniteNetwork.consecutiveProduct_mulVec_eq_of_step` and Mathlib's local `Matrix.vecMul_vecMul`; LeanSearch for the complete backward finite-window recurrence found no theorem packaging its iteration.
-- minimal hypotheses: `[Semiring R]` supplies square-matrix multiplication, identity, and `vecMul`; `[Fintype Node] [DecidableEq Node]` supply finite contraction and the identity matrix; the recurrence is required only at offsets inside the requested window.

/-- A newest-on-the-left consecutive matrix product carries a row-vector
trajectory backward across the corresponding time window when every one-step
right matrix action moves that trajectory back by one time index.

Layer: Model | Gap: Level 1 (backward finite-window evolution for a nonautonomous row-vector recurrence)
Proof: induct on the window length; use the identity action at zero and `Matrix.vecMul_vecMul` with the newest one-step recurrence at the successor.
Source: Mathlib finite matrices, semiring matrix multiplication, identity-matrix vector action, and `Matrix.vecMul_vecMul`
Used in: propagating absolute probability rows and push weights backward across a consecutive communication window in time-varying consensus and push-pull analyses
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem vecMul_consecutiveMatrixProduct_eq_of_step
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [Semiring R]
    (A : Nat -> Matrix Node Node R) (w : Nat -> Node -> R)
    (t j : Nat)
    (hstep : ∀ k < j,
      Matrix.vecMul (w (t + k + 1)) (A (t + k)) = w (t + k)) :
    Matrix.vecMul (w (t + j)) (consecutiveProduct A t j) = w t := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show t + (j + 1) = t + j + 1 by
        exact (Nat.add_assoc t j 1).symm]
      rw [consecutiveProduct_succ, ← Matrix.vecMul_vecMul,
        hstep j (Nat.lt_succ_self j),
        ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))]

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_periodProduct_fixedPoints_of_pushPullPerronEquations_of_periodic.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: period-product fixed points of paired periodic matrix recurrences; orig was competitor_phase_stationary.
-- generality used: arbitrary finite node carrier, semiring-valued matrix schedules, a natural period, and paired semiring-valued node-vector sequences satisfying left/right one-step recurrences and the two period equalities; no nonemptiness, normalization, stochasticity, positivity, schedule periodicity, uniqueness, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are used.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, switched-system, and nonhomogeneous Markov-chain proofs change their scalar semiring, schedules, period, and vector sequences while retaining the one-step left/right evolution equations and sequence periodicity, obtaining fixed points for every phase-start full-period product.
-- counterargument checked: this is not merely paper traceability or a pure wrapper because it packages two oppositely oriented nonautonomous recurrences and periodic endpoint identification into the paired phase-product stationary conclusion used repeatedly in periodic-network analysis; Mathlib's fixed-map periodic-point API does not cover time-ordered varying matrix schedules.
-- coverage search: lean_search_symbols queries "period product fixed points of left and right Perron evolution equations periodic sequences" and "consecutive matrix product fixed vector periodic trajectory one step recurrence" found the staged `FiniteNetwork.PushPullPerronEquations` and the two separate finite-window recurrence theorems, but no declaration combining them with periodic endpoints; LeanSearch for periodic left/right matrix recurrences returned `Function.IsPeriodicPt.isFixedPt`, which concerns iterates of one fixed self-map and is only partial coverage.
-- minimal hypotheses: normalization, positivity, and periodicity of `R` and `C` are omitted because the proof uses only the two recurrences and the two sequence-period equations; `[Semiring S] [Fintype Node] [DecidableEq Node]` are exactly required by finite matrix products and matrix-vector actions.

/-- A periodic pair satisfying left and right one-step matrix recurrences is
fixed by every phase-start full-period matrix product.

The left sequence is a fixed row vector of the first product, while the right
sequence is a fixed column vector of the second product at the same phase.

Layer: Model | Gap: Level 1 (paired phase-product fixed points from periodic recurrences)
Proof: apply the backward row-vector and forward column-vector finite-window recurrence theorems to one full period, then identify each terminal sequence value with its initial value by periodicity.
Source: periodic linear recurrences and SOptLib consecutive matrix-product evolution
Used in: periodic push-pull, gradient-tracking, switched-system, and nonhomogeneous finite-state linear-evolution proofs that turn one-step recurrences into fixed vectors for each phase-dependent full-period product
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodProduct_fixedPoints_of_step_recurrences_of_periodic
    {Node S : Type*} [Fintype Node] [DecidableEq Node] [Semiring S]
    (R C : Nat -> Matrix Node Node S) (p : Nat)
    (seqs : (Nat -> Node -> S) × (Nat -> Node -> S))
    (hLeft : ∀ t : Nat,
      Matrix.vecMul (seqs.1 (t + 1)) (R t) = seqs.1 t)
    (hRight : ∀ t : Nat,
      (C t).mulVec (seqs.2 t) = seqs.2 (t + 1))
    (hLeftPeriodic : ∀ t : Nat, seqs.1 (t + p) = seqs.1 t)
    (hRightPeriodic : ∀ t : Nat, seqs.2 (t + p) = seqs.2 t) :
    (∀ t : Nat,
      Matrix.vecMul (seqs.1 t) (consecutiveProduct R t p) = seqs.1 t) ∧
      (∀ t : Nat,
        (consecutiveProduct C t p).mulVec (seqs.2 t) = seqs.2 t) := by
  constructor
  · intro t
    have hproduct := vecMul_consecutiveMatrixProduct_eq_of_step R seqs.1 t p
      (fun k _ => hLeft (t + k))
    rw [hLeftPeriodic t] at hproduct
    exact hproduct
  · intro t
    have hproduct := consecutiveProduct_mulVec_eq_of_step C seqs.2 t p
      (fun k _ => hRight (t + k))
    rw [hRightPeriodic t] at hproduct
    exact hproduct

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consecutiveMatrixProduct_entry_nonneg.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: entrywise nonnegativity of a consecutive time-varying matrix product; orig was consecutiveProduct_entry_nonneg.
-- generality used: arbitrary finite node type and scalar semiring with a partial ordered-ring structure, a natural-time-indexed square-matrix schedule, start time, window length, and selected entry; no stochasticity, positivity beyond entrywise nonnegativity, topology, norm, measure, convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: consensus, gossip, push-sum, gradient-tracking, and nonhomogeneous Markov-chain proofs change the finite node type, ordered semiring, matrix schedule, start time, window length, and selected entry while retaining nonnegativity of every accumulated transition-product entry.
-- counterargument checked: Mathlib's `Matrix.pow_apply_nonneg` covers powers of one fixed matrix and `dotProduct_nonneg_of_nonneg` covers one multiplication entry, but neither covers a nonautonomous ordered product; the result is therefore not paper-local, a pure rename, or a caller-side expression.
-- coverage search: lean_search_symbols queries "entrywise nonnegative matrices product entry nonnegative semiring ordered", "consecutive matrix product entries nonnegative each factor entry nonnegative", and "matrix multiplication nonnegative entries of nonnegative matrices" found only the source declaration and partial matrix/order infrastructure; LeanSearch found `Matrix.pow_apply_nonneg`, `dotProduct_nonneg_of_nonneg`, and scalar `mul_nonneg`, but no time-varying consecutive-product theorem.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` form square-matrix multiplication and its identity; `[Semiring R] [PartialOrder R] [IsOrderedRing R]` give nonnegative zero, one, products, and finite sums; the schedule hypothesis is pointwise entrywise nonnegativity and no algorithm setup assumptions remain.

/-- Every entry of a consecutive product of entrywise nonnegative square
matrices is nonnegative.

Layer: Model | Gap: Level 1 (entrywise nonnegativity of time-varying consecutive matrix products)
Proof: induct on the window length; the identity matrix is entrywise nonnegative, and each successor entry is a finite sum of products of nonnegative entries.
Source: Mathlib finite matrix multiplication, ordered semirings, `Finset.sum_nonneg`, and `Matrix.one_apply`
Used in: time-varying consensus and push-pull block-minorization arguments that first establish nonnegativity of accumulated communication weights before deriving strict lower bounds
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveMatrixProduct_entry_nonneg
    {Node R : Type*} [Fintype Node] [DecidableEq Node]
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (A : Nat -> Matrix Node Node R)
    (t k : Nat)
    (hA : ∀ s < k, ∀ i j : Node, 0 <= A (t + s) i j)
    (i j : Node) :
    0 <= consecutiveProduct A t k i j := by
  induction k generalizing i j with
  | zero =>
      simp only [consecutiveProduct_zero, Matrix.one_apply]
      split_ifs <;> simp
  | succ k ih =>
      rw [consecutiveProduct_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun u _ =>
        mul_nonneg
          (hA k (Nat.lt_succ_self k) i u)
          (ih (fun s hs => hA s (Nat.lt_succ_of_lt hs)) u j)

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consecutiveMatrixProduct_mem_rowStochastic.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: row-stochasticity of a consecutive time-varying matrix product; orig was consecutiveProduct_rowStochastic.
-- generality used: arbitrary finite node type, arbitrary partially ordered semiring satisfying `IsOrderedRing`, a natural-time-indexed square-matrix schedule, start time, and window length; no real scalars, nonempty node assumption, topology, norm, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses.
-- portable call pattern: consensus, gossip, push-sum, gradient-tracking, and nonhomogeneous Markov-chain proofs change the finite node type, ordered semiring, matrix schedule, start time, and window length while retaining row-stochasticity of every factor in the selected window.
-- counterargument checked: Mathlib packages row-stochastic matrices as a submonoid, but provides no theorem connecting that submonoid to a nonautonomous consecutive-product schedule; the result packages the reusable finite-window induction rather than merely renaming one multiplication closure fact.
-- coverage search: lean_search_symbols queries "consecutive product matrices row stochastic if each matrix row stochastic", "row stochastic matrix multiplication closed semiring", "finite product row stochastic matrices", and "Matrix mem_rowStochastic mul" found no consecutive-product theorem; LeanSearch found Mathlib's row- and doubly-stochastic submonoids and their one-step multiplication closure, but no time-varying window result.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node] [Semiring R] [PartialOrder R] [IsOrderedRing R]` are exactly the parameters of Mathlib's row-stochastic submonoid; the factor hypothesis is restricted to offsets inside the requested window.

/-- A consecutive product of row-stochastic square matrices is row stochastic
when every factor in the selected time window is row stochastic.

Layer: Model | Gap: Level 1 (row-stochasticity of time-varying consecutive matrix products)
Proof: induct on the window length and use the identity and multiplication closure laws of Mathlib's `Matrix.rowStochastic` submonoid at the zero and successor steps.
Source: Mathlib row-stochastic matrix submonoid and monoid multiplication in `Mathlib.LinearAlgebra.Matrix.Stochastic`
Used in: time-varying consensus and push-pull contraction proofs, where accumulated communication products must remain row stochastic before applying diameter nonexpansiveness or block minorization
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveMatrixProduct_mem_rowStochastic
    {Node R : Type*} [Fintype Node] [DecidableEq Node]
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (A : Nat -> Matrix Node Node R) (t k : Nat)
    (hA : ∀ s < k, A (t + s) ∈ Matrix.rowStochastic R Node) :
    consecutiveProduct A t k ∈ Matrix.rowStochastic R Node := by
  induction k with
  | zero =>
      exact (Matrix.rowStochastic R Node).one_mem
  | succ k ih =>
      rw [consecutiveProduct_succ]
      exact (Matrix.rowStochastic R Node).mul_mem
        (hA k (Nat.lt_succ_self k))
        (ih (fun s hs => hA s (Nat.lt_succ_of_lt hs)))

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consensusError_add_const.lean. -/


noncomputable section

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: translation invariance of finite-network consensus error; orig was `consensusError_add_constant`.
-- generality used: arbitrary finite node type and additive commutative real-module state space; no nonemptiness, norm, topology, completeness, inner product, finite-dimensionality, measure, convexity, smoothness, independence, integrability, or oracle assumptions are used.
-- portable call pattern: consensus, push-sum, push-pull, and gradient-tracking proofs change the node type, module-valued state, and common translation while reusing that the disagreement component is unchanged.
-- counterargument checked: not paper-local or merely caller-side algebra because translation invariance is a stable API property of the named `FiniteNetwork.consensusError`; it is not a pure rename of the available finite-average constant theorem.
-- coverage search: `lean_search_symbols` queries "finite network consensus error unchanged under adding constant state translation invariance", "FiniteNetwork consensusError add constant", and "finite uniform average add constant function" found the source theorem, `FiniteNetwork.consensusError_apply`, and `SOptLib.finiteUniformAverage_const`, but no theorem with this conclusion; LeanSearch found the analogous `Fintype.balance_add` and `Finset.expect_const` APIs for different averaging objects.
-- minimal hypotheses: `[Fintype Node]` is the indexing assumption of `FiniteNetwork.consensusError`; the empty-node case is vacuous, while `[AddCommGroup E] [Module ℝ E]` are exactly its algebraic assumptions and those needed for subtraction cancellation.

/-- Adding the same state at every node does not change the finite-network
consensus error.

Layer: Model | Gap: Level 0 (translation invariance of finite-network disagreement)
Proof: split on whether the node type is empty; the empty case is vacuous, while in the nonempty case distribute the finite uniform average across the pointwise sum, reduce the average of the constant state with `SOptLib.finiteUniformAverage_const`, and cancel the common translation coordinatewise.
Source: Mathlib pointwise function addition and additive-group cancellation, together with SOptLib finite-uniform average and finite-network consensus error
Used in: consensus and gradient-tracking initial-state and recurrence proofs that remove a common node translation before estimating the disagreement component
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/14
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem consensusError_add_const
    {Node E : Type*} [Fintype Node]
    [AddCommGroup E] [Module ℝ E] (X : Node → E) (x : E) :
    consensusError (X + fun _ => x) = consensusError X := by
  classical
  cases isEmpty_or_nonempty Node with
  | inl hNode =>
      letI := hNode
      funext i
      exact isEmptyElim i
  | inr hNode =>
      letI := hNode
      have hmean : meanState (X + fun _ => x) = meanState X + x := by
        change SOptLib.finiteUniformAverage (X + fun _ => x) =
          SOptLib.finiteUniformAverage X + x
        calc
          SOptLib.finiteUniformAverage (X + fun _ => x) =
              SOptLib.finiteUniformAverage X +
                SOptLib.finiteUniformAverage (fun _ : Node => x) := by
            simp [SOptLib.finiteUniformAverage_def, Finset.sum_add_distrib, smul_add]
          _ = SOptLib.finiteUniformAverage X + x := by
            rw [SOptLib.finiteUniformAverage_const]
      funext i
      simp only [consensusError_apply, Pi.add_apply, hmean]
      abel

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consensusError_eq_self_of_sum_eq_zero.lean. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: fixed-point property of the finite-network consensus-error projector on zero-sum states; orig was `consensusError_eq_self_of_sum_eq_zero`.
-- generality used: arbitrary finite node carrier and additive commutative real-module state space; no node nonemptiness, norm, topology, completeness, inner product, finite-dimensionality, measure, convexity, smoothness, independence, integrability, or oracle assumptions are used.
-- portable call pattern: consensus, tracking, push-sum, and push-pull proofs change the finite node type and module-valued zero-sum state while reusing that removing the uniform consensus component leaves the state unchanged.
-- counterargument checked: Mathlib's `Fintype.balance` is an analogous averaging projector, but no theorem found states this fixed-point contract for SOptLib's named `FiniteNetwork.consensusError`; this is a stable projector API property rather than paper-local traceability or a caller-side expression.
-- coverage search: `lean_search_symbols` queries "finite network consensus error equals self sum zero", "finite uniform average equals zero when finite sum equals zero", and "disagreement projector fixes zero sum state" found `FiniteNetwork.consensusError`, its unfolding/apply lemmas, and unrelated zero-sum results but no matching theorem; LeanSearch returned `Fintype.balance` and `Fintype.sum_balance`, which concern Mathlib's nonnegative-rational averaging object and do not cover this real-module consensus-error API.
-- minimal hypotheses: `[Fintype Node]`, `[AddCommGroup E]`, and `[Module ℝ E]` are exactly the assumptions of `FiniteNetwork.consensusError`; the original `[Nonempty Node]`, normed-space, Hilbert-space, completeness, and finite-dimensional assumptions are unnecessary, and the sole data hypothesis is the coordinate-sum equality used by the proof.

/-- The finite-network consensus-error projector fixes every state whose
coordinate sum is zero.

Layer: Model | Gap: Level 0 (zero-sum fixed point of the finite-network disagreement projector)
Proof: unfold the consensus error and finite uniform mean, rewrite the coordinate sum to zero, and simplify the resulting zero consensus component pointwise.
Source: finite-dimensional consensus projector algebra, Mathlib finite sums, and SOptLib finite-network consensus error and finite-uniform average
Used in: push-pull and gradient-tracking joint-coordinate decompositions where an already centered network state passes unchanged through the consensus-error projector
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/14
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem consensusError_eq_self_of_sum_eq_zero
    {Node E : Type*} [Fintype Node] [AddCommGroup E] [Module ℝ E]
    (X : Node → E) (hX : ∑ i : Node, X i = 0) :
    consensusError X = X := by
  funext i
  simp [consensusError_apply, meanState, SOptLib.finiteUniformAverage, hX]

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consensusError_smulVec_consensusError_of_rowStochastic.lean. -/


noncomputable section

open scoped BigOperators Matrix.Module

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: a matrix action whose rows sum to one depends only on the finite-network consensus error; orig was `consensusError_leftMul_consensusError`.
-- generality used: arbitrary finite nonempty node type with decidable equality and additive real module state space, assuming only that every matrix row sums to one; no entrywise nonnegativity, norm, topology, completeness, inner-product, finite-dimensional, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: consensus, gossip, push-sum, and push-pull recurrences change the node type, mixing matrix, and module-valued state while reusing the equality that removes the constant consensus component before matrix mixing and reprojection.
-- counterargument checked: not paper-local or a pure rename because it links the row-sum-one matrix action contract to SOptLib's named consensus-error projection; neither Mathlib nor SOptLib already supplies this representation-invariance theorem.
-- coverage search: `lean_search_symbols` queries "consensus error matrix smul vector equality row stochastic", "row stochastic matrix constant state sum smul consensus error", and "FiniteNetwork consensusError add constant unchanged" found `Matrix.sum_row_of_mem_rowStochastic`, `FiniteNetwork.consensusError_apply`, and the paper-local source theorem but no theorem with this equality; LeanSearch for the full semantic contract returned stochastic-matrix APIs but no consensus-error result.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support the matrix action and finite averages, `[Nonempty Node]` makes the uniform average of a constant equal that constant, `[AddCommGroup E] [Module ℝ E]` are exactly the state-space assumptions used, and the pointwise row-sum-one hypothesis is precisely the matrix property driving the proof.

/-- The consensus error after a matrix action whose rows sum to one depends
only on the input consensus error.

Layer: Model | Gap: Level 1 (row-sum-one action invariance under removal of the consensus component)
Proof: split the state into its disagreement part and constant mean; the row-sum-one property preserves the constant mean, and finite uniform averaging shows that adding a constant state does not change consensus error.
Source: Mathlib finite matrix-module actions, together with SOptLib finite-network consensus error and finite-uniform average
Used in: consensus and gradient-tracking recurrences that remove the current network-average component before propagating disagreement through a row-normalized mixing matrix
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/19
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusError_smulVec_consensusError_of_sum_row_eq_one
    {Node E : Type*} [Fintype Node] [DecidableEq Node] [Nonempty Node]
    [AddCommGroup E] [Module ℝ E]
    (A : Matrix Node Node ℝ) (X : Node → E)
    (hrow : ∀ i, ∑ j, A i j = 1) :
    consensusError (A • X) = consensusError (A • consensusError X) := by
  classical
  let avg := meanState X
  have hsplit :
      A • X = A • consensusError X + fun _ => avg := by
    funext i
    simp only [Matrix.Module.smul_apply, consensusError_apply, Pi.add_apply,
      smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hrow i]
    simp [avg]
  have hconstant (Y : Node → E) (c : E) :
      consensusError (Y + fun _ => c) = consensusError Y := by
    have hmean : meanState (Y + fun _ => c) = meanState Y + c := by
      change SOptLib.finiteUniformAverage (Y + fun _ => c) =
        SOptLib.finiteUniformAverage Y + c
      calc
        SOptLib.finiteUniformAverage (Y + fun _ => c) =
            SOptLib.finiteUniformAverage Y +
              SOptLib.finiteUniformAverage (fun _ : Node => c) := by
          simp [SOptLib.finiteUniformAverage_def, Finset.sum_add_distrib,
            smul_add]
        _ = SOptLib.finiteUniformAverage Y + c := by
          rw [SOptLib.finiteUniformAverage_const]
    funext i
    simp only [consensusError_apply, Pi.add_apply, hmean]
    abel
  rw [hsplit, hconstant]

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consensusError_smul_const.lean. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: compatibility of finite-network consensus error with a scalar coefficient row acting on a fixed module vector; orig was `consensusError_rankOne`.
-- generality used: arbitrary finite node carrier and additive commutative real-module state space; no node nonemptiness, decidable equality, norm, topology, completeness, inner product, finite-dimensionality, measure, convexity, smoothness, independence, integrability, or oracle assumptions are used.
-- portable call pattern: consensus, push-sum, push-pull, and gradient-tracking proofs change the finite node type, scalar coefficient row, and module vector while reusing that centering a rank-one state centers only its scalar row.
-- counterargument checked: although the proof is short algebra, this is a stable interaction theorem between the named consensus-error projector and rank-one module states, not a paper-local projector-matrix wrapper or a pure rename of an existing result.
-- coverage search: `lean_search_symbols` queries "consensus error scalar multiple constant vector equals consensus projector matrix coefficient row scalar tensor vector", "consensusError fixed vector scalar coefficient smul commutes", and "finite uniform average scalar multiples fixed module vector" found the local source theorem, the distinct row-sum-one matrix-action theorem, and the finite-uniform-average API, but no matching theorem; LeanSearch for a finite average of scalar multiples of a fixed module vector did not return an applicable named result.
-- minimal hypotheses: `[Fintype Node]`, `[AddCommGroup E]`, and `[Module ℝ E]` are exactly the assumptions of `FiniteNetwork.consensusError`; all stronger source assumptions were removed.

/-- Centering a node-indexed family of scalar multiples of one fixed vector
centers the scalar coefficient row and leaves the vector unchanged.

Layer: Model | Gap: Level 0 (rank-one compatibility of finite-network consensus error)
Proof: expand the finite-network mean, move the finite scalar sum through the fixed vector using `Finset.sum_smul`, and combine nested scalar actions before distributing subtraction.
Source: Mathlib finite sums and real module scalar-action identities, together with SOptLib finite-network consensus error and finite-uniform average
Used in: directed consensus and push-pull tracker decompositions that project a Perron-weighted aggregate state onto its disagreement component
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/20
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusError_smul_const
    {Node E : Type*} [Fintype Node] [AddCommGroup E] [Module ℝ E]
    (v : Node → ℝ) (x : E) :
    consensusError (fun i => v i • x) = fun i => consensusError v i • x := by
  classical
  funext i
  simp only [consensusError_apply, meanState, SOptLib.finiteUniformAverage_def]
  rw [← Finset.sum_smul, smul_smul, sub_smul]
  simp only [smul_eq_mul]

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_consensusProjectorMatrix.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network consensus projector matrix; orig was `consensusProjectorMatrix`.
-- generality used: arbitrary finite node type with decidable equality and real matrix entries; no nonemptiness, algorithm setup, stochasticity, norm, topology, finite-dimensional, measure, convexity, smoothness, or oracle assumptions are needed.
-- portable call pattern: consensus, gossip, push-sum, and gradient-tracking proofs change the finite node type while applying the same matrix to split a scalar network vector into its uniform-consensus and disagreement components.
-- counterargument checked: although the defining formula is short, the standard disagreement projector is a recognized finite-network object used across several matrix identities and contraction arguments; Mathlib's abstract complementary projections and stochastic-matrix API do not provide this concrete uniform-averaging matrix.
-- coverage search: `lean_search_symbols` queries "finite network consensus projector matrix identity minus uniform averaging rank one matrix", "matrix identity minus constant inverse cardinality projection disagreement", and "orthogonal projection mean zero functions finite type matrix" found only the paper-local declaration and related consensus-error theorems; LeanSearch for "matrix identity minus all ones matrix divided by finite cardinality consensus projection" found stochastic-matrix identity actions and abstract complementary projections, but no matching concrete matrix definition.
-- minimal hypotheses: `[Fintype Node]` supplies the network cardinality and `[DecidableEq Node]` supplies the identity matrix; all source assumptions beyond this finite-matrix structure are dropped.

/-- The matrix that removes the uniform-consensus component of a finite real
network vector, `I - 11ᵀ / n`.

Layer: Model | Concept: finite-network uniform-consensus projector matrix
Proof: (definitional construction; subtract the constant inverse-cardinality matrix from the identity matrix)
Source: Mathlib finite matrices, identity matrices, and real inverse cardinalities; the standard disagreement projection from finite-network consensus theory
Used in: consensus, gossip, push-sum, and gradient-tracking decompositions that project Perron weights or node states onto the disagreement component before a contraction estimate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/14
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def consensusProjectorMatrix
    {Node : Type*} [Fintype Node] [DecidableEq Node] : Matrix Node Node Real :=
  (1 : Matrix Node Node Real) -
    Matrix.of (fun _ _ => (Fintype.card Node : Real)⁻¹)

/-- The finite-network consensus projector unfolds to the identity matrix minus
the constant uniform-averaging matrix.

Layer: Model | Gap: Level 0 (definitional specification of the uniform-consensus projector matrix)
Proof: by rfl after unfolding `FiniteNetwork.consensusProjectorMatrix`.
Source: Mathlib finite matrices, identity matrices, and real inverse cardinalities
Used in: entrywise and matrix-action calculations for consensus, gossip, push-sum, and gradient-tracking decompositions
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/14
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem consensusProjectorMatrix_def
    {Node : Type*} [Fintype Node] [DecidableEq Node] :
    consensusProjectorMatrix (Node := Node) =
      (1 : Matrix Node Node Real) -
        Matrix.of (fun _ _ => (Fintype.card Node : Real)⁻¹) := by
  rfl

/-- Each entry of the finite-network consensus projector is the corresponding
identity entry minus the inverse network cardinality.

Layer: Model | Gap: Level 0 (entrywise specification of the uniform-consensus projector matrix)
Proof: unfold `FiniteNetwork.consensusProjectorMatrix` and evaluate matrix subtraction and the identity matrix entrywise.
Source: Mathlib pointwise matrix subtraction and `Matrix.one_apply`
Used in: rewriting projected Perron vectors and node states into coordinatewise disagreement formulas in consensus and gradient-tracking arguments
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/14
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem consensusProjectorMatrix_apply
    {Node : Type*} [Fintype Node] [DecidableEq Node] (i j : Node) :
    consensusProjectorMatrix (Node := Node) i j =
      (if i = j then 1 else 0) - (Fintype.card Node : Real)⁻¹ := by
  simp [consensusProjectorMatrix, Matrix.one_apply]

/-- Acting by the finite-network consensus projector removes the uniform mean
from every coordinate, producing the finite-network consensus error.

Layer: Model | Gap: Level 0 (matrix-action characterization of the uniform-consensus projector)
Proof: distribute matrix subtraction through `mulVec`, collapse the identity action, and identify the constant-matrix action with the finite uniform average.
Source: Mathlib matrix-vector multiplication and SOptLib finite-network consensus-error and finite-uniform-average APIs
Used in: consensus, gossip, push-sum, and gradient-tracking proofs that pass between matrix projector notation and centered network states
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/14
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusProjectorMatrix_mulVec
    {Node : Type*} [Fintype Node] [DecidableEq Node] (v : Node → Real) :
    (consensusProjectorMatrix (Node := Node)).mulVec v = consensusError v := by
  rw [consensusProjectorMatrix_def, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    consensusError_apply, meanState_def, SOptLib.finiteUniformAverage_def,
    smul_eq_mul]
  rw [Finset.mul_sum]

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_effectiveNodeCount.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: effective node count from aggregate gain and average squared influence; orig was `effectiveNodeCount` on the time-varying push-pull setup.
-- generality used: two real scalars representing aggregate influence gain and average squared influence; no node carrier, finiteness, network schedule, measure, convexity, smoothness, oracle, normed-space, inner-product, or finite-dimensional assumptions are needed.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and weighted distributed stochastic algorithms supply their own aggregate gain and influence second moment while reusing the same effective-parallelism statistic in variance and complexity bounds.
-- counterargument checked: although formula-bodied, this is not merely paper-local traceability or a caller-side expression because downstream positivity, range, equality-characterization, tuning, and convergence statements reason through the named statistic; the paired unfolding theorem gives it a controlled Model API.
-- coverage search: lean_search_symbols queries "effective node count squared gain divided by second moment" and "effective sample size square sum weights divided by sum squares" found only the source-local definition and related finite Cauchy lemmas; LeanSearch for "effective sample size defined as square of total weight divided by sum of squared weights" found weighted-sum and mean-inequality primitives but no definition of this statistic.
-- minimal hypotheses: all already minimal after replacing the algorithm setup by the two real quantities used in the formula.

/-- The effective number of contributing nodes determined by an aggregate
influence gain and its average squared influence.

Layer: Model | Concept: finite-network effective node count
Proof: (definitional construction; square the aggregate influence gain and divide by the average squared influence)
Source: survey-sampling effective sample size and Mathlib real powers and division
Used in: periodic distributed stochastic optimization analyses that express noise reduction, parameter tuning, and convergence constants through the effective parallelism of nonuniform network influence
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def effective_node_count (gain secondMoment : Real) : Real :=
  gain ^ 2 / secondMoment

/-- Effective node count unfolds to squared aggregate gain divided by average
squared influence.

Layer: Model | Gap: Level 0 (effective-node-count unfolding)
Proof: by rfl after unfolding `FiniteNetwork.effective_node_count`.
Source: Mathlib real powers and division
Used in: specializing a named effective-parallelism quantity to the influence gain and influence second moment before positivity, range, or equality-case calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem effective_node_count_def (gain secondMoment : Real) :
    effective_node_count gain secondMoment = gain ^ 2 / secondMoment := by
  rfl

/-- Effective node count is strictly positive when the influence second moment
is positive and the aggregate influence gain is nonzero.

Layer: Model | Gap: Level 0 (effective-node-count positivity)
Proof: the square of a nonzero gain is positive, and a quotient of positive
real numbers is positive.
Source: Mathlib ordered-field positivity for squares and division
Used in: distributed stochastic optimization bounds requiring a positive
effective parallelism parameter -/
theorem effective_node_count_pos (gain secondMoment : Real)
    (hsecondMoment : 0 < secondMoment) (hgain : gain ≠ 0) :
    0 < effective_node_count gain secondMoment := by
  rw [effective_node_count_def]
  exact div_pos (sq_pos_of_ne_zero hgain) hsecondMoment

/-- Effective node count is at most `n` when squared aggregate gain is at most
`n` times the influence second moment.

Layer: Model | Gap: Level 0 (effective-node-count upper bound)
Proof: unfold the statistic and clear the positive denominator.
Source: Mathlib ordered-field division inequalities
Used in: finite-network stochastic optimization bounds obtained from a
Cauchy--Schwarz estimate on aggregate influence -/
theorem effective_node_count_le_of_sq_le_mul (gain secondMoment n : Real)
    (hsecondMoment : 0 < secondMoment)
    (hgain : gain ^ 2 ≤ n * secondMoment) :
    effective_node_count gain secondMoment ≤ n := by
  rw [effective_node_count_def, div_le_iff₀ hsecondMoment]
  exact hgain

/-- Deprecated reducible compatibility definition for source proofs staged
before the snake_case Model API was introduced. New code should use
`effective_node_count`. -/
@[reducible, deprecated effective_node_count (since := "2026-10-26")]
noncomputable def effectiveNodeCount (gain secondMoment : Real) : Real :=
  gain ^ 2 / secondMoment

end FiniteNetwork

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: strong connectivity of a matrix's directed positive support; orig was StronglyConnectedPositiveGraph.
-- generality used: arbitrary node and scalar types, with only `[Zero R] [LT R]`; no finiteness, nonemptiness, decidable equality, ring, linear order, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional assumptions.
-- portable call pattern: directed-consensus, push-pull, gossip, and Markov-mixing proofs change the node type, ordered scalar type, and mixing matrix while reusing reachability of every ordered node pair through positive entries.
-- counterargument checked: Mathlib's `Matrix.toQuiver` with `Quiver.IsStronglyConnected` expresses the same contract for linearly ordered rings, but does not cover this definition's strictly weaker `[Zero R] [LT R]` boundary; the named matrix-support predicate also avoids installing a local quiver instance at every network call site.
-- coverage search: lean_search_symbols queries for "matrix positive entries support strongly connected reflexive transitive closure" and "strongly connected directed graph positive support matrix every pair reachable" found the paper-local declaration and `TimeVaryingDigraph.BStepStronglyConnected`, whose time-window/self-loop contract is different; LeanSearch found `Matrix.toQuiver`, `Quiver.IsStronglyConnected`, and `Matrix.IsIrreducible`, all requiring stronger algebraic/order structure or additional nonnegativity and positive-cycle content.
-- minimal hypotheses: `[Zero R]` supplies the support threshold and `[LT R]` supplies strict positivity; every source-specific finiteness, real-scalar, stochasticity, and algorithm setup assumption was removed.

/-- A square matrix has strongly connected positive support when every ordered
pair of indices is joined by a possibly empty directed path through strictly
positive entries.

Layer: Model | Concept: matrix positive-support strong connectivity
Proof: (definitional construction; universal reflexive-transitive reachability in the strict-positive entry relation)
Source: Mathlib relation closures (`Relation.ReflTransGen`) and positive-entry matrix quivers (`Matrix.toQuiver`)
Used in: periodic push-pull network assumptions and matrix-product arguments that propagate positive communication weights along directed paths
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks -/
def IsStronglyConnectedPositiveSupport {Node R : Type*} [Zero R] [LT R]
    (A : Matrix Node Node R) : Prop :=
  ∀ i j : Node, Relation.ReflTransGen (fun u v : Node => 0 < A u v) i j

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_IsStronglyConnectedPositiveSupport_exists_edge_into.lean. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: an incoming edge across every nonempty proper cut in a strongly connected positive-support matrix; orig was exists_positive_edge_into_finset.
-- generality used: arbitrary finite node type and scalar type with only zero and a strict-order relation; no nonemptiness, preorder laws, ring, stochasticity, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional assumptions.
-- portable call pattern: directed-consensus, finite Markov-chain, gossip, and push-pull reachability-growth proofs change the finite node type, scalar type, mixing matrix, and reached set while reusing the same positive incoming cut-edge conclusion.
-- counterargument checked: Mathlib has a boundary-edge decomposition theorem for `Quiver.Path`, but this is not a pure wrapper because it bridges the reusable matrix positive-support connectivity predicate, represented by `Relation.ReflTransGen`, directly to the finite-cut witness consumed by matrix-product arguments.
-- coverage search: lean_search_symbols queries "strongly connected positive support matrix edge from complement into nonempty proper finite set", "reflexive transitive path crosses finset boundary edge", and "directed graph strongly connected cut has incoming edge" found only the source declaration, the staged connectivity predicate, and different time-window connectivity APIs; LeanSearch found `Quiver.Path.exists_notMem_mem_hom_path_path_of_notMem_mem`, which uses a quiver path and an arbitrary set rather than matrix support connectivity and a finite cut.
-- minimal hypotheses: `[Zero R] [LT R]` are exactly those of `IsStronglyConnectedPositiveSupport`; `[Fintype Node]` supports `Finset.univ`, decidable equality is kept proof-local, and nonemptiness follows from `S.Nonempty`.

/-- A strongly connected positive-support matrix has a positive edge entering
every nonempty proper finite set of indices from its complement.

Layer: Model | Gap: Level 1 (positive-support connectivity to incoming cut edge)
Proof: choose a vertex outside the proper set and one inside it, obtain a positive-support reflexive-transitive path from connectivity, and induct along that path to select its first edge crossing the cut.
Source: Mathlib relation closures (`Relation.ReflTransGen`) and finite-set complements; compare `Quiver.Path.exists_notMem_mem_hom_path_path_of_notMem_mem`
Used in: finite-network matrix-product minorization, where the currently reached node set must gain an outside node through a positive communication edge at the next step
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks -/
theorem IsStronglyConnectedPositiveSupport.exists_edge_into
    {Node R : Type*} [Fintype Node] [Zero R] [LT R]
    (A : Matrix Node Node R) (hA : IsStronglyConnectedPositiveSupport A)
    (S : Finset Node) (hS : S.Nonempty) (hS_ne : S ≠ Finset.univ) :
    ∃ i u : Node, i ∉ S ∧ u ∈ S ∧ 0 < A i u := by
  classical
  have houtside : ∃ i : Node, i ∉ S := by
    by_contra h
    apply hS_ne
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := houtside
  obtain ⟨u, hu⟩ := hS
  have hpath := hA i u
  have hcross : ∀ {x y : Node}, x ∉ S → y ∈ S →
      Relation.ReflTransGen (fun a b : Node => 0 < A a b) x y →
        ∃ a b : Node, a ∉ S ∧ b ∈ S ∧ 0 < A a b := by
    intro x y hx hy hxy
    induction hxy with
    | refl => exact False.elim (hx hy)
    | @tail b c hab hbc ih =>
        by_cases hb : b ∈ S
        · exact ih hb
        · exact ⟨b, c, hb, hy, hbc⟩
  exact hcross hi hu hpath

end FiniteNetwork

/-! Promoted from Staging/Matrix_analyticAt_rieszProjectionOnCircle_of_spectrum_disjoint.lean. -/


noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Matrix

set_option maxHeartbeats 2000000 in

-- Generalization plan (G0):
-- concept/name: analyticity of a finite-matrix circle Riesz projection under a spectrum-disjoint analytic perturbation; orig was `fixed_circle_projection_endpoint_local_analyticity`.
-- generality used: arbitrary finite index type, a real-parameterized real square-matrix family, arbitrary complex contour center, and real inner/outer parameter radii; only pointwise real analyticity of the matrix family and determinant nonvanishing on the fixed contour are used, with no algorithm, probability, convexity, oracle, or ambient finite-dimensional-space assumptions.
-- portable call pattern: spectral perturbation arguments for consensus, Markov, and distributed-optimization matrices provide pointwise analyticity of the matrix family and a spectral-disjointness certificate for a fixed contour.
-- counterargument checked: this is not paper-local or a pure wrapper because it combines analytic inversion in a continuous-map Banach algebra with bounded contour integration; Mathlib supplies those ingredients but no finite-matrix Riesz-projection perturbation theorem.
-- coverage search: `lean_search_symbols` queries "Riesz projection analytic at parameter matrix family spectrum disjoint circle" and "fixed circle projection analytic on smaller interval analytic matrix larger interval no eigenvalue boundary" found the paper-local declaration and the staged Riesz-projection definition/interval-integral bridge, but no theorem with this contract; `lean_leansearch` for analytic finite-matrix Riesz projections found no matching Mathlib declaration.
-- minimal hypotheses: `[Fintype ι] [Nonempty ι] [DecidableEq ι]`, nonnegative contour radius, analyticity at the parameter, and determinant nonvanishing on the contour at that parameter are exactly used; nonemptiness supports the operator matrix norm.

/-- A circle Riesz projection of a finite real-matrix family is real-analytic
at a parameter where the family is analytic and the circle is disjoint from
the spectrum.

The conclusion takes entrywise real parts, the canonical real projection used
for real matrix families; the contour center itself may be complex.

Layer: Model | Gap: Level 2 (endpoint-safe analytic perturbation of finite-matrix Riesz projections)
Proof: lift the circle resolvent to the Banach algebra of continuous matrix-valued functions, apply analytic inversion at each spectrally disjoint base point, and compose with the bounded normalized contour-integration map.
Source: Mathlib `analyticAt_inverse`, `ContinuousMap.isUnit_iff_forall_isUnit`, `Matrix.isUnit_iff_isUnit_det`, and `Matrix.rieszProjectionOnCircle_apply_eq_integral_Icc`
Used in: fixed-contour spectral splittings for periodic push-pull and consensus products, including endpoints of closed perturbation intervals
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_rieszProjectionOnCircle_of_spectrum_disjoint
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ι → ι → ℝ) (a radius : ℝ) (center : ℂ)
    (hradius_nonneg : 0 ≤ radius)
    (hA : AnalyticAt ℝ A a)
    (hspectrum : ∀ z : ℂ, ‖z - center‖ = radius →
      det (z • (1 : Matrix ι ι ℂ) - Matrix.map (A a) (algebraMap ℝ ℂ)) ≠ 0) :
    AnalyticAt ℝ
      (fun b : ℝ =>
        fun i j => Complex.re (rieszProjectionOnCircle
          (Matrix.map (A b) (algebraMap ℝ ℂ)) center radius i j))
      a := by
  classical
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  let K : Type := Set.Icc (0 : ℝ) (2 * Real.pi)
  letI : NormedAddCommGroup (Matrix ι ι ℂ) :=
    Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℝ (Matrix ι ι ℂ) :=
    NormedSpace.restrictScalars ℝ ℂ (Matrix ι ι ℂ)
  letI : IsBoundedSMul ℝ (Matrix ι ι ℂ) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ (Matrix ι ι ℂ) := IsBoundedSMul.continuousSMul
  letI hMComplete : CompleteSpace (Matrix ι ι ℂ) :=
    FiniteDimensional.complete ℂ (Matrix ι ι ℂ)
  have hCMComplete : CompleteSpace (ContinuousMap K (Matrix ι ι ℂ)) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K (Matrix ι ι ℂ)).completeSpace
  letI := hCMComplete
  letI : HasSummableGeomSeries (ContinuousMap K (Matrix ι ι ℂ)) :=
    @instHasSummableGeomSeriesOfCompleteSpace
      (ContinuousMap K (Matrix ι ι ℂ)) _ hCMComplete
  let C : Matrix ι ι ℝ →ₗ[ℝ] ContinuousMap K (Matrix ι ι ℂ) :=
    { toFun := fun B =>
        ⟨fun _ => B.map (algebraMap ℝ ℂ), continuous_const⟩
      map_add' := by
        intro B D
        ext theta i j
        change ((B i j + D i j : ℝ) : ℂ) = (B i j : ℂ) + (D i j : ℂ)
        exact Complex.ofReal_add _ _
      map_smul' := by
        intro r B
        ext theta i j
        change ((r * B i j : ℝ) : ℂ) = (r : ℂ) * (B i j : ℂ)
        exact Complex.ofReal_mul _ _ }
  let Cc : Matrix ι ι ℝ →L[ℝ] ContinuousMap K (Matrix ι ι ℂ) :=
    LinearMap.toContinuousLinearMap C
  let Z : ContinuousMap K (Matrix ι ι ℂ) :=
    ⟨fun theta =>
        (circleMap center radius theta.1) • (1 : Matrix ι ι ℂ),
      (continuous_circleMap center radius).comp continuous_subtype_val |>.smul
        continuous_const⟩
  let R : ℝ → ContinuousMap K (Matrix ι ι ℂ) := fun b => Z - Cc (A b)
  have hR_analytic : AnalyticAt ℝ R a := by
    simpa [R] using analyticAt_const.sub ((Cc.analyticAt (A a)).comp' hA)
  have hR_unit : IsUnit (R a) := by
    rw [ContinuousMap.isUnit_iff_forall_isUnit]
    intro theta
    rw [Matrix.isUnit_iff_isUnit_det]
    exact (isUnit_iff_ne_zero.mpr <| hspectrum
      (circleMap center radius theta.1) <| by
        simpa [Metric.mem_sphere, dist_eq_norm] using
          circleMap_mem_sphere center hradius_nonneg theta.1)
  have hR_inv_analytic :
      AnalyticAt ℝ (fun b => Ring.inverse (R b)) a := by
    exact (analyticAt_inverse (𝕜 := ℝ) hR_unit.unit).comp_of_eq'
      hR_analytic hR_unit.unit_spec.symm
  have hR_eventually_unit : ∀ᶠ b in 𝓝 a, IsUnit (R b) :=
    hR_analytic.continuousAt (Units.isOpen.mem_nhds hR_unit)
  let muK : Measure K := Measure.comap (Subtype.val : K → ℝ) volume
  have hmuK : muK (Set.univ : Set K) < ⊤ := by
    dsimp [muK, K]
    rw [comap_subtype_coe_apply isCompact_Icc.measurableSet]
    simpa using (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).measure_lt_top
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let entryLin : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B i j
      map_add' := by intro B D; rfl
      map_smul' := by intro z B; rfl }
  let entryCLM : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap entryLin
  let T : ContinuousMap K (Matrix ι ι ℂ) →ₗ[ℝ] ContinuousMap K ℂ :=
    { toFun := fun f =>
        ⟨fun theta =>
            c * deriv (circleMap center radius) theta.1 * f theta i j, by
          have hfij : Continuous (fun theta : K => f theta i j) :=
            (continuous_apply j).comp ((continuous_apply i).comp f.continuous)
          simpa only [deriv_circleMap] using
            (continuous_const.mul
              (((continuous_circleMap 0 radius).comp continuous_subtype_val).mul
                continuous_const)).mul hfij⟩
      map_add' := by
        intro f g
        ext theta
        simp [mul_add]
      map_smul' := by
        intro r f
        ext theta
        change c * deriv (circleMap center radius) theta.1 *
            ((r : ℂ) * f theta i j) =
          (r : ℂ) * (c * deriv (circleMap center radius) theta.1 * f theta i j)
        ring }
  let Tc : ContinuousMap K (Matrix ι ι ℂ) →L[ℝ] ContinuousMap K ℂ :=
    LinearMap.mkContinuous T (‖c‖ * |radius| * ‖entryCLM‖) (by
        intro f
        let g : ContinuousMap K ℂ :=
          ⟨fun theta : K =>
              c * deriv (circleMap center radius) theta.1 * f theta i j, by
            have hfij : Continuous (fun theta : K => f theta i j) :=
              (continuous_apply j).comp ((continuous_apply i).comp f.continuous)
            simpa only [deriv_circleMap] using
              (continuous_const.mul
                (((continuous_circleMap 0 radius).comp continuous_subtype_val).mul
                  continuous_const)).mul hfij⟩
        change ‖g‖ ≤ (‖c‖ * |radius| * ‖entryCLM‖) * ‖f‖
        apply (g.norm_le (mul_nonneg
          (mul_nonneg (mul_nonneg (norm_nonneg c) (abs_nonneg radius))
            (norm_nonneg entryCLM)) (norm_nonneg f))).2
        intro theta
        change ‖c * deriv (circleMap center radius) theta.1 * f theta i j‖ ≤
          (‖c‖ * |radius| * ‖entryCLM‖) * ‖f‖
        calc
          ‖c * deriv (circleMap center radius) theta.1 * f theta i j‖ =
              (‖c‖ * |radius|) * ‖f theta i j‖ := by
                simp [deriv_circleMap]
          _ ≤ (‖c‖ * |radius|) * (‖entryCLM‖ * ‖f theta‖) := by
            have hentry : ‖f theta i j‖ ≤ ‖entryCLM‖ * ‖f theta‖ := by
              simpa [entryCLM, entryLin] using
                (ContinuousLinearMap.le_opNorm entryCLM (f theta))
            exact mul_le_mul_of_nonneg_left hentry (by positivity)
          _ ≤ (‖c‖ * |radius|) * (‖entryCLM‖ * ‖f‖) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (ContinuousMap.norm_coe_le_norm f theta) (norm_nonneg entryCLM))
              (by positivity)
          _ = (‖c‖ * |radius| * ‖entryCLM‖) * ‖f‖ := by ring)
  let LI : ContinuousMap K ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun f => ∫ theta in (Set.univ : Set K), f theta ∂muK
      map_add' := by
        intro f g
        have hf : Integrable (fun theta : K => f theta) muK := by
          simpa [IntegrableOn] using
            (f.continuous.continuousOn.integrableOn_of_subset_isCompact
              (μ := muK) (K := Set.univ) isCompact_univ MeasurableSet.univ
              (fun x hx => hx) (ne_of_lt hmuK))
        have hg : Integrable (fun theta : K => g theta) muK := by
          simpa [IntegrableOn] using
            (g.continuous.continuousOn.integrableOn_of_subset_isCompact
              (μ := muK) (K := Set.univ) isCompact_univ MeasurableSet.univ
              (fun x hx => hx) (ne_of_lt hmuK))
        simpa [Pi.add_apply] using integral_add hf hg
      map_smul' := by
        intro r f
        simpa [Pi.smul_apply] using
          (integral_smul (μ := muK) (𝕜 := ℝ) (G := ℂ) r (fun x : K => f x)) }
  let LIc : ContinuousMap K ℂ →L[ℝ] ℂ :=
    LinearMap.mkContinuous LI (muK.real (Set.univ : Set K)) (by
      intro f
      change ‖∫ theta in (Set.univ : Set K), f theta ∂muK‖ ≤
        muK.real (Set.univ : Set K) * ‖f‖
      have hbound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := muK) (s := (Set.univ : Set K))
        (f := fun theta : K => f theta) hmuK
        (fun theta _ => ContinuousMap.norm_coe_le_norm f theta)
      simpa only [mul_comm] using hbound)
  have hIntegral_analytic : AnalyticAt ℝ
      (fun b => LIc (Tc (Ring.inverse (R b)))) a :=
    (LIc.analyticAt _).comp' ((Tc.analyticAt _).comp' hR_inv_analytic)
  have hIntegral_eq : ∀ᶠ b in 𝓝 a,
      LIc (Tc (Ring.inverse (R b))) =
        rieszProjectionOnCircle
          (Matrix.map (A b) (algebraMap ℝ ℂ)) center radius i j := by
    filter_upwards [hR_eventually_unit] with b hb
    have hinv_apply (theta : K) :
        Ring.inverse (R b) theta =
          ((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
            Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
      have hu : (hb.unit : ContinuousMap K (Matrix ι ι ℂ)) = R b :=
        hb.unit_spec
      calc
        Ring.inverse (R b) theta =
            Ring.inverse (↑hb.unit : ContinuousMap K (Matrix ι ι ℂ)) theta := by
          rw [hu]
        _ = (↑hb.unit⁻¹ : ContinuousMap K (Matrix ι ι ℂ)) theta := by
          rw [Ring.inverse_unit]
        _ = ↑(ContinuousMap.unitsLift.symm hb.unit theta)⁻¹ := by
          exact (ContinuousMap.unitsLift_symm_apply_apply_inv' hb.unit theta).symm
        _ = Ring.inverse ((R b) theta) := by
          rw [← Ring.inverse_unit (ContinuousMap.unitsLift.symm hb.unit theta)]
          rfl
        _ = Ring.inverse
            ((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ)) := by
          rfl
    rw [rieszProjectionOnCircle_apply_eq_integral_Icc]
    have hdec : (Classical.decEq ι) = (inferInstance : DecidableEq ι) :=
      Subsingleton.elim _ _
    rw [hdec]
    change
      (∫ theta in (Set.univ : Set K),
        c * deriv (circleMap center radius) theta.1 *
          (Ring.inverse (R b) theta) i j ∂muK) =
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center radius) theta •
              (@Inv.inv (Matrix ι ι ℂ) Matrix.inv
                (fun k l : ι =>
                  circleMap center radius theta * (1 : Matrix ι ι ℂ) k l -
                    Matrix.map (A b) (algebraMap ℝ ℂ) k l)) i j)
    have hsubtype := MeasureTheory.integral_subtype_comap
      (μ := volume) (s := Set.Icc (0 : ℝ) (2 * Real.pi))
      isCompact_Icc.measurableSet
      (fun theta : ℝ =>
        c * deriv (circleMap center radius) theta *
          (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
            Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j)
    rw [show
      (∫ theta in (Set.univ : Set K),
          c * deriv (circleMap center radius) theta.1 *
            (Ring.inverse (R b) theta) i j ∂muK) =
        ∫ theta in (Set.univ : Set K),
          c * deriv (circleMap center radius) theta.1 *
            (((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j ∂muK by
        apply integral_congr_ae
        filter_upwards with theta
        rw [hinv_apply theta]]
    rw [show
      (∫ theta in (Set.univ : Set K),
          c * deriv (circleMap center radius) theta.1 *
            (((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j ∂muK) =
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          c * deriv (circleMap center radius) theta *
            (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j by
        simpa [K, muK] using hsubtype]
    rw [show
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          c * deriv (circleMap center radius) theta *
            (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j) =
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          c * (deriv (circleMap center radius) theta *
            (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j) by
        apply integral_congr_ae
        filter_upwards with theta
        ring]
    calc
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          c * (deriv (circleMap center radius) theta *
            (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j)) =
        c * (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap center radius) theta *
            (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A b) (algebraMap ℝ ℂ))⁻¹) i j) := by
          exact MeasureTheory.integral_const_mul
            (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) c _
      _ = _ := by
        dsimp [c]
        apply congrArg (fun x : ℂ =>
          (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) * x)
        apply integral_congr_ae
        filter_upwards with theta
        have hmatrix :
            (circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
                Matrix.map (A b) Complex.ofReal =
              fun k l : ι =>
                circleMap center radius theta * (1 : Matrix ι ι ℂ) k l -
                  (A b k l : ℂ) := by
          ext k l
          rfl
        rw [hmatrix]
  have hentry_analytic : AnalyticAt ℝ
      (fun b => rieszProjectionOnCircle
        (Matrix.map (A b) (algebraMap ℝ ℂ)) center radius i j) a :=
    hIntegral_analytic.congr hIntegral_eq
  exact (Complex.reCLM.analyticAt _).comp' hentry_analytic

end Matrix

/-! Promoted from Staging/FiniteNetwork_IsStronglyConnectedPositiveSupport.lean. -/

namespace FiniteNetwork
/-- Strong connectivity of positive matrix support unfolds to reachability of
every ordered index pair through the reflexive-transitive closure of positive
entries.

Layer: Model | Gap: Level 0 (matrix positive-support connectivity unfolding)
Proof: by rfl after unfolding `FiniteNetwork.IsStronglyConnectedPositiveSupport`.
Source: Mathlib relation closures (`Relation.ReflTransGen`) and square matrices
Used in: exposing positive-entry paths from a reusable connectivity assumption in directed consensus and push-pull matrix estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks -/
@[simp] theorem IsStronglyConnectedPositiveSupport_def
    {Node R : Type*} [Zero R] [LT R] (A : Matrix Node Node R) :
    IsStronglyConnectedPositiveSupport A ↔
      ∀ i j : Node, Relation.ReflTransGen (fun u v : Node => 0 < A u v) i j := by
  rfl

/-- Strong connectivity is preserved when every positive edge in one matrix's
support remains positive in another matrix's support.

Layer: Model | Gap: Level 0 (positive-support connectivity monotonicity)
Proof: map each edge of every reflexive-transitive path through the support
inclusion.
Source: Mathlib `Relation.ReflTransGen.mono` and square matrices
Used in: transferring consensus, gossip, and push-pull connectivity assumptions
to mixing matrices with larger positive support -/
theorem IsStronglyConnectedPositiveSupport.mono
    {Node R : Type*} [Zero R] [LT R] {A B : Matrix Node Node R}
    (hA : IsStronglyConnectedPositiveSupport A)
    (hAB : ∀ i j : Node, 0 < A i j → 0 < B i j) :
    IsStronglyConnectedPositiveSupport B := by
  intro i j
  exact Relation.ReflTransGen.mono hAB (hA i j)

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_ZeroSumState.lean. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: zero-sum state of a finite network; orig was `ZeroSumState` in the time-varying Push--Pull development.
-- generality used: arbitrary finite node type and additive commutative monoid of coordinate values; no nonemptiness, topology, norm, scalar action, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: consensus, push-sum, Push--Pull, and gradient-tracking proofs change the finite node type and additive state space while reusing the same invariant domain for mass-preserving mixing and correction operators.
-- counterargument checked: although the body is a short subtype expression, it is not paper-local bookkeeping or a pure rename of an existing type; many downstream operators share this canonical invariant domain and use its membership proof through the subtype API.
-- coverage search: lean_search_symbols queries for "finite node indexed additive state coordinate sum equals zero subtype", "zero sum functions finite type additive commutative monoid", and "kernel finite sum linear map functions zero sum subtype" found only the paper-local declaration and unrelated zero-sum theorems; LeanSearch found `Fintype.sum_balance`, which constructs one balanced function under stronger assumptions but does not provide this subtype.
-- minimal hypotheses: `[Fintype Node]` supplies the coordinate sum and `[AddCommMonoid E]` supplies addition and zero; all source assumptions beyond these are dropped.

/-- The additive states on a finite network whose coordinates sum to zero.

This is the invariant domain naturally preserved by mass-preserving mixing
operators and used for disagreement or gradient-tracking corrections.

Layer: Model | Concept: finite-network zero-sum state
Proof: (definitional construction; subtype of node-indexed additive states satisfying a zero finite-coordinate sum)
Source: Mathlib finite-type big operators and subtype constructions for additive commutative monoids
Used in: corrected-lift and tracker-error arguments where column-stochastic mixing transports a zero-total-mass network state through successive communication steps
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
abbrev ZeroSumState (Node E : Type*) [Fintype Node] [AddCommMonoid E] :=
  { W : Node → E // ∑ i : Node, W i = 0 }

namespace ZeroSumState

variable {Node E : Type*} [Fintype Node] [AddCommMonoid E]

/-- A zero-sum state has zero total coordinate sum. -/
@[simp]
theorem sum_coe_eq_zero (W : ZeroSumState Node E) :
    ∑ i : Node, (W : Node → E) i = 0 :=
  W.property

instance zero : Zero (ZeroSumState Node E) where
  zero := ⟨0, by simp⟩

@[simp, norm_cast]
theorem coe_zero :
    ((0 : ZeroSumState Node E) : Node → E) = 0 :=
  rfl

instance add : Add (ZeroSumState Node E) where
  add W V :=
    ⟨W.1 + V.1, by
      simp only [Pi.add_apply, Finset.sum_add_distrib, W.property, V.property, add_zero]⟩

@[simp, norm_cast]
theorem coe_add (W V : ZeroSumState Node E) :
    ((W + V : ZeroSumState Node E) : Node → E) = W + V :=
  rfl

instance nsmul : SMul ℕ (ZeroSumState Node E) where
  smul n W :=
    ⟨n • W.1, by
      change ∑ i : Node, n • W.1 i = 0
      induction n with
      | zero => simp
      | succ n ih =>
          simp only [succ_nsmul, Finset.sum_add_distrib, ih, W.property, add_zero]⟩

@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (W : ZeroSumState Node E) :
    ((n • W : ZeroSumState Node E) : Node → E) = n • (W : Node → E) :=
  rfl

/-- Zero-sum states form an additive commutative monoid under pointwise addition. -/
instance addCommMonoid : AddCommMonoid (ZeroSumState Node E) :=
  Subtype.coe_injective.addCommMonoid _ coe_zero coe_add (fun W n => coe_nsmul n W)

end ZeroSumState

end FiniteNetwork

/-! Promoted from Staging/FiniteNetwork_averagePeriodicPerronOverlap.lean. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: average periodic Perron overlap; orig was `averagePerronOverlap`.
-- generality used: arbitrary finite node carrier, natural period, and two real-valued node-vector sequences; no nonempty-node, positive-period, stochasticity, periodicity, positivity, norm, inner-product-space, finite-dimensional, measure, convexity, smoothness, or oracle assumptions are needed.
-- portable call pattern: periodic push-pull, push-sum, and gradient-tracking analyses change their left/right Perron sequences and period while reusing the same shifted period-average overlap as the average influence row and scalar gain.
-- counterargument checked: although the construction is a single finite-sum formula, it is not paper-local bookkeeping because later proofs reason through it as a positive DC-gain scalar and identify an average influence row with its constant row; the paired unfolding theorem supplies the controlled Model API.
-- coverage search: `lean_search_symbols` queries "period average overlap shifted left right Perron sequences" and "finite periodic sequences average inner product overlap" found only the source declaration and complementary periodic Perron-sequence APIs; LeanSearch for the shifted finite-period inner-product average found generic `birkhoffAverage`, `Finset.expect`, and `RCLike.wInner_cWeight_eq_expect`, but no Perron-overlap object with this shift and normalization.
-- minimal hypotheses: `[Fintype Node]` is exactly what the node-coordinate sum requires; the source setup, `Nonempty Node`, positive period, Perron equations, positivity, and periodicity were removed because the definition does not consume them.

/-- The average over one period of the overlaps between a shifted left Perron
sequence and a right Perron sequence.

For left and right sequences `pi` and `v`, this is
`p⁻¹ ∑ r : Fin p, ∑ i, pi (r + 1) i * v r i`.  The definition is
total at period zero; periodic-network applications normally supply `0 < p`.

Layer: Model | Concept: average periodic Perron overlap
Proof: (definitional construction; reciprocal-period scaling of the finite phase sum of coordinatewise left/right Perron products with the left sequence shifted by one step)
Source: finite-state nonhomogeneous Markov-chain Perron sequences, finite-period averaging, and Mathlib finite sums over `Fin p` and finite node types
Used in: periodic push-pull, push-sum, and gradient-tracking analyses that identify the average influence row and its scalar gain from shifted left/right Perron weights
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def averagePeriodicPerronOverlap
    {Node : Type*} [Fintype Node] {p : Nat}
    (pi v : Nat → Node → Real) : Real := by
  classical
  exact ((p : Real)⁻¹) *
    ∑ r : Fin p, ∑ i : Node, pi (r.1 + 1) i * v r.1 i

/-- The average periodic Perron overlap unfolds to its reciprocal-period-scaled
sum of shifted left/right coordinate products.

Layer: Model | Gap: Level 0 (average periodic Perron-overlap unfolding)
Proof: by rfl after unfolding `FiniteNetwork.averagePeriodicPerronOverlap` with the classical finite-node enumeration.
Source: Mathlib finite sums and real reciprocal scaling together with finite-state periodic Perron sequences
Used in: exposing the phase-and-node sum before positivity proofs and average-influence DC-gain identities for periodic directed-network algorithms
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem averagePeriodicPerronOverlap_def
    {Node : Type*} [Fintype Node] {p : Nat}
    (pi v : Nat → Node → Real) :
    averagePeriodicPerronOverlap (p := p) pi v =
      ((p : Real)⁻¹) *
        ∑ r : Fin p, ∑ i : Node, pi (r.1 + 1) i * v r.1 i := by
  classical
  rfl

/-- The average periodic Perron overlap is strictly positive when the period is
positive and every shifted left/right coordinate pair is strictly positive.

Layer: Model | Gap: Level 0 (average periodic Perron-overlap strict positivity)
Proof: each phase overlap is a positive finite sum over the nonempty node type,
then the finite uniform average over the positive-length period is positive.
Source: strict positivity of finite sums and SOptLib finite uniform averages
Used in: periodic directed-network algorithms whose positive Perron weights
give a positive scalar gain after averaging over one period
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem averagePeriodicPerronOverlap_pos
    {Node : Type*} [Fintype Node] [Nonempty Node] {p : Nat}
    (pi v : Nat → Node → Real) (hp : 0 < p)
    (hpi : ∀ r : Fin p, ∀ i : Node, 0 < pi (r.1 + 1) i)
    (hv : ∀ r : Fin p, ∀ i : Node, 0 < v r.1 i) :
    0 < averagePeriodicPerronOverlap (p := p) pi v := by
  classical
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  have hphase : ∀ r : Fin p,
      0 < ∑ i : Node, pi (r.1 + 1) i * v r.1 i := by
    intro r
    exact Finset.sum_pos
      (fun i _ => mul_pos (hpi r i) (hv r i))
      Finset.univ_nonempty
  simpa [averagePeriodicPerronOverlap, SOptLib.finiteUniformAverage,
    smul_eq_mul] using
    (SOptLib.finiteUniformAverage_pos
      (fun r : Fin p => ∑ i : Node, pi (r.1 + 1) i * v r.1 i)
      hphase)

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

-- Generalization plan (G0):
-- concept/name: finite-network agreement-state predicate; orig was `AgreementSubspace`
-- generality used: arbitrary node and state carriers; no finiteness, decidable equality, algebraic, topological, measure, convexity, smoothness, oracle, or finite-dimensional assumptions are needed
-- portable call pattern: consensus, gossip, and gradient-tracking proofs use the same predicate to state that all node coordinates agree while changing the node type, state type, and mechanism establishing agreement
-- counterargument checked: although the body is elementary, this is not paper-local traceability or a rename of an existing primitive; it names the standard consensus invariant for arbitrary node states and complements the existing finite-network consensus-state construction
-- coverage search: `lean_search_symbols` queries for "finite network state all coordinates equal pairwise agreement consensus" and "function values equal every pair constant" found the distinct `FiniteNetwork.consensusState` construction and the local SDCS declaration, but no Mathlib or SOptLib agreement-state predicate; LeanSearch was attempted for the pairwise-constant function characterization but returned an HTTP 500 error
-- minimal hypotheses: all already minimal after removing the source's `Fintype`, measurable-space, Hilbert-space, completeness, Borel-space, and second-countability assumptions


namespace FiniteNetwork

/-- A node-indexed state is an agreement state when every pair of node values is equal.

Layer: Model | Concept: finite-network agreement state
Proof: (definitional construction; pairwise equality of all values of a node-indexed state)
Source: finite-network consensus theory and Mathlib dependent-function equality
Used in: consensus, gossip, and gradient-tracking invariants, including identifying the kernel of a connected lifted graph Laplacian with states whose local copies agree
Book citation: book/research/Source.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
def IsAgreementState {Node E : Type*} (x : Node → E) : Prop :=
  ∀ i j, x i = x j

/-- The finite-network agreement-state predicate unfolds to pairwise equality of
all node values.

Layer: Model | Gap: Level 0 (finite-network agreement-state unfolding)
Proof: by rfl after unfolding `FiniteNetwork.IsAgreementState`.
Source: finite-network consensus theory and Mathlib dependent-function equality
Used in: rewriting a connected-network agreement invariant into coordinate equalities at selected pairs of agents
Book citation: book/research/Source.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
@[simp] theorem IsAgreementState_def {Node E : Type*} (x : Node → E) :
    IsAgreementState x ↔ ∀ i j, x i = x j := Iff.rfl

/-- A state on a finite nonempty network is an agreement state exactly when it
is fixed by the consensus-state construction.

Layer: Model | Gap: Level 0 (agreement-state consensus characterization)
Proof: an agreement state is constant, so its finite uniform average is its
common value; conversely, `consensusState` is constant across nodes.
Source: finite-network consensus theory, SOptLib finite-uniform averaging, and
Mathlib dependent-function equality
Used in: converting pairwise agreement invariants into fixed-point statements
for consensus projections in consensus, gossip, and gradient-tracking proofs -/
@[simp] theorem isAgreementState_iff_eq_consensusState
    {Node E : Type*} [Fintype Node] [Nonempty Node]
    [AddCommGroup E] [Module ℝ E] (x : Node → E) :
    IsAgreementState x ↔ x = consensusState x := by
  constructor
  · intro h
    let i₀ : Node := Classical.choice (inferInstance : Nonempty Node)
    have hx : x = fun _ => x i₀ := by
      funext i
      exact h i i₀
    rw [hx]
    funext i
    exact (SOptLib.finiteUniformAverage_const (x i₀)).symm
  · intro hx i j
    rw [hx]
    rfl

end FiniteNetwork

-- Generalization plan (G0):
-- concept/name: connected finite-network Laplacian contract; orig was `IsConnectedLiftedLaplacian`
-- generality used: arbitrary finite node carrier, real normed state space, explicit real-valued pairing, and continuous linear endomorphism; no measurability, completeness, inner-product, convexity, smoothness, oracle, probability, or finite-dimensional assumptions are needed
-- portable call pattern: decentralized consensus, gradient-tracking, gossip, and primal-dual methods replace the node type, coordinate space, pairing, and lifted communication operator while retaining the same agreement-kernel, quadratic-nonnegativity, and pairing-self-adjointness conclusions
-- counterargument checked: this is not merely paper traceability or a caller-side expression because the three clauses form the standard connected positive-semidefinite Laplacian contract and are consumed independently in network proofs; Mathlib's form-level self-adjoint and positive-semidefinite predicates do not include the agreement-kernel characterization or cover an explicit caller-supplied pairing
-- coverage search: `lean_search_symbols` queries for "finite network connected Laplacian agreement kernel nonnegative quadratic form symmetric pairing" and "linear operator kernel consensus positive semidefinite self adjoint" found no SOptLib or Mathlib declaration; direct Mathlib source search found `LinearMap.BilinForm.IsSelfAdjoint` and positive-semidefinite form predicates, which cover individual form-level notions but not this combined network contract; LeanSearch was attempted with the complete semantic shape and returned HTTP 500
-- minimal hypotheses: `[Fintype Node]`, `[NormedAddCommGroup E]`, and `[NormedSpace ℝ E]` are exactly those needed to form the continuous linear endomorphism on `Node → E`; the source's measurable, complete, Borel, second-countable, and inner-product assumptions are removed


namespace FiniteNetwork

/-- A continuous linear network operator is a connected Laplacian relative to a
pairing when its kernel is exactly the agreement states, its quadratic form is
nonnegative, and it is self-adjoint for that pairing.

Layer: Model | Concept: connected finite-network Laplacian
Proof: (definitional construction; conjunction of agreement-kernel characterization, nonnegative quadratic form, and pairing-relative self-adjointness)
Source: finite-network Laplacian theory together with Mathlib continuous linear endomorphisms and bilinear-form self-adjointness conventions
Used in: decentralized consensus and stochastic primal-dual proofs that turn graph connectedness into consensus-kernel facts and transpose a lifted communication operator across a product-space pairing
Book citation: book/research/Source.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
def IsConnectedLaplacian {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pairing : (Node → E) → (Node → E) → ℝ)
    (L : (Node → E) →L[ℝ] (Node → E)) : Prop :=
  (∀ x, L x = 0 ↔ IsAgreementState x) ∧
    (∀ x, 0 ≤ pairing (L x) x) ∧
    (∀ x y, pairing (L x) y = pairing x (L y))

/-- The connected-Laplacian contract unfolds to its agreement-kernel,
quadratic-nonnegativity, and pairing-self-adjointness clauses.

Layer: Model | Gap: Level 0 (connected finite-network Laplacian contract unfolding)
Proof: by rfl after unfolding `FiniteNetwork.IsConnectedLaplacian`.
Source: finite-network Laplacian theory and Mathlib continuous linear endomorphisms
Used in: exposing the three network-operator clauses needed separately by consensus feasibility and primal-dual pairing arguments
Book citation: book/research/Source.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
@[simp] theorem IsConnectedLaplacian_def {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pairing : (Node → E) → (Node → E) → ℝ)
    (L : (Node → E) →L[ℝ] (Node → E)) :
    IsConnectedLaplacian pairing L ↔
      (∀ x, L x = 0 ↔ IsAgreementState x) ∧
        (∀ x, 0 ≤ pairing (L x) x) ∧
        (∀ x y, pairing (L x) y = pairing x (L y)) := by
  rfl

/-- A connected finite-network Laplacian vanishes exactly on agreement states.

Layer: Model | Gap: Level 0 (agreement-kernel projection from a connected Laplacian contract)
Proof: project the first conjunct of `FiniteNetwork.IsConnectedLaplacian`.
Source: connected graph Laplacian kernel characterization in finite-network consensus theory
Used in: converting a zero lifted communication residual into node agreement, and conversely discharging the residual for consensus states
Book citation: book/research/Source.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem IsConnectedLaplacian.apply_eq_zero_iff {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {pairing : (Node → E) → (Node → E) → ℝ}
    {L : (Node → E) →L[ℝ] (Node → E)}
    (h : IsConnectedLaplacian pairing L) (x : Node → E) :
    L x = 0 ↔ IsAgreementState x :=
  h.1 x

/-- The quadratic form of a connected finite-network Laplacian is nonnegative.

Layer: Model | Gap: Level 0 (quadratic nonnegativity projection from a connected Laplacian contract)
Proof: project and specialize the second conjunct of `FiniteNetwork.IsConnectedLaplacian`.
Source: positive-semidefinite graph Laplacians and Mathlib ordered real inequalities
Used in: discarding or bounding lifted network quadratic terms in decentralized convergence estimates
Book citation: book/research/Source.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem IsConnectedLaplacian.quadratic_nonneg {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {pairing : (Node → E) → (Node → E) → ℝ}
    {L : (Node → E) →L[ℝ] (Node → E)}
    (h : IsConnectedLaplacian pairing L) (x : Node → E) :
    0 ≤ pairing (L x) x :=
  h.2.1 x

/-- A connected finite-network Laplacian is self-adjoint relative to its
supplied pairing.

Layer: Model | Gap: Level 0 (pairing self-adjointness projection from a connected Laplacian contract)
Proof: project and specialize the third conjunct of `FiniteNetwork.IsConnectedLaplacian`.
Source: self-adjoint graph Laplacians and Mathlib bilinear-form self-adjointness conventions
Used in: moving a lifted network operator between primal and dual arguments in decentralized saddle-point and consensus estimates
Book citation: book/research/Source.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem IsConnectedLaplacian.pairing_apply_left_eq_right {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {pairing : (Node → E) → (Node → E) → ℝ}
    {L : (Node → E) →L[ℝ] (Node → E)}
    (h : IsConnectedLaplacian pairing L) (x y : Node → E) :
    pairing (L x) y = pairing x (L y) :=
  h.2.2 x y

end FiniteNetwork

/-! Promoted from Staging/Module_End_exists_analyticRankOneSpectralSplitting_with_base_projection.lean. -/

noncomputable section

open scoped BigOperators

namespace Module.End

local instance matrixNormedAddCommGroup {Node : Type*} [Fintype Node] :
    NormedAddCommGroup (Matrix Node Node ℝ) := by
  change NormedAddCommGroup (Node → Node → ℝ)
  infer_instance

local instance matrixNormedSpace {Node : Type*} [Fintype Node] :
    NormedSpace ℝ (Matrix Node Node ℝ) := by
  change NormedSpace ℝ (Node → Node → ℝ)
  infer_instance

/-- An analytic rank-one splitting based at a normalized algebraically simple
unit eigenpair can be chosen with the canonical normalized outer projector at
the base parameter.

Layer: Model | Gap: Level 2 (canonical base projector for an analytic rank-one spectral splitting)
Proof: identify the projector on the distinguished right mode and on the
  complementary residual range, then use the supplied simple-eigenpair
  decomposition to obtain its normalized outer-product action.
Source: finite-dimensional simple-eigenvalue perturbation theory, normalized left/right eigenvectors, and Riesz-projector algebra
Used in: retaining the base slow-projector identity after constructing the analytic slow-stable decomposition of a periodic push-pull or transition operator family
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_analyticRankOneSpectralSplitting_with_base_projection
    {Node : Type*} [Fintype Node] [Nonempty Node]
    (operatorAdd operatorMul : Matrix Node Node ℝ → Matrix Node Node ℝ → Matrix Node Node ℝ)
    (operatorPower : Matrix Node Node ℝ → ℕ → Matrix Node Node ℝ)
    (operatorNorm : Matrix Node Node ℝ → ℝ)
    (isRiesz : Matrix Node Node ℝ → ℝ → Matrix Node Node ℝ → Prop)
    (A : ℝ → Matrix Node Node ℝ) (alpha1 r0 : ℝ)
    (right left : Node → ℝ)
    (hright : (A 0).mulVec right = right)
    (hfixed : ∀ {M lambda P}, isRiesz M lambda P → ∀ x,
      P.mulVec x = x ↔ M.mulVec x = lambda • x)
    (hmulright_native : ∀ {M lambda P}, isRiesz M lambda P →
      P * M = lambda • P)
    (hresidual : ∀ x : Node → ℝ, ∃ z : Node → ℝ,
      (A 0).mulVec z - z = x - dotProduct left x • right)
    (hsplit :
      ∃ alpha0 theta K : ℝ, ∃ gamma : ℝ → ℝ,
        ∃ P F : ℝ → Matrix Node Node ℝ,
          alpha0 ≤ alpha1 ∧
            AnalyticRankOneSpectralSplitting
              operatorAdd operatorMul operatorPower operatorNorm
              Matrix.mulVec dotProduct isRiesz
              A 1 r0 alpha0 1 theta K right left gamma P F) :
    ∃ alpha0 theta K : ℝ, ∃ gamma : ℝ → ℝ,
      ∃ P F : ℝ → Matrix Node Node ℝ,
        alpha0 ≤ alpha1 ∧
          P 0 = Matrix.vecMulVec right left ∧
          AnalyticRankOneSpectralSplitting
            operatorAdd operatorMul operatorPower operatorNorm
            Matrix.mulVec dotProduct isRiesz
            A 1 r0 alpha0 1 theta K right left gamma P F := by
  classical
  rcases hsplit with ⟨alpha0, theta, K, gamma, P, F, halpha0_le, hs⟩
  rcases hs with
    ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, hgamma0,
      hgamma_analytic, hP_analytic, hderiv, hlocal⟩
  have hzero : |(0 : ℝ)| ≤ alpha0 := by simpa using halpha0_pos.le
  obtain ⟨hP0_riesz, _hsplit0, _hPF0, _hFP0, _hpower0⟩ := hlocal 0 hzero
  have hP0_riesz_one : isRiesz (A 0) 1 (P 0) := by
    simpa [hgamma0] using hP0_riesz
  have hP0_right : (P 0).mulVec right = right :=
    (hfixed hP0_riesz_one right).2 (by simpa using hright)
  have hP0_residual (z : Node → ℝ) :
      (P 0).mulVec ((A 0).mulVec z - z) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    rw [hmulright_native hP0_riesz_one]
    simp
  have hP0_action (x : Node → ℝ) :
      (P 0).mulVec x = dotProduct left x • right := by
    obtain ⟨z, hz⟩ := hresidual x
    let c : ℝ := dotProduct left x
    let y : Node → ℝ := x - c • right
    have hy : y = (A 0).mulVec z - z := by
      simpa [y, c] using hz.symm
    have hPy : (P 0).mulVec y = 0 := by
      rw [hy]
      exact hP0_residual z
    have hx : x = y + c • right := by
      simp [y, c]
    calc
      (P 0).mulVec x = (P 0).mulVec (y + c • right) := by rw [hx]
      _ = (P 0).mulVec y + c • (P 0).mulVec right := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = c • right := by rw [hPy, hP0_right]; simp
      _ = dotProduct left x • right := by rfl
  have hP0 : P 0 = Matrix.vecMulVec right left := by
    apply Matrix.ext
    intro i j
    let e : Node → ℝ := Pi.single j 1
    have haction := congrFun (hP0_action e) i
    simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply,
      apply_ite, Finset.mul_sum, mul_comm] using haction
  refine ⟨alpha0, theta, K, gamma, P, F, halpha0_le, hP0, ?_⟩
  exact ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, hgamma0,
    hgamma_analytic, hP_analytic, hderiv, hlocal⟩

end Module.End

/-! Promoted from Staging/Matrix_rieszProjectionOnCircle_idempotent_and_map_conj_eq_self_of_spectrum_disjoint.lean. -/


noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Filter

namespace Matrix
namespace RieszProjectionOnCircleProof

variable {Node : Type*}
variable [Fintype Node] [Nonempty Node]

private abbrev NodeMatrix (Node : Type*) := Node → Node → ℝ
private abbrev ComplexRowVector (Node : Type*) := Node → ℂ

private noncomputable def complexMatrixMulVector
    (A : NodeMatrix Node) (v : ComplexRowVector Node) : ComplexRowVector Node :=
  fun i => ∑ j : Node, (A i j : ℂ) * v j

private def IsComplexRightEigenvalue (A0 : NodeMatrix Node) (gamma : ℂ) : Prop :=
  ∃ v : ComplexRowVector Node,
    v ≠ 0 ∧ complexMatrixMulVector (Node := Node) A0 v = gamma • v

private abbrev ComplexNodeMatrix (Node : Type*) := Matrix Node Node ℂ

private noncomputable def complexIdentityMatrix : ComplexNodeMatrix Node := by
  classical
  exact 1

private def complexOfRealMatrix (A : NodeMatrix Node) : ComplexNodeMatrix Node :=
  fun i j => (A i j : ℂ)


private def complexMatrixSub (A B : ComplexNodeMatrix Node) : ComplexNodeMatrix Node :=
  fun i j => A i j - B i j

/-- Complex matrix multiplication in the fixed finite node coordinates. -/

private noncomputable def complexMatrixMul
    (A B : ComplexNodeMatrix Node) : ComplexNodeMatrix Node :=
  A * B

/-- Action of a complex node matrix on a complex node vector. -/

private noncomputable def complexNodeMatrixMulVector
    (A : ComplexNodeMatrix Node) (v : ComplexRowVector Node) :
    ComplexRowVector Node :=
  Matrix.mulVec A v

/-- The resolvent matrix `zI - A` in the complex scalar extension. -/

private noncomputable def complexResolventMatrix
    (A : NodeMatrix Node) (z : ℂ) : ComplexNodeMatrix Node :=
  complexMatrixSub (Node := Node)
    (fun i j : Node => z * complexIdentityMatrix (Node := Node) i j)
    (complexOfRealMatrix (Node := Node) A)

/-- The complex contour Riesz projection
`(2πi)⁻¹ ∮ (zI-A)⁻¹ dz` on a fixed circle.

This is the canonical Appendix A object.  It is intentionally defined from
Mathlib's `circleIntegral` and the concrete nonsingular inverse for the
complex scalar extension, rather than by choosing an arbitrary projection
branch from an existence theorem. -/

private noncomputable def complexRieszProjectionOnCircle
    (A : NodeMatrix Node) (center : ℂ) (radius : ℝ) :
    ComplexNodeMatrix Node := by
  classical
  exact fun i j : Node =>
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (∮ z in C(center, radius),
        ((complexResolventMatrix (Node := Node) A z)⁻¹) i j)

/-- Entrywise real part of a complex node matrix. -/

private theorem circleIntegral_eq_Icc_integral_deriv_mul
    (f : ℂ → ℂ) (center : ℂ) (radius : ℝ) :
    (∮ z in C(center, radius), f z) =
      ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center radius) theta *
          f (circleMap center radius theta) := by
  simpa only [smul_eq_mul] using
    (circleIntegral_def_Icc f center radius)

private theorem complexRieszProjectionOnCircle_entry_eq_Icc_integral
    (A : NodeMatrix Node) (center : ℂ) (radius : ℝ) (i j : Node) :
    complexRieszProjectionOnCircle (Node := Node) A center radius i j =
      (letI : DecidableEq Node := Classical.decEq Node;
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center radius) theta •
              ((complexResolventMatrix (Node := Node) A
                (circleMap center radius theta))⁻¹) i j)) := by
  letI : DecidableEq Node := Classical.decEq Node
  rw [complexRieszProjectionOnCircle,
    circleIntegral_eq_Icc_integral_deriv_mul]
  rfl

/-- Pointwise analyticity of the real-parameter integrand after restricting
the fixed spectral parameter to the source circle.

This consumes the already-proved fixed-`z` scaled resolvent analyticity and
the `circleMap` sphere identity; it leaves only the genuine
analytic-under-interval-integral step for the contour entry. -/

private theorem complexIdentityMatrix_apply [DecidableEq Node] (i j : Node) :
    complexIdentityMatrix (Node := Node) i j =
      if i = j then (1 : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp [complexIdentityMatrix]
  · simp [complexIdentityMatrix, hij]

private theorem complexIdentityMatrix_eq_one [DecidableEq Node] :
    complexIdentityMatrix (Node := Node) = (1 : Matrix Node Node ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [complexIdentityMatrix]
  · simp [complexIdentityMatrix, hij]

private theorem complexMatrixMul_apply
    (A B : ComplexNodeMatrix Node) (i k : Node) :
    complexMatrixMul (Node := Node) A B i k =
      ∑ j : Node, A i j * B j k := by
  classical
  simp [complexMatrixMul, Matrix.mul_apply, dotProduct]

private theorem complexNodeMatrixMulVector_apply
    (A : ComplexNodeMatrix Node) (v : ComplexRowVector Node) (i : Node) :
    complexNodeMatrixMulVector (Node := Node) A v i =
      ∑ j : Node, A i j * v j := by
  classical
  simp [complexNodeMatrixMulVector, Matrix.mulVec, dotProduct]

private theorem complexNodeMatrixMulVector_complexOfRealMatrix
    (A : NodeMatrix Node) (v : ComplexRowVector Node) :
    complexNodeMatrixMulVector (Node := Node)
        (complexOfRealMatrix (Node := Node) A) v =
      complexMatrixMulVector (Node := Node) A v := by
  classical
  funext i
  simp [complexNodeMatrixMulVector_apply, complexOfRealMatrix,
    complexMatrixMulVector]

private theorem complex_resolvent_row_sum_eq [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ) (v : ComplexRowVector Node) (i : Node) :
    (∑ x : Node, ((if i = x then z else 0) - (A i x : ℂ)) * v x) =
      z * v i - ∑ x : Node, (A i x : ℂ) * v x := by
  classical
  calc
    (∑ x : Node, ((if i = x then z else 0) - (A i x : ℂ)) * v x)
        = (∑ x : Node, (if i = x then z else 0) * v x) -
            ∑ x : Node, (A i x : ℂ) * v x := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib]
    _ = z * v i - ∑ x : Node, (A i x : ℂ) * v x := by
          simp

private theorem complexResolventMatrix_mulVec_eq_zero_iff_eigen
    (A : NodeMatrix Node) (z : ℂ) (v : ComplexRowVector Node) :
    complexNodeMatrixMulVector (Node := Node)
        (complexResolventMatrix (Node := Node) A z) v = 0 ↔
      complexMatrixMulVector (Node := Node) A v = z • v := by
  classical
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp [complexNodeMatrixMulVector_apply, complexResolventMatrix,
      complexMatrixSub, complexIdentityMatrix_apply, complexOfRealMatrix,
      complexMatrixMulVector, Pi.smul_apply] at hi ⊢
    rw [complex_resolvent_row_sum_eq (Node := Node) A z v i] at hi
    exact (sub_eq_zero.mp hi).symm
  · intro h
    funext i
    have hi := congrFun h i
    simp [complexNodeMatrixMulVector_apply, complexResolventMatrix,
      complexMatrixSub, complexIdentityMatrix_apply, complexOfRealMatrix,
      complexMatrixMulVector, Pi.smul_apply] at hi ⊢
    rw [complex_resolvent_row_sum_eq (Node := Node) A z v i]
    exact sub_eq_zero.mpr hi.symm

private theorem complexResolvent_det_ne_zero_of_not_eigen [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hvne, hvker⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := complexResolventMatrix (Node := Node) A z)).2 hdet
  apply hnot
  refine ⟨v, hvne, ?_⟩
  exact (complexResolventMatrix_mulVec_eq_zero_iff_eigen
    (Node := Node) A z v).1 (by
      simpa [complexNodeMatrixMulVector] using hvker)

/-- Conversely, a nonsingular concrete resolvent excludes complex right
eigenvectors at the spectral parameter. -/

private theorem not_isComplexRightEigenvalue_of_complexResolvent_det_ne_zero
    [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hdet : Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0) :
    ¬ IsComplexRightEigenvalue (Node := Node) A z := by
  classical
  intro heig
  obtain ⟨v, hvne, hv⟩ := heig
  apply hdet
  exact (Matrix.exists_mulVec_eq_zero_iff
    (M := complexResolventMatrix (Node := Node) A z)).1
    ⟨v, hvne, by
      simpa [complexNodeMatrixMulVector] using
        (complexResolventMatrix_mulVec_eq_zero_iff_eigen
          (Node := Node) A z v).2 hv⟩

/-- For fixed `A`, the resolvent matrix is continuous as a function of the
complex spectral parameter. -/

private theorem complexResolventMatrix_continuous_z
    (A : NodeMatrix Node) :
    Continuous (fun z : ℂ =>
      complexResolventMatrix (Node := Node) A z) := by
  classical
  change Continuous (fun z : ℂ => fun i : Node => fun j : Node =>
    complexResolventMatrix (Node := Node) A z i j)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold complexResolventMatrix complexMatrixSub complexOfRealMatrix
  exact (continuous_id.mul continuous_const).sub continuous_const

/-- For fixed `A`, the determinant of the resolvent matrix is continuous in the
complex spectral parameter. -/

private theorem complexResolventDet_continuous_z [DecidableEq Node]
    (A : NodeMatrix Node) :
    Continuous (fun z : ℂ =>
      Matrix.det (complexResolventMatrix (Node := Node) A z)) := by
  exact (Continuous.matrix_det continuous_id).comp
    (complexResolventMatrix_continuous_z (Node := Node) A)

private theorem complexMatrix_det_analyticAt_z [DecidableEq Node]
    (M : ℂ → ComplexNodeMatrix Node) {z0 : ℂ}
    (hM : ∀ i j : Node, AnalyticAt ℂ (fun z : ℂ => M z i j) z0) :
    AnalyticAt ℂ (fun z : ℂ => Matrix.det (M z)) z0 := by
  classical
  simpa [Matrix.det_apply'] using
    Finset.analyticAt_fun_sum
      (Finset.univ : Finset (Equiv.Perm Node)) (fun σ _hσ =>
      analyticAt_const.mul
        (Finset.analyticAt_fun_prod Finset.univ (fun i _hi =>
          hM (σ i) i)))

private theorem complexMatrix_adjugate_entry_analyticAt_z [DecidableEq Node]
    (M : ℂ → ComplexNodeMatrix Node) {z0 : ℂ}
    (hM : ∀ i j : Node, AnalyticAt ℂ (fun z : ℂ => M z i j) z0)
    (i j : Node) :
    AnalyticAt ℂ (fun z : ℂ => Matrix.adjugate (M z) i j) z0 := by
  classical
  simpa [Matrix.adjugate_apply] using
    (complexMatrix_det_analyticAt_z (Node := Node)
      (fun z : ℂ => (M z).updateRow j (Pi.single i (1 : ℂ)))
      (z0 := z0) (by
        intro r c
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow] using
            (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
              (v := ((Pi.single i (1 : ℂ) : Node → ℂ) c)) (x := z0))
        · simpa [Matrix.updateRow, hr] using hM r c))

private theorem complexMatrix_inv_entry_analyticAt_z_of_det_ne_zero
    [DecidableEq Node]
    (M : ℂ → ComplexNodeMatrix Node) {z0 : ℂ}
    (hM : ∀ i j : Node, AnalyticAt ℂ (fun z : ℂ => M z i j) z0)
    (hdet : Matrix.det (M z0) ≠ 0) (i j : Node) :
    AnalyticAt ℂ (fun z : ℂ => (M z)⁻¹ i j) z0 := by
  classical
  have hdet_analytic :
      AnalyticAt ℂ (fun z : ℂ => Matrix.det (M z)) z0 :=
    complexMatrix_det_analyticAt_z (Node := Node) M hM
  have hinv_base :
      AnalyticAt ℂ (fun x : ℂ => x⁻¹) (Matrix.det (M z0)) :=
    analyticAt_inv hdet
  have hinv_det :
      AnalyticAt ℂ (fun z : ℂ => (Matrix.det (M z))⁻¹) z0 :=
    AnalyticAt.comp_of_eq' (𝕜 := ℂ)
      (g := fun x : ℂ => x⁻¹)
      (f := fun z : ℂ => Matrix.det (M z))
      (y := Matrix.det (M z0)) (x := z0)
      hinv_base hdet_analytic rfl
  have hentry :
      AnalyticAt ℂ
        (fun z : ℂ =>
          (Matrix.det (M z))⁻¹ * Matrix.adjugate (M z) i j) z0 :=
    hinv_det.mul
      (complexMatrix_adjugate_entry_analyticAt_z (Node := Node) M hM i j)
  simpa [Matrix.inv_def, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using
    hentry

private theorem complexResolventMatrix_entry_analyticAt_z
    (A0 : NodeMatrix Node) {z0 : ℂ} (i j : Node) :
    AnalyticAt ℂ
      (fun z : ℂ => complexResolventMatrix (Node := Node) A0 z i j) z0 := by
  classical
  have hlinear :
      AnalyticAt ℂ
        (fun z : ℂ =>
          z * complexIdentityMatrix (Node := Node) i j - (A0 i j : ℂ)) z0 :=
    (analyticAt_id.mul analyticAt_const).sub analyticAt_const
  simpa [complexResolventMatrix, complexMatrixSub, complexOfRealMatrix] using
    hlinear

private theorem complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
    [DecidableEq Node]
    (A0 : NodeMatrix Node) {z0 : ℂ}
    (hdet : Matrix.det (complexResolventMatrix (Node := Node) A0 z0) ≠ 0)
    (i j : Node) :
    DifferentiableAt ℂ
      (fun z : ℂ => (complexResolventMatrix (Node := Node) A0 z)⁻¹ i j) z0 := by
  classical
  exact (complexMatrix_inv_entry_analyticAt_z_of_det_ne_zero
    (Node := Node) (fun z : ℂ => complexResolventMatrix (Node := Node) A0 z)
    (z0 := z0)
    (by
      intro r c
      exact complexResolventMatrix_entry_analyticAt_z
        (Node := Node) A0 (z0 := z0) r c)
    hdet i j).differentiableAt

/-- For fixed `z` outside the point spectrum at `alpha`, each canonical
inverse-resolvent entry depends analytically on the real parameter. -/

private theorem circleMap_deriv_continuous (center : ℂ) (radius : ℝ) :
    Continuous (fun theta : ℝ => deriv (circleMap center radius) theta) := by
  have hfun :
      (fun theta : ℝ => deriv (circleMap center radius) theta) =
        fun theta : ℝ => circleMap (0 : ℂ) radius theta * Complex.I := by
    funext theta
    exact deriv_circleMap center radius theta
  rw [hfun]
  have hI : Continuous (fun _ : ℝ => (Complex.I : ℂ)) := continuous_const
  exact (continuous_circleMap (0 : ℂ) radius).mul hI

/-- Joint continuity of the scaled fixed-contour interval integrand.

This is the compact-contour continuity layer below the missing
analytic-under-integral step: after shrinking to a parameter interval where
the fixed shifted circle contains no spectrum, the inverse resolvent entry
composed with the circle parametrization is continuous jointly in the real
parameter and contour angle. -/

private theorem fixed_circle_simple_pole_entry_integral_eq
    (baseRadius : ℝ) (hbaseRadius_pos : 0 < baseRadius) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹ * c) = c := by
  classical
  have hmem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) baseRadius := by
    simpa [Metric.mem_ball, dist_self] using hbaseRadius_pos
  have hinv :
      (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball
      (c := (1 : ℂ)) (w := (1 : ℂ)) (R := baseRadius) hmem
  have hconst :
      (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹ * c) =
        c * (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹) := by
    rw [show (fun z : ℂ => (z - (1 : ℂ))⁻¹ * c) =
        fun z : ℂ => c * (z - (1 : ℂ))⁻¹ by
          funext z
          ring]
    exact circleIntegral.integral_const_mul c
      (fun z : ℂ => (z - (1 : ℂ))⁻¹) (1 : ℂ) baseRadius
  rw [hconst, hinv]
  rw [mul_comm c ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)]
  rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

private theorem circleIntegral_sub_inv_mul_const_eq_of_mem_ball
    {center pole : ℂ} {radius : ℝ}
    (hpole : pole ∈ Metric.ball center radius) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C(center, radius), (z - pole)⁻¹ * c) = c := by
  classical
  have hinv :
      (∮ z in C(center, radius), (z - pole)⁻¹) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball
      (c := center) (w := pole) (R := radius) hpole
  have hconst :
      (∮ z in C(center, radius), (z - pole)⁻¹ * c) =
        c * (∮ z in C(center, radius), (z - pole)⁻¹) := by
    rw [show (fun z : ℂ => (z - pole)⁻¹ * c) =
        fun z : ℂ => c * (z - pole)⁻¹ by
          funext z
          ring]
    exact circleIntegral.integral_const_mul c
      (fun z : ℂ => (z - pole)⁻¹) center radius
  rw [hconst, hinv]
  rw [mul_comm c ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)]
  rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

private theorem circleIntegral_w_sub_inv_mul_const_eq_neg_of_mem_ball
    {center pole : ℂ} {radius : ℝ}
    (hpole : pole ∈ Metric.ball center radius) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C(center, radius), (pole - z)⁻¹ * c) = -c := by
  classical
  have hrewrite :
      (∮ z in C(center, radius), (pole - z)⁻¹ * c) =
        ∮ z in C(center, radius), (z - pole)⁻¹ * (-c) := by
    have hradius_pos : 0 < radius := by
      have hdist_nonneg : 0 ≤ dist pole center := dist_nonneg
      have hdist_lt : dist pole center < radius := Metric.mem_ball.mp hpole
      linarith
    refine circleIntegral.integral_congr
      (le_of_lt hradius_pos) ?_
    intro z _hz
    change (pole - z)⁻¹ * c = (z - pole)⁻¹ * (-c)
    have hneg : pole - z = -(z - pole) := by ring
    rw [hneg]
    rw [inv_neg]
    ring
  rw [hrewrite]
  simpa using
    circleIntegral_sub_inv_mul_const_eq_of_mem_ball
      (center := center) (pole := pole) (radius := radius) hpole (-c)

private theorem circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) :
    (∮ z in C(center, radius), (z - pole)⁻¹) = 0 := by
  classical
  refine
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hradius_nonneg (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · intro z hz
    have hzw : z ≠ pole := by
      intro hzp
      exact hpole (by simpa [hzp] using hz)
    have hsub_ne : z - pole ≠ 0 := sub_ne_zero.mpr hzw
    have hsub_diff :
        DifferentiableAt ℂ (fun y : ℂ => y - pole) z :=
      differentiableAt_id.sub
        (differentiableAt_const (𝕜 := ℂ) (c := pole) (x := z))
    exact
      ((differentiableAt_inv hsub_ne).comp z hsub_diff).continuousAt.continuousWithinAt
  · intro z hz
    have hzclosed : z ∈ Metric.closedBall center radius :=
      Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.mp hz.1))
    have hzw : z ≠ pole := by
      intro hzp
      exact hpole (by simpa [hzp] using hzclosed)
    have hsub_ne : z - pole ≠ 0 := sub_ne_zero.mpr hzw
    have hsub_diff :
        DifferentiableAt ℂ (fun y : ℂ => y - pole) z :=
      differentiableAt_id.sub
        (differentiableAt_const (𝕜 := ℂ) (c := pole) (x := z))
    exact (differentiableAt_inv hsub_ne).comp z hsub_diff

private theorem circleIntegral_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) (c : ℂ) :
    (∮ z in C(center, radius), (z - pole)⁻¹ * c) = 0 := by
  classical
  have hconst :
      (∮ z in C(center, radius), (z - pole)⁻¹ * c) =
        c * (∮ z in C(center, radius), (z - pole)⁻¹) := by
    rw [show (fun z : ℂ => (z - pole)⁻¹ * c) =
        fun z : ℂ => c * (z - pole)⁻¹ by
          funext z
          ring]
    exact circleIntegral.integral_const_mul c
      (fun z : ℂ => (z - pole)⁻¹) center radius
  rw [hconst,
    circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
      hradius_nonneg hpole]
  simp

private theorem circleIntegral_w_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) (c : ℂ) :
    (∮ z in C(center, radius), (pole - z)⁻¹ * c) = 0 := by
  classical
  have hrewrite :
      (∮ z in C(center, radius), (pole - z)⁻¹ * c) =
        ∮ z in C(center, radius), (z - pole)⁻¹ * (-c) := by
    refine circleIntegral.integral_congr hradius_nonneg ?_
    intro z _hz
    change (pole - z)⁻¹ * c = (z - pole)⁻¹ * (-c)
    have hneg : pole - z = -(z - pole) := by ring
    rw [hneg, inv_neg]
    ring
  rw [hrewrite]
  exact circleIntegral_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    hradius_nonneg hpole (-c)

private theorem complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    (∮ z in C((1 : ℂ), outerRadius),
        ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) =
      ∮ z in C((1 : ℂ), innerRadius),
        ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j := by
  classical
  refine
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := (1 : ℂ)) hinner_pos hradii (s := (∅ : Set ℂ))
      Set.countable_empty ?_ ?_
  · intro z hz
    rcases hz with ⟨hzclosed, hznotball⟩
    have hlower : innerRadius ≤ ‖z - (1 : ℂ)‖ := by
      have hnotlt : ¬ dist z (1 : ℂ) < innerRadius := by
        intro hlt
        exact hznotball (Metric.mem_ball.2 hlt)
      simpa [dist_eq_norm] using le_of_not_gt hnotlt
    have hupper : ‖z - (1 : ℂ)‖ ≤ outerRadius := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hzclosed)
    have hdet :
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
        (hnoAnnulus z hlower hupper)
    exact
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i j).continuousAt.continuousWithinAt
  · intro z hz
    rcases hz with ⟨⟨hzball, hznotclosed⟩, _hznotempty⟩
    have hlower : innerRadius ≤ ‖z - (1 : ℂ)‖ := by
      have hnotle : ¬ dist z (1 : ℂ) ≤ innerRadius := by
        intro hle
        exact hznotclosed (Metric.mem_closedBall.2 hle)
      exact le_of_lt (by
        simpa [dist_eq_norm] using lt_of_not_ge hnotle)
    have hupper : ‖z - (1 : ℂ)‖ ≤ outerRadius := by
      exact le_of_lt (by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hzball))
    have hdet :
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
        (hnoAnnulus z hlower hupper)
    exact complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
      (Node := Node) Aalpha hdet i j

private theorem complexRieszProjectionOnCircle_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) outerRadius =
      complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) innerRadius := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  ext i j
  simp only [complexRieszProjectionOnCircle]
  exact congrArg
    (fun x : ℂ => (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) * x)
    (complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
      (Node := Node) Aalpha hinner_pos hradii hnoAnnulus i j)

private theorem mem_cthickening_sphere_of_abs_norm_sub_le
    {center z : ℂ} {radius delta : ℝ}
    (hradius_pos : 0 < radius) (hdelta_nonneg : 0 ≤ delta)
    (hdelta_lt_radius : delta < radius)
    (hz : |‖z - center‖ - radius| ≤ delta) :
    z ∈ Metric.cthickening delta (Metric.sphere center radius) := by
  classical
  let d : ℝ := ‖z - center‖
  have hd_pos : 0 < d := by
    have hleft : -delta ≤ d - radius := (abs_le.mp hz).1
    dsimp [d]
    nlinarith [hradius_pos, hdelta_lt_radius, hleft]
  let y : ℂ := center + ((radius / d : ℝ) : ℂ) * (z - center)
  have hy_sphere : y ∈ Metric.sphere center radius := by
    have hy_sub : y - center = ((radius / d : ℝ) : ℂ) * (z - center) := by
      simp [y]
    have hnorm :
        ‖((radius / d : ℝ) : ℂ) * (z - center)‖ = radius := by
      have hdiv_nonneg : 0 ≤ radius / d := div_nonneg
        (le_of_lt hradius_pos) (le_of_lt hd_pos)
      rw [norm_mul, Complex.norm_of_nonneg hdiv_nonneg]
      rw [show ‖z - center‖ = d by rfl]
      field_simp [ne_of_gt hd_pos]
    exact Metric.mem_sphere.mpr (by
      simpa [dist_eq_norm, hy_sub] using hnorm)
  have hdist_le : dist z y ≤ delta := by
    have hz_sub :
        z - y = (1 - ((radius / d : ℝ) : ℂ)) * (z - center) := by
      simp [y]
      ring
    have hnorm :
        ‖(1 - ((radius / d : ℝ) : ℂ)) * (z - center)‖ =
          |d - radius| := by
      rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real]
      rw [show ‖z - center‖ = d by rfl]
      have hfactor :
          |(1 : ℝ) - radius / d| * d = |d - radius| := by
        have hd_ne : d ≠ 0 := ne_of_gt hd_pos
        calc
          |(1 : ℝ) - radius / d| * d =
              |(d - radius) / d| * d := by
                congr 1
                field_simp [hd_ne]
          _ = (|d - radius| / d) * d := by
                rw [abs_div, abs_of_pos hd_pos]
          _ = |d - radius| := by
                field_simp [hd_ne]
      simpa [d] using hfactor
    have hdist : dist z y = |d - radius| := by
      simpa [dist_eq_norm, hz_sub] using hnorm
    simpa [d, hdist] using hz
  exact Metric.mem_cthickening_of_dist_le z y delta
    (Metric.sphere center radius) hy_sphere hdist_le

private theorem exists_no_eigen_annulus_around_fixed_circle
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    ∃ innerRadius outerRadius : ℝ,
      0 < innerRadius ∧ innerRadius < baseRadius ∧
      baseRadius < outerRadius ∧
      (∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) := by
  classical
  let center : ℂ := 1
  let sphere : Set ℂ := Metric.sphere center baseRadius
  let detFun : ℂ → ℂ := fun z =>
    Matrix.det (complexResolventMatrix (Node := Node) Aalpha z)
  let U : Set ℂ := {z : ℂ | detFun z ≠ 0}
  have hscompact : IsCompact sphere := by
    simpa [sphere] using isCompact_sphere center baseRadius
  have hUopen : IsOpen U := by
    have hclosed : IsClosed (detFun ⁻¹' ({0} : Set ℂ)) := by
      exact isClosed_singleton.preimage
        ((complexResolventDet_continuous_z (Node := Node) Aalpha))
    simpa [U, detFun, Set.preimage, Set.compl_setOf] using hclosed.isOpen_compl
  have hs_subset_U : sphere ⊆ U := by
    intro z hz
    have hzboundary : ‖z - (1 : ℂ)‖ = baseRadius := by
      simpa [sphere, center, Metric.mem_sphere, dist_eq_norm] using hz
    exact complexResolvent_det_ne_zero_of_not_eigen
      (Node := Node) Aalpha z (hnoBoundary z hzboundary)
  rcases hscompact.exists_cthickening_subset_open hUopen hs_subset_U with
    ⟨delta, hdelta_pos, hdelta_subset⟩
  let eta : ℝ := min (delta / 2) (baseRadius / 2)
  have heta_pos : 0 < eta := by
    exact lt_min (half_pos hdelta_pos) (half_pos hbaseRadius_pos)
  have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
  have heta_le_delta : eta ≤ delta := by
    exact le_trans (min_le_left (delta / 2) (baseRadius / 2)) (by linarith)
  have heta_lt_radius : eta < baseRadius := by
    exact lt_of_le_of_lt (min_le_right (delta / 2) (baseRadius / 2)) (by linarith)
  refine ⟨baseRadius - eta, baseRadius + eta, ?_, ?_, ?_, ?_⟩
  · nlinarith [heta_lt_radius]
  · nlinarith [heta_pos]
  · nlinarith [heta_pos]
  · intro z hzinner hzouter
    have hz_abs : |‖z - (1 : ℂ)‖ - baseRadius| ≤ eta := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [hzinner, hzouter]
    have hz_cthick_eta :
        z ∈ Metric.cthickening eta sphere := by
      exact mem_cthickening_sphere_of_abs_norm_sub_le
        (center := center) (radius := baseRadius) hbaseRadius_pos
        heta_nonneg heta_lt_radius (by simpa [center] using hz_abs)
    have hz_cthick_delta :
        z ∈ Metric.cthickening delta sphere :=
      Metric.cthickening_mono heta_le_delta sphere hz_cthick_eta
    have hdet_ne : detFun z ≠ 0 := hdelta_subset hz_cthick_delta
    exact not_isComplexRightEigenvalue_of_complexResolvent_det_ne_zero
      (Node := Node) Aalpha z (by simpa [detFun] using hdet_ne)

private theorem complex_resolvent_inverse_identity_two_points
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (z w : ℂ)
    (hz : ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (hw : ¬ IsComplexRightEigenvalue (Node := Node) A0 w) :
    (complexResolventMatrix (Node := Node) A0 z)⁻¹ -
        (complexResolventMatrix (Node := Node) A0 w)⁻¹ =
      (w - z) •
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹ *
          (complexResolventMatrix (Node := Node) A0 w)⁻¹) := by
  classical
  let Mz : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 z
  let Mw : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 w
  have hdetz : Matrix.det Mz ≠ 0 := by
    simpa [Mz] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 z hz
  have hdetw : Matrix.det Mw ≠ 0 := by
    simpa [Mw] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 w hw
  have hMzUnit : IsUnit Mz :=
    (Matrix.isUnit_iff_isUnit_det Mz).2 (isUnit_iff_ne_zero.mpr hdetz)
  have hMwUnit : IsUnit Mw :=
    (Matrix.isUnit_iff_isUnit_det Mw).2 (isUnit_iff_ne_zero.mpr hdetw)
  have hunits : IsUnit Mz ↔ IsUnit Mw := ⟨fun _ => hMwUnit, fun _ => hMzUnit⟩
  have hdiff_inv :
      Mz⁻¹ - Mw⁻¹ = Mz⁻¹ * (Mw - Mz) * Mw⁻¹ :=
    Matrix.inv_sub_inv (A := Mz) (B := Mw) hunits
  have hdiff_matrix :
      Mw - Mz = (w - z) • (1 : ComplexNodeMatrix Node) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Mz, Mw, complexResolventMatrix, complexMatrixSub,
        complexIdentityMatrix, complexOfRealMatrix]
    · simp [Mz, Mw, complexResolventMatrix, complexMatrixSub,
        complexIdentityMatrix, complexOfRealMatrix, hij]
  have hscalar :
      Mz⁻¹ * ((w - z) • (1 : ComplexNodeMatrix Node)) * Mw⁻¹ =
        (w - z) • (Mz⁻¹ * Mw⁻¹) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum]
    ring
  calc
    (complexResolventMatrix (Node := Node) A0 z)⁻¹ -
        (complexResolventMatrix (Node := Node) A0 w)⁻¹ =
        Mz⁻¹ - Mw⁻¹ := rfl
    _ = Mz⁻¹ * (Mw - Mz) * Mw⁻¹ := hdiff_inv
    _ = Mz⁻¹ * ((w - z) • (1 : ComplexNodeMatrix Node)) * Mw⁻¹ := by
          rw [hdiff_matrix]
    _ = (w - z) • (Mz⁻¹ * Mw⁻¹) := hscalar
    _ = (w - z) •
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹ *
          (complexResolventMatrix (Node := Node) A0 w)⁻¹) := rfl

private theorem complex_resolvent_inverse_product_entry_eq_div_difference
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (z w : ℂ)
    (hz : ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (hw : ¬ IsComplexRightEigenvalue (Node := Node) A0 w)
    (hwz : w ≠ z) (i j : Node) :
    (∑ k : Node,
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i k *
          ((complexResolventMatrix (Node := Node) A0 w)⁻¹) k j) =
      (w - z)⁻¹ *
        (((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j -
          ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j) := by
  classical
  let Rz : ComplexNodeMatrix Node :=
    (complexResolventMatrix (Node := Node) A0 z)⁻¹
  let Rw : ComplexNodeMatrix Node :=
    (complexResolventMatrix (Node := Node) A0 w)⁻¹
  have hidentity :
      Rz - Rw = (w - z) • (Rz * Rw) := by
    simpa [Rz, Rw] using
      complex_resolvent_inverse_identity_two_points (Node := Node)
        A0 z w hz hw
  have hentry :
      Rz i j - Rw i j =
        (w - z) *
          (∑ k : Node, Rz i k * Rw k j) := by
    have h := congrArg (fun M : ComplexNodeMatrix Node => M i j) hidentity
    simpa [Matrix.sub_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
      using h
  have hsub_ne : w - z ≠ 0 := sub_ne_zero.mpr hwz
  calc
    (∑ k : Node, Rz i k * Rw k j) =
        (w - z)⁻¹ * ((w - z) *
          (∑ k : Node, Rz i k * Rw k j)) := by
          field_simp [hsub_ne]
    _ = (w - z)⁻¹ * (Rz i j - Rw i j) := by
          rw [← hentry]
    _ =
      (w - z)⁻¹ *
        (((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j -
          ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j) := by
          simp [Rz, Rw]

private def complexConjMatrix (M : ComplexNodeMatrix Node) :
    ComplexNodeMatrix Node :=
  fun i j => conj (M i j)

private theorem complexConjMatrix_one [DecidableEq Node] :
    complexConjMatrix (Node := Node) (1 : ComplexNodeMatrix Node) = 1 := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    simp [complexConjMatrix]
  · simp [complexConjMatrix, Matrix.one_apply, hij]

private theorem complexConjMatrix_mul [DecidableEq Node]
    (M N : ComplexNodeMatrix Node) :
    complexConjMatrix (Node := Node) (M * N) =
      complexConjMatrix (Node := Node) M *
        complexConjMatrix (Node := Node) N := by
  classical
  funext i j
  calc
    complexConjMatrix (Node := Node) (M * N) i j =
        conj (∑ k : Node, M i k * N k j) := by
          simp [complexConjMatrix, Matrix.mul_apply]
    _ = ∑ k : Node, conj (M i k * N k j) := by
          simpa using
            (map_sum Complex.conjAe (fun k : Node => M i k * N k j)
              Finset.univ)
    _ = (complexConjMatrix (Node := Node) M *
          complexConjMatrix (Node := Node) N) i j := by
          simp [complexConjMatrix, Matrix.mul_apply]

private theorem complexConjMatrix_resolvent
    (A0 : NodeMatrix Node) (z : ℂ) :
    complexConjMatrix (Node := Node)
        (complexResolventMatrix (Node := Node) A0 z) =
      complexResolventMatrix (Node := Node) A0 (conj z) := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    simp [complexConjMatrix, complexResolventMatrix, complexMatrixSub,
      complexIdentityMatrix, complexOfRealMatrix]
  · simp [complexConjMatrix, complexResolventMatrix, complexMatrixSub,
      complexIdentityMatrix, complexOfRealMatrix, hij]

private theorem fixed_unit_circle_conj_boundary
    (baseRadius : ℝ) {z : ℂ}
    (hz : ‖z - (1 : ℂ)‖ = baseRadius) :
    ‖conj z - (1 : ℂ)‖ = baseRadius := by
  calc
    ‖conj z - (1 : ℂ)‖ = ‖conj (z - (1 : ℂ))‖ := by
      rw [map_sub]
      simp
    _ = ‖z - (1 : ℂ)‖ := Complex.norm_conj _
    _ = baseRadius := hz

private theorem fixed_circleMap_boundary_norm
    (baseRadius : ℝ) (hbaseRadius_pos : 0 < baseRadius) (theta : ℝ) :
    ‖circleMap (1 : ℂ) baseRadius theta - (1 : ℂ)‖ = baseRadius := by
  have hmem :
      circleMap (1 : ℂ) baseRadius theta ∈
        Metric.sphere (1 : ℂ) baseRadius :=
    circleMap_mem_sphere (1 : ℂ) (le_of_lt hbaseRadius_pos) theta
  simpa [Metric.mem_sphere, dist_eq_norm] using hmem

private theorem fixed_circleMap_outer_not_mem_closedBall_inner
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (theta : ℝ) :
    circleMap (1 : ℂ) outerRadius theta ∉
      Metric.closedBall (1 : ℂ) innerRadius := by
  intro hmem
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have hdist_outer :
      dist (circleMap (1 : ℂ) outerRadius theta) (1 : ℂ) =
        outerRadius := by
    simpa [dist_eq_norm] using
      fixed_circleMap_boundary_norm outerRadius houter_pos theta
  have hdist_le :
      dist (circleMap (1 : ℂ) outerRadius theta) (1 : ℂ) ≤
        innerRadius :=
    Metric.mem_closedBall.mp hmem
  linarith

private theorem fixed_circleMap_inner_mem_ball_outer
    {innerRadius outerRadius : ℝ}
    (hinner_nonneg : 0 ≤ innerRadius) (hradii : innerRadius < outerRadius)
    (phi : ℝ) :
    circleMap (1 : ℂ) innerRadius phi ∈
      Metric.ball (1 : ℂ) outerRadius := by
  have hdist_inner :
      dist (circleMap (1 : ℂ) innerRadius phi) (1 : ℂ) =
        innerRadius := by
    by_cases hinner_pos : 0 < innerRadius
    · simpa [dist_eq_norm] using
        fixed_circleMap_boundary_norm innerRadius hinner_pos phi
    · have hinner_zero : innerRadius = 0 := by linarith
      simp [hinner_zero, circleMap, dist_self]
  exact Metric.mem_ball.mpr (by linarith)

private theorem fixed_circleIntegral_inner_sub_outer_point_mul_const_eq_zero
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (theta : ℝ) (c : ℂ) :
    (∮ w in C((1 : ℂ), innerRadius),
        (w - circleMap (1 : ℂ) outerRadius theta)⁻¹ * c) = 0 := by
  exact circleIntegral_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    (center := (1 : ℂ)) (pole := circleMap (1 : ℂ) outerRadius theta)
    (radius := innerRadius) (le_of_lt hinner_pos)
    (fixed_circleMap_outer_not_mem_closedBall_inner hinner_pos hradii theta) c

private theorem fixed_circleIntegral_outer_inner_point_sub_mul_const_eq_neg
    {innerRadius outerRadius : ℝ}
    (hinner_nonneg : 0 ≤ innerRadius) (hradii : innerRadius < outerRadius)
    (phi : ℝ) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), outerRadius),
          (circleMap (1 : ℂ) innerRadius phi - z)⁻¹ * c) = -c := by
  exact circleIntegral_w_sub_inv_mul_const_eq_neg_of_mem_ball
    (center := (1 : ℂ)) (pole := circleMap (1 : ℂ) innerRadius phi)
    (radius := outerRadius)
    (fixed_circleMap_inner_mem_ball_outer hinner_nonneg hradii phi) c

private theorem fixed_circleParameter_inner_sub_outer_point_mul_const_eq_zero
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (theta : ℝ) (c : ℂ) :
    (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((circleMap (1 : ℂ) innerRadius phi -
              circleMap (1 : ℂ) outerRadius theta)⁻¹ * c)) = 0 := by
  have hcircle :=
    fixed_circleIntegral_inner_sub_outer_point_mul_const_eq_zero
      (innerRadius := innerRadius) (outerRadius := outerRadius)
      hinner_pos hradii theta c
  rw [circleIntegral_eq_Icc_integral_deriv_mul] at hcircle
  simpa [mul_assoc] using hcircle

private theorem fixed_circleParameter_outer_inner_point_sub_mul_const_eq_neg
    {innerRadius outerRadius : ℝ}
    (hinner_nonneg : 0 ≤ innerRadius) (hradii : innerRadius < outerRadius)
    (phi : ℝ) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) outerRadius) theta *
          ((circleMap (1 : ℂ) innerRadius phi -
              circleMap (1 : ℂ) outerRadius theta)⁻¹ * c)) = -c := by
  have hcircle :=
    fixed_circleIntegral_outer_inner_point_sub_mul_const_eq_neg
      (innerRadius := innerRadius) (outerRadius := outerRadius)
      hinner_nonneg hradii phi c
  rw [circleIntegral_eq_Icc_integral_deriv_mul] at hcircle
  simpa [mul_assoc] using hcircle

private theorem fixed_zero_circleMap_conj
    (baseRadius theta : ℝ) :
    conj (circleMap (0 : ℂ) baseRadius theta) =
      circleMap (0 : ℂ) baseRadius (-theta) := by
  rw [circleMap, circleMap]
  simp only [zero_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  apply congrArg Complex.exp
  simp

private theorem fixed_circleMap_conj
    (baseRadius theta : ℝ) :
    conj (circleMap (1 : ℂ) baseRadius theta) =
      circleMap (1 : ℂ) baseRadius (-theta) := by
  rw [circleMap, circleMap]
  simp only [map_add, map_one, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 2
  apply congrArg Complex.exp
  simp

private theorem fixed_circleMap_deriv_conj
    (baseRadius theta : ℝ) :
    conj (deriv (circleMap (1 : ℂ) baseRadius) theta) =
      -deriv (circleMap (1 : ℂ) baseRadius) (-theta) := by
  calc
    conj (deriv (circleMap (1 : ℂ) baseRadius) theta) =
        conj (circleMap (0 : ℂ) baseRadius theta * Complex.I) := by
          exact congrArg conj (deriv_circleMap (1 : ℂ) baseRadius theta)
    _ =
        conj (circleMap (0 : ℂ) baseRadius theta) * conj Complex.I := by
          rw [map_mul]
    _ = circleMap (0 : ℂ) baseRadius (-theta) * (-Complex.I) := by
          rw [fixed_zero_circleMap_conj]
          simp
    _ = -(circleMap (0 : ℂ) baseRadius (-theta) * Complex.I) := by
          ring
    _ = -deriv (circleMap (1 : ℂ) baseRadius) (-theta) := by
          exact congrArg (fun z : ℂ => -z)
            (deriv_circleMap (1 : ℂ) baseRadius (-theta)).symm

private theorem complex_Icc_integral_conj
    (l u : ℝ) (f : ℝ → ℂ) :
    conj (∫ theta in Set.Icc l u, f theta) =
      ∫ theta in Set.Icc l u, conj (f theta) := by
  simpa using
    (integral_conj
      (μ := volume.restrict (Set.Icc l u)) (f := f)).symm

private theorem complex_setIntegral_Icc_eq_intervalIntegral
    (l u : ℝ) (f : ℝ → ℂ) (hlu : l ≤ u) :
    (∫ theta in Set.Icc l u, f theta) =
      ∫ theta in l..u, f theta := by
  rw [intervalIntegral.integral_of_le hlu,
    MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem complex_setIntegral_Icc_Icc_swap_of_continuousOn
    (a b c d : ℝ) (F : ℝ → ℝ → ℂ)
    (hF :
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in Set.Icc a b, ∫ y in Set.Icc c d, F x y) =
      ∫ y in Set.Icc c d, ∫ x in Set.Icc a b, F x y := by
  classical
  let s : Set ℝ := Set.Icc a b
  let t : Set ℝ := Set.Icc c d
  let G : ℝ × ℝ → ℂ := fun p => F p.1 p.2
  have hcompact : IsCompact (s ×ˢ t) := by
    simpa [s, t] using (isCompact_Icc.prod isCompact_Icc)
  have hmeas : MeasurableSet (s ×ˢ t) := hcompact.measurableSet
  have hfinite : volume (s ×ˢ t) < ⊤ := hcompact.measure_lt_top
  have hGintOn : IntegrableOn G (s ×ˢ t) volume :=
    hF.integrableOn_of_subset_isCompact
      (μ := volume) (K := s ×ˢ t) hcompact hmeas
      (fun p hp => hp) (ne_of_lt hfinite)
  have hGint :
      Integrable (fun p : ℝ × ℝ => G p)
        ((volume.restrict s).prod (volume.restrict t)) := by
    rw [Measure.prod_restrict]
    simpa [IntegrableOn, G] using hGintOn
  calc
    (∫ x in Set.Icc a b, ∫ y in Set.Icc c d, F x y) =
        ∫ x, ∫ y, G (x, y) ∂(volume.restrict t) ∂(volume.restrict s) := by
          simp [s, t, G]
    _ =
        ∫ y, ∫ x, G (x, y) ∂(volume.restrict s) ∂(volume.restrict t) := by
          simpa [G] using
            (MeasureTheory.integral_integral_swap
              (μ := volume.restrict s) (ν := volume.restrict t)
              (f := fun x y => G (x, y)) hGint)
    _ = ∫ y in Set.Icc c d, ∫ x in Set.Icc a b, F x y := by
          simp [s, t, G]

private theorem complex_circleParameter_Icc_integral_swap_of_continuousOn
    (center : ℂ) (outerRadius innerRadius : ℝ) (F : ℂ → ℂ → ℂ)
    (hF :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          deriv (circleMap center outerRadius) p.1 *
            (deriv (circleMap center innerRadius) p.2 *
              F (circleMap center outerRadius p.1)
                (circleMap center innerRadius p.2)))
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          Set.Icc (0 : ℝ) (2 * Real.pi))) :
    (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center outerRadius) theta *
          (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center innerRadius) phi *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi))) =
      ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center innerRadius) phi *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center outerRadius) theta *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi)) := by
  classical
  let H : ℝ → ℝ → ℂ := fun theta phi =>
    deriv (circleMap center outerRadius) theta *
      (deriv (circleMap center innerRadius) phi *
        F (circleMap center outerRadius theta)
          (circleMap center innerRadius phi))
  have hswap :
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi) =
        ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi :=
    complex_setIntegral_Icc_Icc_swap_of_continuousOn
      (0 : ℝ) (2 * Real.pi) (0 : ℝ) (2 * Real.pi) H (by
        simpa [H] using hF)
  calc
    (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center outerRadius) theta *
          (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center innerRadius) phi *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi))) =
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro theta _htheta
          dsimp only
          simpa [H] using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
              (deriv (circleMap center outerRadius) theta)
              (fun phi : ℝ =>
                deriv (circleMap center innerRadius) phi *
                  F (circleMap center outerRadius theta)
                    (circleMap center innerRadius phi))).symm
    _ = ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi := hswap
    _ =
      ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center innerRadius) phi *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center outerRadius) theta *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi)) := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro phi _hphi
          dsimp only
          rw [show
              (fun theta : ℝ => H theta phi) =
                fun theta : ℝ =>
                  deriv (circleMap center innerRadius) phi *
                    (deriv (circleMap center outerRadius) theta *
                      F (circleMap center outerRadius theta)
                        (circleMap center innerRadius phi)) by
            funext theta
            simp [H]
            ring]
          simpa using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
              (deriv (circleMap center innerRadius) phi)
              (fun theta : ℝ =>
                deriv (circleMap center outerRadius) theta *
                  F (circleMap center outerRadius theta)
                    (circleMap center innerRadius phi)))

private theorem separated_resolvent_product_circleParameter_continuousOn
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deriv (circleMap (1 : ℂ) outerRadius) p.1 *
          (deriv (circleMap (1 : ℂ) innerRadius) p.2 *
            (∑ k : Node,
              ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) outerRadius p.1))⁻¹) i k *
                ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) innerRadius p.2))⁻¹) k j)))
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
        Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  classical
  let rect : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (0 : ℝ) (2 * Real.pi)
  have houter_pos : 0 < outerRadius := lt_of_lt_of_le hinner_pos hradii
  have houter_entry :
      ∀ k : Node,
        ContinuousOn
          (fun p : ℝ × ℝ =>
            ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) outerRadius p.1))⁻¹) i k)
          rect := by
    intro k p hp
    have hz_norm :
        ‖circleMap (1 : ℂ) outerRadius p.1 - (1 : ℂ)‖ =
          outerRadius :=
      fixed_circleMap_boundary_norm outerRadius houter_pos p.1
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius p.1)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) outerRadius p.1)
        (hnoAnnulus (circleMap (1 : ℂ) outerRadius p.1)
          (by
            rw [hz_norm]
            exact hradii)
          (by
            rw [hz_norm]))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
          (circleMap (1 : ℂ) outerRadius p.1) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i k).continuousAt
    have hcircle_cont :
        ContinuousWithinAt
          (fun q : ℝ × ℝ => circleMap (1 : ℂ) outerRadius q.1)
          rect p := by
      exact (continuous_circleMap (1 : ℂ) outerRadius).continuousAt
        |>.comp_continuousWithinAt continuousWithinAt_fst
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ => circleMap (1 : ℂ) outerRadius q.1)
      hentry_cont hcircle_cont
  have hinner_entry :
      ∀ k : Node,
        ContinuousOn
          (fun p : ℝ × ℝ =>
            ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) innerRadius p.2))⁻¹) k j)
          rect := by
    intro k p hp
    have hz_norm :
        ‖circleMap (1 : ℂ) innerRadius p.2 - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos p.2
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius p.2)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) innerRadius p.2)
        (hnoAnnulus (circleMap (1 : ℂ) innerRadius p.2)
          (by
            rw [hz_norm])
          (by
            rw [hz_norm]
            exact hradii))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) k j)
          (circleMap (1 : ℂ) innerRadius p.2) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet k j).continuousAt
    have hcircle_cont :
        ContinuousWithinAt
          (fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
          rect p := by
      exact (continuous_circleMap (1 : ℂ) innerRadius).continuousAt
        |>.comp_continuousWithinAt continuousWithinAt_snd
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
      hentry_cont hcircle_cont
  have hsum :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) outerRadius p.1))⁻¹) i k *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) innerRadius p.2))⁻¹) k j)
        rect := by
    refine continuousOn_finset_sum Finset.univ ?_
    intro k _hk
    exact (houter_entry k).mul (hinner_entry k)
  have hderivOuter :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) outerRadius) p.1)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) outerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) outerRadius
    simpa using (hderivTheta.comp continuous_fst).continuousOn
  have hderivInner :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) innerRadius) p.2)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) innerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) innerRadius
    simpa using (hderivTheta.comp continuous_snd).continuousOn
  simpa [rect] using hderivOuter.mul (hderivInner.mul hsum)

private theorem separated_resolvent_product_circleParameter_eq_div_difference
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (theta phi : ℝ) (i j : Node) :
    (∑ k : Node,
        ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j) =
      (circleMap (1 : ℂ) innerRadius phi -
          circleMap (1 : ℂ) outerRadius theta)⁻¹ *
        (((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius theta))⁻¹) i j -
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j) := by
  classical
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have houter_norm :
      ‖circleMap (1 : ℂ) outerRadius theta - (1 : ℂ)‖ =
        outerRadius :=
    fixed_circleMap_boundary_norm outerRadius houter_pos theta
  have hinner_norm :
      ‖circleMap (1 : ℂ) innerRadius phi - (1 : ℂ)‖ =
        innerRadius :=
    fixed_circleMap_boundary_norm innerRadius hinner_pos phi
  have houter_not :
      ¬ IsComplexRightEigenvalue (Node := Node) Aalpha
        (circleMap (1 : ℂ) outerRadius theta) := by
    exact hnoAnnulus (circleMap (1 : ℂ) outerRadius theta)
      (by
        rw [houter_norm]
        exact le_of_lt hradii)
      (by rw [houter_norm])
  have hinner_not :
      ¬ IsComplexRightEigenvalue (Node := Node) Aalpha
        (circleMap (1 : ℂ) innerRadius phi) := by
    exact hnoAnnulus (circleMap (1 : ℂ) innerRadius phi)
      (by rw [hinner_norm])
      (by
        rw [hinner_norm]
        exact le_of_lt hradii)
  have hneq :
      circleMap (1 : ℂ) innerRadius phi ≠
        circleMap (1 : ℂ) outerRadius theta := by
    intro hsame
    have hnorm_eq : innerRadius = outerRadius := by
      rw [← hinner_norm, hsame, houter_norm]
    exact (ne_of_lt hradii) hnorm_eq
  exact
    complex_resolvent_inverse_product_entry_eq_div_difference
      (Node := Node) Aalpha
      (circleMap (1 : ℂ) outerRadius theta)
      (circleMap (1 : ℂ) innerRadius phi)
      houter_not hinner_not hneq i j

private theorem separated_inner_resolvent_cauchy_circleParameter_continuousOn
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deriv (circleMap (1 : ℂ) outerRadius) p.1 *
          (deriv (circleMap (1 : ℂ) innerRadius) p.2 *
            ((circleMap (1 : ℂ) innerRadius p.2 -
                circleMap (1 : ℂ) outerRadius p.1)⁻¹ *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) innerRadius p.2))⁻¹) i j)))
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
        Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  classical
  let rect : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (0 : ℝ) (2 * Real.pi)
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have hden_ne :
      ∀ p : ℝ × ℝ, p ∈ rect →
        circleMap (1 : ℂ) innerRadius p.2 -
            circleMap (1 : ℂ) outerRadius p.1 ≠ 0 := by
    intro p _hp hzero
    have hsame :
        circleMap (1 : ℂ) innerRadius p.2 =
          circleMap (1 : ℂ) outerRadius p.1 := sub_eq_zero.mp hzero
    have hinner_norm :
        ‖circleMap (1 : ℂ) innerRadius p.2 - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos p.2
    have houter_norm :
        ‖circleMap (1 : ℂ) outerRadius p.1 - (1 : ℂ)‖ =
          outerRadius :=
      fixed_circleMap_boundary_norm outerRadius houter_pos p.1
    have hnorm_eq : innerRadius = outerRadius := by
      rw [← hinner_norm, hsame, houter_norm]
    exact (ne_of_lt hradii) hnorm_eq
  have hsub :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          circleMap (1 : ℂ) innerRadius p.2 -
            circleMap (1 : ℂ) outerRadius p.1)
        rect := by
    fun_prop
  have hinv :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          (circleMap (1 : ℂ) innerRadius p.2 -
            circleMap (1 : ℂ) outerRadius p.1)⁻¹)
        rect := by
    intro p hp
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ =>
        circleMap (1 : ℂ) innerRadius q.2 -
          circleMap (1 : ℂ) outerRadius q.1)
      (continuousAt_inv₀ (hden_ne p hp)) (hsub p hp)
  have hinner_entry :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius p.2))⁻¹) i j)
        rect := by
    intro p hp
    have hz_norm :
        ‖circleMap (1 : ℂ) innerRadius p.2 - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos p.2
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius p.2)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) innerRadius p.2)
        (hnoAnnulus (circleMap (1 : ℂ) innerRadius p.2)
          (by rw [hz_norm])
          (by
            rw [hz_norm]
            exact le_of_lt hradii))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (circleMap (1 : ℂ) innerRadius p.2) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i j).continuousAt
    have hcircle_cont :
        ContinuousWithinAt
          (fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
          rect p := by
      exact (continuous_circleMap (1 : ℂ) innerRadius).continuousAt
        |>.comp_continuousWithinAt continuousWithinAt_snd
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
      hentry_cont hcircle_cont
  have hderivOuter :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) outerRadius) p.1)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) outerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) outerRadius
    simpa using (hderivTheta.comp continuous_fst).continuousOn
  have hderivInner :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) innerRadius) p.2)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) innerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) innerRadius
    simpa using (hderivTheta.comp continuous_snd).continuousOn
  have hkernel :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          (circleMap (1 : ℂ) innerRadius p.2 -
              circleMap (1 : ℂ) outerRadius p.1)⁻¹ *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) innerRadius p.2))⁻¹) i j)
        rect :=
    hinv.mul hinner_entry
  simpa [rect] using hderivOuter.mul (hderivInner.mul hkernel)

private theorem separated_inner_resolvent_cauchy_outer_residue_integral_eq_neg
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (i j : Node) :
    (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                ((circleMap (1 : ℂ) innerRadius phi -
                    circleMap (1 : ℂ) outerRadius theta)⁻¹ *
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j)))) =
      -∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j := by
  classical
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let Rinner : ℝ → ℂ := fun phi =>
    ((complexResolventMatrix (Node := Node) Aalpha
      (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j
  have hpoint :
      ∀ phi : ℝ,
        c *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                ((circleMap (1 : ℂ) innerRadius phi -
                    circleMap (1 : ℂ) outerRadius theta)⁻¹ *
                  Rinner phi)) =
          -Rinner phi := by
    intro phi
    simpa [c, Rinner] using
      fixed_circleParameter_outer_inner_point_sub_mul_const_eq_neg
        (innerRadius := innerRadius) (outerRadius := outerRadius)
        (le_of_lt hinner_pos) hradii phi (Rinner phi)
  calc
    (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                ((circleMap (1 : ℂ) innerRadius phi -
                    circleMap (1 : ℂ) outerRadius theta)⁻¹ *
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j)))) =
        ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) innerRadius) phi * (-Rinner phi) := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro phi _hphi
          simpa [c, Rinner] using
            congrArg
              (fun x : ℂ =>
                deriv (circleMap (1 : ℂ) innerRadius) phi * x)
              (hpoint phi)
    _ =
        ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          -(deriv (circleMap (1 : ℂ) innerRadius) phi * Rinner phi) := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro phi _hphi
          ring
    _ =
      -∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j := by
          rw [MeasureTheory.integral_neg]

private theorem separated_outer_inner_resolvent_product_integral_eq_inner
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) outerRadius) theta *
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
              (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
                deriv (circleMap (1 : ℂ) innerRadius) phi *
                  (∑ k : Node,
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)))) =
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j) := by
  classical
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let I : Set ℝ := Set.Icc (0 : ℝ) (2 * Real.pi)
  have hI_compact : IsCompact I := by
    simpa [I] using isCompact_Icc
  have hI_meas : MeasurableSet I := hI_compact.measurableSet
  let Ro : ℝ → ℂ := fun theta =>
    ((complexResolventMatrix (Node := Node) Aalpha
      (circleMap (1 : ℂ) outerRadius theta))⁻¹) i j
  let Ri : ℝ → ℂ := fun phi =>
    ((complexResolventMatrix (Node := Node) Aalpha
      (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j
  let K : ℝ → ℝ → ℂ := fun theta phi =>
    (circleMap (1 : ℂ) innerRadius phi -
      circleMap (1 : ℂ) outerRadius theta)⁻¹
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have hden_ne :
      ∀ theta phi : ℝ,
        circleMap (1 : ℂ) innerRadius phi -
            circleMap (1 : ℂ) outerRadius theta ≠ 0 := by
    intro theta phi hzero
    have hsame :
        circleMap (1 : ℂ) innerRadius phi =
          circleMap (1 : ℂ) outerRadius theta := sub_eq_zero.mp hzero
    have hinner_norm :
        ‖circleMap (1 : ℂ) innerRadius phi - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos phi
    have houter_norm :
        ‖circleMap (1 : ℂ) outerRadius theta - (1 : ℂ)‖ =
          outerRadius :=
      fixed_circleMap_boundary_norm outerRadius houter_pos theta
    have hnorm_eq : innerRadius = outerRadius := by
      rw [← hinner_norm, hsame, houter_norm]
    exact (ne_of_lt hradii) hnorm_eq
  have hderivInner_cont :
      ContinuousOn
        (fun phi : ℝ => deriv (circleMap (1 : ℂ) innerRadius) phi) I := by
    have hderivTheta :
        Continuous
          (fun phi : ℝ => deriv (circleMap (1 : ℂ) innerRadius) phi) := by
      exact circleMap_deriv_continuous (1 : ℂ) innerRadius
    exact hderivTheta.continuousOn
  have hRi_cont : ContinuousOn Ri I := by
    intro phi _hphi
    have hz_norm :
        ‖circleMap (1 : ℂ) innerRadius phi - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos phi
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) innerRadius phi)
        (hnoAnnulus (circleMap (1 : ℂ) innerRadius phi)
          (by rw [hz_norm])
          (by
            rw [hz_norm]
            exact le_of_lt hradii))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (circleMap (1 : ℂ) innerRadius phi) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i j).continuousAt
    exact hentry_cont.comp_continuousWithinAt
      (continuous_circleMap (1 : ℂ) innerRadius).continuousAt.continuousWithinAt
  have hK_cont :
      ∀ theta : ℝ, ContinuousOn (fun phi : ℝ => K theta phi) I := by
    intro theta phi _hphi
    have hsub_cont :
        ContinuousWithinAt
          (fun x : ℝ =>
            circleMap (1 : ℂ) innerRadius x -
              circleMap (1 : ℂ) outerRadius theta) I phi :=
      ((continuous_circleMap (1 : ℂ) innerRadius).continuousAt.sub
        continuousAt_const).continuousWithinAt
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun x : ℝ =>
        circleMap (1 : ℂ) innerRadius x -
          circleMap (1 : ℂ) outerRadius theta)
      (continuousAt_inv₀ (hden_ne theta phi)) hsub_cont
  have hphi_integrable :
      ∀ theta : ℝ,
        Integrable
            (fun phi : ℝ =>
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ro theta)) (volume.restrict I) ∧
          Integrable
            (fun phi : ℝ =>
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi)) (volume.restrict I) := by
    intro theta
    have hcompact : IsCompact I := by
      simpa [I] using isCompact_Icc
    have hmeas : MeasurableSet I := hcompact.measurableSet
    have hfinite : volume I < ⊤ := hcompact.measure_lt_top
    have hcont_left :
        ContinuousOn
          (fun phi : ℝ =>
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (K theta phi * Ro theta)) I :=
      hderivInner_cont.mul ((hK_cont theta).mul continuousOn_const)
    have hcont_right :
        ContinuousOn
          (fun phi : ℝ =>
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (K theta phi * Ri phi)) I :=
      hderivInner_cont.mul ((hK_cont theta).mul hRi_cont)
    constructor
    · simpa [IntegrableOn] using
        hcont_left.integrableOn_of_subset_isCompact
          (μ := volume) (K := I) hcompact hmeas (fun x hx => hx)
          (ne_of_lt hfinite)
    · simpa [IntegrableOn] using
        hcont_right.integrableOn_of_subset_isCompact
          (μ := volume) (K := I) hcompact hmeas (fun x hx => hx)
          (ne_of_lt hfinite)
  have hprod :
      ∀ theta phi : ℝ,
        (∑ k : Node,
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j) =
            K theta phi * (Ro theta - Ri phi) := by
    intro theta phi
    simpa [K, Ro, Ri] using
      separated_resolvent_product_circleParameter_eq_div_difference
        (Node := Node) Aalpha hinner_pos hradii hnoAnnulus theta phi i j
  have hsplit :
      ∀ theta : ℝ,
        c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (∑ k : Node,
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)) =
          -(c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi))) := by
    intro theta
    have hzero :
        (∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            (K theta phi * Ro theta)) = 0 := by
      simpa [I, K, Ro] using
        fixed_circleParameter_inner_sub_outer_point_mul_const_eq_zero
          (innerRadius := innerRadius) (outerRadius := outerRadius)
          hinner_pos hradii theta (Ro theta)
    calc
      c *
          (∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (∑ k : Node,
                ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)) =
          c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * (Ro theta - Ri phi))) := by
            congr 1
            refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
            intro phi _hphi
            exact congrArg
              (fun x : ℂ =>
                deriv (circleMap (1 : ℂ) innerRadius) phi * x)
              (hprod theta phi)
      _ =
          c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ro theta) -
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi)) := by
            congr 1
            refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
            intro phi _hphi
            ring
      _ =
          c *
            ((∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ro theta)) -
             (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi))) := by
            rw [MeasureTheory.integral_sub]
            · exact (hphi_integrable theta).1
            · exact (hphi_integrable theta).2
      _ =
          -(c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi))) := by
            rw [hzero]
            ring
  have hswap :
      (∫ theta in I,
        deriv (circleMap (1 : ℂ) outerRadius) theta *
          (∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (K theta phi * Ri phi))) =
        ∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            (∫ theta in I,
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                (K theta phi * Ri phi)) := by
    simpa [I, K, Ri] using
      complex_circleParameter_Icc_integral_swap_of_continuousOn
        (center := (1 : ℂ)) (outerRadius := outerRadius)
        (innerRadius := innerRadius)
        (F := fun z w : ℂ =>
          (w - z)⁻¹ *
            ((complexResolventMatrix (Node := Node) Aalpha w)⁻¹) i j)
        (separated_inner_resolvent_cauchy_circleParameter_continuousOn
          (Node := Node) Aalpha hinner_pos hradii hnoAnnulus i j)
  have hresidue :
      (∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            (c *
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (K theta phi * Ri phi)))) =
        -∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi * Ri phi := by
    simpa [I, c, K, Ri] using
      separated_inner_resolvent_cauchy_outer_residue_integral_eq_neg
        (Node := Node) Aalpha hinner_pos hradii i j
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) outerRadius) theta *
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
              (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
                deriv (circleMap (1 : ℂ) innerRadius) phi *
                  (∑ k : Node,
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)))) =
        c *
          (∫ theta in I,
            deriv (circleMap (1 : ℂ) outerRadius) theta *
              (-(c *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (K theta phi * Ri phi))))) := by
          refine congrArg (fun x : ℂ => c * x) ?_
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro theta _htheta
          simpa [c, I] using
            congrArg
              (fun x : ℂ =>
                deriv (circleMap (1 : ℂ) outerRadius) theta * x)
              (hsplit theta)
    _ =
        -c *
          (∫ theta in I,
                    deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (c *
                      (∫ phi in I,
                        deriv (circleMap (1 : ℂ) innerRadius) phi *
                          (K theta phi * Ri phi)))) := by
          have hneg :
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (-(c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi))))) =
                -(∫ theta in I,
                  deriv (circleMap (1 : ℂ) outerRadius) theta *
                    (c *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi)))) := by
            calc
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (-(c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi))))) =
                  ∫ theta in I,
                    -(deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (c *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi)))) := by
                    refine MeasureTheory.setIntegral_congr_fun hI_meas ?_
                    intro theta _htheta
                    ring
              _ =
                  -(∫ theta in I,
                    deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (c *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi)))) := by
                    rw [MeasureTheory.integral_neg]
          rw [hneg]
          ring
    _ =
        -c *
          (c *
            (∫ theta in I,
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (K theta phi * Ri phi)))) := by
          have hconst :
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi)))) =
                c *
                  (∫ theta in I,
                    deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (∫ phi in I,
                        deriv (circleMap (1 : ℂ) innerRadius) phi *
                          (K theta phi * Ri phi))) := by
            calc
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi)))) =
                  ∫ theta in I,
                    c *
                      (deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi))) := by
                    refine MeasureTheory.setIntegral_congr_fun
                      isCompact_Icc.measurableSet ?_
                    intro theta _htheta
                    ring
              _ =
                  c *
                    (∫ theta in I,
                      deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi))) := by
                    simpa using
                      (MeasureTheory.integral_const_mul
                        (μ := volume.restrict I) c
                        (fun theta : ℝ =>
                          deriv (circleMap (1 : ℂ) outerRadius) theta *
                            (∫ phi in I,
                              deriv (circleMap (1 : ℂ) innerRadius) phi *
                                (K theta phi * Ri phi))))
          rw [hconst]
    _ =
        -c *
          (c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (∫ theta in I,
                  deriv (circleMap (1 : ℂ) outerRadius) theta *
                    (K theta phi * Ri phi)))) := by
          rw [hswap]
    _ =
        -c *
          (∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (c *
                (∫ theta in I,
                  deriv (circleMap (1 : ℂ) outerRadius) theta *
                    (K theta phi * Ri phi)))) := by
          have hconst :
              c *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (∫ theta in I,
                      deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (K theta phi * Ri phi))) =
                ∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (c *
                      (∫ theta in I,
                        deriv (circleMap (1 : ℂ) outerRadius) theta *
                          (K theta phi * Ri phi))) := by
            calc
              c *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (∫ theta in I,
                      deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (K theta phi * Ri phi))) =
                  ∫ phi in I,
                    c *
                      (deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (∫ theta in I,
                          deriv (circleMap (1 : ℂ) outerRadius) theta *
                            (K theta phi * Ri phi))) := by
                    exact
                      (MeasureTheory.integral_const_mul
                        (μ := volume.restrict I) c
                        (fun phi : ℝ =>
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (∫ theta in I,
                              deriv (circleMap (1 : ℂ) outerRadius) theta *
                                (K theta phi * Ri phi)))).symm
              _ =
                  ∫ phi in I,
                    deriv (circleMap (1 : ℂ) innerRadius) phi *
                      (c *
                        (∫ theta in I,
                          deriv (circleMap (1 : ℂ) outerRadius) theta *
                            (K theta phi * Ri phi))) := by
                    refine MeasureTheory.setIntegral_congr_fun hI_meas ?_
                    intro phi _hphi
                    ring
          rw [hconst]
    _ =
        -c *
          (-(∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi * Ri phi)) := by
          rw [hresidue]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j) := by
          simp [c, I, Ri]

private theorem complex_Icc_integral_neg_eq_of_periodic
    (T : ℝ) (hT_pos : 0 < T) (f : ℝ → ℂ)
    (hf : Function.Periodic f T) :
    (∫ theta in Set.Icc (0 : ℝ) T, f (-theta)) =
      ∫ theta in Set.Icc (0 : ℝ) T, f theta := by
  calc
    (∫ theta in Set.Icc (0 : ℝ) T, f (-theta)) =
        ∫ theta in (0 : ℝ)..T, f (-theta) := by
          exact complex_setIntegral_Icc_eq_intervalIntegral
            (0 : ℝ) T (fun theta => f (-theta)) (le_of_lt hT_pos)
    _ = ∫ theta in -T..-(0 : ℝ), f theta := by
          exact intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := T)
    _ = ∫ theta in (0 : ℝ)..T, f theta := by
          simpa using (hf.intervalIntegral_add_eq (-T) (0 : ℝ))
    _ = ∫ theta in Set.Icc (0 : ℝ) T, f theta := by
          exact (complex_setIntegral_Icc_eq_intervalIntegral
            (0 : ℝ) T f (le_of_lt hT_pos)).symm

private theorem fixed_circle_scaled_resolvent_integrand_periodic
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ) (i j : Node) :
    Function.Periodic
      (fun theta : ℝ =>
        deriv (circleMap (1 : ℂ) baseRadius) theta *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j)
      (2 * Real.pi) := by
  intro theta
  have hcircle :
      circleMap (1 : ℂ) baseRadius (theta + 2 * Real.pi) =
        circleMap (1 : ℂ) baseRadius theta := by
    simpa using
      (periodic_circleMap (1 : ℂ) baseRadius theta)
  have hderiv :
      deriv (circleMap (1 : ℂ) baseRadius) (theta + 2 * Real.pi) =
        deriv (circleMap (1 : ℂ) baseRadius) theta := by
    calc
      deriv (circleMap (1 : ℂ) baseRadius) (theta + 2 * Real.pi) =
          circleMap (0 : ℂ) baseRadius (theta + 2 * Real.pi) * Complex.I :=
        deriv_circleMap (1 : ℂ) baseRadius (theta + 2 * Real.pi)
      _ = circleMap (0 : ℂ) baseRadius theta * Complex.I := by
        rw [show circleMap (0 : ℂ) baseRadius (theta + 2 * Real.pi) =
            circleMap (0 : ℂ) baseRadius theta by
              simpa using (periodic_circleMap (0 : ℂ) baseRadius theta)]
      _ = deriv (circleMap (1 : ℂ) baseRadius) theta :=
        (deriv_circleMap (1 : ℂ) baseRadius theta).symm
  dsimp
  rw [hcircle, hderiv]

private theorem fixed_circle_scaled_resolvent_neg_Icc_integral_eq_self
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ) (i j : Node) :
    (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j) =
      ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) theta *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j := by
  let f : ℝ → ℂ := fun theta =>
    deriv (circleMap (1 : ℂ) baseRadius) theta *
      ((complexResolventMatrix (Node := Node) Aalpha
        (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j
  have hf : Function.Periodic f (2 * Real.pi) := by
    simpa [f] using
      fixed_circle_scaled_resolvent_integrand_periodic
        (Node := Node) Aalpha baseRadius i j
  simpa [f] using
    complex_Icc_integral_neg_eq_of_periodic
      (2 * Real.pi) Real.two_pi_pos f hf

private theorem complexRieszProjectionOnCircle_entry_im_zero_of_scaled_conj_and_neg_integral
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ) (i j : Node)
    (hscaled :
      letI : DecidableEq Node := Classical.decEq Node
      ∀ theta : ℝ,
        conj
            (deriv (circleMap (1 : ℂ) baseRadius) theta *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j)
    (hnegIntegral :
      letI : DecidableEq Node := Classical.decEq Node
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j) =
      ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) theta *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) :
    ((complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius i j).im = 0) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let f : ℝ → ℂ := fun theta =>
    deriv (circleMap (1 : ℂ) baseRadius) theta *
      ((complexResolventMatrix (Node := Node) Aalpha
        (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j
  let fneg : ℝ → ℂ := fun theta =>
    deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
      ((complexResolventMatrix (Node := Node) Aalpha
        (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j
  have hentry :
      complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j =
        c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta := by
    simpa only [c, f, smul_eq_mul] using
      (complexRieszProjectionOnCircle_entry_eq_Icc_integral
        (Node := Node) Aalpha (1 : ℂ) baseRadius i j)
  have hconj_c : conj c = -c := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    have hpi : conj (Real.pi : ℂ) = (Real.pi : ℂ) := by simp
    calc
      conj c =
          (conj ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))⁻¹ := by
            simp [c]
      _ = (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I))⁻¹ := by
            congr 1
            rw [map_mul, map_mul, htwo, hpi]
            simp
      _ = -c := by
            simp [c]
  have hconj_integral :
      conj (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) =
        -∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta := by
    calc
      conj (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) =
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), conj (f theta) := by
            exact complex_Icc_integral_conj (0 : ℝ) (2 * Real.pi) f
      _ = ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), -fneg theta := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with theta
            simpa [f, fneg] using hscaled theta
      _ = -∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta := by
            rw [MeasureTheory.integral_neg]
  have hconj_entry :
      conj (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j) =
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j := by
    calc
      conj (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j) =
          conj (c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) := by
            rw [hentry]
      _ =
          conj c *
            conj (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) := by
            rw [map_mul]
      _ =
          (-c) *
            (-(∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta)) := by
            rw [hconj_c, hconj_integral]
      _ =
          c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta := by
            ring
      _ =
          c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta := by
            rw [hnegIntegral]
      _ =
          complexRieszProjectionOnCircle (Node := Node)
            Aalpha (1 : ℂ) baseRadius i j := hentry.symm
  exact Complex.conj_eq_iff_im.mp hconj_entry

private theorem fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    CircleIntegrable
      (fun z : ℂ =>
        ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
      (1 : ℂ) baseRadius := by
  classical
  have hcont_sphere :
      ContinuousOn
        (fun z : ℂ =>
          ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
        (Metric.sphere (1 : ℂ) baseRadius) := by
    intro z hz
    have hz_norm : ‖z - (1 : ℂ)‖ = baseRadius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hdet_z :
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
        (hnoBoundary z hz_norm)
    exact
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet_z i j).continuousAt.continuousWithinAt
  exact hcont_sphere.circleIntegrable (le_of_lt hbaseRadius_pos)

private theorem complexRieszProjectionOnCircle_mul_self_entry_eq_single_contour_right
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hresolvent_entry_circleIntegrable :
      letI : DecidableEq Node := Classical.decEq Node;
      ∀ i j : Node,
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (1 : ℂ) baseRadius)
    (i j : Node) :
    complexMatrixMul (Node := Node)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) i j =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (letI : DecidableEq Node := Classical.decEq Node;
            (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
              complexRieszProjectionOnCircle (Node := Node)
                Aalpha (1 : ℂ) baseRadius) i j)) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let P : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius
  let R : ℂ → ComplexNodeMatrix Node :=
    fun z : ℂ => (complexResolventMatrix (Node := Node) Aalpha z)⁻¹
  have hterm_integrable :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable (fun z : ℂ => R z i k * P k j)
          (1 : ℂ) baseRadius := by
    intro k _hk
    have hk :
        CircleIntegrable (fun z : ℂ => P k j * R z i k)
          (1 : ℂ) baseRadius := by
      simpa [R, Pi.smul_apply, smul_eq_mul] using
        (hresolvent_entry_circleIntegrable i k).const_smul (a := P k j)
    simpa [mul_comm] using hk
  calc
    complexMatrixMul (Node := Node) P P i j =
        ∑ k : Node, P i k * P k j := by
          simp [complexMatrixMul, Matrix.mul_apply, P]
    _ = ∑ k : Node, (c *
          (∮ z in C((1 : ℂ), baseRadius), R z i k)) * P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          have hPik :
              P i k =
                c * (∮ z in C((1 : ℂ), baseRadius), R z i k) := by
            dsimp [P, c, R]
            rw [complexRieszProjectionOnCircle]
          rw [hPik]
    _ = c *
        ∑ k : Node,
          (∮ z in C((1 : ℂ), baseRadius), R z i k) * P k j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ = c *
        ∑ k : Node,
          (∮ z in C((1 : ℂ), baseRadius), R z i k * P k j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          simpa [smul_eq_mul] using
            (circleIntegral.integral_smul_const
              (fun z : ℂ => R z i k) (P k j) (1 : ℂ) baseRadius).symm
    _ = c *
        (∮ z in C((1 : ℂ), baseRadius),
          ∑ k : Node, R z i k * P k j) := by
          rw [circleIntegral.integral_fun_sum hterm_integrable]
    _ = c *
        (∮ z in C((1 : ℂ), baseRadius), (R z * P) i j) := by
          simp [Matrix.mul_apply]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
            complexRieszProjectionOnCircle (Node := Node)
              Aalpha (1 : ℂ) baseRadius) i j) := by
          simp [c, P, R]

private theorem complexResolvent_inv_mul_complexRieszProjectionOnCircle_entry_eq_inner_contour
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hresolvent_entry_circleIntegrable :
      letI : DecidableEq Node := Classical.decEq Node;
      ∀ i j : Node,
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (1 : ℂ) baseRadius)
    (z : ℂ) (i j : Node) :
    (letI : DecidableEq Node := Classical.decEq Node;
      (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) i j) =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ w in C((1 : ℂ), baseRadius),
          (letI : DecidableEq Node := Classical.decEq Node;
            ∑ k : Node,
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
                ((complexResolventMatrix (Node := Node) Aalpha w)⁻¹) k j)) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let P : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius
  let R : ℂ → ComplexNodeMatrix Node :=
    fun z : ℂ => (complexResolventMatrix (Node := Node) Aalpha z)⁻¹
  have hterm_integrable :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable (fun w : ℂ => R z i k * R w k j)
          (1 : ℂ) baseRadius := by
    intro k _hk
    simpa [R, Pi.smul_apply, smul_eq_mul] using
      (hresolvent_entry_circleIntegrable k j).const_smul
        (a := R z i k)
  calc
    (R z * P) i j =
        ∑ k : Node, R z i k * P k j := by
          simp [Matrix.mul_apply]
    _ = ∑ k : Node,
          R z i k *
            (c * (∮ w in C((1 : ℂ), baseRadius), R w k j)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          have hPkj :
              P k j =
                c * (∮ w in C((1 : ℂ), baseRadius), R w k j) := by
            dsimp [P, c, R]
            rw [complexRieszProjectionOnCircle]
          rw [hPkj]
    _ = c *
        ∑ k : Node,
          R z i k * (∮ w in C((1 : ℂ), baseRadius), R w k j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ = c *
        ∑ k : Node,
          (∮ w in C((1 : ℂ), baseRadius), R z i k * R w k j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          rw [circleIntegral.integral_const_mul]
    _ = c *
        (∮ w in C((1 : ℂ), baseRadius),
          ∑ k : Node, R z i k * R w k j) := by
          rw [circleIntegral.integral_fun_sum hterm_integrable]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ w in C((1 : ℂ), baseRadius),
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              ((complexResolventMatrix (Node := Node) Aalpha w)⁻¹) k j) := by
          simp [c, R]

private theorem complexResolvent_inv_mul_fixed_matrix_entry_circleIntegral_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (P : ComplexNodeMatrix Node)
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    (∮ z in C((1 : ℂ), outerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j) =
      ∮ z in C((1 : ℂ), innerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j := by
  classical
  have houter_pos : 0 < outerRadius := lt_of_lt_of_le hinner_pos hradii
  have houter_boundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = outerRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hz
    exact hnoAnnulus z (by rw [hz]; exact hradii) (by rw [hz])
  have hinner_boundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = innerRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hz
    exact hnoAnnulus z (by rw [hz]) (by rw [hz]; exact hradii)
  have houter_term :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j)
          (1 : ℂ) outerRadius := by
    intro k _hk
    have hk :
        CircleIntegrable
          (fun z : ℂ =>
            P k j *
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
          (1 : ℂ) outerRadius := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
          (Node := Node) Aalpha outerRadius houter_pos houter_boundary i k).const_smul
          (a := P k j)
    simpa [mul_comm] using hk
  have hinner_term :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j)
          (1 : ℂ) innerRadius := by
    intro k _hk
    have hk :
        CircleIntegrable
          (fun z : ℂ =>
            P k j *
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
          (1 : ℂ) innerRadius := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
          (Node := Node) Aalpha innerRadius hinner_pos hinner_boundary i k).const_smul
          (a := P k j)
    simpa [mul_comm] using hk
  calc
    (∮ z in C((1 : ℂ), outerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j) =
        ∮ z in C((1 : ℂ), outerRadius),
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          refine circleIntegral.integral_congr (le_of_lt houter_pos) ?_
          intro z _hz
          simp [Matrix.mul_apply]
    _ =
        ∑ k : Node,
          ∮ z in C((1 : ℂ), outerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          rw [circleIntegral.integral_fun_sum houter_term]
    _ =
        ∑ k : Node,
          (∮ z in C((1 : ℂ), outerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k) *
              P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          simpa [smul_eq_mul] using
            (circleIntegral.integral_smul_const
              (fun z : ℂ =>
                ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
              (P k j) (1 : ℂ) outerRadius)
    _ =
        ∑ k : Node,
          (∮ z in C((1 : ℂ), innerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k) *
              P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
            (Node := Node) Aalpha hinner_pos hradii hnoAnnulus i k]
    _ =
        ∑ k : Node,
          ∮ z in C((1 : ℂ), innerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          simpa [smul_eq_mul] using
            (circleIntegral.integral_smul_const
              (fun z : ℂ =>
                ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
              (P k j) (1 : ℂ) innerRadius).symm
    _ =
        ∮ z in C((1 : ℂ), innerRadius),
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          rw [circleIntegral.integral_fun_sum hinner_term]
    _ =
      ∮ z in C((1 : ℂ), innerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j := by
          refine circleIntegral.integral_congr (le_of_lt hinner_pos) ?_
          intro z _hz
          simp [Matrix.mul_apply]

set_option maxHeartbeats 800000 in

private theorem complexRieszProjectionOnCircle_resolvent_action_eq_self_of_no_boundary
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    letI : DecidableEq Node := Classical.decEq Node
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
            complexRieszProjectionOnCircle (Node := Node)
              Aalpha (1 : ℂ) baseRadius) i j) =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let Pbase : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius
  let R : ℂ → ComplexNodeMatrix Node :=
    fun z : ℂ => (complexResolventMatrix (Node := Node) Aalpha z)⁻¹
  rcases exists_no_eigen_annulus_around_fixed_circle
      (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary with
    ⟨innerRadius, outerRadius, hinner_pos, hinner_lt_base,
      hbase_lt_outer, hnoAnnulus⟩
  let Pinner : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) innerRadius
  have hinner_lt_outer : innerRadius < outerRadius :=
    lt_trans hinner_lt_base hbase_lt_outer
  have houter_pos : 0 < outerRadius :=
    lt_trans hbaseRadius_pos hbase_lt_outer
  have hnoInnerBase :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ baseRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hl hu
    exact hnoAnnulus z hl (le_trans hu (le_of_lt hbase_lt_outer))
  have hnoBaseOuter :
      ∀ z : ℂ, baseRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hl hu
    exact hnoAnnulus z (le_trans (le_of_lt hinner_lt_base) hl) hu
  have hinner_boundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = innerRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hz
    exact hnoAnnulus z (by rw [hz]) (by
      rw [hz]
      exact le_of_lt hinner_lt_outer)
  have hPbase_inner : Pbase = Pinner := by
    dsimp [Pbase, Pinner]
    exact
      complexRieszProjectionOnCircle_eq_of_no_eigen_annulus
        (Node := Node) Aalpha hinner_pos (le_of_lt hinner_lt_base)
        hnoInnerBase
  have haction_outer_base :
      (∮ z in C((1 : ℂ), outerRadius), (R z * Pbase) i j) =
        ∮ z in C((1 : ℂ), baseRadius), (R z * Pbase) i j := by
    simpa [R, Pbase] using
      complexResolvent_inv_mul_fixed_matrix_entry_circleIntegral_eq_of_no_eigen_annulus
        (Node := Node) Aalpha Pbase hbaseRadius_pos
        (le_of_lt hbase_lt_outer) hnoBaseOuter i j
  have hresolvent_inner_circleIntegrable :
      ∀ a b : Node,
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) a b)
          (1 : ℂ) innerRadius := by
    intro a b
    exact fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
      (Node := Node) Aalpha innerRadius hinner_pos hinner_boundary a b
  have hinner_expand :
      ∀ z : ℂ,
        (R z * Pinner) i j =
          c *
            (∮ w in C((1 : ℂ), innerRadius),
              ∑ k : Node, R z i k * R w k j) := by
    intro z
    simpa [c, R, Pinner] using
      complexResolvent_inv_mul_complexRieszProjectionOnCircle_entry_eq_inner_contour
        (Node := Node) Aalpha innerRadius hresolvent_inner_circleIntegrable
        z i j
  have houter_expand :
      (∮ z in C((1 : ℂ), outerRadius), (R z * Pinner) i j) =
        ∮ z in C((1 : ℂ), outerRadius),
          c *
            (∮ w in C((1 : ℂ), innerRadius),
              ∑ k : Node, R z i k * R w k j) := by
    refine circleIntegral.integral_congr (le_of_lt houter_pos) ?_
    intro z _hz
    exact hinner_expand z
  have hseparated_circle :
      c *
          (∮ z in C((1 : ℂ), outerRadius),
            c *
              (∮ w in C((1 : ℂ), innerRadius),
                ∑ k : Node, R z i k * R w k j)) =
        c *
          (∮ w in C((1 : ℂ), innerRadius), R w i j) := by
    have hinner_parameterized (theta : ℝ) :
        (∮ w in C((1 : ℂ), innerRadius),
            ∑ k : Node,
              R (circleMap (1 : ℂ) outerRadius theta) i k * R w k j) =
          ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (∑ k : Node,
                R (circleMap (1 : ℂ) outerRadius theta) i k *
                  R (circleMap (1 : ℂ) innerRadius phi) k j) := by
      exact circleIntegral_eq_Icc_integral_deriv_mul
        (fun w : ℂ =>
          ∑ k : Node,
            R (circleMap (1 : ℂ) outerRadius theta) i k * R w k j)
        (1 : ℂ) innerRadius
    rw [circleIntegral_eq_Icc_integral_deriv_mul,
      circleIntegral_eq_Icc_integral_deriv_mul]
    simp_rw [hinner_parameterized]
    simpa only [c, R] using
      separated_outer_inner_resolvent_product_integral_eq_inner
        (Node := Node) Aalpha hinner_pos hinner_lt_outer hnoAnnulus i j
  have hresolvent_base_inner :
      (∮ z in C((1 : ℂ), baseRadius), R z i j) =
        ∮ z in C((1 : ℂ), innerRadius), R z i j := by
    simpa [R] using
      complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
        (Node := Node) Aalpha hinner_pos (le_of_lt hinner_lt_base)
        hnoInnerBase i j
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
            complexRieszProjectionOnCircle (Node := Node)
              Aalpha (1 : ℂ) baseRadius) i j) =
        c * (∮ z in C((1 : ℂ), baseRadius), (R z * Pbase) i j) := by
          simp [c, R, Pbase]
    _ = c * (∮ z in C((1 : ℂ), outerRadius), (R z * Pbase) i j) := by
          rw [← haction_outer_base]
    _ = c * (∮ z in C((1 : ℂ), outerRadius), (R z * Pinner) i j) := by
          rw [hPbase_inner]
    _ =
        c *
          (∮ z in C((1 : ℂ), outerRadius),
            c *
              (∮ w in C((1 : ℂ), innerRadius),
                ∑ k : Node, R z i k * R w k j)) := by
          rw [houter_expand]
    _ = c * (∮ w in C((1 : ℂ), innerRadius), R w i j) :=
          hseparated_circle
    _ = c * (∮ z in C((1 : ℂ), baseRadius), R z i j) := by
          rw [hresolvent_base_inner]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) := by
          simp [c, R]

private theorem complexConjMatrix_inv_of_det_ne_zero [DecidableEq Node]
    (M : ComplexNodeMatrix Node) (hdet : Matrix.det M ≠ 0) :
    complexConjMatrix (Node := Node) M⁻¹ =
      (complexConjMatrix (Node := Node) M)⁻¹ := by
  classical
  symm
  refine Matrix.inv_eq_right_inv ?_
  calc
    complexConjMatrix (Node := Node) M *
        complexConjMatrix (Node := Node) M⁻¹ =
        complexConjMatrix (Node := Node) (M * M⁻¹) := by
          rw [complexConjMatrix_mul]
    _ = complexConjMatrix (Node := Node) (1 : ComplexNodeMatrix Node) := by
          rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet)]
    _ = 1 := complexConjMatrix_one (Node := Node)

private theorem complexResolvent_inv_conj_entry_of_not_eigen
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A0 z) (i j : Node) :
    conj
        (((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j) =
      ((complexResolventMatrix (Node := Node) A0 (conj z))⁻¹) i j := by
  classical
  have hdet : Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 :=
    complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 z hnot
  have hmatrix :=
    complexConjMatrix_inv_of_det_ne_zero (Node := Node)
      (complexResolventMatrix (Node := Node) A0 z) hdet
  have hentry := congrArg (fun M : ComplexNodeMatrix Node => M i j) hmatrix
  simpa [complexConjMatrix, complexConjMatrix_resolvent] using hentry

private theorem complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    complexMatrixMul (Node := Node)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) =
      complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) baseRadius ∧
      ∀ i j : Node,
        ((complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) baseRadius i j).im = 0) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  have hboundary_det :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 := by
    intro z hz
    exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
      (hnoBoundary z hz)
  have hresolvent_identity :
      ∀ z w : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ‖w - (1 : ℂ)‖ = baseRadius →
          (complexResolventMatrix (Node := Node) Aalpha z)⁻¹ -
              (complexResolventMatrix (Node := Node) Aalpha w)⁻¹ =
            (w - z) •
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹ *
                (complexResolventMatrix (Node := Node) Aalpha w)⁻¹) := by
    intro z w hz hw
    exact complex_resolvent_inverse_identity_two_points (Node := Node)
      Aalpha z w (hnoBoundary z hz) (hnoBoundary w hw)
  have hsimple_pole :
      ∀ c : ℂ,
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹ * c) = c := by
    intro c
    exact fixed_circle_simple_pole_entry_integral_eq baseRadius
      hbaseRadius_pos c
  have hboundary_conj :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ‖conj z - (1 : ℂ)‖ = baseRadius := by
    intro z hz
    exact fixed_unit_circle_conj_boundary baseRadius hz
  have hresolvent_conj_entry :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ∀ i j : Node,
          conj
              (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) =
            ((complexResolventMatrix (Node := Node) Aalpha (conj z))⁻¹) i j := by
    intro z hz i j
    exact complexResolvent_inv_conj_entry_of_not_eigen (Node := Node)
      Aalpha z (hnoBoundary z hz) i j
  have hcircleMap_boundary :
      ∀ theta : ℝ,
        ‖circleMap (1 : ℂ) baseRadius theta - (1 : ℂ)‖ =
          baseRadius := by
    intro theta
    exact fixed_circleMap_boundary_norm baseRadius hbaseRadius_pos theta
  have hcircleMap_conj :
      ∀ theta : ℝ,
        conj (circleMap (1 : ℂ) baseRadius theta) =
          circleMap (1 : ℂ) baseRadius (-theta) := by
    intro theta
    exact fixed_circleMap_conj baseRadius theta
  have hcircleMap_deriv_conj :
      ∀ theta : ℝ,
        conj (deriv (circleMap (1 : ℂ) baseRadius) theta) =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) := by
    intro theta
    exact fixed_circleMap_deriv_conj baseRadius theta
  have hscaled_resolvent_conj_entry :
      ∀ theta : ℝ, ∀ i j : Node,
        conj
            (deriv (circleMap (1 : ℂ) baseRadius) theta *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j := by
    intro theta i j
    have hres :=
      hresolvent_conj_entry (circleMap (1 : ℂ) baseRadius theta)
        (hcircleMap_boundary theta) i j
    rw [hcircleMap_conj theta] at hres
    calc
      conj
          (deriv (circleMap (1 : ℂ) baseRadius) theta *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) =
          conj (deriv (circleMap (1 : ℂ) baseRadius) theta) *
            conj
              (((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) := by
            rw [map_mul]
      _ =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j := by
            rw [hcircleMap_deriv_conj theta, hres]
  /-
  Remaining complex contour primitive.  The first projection component is the
  standard double-contour calculation: expand the matrix product of the two
  circle integrals, use `hresolvent_identity` entrywise, and reduce the two
  resulting simple-pole circle integrals with `hsimple_pole` to the original
  contour integral.
  The second component is the conjugation-symmetry descent for a real matrix
  on the real-centered circle; the algebraic inverse-resolvent conjugation and
  boundary invariance have now been sharpened to the parameter-level scaled
  integrand identity `hscaled_resolvent_conj_entry`.  Both are strictly below the real
  `fixedCircleRieszProjection` statement and are the contour/Riesz calculus
  still missing from local Mathlib/SOptLib infrastructure.
  -/
  refine ⟨?_, ?_⟩
  · /-
    Exact remaining complex contour primitive: expand the matrix product of
    the two contour integrals, exchange the finite node sum with the two
    circle integrals, apply `hresolvent_identity` entrywise, and reduce the
    two simple-pole terms with `hsimple_pole`.
    -/
    have hresolvent_entry_circleIntegrable :
        ∀ i j : Node,
          CircleIntegrable
            (fun z : ℂ =>
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
            (1 : ℂ) baseRadius := by
      intro i j
      exact fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
        (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary i j
    ext i j
    rw [complexRieszProjectionOnCircle_mul_self_entry_eq_single_contour_right
      (Node := Node) Aalpha baseRadius hresolvent_entry_circleIntegrable i j]
    exact
      complexRieszProjectionOnCircle_resolvent_action_eq_self_of_no_boundary
        (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary i j
  · intro i j
    exact
      complexRieszProjectionOnCircle_entry_im_zero_of_scaled_conj_and_neg_integral
        (Node := Node) Aalpha baseRadius i j
        (by
          intro theta
          exact hscaled_resolvent_conj_entry theta i j)
        (fixed_circle_scaled_resolvent_neg_Icc_integral_eq_self
          (Node := Node) Aalpha baseRadius i j)

private theorem rieszProjectionOnCircle_idempotent_and_map_conj_eq_self_one
    [DecidableEq Node]
    (A : NodeMatrix Node) (radius : ℝ) (hradius : 0 < radius)
    (hboundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = radius →
        Matrix.det (fun i j : Node =>
          z * (1 : Matrix Node Node ℂ) i j - (A i j : ℂ)) ≠ 0) :
    let P := complexRieszProjectionOnCircle (Node := Node) A (1 : ℂ) radius
    complexMatrixMul (Node := Node) P P = P ∧
      P.map (starRingEnd ℂ) = P := by
  classical
  have hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) A z := by
    intro z hz
    apply not_isComplexRightEigenvalue_of_complexResolvent_det_ne_zero
      (Node := Node) A z
    have hresolvent :
        complexResolventMatrix (Node := Node) A z =
          fun i j : Node =>
            z * (1 : Matrix Node Node ℂ) i j - (A i j : ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [complexResolventMatrix, complexMatrixSub,
          complexIdentityMatrix, complexOfRealMatrix]
      · simp [complexResolventMatrix, complexMatrixSub,
          complexIdentityMatrix, complexOfRealMatrix, hij]
    rw [hresolvent]
    exact hboundary z hz
  obtain ⟨hidem, hreal⟩ :=
    complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary
      (Node := Node) A radius hradius hnoBoundary
  refine ⟨hidem, ?_⟩
  ext i j
  apply Complex.ext
  · simp
  · simp [hreal i j]

end RieszProjectionOnCircleProof

/-- Entrywise conjugation fixes a complex matrix exactly when all of its
entries have zero imaginary part.

Layer: Model | Gap: Level 0 (complex-matrix conjugation fixed-point characterization)
Proof: apply matrix extensionality and the scalar equivalence `Complex.conj_eq_iff_im` entrywise.
Source: Mathlib complex conjugation and matrix extensionality
Used in: descending complex spectral projections of real network matrices to real-entry projection statements
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem map_conj_eq_self_iff_forall_im_eq_zero
    {ι κ : Type*} (P : Matrix ι κ ℂ) :
    P.map (starRingEnd ℂ) = P ↔ ∀ i j, (P i j).im = 0 := by
  constructor
  · intro h i j
    apply Complex.conj_eq_iff_im.mp
    have hij := congrArg (fun M : Matrix ι κ ℂ => M i j) h
    simpa only [Matrix.map_apply] using hij
  · intro h
    ext i j
    simpa only [Matrix.map_apply, Complex.conj_eq_iff_im] using h i j

/-- The circle Riesz projection of a finite real matrix is idempotent and fixed
by entrywise complex conjugation when the circle is disjoint from its spectrum.

The contour center is any real scalar. The determinant hypothesis states
directly that every boundary point belongs to the resolvent set.

Layer: Model | Gap: Level 2 (finite-matrix circle Riesz projection idempotence and real descent)
Proof: translate the real-centered contour to the unit-centered contour, apply the resolvent-identity double-contour calculation, and use conjugation symmetry of the real resolvent.
Source: finite-dimensional holomorphic functional calculus, Mathlib complex circle integrals, and Mathlib nonsingular matrix inverses
Used in: fixed-contour spectral splittings for finite consensus and push-pull transition matrices, where the isolated dominant spectral cluster must yield a real idempotent projection
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem rieszProjectionOnCircle_idempotent_and_map_conj_eq_self_of_spectrum_disjoint
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (center radius : ℝ)
    (hradius : 0 < radius)
    (hspectrum :
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
        Matrix.det (fun i j : ι =>
          z * (1 : Matrix ι ι ℂ) i j - (A i j : ℂ)) ≠ 0) :
    let Aℂ : Matrix ι ι ℂ := fun i j => (A i j : ℂ)
    let P := rieszProjectionOnCircle Aℂ (center : ℂ) radius
    P * P = P ∧ P.map (starRingEnd ℂ) = P := by
  classical
  let shift : ℝ := 1 - center
  let B : Matrix ι ι ℝ := fun i j => A i j + shift * (1 : Matrix ι ι ℝ) i j
  have hshift (z : ℂ) :
      (fun i j : ι => z * (1 : Matrix ι ι ℂ) i j - (B i j : ℂ)) =
        (fun i j : ι =>
          (z - (shift : ℂ)) * (1 : Matrix ι ι ℂ) i j - (A i j : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [B, shift]
      ring
    · simp [B, shift, hij]
  have hB :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = radius →
        Matrix.det (fun i j : ι =>
          z * (1 : Matrix ι ι ℂ) i j - (B i j : ℂ)) ≠ 0 := by
    intro z hz
    rw [hshift z]
    apply hspectrum (z - (shift : ℂ))
    convert hz using 1
    congr 1
    push_cast [shift]
    ring
  obtain ⟨hidem, hconj⟩ :=
    RieszProjectionOnCircleProof.rieszProjectionOnCircle_idempotent_and_map_conj_eq_self_one
      (Node := ι) B radius hradius hB
  let Aℂ : Matrix ι ι ℂ := fun i j => (A i j : ℂ)
  let L := RieszProjectionOnCircleProof.complexRieszProjectionOnCircle
    (Node := ι) B (1 : ℂ) radius
  let P := rieszProjectionOnCircle Aℂ (center : ℂ) radius
  have hcircle (theta : ℝ) :
      circleMap (1 : ℂ) radius theta - (shift : ℂ) =
        circleMap (center : ℂ) radius theta := by
    simp only [circleMap]
    push_cast [shift]
    ring
  have hresolvent (theta : ℝ) :
      RieszProjectionOnCircleProof.complexResolventMatrix
          (Node := ι) B (circleMap (1 : ℂ) radius theta) =
        (fun i j : ι =>
          circleMap (center : ℂ) radius theta *
              (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) i j -
            Aℂ i j) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [RieszProjectionOnCircleProof.complexResolventMatrix,
        RieszProjectionOnCircleProof.complexMatrixSub,
        RieszProjectionOnCircleProof.complexIdentityMatrix,
        RieszProjectionOnCircleProof.complexOfRealMatrix, B, Aℂ]
      rw [← hcircle theta]
      ring
    · simp [RieszProjectionOnCircleProof.complexResolventMatrix,
        RieszProjectionOnCircleProof.complexMatrixSub,
        RieszProjectionOnCircleProof.complexIdentityMatrix,
        RieszProjectionOnCircleProof.complexOfRealMatrix, B, Aℂ, hij]
  have hprojection : L = P := by
    ext i j
    simp only [L, P,
      RieszProjectionOnCircleProof.complexRieszProjectionOnCircle,
      rieszProjectionOnCircle]
    congr 1
    rw [circleIntegral_def_Icc, circleIntegral_def_Icc]
    apply integral_congr_ae
    filter_upwards [] with theta
    rw [deriv_circleMap, deriv_circleMap, hresolvent theta]
  change L * L = L at hidem
  change L.map (starRingEnd ℂ) = L at hconj
  change P * P = P ∧ P.map (starRingEnd ℂ) = P
  rw [← hprojection]
  exact ⟨hidem, hconj⟩

end Matrix

/-! Phase 4 batch 3: `Matrix_smulVec`. -/

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: rectangular matrix action on a module-valued vector; orig was `leftMul`.
-- generality used: arbitrary row and column types, a finite column type, and an arbitrary scalar action on an additive commutative monoid; no scalar addition or multiplication, module laws, norm, topology, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: consensus, push-sum, gradient-tracking, and decentralized-optimization proofs change the node types, scalar type, state type, scalar action, and mixing matrix while reusing the same coordinate-level matrix action.
-- counterargument checked: Mathlib's `Matrix.Module.matrixModule` has the same formula for square matrices over a ring acting on an additive group, but it does not cover rectangular matrices or a bare scalar action on an additive commutative monoid; the generalized operation therefore is not a pure alias of that action or of scalar-valued `Matrix.mulVec`.
-- coverage search: `lean_search_symbols` queries "matrix acts on module valued vector finite sum scalar multiplication", "Matrix smulVec module vector coordinate sum", and "mulVecLin matrix module scalar multiplication", plus LeanSearch query "a matrix with scalar entries acts on a vector valued in a module by summing scalar multiples", found `Matrix.Module.smul_apply`, `Matrix.Module.smul_def`, and scalar-valued `Matrix.mulVec`; all are partial because they require a square matrix or a scalar-valued vector.
-- minimal hypotheses: `[Fintype n]` indexes the finite contraction, `[AddCommMonoid E]` supplies the finite sum, and `[SMul R E]` supplies exactly the scalar multiplication appearing in each summand; interaction lemmas below add only the zero or zero-and-one action laws they use.

namespace Matrix

/-- A rectangular scalar matrix acts on a module-valued vector by taking the
finite scalar-weighted sum along each row.

Layer: Glue | Concept: rectangular matrix action on a module-valued vector
Proof: (definitional construction; each output coordinate is the finite sum of the row entries acting by scalar multiplication on the input coordinates)
Source: Mathlib finite matrices, finite sums, and scalar actions; this extends the coordinate formula of `Matrix.Module.smul_def` beyond square matrices
Used in: consensus, push-sum, and gradient-tracking state updates where a finite mixing matrix combines module-valued node states row by row
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def smulVec {R m n E : Type*} [Fintype n] [AddCommMonoid E] [SMul R E]
    (A : Matrix m n R) (X : n -> E) : m -> E :=
  fun i => ∑ j : n, A i j • X j

/-- The coordinates of `Matrix.smulVec` are the scalar-weighted sums of the
corresponding matrix rows.

Layer: Glue | Gap: Level 0 (coordinate specification of a rectangular matrix action on module-valued vectors)
Proof: by rfl after unfolding `Matrix.smulVec`.
Source: Mathlib finite matrices, finite sums, and scalar multiplication
Used in: unfolding finite-network mixing updates at one node before stochastic-optimization recurrence and consensus estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem smulVec_apply {R m n E : Type*} [Fintype n]
    [AddCommMonoid E] [SMul R E] (A : Matrix m n R) (X : n -> E) (i : m) :
    smulVec A X i = ∑ j : n, A i j • X j := by
  rfl

/-- On a two-element Boolean index, a row action is the sum of its two
coordinates. -/
@[simp] theorem smulVec_bool_apply {R m E : Type*}
    [AddCommMonoid E] [SMul R E]
    (A : Matrix m Bool R) (X : Bool → E) (i : m) :
    smulVec A X i = A i true • X true + A i false • X false := by
  rw [smulVec_apply, Fintype.sum_bool]

/-- A matrix sends the zero module-valued vector to zero. -/
@[simp] theorem smulVec_zero {R m n E : Type*} [Fintype n]
    [AddCommMonoid E] [SMulZeroClass R E] (A : Matrix m n R) :
    smulVec A (0 : n → E) = 0 := by
  funext i
  simp [smulVec_apply]

/-- Every coordinate of the image of the zero vector is zero. -/
@[simp] theorem smulVec_zero_apply {R m n E : Type*} [Fintype n]
    [AddCommMonoid E] [SMulZeroClass R E] (A : Matrix m n R) (i : m) :
    smulVec A (0 : n → E) i = 0 := by
  rw [smulVec_apply]
  simp

/-- The matrix with Kronecker-delta entries acts identically on a
module-valued vector. -/
@[simp] theorem smulVec_identity {R n E : Type*} [Fintype n] [DecidableEq n]
    [MonoidWithZero R] [AddCommMonoid E] [MulActionWithZero R E] (X : n → E) :
    smulVec (fun i j : n => if i = j then 1 else 0) X = X := by
  funext i
  simp [smulVec_apply]

@[simp] theorem smulVec_identity_apply {R n E : Type*} [Fintype n] [DecidableEq n]
    [MonoidWithZero R] [AddCommMonoid E] [MulActionWithZero R E]
    (X : n → E) (i : n) :
    smulVec (fun k j : n => if k = j then 1 else 0) X i = X i := by
  simp

/-- A coordinate of a matrix action is unchanged when the matrix can be
identified with the Kronecker-delta matrix. -/
@[simp] theorem smulVec_apply_eq_self_of_eq_identity
    {R n E : Type*} [Fintype n] [DecidableEq n]
    [MonoidWithZero R] [AddCommMonoid E] [MulActionWithZero R E]
    (A : Matrix n n R) (X : n → E) (i : n)
    (hA : ∀ j, A i j = if i = j then 1 else 0) :
    smulVec A X i = X i := by
  rw [smulVec_apply]
  simp_rw [hA]
  simp

end Matrix
/-! Phase 4 batch 3: `Matrix_sum_smulVec_of_mem_colStochastic`. -/

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: preservation of the coordinate sum under a column-stochastic matrix action on a module-valued vector; orig was `columnStochastic_leftMul_sum_eq_sum`.
-- generality used: arbitrary finite node type, ordered semiring of matrix coefficients, and additive commutative module of state values; no norm, topology, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle hypotheses are used.
-- portable call pattern: gradient-tracking, push-sum, and consensus proofs change the finite node type, ordered scalar semiring, module-valued state space, column-stochastic matrix, and state while retaining exact preservation of the coordinate sum.
-- counterargument checked: Mathlib's `Matrix.sum_mulVec_of_mem_colStochastic` proves the scalar-valued case, but does not apply to module-valued node states; the theorem is therefore a genuine module extension rather than a paper-local wrapper or pure rename.
-- coverage search: `lean_search_symbols` queries "matrix smulVec coordinate sum preserved column stochastic", "sum matrix scalar action module valued vector column sums one", and "sum smulVec column stochastic module", together with LeanSearch query "column stochastic matrix preserves the sum of coordinates when acting on a module valued vector", found Mathlib's scalar-only `Matrix.sum_mulVec_of_mem_colStochastic`, `Matrix.sum_col_of_mem_colStochastic`, and staged `Matrix.smulVec`; none states the module-valued conclusion.
-- minimal hypotheses: `[Fintype Node]` and `[DecidableEq Node]` support finite matrix sums and Mathlib's stochastic-matrix predicate; `[Semiring R] [PartialOrder R] [IsOrderedRing R]` are exactly the predicate's scalar assumptions; `[AddCommMonoid E] [Module R E]` are exactly the finite-sum and scalar-distribution laws used in the proof.

namespace Matrix

/-- Applying a column-stochastic scalar matrix to a module-valued finite vector
preserves the sum of its coordinates.

Layer: Model | Gap: Level 1 (module-valued column-stochastic sum preservation)
Proof: commute the two finite sums, factor each fixed state coordinate through its column sum, and rewrite that sum to one using `Matrix.sum_col_of_mem_colStochastic`.
Source: Mathlib column-stochastic matrices, finite big-operator scalar distribution, and the SOptLib rectangular module-valued matrix action
Used in: gradient-tracking pull updates and zero-sum tracker recurrences where a column-stochastic communication matrix must preserve the aggregate module-valued state
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sum_smulVec_of_mem_colStochastic
    {R Node E : Type*} [Fintype Node] [DecidableEq Node]
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [AddCommMonoid E] [Module R E]
    {A : Matrix Node Node R} (X : Node → E)
    (hA : A ∈ colStochastic R Node) :
    ∑ i : Node, smulVec A X i = ∑ j : Node, X j := by
  simp only [smulVec_apply]
  rw [Finset.sum_comm]
  calc
    (∑ j : Node, ∑ i : Node, A i j • X j) =
        ∑ j : Node, (∑ i : Node, A i j) • X j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_smul]
    _ = ∑ j : Node, X j := by
      simp [sum_col_of_mem_colStochastic hA]

end Matrix
/-! Phase 4 batch 3: `Matrix_sub_one_smulVec`. -/

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: subtraction of the identity under a module-valued matrix action; orig was `leftMul_sub_identity`.
-- generality used: an arbitrary ring of matrix scalars, finite square index type, additive commutative group, and module; no norm, topology, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: consensus, push-sum, and gradient-tracking recurrences change the scalar matrix, finite network, and module-valued state while reusing the identity that the innovation matrix `A - 1` acts as the original matrix action minus the state.
-- counterargument checked: this is not paper-local bookkeeping or a pure rename; Mathlib's `Matrix.sub_mulVec` and `Matrix.one_mulVec` cover only scalar-valued vectors, while the existing `Matrix.smulVec_identity` supplies only the identity half of the module-valued result.
-- coverage search: `lean_search_symbols` queries "matrix subtraction identity matrix smul vector equals matrix smul vector minus vector" and "Matrix sub one smulVec", plus LeanSearch query "a matrix minus the identity acting on a module-valued vector equals the matrix action minus the vector", found `Matrix.smulVec_identity` and the scalar-only `Matrix.sub_mulVec` and `Matrix.one_mulVec`, but no module-valued subtraction-by-identity law.
-- minimal hypotheses: `[Ring R]` provides matrix subtraction and distributive scalar subtraction, `[Fintype Node] [DecidableEq Node]` provide finite row sums and the identity matrix, and `[AddCommGroup E] [Module R E]` provide subtraction and the compatible scalar action.

namespace Matrix

/-- Acting on a module-valued finite vector by a matrix minus the identity is
the original matrix action minus that vector.

Layer: Model | Gap: Level 0 (module-valued matrix subtraction by the identity)
Proof: distribute scalar subtraction through each finite row sum, then collapse the identity-matrix row sum to its diagonal term.
Source: Mathlib finite matrix algebra and module big operators, extending the scalar-valued `Matrix.sub_mulVec` and `Matrix.one_mulVec` laws
Used in: push-pull gradient-tracking innovation recurrences, where `(C_t - I)` acting on an oracle or tracker state is rewritten as `C_t` acting on that state minus the unchanged state
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec/steps/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sub_one_smulVec
    {R Node E : Type*} [Ring R] [Fintype Node] [DecidableEq Node]
    [AddCommGroup E] [Module R E] (A : Matrix Node Node R) (X : Node → E) :
    smulVec (A - 1) X = smulVec A X - X := by
  calc
    smulVec (A - 1) X = smulVec A X - smulVec (1 : Matrix Node Node R) X := by
      funext i
      simp only [smulVec_apply, Matrix.sub_apply, sub_smul,
        Finset.sum_sub_distrib, Pi.sub_apply]
    _ = smulVec A X - X := by
      congr 1
      funext i
      rw [smulVec_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp

end Matrix
/-! Phase 4 batch 3: `FiniteNetwork_PositiveDiagonal_mul`. -/

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: positive-diagonal closure under multiplication of entrywise nonnegative square matrices; orig was matrixMul_positiveDiagonal.
-- generality used: arbitrary finite node type and scalar semiring with a partial strict ordered-ring structure; no nonempty-node, field, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional assumptions.
-- portable call pattern: consensus, gossip, and push-pull proofs multiply two different nonnegative mixing matrices with positive self-weights and conclude that the accumulated mixing matrix retains positive self-weights.
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it combines strict positivity of one diagonal summand with nonnegativity of every other matrix-product summand, a reusable closure theorem not supplied by the predicate's existing monotonicity API.
-- coverage search: symbol searches for "matrix product positive diagonal entrywise nonnegative positive diagonal" and "PositiveDiagonal multiplication nonnegative matrices" found only the staged predicate and `PositiveDiagonal.mono`; LeanSearch for the full matrix-product contract found `Matrix.pow_apply_nonneg` and diagonal-matrix multiplication, but no two-factor positive-diagonal closure theorem.
-- minimal hypotheses: `[Fintype Node]` forms the multiplication sum and `[Semiring R] [PartialOrder R] [IsStrictOrderedRing R]` supply finite-sum monotonicity, nonnegative products, and strict positivity of the selected diagonal product; decidable equality is introduced locally.

/-- The product of two entrywise nonnegative square matrices with positive
diagonals again has a positive diagonal.

Layer: Model | Gap: Level 1 (positive-diagonal closure under nonnegative matrix multiplication)
Proof: lower-bound each diagonal entry of the product by its self-indexed summand; that summand is strictly positive by the two positive-diagonal hypotheses, while every summand is nonnegative.
Source: Mathlib finite matrix multiplication (`Matrix.mul_apply`), ordered-semiring multiplication, and `Finset.single_le_sum`
Used in: inductive construction of accumulated mixing matrices in consensus and time-varying push-pull proofs, where each new nonnegative communication matrix preserves positive self-weights
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem PositiveDiagonal.mul {Node R : Type*} [Fintype Node]
    [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {A B : Matrix Node Node R}
    (hA_nonneg : ∀ i j : Node, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Node, 0 ≤ B i j)
    (hA_diag : PositiveDiagonal A)
    (hB_diag : PositiveDiagonal B) :
    PositiveDiagonal (A * B) := by
  classical
  intro i
  have hterm : 0 < A i i * B i i := mul_pos (hA_diag i) (hB_diag i)
  have hle : A i i * B i i ≤ ∑ j : Node, A i j * B j i := by
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (hA_nonneg i j) (hB_nonneg j i))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm (by simpa [Matrix.mul_apply] using hle)

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_IsStronglyConnectedPositiveSupport_mul_of_right_positiveDiagonal`. -/

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: preservation of positive-support strong connectivity under multiplication by a nonnegative matrix with positive diagonal; orig was matrixMul_stronglyConnected_of_left.
-- generality used: arbitrary finite node type and scalar non-unital non-associative semiring with a preorder, additive left monotonicity, positivity monotonicity, and strict positivity under multiplication; no real scalar, nonempty-node, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses.
-- portable call pattern: consensus, gossip, and push-pull proofs multiply a strongly connected nonnegative mixing matrix by a different nonnegative accumulated matrix with positive self-weights and retain strong connectivity while changing the node type, scalar type, and matrix factors.
-- counterargument checked: this is not paper-local traceability or a pure wrapper; `IsStronglyConnectedPositiveSupport.mono` still requires the nontrivial positive-support inclusion, while this theorem derives that inclusion from matrix multiplication, two entrywise nonnegativity hypotheses, and the right factor's positive diagonal.
-- coverage search: symbol searches for "matrix product positive support strongly connected left factor right positive diagonal entrywise nonnegative" and "strong connectivity preserved matrix multiplication positive diagonal" found only the source theorem, `IsStronglyConnectedPositiveSupport.mono`, and the distinct `PositiveDiagonal.mul`; LeanSearch found `Matrix.IsIrreducible` and `Matrix.isIrreducible_iff_exists_pow_pos`, but no theorem with this product-preservation contract.
-- minimal hypotheses: `[Fintype Node]` forms the matrix-product sum; `[NonUnitalNonAssocSemiring R] [Preorder R] [AddLeftMono R] [PosMulMono R]` supply nonnegative products and finite-sum monotonicity, and `[PosMulStrictMono R]` supplies positivity of the selected product term; decidable equality is proof-local.

/-- Multiplying a nonnegative matrix with strongly connected positive support on
the right by a nonnegative matrix with positive diagonal preserves that strong
connectivity.

Layer: Model | Gap: Level 1 (positive-support connectivity under nonnegative matrix multiplication)
Proof: use the right factor's positive diagonal to show that every positive entry of the left factor remains positive in the product, lower-bounding the product entry by its corresponding diagonal summand; then apply positive-support connectivity monotonicity.
Source: Mathlib finite matrix multiplication (`Matrix.mul_apply`), ordered-semiring multiplication, `Finset.single_le_sum`, and `Relation.ReflTransGen.mono`
Used in: periodic consensus and push-pull product proofs, where the newest strongly connected communication matrix is multiplied by an accumulated nonnegative product with positive self-weights
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem IsStronglyConnectedPositiveSupport.mul_of_right_positiveDiagonal
    {Node R : Type*} [Fintype Node]
    [NonUnitalNonAssocSemiring R] [Preorder R] [AddLeftMono R]
    [PosMulMono R] [PosMulStrictMono R]
    {A B : Matrix Node Node R}
    (hA_nonneg : ∀ i j : Node, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Node, 0 ≤ B i j)
    (hA_conn : IsStronglyConnectedPositiveSupport A)
    (hB_diag : PositiveDiagonal B) :
    IsStronglyConnectedPositiveSupport (A * B) := by
  classical
  exact hA_conn.mono (fun u v huv => by
    have hterm : 0 < A u v * B v v := mul_pos huv (hB_diag v)
    have hle : A u v * B v v ≤ ∑ k : Node, A u k * B k v := by
      exact Finset.single_le_sum
        (fun k _ => mul_nonneg (hA_nonneg u k) (hB_nonneg k v))
        (Finset.mem_univ v)
    exact lt_of_lt_of_le hterm (by simpa [Matrix.mul_apply] using hle))

end FiniteNetwork
/-! Phase 4 batch 3: `Module_End_comp_eq_smul_of_isNormalizedRankOneProjection_and_eigenspace_le_fixedSpace`. -/

open scoped BigOperators Matrix

-- Generalization plan (G0):
-- concept/name: left spectral action of a normalized rank-one projection whose scalar-extended eigenspace is fixed; orig was `matrix_mul_projection_eq_smul_of_rankOneProjection_and_complex_eigen_fixed`.
-- generality used: arbitrary base and extension fields linked by an algebra structure, arbitrary finite coordinate type, a base-field operator and normalized rank-one projector, existence of the extended eigenvalue, and pointwise fixation of its extended eigenspace; no order, norm, topology, measure, convexity, smoothness, oracle, algorithm setup, or ambient finite-dimensional typeclass is used.
-- portable call pattern: finite-dimensional spectral perturbation, Markov-chain mode splitting, and distributed-consensus proofs change the two scalar fields, coordinate type, operator, eigenvalue, and normalized rank-one projector while reusing the conclusion that left composition by the operator scales the projector.
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it combines a base-field rank-one factorization with an eigenvector available only after scalar extension, proves that the rank-one direction is itself an eigenvector by cancelling a nonzero extension-field coefficient, and descends the resulting action identity through the injective algebra map.
-- coverage search: `lean_search_symbols` queries “endomorphism composition projection equals scalar multiple if rank one range and eigenspace fixed”, “rank one projection fixes eigenspace operator comp equals eigenvalue smul projection”, and “eigenspace contained fixed space projection one dimensional range composition scalar” found the matrix rank-one predicate and Riesz-projection APIs but no theorem with this implication; LeanSearch returned `Module.End.HasEigenvector.apply_eq_smul` and invariant-projection facts, none combining rank one, scalar extension, fixed eigenspace, and descent to the base field.
-- minimal hypotheses: idempotence, nonzero left factor, and normalization travel inside the established normalized-rank-one predicate but the proof needs only its nonzero right factor and rank-one action formula; the scalar-extension eigenvalue and fixed-eigenspace hypotheses are pointwise and match the source assumptions exactly.

/-- If a normalized rank-one projector over a base field fixes a nonzero
eigenspace after scalar extension, left multiplication by the original
operator scales the projector by that eigenvalue.

Layer: Model | Gap: Level 2 (rank-one spectral action descended from a scalar-extended fixed eigenspace)
Proof: expand the normalized rank-one action after scalar extension, use a fixed nonzero eigenvector to show its coefficient along the rank-one direction is nonzero, cancel that coefficient to make the direction an eigenvector, and descend the coordinate identity through the injective algebra map.
Source: Mathlib finite matrix actions, scalar extension by `Matrix.map`, and injectivity of algebra maps between fields
Used in: the rank-one fixed-contour step of a spectral splitting, where the contour projector fixes the enclosed complex eigenspace and the real matrix action must be identified with multiplication by the moving eigenvalue
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Matrix.IsNormalizedRankOneProjection.mul_left_eq_smul_of_eigenspace_le_fixed_space
    {𝕜 𝕂 ι : Type*} [Field 𝕜] [Field 𝕂] [Algebra 𝕜 𝕂] [Fintype ι]
    (A P : Matrix ι ι 𝕜) (lambda : 𝕜)
    (hP : Matrix.IsNormalizedRankOneProjection P)
    (hlambdaEigen :
      ∃ v : ι → 𝕂, v ≠ 0 ∧
        A.map (algebraMap 𝕜 𝕂) *ᵥ v =
          algebraMap 𝕜 𝕂 lambda • v)
    (heigenspace_le_fixedSpace :
      ∀ v : ι → 𝕂,
        A.map (algebraMap 𝕜 𝕂) *ᵥ v =
            algebraMap 𝕜 𝕂 lambda • v →
          P.map (algebraMap 𝕜 𝕂) *ᵥ v = v) :
    A * P = lambda • P := by
  classical
  rcases hP with
    ⟨_idempotent, right, left, hright_ne, _hleft_ne, _hnormalized, hP_apply⟩
  obtain ⟨v, hv_ne, hAv⟩ := hlambdaEigen
  have hP_entry : ∀ i j : ι, P i j = left j * right i := by
    intro i j
    have h := congrFun (hP_apply (Pi.single j (1 : 𝕜))) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  let coeff : 𝕂 := ∑ j : ι, algebraMap 𝕜 𝕂 (left j) * v j
  have hPv_rank :
      P.map (algebraMap 𝕜 𝕂) *ᵥ v =
        coeff • fun i : ι ↦ algebraMap 𝕜 𝕂 (right i) := by
    funext i
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hP_entry, map_mul,
      Pi.smul_apply]
    unfold coeff
    rw [smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hv_span :
      v = coeff • fun i : ι ↦ algebraMap 𝕜 𝕂 (right i) := by
    rw [← heigenspace_le_fixedSpace v hAv]
    exact hPv_rank
  have hcoeff_ne : coeff ≠ 0 := by
    intro hcoeff_zero
    apply hv_ne
    rw [hv_span, hcoeff_zero]
    simp
  have hright_extension_eigen :
      A.map (algebraMap 𝕜 𝕂) *ᵥ
          (fun i : ι ↦ algebraMap 𝕜 𝕂 (right i)) =
        algebraMap 𝕜 𝕂 lambda •
          (fun i : ι ↦ algebraMap 𝕜 𝕂 (right i)) := by
    have hAv_span :
        A.map (algebraMap 𝕜 𝕂) *ᵥ
            (coeff • fun i : ι ↦ algebraMap 𝕜 𝕂 (right i)) =
          algebraMap 𝕜 𝕂 lambda •
            (coeff • fun i : ι ↦ algebraMap 𝕜 𝕂 (right i)) := by
      simpa [← hv_span] using hAv
    rw [Matrix.mulVec_smul] at hAv_span
    funext i
    have hi := congrFun hAv_span i
    have hi' := congrArg (fun z : 𝕂 ↦ coeff⁻¹ * z) hi
    simpa [Pi.smul_apply, hcoeff_ne, mul_comm, mul_left_comm, mul_assoc] using hi'
  have hright_eigen : A *ᵥ right = lambda • right := by
    funext i
    apply (algebraMap 𝕜 𝕂).injective
    have hi := congrFun hright_extension_eigen i
    calc
      algebraMap 𝕜 𝕂 ((A *ᵥ right) i) =
          (A.map (algebraMap 𝕜 𝕂) *ᵥ
            (fun k : ι ↦ algebraMap 𝕜 𝕂 (right k))) i :=
        RingHom.map_mulVec (algebraMap 𝕜 𝕂) A right i
      _ = algebraMap 𝕜 𝕂 lambda *
          algebraMap 𝕜 𝕂 (right i) := by
        simpa [Pi.smul_apply] using hi
      _ = algebraMap 𝕜 𝕂 ((lambda • right) i) := by
        simp [Pi.smul_apply, map_mul]
  ext i j
  have hright_i := congrFun hright_eigen i
  calc
    (A * P) i j = ∑ k : ι, A i k * P k j := by simp [Matrix.mul_apply]
    _ = ∑ k : ι, A i k * (left j * right k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [hP_entry k j]
    _ = left j * ∑ k : ι, A i k * right k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = left j * (lambda * right i) := by
      rw [show ∑ k : ι, A i k * right k = lambda * right i by
        simpa [Matrix.mulVec, Pi.smul_apply] using hright_i]
    _ = lambda * P i j := by
      rw [hP_entry i j]
      ring
    _ = (lambda • P) i j := by simp
/-! Phase 4 batch 3: `FiniteNetwork_influenceEntriesAllEqual_of_period_eq_one`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: equality of every phase-node influence entry when a constant normalized phase average has period one; orig was `influenceEntriesAllEqual_of_period_eq_one`.
-- generality used: arbitrary node carrier, natural period, real-valued phase-indexed row family, and real constant; only the constant normalized phase-average identity and the period-one equality are assumed, with no node finiteness, network matrices, periodicity, positivity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional hypotheses.
-- portable call pattern: static-network specializations of periodic push-pull, push-sum, consensus, and gradient-tracking analyses change the node type and influence row while reusing the same reduction from a constant phase-average identity to equality of all entries.
-- counterargument checked: the proof is elementary, but the declaration is not merely paper-local traceability or a pure rename because it reorganizes singleton-phase finite-sum simplification and coordinate extensionality into the exact reusable bridge from an averaged influence invariant to the entrywise equality condition used in effective-network-size arguments.
-- coverage search: `lean_search_symbols` queries "finite period one normalized average constant function entries all equal", "Fin p family average equals constant period equals one pairwise entries equal", and "sum over Fin one function equals value unique index" found only the paper-local candidate, the distinct effective-node equality characterization, and generic finite-average APIs; LeanSearch returned `Finset.expect_singleton` and singleton-vector facts, which cover only the internal singleton simplification, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Fintype Node]` was dropped because the proof never sums over nodes; the constant-average equality and `p = 1` are exactly the two facts needed to identify arbitrary phase-node entries.

/-- A real-valued phase-indexed influence family has equal entries at every
phase and node when its normalized phase average is constant and the period is
one.

Layer: Model | Gap: Level 1 (period-one constant-average influence equality)
Proof: substitute the period-one equality, simplify each coordinate of the normalized sum over `Fin 1`, and use subsingleton elimination to identify the two phase indices.
Source: Mathlib finite-type big operators, singleton `Fin 1` sums, and subsingleton elimination
Used in: static-network specializations of periodic push-pull, push-sum, consensus, and gradient-tracking analyses that discharge the all-influence-entries-equal condition after identifying a constant phase-average influence row
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem influence_entry_eq_of_period_eq_one_of_average_eq_const
    {Node : Type*} {p : Nat}
    (b : Fin p → Node → ℝ) (kappa : ℝ)
    (haverage :
      (fun i : Node => ((p : ℝ)⁻¹) * ∑ r : Fin p, b r i) =
        fun _ : Node => kappa) :
    p = 1 → ∀ r s : Fin p, ∀ i j : Node, b r i = b s j := by
  intro hp
  subst p
  intro r s i j
  have hi := congrFun haverage i
  have hj := congrFun haverage j
  simp at hi hj
  have hr : r = 0 := Subsingleton.elim _ _
  have hs : s = 0 := Subsingleton.elim _ _
  simpa [hr, hs] using hi.trans hj.symm

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceGain_eq_card_mul_of_average_eq_const`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: cardinality formula for periodic influence gain with a constant phase-average row; orig was `influenceGain_eq_nodeCount_mul_averagePerronOverlap`.
-- generality used: arbitrary finite node carrier, natural period, semiring-valued phase-indexed row family, and semiring constant, with inversion for the common reciprocal-period scale; no nonemptiness, positive-period, stochasticity, periodicity, positivity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and consensus analyses change the influence family, period, and identified average-row constant while reusing the conversion from a constant average influence row to total average gain.
-- counterargument checked: Mathlib's constant-sum lemmas handle only the final node sum; the phase/node sum interchange and reciprocal-period-scaled influence contract are not covered, so this is a reusable finite-network bridge rather than paper-local traceability, a pure rename, or a caller-side expression.
-- coverage search: `lean_search_symbols` queries "periodic influence gain equals card times constant average row" and "finite sum constant function card multiplication after interchange average" found the paper-local theorem and the complementary periodic influence Cauchy bound but no duplicate; LeanSearch for the full contract returned `Finset.sum_eq_card_nsmul`, `Fintype.card_mul_expect`, and `Real.arith_mean_weighted_of_constant`, which cover only the constant-sum endpoint.
-- minimal hypotheses: `[Fintype Node]` is exactly what the node sum requires; `Fin p` supplies the finite phase family, and the equality remains valid at zero period and for an empty node type, so no positivity or nonemptiness hypothesis is added.

/-- If every coordinate of a phase-average influence row equals the same
constant, then its period-average total gain is the node cardinality times
that constant.

Layer: Model | Gap: Level 1 (periodic influence gain from a constant average row)
Proof: interchange the finite phase and node sums, distribute reciprocal-period scaling across the node sum, rewrite by the constant-row hypothesis, and evaluate the finite sum of a constant.
Source: Mathlib finite big operators, `Finset.sum_comm`, `Finset.mul_sum`, and finite-type constant-sum simplification
Used in: periodic push-pull, push-sum, and gradient-tracking analyses that turn an identified constant phase-average influence row into the scalar block gain used by effective-node and convergence-rate estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceGain_eq_card_mul_of_average_eq_const
    {R : Type*} [Semiring R] [Inv R]
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → R) (kappa : R)
    (haverage :
      (fun i : Node => ((p : R)⁻¹) * ∑ r : Fin p, b r i) =
        fun _ : Node => kappa) :
    ((p : R)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i =
      (Fintype.card Node : R) * kappa := by
  classical
  calc
    ((p : R)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i =
        ∑ i : Node, ((p : R)⁻¹) * ∑ r : Fin p, b r i := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ _i : Node, kappa := by rw [haverage]
    _ = (Fintype.card Node : R) * kappa := by simp

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceGain_pos_of_average_eq_const`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: strict positivity of periodic influence gain from a positive constant phase-average row; orig was `influenceGain_pos`.
-- generality used: arbitrary finite nonempty node carrier, natural period, strictly ordered semiring-valued phase-indexed influence family, and positive average-row constant, with inversion for the common reciprocal-period scale; no positive-period, stochasticity, periodicity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and consensus analyses change the influence family, period, and positive constant average while reusing strict positivity of the resulting average total influence gain.
-- counterargument checked: this is not paper-local traceability or a pure rename; it composes the reusable phase/node averaging identity with nonempty finite-network cardinality positivity to expose the positivity boundary consumed by effective-node and block-gain estimates.
-- coverage search: `lean_search_symbols` queries "periodic influence gain positive average equals positive constant", "finite family average row constant total sum strict positivity", and "cardinality positive multiplication positive constant" found the complementary `FiniteNetwork.periodicInfluenceGain_eq_card_mul_of_average_eq_const`, the paper-local source theorem, and unrelated positivity results, but no theorem with this full contract; LeanSearch found `Fintype.card_pos` as the relevant Mathlib endpoint only.
-- minimal hypotheses: `[Fintype Node] [Nonempty Node]` are exactly needed to make the node cardinality strictly positive; the strict ordered semiring structure supplies positive natural-number casts and strict positivity of products, while inversion is used only by the averaging expression; `0 < kappa` and the constant-average equality are pointwise inputs, and positive period is unnecessary because these hypotheses already rule out the degenerate case relevant to the conclusion.

/-- A finite nonempty network's period-average total influence is strictly
positive when its phase-average influence row is a positive constant row.

Layer: Model | Gap: Level 1 (positive periodic influence gain from a constant average row)
Proof: rewrite the period-average total influence with `FiniteNetwork.periodicInfluenceGain_eq_card_mul_of_average_eq_const`, then multiply positivity of the nonempty node cardinality by positivity of the constant row entry.
Source: Mathlib finite-type cardinality positivity and strictly ordered semiring multiplication, together with the finite-network phase/node averaging identity
Used in: periodic push-pull, push-sum, and gradient-tracking analyses after identifying the average influence row, before proving positivity of block gains, influence second moments, and effective node counts
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodic_influence_gain_pos_of_average_eq_const
    {R : Type*} [Semiring R] [Inv R] [PartialOrder R] [IsStrictOrderedRing R]
    {Node : Type*} [Fintype Node] [Nonempty Node] {p : Nat}
    (b : Fin p → Node → R) (kappa : R) (hkappa : 0 < kappa)
    (haverage :
      (fun i : Node => ((p : R)⁻¹) * ∑ r : Fin p, b r i) =
        fun _ : Node => kappa) :
    0 < ((p : R)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i := by
  rw [periodicInfluenceGain_eq_card_mul_of_average_eq_const b kappa haverage]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hkappa

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceGain_sq_le_card_mul_secondMoment`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: normalized finite-network Cauchy bound relating periodic influence gain to influence second moment; orig was `influenceGain_sq_le_nodeCount_mul_influenceSecondMoment`.
-- generality used: arbitrary finite node carrier, natural period, and real-valued phase-node family; no nonemptiness, positive-period, network, stochasticity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are needed.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and consensus analyses change the phase-node influence family and period while reusing the same bound of squared coherent gain by node cardinality times quadratic amplification.
-- counterargument checked: Mathlib supplies the unnormalized finite scalar Cauchy inequality, but not the phase-node flattening and reciprocal-period cancellation that retain only node cardinality; this is therefore a reusable Model bridge rather than paper-local traceability, a pure rename, or a caller-side expression.
-- coverage search: `lean_search_symbols` queries "periodic influence gain square card second moment" and "inverse period sum row sums squared less than node card inverse period sum squares" found only the paper-local theorem and related effective-node APIs; LeanSearch found the partial hits `sq_sum_le_card_mul_sum_sq` and `sum_div_card_sq_le_sum_sq_div_card`, but no theorem with this normalized phase-node statement.
-- minimal hypotheses: `[Fintype Node]` is exactly what the node sums require; `Fin p` supplies the finite phase family, and splitting on `p = 0` removes the source's positive-period hypothesis while keeping the reciprocal convention total.

/-- The squared period-average total influence of a finite phase-node family is
at most the node cardinality times its period-average squared influence.

The statement remains valid at period zero under the totalized real reciprocal;
positive-period network applications recover the usual normalized
Cauchy--Schwarz inequality.

Layer: Model | Gap: Level 1 (normalized periodic finite-network Cauchy bound)
Proof: flatten the phase-node family to `Fin p × Node`, apply Mathlib's `sq_sum_le_card_mul_sum_sq`, and cancel one reciprocal-period factor; the zero-period case simplifies separately.
Source: Mathlib finite-product cardinalities, finite big operators, ordered real-field algebra, and `sq_sum_le_card_mul_sum_sq`
Used in: periodic distributed stochastic optimization proofs that bound squared coherent influence gain by network size times the quadratic noise-amplification coefficient before controlling effective node count
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceGain_sq_le_card_mul_secondMoment
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → Real) :
    (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i) ^ 2 ≤
      (Fintype.card Node : Real) *
        (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) := by
  classical
  by_cases hp : p = 0
  · subst p
    simp
  · have hpReal : (p : Real) ≠ 0 := by
      exact_mod_cast hp
    let x : Fin p × Node → Real := fun a => b a.1 a.2
    have hcauchy := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := x)
    have htotal :
        (∑ a : Fin p × Node, x a) =
          ∑ r : Fin p, ∑ i : Node, b r i := by
      rw [Fintype.sum_prod_type]
    have hsquares :
        (∑ a : Fin p × Node, (x a) ^ 2) =
          ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 := by
      rw [Fintype.sum_prod_type]
    rw [htotal, hsquares] at hcauchy
    have hraw :
        (∑ r : Fin p, ∑ i : Node, b r i) ^ 2 ≤
          (p : Real) * (Fintype.card Node : Real) *
            ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 := by
      simpa [x, Fintype.card_prod, mul_assoc] using hcauchy
    calc
      (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i) ^ 2 =
          ((p : Real)⁻¹) ^ 2 *
            (∑ r : Fin p, ∑ i : Node, b r i) ^ 2 := by ring
      _ ≤ ((p : Real)⁻¹) ^ 2 *
          ((p : Real) * (Fintype.card Node : Real) *
            ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
      _ = (Fintype.card Node : Real) *
          (((p : Real)⁻¹) *
            ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) := by
        field_simp [hpReal]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceSecondMoment`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: periodic influence second moment, the phase-average squared Euclidean energy of finite-network influence rows; orig was `influenceSecondMoment`.
-- generality used: arbitrary finite node carrier, natural period, and real-valued phase-node family; no network matrices, stochasticity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are needed.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and consensus analyses change the phase-indexed influence family and period while retaining the same quadratic amplification statistic in noise-variance and effective-node-count bounds.
-- counterargument checked: although the construction is one formula, it is not merely paper-local traceability or an isolated caller expression because positivity, normalized Cauchy, effective-node-count, equality-case, and block-noise theorems use this statistic as a stable mathematical object; the paired unfolding theorem supplies its basic Model API.
-- coverage search: `lean_search_symbols` queries "period average squared Euclidean norm finite family second moment", "periodic influence second moment average row norm squared", and "finite average norm squared family definition" found finite-average moment inequalities and the raw-formula periodic influence theorems, but no named definition; LeanSearch for "the average squared Euclidean norm of a finite family of real vectors" found `MeasureTheory.average`, `RCLike.norm_expect_le`, and finite-sum square inequalities, none of which defines this finite-network statistic.
-- minimal hypotheses: `[Fintype Node]` is exactly what the node-coordinate sum requires; `Fin p` supplies the phase family, and the totalized reciprocal preserves the source formula without a positive-period assumption.

/-- The periodic influence second moment is the phase-average squared Euclidean
energy of a finite family of node-influence rows.

For period zero, the totalized real reciprocal and the empty phase sum make the
statistic zero.

Layer: Model | Concept: finite-network periodic influence second moment
Proof: (definitional construction; multiply the sum of phase-wise node-coordinate squares by the reciprocal of the period)
Source: Mathlib finite sums over `Fin` and finite node types, natural casts to the reals, and totalized real reciprocals
Used in: periodic distributed stochastic optimization when phase-dependent network influence is converted into a quadratic noise-amplification coefficient and the denominator of an effective-node count
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def periodicInfluenceSecondMoment
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → Real) : Real :=
  ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2

/-- The periodic influence second moment unfolds to the reciprocal period times
the sum of all squared phase-node influence entries.

Layer: Model | Gap: Level 0 (periodic influence second-moment unfolding)
Proof: by rfl after unfolding `FiniteNetwork.periodicInfluenceSecondMoment`.
Source: Mathlib finite sums over `Fin` and finite node types, natural casts to the reals, and totalized real reciprocals
Used in: specializing the named periodic influence statistic to raw phase-node sums before Cauchy bounds, positivity arguments, effective-node calculations, and block-noise variance estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem periodicInfluenceSecondMoment_def
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → Real) :
    periodicInfluenceSecondMoment b =
      ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 := by
  rfl

/-- Multiplying a nonempty-period influence second moment by the period
recovers the unnormalized squared influence energy.

Layer: Model | Gap: Level 0 (period-average cancellation)
Proof: unfold `periodicInfluenceSecondMoment` and cancel the nonzero real cast
of the period.
Source: Mathlib finite sums, natural casts to the reals, and field
simplification
Used in: converting a period-averaged network noise coefficient back to the
finite phase sum in block variance identities -/
theorem sum_sq_eq_period_mul_periodicInfluenceSecondMoment
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → Real) (hp : p ≠ 0) :
    (∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) =
      (p : Real) * periodicInfluenceSecondMoment b := by
  have hp' : (p : Real) ≠ 0 := by
    exact_mod_cast hp
  rw [periodicInfluenceSecondMoment_def]
  rw [← mul_assoc, mul_inv_cancel₀ hp', one_mul]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceSecondMoment_pos_of_gain_pos`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: strict positivity of periodic influence second moment from positive periodic influence gain; orig was `influenceSecondMoment_pos`.
-- generality used: arbitrary finite node carrier, natural period, and real-valued phase-node family; no nonemptiness, positive-period, network, stochasticity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and consensus analyses change the influence family and period while reusing positivity of the quadratic influence statistic before dividing by it in effective-node or variance-normalization expressions.
-- counterargument checked: not paper-local traceability or a pure wrapper because it composes a normalized phase-node Cauchy bound and positive gain into the reusable strict positivity needed at denominator call sites; Mathlib has only the underlying finite-sum inequalities.
-- coverage search: `lean_search_symbols` queries "periodic influence second moment positive of gain positive Cauchy cardinality" and "finite family normalized total sum positive implies normalized sum squares positive" found the complementary `FiniteNetwork.periodicInfluenceGain_sq_le_card_mul_secondMoment` and the paper-local source theorem, but no theorem with this full contract; LeanSearch for "If a finite sum of real numbers is positive, then the sum of their squares is positive" found `sq_sum_le_card_mul_sum_sq` and related finite-sum lemmas, but no normalized periodic-network consequence.
-- minimal hypotheses: `[Fintype Node]` is exactly what the node sums require; nonemptiness and positive period are unnecessary because the positive-gain hypothesis itself excludes their degenerate cases, and all algorithm setup assumptions were removed.

/-- The period-average squared influence of a finite network is
strictly positive whenever its period-average total influence is positive.

Layer: Model | Gap: Level 1 (positive periodic influence second moment from positive gain)
Proof: combine `FiniteNetwork.periodicInfluenceGain_sq_le_card_mul_secondMoment` with nonnegativity of the node cardinality and the strictly positive square of the gain.
Source: Mathlib finite-type cardinality positivity and ordered real nonlinear arithmetic, together with the normalized finite phase-node Cauchy inequality
Used in: periodic distributed stochastic optimization after proving positive influence gain, before using the quadratic influence statistic as the denominator of an effective-node count or a variance normalization
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodic_influence_second_moment_pos_of_gain_pos
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → Real)
    (hgain : 0 < ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i) :
    0 < ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 := by
  have hcard : 0 ≤ (Fintype.card Node : Real) := by positivity
  nlinarith [periodicInfluenceGain_sq_le_card_mul_secondMoment b,
    sq_pos_of_pos hgain]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_effectiveNodeCount_pos_and_le_card`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: positive effective node count bounded by the finite network cardinality; orig was `effectiveNodeCount_pos_and_le_nodeCount`.
-- generality used: arbitrary finite node carrier, natural period, and real-valued phase-node influence family with nonzero period-average total influence; no network matrices, stochasticity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and weighted distributed stochastic algorithms change their phase-dependent influence family while reusing the same positive effective-parallelism and network-cardinality bound.
-- counterargument checked: the scalar effective-node-count API gives the two conclusions separately from denominator positivity and a square bound, but callers with a phase-node family would still have to derive both premises; composing the normalized Cauchy and positive-second-moment contracts is a substantive family-level Model theorem rather than paper-local traceability or a pure rename.
-- coverage search: `lean_search_symbols` queries "effective node count positive at most finite cardinality sum entries square sum squares nonzero" and "effective_node_count_pos effective_node_count_le_of_sq_le_mul" found the partial scalar lemmas `FiniteNetwork.effective_node_count_pos` and `FiniteNetwork.effective_node_count_le_of_sq_le_mul`, the normalized Cauchy theorem `FiniteNetwork.periodicInfluenceGain_sq_le_card_mul_secondMoment`, and the source-local result, but no combined family-level theorem; LeanSearch for "effective sample size square of sum divided by sum of squares is positive and at most cardinality" found `sq_sum_le_card_mul_sum_sq` but no effective-count quotient theorem.
-- minimal hypotheses: `[Fintype Node]` supports the finite sums, and nonvanishing of the averaged gain is the exact nondegeneracy hypothesis; it forces the averaged second moment positive and rules out empty-node and zero-period cases, so neither `[Nonempty Node]` nor `0 < p` is needed.

/-- The effective node count of a finite phase-indexed influence family is
strictly positive and at most the number of nodes when its averaged total
influence is nonzero.

Layer: Model | Gap: Level 1 (effective-node-count range for periodic influence families)
Proof: derive positivity of the averaged squared influence from nonzero gain, then combine the scalar effective-node-count positivity and upper-bound APIs with the normalized finite phase-node Cauchy inequality.
Source: Mathlib finite-sum Cauchy--Schwarz and ordered-field division inequalities, together with the SOptLib effective-node-count and periodic-influence APIs
Used in: periodic distributed stochastic optimization after establishing nonzero aggregate network influence, before using effective parallelism in variance reduction and convergence-rate bounds
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodic_effective_node_count_pos_and_le_card
    {Node : Type*} [Fintype Node] {p : Nat}
    (b : Fin p → Node → Real)
    (hgain : ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i ≠ 0) :
    0 < effective_node_count
        (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i)
        (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) ∧
      effective_node_count
          (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i)
          (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) ≤
        (Fintype.card Node : Real) := by
  have hcard : 0 ≤ (Fintype.card Node : Real) := by positivity
  have hgainSq :
      0 < (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i) ^ 2 :=
    sq_pos_of_ne_zero hgain
  have hsecondMoment :
      0 < ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 := by
    by_contra h
    have hnonpos :
        ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 ≤ 0 :=
      le_of_not_gt h
    have hproduct_nonpos :
        (Fintype.card Node : Real) *
            (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcard hnonpos
    exact (not_lt_of_ge
      ((periodicInfluenceGain_sq_le_card_mul_secondMoment b).trans
        hproduct_nonpos)) hgainSq
  constructor
  · exact effective_node_count_pos _ _ hsecondMoment hgain
  · exact effective_node_count_le_of_sq_le_mul _ _ _ hsecondMoment
      (periodicInfluenceGain_sq_le_card_mul_secondMoment b)

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceSeriesTerm`. -/

open scoped BigOperators Matrix

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: shifted Perron-row coefficient in a periodic network influence series; orig was `influenceSeriesTerm`.
-- generality used: arbitrary finite node carrier, a ring-valued matrix schedule, and a ring-valued row-weight sequence; no nonempty, stochasticity, positivity, periodicity, norm, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic push-pull, push-sum, and gradient-tracking analyses change the finite node type, pull schedule, absolute-probability row, phase, and lag while using the same propagated one-step network-innovation coefficient and its weighted-column specification.
-- counterargument checked: although formula-bodied, this is not paper-local bookkeeping or a caller-side abbreviation because the shifted row, newest-on-the-left propagation window, and final `C r - 1` innovation recur as one stable coefficient in summability, phase-periodicity, corrected-lift, and impulse-response arguments; the unfolding and weighted-column theorems provide a usable Model API.
-- coverage search: lean_search_symbols queries "Perron row weighted influence tail term consecutive matrix product innovation C minus identity", "row vector multiplied by consecutive product and matrix minus identity weighted column equality", and "periodic influence series term weighted column" found `FiniteNetwork.consecutiveProduct`, the related but structurally different `FiniteNetwork.periodicCorrectedLiftSeriesTerm`, and only paper-local `influenceSeriesTerm` declarations; LeanSearch for "row vector times matrix product times matrix minus identity coordinate equals weighted sum of a column" found Mathlib's `Matrix.vecMul`, `Matrix.dotProduct_mulVec`, and `Matrix.vecMul_vecMul` primitives but no packaged influence coefficient.
-- minimal hypotheses: `[Ring R]` supplies the matrix semiring structure and the subtraction in the one-step innovation, while `[Fintype Node]` supplies finite matrix products; the noncomputable definition selects classical equality internally for the identity matrix, so `DecidableEq Node` is not stored in the public object; all source network and algorithm assumptions were removed.

/-- The lag-`j` influence-tail row obtained by propagating a shifted weight row
through a consecutive matrix window and then applying the phase-`r` innovation.

The propagation window starts at `r + 1`, uses the newest-on-the-left
convention, and the terminal innovation is `C r - 1`.

Layer: Model | Concept: periodic finite-network influence-series coefficient
Proof: (definitional construction; multiply the shifted row by the newest-on-the-left consecutive matrix product and then by the one-step matrix innovation)
Source: finite-state nonhomogeneous Markov-chain influence series, Mathlib row-matrix multiplication, and `FiniteNetwork.consecutiveProduct`
Used in: periodic push-pull and gradient-tracking influence-series summability, phase-periodicity, corrected-lift identities, and finite impulse-response expansions
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def periodicInfluenceSeriesTerm
    {R Node : Type*} [Ring R] [Fintype Node]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (r j : Nat) : Node -> R :=
  by
    classical
    exact Matrix.vecMul
      (Matrix.vecMul (pi (r + j + 2)) (consecutiveProduct C (r + 1) j))
      (C r - 1)

/-- A periodic influence-series coefficient unfolds to its shifted row,
consecutive propagation window, and terminal one-step innovation.

Layer: Model | Gap: Level 0 (periodic influence-series coefficient unfolding)
Proof: identify the caller's decidable-equality instance with the classical instance selected by the definition, then close by reflexivity.
Source: Mathlib row-matrix multiplication and matrix subtraction together with `FiniteNetwork.consecutiveProduct`
Used in: exposing the exact influence-tail coefficient before summability, periodicity, and corrected-lift calculations in periodic distributed optimization
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem periodicInfluenceSeriesTerm_def
    {R Node : Type*} [Ring R] [Fintype Node]
    [decEqNode : DecidableEq Node]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (r j : Nat) :
    periodicInfluenceSeriesTerm C pi r j =
      Matrix.vecMul
        (Matrix.vecMul (pi (r + j + 2)) (consecutiveProduct C (r + 1) j))
        (C r - 1) := by
  have hdec : Classical.decEq Node = decEqNode := Subsingleton.elim _ _
  cases hdec
  rfl

/-- Each coordinate of a periodic influence-series coefficient is the shifted
row-weighted action of the propagation window on the corresponding innovation
column.

Layer: Model | Gap: Level 1 (influence coefficient to propagated innovation column)
Proof: reassociate the finite row-matrix contraction with `Matrix.dotProduct_mulVec`; matrix subtraction then identifies the selected innovation column.
Source: Mathlib `Matrix.dotProduct_mulVec`, finite row-matrix multiplication, and matrix-vector multiplication
Used in: bounding each coordinate of a periodic push-pull influence tail by applying zero-sum pull-product contraction to a column of `C r - 1`
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceSeriesTerm_apply
    {R Node : Type*} [Ring R] [Fintype Node] [DecidableEq Node]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (r j : Nat) (i : Node) :
    periodicInfluenceSeriesTerm C pi r j i =
      dotProduct (pi (r + j + 2))
        (Matrix.mulVec (consecutiveProduct C (r + 1) j)
          (fun k : Node => C r k i - (1 : Matrix Node Node R) k i)) := by
  rw [periodicInfluenceSeriesTerm_def, Matrix.dotProduct_mulVec]
  rfl

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicCorrectedLiftSeriesTerm`. -/

open scoped BigOperators Matrix.Module

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: Perron-weighted consecutive-product summand of a periodic corrected lift; orig was `correctedLiftSeriesTerm`.
-- generality used: arbitrary finite node carrier with decidable equality, semiring-valued matrix and weight schedules, and an additive-commutative-monoid-valued zero-sum state with a scalar action; no module laws, nonempty, normed, inner-product, completeness, finite-dimensional, stochasticity, periodicity, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic consensus, push-sum, and gradient-tracking proofs change the pull schedule, Perron-weight sequence, state module, phase, and propagation lag while using the same weighted propagated zero-sum summand in a corrected-lift series.
-- counterargument checked: although this is a single formula, it is not paper-only caller syntax because it fixes the time shift and newest-on-the-left propagation convention shared by the summability, transport, periodicity, and linearity API of corrected lifts; a companion unfolding theorem gives the Model definition a stable public specification.
-- coverage search: lean_search_symbols queries "Perron weighted propagated zero sum state corrected lift series term", "weighted state matrix product action zero sum", and "consecutive matrix product weighted state smulVec Perron zero sum" found the existing `FiniteNetwork.ZeroSumState` and `FiniteNetwork.consecutiveProduct` ingredients but no declaration packaging this summand; LeanSearch for "Perron weighted propagated term of a zero sum state under a product of stochastic matrices" found unrelated stochastic-matrix and kernel results, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` supply the finite weighted sums and square-matrix identity, `[Semiring R]` supplies the consecutive matrix product, and `[AddCommMonoid E] [SMul R E]` supply exactly the state addition and scalar action used in the formula; the zero-sum proof is carried by the domain but no extra property hypothesis is consumed by this definitional construction.

/-- The Perron-weighted term obtained by propagating a zero-sum finite-network
state through a consecutive window of a matrix schedule.

The matrix window uses the newest-on-the-left convention, and the weight at
lag `j` is read at time `t + j + 1`.

Layer: Model | Concept: periodic corrected-lift series summand on a zero-sum network state
Proof: (definitional construction; apply a consecutive matrix product to the state and take its finite Perron-weighted sum at the shifted time)
Source: finite-state nonhomogeneous Markov-chain absolute probability sequences, Mathlib matrix module actions, and finite weighted sums
Used in: periodic consensus, push-sum, and gradient-tracking corrected-lift series before summability, Poisson transport, phase-periodicity, and linearity arguments
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def periodicCorrectedLiftSeriesTerm
    {R Node E : Type*} [Semiring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (t j : Nat) (W : ZeroSumState Node E) : E :=
  ∑ i : Node,
    pi (t + j + 1) i • Matrix.smulVec (consecutiveProduct C t j) W.1 i

/-- The periodic corrected-lift summand unfolds to the shifted Perron-weighted
sum of the consecutively propagated state.

Layer: Model | Gap: Level 0 (corrected-lift summand unfolding)
Proof: by rfl after unfolding `FiniteNetwork.periodicCorrectedLiftSeriesTerm`.
Source: Mathlib finite weighted sums and matrix module actions together with `FiniteNetwork.consecutiveProduct`
Used in: rewriting corrected-lift summands for geometric bounds, one-step transport, schedule-periodicity, and additivity in periodic distributed optimization
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem periodicCorrectedLiftSeriesTerm_def
    {R Node E : Type*} [Semiring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (t j : Nat) (W : ZeroSumState Node E) :
    periodicCorrectedLiftSeriesTerm C pi t j W =
      ∑ i : Node,
        pi (t + j + 1) i • Matrix.smulVec (consecutiveProduct C t j) W.1 i := by
  rfl

/-- A periodic corrected-lift summand is additive in its zero-sum state.

Layer: Model | Gap: Level 1 (additivity of a propagated weighted zero-sum state)
Proof: distribute the matrix action over pointwise state addition, then distribute the shifted weights and finite sum.
Source: Mathlib distributive scalar actions and finite sums together with `Matrix.smulVec`
Used in: linearity arguments for corrected lifts in periodic consensus, push-sum, and gradient tracking
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLiftSeriesTerm_add
    {R Node E : Type*} [Semiring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [DistribSMul R E]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (t j : Nat) (W V : ZeroSumState Node E) :
    periodicCorrectedLiftSeriesTerm C pi t j (W + V) =
      periodicCorrectedLiftSeriesTerm C pi t j W +
        periodicCorrectedLiftSeriesTerm C pi t j V := by
  simp only [periodicCorrectedLiftSeriesTerm_def, ZeroSumState.coe_add,
    Pi.add_apply, smul_add, Finset.sum_add_distrib, Matrix.smulVec_apply]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicCorrectedLiftSeriesTerm_succ_transport`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: successor transport of a periodic corrected-lift series summand; orig was `correctedLiftSeriesTerm_succ_transport`.
-- generality used: arbitrary finite node carrier with decidable equality, semiring-valued matrix and weight schedules, and an additive-commutative-monoid-valued module state; the only property hypothesis is the pointwise zero-sum preservation needed to form the transported state, with no stochasticity, periodicity, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: time-varying consensus, push-sum, and gradient-tracking Poisson-equation proofs change the communication schedule, Perron weights, scalar semiring, state module, phase, and lag while removing the first matrix from a positive-length corrected-lift summand in exactly the same way.
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it combines the noncommutative adjacent-window product law, associativity of a matrix action on module-valued states, shifted-time arithmetic, and zero-sum subtype transport into the reusable termwise equality needed before an infinite-series shift.
-- coverage search: `lean_search_symbols` queries "corrected lift series successor transport consecutive matrix product", "weighted state consecutive product successor equals next time transported state", and "matrix product action successor transport zero sum state" found the staged summand definition and product ingredients but only the paper-local source theorem with this complete contract; LeanSearch for a consecutive matrix-product successor action found unrelated vector-cons lemmas and no matching transport theorem, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Semiring R]` and `[Module R E]` supply matrix multiplication and associative distributive scalar action, `[Fintype Node] [DecidableEq Node]` supply finite sums and the matrix identity, and `hzero` is the weakest caller-facing evidence required by the codomain `ZeroSumState Node E`.

/-- Removing the first matrix from a positive-length periodic corrected-lift
summand transports the zero-sum state to the next time step.

Layer: Model | Gap: Level 1 (successor transport for a corrected-lift series summand)
Proof: split the ordered consecutive product into its tail times its first matrix, expand the module-valued matrix action, and normalize the shifted weight index; `hzero` supplies the transported zero-sum subtype witness.
Source: Mathlib semiring modules and finite matrix multiplication together with `FiniteNetwork.consecutiveProduct_add` and `Matrix.smulVec`
Used in: shifting the defining corrected-lift series by one term to prove Poisson identities for periodic consensus, push-sum, and gradient-tracking correction operators
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLiftSeriesTerm_succ_transport
    {R Node E : Type*} [Semiring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [Module R E]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (t j : Nat) (W : ZeroSumState Node E)
    (hzero : ∑ i : Node, Matrix.smulVec (C t) W.1 i = 0) :
    periodicCorrectedLiftSeriesTerm C pi t (j + 1) W =
      periodicCorrectedLiftSeriesTerm C pi (t + 1) j
        ⟨Matrix.smulVec (C t) W.1, hzero⟩ := by
  have hproduct :
      consecutiveProduct C t (j + 1) =
        consecutiveProduct C (t + 1) j * C t := by
    rw [show j + 1 = 1 + j by omega, consecutiveProduct_add]
    simp
  have haction (A B : Matrix Node Node R) (X : Node -> E) :
      Matrix.smulVec (A * B) X =
        Matrix.smulVec A (Matrix.smulVec B X) := by
    funext i
    simp only [Matrix.smulVec_apply, Matrix.mul_apply, Finset.smul_sum,
      Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  simp only [periodicCorrectedLiftSeriesTerm_def]
  rw [hproduct, haction]
  simp only [Nat.add_left_comm, Nat.add_comm]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_periodicInfluenceSeriesTerm_weightedState`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: weighted-state action of a periodic influence-series coefficient as the corresponding corrected-lift summand; orig was `influenceSeriesTerm_weightedState`.
-- generality used: arbitrary finite node carrier with decidable equality, ring-valued matrix and weight schedules, and an additive-commutative-monoid-valued module state; the only property hypothesis is the zero coordinate sum needed to package the one-step innovation, with no stochasticity, periodicity, positivity, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: time-varying push-pull, push-sum, and gradient-tracking analyses change the finite node type, communication schedule, Perron-weight sequence, phase, lag, and distributed state while identifying the action of an influence-tail row with the matching corrected-lift impulse term.
-- counterargument checked: this is not paper-local traceability or a pure wrapper around one existing theorem; it connects two independently reusable Model objects by reassociating two finite matrix actions and aligning their shifted time indices, which is the termwise bridge needed before lifting the identity to an infinite influence series.
-- coverage search: lean_search_symbols queries "influence series coefficient weighted state equals corrected lift term zero sum innovation", "weighted state row vector matrix action equality", and "finite weighted sum vecMul matrix equals weighted sum smulVec" found the staged influence and corrected-lift definitions, the paper-local source theorem, and generic finite-sum infrastructure but no reusable theorem with this complete contract; LeanSearch for a row-matrix weighted module action found `Matrix.vecMul` and related scalar matrix identities, but no module-valued time-shifted bridge, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Ring R]` is inherited from the influence coefficient's matrix subtraction, `[Fintype Node] [DecidableEq Node]` supply finite contractions and the matrix identity, `[AddCommMonoid E] [Module R E]` supply exactly the distributive and associative scalar action used to reassociate the contractions, and `hzero` is the weakest evidence required by the corrected-lift summand's `ZeroSumState` domain.

/-- Weighting a distributed state by a periodic influence-series row equals the
matching corrected-lift summand applied to the one-step network innovation.

The influence row at phase `t` uses the propagation window based at `t + 1`;
after reassociating its two row-matrix products, this is precisely the
corrected-lift summand at base time `t + 1` and lag `j`.

Layer: Model | Gap: Level 1 (influence-series action to corrected-lift summand)
Proof: unfold both Model objects, reassociate each row-matrix contraction with the module-valued matrix action by finite-sum distributivity, and normalize the shifted natural-number indices; `hzero` packages the innovation in the zero-sum domain.
Source: Mathlib finite matrix multiplication and module-valued finite sums together with `FiniteNetwork.periodicInfluenceSeriesTerm` and `FiniteNetwork.periodicCorrectedLiftSeriesTerm`
Used in: periodic push-pull and gradient-tracking proofs that convert an influence-tail series acting on a distributed state into the corrected-lift series acting on its pull innovation
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceSeriesTerm_weightedState
    {R Node E : Type*} [Ring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [Module R E]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (t j : Nat) (X : Node -> E)
    (hzero : ∑ i : Node, Matrix.smulVec (C t - 1) X i = 0) :
    (∑ i : Node, periodicInfluenceSeriesTerm C pi t j i • X i) =
      periodicCorrectedLiftSeriesTerm C pi (t + 1) j
        ⟨Matrix.smulVec (C t - 1) X, hzero⟩ := by
  have weighted_vecMul (w : Node -> R) (A : Matrix Node Node R)
      (Y : Node -> E) :
      (∑ i : Node, Matrix.vecMul w A i • Y i) =
        ∑ i : Node, w i • Matrix.smulVec A Y i := by
    simp only [Matrix.vecMul, dotProduct, Matrix.smulVec_apply,
      Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
  rw [periodicInfluenceSeriesTerm_def,
    periodicCorrectedLiftSeriesTerm_def, weighted_vecMul, weighted_vecMul]
  congr 2
  funext i
  rw [show t + j + 2 = t + 1 + j + 1 by omega]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_correctedWeightedCenter`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network corrected weighted center; orig was `liftedCenter`.
-- generality used: arbitrary scalar semiring, finite node carrier, additive commutative group carrying a module structure, a weight vector, distributed state, scalar correction scale, correction map on zero-sum states, and a zero-sum error; no topology, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, stochasticity, positivity, or normalization assumptions are needed.
-- portable call pattern: push-pull, push-sum, and directed gradient-tracking analyses change the Perron or absolute-probability weights, primal state, stepsize, corrected-lift or Poisson correction operator, and zero-sum tracker error while using the same corrected aggregate as the center coordinate in a successor recurrence.
-- counterargument checked: although the construction is one formula, it is not merely paper-local traceability or an alias: the named object gives a stable interface between a weighted network aggregate and a correction operator, and its unfolding theorem lets later recurrence APIs state conclusions in terms of that center without duplicating the affine formula.
-- coverage search: lean_search_symbols queries "corrected weighted center Perron weighted state minus scaled corrected lift zero sum error" and "weighted center minus scale corrected lift zero sum finite network state definition" found periodic corrected-lift and influence identities but no corrected-center object; LeanSearch for "finite weighted sum of module-valued function minus scalar multiple of a correction" found generic finite-sum and affine-combination algebra only, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Fintype Node]` supplies the finite weighted sum, `[Semiring R] [AddCommGroup E] [Module R E]` supply exactly scalar multiplication and subtraction, and the zero-sum condition is carried only by the correction operator's domain.

/-- The corrected weighted center of a finite-network state is its weighted
aggregate minus a scaled correction of a zero-sum error state.

Layer: Model | Concept: finite-network corrected weighted center
Proof: (definitional construction; subtract a scalar multiple of a zero-sum-state correction from the finite weighted state aggregate)
Source: Mathlib finite module-valued sums and scalar actions, together with the finite-network zero-sum-state model used in Poisson-corrected consensus coordinates
Used in: push-pull, push-sum, and directed gradient-tracking center recurrences that correct a Perron-weighted primal aggregate by the lifted zero-sum tracker error
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def correctedWeightedCenter
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (w : Node → R) (X : Node → E) (alpha : R)
    (D : ZeroSumState Node E → E) (e : ZeroSumState Node E) : E :=
  (∑ i : Node, w i • X i) - alpha • D e

/-- The corrected weighted center unfolds to the weighted network aggregate
minus the scaled correction of its zero-sum error.

Layer: Model | Gap: Level 0 (corrected weighted-center unfolding)
Proof: by rfl after unfolding `FiniteNetwork.correctedWeightedCenter`.
Source: Mathlib finite module-valued sums and scalar actions, together with `FiniteNetwork.ZeroSumState`
Used in: specializing a reusable corrected center back to the Perron-weighted primal center and corrected tracker lift before proving its one-step recurrence
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem correctedWeightedCenter_def
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (w : Node → R) (X : Node → E) (alpha : R)
    (D : ZeroSumState Node E → E) (e : ZeroSumState Node E) :
    correctedWeightedCenter w X alpha D e =
      (∑ i : Node, w i • X i) - alpha • D e := by
  rfl

/-- Adding an increment to every coordinate of a distributed state adds its
weighted aggregate to the corrected weighted center.

The correction term is unchanged, so this packages the affine interaction
used when a network-state update is decomposed into its previous state and an
increment.

Layer: Model | Gap: Level 0 (corrected weighted-center state additivity)
Proof: expand the weighted sum over the pointwise state addition, then use additive commutative-group algebra
Source: Mathlib finite module-valued sums and scalar actions
Used in: center-coordinate recurrences for distributed optimization updates written as a state plus an increment -/
theorem correctedWeightedCenter_add_state
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (w : Node → R) (X Y : Node → E) (alpha : R)
    (D : ZeroSumState Node E → E) (e : ZeroSumState Node E) :
    correctedWeightedCenter w (X + Y) alpha D e =
      correctedWeightedCenter w X alpha D e + ∑ i : Node, w i • Y i := by
  simp only [correctedWeightedCenter_def, Pi.add_apply, smul_add,
    Finset.sum_add_distrib]
  simp only [sub_eq_add_neg, add_assoc, add_comm]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_trackerInnovationResponse`. -/

-- Generalization plan (G0):
-- concept/name: zero-initial finite-network tracker innovation response; orig was
--   `meanTrackerError`
-- generality used: an arbitrary scalar type, finite node type, additive commutative
--   group state with a scalar action, time-varying square matrix stream, and driving state;
--   no norm, topology, inner product, completeness, finite-dimensionality, measure,
--   convexity, smoothness, oracle, stochasticity, or matrix stochasticity is used
-- portable call pattern: consensus and gradient-tracking proofs call the same
--   zero-initial response while changing the matrix schedule and the mean-gradient,
--   oracle-noise, compression-error, or perturbation state that drives the innovation
-- counterargument checked: this is not the fixed-operator `linearDuhamelResponse` and
--   not a pure rename of `recursiveIterateProcess`; it fixes the reusable time-varying
--   network recurrence and travels with its zero and successor specifications
-- coverage search: symbol searches for "zero initial linear time varying matrix state
--   response innovation matrix minus identity input", "recursive process zero initial
--   mixing matrix innovation response", and "tracker innovation response finite network
--   matrix state" found only the generic `SOptLib.recursiveIterateProcess`, the
--   fixed-operator `SOptLib.linearDuhamelResponse`, and paper-local tracker recurrences;
--   LeanSearch found scalar linear recurrences and matrix identity facts but no matching
--   time-varying module-valued response
-- minimal hypotheses: `[Fintype Node] [AddCommGroup E] [SMul R E]` are exactly
--   what the action-minus-state recurrence uses; ring, module, and decidable node
--   equality structure is needed only by the companion specification that writes
--   the innovation as `C-I`

namespace FiniteNetwork

/-- The zero-initial response of a time-varying finite-network mixing system to
innovations of the form `(C_t - I) U_t`.

At each successor time, the previous response is mixed by `C_t` and the
current driving state contributes through the deviation of `C_t` from the
identity.

Layer: Model | Concept: zero-initial finite-network tracker innovation response
Proof: (definitional construction; specialize the canonical recursive iterate process to time-varying matrix mixing plus a matrix-minus-identity innovation)
Source: discrete time-varying variation-of-constants recurrences, Mathlib finite matrices and modules, and `SOptLib.recursiveIterateProcess`
Used in: consensus and gradient-tracking decompositions that separately propagate mean-gradient, oracle-noise, compression-error, or perturbation innovations through a changing mixing schedule
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def trackerInnovationResponse
    {R Node E : Type*} [Fintype Node] [AddCommGroup E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (U : Nat -> Node -> E) :
    Nat -> Node -> E :=
  fun t =>
    SOptLib.recursiveIterateProcess (0 : Node -> E)
      (fun k current (_ : Unit) =>
        Matrix.smulVec (C k) current + (Matrix.smulVec (C k) (U k) - U k)) t ()

/-- The tracker innovation response unfolds to the canonical zero-initial
recursive process driven by `(C_t - I) U_t`.

Layer: Model | Gap: Level 0 (tracker innovation response defining equation)
Proof: by rfl after unfolding `FiniteNetwork.trackerInnovationResponse`.
Source: `SOptLib.recursiveIterateProcess` and Mathlib finite matrix subtraction and module actions
Used in: exposing the generated response process before applying its initialization or one-step recurrence in consensus and gradient-tracking proofs
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem trackerInnovationResponse_def
    {R Node E : Type*} [Fintype Node] [AddCommGroup E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (U : Nat -> Node -> E) (t : Nat) :
    trackerInnovationResponse C U t =
      SOptLib.recursiveIterateProcess (0 : Node -> E)
        (fun k current (_ : Unit) =>
          Matrix.smulVec (C k) current + (Matrix.smulVec (C k) (U k) - U k)) t () := by
  rfl

/-- The zero-initial tracker innovation response vanishes at time zero.

Layer: Model | Gap: Level 0 (tracker innovation response initialization)
Proof: unfold `trackerInnovationResponse`; the canonical recursive iterate process returns its initial state at time zero.
Source: `SOptLib.recursiveIterateProcess_zero` and the zero element of a finite module-valued state
Used in: base cases for mean-driven, noise-driven, and perturbation-driven tracker decompositions
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem trackerInnovationResponse_zero
    {R Node E : Type*} [Fintype Node] [AddCommGroup E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (U : Nat -> Node -> E) :
    trackerInnovationResponse C U 0 = 0 := by
  rfl

/-- The tracker innovation response advances by mixing the previous response
and adding the current matrix-minus-identity innovation.

Layer: Model | Gap: Level 0 (tracker innovation response successor recurrence)
Proof: unfold `trackerInnovationResponse`; the successor equation is the defining branch of `SOptLib.recursiveIterateProcess`.
Source: `SOptLib.recursiveIterateProcess_succ`, Mathlib finite matrices, and `Matrix.smulVec`
Used in: induction steps for zero-sum invariants and additive decompositions of gradient-tracking error into deterministic and stochastic responses
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem trackerInnovationResponse_succ
    {R Node E : Type*} [Fintype Node] [AddCommGroup E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (U : Nat -> Node -> E) (t : Nat) :
    trackerInnovationResponse C U (t + 1) =
      Matrix.smulVec (C t) (trackerInnovationResponse C U t) +
        (Matrix.smulVec (C t) (U t) - U t) := by
  rfl

/-- The successor innovation can be written literally as the action of
`C_t - I` on the driving state.

Layer: Model | Gap: Level 0 (tracker innovation matrix-minus-identity recurrence)
Proof: rewrite the action-minus-state innovation with `Matrix.sub_one_smulVec`.
Source: Mathlib finite matrix subtraction and the module-valued `Matrix.sub_one_smulVec` identity
Used in: source-facing push-pull and gradient-tracking recurrences stated with the literal innovation matrix `(C_t-I)`
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem trackerInnovationResponse_succ_sub_one
    {R Node E : Type*} [Ring R] [Fintype Node] [DecidableEq Node]
    [AddCommGroup E] [Module R E]
    (C : Nat -> Matrix Node Node R) (U : Nat -> Node -> E) (t : Nat) :
    trackerInnovationResponse C U (t + 1) =
      Matrix.smulVec (C t) (trackerInnovationResponse C U t) +
        Matrix.smulVec (C t - 1) (U t) := by
  rw [trackerInnovationResponse_succ, Matrix.sub_one_smulVec]

end FiniteNetwork
/-! Phase 4 batch 3: `FiniteNetwork_trackerInnovationResponse_sum_eq_zero`. -/

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: zero-total-mass invariant of a zero-initial tracker innovation response; orig was `meanTrackerError_zeroSum`.
-- generality used: arbitrary finite node type, semiring of matrix coefficients, additive commutative module-valued states with subtraction, a time-varying matrix stream whose columns sum to one, and an arbitrary driving state; no order, entrywise nonnegativity, decidable node equality, norm, topology, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle hypotheses are used.
-- portable call pattern: gradient-tracking, push-sum, and dynamic-consensus proofs change the column-normalized schedule and the mean-gradient, oracle-noise, compression-error, or perturbation driver while the zero-total-mass conclusion for the zero-initial response stays unchanged.
-- counterargument checked: the one-step ingredients are already staged, but callers would otherwise repeat the induction connecting response initialization, preservation of coordinate sums by a column-normalized matrix, and cancellation of every action-minus-state innovation; no existing Mathlib or SOptLib theorem packages that reusable invariant.
-- coverage search: `lean_search_symbols` query "sum of smulVec coordinates equals sum of vector coordinates when each matrix column sums to one" found `Matrix.sum_smulVec_of_mem_colStochastic`, whose stronger stochasticity premise includes unused entrywise nonnegativity; no theorem exposes the required column-sum-only contract.
-- minimal hypotheses: `forall t j, ∑ i, C t i j = 1` is precisely the matrix normalization used; `[Fintype Node]`, `[Semiring R]`, and `[AddCommGroup E] [Module R E]` are exactly what the response, finite-sum rearrangement, and scalar factoring require.

namespace FiniteNetwork

/-- A zero-initial tracker innovation response driven through a matrix schedule
whose columns sum to one has zero coordinate sum at every time.

Layer: Model | Gap: Level 1 (zero-total-mass invariant for a time-varying tracker innovation response)
Proof: induct on time using the response initialization and successor recurrence; commute the finite coordinate sums and use column normalization to show that mixing preserves the coordinate sum, so every action-minus-state driver contribution cancels.
Source: Mathlib finite big operators and modules, together with `FiniteNetwork.trackerInnovationResponse_succ`
Used in: mean-gradient, oracle-noise, compression-error, and perturbation tracker recurrences whose column-normalized mixing schedule must keep a zero-initial response in the finite-network zero-sum subspace
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem trackerInnovationResponse_sum_eq_zero
    {R Node E : Type*} [Fintype Node] [Semiring R]
    [AddCommGroup E] [Module R E]
    (C : Nat → Matrix Node Node R) (U : Nat → Node → E) (t : Nat)
    (hC : ∀ k j, ∑ i, C k i j = 1) :
    ∑ i : Node, trackerInnovationResponse C U t i = 0 := by
  induction t with
  | zero =>
      rw [trackerInnovationResponse_zero]
      simp
  | succ t ih =>
      rw [trackerInnovationResponse_succ]
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      have hsum (X : Node → E) :
          ∑ i : Node, Matrix.smulVec (C t) X i = ∑ j : Node, X j := by
        simp only [Matrix.smulVec_apply]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, hC t j, one_smul]
      rw [hsum, hsum, ih]
      simp

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_norm_weightedState_sub_weightedState_le_pairwiseDiameter`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: distance between two finite normalized nonnegative weighted states bounded by the pairwise diameter; orig was `norm_weightedState_sub_weightedState_le_statePairwiseDiameter`.
-- generality used: arbitrary finite index type and real seminormed module; no nonemptiness, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or stochastic-matrix assumptions.
-- portable call pattern: consensus, gossip, push-sum, and decentralized averaging proofs change the finite carrier, state space, two probability rows, and state family while reusing the same diameter bound between their barycenters.
-- counterargument checked: not paper-local or a one-line wrapper because it packages the product-coupling expansion and two normalization arguments; Mathlib's convex-hull diameter API is only a component route and does not state this normalized-weight contract directly.
-- coverage search: `lean_search_symbols` queries "norm convex combinations finite family bounded by pairwise diameter nonnegative weights sum one", "weighted state barycenter distance less than diameter probability weights", and "two weighted sums norm difference pairwise diameter" found only the source-local theorem and unrelated weighted estimates; `lean_leansearch` found `convexHull_exists_dist_ge2`, `Metric.dist_le_diam_of_mem`, and `EuclideanGeometry.dist_affineCombination`, none with the complete nonnegative normalized-weight conclusion. The previously staged `FiniteNetwork.statePairwiseDiameter` was rejected in favor of Mathlib's `Metric.diam`, which is used directly here.
-- minimal hypotheses: `[Fintype iota]` makes `Set.range X` finite and bounded; no `Nonempty iota` instance is needed because the two unit-mass hypotheses already exclude an inhabited call on an empty carrier. `[SeminormedAddCommGroup E] [NormedSpace Real E]` are exactly the subtraction, finite-sum, scalar-action, and norm assumptions used by the proof.

/-- The distance between two normalized nonnegative weighted states of a finite
family is at most the diameter of that family's range.

Layer: Model | Gap: Level 1 (finite barycenter distance bounded by pairwise diameter)
Proof: rewrite the barycenter difference as the product coupling with weights `p i * q j`, apply the norm triangle inequality and the range-diameter bound pointwise, then collapse the double sum using both unit-mass hypotheses.
Source: Mathlib finite-sum norm inequalities and `Metric.dist_le_diam_of_mem` for finite bounded ranges
Used in: Dobrushin contraction and consensus-error estimates for row-stochastic network updates, comparing two node rows as probability weights on the same distributed state
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem norm_sum_smul_sub_sum_smul_le_diam_range
    {iota E : Type*} [Fintype iota]
    [SeminormedAddCommGroup E] [NormedSpace Real E]
    (p q : iota -> Real)
    (hp : forall i : iota, 0 <= p i) (hq : forall i : iota, 0 <= q i)
    (hp_sum : ∑ i : iota, p i = 1) (hq_sum : ∑ i : iota, q i = 1)
    (X : iota -> E) :
    ‖(∑ i : iota, p i • X i) - ∑ i : iota, q i • X i‖ <=
      Metric.diam (Set.range X) := by
  classical
  have hrewrite :
      (∑ i : iota, p i • X i) - ∑ i : iota, q i • X i =
        ∑ i : iota, ∑ j : iota, (p i * q j) • (X i - X j) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    have hfirst : (∑ i : iota, p i • X i) =
        ∑ i : iota, ∑ j : iota, (p i * q j) • X i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_smul, ← Finset.mul_sum, hq_sum, mul_one]
    have hsecond : (∑ j : iota, q j • X j) =
        ∑ i : iota, ∑ j : iota, (p i * q j) • X j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_smul, ← Finset.sum_mul, hp_sum, one_mul]
    rw [hfirst, hsecond]
  rw [hrewrite]
  calc
    ‖∑ i : iota, ∑ j : iota, (p i * q j) • (X i - X j)‖ <=
        ∑ i : iota, ‖∑ j : iota, (p i * q j) • (X i - X j)‖ :=
      norm_sum_le _ _
    _ <= ∑ i : iota, ∑ j : iota, ‖(p i * q j) • (X i - X j)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ = ∑ i : iota, ∑ j : iota, (p i * q j) * ‖X i - X j‖ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hp i) (hq j))]
    _ <= ∑ i : iota, ∑ j : iota,
        (p i * q j) * Metric.diam (Set.range X) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (by
          simpa only [dist_eq_norm] using
            Metric.dist_le_diam_of_mem (Set.finite_range X).isBounded
              (Set.mem_range_self i) (Set.mem_range_self j))
        (mul_nonneg (hp i) (hq j))
    _ = Metric.diam (Set.range X) := by
      have hinner (i : iota) :
          (∑ j : iota, (p i * q j) * Metric.diam (Set.range X)) =
            p i * Metric.diam (Set.range X) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hq_sum, mul_one]
      simp_rw [hinner]
      rw [← Finset.sum_mul, hp_sum, one_mul]

end FiniteNetwork

/-! Phase 4 batch 4: `Module_End_IsSimpleIsolatedDominantEigenpair_outerProjection_isRankOneRieszProjectionAt`. -/


-- Generalization plan (G0):
-- concept/name: rank-one Riesz projection from a normalized simple isolated dominant
--   eigenpair; orig was normalized_unit_outer_product_isUnitRieszProjection_at_base
-- generality used: a complex module, an endomorphism, an
--   arbitrary distinguished eigenvalue, a spectral-radius bound, and normalized
--   right and algebraic-dual left eigenvectors
-- portable call pattern: analytic perturbation, finite Markov-chain, and distributed
--   operator proofs construct the dominant Riesz projector while varying the operator,
--   eigenvalue, spectral gap, and eigenvectors
-- counterargument checked: this is not a unit-eigenvalue notation wrapper; it composes
--   idempotence, two eigenprojection relations, fixed-space identification, and spectral
--   isolation, and no Mathlib or SOptLib declaration supplies that combined constructor
-- coverage search: searched “rank one Riesz projection outer product simple isolated
--   eigenpair”, “outer projection is Riesz projection at eigenvalue normalized left
--   right eigenvectors”, and exact concept names; hits were paper-local source predicates,
--   Matrix.vecMulVec algebra, and contour-projection results, none with this contract
-- minimal hypotheses: normalization implies both factors are nonzero; eigenspace
--   spanning is used only for fixed-space identification; the strict radius gap and
--   competing-eigenvalue bound are used only for isolation

/-- A right eigenvector is algebraically simple when it spans its eigenspace and the
corresponding eigenvalue admits no generalized eigenvector chain of length two.

Layer: Model | Concept: algebraically simple eigenpair
Proof: (definitional construction; one-dimensional eigenspace and absence of a length-two Jordan chain)
Source: Mathlib linear-algebra eigenspaces and generalized eigenvector chains
Used in: spectral perturbation arguments that identify the fixed space of a normalized outer-product projector
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def IsAlgebraicallySimpleEigenpair {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (right : V) : Prop :=
  (∀ v : V, A v = lambda • v → ∃ c : ℂ, v = c • right) ∧
    ∀ v : V, A (A v - lambda • v) = lambda • (A v - lambda • v) →
      A v = lambda • v

@[simp] theorem IsAlgebraicallySimpleEigenpair_def {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (right : V) :
    IsAlgebraicallySimpleEigenpair A lambda right ↔
      (∀ v : V, A v = lambda • v → ∃ c : ℂ, v = c • right) ∧
        ∀ v : V, A (A v - lambda • v) = lambda • (A v - lambda • v) →
          A v = lambda • v := Iff.rfl

theorem IsAlgebraicallySimpleEigenpair.eq_smul_of_mem_eigenspace
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {right v : V}
    (h : IsAlgebraicallySimpleEigenpair A lambda right)
    (hv : v ∈ Module.End.eigenspace A lambda) :
    ∃ c : ℂ, v = c • right :=
  h.1 v (Module.End.mem_eigenspace_iff.mp hv)

theorem IsAlgebraicallySimpleEigenpair.eq_of_residual_mem_eigenspace
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {right v : V}
    (h : IsAlgebraicallySimpleEigenpair A lambda right)
    (hv : A (A v - lambda • v) = lambda • (A v - lambda • v)) :
    A v = lambda • v :=
  h.2 v hv

/-- An endomorphism projector is the spectral projector at an isolated eigenvalue when
it has the two eigenprojection relations, exactly fixes that eigenspace, and admits a
spectral separating circle.

Layer: Model | Concept: isolated eigenprojection
Proof: (definitional construction; commuting eigenprojection laws, fixed-space characterization, and a separating circle)
Source: Mathlib endomorphism eigenspaces and complex normed-space spectral separation
Used in: perturbation and stable-complement proofs that consume the algebraic surface of a Riesz projector
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def Module.End.IsIsolatedEigenprojection {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (P : Module.End ℂ V) : Prop :=
  A * P = lambda • P ∧
    P * A = lambda • P ∧
      (∀ x : V, P x = x ↔ A x = lambda • x) ∧
        ∃ radius : ℝ, 0 < radius ∧
          ∀ z : ℂ, ‖z - lambda‖ = radius → ¬ A.HasEigenvalue z

@[simp] theorem Module.End.IsIsolatedEigenprojection_def {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (P : Module.End ℂ V) :
    A.IsIsolatedEigenprojection lambda P ↔
      A * P = lambda • P ∧
        P * A = lambda • P ∧
          (∀ x : V, P x = x ↔ A x = lambda • x) ∧
            ∃ radius : ℝ, 0 < radius ∧
              ∀ z : ℂ, ‖z - lambda‖ = radius → ¬ A.HasEigenvalue z := Iff.rfl

theorem Module.End.IsIsolatedEigenprojection.left_mul_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsIsolatedEigenprojection lambda P) :
    A * P = lambda • P :=
  h.1

theorem Module.End.IsIsolatedEigenprojection.right_mul_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsIsolatedEigenprojection lambda P) :
    P * A = lambda • P :=
  h.2.1

theorem Module.End.IsIsolatedEigenprojection.apply_eq_self_iff
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsIsolatedEigenprojection lambda P) (x : V) :
    P x = x ↔ A x = lambda • x :=
  h.2.2.1 x

theorem Module.End.IsIsolatedEigenprojection.exists_separating_circle
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsIsolatedEigenprojection lambda P) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, ‖z - lambda‖ = radius → ¬ A.HasEigenvalue z :=
  h.2.2.2

/-- A rank-one Riesz projector is an isolated eigenprojection with a normalized
left-right outer-product representation.

Layer: Model | Concept: rank-one Riesz projection at an eigenvalue
Proof: (definitional construction; normalized rank-one idempotent paired with an isolated eigenprojection)
Source: Mathlib linear maps, algebraic duals, eigenspaces, and spectral projection theory
Used in: dominant-mode decompositions for perturbed operators, Markov kernels, and distributed linear dynamics
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def Module.End.IsRankOneRieszProjectionAt {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (P : Module.End ℂ V) : Prop :=
  (P * P = P ∧
      ∃ right : V, ∃ left : Module.Dual ℂ V,
        right ≠ 0 ∧ left ≠ 0 ∧ left right = 1 ∧
          ∀ x : V, P x = left x • right) ∧
    A.IsIsolatedEigenprojection lambda P

@[simp] theorem Module.End.IsRankOneRieszProjectionAt_def {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (P : Module.End ℂ V) :
    A.IsRankOneRieszProjectionAt lambda P ↔
      (P * P = P ∧
          ∃ right : V, ∃ left : Module.Dual ℂ V,
            right ≠ 0 ∧ left ≠ 0 ∧ left right = 1 ∧
              ∀ x : V, P x = left x • right) ∧
        A.IsIsolatedEigenprojection lambda P := Iff.rfl

theorem Module.End.IsRankOneRieszProjectionAt.idempotent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsRankOneRieszProjectionAt lambda P) :
    P * P = P :=
  h.1.1

theorem Module.End.IsRankOneRieszProjectionAt.exists_normalized_outer_product
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsRankOneRieszProjectionAt lambda P) :
    ∃ right : V, ∃ left : Module.Dual ℂ V,
      right ≠ 0 ∧ left ≠ 0 ∧ left right = 1 ∧
        ∀ x : V, P x = left x • right :=
  h.1.2

theorem Module.End.IsRankOneRieszProjectionAt.is_isolated_eigenprojection
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda : ℂ} {P : Module.End ℂ V}
    (h : A.IsRankOneRieszProjectionAt lambda P) :
    A.IsIsolatedEigenprojection lambda P :=
  h.2

/-- A normalized simple dominant eigenpair packages a spectral-radius gap together
with compatible right and left eigenvectors and algebraic simplicity.

Layer: Model | Concept: simple isolated dominant eigenpair
Proof: (definitional construction; normalized left-right eigenpair, algebraic simplicity, and a competing-spectrum radius bound)
Source: Mathlib endomorphism eigenvalues, algebraic duals, and complex normed-space spectrum
Used in: finite-dimensional perturbation, Markov-chain stationary-mode, and distributed-operator spectral splittings
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def Module.End.IsSimpleIsolatedDominantEigenpair {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda0 : ℂ) (r0 : ℝ)
    (right : V) (left : Module.Dual ℂ V) : Prop :=
  0 ≤ r0 ∧ r0 < ‖lambda0‖ ∧
    A right = lambda0 • right ∧
      left ∘ₗ A = lambda0 • left ∧
        left right = 1 ∧
          IsAlgebraicallySimpleEigenpair A lambda0 right ∧
            ∀ mu : ℂ, A.HasEigenvalue mu → mu ≠ lambda0 → ‖mu‖ ≤ r0

@[simp] theorem Module.End.IsSimpleIsolatedDominantEigenpair_def {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda0 : ℂ) (r0 : ℝ)
    (right : V) (left : Module.Dual ℂ V) :
    A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left ↔
      0 ≤ r0 ∧ r0 < ‖lambda0‖ ∧
        A right = lambda0 • right ∧
          left ∘ₗ A = lambda0 • left ∧
            left right = 1 ∧
              IsAlgebraicallySimpleEigenpair A lambda0 right ∧
                ∀ mu : ℂ, A.HasEigenvalue mu → mu ≠ lambda0 → ‖mu‖ ≤ r0 := Iff.rfl

theorem Module.End.IsSimpleIsolatedDominantEigenpair.radius_nonneg
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left) :
    0 ≤ r0 :=
  h.1

theorem Module.End.IsSimpleIsolatedDominantEigenpair.radius_lt_norm
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left) :
    r0 < ‖lambda0‖ :=
  h.2.1

theorem Module.End.IsSimpleIsolatedDominantEigenpair.right_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left) :
    A right = lambda0 • right :=
  h.2.2.1

theorem Module.End.IsSimpleIsolatedDominantEigenpair.left_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left) :
    left ∘ₗ A = lambda0 • left :=
  h.2.2.2.1

theorem Module.End.IsSimpleIsolatedDominantEigenpair.normalized
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left) :
    left right = 1 :=
  h.2.2.2.2.1

theorem Module.End.IsSimpleIsolatedDominantEigenpair.algebraically_simple
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left) :
    IsAlgebraicallySimpleEigenpair A lambda0 right :=
  h.2.2.2.2.2.1

theorem Module.End.IsSimpleIsolatedDominantEigenpair.eigenvalue_norm_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    {right : V} {left : Module.Dual ℂ V}
    (h : A.IsSimpleIsolatedDominantEigenpair lambda0 r0 right left)
    {mu : ℂ} (hmu : A.HasEigenvalue mu) (hne : mu ≠ lambda0) :
    ‖mu‖ ≤ r0 :=
  h.2.2.2.2.2.2 mu hmu hne

/-- A dominant spectral-radius gap supplies a circle separating the distinguished
eigenvalue from every other eigenvalue.

Layer: Model | Gap: Level 1 (separating circle from a dominant spectral-radius gap)
Proof: choose half the gap between `‖lambda0‖` and `r0`; the reverse triangle inequality and the competing-spectrum bound exclude eigenvalues on that circle.
Source: Mathlib complex norms, endomorphism eigenvalues, and the norm triangle inequality
Used in: Riesz-projector construction at the base point of analytic operator perturbations and dominant-mode splittings
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Module.End.IsSimpleIsolatedDominantEigenpair.exists_separating_circle
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {A : Module.End ℂ V} {lambda0 : ℂ} {r0 : ℝ}
    (hr0_lt : r0 < ‖lambda0‖)
    (hstable : ∀ mu : ℂ, A.HasEigenvalue mu → mu ≠ lambda0 → ‖mu‖ ≤ r0) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, ‖z - lambda0‖ = radius → ¬ A.HasEigenvalue z := by
  refine ⟨(‖lambda0‖ - r0) / 2, by linarith, ?_⟩
  intro z hz heigen
  have hz_ne : z ≠ lambda0 := by
    intro hzl
    subst z
    simp at hz
    linarith
  have hz_norm : ‖z‖ ≤ r0 := hstable z heigen hz_ne
  have htriangle : ‖lambda0‖ ≤ ‖z‖ + ‖z - lambda0‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le z (z - lambda0)
  rw [hz] at htriangle
  linarith

/-- The normalized outer product of a simple isolated dominant left-right eigenpair
is its rank-one Riesz projection at the distinguished eigenvalue.

Layer: Model | Gap: Level 2 (outer-product construction of a rank-one Riesz projector)
Proof: normalization gives an idempotent nonzero rank-one outer product; the left and right eigenrelations give commutation, algebraic simplicity identifies its fixed space, and the spectral gap supplies a separating circle.
Source: Mathlib linear-map composition, scalar-valued linear maps, endomorphism eigenspaces, and complex norm inequalities
Used in: the base-point projector step of analytic perturbation proofs and dominant slow-mode splittings for Markov and distributed operators
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Module.End.IsSimpleIsolatedDominantEigenpair.outer_projection_is_rank_one_riesz_projection_at
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda0 : ℂ) (r0 : ℝ)
    (right : V) (left : Module.Dual ℂ V)
    (hr0_lt : r0 < ‖lambda0‖)
    (hright : A right = lambda0 • right)
    (hleft : left ∘ₗ A = lambda0 • left)
    (hnormalized : left right = 1)
    (hspans : ∀ v : V, A v = lambda0 • v → ∃ c : ℂ, v = c • right)
    (hstable : ∀ mu : ℂ, A.HasEigenvalue mu → mu ≠ lambda0 → ‖mu‖ ≤ r0) :
    A.IsRankOneRieszProjectionAt lambda0 (LinearMap.smulRight left right) := by
  have hright_ne : right ≠ 0 := by
    intro hzero
    subst right
    simp at hnormalized
  have hleft_ne : left ≠ 0 := by
    intro hzero
    subst left
    simp at hnormalized
  let P : Module.End ℂ V := LinearMap.smulRight left right
  have hP_apply (x : V) : P x = left x • right := rfl
  have hP_idem : P * P = P := by
    ext x
    rw [Module.End.mul_apply, hP_apply, hP_apply, map_smul, hnormalized,
      smul_eq_mul, mul_one]
  have hAP : A * P = lambda0 • P := by
    ext x
    rw [Module.End.mul_apply, hP_apply, map_smul, hright,
      LinearMap.smul_apply, hP_apply, smul_smul, smul_smul]
    rw [mul_comm]
  have hPA : P * A = lambda0 • P := by
    ext x
    have hleft_x : left (A x) = lambda0 * left x := by
      simpa [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] using
        LinearMap.congr_fun hleft x
    rw [Module.End.mul_apply, hP_apply, hleft_x, LinearMap.smul_apply,
      hP_apply, smul_smul]
  have hfixed : ∀ x : V, P x = x ↔ A x = lambda0 • x := by
    intro x
    constructor
    · intro hPx
      calc
        A x = A (P x) := by rw [hPx]
        _ = (A * P) x := by rw [Module.End.mul_apply]
        _ = (lambda0 • P) x := by rw [hAP]
        _ = lambda0 • x := by rw [LinearMap.smul_apply, hPx]
    · intro hx
      obtain ⟨c, rfl⟩ := hspans x hx
      rw [hP_apply, map_smul, hnormalized, smul_eq_mul, mul_one]
  refine ⟨⟨hP_idem, right, left, hright_ne, hleft_ne, hnormalized, ?_⟩,
    hAP, hPA, hfixed, ?_⟩
  · exact hP_apply
  · exact Module.End.IsSimpleIsolatedDominantEigenpair.exists_separating_circle
      hr0_lt hstable

/-! Phase 4 batch 4: `Module_End_IsSimpleIsolatedDominantEigenpair_exists_strictly_separating_circle`. -/


-- Generalization plan (G0):
-- concept/name: strict separating circle supplied by a dominant spectral-radius gap; orig was exists_unit_spectral_separating_circle_strong.
-- generality used: an endomorphism of a module over any commutative ring whose additive group is normed, a distinguished scalar, and a real competing-spectrum bound; no topology or norm on the carrier, finite dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: finite-dimensional perturbation, consensus, and Markov-operator arguments vary the endomorphism, distinguished eigenvalue, and stable spectral radius while reusing the same half-gap contour and strict exclusion estimate.
-- counterargument checked: the existing `exists_separating_circle` is only partial coverage because it exports boundary avoidance but neither bounds the chosen radius by the spectral gap nor gives strict distance for every competing eigenvalue.
-- coverage search: lean_search_symbols queries "dominant eigenvalue spectral gap circle boundary avoidance strict norm separation" and "strict distance lower bound competing eigenvalue dominant spectral radius gap" found the weaker `Module.End.IsSimpleIsolatedDominantEigenpair.exists_separating_circle` and unrelated finite-matrix disk predicates; LeanSearch found spectral-radius APIs but no theorem with the combined radius bound and strict separation conclusion.
-- minimal hypotheses: only `r0 < ‖lambda0‖` and the pointwise norm bound on non-distinguished eigenvalues are used; algebraic simplicity, eigenvectors, carrier norms, and finite dimensionality are unnecessary.

/-- A dominant spectral-radius gap supplies a circle strictly separating the
distinguished eigenvalue from every competing eigenvalue.

The half-gap radius is positive, is smaller than the full radial gap, avoids
the spectrum on its boundary, and is strictly below the distance from the
distinguished eigenvalue to every other eigenvalue.

Layer: Glue | Gap: Level 1 (strict separating circle from a dominant spectral-radius gap)
Proof: choose half the gap `‖lambda0‖ - r0`; the norm triangle inequality and the pointwise competing-spectrum bound give strict radial separation, which also excludes eigenvalues from the boundary.
Source: Mathlib complex norm triangle inequalities and endomorphism eigenspaces, extending the companion dominant-eigenpair separating-circle theorem
Used in: choosing a fixed contour for analytic operator perturbations while retaining the strict interior-exclusion estimate needed to keep every competing spectral mode outside the contour
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Module.End.exists_strictly_separating_circle_of_eigenvalue_norm_le
    {𝕜 : Type*} [CommRing 𝕜] [SeminormedAddCommGroup 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {A : Module.End 𝕜 V} {lambda0 : 𝕜} {r0 : ℝ}
    (hr0_lt : r0 < ‖lambda0‖)
    (hstable :
      ∀ mu : 𝕜, A.HasEigenvalue mu → mu ≠ lambda0 → ‖mu‖ ≤ r0) :
    ∃ radius : ℝ, 0 < radius ∧ radius < ‖lambda0‖ - r0 ∧
      (∀ z : 𝕜, ‖z - lambda0‖ = radius → ¬ A.HasEigenvalue z) ∧
      (∀ z : 𝕜, A.HasEigenvalue z → z ≠ lambda0 →
        radius < ‖z - lambda0‖) := by
  refine ⟨(‖lambda0‖ - r0) / 2, by linarith, by linarith, ?_, ?_⟩
  · intro z hz heigen
    have hz_ne : z ≠ lambda0 := by
      intro hzl
      subst z
      simp at hz
      linarith
    have hz_norm : ‖z‖ ≤ r0 := hstable z heigen hz_ne
    have htriangle : ‖lambda0‖ ≤ ‖z‖ + ‖z - lambda0‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le z (z - lambda0)
    rw [hz] at htriangle
    linarith
  · intro z heigen hz_ne
    have hz_norm : ‖z‖ ≤ r0 := hstable z heigen hz_ne
    have htriangle : ‖lambda0‖ ≤ ‖z‖ + ‖z - lambda0‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le z (z - lambda0)
    linarith

/-! Phase 4 batch 4: `FiniteNetwork_normalizedCoordinateError`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: normalized coordinate error of a finite weight vector; orig was `perronCoordinateError`.
-- generality used: arbitrary finite node type and coordinate type with an additive commutative group and a distinguished one, a weight vector, a selected node, and only the normalization equality that its coordinates sum to one; no positivity, order, multiplication, stochastic-matrix, periodicity, Perron, normed-space, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: Markov-chain, consensus, push-sum, and gradient-tracking proofs change the normalized weight vector and selected node while reusing the same zero-total-mass coordinate-centering construction.
-- counterargument checked: although the formula is short, it is not merely paper-local traceability or a caller-side expression because it canonically packages a normalized vector minus a coordinate unit vector in the reusable `ZeroSumState` invariant domain and exposes that construction through a specification theorem.
-- coverage search: `lean_search_symbols` queries "normalized finite weight vector minus coordinate unit vector zero sum state", "probability weights sub single coordinate indicator sum zero", and "FiniteNetwork normalizedCoordinateError coordinate error ZeroSumState" found only the source declaration, `FiniteNetwork.ZeroSumState`, and unrelated normalization results; LeanSearch found `Fintype.sum_ite_eq'`, `stdSimplex`, and `Pi.basisFun`, which supply components but not this zero-sum-state construction.
-- minimal hypotheses: `[Fintype Node]` forms the coordinate sum, `[DecidableEq Node]` selects the unit coordinate, `[AddCommGroup R]` supplies finite-sum subtraction and zero, `[One R]` supplies the unit coordinate's value, and `hsum` is exactly the normalization equality consumed by the proof; source positivity, nonemptiness, Perron dynamics, and ambient optimization-space assumptions are dropped.

/-- Subtracting a selected coordinate unit vector from a normalized finite
weight vector gives a zero-sum network state.

Layer: Model | Concept: normalized finite-network coordinate error
Proof: (definitional construction; pointwise subtraction of a Kronecker coordinate unit vector, with zero-sum membership proved from the supplied unit-mass normalization)
Source: Mathlib finite-type sums, subtraction over finite sums, and `Fintype.sum_ite_eq'`, together with SOptLib's finite-network zero-sum-state subtype
Used in: Markov, consensus, push-sum, and gradient-tracking influence arguments that center a normalized stationary or Perron weight vector at a selected node before applying a zero-sum contraction or corrected lift
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def normalizedCoordinateError
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [AddCommGroup R] [One R]
    (v : Node → R) (i : Node) (hsum : ∑ k : Node, v k = 1) :
    ZeroSumState Node R :=
  ⟨fun k : Node => v k - if k = i then 1 else 0, by
    rw [Finset.sum_sub_distrib, hsum, Fintype.sum_ite_eq', sub_self]⟩

/-- The normalized coordinate error unfolds to subtraction of the selected
coordinate unit vector. -/
@[simp] theorem normalizedCoordinateError_def
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [AddCommGroup R] [One R]
    (v : Node → R) (i : Node) (hsum : ∑ j : Node, v j = 1) :
    (normalizedCoordinateError v i hsum : Node → R) =
      fun k => v k - if k = i then 1 else 0 := by
  rfl

/-- The normalized coordinate error is pointwise the weight vector minus the
selected coordinate unit vector.

Layer: Model | Gap: Level 0 (pointwise specification of normalized finite-network coordinate error)
Proof: by rfl after unfolding `FiniteNetwork.normalizedCoordinateError`.
Source: Mathlib function subtypes and pointwise finite-vector operations
Used in: rewriting a normalized stationary-weight coordinate error into its explicit Perron-weight-minus-indicator formula inside corrected-lift and influence-coordinate calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem normalizedCoordinateError_apply
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [AddCommGroup R] [One R]
    (v : Node → R) (i k : Node) (hsum : ∑ j : Node, v j = 1) :
    (normalizedCoordinateError v i hsum : Node → R) k =
      v k - if k = i then 1 else 0 := by
  rfl

/-- The normalized coordinate error vanishes exactly when the weight vector is
the selected coordinate unit vector. -/
theorem normalizedCoordinateError_eq_zero_iff
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [AddCommGroup R] [One R]
    (v : Node → R) (i : Node) (hsum : ∑ j : Node, v j = 1) :
    normalizedCoordinateError v i hsum = 0 ↔
      v = fun k => if k = i then 1 else 0 := by
  constructor
  · intro h
    funext k
    have hk := congrArg
      (fun W : ZeroSumState Node R => (W : Node → R) k) h
    simpa only [normalizedCoordinateError_apply, ZeroSumState.coe_zero,
      Pi.zero_apply, sub_eq_zero] using hk
  · intro h
    apply Subtype.ext
    funext k
    simp [h]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_perronResidual`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network Perron residual; orig was `perronResidual`.
-- generality used: arbitrary scalar semiring, finite node carrier, additive commutative group carrying a module structure, node weights, and a node-valued state; no nonempty-node, topology, norm, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, stochasticity, positivity, or weight-normalization assumptions are needed to define the residual.
-- portable call pattern: directed consensus, push-sum, push-pull, and gradient-tracking proofs change the Perron or absolute-probability weight and the node-valued state while using the same disagreement residual from the weight-scaled reconstruction of total state mass.
-- counterargument checked: although the body is one formula, this is not merely paper-local traceability or a caller-side abbreviation: the rank-one Perron residual is a standard recurring state object, and naming it gives matrix-action, zero-sum, and norm estimates a shared Model-level interface.
-- coverage search: lean_search_symbols queries "finite network Perron weighted disagreement residual state minus weight times total mass", "state subtract weighted reconstruction total sum node", and "Perron residual definition weighted disagreement state minus weight scalar total sum" found related weighted-state, normalized-coordinate-error, and residual-centering theorems but no definition with this statement shape; LeanSearch for "finite function residual from weighted reconstruction of its sum" timed out, while the inspected Mathlib finite-sum/module APIs provide only the construction ingredients.
-- minimal hypotheses: `[Fintype Node]` supplies the total finite sum, `[Semiring R] [AddCommGroup E] [Module R E]` supply exactly scalar multiplication and subtraction, and neither normalization of the weights nor nonemptiness of the node type is needed by the definition.

/-- The Perron residual of a finite-network state subtracts from each node the
weight-scaled reconstruction of the state's total mass.

For weights `v : Node → R` and state `W : Node → E`, the coordinate at `i` is
`W i - v i • ∑ j, W j`, corresponding to the rank-one residual
`(I - v 1ᵀ) W`.

Layer: Model | Concept: finite-network Perron disagreement residual
Proof: (definitional construction; pointwise subtraction of the weight-scaled finite total state mass)
Source: finite-state nonhomogeneous Markov-chain Perron projections and Mathlib finite module-valued sums
Used in: directed push-pull and gradient-tracking analyses that isolate tracker disagreement from the instantaneous Perron reconstruction before zero-sum and contraction estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def perronResidual
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (v : Node → R) (W : Node → E) : Node → E :=
  fun i => W i - v i • ∑ j : Node, W j

/-- The finite-network Perron residual is the pointwise difference between the
state and its weight-scaled total-mass reconstruction.

Layer: Model | Gap: Level 0 (finite-network Perron residual unfolding)
Proof: by rfl after unfolding `FiniteNetwork.perronResidual`.
Source: finite-state nonhomogeneous Markov-chain Perron projections and Mathlib finite module-valued sums
Used in: rewriting the named disagreement state as a node function before extensional matrix-action and zero-total-mass arguments
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem perronResidual_def
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (v : Node → R) (W : Node → E) :
    perronResidual v W = fun i => W i - v i • ∑ j : Node, W j := by
  rfl

/-- The finite-network Perron residual unfolds coordinatewise to the state
minus the weight-scaled total state mass.

Layer: Model | Gap: Level 0 (finite-network Perron residual coordinate specification)
Proof: by rfl after unfolding `FiniteNetwork.perronResidual`.
Source: finite-state nonhomogeneous Markov-chain Perron projections and Mathlib finite module-valued sums
Used in: rewriting a named directed-network disagreement state into coordinates for zero-total-mass identities and matrix-action recurrences
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem perronResidual_apply
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (v : Node → R) (W : Node → E) (i : Node) :
    perronResidual v W i = W i - v i • ∑ j : Node, W j := by
  rfl

/-- A normalized Perron residual has zero total mass.

Layer: Model | Gap: Level 0 (finite-network Perron residual mass cancellation)
Proof: sum the pointwise residual, factor the common total state mass, and use
  normalization of the node weights.
Source: finite-state Perron projections and Mathlib finite module-valued sums
Used in: directed push-pull and gradient-tracking arguments that restrict the
  tracker disagreement to the zero-sum state subspace -/
theorem perronResidual_sum_eq_zero
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (v : Node → R) (W : Node → E) (hv : ∑ i : Node, v i = 1) :
    ∑ i : Node, perronResidual v W i = 0 := by
  simp only [perronResidual_apply, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, hv, one_smul, sub_self]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_initialGradientHeterogeneity`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: initial gradient heterogeneity measured by the finite-product L2 norm of a Perron residual; orig was `initialGradientHeterogeneity`.
-- generality used: arbitrary finite node carrier, real seminormed module, node weight, and initial node-indexed gradient table; no compatibility between the seminorm and scalar multiplication, weight normalization, positivity, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or stochasticity assumptions are used.
-- portable call pattern: directed push-pull, push-sum gradient tracking, and decentralized gradient methods change the initial local-gradient table and Perron weight while retaining the same scalar initial-heterogeneity term in convergence constants.
-- counterargument checked: although definitionally composed from a Perron residual and finite-product energy, this is not paper-local bookkeeping because initial gradient heterogeneity is a standard named initialization parameter used as a stable scalar boundary in directed distributed-optimization estimates; the paired formula theorem exposes its interaction with both existing objects.
-- coverage search: `lean_search_symbols` queries "finite network initial gradient heterogeneity Frobenius norm Perron residual local gradient table", "square root sum squared norms residual weighted finite node state", and "finite dependent product L2 norm square root sum squared norms definition" found the source declaration, `FiniteNetwork.perronResidual`, and `SOptLib.dependentProductNormSq`, but no declaration naming their heterogeneity composition; Mathlib LeanSearch returned no matching semantic result.
-- minimal hypotheses: `[Fintype Node]` forms the finite residual energy, while `[SeminormedAddCommGroup E] [Module Real E]` give exactly the subtraction, scalar action, and seminorm used in the formula; compatibility between scalar multiplication and the seminorm is not needed, and all stronger source assumptions were removed.

/-- The initial gradient heterogeneity is the finite-product L2 norm of the
Perron residual of an initial node-indexed gradient table.

For a node weight `v` and initial table `G0`, this is
`sqrt (sum_i ‖G0_i - v_i • sum_j G0_j‖²)`.

Layer: Model | Concept: directed finite-network initial gradient heterogeneity
Proof: (definitional construction; real square root of the SOptLib finite dependent-product squared norm energy of a Perron residual)
Source: finite-state Perron disagreement projections, Mathlib seminormed real modules, and SOptLib finite dependent-product squared norm energy
Used in: directed push-pull and gradient-tracking convergence bounds whose initialization term measures disagreement of the initial local-gradient table from its Perron reconstruction
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def initialGradientHeterogeneity
    {Node E : Type*} [Fintype Node]
    [SeminormedAddCommGroup E] [Module Real E]
    (v : Node -> Real) (G0 : Node -> E) : Real :=
  Real.sqrt (SOptLib.dependentProductNormSq (perronResidual v G0))

/-- Initial gradient heterogeneity unfolds to the square root of the sum of
squared norms of the Perron-residual coordinates.

Layer: Model | Gap: Level 0 (initial gradient heterogeneity formula)
Proof: by rfl after unfolding `FiniteNetwork.initialGradientHeterogeneity` and `SOptLib.dependentProductNormSq` through definitional equality.
Source: finite-state Perron disagreement projections, Mathlib finite sums and norms, and SOptLib finite dependent-product squared norm energy
Used in: rewriting the named initial heterogeneity constant into the Frobenius-style residual formula used by directed gradient-tracking initialization estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem initialGradientHeterogeneity_def
    {Node E : Type*} [Fintype Node]
    [SeminormedAddCommGroup E] [Module Real E]
    (v : Node -> Real) (G0 : Node -> E) :
    initialGradientHeterogeneity v G0 =
      Real.sqrt (∑ i : Node, ‖perronResidual v G0 i‖ ^ 2) := by
  rfl

/-- Initial gradient heterogeneity is nonnegative.

Layer: Model | Gap: Level 0 (initial gradient heterogeneity nonnegativity)
Proof: by nonnegativity of the real square root.
Source: Mathlib real square-root order API
Used in: directed gradient-tracking estimates that multiply or square the
  initial heterogeneity term. -/
theorem initialGradientHeterogeneity_nonneg
    {Node E : Type*} [Fintype Node]
    [SeminormedAddCommGroup E] [Module Real E]
    (v : Node -> Real) (G0 : Node -> E) :
    0 ≤ initialGradientHeterogeneity v G0 := by
  exact Real.sqrt_nonneg _

/-- Squaring initial gradient heterogeneity recovers the finite-product
squared norm energy of the Perron residual.

Layer: Model | Gap: Level 0 (initial gradient heterogeneity square formula)
Proof: unfold the named heterogeneity and cancel the square root using
  nonnegativity of finite dependent-product squared norm energy.
Source: Mathlib real square-root identities and SOptLib finite dependent-product
  energy nonnegativity
Used in: directed gradient-tracking estimates stated in squared-energy form. -/
theorem initialGradientHeterogeneity_sq
    {Node E : Type*} [Fintype Node]
    [SeminormedAddCommGroup E] [Module Real E]
    (v : Node -> Real) (G0 : Node -> E) :
    initialGradientHeterogeneity v G0 ^ 2 =
      SOptLib.dependentProductNormSq (perronResidual v G0) := by
  rw [initialGradientHeterogeneity]
  exact Real.sq_sqrt (SOptLib.dependentProductNormSq_nonneg _)

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_smulVec_perronResidual_eq_sub_rankOne_of_mulVec_eq`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: transport of a finite-network Perron residual through a matrix whose action advances the weight vector; orig was `leftMul_C_perronResidual`.
-- generality used: arbitrary scalar semiring, finite source-node carrier, arbitrary target-node carrier, additive commutative group with a module structure, a rectangular scalar matrix, consecutive weight vectors, and a module-valued source state; no decidable equality, stochasticity, normalization, positivity, topology, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: directed consensus, push-sum, push-pull, and gradient-tracking proofs supply a communication matrix and consecutive Perron or absolute-probability weights satisfying `A.mulVec v = vNext`; the matrix, weights, node carriers, and module-valued state change while the transported rank-one-residual identity stays unchanged.
-- counterargument checked: this is not paper-local traceability or a pure wrapper around `perronResidualMatrix_smulVec`; that theorem only identifies a residual matrix action, whereas this theorem composes an arbitrary matrix transition with the state residual and converts the current weight into the next weight without matrix multiplication or decidable equality.
-- coverage search: lean_search_symbols queries "matrix smulVec Perron residual equals smulVec state minus next weight total mass of mulVec weight equals next weight", "smulVec subtract rank one reconstruction of total sum mulVec equality", and "matrix action residual transport of weight vector eigenvector" found the adjacent `FiniteNetwork.perronResidualMatrix_smulVec` and raw matrix-action APIs but no transport theorem; LeanSearch for "matrix action on vector-valued function minus weight times total sum when matrix times weight equals next weight" likewise found only `Matrix.Module` and finite-sum primitives.
-- minimal hypotheses: `[Fintype Source]` is needed for the source contractions and total state mass; `[Semiring R] [AddCommGroup E] [Module R E]` are exactly the algebra used to distribute the matrix action through subtraction and reassociate scalar multiplication; the target carrier need not be finite.

/-- A matrix carrying one weight vector to another carries the corresponding
Perron residual to its action on the state minus the next-weight rank-one
reconstruction of the original state's total mass.

Layer: Model | Gap: Level 1 (matrix transport of a finite-network Perron residual)
Proof: expand `Matrix.smulVec` and `FiniteNetwork.perronResidual`, distribute the row sum through subtraction, factor the common total state mass, and rewrite the scalar row contraction with `A.mulVec v = vNext`.
Source: Mathlib finite module-valued sums, scalar-tower laws, and matrix-vector multiplication, together with `Matrix.smulVec` and `FiniteNetwork.perronResidual`
Used in: directed push-pull and gradient-tracking recurrences where a pull matrix advances the right Perron weight and the current tracker disagreement must be rewritten using the next Perron reconstruction
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem smulVec_perronResidual_eq_sub_rankOne_of_mulVec_eq
    {R Source Target E : Type*} [Semiring R] [Fintype Source]
    [AddCommGroup E] [Module R E]
    (A : Matrix Target Source R) (v : Source → R) (vNext : Target → R)
    (X : Source → E) (hAv : Matrix.mulVec A v = vNext) :
    Matrix.smulVec A (perronResidual v X) =
      Matrix.smulVec A X - fun i => vNext i • ∑ j : Source, X j := by
  funext i
  simp only [Matrix.smulVec_apply, perronResidual_apply, Pi.sub_apply,
    smul_sub, smul_smul, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul]
  change (∑ j : Source, A i j • X j) -
      Matrix.mulVec A v i • (∑ j : Source, X j) =
    (∑ j : Source, A i j • X j) -
      vNext i • ∑ j : Source, X j
  rw [hAv]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_sum_add_perronResidual_eq_zero`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: zero-total-mass stability under addition of a normalized Perron residual; orig was `meanJointCoordinate_zeroSum`.
-- generality used: arbitrary scalar semiring, finite node carrier, additive commutative group with a module action, two node-indexed states, and a normalized node-weight vector; no nonempty-node, topology, norm, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, independence, integrability, oracle, or stochastic-matrix assumptions.
-- portable call pattern: directed consensus, push-sum, push-pull, and gradient-tracking proofs change the zero-sum error state, normalized Perron vector, and node state while retaining that their joint residual has zero total mass before a zero-sum contraction is applied.
-- counterargument checked: the proof composes finite-sum additivity with `perronResidual_sum_eq_zero`, but the conclusion is a reusable invariant for the named Perron residual rather than a pure rename or paper-local expression; it packages the exact joint-state boundary repeatedly needed before restricting network dynamics to the zero-sum subspace.
-- coverage search: `lean_search_symbols` queries "finite network sum zero state plus Perron residual normalized weights sum one", "sum add perronResidual equals zero of sum weights one and sum state zero", and "zero sum state add Perron residual sum equals zero normalized weights" found `FiniteNetwork.perronResidual_sum_eq_zero` as a strict component and generic finite-sum additivity, but no declaration with the combined conclusion; LeanSearch for the full finite-network contract found no matching theorem.
-- minimal hypotheses: `[Fintype Node]` supplies the coordinate sums, `[Semiring R] [AddCommGroup E] [Module R E]` are exactly the assumptions of `perronResidual`, `he` is precisely the zero-mass premise for the added state, and `hv` is precisely the normalization consumed by `perronResidual_sum_eq_zero`.

/-- Adding a normalized Perron residual to a zero-sum finite-network state
preserves zero total mass.

Layer: Model | Gap: Level 0 (zero-sum closure for an error state plus a normalized Perron residual)
Proof: distribute the coordinate sum over addition, cancel the first summand with its zero-mass hypothesis, and cancel the second with `FiniteNetwork.perronResidual_sum_eq_zero` using weight normalization.
Source: finite-state Perron projection algebra, Mathlib finite module-valued sums, and `FiniteNetwork.perronResidual_sum_eq_zero`
Used in: directed gradient-tracking joint-coordinate estimates where a zero-sum mean tracker error is added to the instantaneous Perron residual before applying contraction on the zero-sum pull subspace
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sum_add_perronResidual_eq_zero
    {R Node E : Type*} [Semiring R] [Fintype Node]
    [AddCommGroup E] [Module R E]
    (e W : Node → E) (v : Node → R)
    (he : ∑ i : Node, e i = 0) (hv : ∑ i : Node, v i = 1) :
    ∑ i : Node, (e + perronResidual v W) i = 0 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, he,
    perronResidual_sum_eq_zero v W hv, add_zero]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_perronResidualMatrix`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network Perron residual matrix; orig was `perronResidualMatrix`.
-- generality used: arbitrary scalar ring and node carrier with decidable equality for the identity matrix; finiteness and a module-valued state are added only by the matrix-action theorem, with no normalization, positivity, stochasticity, topology, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: directed consensus, push-sum, push-pull, and gradient-tracking proofs change the right Perron or absolute-probability vector while using the same identity-minus-rank-one matrix to remove its reconstructed total-mass component before contraction and operator-norm estimates.
-- counterargument checked: this is not subsumed by the staged state-level `FiniteNetwork.perronResidual`, because downstream matrix norm and product arguments require the operator as a matrix; pairing the definition with its entry and module-valued action specifications prevents it from being a bare caller-side expression.
-- coverage search: lean_search_symbols queries "identity matrix minus outer product vector all ones row rank one residual matrix" and "Perron residual matrix identity minus rank one weight all ones matrix mulVec equals residual" found the source declaration, the distinct state-level `FiniteNetwork.perronResidual`, and unrelated rank-one matrix results; LeanSearch for "matrix identity minus the outer product of a vector and the all-ones row" found `Matrix.vecMulVec` construction lemmas but no named residual matrix.
-- minimal hypotheses: `[NonAssocRing R] [DecidableEq Node]` are exactly what the defining identity-minus-outer-product matrix uses; `[Fintype Node] [Ring R] [AddCommGroup E] [Module R E]` are required only to identify its finite matrix action on an `E`-valued state.

/-- The Perron residual matrix subtracts the rank-one reconstruction formed by
a node-weight vector and the all-ones row from the identity matrix.

For `v : Node → R`, this is the matrix `I - v 1ᵀ`; when `v` is normalized,
its action removes the `v`-weighted reconstruction of total state mass.

Layer: Model | Concept: finite-network Perron residual matrix
Proof: (definitional construction; identity matrix minus the outer product `Matrix.vecMulVec v 1`)
Source: Mathlib finite matrices and `Matrix.vecMulVec`, together with finite-state Perron projections from directed consensus theory
Used in: directed push-pull and gradient-tracking recurrences that apply `I - v_t 1ᵀ` to gradient-table increments before zero-sum contraction and operator-norm estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def perronResidualMatrix
    {R Node : Type*} [NonAssocRing R] [DecidableEq Node]
    (v : Node → R) : Matrix Node Node R :=
  (1 : Matrix Node Node R) - Matrix.vecMulVec v 1

/-- The Perron residual matrix unfolds to the identity minus the outer product
of its node-weight vector with the all-ones row.

Layer: Model | Gap: Level 0 (finite-network Perron residual matrix unfolding)
Proof: by rfl after unfolding `FiniteNetwork.perronResidualMatrix`.
Source: Mathlib identity matrices, pointwise matrix subtraction, and `Matrix.vecMulVec`
Used in: matrix-product and operator-norm calculations that need the rank-one formula for the directed-network residual operator
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem perronResidualMatrix_def
    {R Node : Type*} [NonAssocRing R] [DecidableEq Node]
    (v : Node → R) :
    perronResidualMatrix v =
      (1 : Matrix Node Node R) - Matrix.vecMulVec v 1 := by
  rfl

/-- An entry of the Perron residual matrix is the Kronecker-delta identity
entry minus the corresponding node weight.

Layer: Model | Gap: Level 0 (entrywise Perron residual matrix specification)
Proof: unfold the matrix, evaluate `Matrix.one_apply` and `Matrix.vecMulVec`, and simplify multiplication by one.
Source: Mathlib `Matrix.one_apply` and the entrywise definition of `Matrix.vecMulVec`
Used in: coordinatewise expansions of directed-network residual actions and periodic residual-matrix equalities
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem perronResidualMatrix_apply
    {R Node : Type*} [NonAssocRing R] [DecidableEq Node]
    (v : Node → R) (i j : Node) :
    perronResidualMatrix v i j = (if i = j then 1 else 0) - v i := by
  simp [perronResidualMatrix, Matrix.one_apply, Matrix.vecMulVec]

/-- Acting on a module-valued finite-network state by the Perron residual
matrix produces the state-level Perron residual.

Layer: Model | Gap: Level 0 (matrix action representation of the Perron residual)
Proof: expand `Matrix.smulVec` entrywise, distribute subtraction through scalar multiplication and the finite sum, collapse the identity row, and factor the common node weight from the total state mass.
Source: Mathlib finite module-valued sums and identity-matrix action, together with `Matrix.smulVec` and `FiniteNetwork.perronResidual`
Used in: directed gradient-tracking proofs that pass between residual-matrix operator norms and zero-sum Perron-residual states in the joint-coordinate recurrence
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem perronResidualMatrix_smulVec
    {R Node E : Type*} [Ring R] [Fintype Node] [DecidableEq Node]
    [AddCommGroup E] [Module R E]
    (v : Node → R) (W : Node → E) :
    Matrix.smulVec (perronResidualMatrix v) W = perronResidual v W := by
  funext i
  simp only [Matrix.smulVec_apply, perronResidualMatrix_apply,
    perronResidual_apply, sub_smul, Finset.sum_sub_distrib]
  rw [← Finset.smul_sum]
  simp

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_periodicPushPullPerronSequences`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: canonical positive periodic push-pull Perron-sequence pair; orig was perronSequences.
-- generality used: arbitrary finite node carrier, real row/column matrix schedules, a natural period, and existence of a pair satisfying the unique positive periodic normalized Perron specification; no decidable equality, nonemptiness, stochasticity, schedule regularity, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are used by the selection itself.
-- portable call pattern: a periodic push-pull, push-sum, or gradient-tracking development changes its finite network schedules and period while selecting the same canonical pair from a proved unique positive periodic Perron specification, without exposing witness construction at later call sites.
-- counterargument checked: this is not merely paper-local traceability because the selected pair and its specification form a reusable Model API over arbitrary schedules; generic `Classical.choose` and SOptLib optimizer selectors do not name this network object, while the companion specification theorem prevents the definition from being a single-expression API with no usable contract.
-- coverage search: lean_search_symbols queries "canonical choice unique positive periodic push pull Perron sequence pair exists unique specification", "canonical selected witness unique positive periodic Perron sequences specification", and "select witness from exists predicate and specification Classical choose" found `FiniteNetwork.UniquePositivePeriodicPushPullPerronSequences`, its schedule-level existence theorem, and unrelated optimizer selectors, but no selected periodic Perron-pair object; coverage is complementary rather than duplicative.
-- minimal hypotheses: `[Fintype Node]` is required by the specification predicate, and the existential certificate is the only value-level hypothesis consumed by `Classical.choose`; uniqueness is retained inside that predicate rather than repeated as a stronger external assumption.

/-- The canonical pair of positive periodic normalized Perron sequences for
paired push-pull matrix schedules, selected from its unique specification.

Layer: Model | Concept: canonical periodic push-pull Perron-sequence pair
Proof: (definitional construction; classical choice from existence of a pair satisfying the unique positive periodic normalized push-pull Perron specification)
Source: classical choice together with finite-state nonhomogeneous Markov-chain absolute probability sequences and Perron--Frobenius theory for periodic stochastic matrix products
Used in: periodic push-pull, push-sum, and gradient-tracking analyses that fix canonical left absolute-probability and right Perron sequences before weighted-consensus and coordinate-normalization arguments
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def periodicPushPullPerronSequences
    {Node : Type*} [Fintype Node]
    (R C : Nat -> Matrix Node Node Real) (p : Nat)
    (hexists : Exists (UniquePositivePeriodicPushPullPerronSequences R C p)) :
    (Nat -> Node -> Real) × (Nat -> Node -> Real) :=
  Classical.choose hexists

/-- The canonical periodic push-pull Perron pair unfolds to the witness selected
from its existence certificate.

Layer: Model | Gap: Level 0 (canonical periodic Perron-pair selector unfolding)
Proof: by rfl after unfolding `FiniteNetwork.periodicPushPullPerronSequences`.
Source: Lean classical choice for existential witnesses
Used in: reducing equality questions about the canonical periodic push-pull Perron pair to the witness selected from the schedule-level existence certificate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem periodicPushPullPerronSequences_def
    {Node : Type*} [Fintype Node]
    (R C : Nat -> Matrix Node Node Real) (p : Nat)
    (hexists : Exists (UniquePositivePeriodicPushPullPerronSequences R C p)) :
    periodicPushPullPerronSequences R C p hexists = Classical.choose hexists := by
  rfl

/-- The canonical periodic push-pull Perron pair satisfies the unique positive
periodic normalized Perron specification from which it was selected.

Layer: Model | Gap: Level 0 (canonical periodic Perron-pair specification)
Proof: apply `Classical.choose_spec` to the supplied existence certificate for the unique positive periodic push-pull Perron predicate.
Source: Lean classical choice specification and the finite-network unique positive periodic push-pull Perron contract
Used in: projecting evolution, normalization, strict positivity, periodicity, and uniqueness facts for the canonical Perron weights in periodic directed-network optimization
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicPushPullPerronSequences_spec
    {Node : Type*} [Fintype Node]
    (R C : Nat -> Matrix Node Node Real) (p : Nat)
    (hexists : Exists (UniquePositivePeriodicPushPullPerronSequences R C p)) :
    UniquePositivePeriodicPushPullPerronSequences R C p
      (periodicPushPullPerronSequences R C p hexists) := by
  exact Classical.choose_spec hexists

end FiniteNetwork

/-! Phase 4 batch 4: `ContinuousLinearMap_projectionComplementAction_sub_norm_le`. -/


-- Generalization plan (G0):
-- concept/name: perturbation bound for two identity-minus continuous-linear-map actions; orig was the local block `projectionComplementAction_sub_norm_le`.
-- generality used: an arbitrary nontrivially normed scalar field and seminormed additive commutative scalar space, with two continuous endomorphisms and two vectors; no idempotence, completeness, finite-dimensionality, spectral, measure, convexity, smoothness, oracle, or algorithm assumptions are used.
-- portable call pattern: operator perturbation and consensus/disagreement proofs change the normed space, the two bounded operators, and the two inputs while reusing the same separation into input perturbation and operator perturbation terms.
-- counterargument checked: this is not paper-local bookkeeping or a pure rename; it combines a nontrivial two-operator algebraic decomposition with three norm bounds, while Mathlib exposes only the component triangle and operator-norm inequalities.
-- coverage search: `lean_search_symbols` queries "norm difference complementary operator actions bounded by input difference and operator difference" and "continuous linear map norm sub apply perturbation bound" found no matching SOptLib or Mathlib declaration; LeanSearch for the full identity-minus-operator perturbation bound found `ContinuousLinearMap.le_opNorm` and `ContinuousLinearMap.dist_le_opNorm`, which cover only individual operator actions.
-- minimal hypotheses: the source's real matrices, finite coordinate type, custom Euclidean norm, and finite-dimensional structure are removed; seminormedness and a nontrivially normed field are sufficient for the operator norm and triangle inequalities.

namespace ContinuousLinearMap

/-- The difference of two identity-minus operator actions is bounded by an
input perturbation term and an operator perturbation term.

Layer: Glue | Gap: Level 1 (identity-minus bounded-operator action perturbation bound)
Proof: decompose the difference as `(1 - f) (x - y) - (f - g) y`, then apply the triangle inequality, the continuous-linear-map operator-norm bound, and `‖1 - f‖ ≤ 1 + ‖f‖`.
Source: Mathlib continuous-linear-map operator norm and seminormed additive-group triangle inequalities
Used in: stable spectral-complement and consensus/disagreement input comparisons, where both the bounded operator and its input vary between a perturbed system and a base system
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem norm_one_sub_apply_sub_one_sub_apply_le
    {K E : Type*} [NontriviallyNormedField K] [SeminormedAddCommGroup E]
    [NormedSpace K E] (f g : E →L[K] E) (x y : E) :
    ‖(1 - f) x - (1 - g) y‖ ≤
      (1 + ‖f‖) * ‖x - y‖ + ‖f - g‖ * ‖y‖ := by
  have h_one_sub : ‖(1 - f : E →L[K] E)‖ ≤ 1 + ‖f‖ := by
    calc
      ‖(1 - f : E →L[K] E)‖ ≤ ‖(1 : E →L[K] E)‖ + ‖f‖ :=
        norm_sub_le _ _
      _ ≤ 1 + ‖f‖ := add_le_add norm_id_le le_rfl
  calc
    ‖(1 - f) x - (1 - g) y‖ =
        ‖(1 - f) (x - y) - (f - g) y‖ := by
      congr 1
      simp only [sub_apply, one_apply, map_sub]
      abel
    _ ≤ ‖(1 - f) (x - y)‖ + ‖(f - g) y‖ := norm_sub_le _ _
    _ ≤ ‖(1 - f : E →L[K] E)‖ * ‖x - y‖ +
          ‖f - g‖ * ‖y‖ :=
      add_le_add ((1 - f).le_opNorm (x - y)) ((f - g).le_opNorm y)
    _ ≤ (1 + ‖f‖) * ‖x - y‖ + ‖f - g‖ * ‖y‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right h_one_sub (norm_nonneg (x - y))) le_rfl

end ContinuousLinearMap

/-! Phase 4 batch 4: `FiniteNetwork_columnInnovation_eq_normalizedCoordinateError_sub_smulVec`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: normalized matrix-column innovation as a coboundary of consecutive normalized coordinate errors; orig was `pullColumnInnovation_eq_error_sub_transport`.
-- generality used: arbitrary finite node type and nonassociative ring of coefficients, a square matrix, two normalized vectors, a selected coordinate, and only the one-step matrix-action equality; no stochasticity, positivity, Perron, periodicity, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions.
-- portable call pattern: nonhomogeneous Markov-chain, push-sum, consensus, and gradient-tracking proofs change the transition matrix, consecutive normalized weights, and selected coordinate while reusing the same innovation-as-error-coboundary equality.
-- counterargument checked: this is not merely paper traceability or a pure wrapper; it combines a matrix-vector transition with two coordinate-centerings and the selected matrix column, while the available Mathlib and staged APIs provide only the separate matrix-action and coordinate-error components.
-- coverage search: `lean_search_symbols` queries "normalized coordinate error next vector minus matrix smulVec current error of matrix times current equals next", "column innovation equals normalized coordinate error sub transport", and "matrix column minus identity column equals next vector error minus matrix action current vector error" found only the source-local theorem and component declarations; LeanSearch found `Matrix.mulVec_single_one`, `Matrix.mulVec_sub`, and `Matrix.one_mulVec`, which are scalar-valued proof ingredients but do not state the normalized-error coboundary identity.
-- minimal hypotheses: `[Fintype Node]` and `[DecidableEq Node]` form finite sums and the selected coordinate; `[NonAssocRing R]` supplies exactly additive subtraction, multiplication, zero, one, and distributivity; the three sum-to-one proofs construct the normalized errors, and `hstep` is the sole transition hypothesis.

/-- A normalized matrix column is the next normalized coordinate error minus
the matrix transport of the current normalized coordinate error whenever the
matrix sends the current normalized vector to the next one.

Layer: Model | Gap: Level 1 (normalized coordinate-error coboundary for a matrix transition)
Proof: expand the three normalized coordinate errors and `Matrix.smulVec`, distribute multiplication over subtraction, and use the one-step transition together with the Kronecker-column finite sum.
Source: Mathlib finite matrices, finite sums, distributivity, and Kronecker-coordinate identities, together with `FiniteNetwork.normalizedCoordinateError` and `Matrix.smulVec`
Used in: nonhomogeneous Markov, push-sum, consensus, and gradient-tracking influence proofs that rewrite a normalized mixing-column innovation as a telescoping error plus transported disagreement
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem columnInnovation_eq_normalizedCoordinateError_sub_smulVec
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [NonAssocRing R]
    (A : Matrix Node Node R) (v vNext : Node → R) (i : Node)
    (hA : ∑ k : Node, A k i = 1)
    (hv : ∑ k : Node, v k = 1)
    (hvNext : ∑ k : Node, vNext k = 1)
    (hstep : Matrix.smulVec A v = vNext) :
    (normalizedCoordinateError (fun k ↦ A k i) i hA : Node → R) =
      (normalizedCoordinateError vNext i hvNext : Node → R) -
        Matrix.smulVec A (normalizedCoordinateError v i hv : Node → R) := by
  funext k
  simp only [normalizedCoordinateError_apply, Matrix.smulVec_apply,
    Pi.sub_apply, smul_eq_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have htransition : ∑ l : Node, A k l * v l = vNext k := by
    simpa only [Matrix.smulVec_apply, smul_eq_mul] using congrFun hstep k
  rw [htransition]
  have hcoordinate :
      ∑ l : Node, A k l * (if l = i then 1 else 0) = A k i := by
    simp
  rw [hcoordinate]
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_dependentProductL2Seminorm_le_sqrt_card_mul_geometric_of_stateL1Norm`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite dependent-product L1-to-L2 geometric-bound transfer; orig was `pullLiftProduct_frobenius_rate`.
-- generality used: arbitrary finite index type, dependent seminormed additive coordinate groups, state endomorphism, geometric prefactor and rate, and a pointwise coordinate-norm-sum bound; no commutativity, scalar action, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, stochastic-matrix, or zero-sum assumptions are used by the transfer itself.
-- portable call pattern: push-sum, gradient-tracking, directed-consensus, and block-product proofs change the finite node type, state space, matrix-product action, prefactor, rate, and invariant state while reusing the same conversion from an L1 geometric estimate to a dependent-product L2 estimate.
-- counterargument checked: this is not paper-local traceability or a pure wrapper because it composes two finite-norm comparisons with a supplied geometric operator estimate; the zero-sum and matrix-schedule assumptions correctly remain at the caller that establishes the L1 premise.
-- coverage search: `lean_search_symbols` queries for finite-state L1 geometric bounds implying Frobenius/L2 bounds found only the paper-local source and its component norm comparisons; `lean_leansearch` found `Real.sum_mul_le_sqrt_mul_sqrt`, `Finset.sum_sq_le_sq_sum_of_nonneg`, and ambient `PiLp` facts, but no theorem with the complete transfer contract.
-- minimal hypotheses: `[Fintype Node]` and dependent coordinate `[SeminormedAddGroup (Block i)]` instances are sufficient; nonnegativity is required only for the full geometric coefficient `c * rate ^ j`, and the coordinate-norm-sum contraction is pointwise at the state being bounded.

/-- A geometric bound in the coordinate-sum norm transfers to the finite
dependent-product L2 seminorm with a square-root-cardinality loss.

The operator and state need no algebraic compatibility beyond the supplied
pointwise L1 estimate. This lets invariant-domain or zero-sum assumptions stay
with the proof that produces that estimate.

Layer: Model | Gap: Level 1 (finite dependent-product L1-to-L2 geometric-bound transfer)
Proof: sandwich the supplied coordinate-sum estimate between the root-sum-square-to-sum inequality and finite Cauchy--Schwarz, using nonnegativity of the geometric coefficient to multiply the latter bound.
Source: Mathlib `Finset.sum_sq_le_sq_sum_of_nonneg` and `Real.sum_mul_le_sqrt_mul_sqrt`, together with SOptLib's finite dependent-product squared norm energy
Used in: periodic directed-network pull-product contraction, where a zero-sum state L1 estimate is converted into the Frobenius contraction used by the Push--Pull consensus analysis
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem dependentProductL2Seminorm_le_sqrt_card_mul_geometric_of_sum_norm_le
    {Node : Type*} [Fintype Node]
    {Block : Node -> Type*} [∀ i, SeminormedAddGroup (Block i)]
    (T : (∀ i, Block i) -> (∀ i, Block i)) (c rate : Real) (j : Nat)
    (W : ∀ i, Block i)
    (hcoeff_nonneg : 0 <= c * rate ^ j)
    (hL1 : (∑ i : Node, ‖T W i‖) <=
      c * rate ^ j * ∑ i : Node, ‖W i‖) :
    Real.sqrt (SOptLib.dependentProductNormSq (T W)) <=
      c * Real.sqrt (Fintype.card Node : Real) * rate ^ j *
        Real.sqrt (SOptLib.dependentProductNormSq W) := by
  classical
  have hl2_le_l1 :
      Real.sqrt (SOptLib.dependentProductNormSq (T W)) <=
        ∑ i : Node, ‖T W i‖ := by
    have hsquares :
        (∑ i : Node, ‖T W i‖ ^ 2) <=
          (∑ i : Node, ‖T W i‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
    rw [SOptLib.dependentProductNormSq_def]
    calc
      Real.sqrt (∑ i : Node, ‖T W i‖ ^ 2) <=
          Real.sqrt ((∑ i : Node, ‖T W i‖) ^ 2) :=
        Real.sqrt_le_sqrt hsquares
      _ = ∑ i : Node, ‖T W i‖ :=
        Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hl1_le_l2 :
      (∑ i : Node, ‖W i‖) <=
        Real.sqrt (Fintype.card Node : Real) *
          Real.sqrt (SOptLib.dependentProductNormSq W) := by
    simpa [SOptLib.dependentProductNormSq_def] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Node)
        (fun _ : Node => (1 : Real)) (fun i : Node => ‖W i‖))
  calc
    Real.sqrt (SOptLib.dependentProductNormSq (T W)) <=
        ∑ i : Node, ‖T W i‖ := hl2_le_l1
    _ <= c * rate ^ j * ∑ i : Node, ‖W i‖ := hL1
    _ <= c * rate ^ j *
          (Real.sqrt (Fintype.card Node : Real) *
            Real.sqrt (SOptLib.dependentProductNormSq W)) :=
      mul_le_mul_of_nonneg_left hl1_le_l2 hcoeff_nonneg
    _ = c * Real.sqrt (Fintype.card Node : Real) * rate ^ j *
          Real.sqrt (SOptLib.dependentProductNormSq W) := by
      ring

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_ZeroSumState_smulVec_mem_of_mem_colStochastic`. -/


open scoped BigOperators

namespace FiniteNetwork.ZeroSumState

-- Generalization plan (G0):
-- concept/name: preservation of the finite-network zero-sum state subspace by a column-stochastic matrix action; orig was `pullLiftProduct_leftMul_zeroSum`.
-- generality used: arbitrary finite node type, ordered semiring of matrix coefficients, and additive commutative module of state values; no nonemptiness, norm, topology, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle hypotheses are used.
-- portable call pattern: gradient-tracking, push-sum, and pull-based consensus proofs change the finite network, module-valued state space, column-stochastic communication matrix, and zero-sum tracker state while reusing the same invariant-subspace conclusion.
-- counterargument checked: although the proof is a short composition, this is not paper-local traceability or a pure rename; it packages the recurring invariant-domain transition from a zero-sum subtype through a column-stochastic module-valued matrix action.
-- coverage search: lean_search_symbols queries "zero sum state smulVec column stochastic preserves zero sum membership", "column stochastic matrix action preserves zero sum subspace module valued state", and "FiniteNetwork ZeroSumState smulVec mem colStochastic" found the component lemmas `Matrix.sum_smulVec_of_mem_colStochastic` and `FiniteNetwork.ZeroSumState.sum_coe_eq_zero`, but no theorem packaging the invariant-subspace conclusion; LeanSearch for "a column stochastic matrix preserves the zero sum subspace of module-valued finite vectors" found scalar stochastic-matrix APIs only.
-- minimal hypotheses: `[Fintype Node]` and `[DecidableEq Node]` are required by Mathlib's column-stochastic predicate; `[Semiring R] [PartialOrder R] [IsOrderedRing R]` are its scalar assumptions; `[AddCommMonoid E] [Module R E]` are exactly the zero-sum and module-valued matrix-action requirements.

/-- A column-stochastic matrix action sends a finite-network zero-sum state to
another state whose coordinates sum to zero.

Layer: Model | Gap: Level 1 (column-stochastic invariance of the module-valued zero-sum subspace)
Proof: use `Matrix.sum_smulVec_of_mem_colStochastic` to preserve the coordinate sum, then discharge that sum with `FiniteNetwork.ZeroSumState.sum_coe_eq_zero`.
Source: Mathlib column-stochastic matrices and finite big operators, together with SOptLib's module-valued matrix action and finite-network zero-sum state
Used in: pull-based gradient-tracking product recurrences where successive column-stochastic communication matrices must keep tracker errors inside the zero-total-mass state space
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem smulVec_mem_of_mem_colStochastic
    {R Node E : Type*} [Fintype Node] [DecidableEq Node]
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [AddCommMonoid E] [Module R E]
    {A : Matrix Node Node R} (W : FiniteNetwork.ZeroSumState Node E)
    (hA : A ∈ Matrix.colStochastic R Node) :
    ∑ i : Node, Matrix.smulVec A (W : Node → E) i = 0 := by
  rw [Matrix.sum_smulVec_of_mem_colStochastic (W : Node → E) hA]
  exact W.sum_coe_eq_zero

end FiniteNetwork.ZeroSumState

/-! Phase 4 batch 4: `Matrix_sum_sub_one_smulVec_eq_zero_of_mem_colStochastic`. -/


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: zero total mass of the module-valued innovation produced by a column-stochastic matrix; orig was `pull_innovation_sum_zero`.
-- generality used: arbitrary finite node type, ordered ring of matrix coefficients, and additive commutative module of state values; no norm, topology, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle hypotheses are used.
-- portable call pattern: consensus, push-sum, and gradient-tracking proofs change the column-stochastic communication matrix and module-valued state while reusing that the `(A - I)` innovation lies in the zero-total-mass subspace.
-- counterargument checked: the conclusion is a short composition of existing module-valued matrix-action lemmas, but it exposes the standard invariant-subspace boundary needed repeatedly in tracker and innovation recurrences; it is not a pure rename of either component theorem.
-- coverage search: `lean_search_symbols` queries "module valued sum of matrix minus identity smulVec zero column stochastic" and "sum smulVec subtraction identity column stochastic zero", plus LeanSearch query "For a column stochastic matrix A and a module-valued finite vector X, the sum of the coordinates of (A minus the identity) acting on X is zero", found Mathlib's scalar stochastic-matrix API and the staged component lemmas `Matrix.sub_one_smulVec` and `Matrix.sum_smulVec_of_mem_colStochastic`, but no theorem with this module-valued zero-innovation conclusion.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite sums, identity matrices, and the stochastic predicate; `[Ring R] [PartialOrder R] [IsOrderedRing R]` support subtraction and column-stochasticity; `[AddCommGroup E] [Module R E]` are exactly the state operations used by the two component lemmas.

namespace Matrix

/-- The module-valued innovation of a column-stochastic matrix has zero total
mass: the coordinates of `(A - 1)X` sum to zero.

Layer: Model | Gap: Level 1 (zero-total-mass column-stochastic innovation on module-valued states)
Proof: rewrite the innovation action with `Matrix.sub_one_smulVec`, distribute the coordinate sum over subtraction, and cancel using `Matrix.sum_smulVec_of_mem_colStochastic`.
Source: Mathlib column-stochastic matrices and finite big operators, together with SOptLib's module-valued matrix action laws
Used in: push-pull gradient-tracking and consensus recurrences where communication increments of the form `(C_t - I)X` must enter the zero-sum tracker subspace
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sum_sub_one_smulVec_eq_zero_of_mem_colStochastic
    {R Node E : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    [Fintype Node] [DecidableEq Node]
    [AddCommGroup E] [Module R E]
    {A : Matrix Node Node R} (X : Node → E)
    (hA : A ∈ colStochastic R Node) :
    ∑ i : Node, smulVec (A - 1) X i = 0 := by
  rw [sub_one_smulVec]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  rw [sum_smulVec_of_mem_colStochastic X hA]
  exact sub_self _

end Matrix

/-! Phase 4 batch 4: `FiniteNetwork_mul_consecutiveProduct_period_eq_consecutiveProduct_succ_mul_of_periodic`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: endpoint-closed rotation of a consecutive product; orig was pushLiftProduct_cyclic.
-- generality used: an arbitrary monoid-valued natural-time schedule and equality of the two window endpoints; no global periodicity, matrix, scalar, node, finiteness, decidable-equality, positivity-of-window-length, stochasticity, topology, norm, measure, convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: switched-system, consensus, gossip, push-sum, and gradient-tracking proofs change the monoid-valued schedule, window length, and phase while reusing the same rotation identity whenever the window endpoints agree.
-- counterargument checked: this is not paper-local traceability or a pure rename; it packages the noncommutative factor order, adjacent-window split, and endpoint replacement needed whenever a phase-start product is rotated, and neither Mathlib nor SOptLib exposes this exact contract.
-- coverage search: lean_search_symbols queries "consecutive product monoid endpoint equality rotation start successor" and "multiplication consecutive product successor equals rotation from endpoint equality" found only the underlying staged `FiniteNetwork.consecutiveProduct` successor and adjacent-window laws.
-- minimal hypotheses: `[Monoid M]` supplies the identity, multiplication, and associativity; `A (t + p) = A t` is exactly the endpoint replacement used by the proof, and the result also holds at window length zero, so no positivity assumption is needed.

/-- Multiplication by the first value rotates a consecutive product whose
endpoint value agrees with its initial value.

For the newest-on-the-left product convention, the product starting at `t + 1`
ends with `A (t + p)`, which the endpoint hypothesis replaces by `A t` before
reassociation.

Layer: Model | Gap: Level 1 (rotation of an endpoint-closed ordered monoid product)
Proof: split the original window after its first factor, unfold the successor-phase product at its last factor, replace that factor using endpoint equality, and reassociate the monoid product.
Source: Mathlib natural-number addition and monoid associativity, together with the SOptLib consecutive-product adjacent-window law
Used in: switched-system and distributed-optimization phase arguments that commute the first communication operator across an endpoint-closed schedule window
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/7
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem mul_consecutiveProduct_eq_consecutiveProduct_succ_mul_of_endpoint_eq
    {M : Type*} [Monoid M] (A : Nat -> M) (p t : Nat)
    (hendpoint : A (t + p) = A t) :
    A t * consecutiveProduct A t p =
      consecutiveProduct A (t + 1) p * A t := by
  cases p with
  | zero => simp
  | succ p =>
      have hindex : t + 1 + p = t + (p + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 p]
      have hAt : A (t + 1 + p) = A t := by
        rw [hindex]
        exact hendpoint
      calc
        A t * consecutiveProduct A t (p + 1) =
            A t * (consecutiveProduct A (t + 1) p *
              consecutiveProduct A t 1) := by
          rw [Nat.add_comm p 1, consecutiveProduct_add]
        _ = A t * (consecutiveProduct A (t + 1) p * A t) := by
          simp
        _ = (A t * consecutiveProduct A (t + 1) p) * A t := by
          rw [mul_assoc]
        _ = (A (t + 1 + p) * consecutiveProduct A (t + 1) p) * A t := by
          rw [hAt]
        _ = consecutiveProduct A (t + 1) (p + 1) * A t := by
          rw [consecutiveProduct_succ]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_consecutiveProduct_add_period_eq_of_periodic`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: invariance of a consecutive product under shifting its start by a schedule period; orig was pushLiftProduct_periodic_start.
-- generality used: an arbitrary monoid-valued natural-time schedule with Mathlib's `Function.Periodic` predicate; no matrix, scalar, node, finiteness, decidable-equality, positive-period, stochasticity, topology, norm, measure, convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: periodic switched-system, consensus, gossip, push-sum, and gradient-tracking proofs change the monoid-valued schedule, period, start, and window length while reusing equality of the two start-shifted propagation products.
-- counterargument checked: not paper-local or a pure wrapper because it lifts pointwise schedule periodicity through a noncommutative recursively ordered window product; Mathlib's periodic-product closure lemmas concern pointwise products of a fixed finite collection of functions, not a consecutive window whose factors depend on the start index.
-- coverage search: `lean_search_symbols` queries "consecutive product start shifted by period periodic sequence equality" and "periodic monoid sequence consecutiveProduct add period equal" found the staged consecutive-product definition, its adjacent-window law, and the distinct endpoint-rotation theorem, but no start-shift theorem; LeanSearch for a periodic monoid-valued sequence's consecutive finite product found `List.periodic_prod` and commutative `Finset.prod_range` lemmas, none of which has this noncommutative consecutive-window contract.
-- minimal hypotheses: `[Monoid M]` is required by `FiniteNetwork.consecutiveProduct`, and `Function.Periodic A p` is exactly the pointwise equality used at each factor; the result holds for zero periods and zero-length windows, so no positivity hypothesis is needed.

/-- A consecutive product of a periodic monoid-valued schedule is unchanged
when its start is shifted forward by one period.

The equality preserves the newest-on-the-left factor order of
`FiniteNetwork.consecutiveProduct`; no commutativity or positive-period
assumption is required.

Layer: Model | Gap: Level 1 (period-shift invariance of ordered consecutive products)
Proof: induct on the window length, rewrite both successor products, use the induction hypothesis, and apply schedule periodicity after reassociating the natural-number index.
Source: Mathlib `Function.Periodic`, natural-number addition, and monoids, together with the SOptLib consecutive-product specification
Used in: identifying phase-shifted communication-window products in periodic push-pull Perron-sequence proofs and periodic switched-system propagation
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/7
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveProduct_add_period_eq_of_periodic
    {M : Type*} [Monoid M] (A : Nat -> M) (p t j : Nat)
    (hA : Function.Periodic A p) :
    consecutiveProduct A (t + p) j = consecutiveProduct A t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [consecutiveProduct_succ, consecutiveProduct_succ, ih,
        Nat.add_right_comm t p j, hA]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_periodicCorrectedLiftSeriesTerm_add_period_mul`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: invariance of a periodic corrected-lift summand after any whole number of schedule periods; orig was `correctedLiftSeriesTerm_blockStart`.
-- generality used: arbitrary finite node carrier with decidable equality, semiring-valued matrix and weight schedules with a common natural period, and an additive-commutative-monoid-valued zero-sum state with a scalar action; no positive-period, stochasticity, norm, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic consensus, push-sum, and gradient-tracking proofs change the matrix schedule, Perron-weight sequence, scalar semiring, state space, period, phase, block number, and lag while replacing a corrected-lift summand at the shifted block phase by the same summand in the reference block.
-- counterargument checked: not paper-local traceability or a pure wrapper because it transports two common periodic schedules through both the shifted Perron weight and a noncommutative consecutive propagation window; it strengthens the source's phase-zero block-start statement to every phase and every period multiple.
-- coverage search: `lean_search_symbols` queries "corrected lift series term equality after period multiple periodic matrix weights", "consecutive matrix product equal after adding period multiple of periodic schedule", and "Function Periodic add natural multiple equality" found the staged summand definition, `FiniteNetwork.consecutiveProduct_add_period_eq_of_periodic`, and Mathlib `Function.Periodic.nat_mul`; LeanSearch found Mathlib's general periodic-function multiple laws but no theorem combining the corrected-lift weight shift with its ordered matrix window, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Semiring R] [Fintype Node] [DecidableEq Node] [AddCommMonoid E] [SMul R E]` are exactly the hypotheses of `periodicCorrectedLiftSeriesTerm`; `hC` and `hpi` are the pointwise common-period assumptions used by the proof, and no positivity or zero-sum preservation hypothesis is needed.

/-- A corrected-lift series summand with periodic matrix and weight schedules is
unchanged when its base phase is shifted by any natural multiple of their
common period.

Layer: Model | Gap: Level 1 (period-multiple invariance of a corrected-lift series summand)
Proof: promote each common-period hypothesis to the requested period multiple, rewrite the shifted Perron weight with Mathlib periodicity, and rewrite the ordered propagation window with `FiniteNetwork.consecutiveProduct_add_period_eq_of_periodic`.
Source: Mathlib `Function.Periodic` natural-multiple laws and finite matrix-module actions, together with the SOptLib consecutive-product and periodic corrected-lift-summand Model APIs
Used in: periodic consensus, push-sum, and gradient-tracking block proofs that identify every corrected-lift series term at a block phase with the matching term in the reference block
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLiftSeriesTerm_add_period_mul
    {R Node E : Type*} [Semiring R] [Fintype Node] [DecidableEq Node]
    [AddCommMonoid E] [SMul R E]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (period t k j : Nat) (W : ZeroSumState Node E)
    (hC : Function.Periodic C period) (hpi : Function.Periodic pi period) :
    periodicCorrectedLiftSeriesTerm C pi (t + period * k) j W =
      periodicCorrectedLiftSeriesTerm C pi t j W := by
  have hCk : Function.Periodic C (period * k) := by
    simpa [Nat.mul_comm] using hC.nat_mul k
  have hpik : Function.Periodic pi (period * k) := by
    simpa [Nat.mul_comm] using hpi.nat_mul k
  simp only [periodicCorrectedLiftSeriesTerm_def]
  rw [show t + period * k + j + 1 = (t + j + 1) + period * k by omega,
    hpik, consecutiveProduct_add_period_eq_of_periodic C (period * k) t j hCk]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_periodicInfluence`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: periodic finite-network influence row; orig was `influence`.
-- generality used: arbitrary finite node carrier, a real matrix schedule, a real row-weight sequence, and a phase index; no nonempty, stochasticity, positivity, periodicity, norm, inner-product, finite-dimensional, measure, convexity, smoothness, or oracle assumptions enter the definition.
-- portable call pattern: periodic push-pull, push-sum, and gradient-tracking analyses change the pull schedule, Perron row sequence, node carrier, and phase while retaining the same Perron base plus infinite propagated-innovation response used for noise amplification and effective parallelism.
-- counterargument checked: although the construction is a single expression, it is not merely paper-local traceability or a caller-side abbreviation because the whole response row is consumed independently by phase averages, squared influence, effective-node counts, and periodic-network comparison arguments; its already-staged summand and this unfolding theorem form a stable Model API.
-- coverage search: lean_search_symbols queries "periodic finite network influence row Perron base infinite response tail tsum" and "row vector equals base probability row plus infinite sum propagated matrix innovation" found the staged `FiniteNetwork.periodicInfluenceSeriesTerm` and the paper-local `influence`, but no whole-series SOptLib or Mathlib object; LeanSearch "infinite response row equals base row plus sum of matrix propagation innovation terms" returned only unrelated matrix row constructors and finite matrix identities.
-- minimal hypotheses: `[Fintype Node]` is required by the matrix contractions inside `periodicInfluenceSeriesTerm`; the source's `Nonempty`, stochasticity, positivity, periodicity, convergence, and algorithm-space assumptions are not needed to name the `tsum`, while real scalars preserve the probability-row semantics of the source object.

/-- The phase-`r` influence row formed from its shifted base weight and the
infinite tail of propagated one-step network innovations.

Layer: Model | Concept: periodic finite-network influence response row
Proof: (definitional construction; add the shifted Perron row to the infinite sum of periodic influence-series coefficients)
Source: finite-state nonhomogeneous Markov-chain response series, Mathlib infinite sums, and `FiniteNetwork.periodicInfluenceSeriesTerm`
Used in: periodic push-pull and gradient-tracking analyses that aggregate phase influence, noise amplification, and effective parallelism from the pull schedule's infinite response
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def periodicInfluence
    {Node : Type*} [Fintype Node]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (r : Nat) : Node -> Real :=
  pi (r + 1) + ∑' j : Nat, periodicInfluenceSeriesTerm C pi r j

/-- A periodic finite-network influence row unfolds to its shifted base row
plus the infinite tail of propagated innovation coefficients.

Layer: Model | Gap: Level 0 (periodic influence response unfolding)
Proof: by rfl after unfolding `FiniteNetwork.periodicInfluence`.
Source: Mathlib infinite sums and `FiniteNetwork.periodicInfluenceSeriesTerm`
Used in: rewriting a periodic network's named influence row into the base-plus-tail form needed for summability, phase aggregation, and effective-node calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem periodicInfluence_def
    {Node : Type*} [Fintype Node]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (r : Nat) :
    periodicInfluence C pi r =
      pi (r + 1) + ∑' j : Nat, periodicInfluenceSeriesTerm C pi r j := by
  rfl

/-- The finite-network influence response inherits a common period of its
matrix and row-weight schedules.

No summability hypothesis is needed: shifting the phase by one period leaves
each coefficient of the defining infinite sum unchanged.

Layer: Model | Gap: Level 1 (periodicity of the influence response)
Proof: transport the common period through the shifted base row and each influence-series coefficient, using period-shift invariance of consecutive products, then apply congruence of `tsum`.
Source: Mathlib `Function.Periodic` and infinite sums, together with `FiniteNetwork.consecutiveProduct_add_period_eq_of_periodic`
Used in: periodic push-pull, push-sum, and gradient-tracking block recurrences that replace an absolute time phase by its representative within one communication period
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluence_periodic
    {Node : Type*} [Fintype Node]
    {C : Nat -> Matrix Node Node Real} {pi : Nat -> Node -> Real}
    {p : Nat} (hC : Function.Periodic C p) (hpi : Function.Periodic pi p) :
    Function.Periodic (periodicInfluence C pi) p := by
  intro r
  classical
  rw [periodicInfluence_def, periodicInfluence_def]
  rw [show r + p + 1 = (r + 1) + p by omega, hpi]
  congr 1
  apply tsum_congr
  intro j
  rw [periodicInfluenceSeriesTerm_def, periodicInfluenceSeriesTerm_def]
  rw [show r + p + j + 2 = (r + j + 2) + p by omega, hpi]
  rw [hC r]
  rw [show r + p + 1 = (r + 1) + p by omega]
  rw [consecutiveProduct_add_period_eq_of_periodic C p (r + 1) j hC]

end FiniteNetwork

/-! Phase 4 batch 4: `FiniteNetwork_periodicInfluenceSeriesTerm_add_period_mul`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: period-multiple invariance of a periodic finite-network influence-series coefficient; orig was `influenceSeriesTerm_blockStart_add`.
-- generality used: arbitrary finite node carrier, a ring-valued matrix schedule, and a ring-valued row-weight schedule with a common natural period; no positive-period, stochasticity, positivity, norm, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic consensus, push-pull, push-sum, and gradient-tracking analyses change the matrix schedule, Perron row sequence, scalar ring, node carrier, period, phase, block number, and lag while replacing a shifted influence coefficient by the matching reference-block coefficient.
-- counterargument checked: not paper-local traceability or a pure wrapper because the result simultaneously transports a shifted weight row, a noncommutative propagation window, and the terminal matrix innovation; unlike the corrected-lift shift theorem, this coefficient has the extra terminal `(C t - 1)` factor and a different weight offset.
-- coverage search: `lean_search_symbols` queries "periodic influence series term equality after adding period multiple periodic matrix row weights", "periodic matrix schedule Perron row propagation window terminal innovation invariant phase shift", and "Function Periodic nat_mul consecutiveProduct add period influence coefficient" found the staged coefficient definition, its coordinate specification, `FiniteNetwork.consecutiveProduct_add_period_eq_of_periodic`, and the structurally different corrected-lift shift theorem, but no influence-coefficient shift theorem; LeanSearch found Mathlib `Function.Periodic.nat_mul` and multiple-shift facts, which cover individual schedules but not this composite matrix coefficient.
-- minimal hypotheses: `[Ring R]` is required by the coefficient's matrix subtraction and matrix algebra, `[Fintype Node]` is required by matrix multiplication, and the two common-period hypotheses are precisely the schedule facts used; classical decidable equality is selected only inside the proof.

/-- An influence-series coefficient built from periodic matrix and row-weight
schedules is unchanged when its base phase is shifted by any natural multiple
of their common period.

Layer: Model | Gap: Level 1 (period-multiple invariance of a periodic influence-series coefficient)
Proof: promote both common-period hypotheses to the requested natural multiple, then rewrite the shifted weight row, terminal innovation, and ordered propagation window using Mathlib periodicity and `FiniteNetwork.consecutiveProduct_add_period_eq_of_periodic`.
Source: Mathlib `Function.Periodic.nat_mul`, finite matrix algebra, and the SOptLib consecutive-product and periodic influence-series coefficient Model APIs
Used in: periodic consensus, push-pull, push-sum, and gradient-tracking block arguments that identify each propagated influence coefficient at an absolute block time with its coefficient at the corresponding reference phase
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceSeriesTerm_add_period_mul
    {R Node : Type*} [Ring R] [Fintype Node]
    (C : Nat -> Matrix Node Node R) (pi : Nat -> Node -> R)
    (period t k j : Nat)
    (hC : Function.Periodic C period) (hpi : Function.Periodic pi period) :
    periodicInfluenceSeriesTerm C pi (t + period * k) j =
      periodicInfluenceSeriesTerm C pi t j := by
  classical
  have hCk : Function.Periodic C (period * k) := by
    simpa [Nat.mul_comm] using hC.nat_mul k
  have hpik : Function.Periodic pi (period * k) := by
    simpa [Nat.mul_comm] using hpi.nat_mul k
  simp only [periodicInfluenceSeriesTerm_def]
  rw [show t + period * k + j + 2 = (t + j + 2) + period * k by omega,
    hpik, hCk t,
    show t + period * k + 1 = (t + 1) + period * k by omega,
    consecutiveProduct_add_period_eq_of_periodic C (period * k) (t + 1) j hCk]

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_periodicInfluence_add_period_mul.lean`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: period-multiple invariance of a periodic finite-network influence response; orig was `influence_blockStart_add`.
-- generality used: arbitrary finite node carrier, a real matrix schedule, and a real row-weight schedule with a common natural period; no positive-period, stochasticity, positivity, summability, norm, inner-product, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic push-pull, push-sum, consensus, and gradient-tracking block proofs change the pull schedule, Perron row sequence, period, phase, and block number while replacing an absolute-block influence row by the matching reference-phase row.
-- counterargument checked: `FiniteNetwork.periodicInfluence_periodic` already gives the one-period function-level invariant, but does not expose the period-multiple phase equality required at block-indexed call sites; this declaration is its assumption-preserving Mathlib-style natural-multiple specialization, not a paper-local setup wrapper or a reproof of the infinite-series identity.
-- coverage search: `lean_search_symbols` queries "periodic influence invariant under adding period multiple periodic matrix sequence Perron sequence", "periodic function equality add period natural multiple", and "periodicInfluence_periodic nat_mul influence block start" found `FiniteNetwork.periodicInfluence_periodic`, `FiniteNetwork.periodicInfluenceSeriesTerm_add_period_mul`, and Mathlib `Function.Periodic.nat_mul`; coverage is partial because the first is a one-period function predicate and the second concerns one series coefficient, while neither states the full response equality at an arbitrary natural period multiple.
-- minimal hypotheses: `[Fintype Node]` is inherited from the concrete `periodicInfluence` object; common periodicity of `C` and `pi` are exactly the hypotheses consumed, and no period positivity or series summability is needed.

/-- A finite-network influence response built from matrix and row-weight
schedules with a common period is unchanged when its phase is shifted by any
natural multiple of that period.

Layer: Model | Gap: Level 1 (period-multiple invariance of a periodic influence response)
Proof: obtain periodicity of the full influence response from `FiniteNetwork.periodicInfluence_periodic`, promote it to a natural multiple with Mathlib `Function.Periodic.nat_mul`, and specialize at the reference phase.
Source: Mathlib `Function.Periodic.nat_mul` together with the SOptLib periodic finite-network influence response Model API
Used in: periodic push-pull, push-sum, consensus, and gradient-tracking block recurrences that replace an absolute-block influence row by the corresponding within-period phase row
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluence_add_period_mul
    {Node : Type*} [Fintype Node]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (period r k : Nat)
    (hC : Function.Periodic C period) (hpi : Function.Periodic pi period) :
    periodicInfluence C pi (r + period * k) = periodicInfluence C pi r := by
  have hInfluence : Function.Periodic (periodicInfluence C pi) period :=
    periodicInfluence_periodic hC hpi
  have hInfluenceK : Function.Periodic (periodicInfluence C pi) (period * k) := by
    simpa [Nat.mul_comm] using hInfluence.nat_mul k
  exact hInfluenceK r

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_consecutiveMatrixProduct_toBlocks_of_upperRight_eq_zero.lean`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: preservation of a zero upper-right block by consecutive matrix products; orig was quadraticRestrictedConsecutiveProduct_alpha_zero_top_right.
-- generality used: arbitrary finite left and right block index types, an arbitrary scalar semiring, a natural-time-indexed square-matrix schedule on their sum, a start time, and a window length; no order, topology, norm, measure, convexity, smoothness, oracle, nonemptiness, or finite-dimensional assumptions are used.
-- portable call pattern: lifted linear recursions, switched state-space systems, and periodic push-pull or gradient-tracking models change the two block index types, scalar semiring, schedule, start, and window length while retaining zero tracker-to-primal coupling in every selected step and therefore in the window product.
-- counterargument checked: Mathlib's `Matrix.BlockTriangular.mul` preserves block triangularity for one multiplication, but neither Mathlib nor SOptLib lifts the invariant through a nonautonomous consecutive window; the theorem packages that reusable induction and is not a paper-local alpha-zero wrapper.
-- coverage search: lean_search_symbols queries "consecutive matrix product upper right block equals zero when each factor upper right block equals zero" and "block lower triangular matrices product upper right block zero" found only the source-local restricted-product facts; LeanSearch found `Matrix.BlockTriangular.mul`, `Matrix.toBlocks₁₂_diagonal`, and block decomposition primitives, but no consecutive time-varying product theorem.
-- minimal hypotheses: `[Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Semiring R]` are exactly those needed for square matrix multiplication and identity on `I ⊕ J`; the zero-block premise is restricted to offsets inside the requested window.

/-- A consecutive product of two-block matrices has zero upper-right block
when every factor in the selected window has zero upper-right block.

Layer: Model | Gap: Level 1 (zero upper-right block invariant for time-varying consecutive matrix products)
Proof: induct on the window length, split each successor matrix product over the sum index, and use the zero upper-right block of the newest factor together with the induction hypothesis for the preceding product.
Source: Mathlib sum-indexed matrix blocks, `Matrix.toBlocks₁₂`, finite matrix multiplication, and zero finite sums
Used in: lifted linear recursions and periodic push-pull or gradient-tracking state-space models, where tracker coordinates cannot feed into primal coordinates at any step and hence cannot do so over a finite propagation window
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveMatrixProduct_toBlocks_of_upperRight_eq_zero
    {I J R : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Semiring R]
    (A : Nat -> Matrix (Sum I J) (Sum I J) R) (start n : Nat)
    (hA : ∀ s < n, (A (start + s)).toBlocks₁₂ = 0) :
    (consecutiveProduct A start n).toBlocks₁₂ = 0 := by
  induction n with
  | zero =>
      ext i j
      simp [Matrix.toBlocks₁₂]
  | succ n ih =>
      have hprev :
          (consecutiveProduct A start n).toBlocks₁₂ = 0 :=
        ih (fun s hs => hA s (Nat.lt_succ_of_lt hs))
      have hstep (i : I) (j : J) :
          A (start + n) (Sum.inl i) (Sum.inr j) = 0 := by
        have hij := congrFun (congrFun (hA n (Nat.lt_succ_self n)) i) j
        simpa [Matrix.toBlocks₁₂] using hij
      have hproduct (i : I) (j : J) :
          consecutiveProduct A start n (Sum.inl i) (Sum.inr j) = 0 := by
        have hij := congrFun (congrFun hprev i) j
        simpa [Matrix.toBlocks₁₂] using hij
      ext i j
      rw [consecutiveProduct_succ]
      simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.zero_apply]
      have hleft :
          (∑ k : I,
            A (start + n) (Sum.inl i) (Sum.inl k) *
              consecutiveProduct A start n (Sum.inl k) (Sum.inr j)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _hk
        simp [hproduct k j]
      have hright :
          (∑ k : J,
            A (start + n) (Sum.inl i) (Sum.inr k) *
              consecutiveProduct A start n (Sum.inr k) (Sum.inr j)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _hk
        simp [hstep i k]
      rw [hleft, hright, add_zero]

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_periodProduct_pow_eq_consecutiveProduct.lean`. -/


namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: power of a full-period ordered product equals the consecutive product over repeated periods; orig was quadraticRestrictedPeriodMatrix_power_eq_consecutiveProduct.
-- generality used: an arbitrary monoid-valued natural-time schedule with a specified natural period; no matrix, finiteness, decidable equality, scalar, topology, norm, measure, stochasticity, convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: periodic consensus, Floquet, switched-system, gossip, push-sum, and lifted-recursion proofs change the ambient monoid, periodic schedule, period, and number of periods while retaining the equality between the phase-zero period-product power and the long consecutive product.
-- counterargument checked: not paper-local or a caller-side wrapper because it combines schedule periodicity, noncommutative adjacent-window composition, and monoid powers into a reusable repeated-period law; Mathlib's list-replication results do not bridge a periodic natural-time schedule to this newest-on-the-left consecutive product.
-- coverage search: lean_search_symbols queries "periodic sequence monoid period product power equals consecutive product" and "consecutive product repeated periods power periodic" found the source theorem and the previously staged `FiniteNetwork.consecutiveProduct_add`, but no theorem with this contract; LeanSearch returned `List.prod_replicate` and `List.prod_eq_pow_card`, which concern already-materialized constant lists rather than periodic schedule windows.
-- minimal hypotheses: `[Monoid M]` supplies exactly identity, multiplication, associativity, and natural powers; `Function.Periodic A p` is the pointwise schedule assumption actually used, and neither `0 < p` nor commutativity is needed.

/-- For a periodic monoid-valued schedule, the power of its phase-zero
full-period product is the consecutive product over the repeated periods.

The ordered product places newer factors on the left, so the result applies to
noncommutative transition operators and matrix products.

Layer: Model | Gap: Level 1 (repeated-period law for ordered monoid schedule products)
Proof: iterate schedule periodicity to identify every block-start window with the phase-zero period, split adjacent windows with `FiniteNetwork.consecutiveProduct_add`, and induct on the number of periods using monoid powers.
Source: Mathlib `Function.Periodic`, natural-number multiplication, and monoid power laws; SOptLib newest-on-the-left consecutive-product composition
Used in: identifying powers of the full-period transition operator with long products of one-step restricted Push--Pull dynamics at complete period boundaries
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodProduct_pow_eq_consecutiveProduct {M : Type*} [Monoid M]
    (A : Nat -> M) (p m : Nat) (hA : Function.Periodic A p) :
    (consecutiveProduct A 0 p) ^ m = consecutiveProduct A 0 (m * p) := by
  have hA_mul (q t : Nat) : A (q * p + t) = A t := by
    induction q with
    | zero => simp
    | succ q ih =>
        have hindex : (q + 1) * p + t = (q * p + t) + p := by
          rw [Nat.succ_mul]
          ac_rfl
        rw [hindex, hA, ih]
  have hstart (q j : Nat) :
      consecutiveProduct A (q * p) j = consecutiveProduct A 0 j := by
    induction j with
    | zero => simp
    | succ j ih =>
        simp only [consecutiveProduct_succ, Nat.zero_add]
        rw [hA_mul q j, ih]
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        (consecutiveProduct A 0 p) ^ (m + 1) =
            consecutiveProduct A 0 p * (consecutiveProduct A 0 p) ^ m := by
              exact pow_succ' _ _
        _ = consecutiveProduct A 0 p * consecutiveProduct A 0 (m * p) := by
              rw [ih]
        _ = consecutiveProduct A (0 + m * p) p *
              consecutiveProduct A 0 (m * p) := by
              rw [Nat.zero_add, hstart]
        _ = consecutiveProduct A 0 (m * p + p) := by
              exact (consecutiveProduct_add A 0 (m * p) p).symm
        _ = consecutiveProduct A 0 ((m + 1) * p) := by
              rw [Nat.succ_mul]

end FiniteNetwork

/-! Phase 4 batch 5: `Module_End_IsRankOneRieszProjectionAt_row_comp_isLeftEigenvector.lean`. -/


open scoped Matrix

-- Generalization plan (G0):
-- concept/name: applying a row on the left preserves a matrix-product scalar-multiple identity; orig was quadraticRestrictedPrimalAverageProjectedRow_left_eigen.
-- generality used: separate finite row and operator index types, a nonunital semiring of matrix entries, and any distributive scalar action commuting with entry multiplication; no square left factor, commutativity, unit, spectral, projection, nonzero-row, norm, topology, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used.
-- portable call pattern: projected linear dynamics, rectangular feature maps, consensus coordinates, and matrix recurrences can turn an intertwining identity into the corresponding identity after applying any row.
-- counterargument checked: this is not paper-local traceability because the premise and conclusion concern only matrix multiplication, vector--matrix action, and scalar multiplication; it is not a pure rename because it composes matrix-action associativity with scalar compatibility.
-- coverage search: `lean_search_symbols` for a vector--matrix action equal to a scalar multiple from a matrix-product scalar-multiple identity found no SOptLib or project declaration with this contract. Mathlib supplies the component identities `Matrix.vecMul_vecMul` and `Matrix.vecMul_smul`.
-- minimal hypotheses: finiteness is required by the two vector--matrix actions; `NonUnitalSemiring R` supports their matrix products, while `DistribSMul S R` and `SMulCommClass S R R` are exactly the assumptions of `Matrix.vecMul_smul`.

/-- Applying a row on the left to a matrix product preserves an equality of
that product with a scalar multiple of its left factor.

Layer: Glue | Gap: Level 1 (matrix intertwining equality under a left row action)
Proof: reassociate the two row actions with `Matrix.vecMul_vecMul`, rewrite by the supplied matrix equality, and move the scalar through the row action using `Matrix.vecMul_smul`.
Source: Mathlib finite-matrix multiplication and vector--matrix action identities `Matrix.vecMul_vecMul` and `Matrix.vecMul_smul`
Used in: projected or rectangular linear-dynamics arguments that first establish a scalar-multiple matrix-product identity and then observe it through a row functional
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Matrix.vecMul_vecMul_eq_smul_of_mul_eq_smul
    {R S m n : Type*} [NonUnitalSemiring R] [Fintype m] [Fintype n]
    [DistribSMul S R] [SMulCommClass S R R]
    (ell : m → R) (P : Matrix m n R) (A : Matrix n n R) (gamma : S)
    (hPA : P * A = gamma • P) :
    (ell ᵥ* P) ᵥ* A = gamma • (ell ᵥ* P) := by
  rw [Matrix.vecMul_vecMul, hPA, Matrix.vecMul_smul]

/-! Phase 4 batch 5: `Matrix_isNormalizedRankOneProjection_of_mul_self_eq_and_finrank_range_eq_one.lean`. -/


open scoped BigOperators Matrix

-- Generalization plan (G0):
-- concept/name: normalized rank-one factorization of an idempotent finite matrix; orig was `rankOneProjection_of_idempotent_finrank_range_eq_one`.
-- generality used: arbitrary commutative field, finite index type, and square matrix; no norm, order, topology, measure, convexity, smoothness, oracle, or algorithm setup assumptions.
-- portable call pattern: finite-dimensional spectral, consensus, and low-rank splitting proofs change the scalar field, index type, and idempotent matrix while reusing the same normalized right/left witness and rank-one action conclusion.
-- counterargument checked: this is not paper-local or a one-line wrapper; idempotence and one-dimensional action range are combined through a chosen linear equivalence to construct biorthogonally normalized witnesses. Mathlib's inner-product `rankOne` lemmas concern already-given rank-one operators, not this converse construction.
-- coverage search: `lean_search_symbols` queries for an idempotent matrix with one-dimensional range and normalized rank-one action found only rank-many outer-product decompositions in `SOptLib.Model.Tensors`/`SOptLib.Glue.Algebra`; LeanSearch returned `InnerProductSpace.isIdempotentElem_rankOne_self_iff` and related forward facts, none with this converse signature.
-- minimal hypotheses: `[Field 𝕜]` supplies exactly the commutative scalar arithmetic and nontriviality used by the coefficient construction; `[Fintype ι]` is required for matrix action and dot products, while decidable equality is chosen classically inside the proof for coordinate singleton vectors.

/-- An idempotent finite square matrix with one-dimensional action range admits
nonzero right and left vectors whose dot product is one and whose normalized
rank-one action equals the matrix action.

Layer: Glue | Gap: Level 2 (normalized rank-one factorization of a one-dimensional idempotent matrix)
Proof: identify the one-dimensional range of `P.mulVecLin` with the scalar field, choose the image of one as the right vector, and read the left coefficients from the images of coordinate singleton vectors. Idempotence fixes the right vector and forces the coefficient pairing to normalize to one.
Source: Mathlib finite free-module dimension theory (`Module.nonempty_linearEquiv_of_finrank_eq_one`) and finite matrix linear-map actions (`Matrix.mulVecLin`)
Used in: analytic spectral and distributed-consensus splittings after rank constancy proves that an idempotent Riesz or consensus projection has one-dimensional range
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Matrix.isNormalizedRankOneProjection_of_mul_self_eq_and_finrank_range_eq_one
    {𝕜 ι : Type*} [Field 𝕜] [Fintype ι]
    (P : Matrix ι ι 𝕜)
    (hidempotent : P * P = P)
    (hrange_dim :
      Module.finrank 𝕜
          (LinearMap.range
            (Matrix.mulVecLin P : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))) = 1) :
    P * P = P ∧
      ∃ right left : ι → 𝕜,
        right ≠ 0 ∧ left ≠ 0 ∧ dotProduct left right = 1 ∧
          ∀ x : ι → 𝕜, P *ᵥ x = dotProduct left x • right := by
  classical
  let L : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜) := Matrix.mulVecLin P
  have hL_idem : ∀ x : ι → 𝕜, L (L x) = L x := by
    intro x
    simpa [L] using congrFun (congrArg Matrix.mulVec hidempotent) x
  obtain ⟨e⟩ :=
    Module.nonempty_linearEquiv_of_finrank_eq_one
      (R := 𝕜) (M := LinearMap.range L) (by simpa [L] using hrange_dim)
  let right : ι → 𝕜 := ((e (1 : 𝕜) : LinearMap.range L) : ι → 𝕜)
  let left : ι → 𝕜 := fun j : ι =>
    e.symm
      ⟨L (Pi.single j (1 : 𝕜)),
        LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩
  have hright_sub_ne : e (1 : 𝕜) ≠ (0 : LinearMap.range L) := by
    intro hzero
    exact (one_ne_zero : (1 : 𝕜) ≠ 0) (by simpa using congrArg e.symm hzero)
  have hright_ne : right ≠ 0 := by
    intro hzero
    exact hright_sub_ne (Subtype.ext hzero)
  have hright_fixed : P *ᵥ right = right := by
    have hmem : right ∈ LinearMap.range L := (e (1 : 𝕜)).property
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
    calc
      P *ᵥ right = L right := by rfl
      _ = L (L y) := by rw [hy]
      _ = L y := hL_idem y
      _ = right := hy
  have hnormalized : dotProduct left right = 1 := by
    have hright_col :
        (⟨L right, LinearMap.mem_range_self L right⟩ : LinearMap.range L) =
          e (1 : 𝕜) := by
      ext i
      simpa [right, L] using congrFun hright_fixed i
    have hcoeff :
        e.symm
            (⟨L right, LinearMap.mem_range_self L right⟩ :
              LinearMap.range L) = 1 := by
      rw [hright_col]
      simp
    have hdecomp :
        (⟨L right, LinearMap.mem_range_self L right⟩ : LinearMap.range L) =
          ∑ j : ι,
            right j •
              (⟨L (Pi.single j (1 : 𝕜)),
                LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                  LinearMap.range L) := by
      ext i
      simp [L, Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.sum_apply,
        mul_comm]
    calc
      dotProduct left right =
          ∑ j : ι,
            right j *
              e.symm
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L) := by
            simp [left, dotProduct, mul_comm]
      _ =
          ∑ j : ι,
            e.symm
              (right j •
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
              (e.symm.map_smul (right j)
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L)).symm
      _ =
          e.symm
            (∑ j : ι,
              right j •
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L)) := by
            rw [map_sum]
      _ =
          e.symm
            (⟨L right, LinearMap.mem_range_self L right⟩ :
              LinearMap.range L) := by
            rw [← hdecomp]
      _ = 1 := hcoeff
  have hleft_ne : left ≠ 0 := by
    intro hleft_zero
    have hzero : dotProduct left right = 0 := by simp [hleft_zero]
    exact zero_ne_one (hzero ▸ hnormalized)
  refine ⟨hidempotent, right, left, hright_ne, hleft_ne, hnormalized, ?_⟩
  intro x
  let yx : LinearMap.range L :=
    ⟨L x, LinearMap.mem_range_self L x⟩
  have hspan (c : 𝕜) :
      ((e c : LinearMap.range L) : ι → 𝕜) = c • right := by
    have hmap := congrArg Subtype.val (e.map_smul c (1 : 𝕜))
    simpa [right] using hmap
  have hdecomp :
      yx =
        ∑ j : ι,
          x j •
            (⟨L (Pi.single j (1 : 𝕜)),
              LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                LinearMap.range L) := by
    ext i
    simp [yx, L, Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.sum_apply,
      mul_comm]
  have hcoeff : e.symm yx = dotProduct left x := by
    calc
      e.symm yx =
          e.symm
            (∑ j : ι,
              x j •
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L)) := by
            rw [hdecomp]
      _ =
          ∑ j : ι,
            e.symm
              (x j •
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L)) := by
            rw [map_sum]
      _ = dotProduct left x := by
            apply Finset.sum_congr rfl
            intro j _hj
            simpa [left, dotProduct, smul_eq_mul, mul_comm, mul_left_comm,
              mul_assoc] using
              (e.symm.map_smul (x j)
                (⟨L (Pi.single j (1 : 𝕜)),
                  LinearMap.mem_range_self L (Pi.single j (1 : 𝕜))⟩ :
                    LinearMap.range L))
  calc
    P *ᵥ x = L x := by rfl
    _ = ((yx : LinearMap.range L) : ι → 𝕜) := rfl
    _ = ((e (e.symm yx) : LinearMap.range L) : ι → 𝕜) := by
      rw [LinearEquiv.apply_symm_apply]
    _ = e.symm yx • right := hspan (e.symm yx)
    _ = dotProduct left x • right := by rw [hcoeff]

/-! Phase 4 batch 5: `FiniteNetwork_zeroSum_fixedPoint_eq_zero_of_periodic_geometric_contraction.lean`. -/


open Filter

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: uniqueness of the zero fixed point under periodic geometric contraction; orig was `real_pull_period_fixed_point_is_zero`.
-- generality used: an arbitrary finite node type, normed additive state space with a real scalar action, a natural-indexed family of real node matrices representing product windows, a positive period, and a geometric contraction rate; no scalar-action laws, nonempty-node, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, stochasticity, or graph assumptions are used once repeated-period fixedness and contraction are available.
-- portable call pattern: periodic consensus, push-sum, and gradient-tracking proofs change the matrix-product family, period, contraction prefactor and rate, and state while reusing the conclusion that a state fixed at every period multiple must vanish.
-- counterargument checked: this is not paper-local traceability or a one-line wrapper because it packages the limiting argument that turns repeated-period invariance plus a geometric product estimate into fixed-point uniqueness; Mathlib's contraction-mapping theorems require a globally contracting self-map, while the available SOptLib periodic-product lemmas provide product identities but not this fixed-point uniqueness conclusion.
-- coverage search: `lean_search_symbols` queries "periodic matrix product fixed point geometric contraction norm zero", "fixed point zero contraction iterates norm bound", and "periodic consecutive product fixed point zero geometric contraction" found only the paper-local source, `FiniteNetwork.periodProduct_pow_eq_consecutiveProduct`, and the component geometric-tail argument; LeanSearch queries for a fixed point of geometrically contracting iterates found Mathlib's stronger `ContractingWith` API and power-limit lemmas, but no declaration with this contract.
-- minimal hypotheses: `[Fintype Node]` and `[NormedAddCommGroup E]` support the finite `PiLp 2` norm, while `[SMul ℝ E]` supplies exactly the real matrix action; positivity of the period and `0 ≤ q < 1` are exactly what makes the period-sampled geometric factor tend to zero, while no sign condition on `K` is needed. The contraction premise is required only at period multiples for the fixed state under consideration.

/-- A state fixed at every multiple of a positive period is zero when
its period-multiple product windows obey a geometric contraction estimate with
rate below one.

The matrices are the already-formed product windows. This separates the
periodic product algebra establishing repeated fixedness from the norm-decay
argument establishing uniqueness of the zero fixed point.

Layer: Model | Gap: Level 1 (periodic-product fixed-point uniqueness from geometric contraction)
Proof: evaluate the contraction estimate at period multiples, rewrite the acted-on state using repeated fixedness, and pass to the limit along the geometric powers; nonnegativity of the norm then forces the finite `PiLp 2` norm, and hence every coordinate, to vanish.
Source: Mathlib finite `PiLp` norms, geometric-power convergence, and order-closed limit inequalities
Used in: the tracker block of periodic Push--Pull and gradient-tracking fixed-point arguments, after periodic product composition shows that a one-period fixed state is fixed at every complete period
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem fixedPoint_eq_zero_of_periodic_geometric_contraction
    {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [SMul ℝ E]
    (C : Nat -> Matrix Node Node ℝ) (p : Nat) (K q : ℝ)
    (w : Node → E)
    (hp : 0 < p) (hq_nonneg : 0 <= q) (hq_lt_one : q < 1)
    (hfixed_periods : forall m : Nat,
      Matrix.smulVec (C (m * p)) w = w)
    (hcontract : forall m : Nat,
      ‖(WithLp.toLp 2 (Matrix.smulVec (C (m * p)) w) :
          PiLp 2 (fun _ : Node => E))‖ <=
        K * q ^ (m * p) *
          ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Node => E))‖) :
    w = 0 := by
  classical
  let wNorm : ℝ :=
    ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Node => E))‖
  have hperiod_rate_nonneg : 0 <= q ^ p := pow_nonneg hq_nonneg p
  have hperiod_rate_lt_one : q ^ p < 1 :=
    pow_lt_one₀ hq_nonneg hq_lt_one (Nat.ne_of_gt hp)
  have hbound : forall m : Nat,
      wNorm <= K * (q ^ p) ^ m * wNorm := by
    intro m
    have hm := hcontract m
    have hpow : q ^ (m * p) = (q ^ p) ^ m := by
      rw [Nat.mul_comm, pow_mul]
    simpa only [wNorm, hfixed_periods m, hpow] using hm
  have hgeom :
      Tendsto (fun m : Nat => (q ^ p) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      hperiod_rate_nonneg hperiod_rate_lt_one
  have hlimit :
      Tendsto (fun m : Nat => K * (q ^ p) ^ m * wNorm) atTop (nhds 0) := by
    simpa using (hgeom.const_mul K).mul_const wNorm
  have hwNorm_le_zero : wNorm <= 0 := ge_of_tendsto' hlimit hbound
  have hwNorm_zero : wNorm = 0 :=
    le_antisymm hwNorm_le_zero (norm_nonneg _)
  have hwPi_zero :
      (WithLp.toLp 2 w : PiLp 2 (fun _ : Node => E)) = 0 :=
    norm_eq_zero.mp hwNorm_zero
  funext i
  have hi := congrArg
    (fun x : PiLp 2 (fun _ : Node => E) => x i) hwPi_zero
  simpa using hi

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_isAgreementState_of_periodProduct_fixed_of_geometric_consensusError.lean`. -/


noncomputable section

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: agreement of a period-product fixed state under geometric consensus-error contraction; orig was `real_push_period_fixed_point_is_consensus`.
-- generality used: an arbitrary finite nonempty node type, normed real state space, natural-indexed family of real node matrices representing product windows, positive period, and geometric contraction rate; no inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, stochasticity, or graph assumptions are used once repeated-period fixedness and consensus-error contraction are available.
-- portable call pattern: periodic consensus, gossip, push-sum, and gradient-tracking proofs change the matrix-product family, period, contraction prefactor and rate, and state while reusing the conclusion that a state fixed at every complete period is an agreement state.
-- counterargument checked: this is not paper-local traceability or a pure wrapper because it combines repeated period-product invariance, decay of a nonzero consensus error, and the agreement characterization; the previously staged zero-fixed-point theorem supplies the analytic decay step but does not itself turn consensus-error contraction into node agreement.
-- coverage search: `lean_search_symbols` queries "agreement state fixed point period product geometric consensus error contraction", "consensus error zero iff agreement state finite network", and "repeated period fixed state geometric contraction consensus error" found the source theorem, `FiniteNetwork.fixedPoint_eq_zero_of_periodic_geometric_contraction`, and `FiniteNetwork.isAgreementState_iff_eq_consensusState`, but no declaration with this combined contract; LeanSearch for a fixed point whose error has a geometric bound found Mathlib's stronger global `ContractingWith` API but no pointwise period-product consensus theorem.
-- minimal hypotheses: `[Fintype Node] [Nonempty Node]` support finite averaging and its agreement characterization; `[NormedAddCommGroup E] [NormedSpace Real E]` support the consensus error and finite `PiLp 2` norm; positivity of the period and `0 <= q < 1` are exactly the conditions used by geometric decay, while no sign condition on `K` is needed.

/-- A state fixed by every complete-period product window is an agreement state
when its consensus error obeys a geometric contraction estimate with rate below
one.

The matrices are already-formed product windows. Thus a caller may establish
repeated fixedness using its own periodic product algebra while this theorem
handles the common fixed-point-to-agreement argument.

Layer: Model | Gap: Level 1 (period-product fixed-point agreement from geometric consensus-error contraction)
Proof: rewrite each contracted product state by repeated fixedness, apply periodic geometric fixed-point uniqueness to the consensus error through identity matrix actions, and use the consensus-state characterization of agreement.
Source: Mathlib finite `PiLp` norms and geometric-power convergence, together with SOptLib finite-network consensus error, agreement states, and periodic geometric fixed-point uniqueness
Used in: the primal block of periodic Push--Pull, gossip, and gradient-tracking spectral arguments, where a unit fixed vector of the period map must lie in the node-agreement subspace
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem isAgreementState_of_periodProduct_fixed_of_geometric_consensusError
    {Node E : Type*} [Fintype Node] [Nonempty Node]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (R : Nat -> Matrix Node Node Real) (p : Nat) (K q : Real)
    (x : Node -> E)
    (hp : 0 < p) (hq_nonneg : 0 <= q) (hq_lt_one : q < 1)
    (hfixed_periods : forall m : Nat,
      Matrix.smulVec (R (m * p)) x = x)
    (hcontract : forall m : Nat,
      ‖(WithLp.toLp 2
          (consensusError (Matrix.smulVec (R (m * p)) x)) :
          PiLp 2 (fun _ : Node => E))‖ <=
        K * q ^ (m * p) *
          ‖(WithLp.toLp 2 (consensusError x) :
            PiLp 2 (fun _ : Node => E))‖) :
    IsAgreementState x := by
  classical
  have hidentity (y : Node -> E) :
      Matrix.smulVec (fun i j : Node => if i = j then (1 : Real) else 0) y = y := by
    funext i
    simp [Matrix.smulVec]
  have herror_zero : consensusError x = 0 := by
    apply fixedPoint_eq_zero_of_periodic_geometric_contraction
      (C := fun _ i j => if i = j then 1 else 0)
      (p := p) (K := K) (q := q) (w := consensusError x)
      hp hq_nonneg hq_lt_one
    · intro m
      exact hidentity (consensusError x)
    · intro m
      rw [hidentity]
      simpa only [hfixed_periods m] using hcontract m
  rw [isAgreementState_iff_eq_consensusState]
  rw [consensusError_def] at herror_zero
  exact sub_eq_zero.mp herror_zero

end FiniteNetwork

/-! Phase 4 batch 5: `Matrix_statePairwiseDiameter_mulVec_le_one_sub_card_mul_of_mem_rowStochastic_of_minorized.lean`. -/


noncomputable section

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: Dobrushin diameter-of-range contraction for a uniformly minorized row-stochastic matrix; orig was `rowMinorized_statePairwiseDiameter_contraction`.
-- generality used: arbitrary finite decidable node type and real seminormed module; no nonemptiness, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or algorithm-setup assumptions.
-- portable call pattern: finite-network consensus, gossip, push-sum, and gradient-tracking proofs change the node type, row-stochastic matrix, common entry minorization, vector-valued state space, and state while retaining the same `1 - card * beta` pairwise-diameter contraction.
-- counterargument checked: not paper-local or a caller-side wrapper because it packages the Dobrushin residual-row decomposition, including the degenerate zero-residual case; Mathlib's row-stochastic API and the staged finite-barycenter diameter theorem each cover only components of this complete contraction step.
-- coverage search: `lean_search_symbols` queries "row stochastic matrix common entry lower bound contracts pairwise diameter one minus cardinality beta" and "Matrix smulVec diameter range upper bound minorized entries row stochastic" found only the source-local theorem, Mathlib row-stochastic projections, and the staged barycenter diameter bound; `lean_leansearch` found doubly-stochastic membership and operator-norm facts but no row-minorization diameter contraction.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support the stochastic-matrix predicate and finite sums; the empty case is discharged separately, while a row exists in the nonempty case to prove the contraction factor nonnegative; `[SeminormedAddCommGroup E] [NormedSpace Real E]` are exactly the subtraction, norm, finite-sum, and real-scalar structures used.

namespace Matrix

/-- A finite real row-stochastic matrix whose entries share a lower bound
`beta` contracts the pairwise diameter of a module-valued state by the
Dobrushin factor `1 - card Node * beta`.

Layer: Model | Gap: Level 1 (uniformly minorized row-stochastic diameter contraction)
Proof: subtract the common `beta` mass from two rows and normalize the residual rows; apply the finite-barycenter diameter bound, treating the zero residual mass separately.
Source: Mathlib row-stochastic matrices and finite sums, together with the Dobrushin contraction argument for finite Markov kernels
Used in: blockwise consensus estimates for row-stochastic communication products, where a common positive entry floor yields geometric contraction of node-state disagreement
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem diam_range_smulVec_le_one_sub_card_mul_of_mem_rowStochastic_of_minorized
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup E] [NormedSpace Real E]
    {A : Matrix Node Node Real} {beta : Real}
    (hA : A ∈ rowStochastic Real Node)
    (hbeta : forall i j : Node, beta <= A i j) (X : Node -> E) :
    Metric.diam (Set.range (smulVec A X)) <=
      (1 - (Fintype.card Node : Real) * beta) *
        Metric.diam (Set.range X) := by
  classical
  rcases isEmpty_or_nonempty Node with hNode | hNode
  · letI := hNode
    simp only [Set.range_eq_empty, Metric.diam_empty, mul_zero, le_refl]
  letI := hNode
  let c : Real := 1 - (Fintype.card Node : Real) * beta
  have hc_nonneg : 0 <= c := by
    have hsum : ∑ j : Node, beta <=
        ∑ j : Node, A (Classical.choice (inferInstance : Nonempty Node)) j :=
      Finset.sum_le_sum fun j _ => hbeta _ j
    rw [sum_row_of_mem_rowStochastic hA] at hsum
    simpa [c] using hsum
  apply Metric.diam_le_of_forall_dist_le_of_nonempty (Set.range_nonempty _)
  rintro xi ⟨i, rfl⟩ xk ⟨k, rfl⟩
  simp only [dist_eq_norm]
  by_cases hc : c = 0
  · have hrow_eq (u : Node) (j : Node) : A u j = beta := by
      have hnonneg : ∀ v ∈ (Finset.univ : Finset Node),
          0 <= A u v - beta := by
        intro v _
        exact sub_nonneg.mpr (hbeta u v)
      have hsumzero : ∑ v : Node, (A u v - beta) = 0 := by
        rw [Finset.sum_sub_distrib, sum_row_of_mem_rowStochastic hA]
        simpa [c] using hc
      have hvzero :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumzero j
          (Finset.mem_univ j)
      linarith
    have hmul : smulVec A X i = smulVec A X k := by
      simp only [smulVec_apply, hrow_eq]
    calc
      ‖smulVec A X i - smulVec A X k‖ = 0 := by rw [hmul, sub_self, norm_zero]
      _ <= (1 - (Fintype.card Node : Real) * beta) *
          Metric.diam (Set.range X) := by
        have hfactor : 1 - (Fintype.card Node : Real) * beta = 0 := by
          simpa [c] using hc
        rw [hfactor, zero_mul]
  · let p : Node -> Real := fun j => (A i j - beta) / c
    let q : Node -> Real := fun j => (A k j - beta) / c
    have hp : forall j : Node, 0 <= p j :=
      fun j => div_nonneg (sub_nonneg.mpr (hbeta i j)) hc_nonneg
    have hq : forall j : Node, 0 <= q j :=
      fun j => div_nonneg (sub_nonneg.mpr (hbeta k j)) hc_nonneg
    have hp_sum : ∑ j : Node, p j = 1 := by
      simp only [p, div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib,
        sum_row_of_mem_rowStochastic hA]
      simpa [c] using (mul_inv_cancel₀ hc)
    have hq_sum : ∑ j : Node, q j = 1 := by
      simp only [q, div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib,
        sum_row_of_mem_rowStochastic hA]
      simpa [c] using (mul_inv_cancel₀ hc)
    have hdecomp (u : Node) :
        smulVec A X u =
          (∑ j : Node, (A u j - beta) • X j) +
            beta • ∑ j : Node, X j := by
      rw [smulVec_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← add_smul]
      congr 1
      ring
    have hp_residual :
        (∑ j : Node, (A i j - beta) • X j) =
          c • ∑ j : Node, p j • X j := by
      simp only [p, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      field_simp
    have hq_residual :
        (∑ j : Node, (A k j - beta) • X j) =
          c • ∑ j : Node, q j • X j := by
      simp only [q, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      field_simp
    have hrewrite :
        smulVec A X i - smulVec A X k =
          c • ((∑ j : Node, p j • X j) -
            ∑ j : Node, q j • X j) := by
      rw [hdecomp i, hdecomp k, hp_residual, hq_residual, smul_sub]
      abel
    rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
    exact mul_le_mul_of_nonneg_left
      (FiniteNetwork.norm_sum_smul_sub_sum_smul_le_diam_range
        p q hp hq hp_sum hq_sum X) hc_nonneg

end Matrix

/-! Phase 4 batch 5: `Matrix_statePairwiseDiameter_mulVec_le_of_mem_rowStochastic.lean`. -/


noncomputable section

-- Generalization plan (G0):
-- concept/name: pairwise-diameter nonexpansiveness of a row-stochastic matrix action; orig was `rowStochastic_statePairwiseDiameter_leftMul_le`.
-- generality used: arbitrary finite decidable node type and real seminormed module; no nonemptiness, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or algorithm-setup assumptions.
-- portable call pattern: consensus, gossip, push-sum, and gradient-tracking proofs change the row-stochastic mixing matrix, finite node type, vector-valued state space, and state while using the same diameter nonexpansiveness estimate for incomplete product windows.
-- counterargument checked: the result is a specialization of the stronger Dobrushin minorization theorem, but it removes the auxiliary entry-floor hypothesis and contraction coefficient at the common row-stochastic remainder-window call site; Mathlib has no theorem exposing this matrix-to-diameter contract directly.
-- coverage search: `lean_search_symbols` queries "row stochastic matrix vector valued state pairwise diameter upper bound nonexpansive", "diameter range matrix smulVec less equal diameter row stochastic", and "statePairwiseDiameter mulVec rowStochastic" found the paper-local source theorem, the staged strictly stronger minorization theorem, and component barycenter bounds but no assumption-matching public theorem; `lean_leansearch` queries for row-stochastic diameter nonexpansiveness and distances between convex combinations found row-stochastic membership, `convexHull_exists_dist_ge2`, and `Metric.dist_le_diam_of_mem`, but no complete matrix-action statement.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` are required by Mathlib's row-stochastic matrix predicate; `[SeminormedAddCommGroup E] [NormedSpace Real E]` are exactly the structures required by the vector-valued Dobrushin theorem, and the empty-node case is already handled there.

namespace Matrix

/-- A finite real row-stochastic matrix acting on a module-valued state does
not increase the diameter of the state's range.

Layer: Model | Gap: Level 1 (row-stochastic pairwise-diameter nonexpansiveness)
Proof: specialize the Dobrushin diameter contraction theorem to the common entry lower bound zero, supplied by row-stochastic entry nonnegativity, and simplify its contraction factor to one.
Source: Mathlib `Matrix.rowStochastic` and finite range diameter, together with the finite-state Dobrushin contraction theorem
Used in: arbitrary remainder windows of row-stochastic communication products, where consensus and gradient-tracking estimates need diameter control without a positive minorization bound
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem diam_range_smulVec_le_of_mem_rowStochastic
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup E] [NormedSpace Real E]
    {A : Matrix Node Node Real} (hA : A ∈ rowStochastic Real Node)
    (X : Node -> E) :
    Metric.diam (Set.range (smulVec A X)) <= Metric.diam (Set.range X) := by
  simpa using
    (diam_range_smulVec_le_one_sub_card_mul_of_mem_rowStochastic_of_minorized
      (A := A) (beta := 0) hA
      (fun i j => nonneg_of_mem_rowStochastic hA) X)

end Matrix

/-! Phase 4 batch 5: `FiniteNetwork_periodicCorrectedLift_smul.lean`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: homogeneity of the phase-indexed corrected lift for a periodic finite network; orig was `scalarCorrectedLift_smul_real`.
-- generality used: arbitrary finite node carrier and normed real vector space, explicit phase-weight and transition-product streams, a real scalar, and summability of the unscaled corrected-lift series; no nonempty-node, inner-product, complete-space, finite-dimensional, stochasticity, positivity, periodicity, measure, convexity, smoothness, or oracle assumptions are used by homogeneity.
-- portable call pattern: a future periodic push-sum, gradient-tracking, or push-pull proof changes the node type, normed optimization space, phase-weight sequence, transition products, phase, and zero-sum state while reusing the same corrected-lift homogeneity conclusion.
-- counterargument checked: the final infinite-sum step is supported by Mathlib's `Summable.tsum_const_smul`, but the candidate is not a pure wrapper because it also establishes that the concrete weighted matrix-propagation summands commute with scaling on the zero-sum carrier; naming the corrected lift exposes a reusable network operator rather than a caller-side expression.
-- coverage search: `lean_search_symbols` queries "corrected lift weighted propagated zero sum state infinite series scalar homogeneous", "matrix action on module valued vector commutes with scalar multiplication", and "weighted finite sum scalar multiplication homogeneity" found only the paper-local corrected-lift declarations and the previously staged `Matrix.smulVec`; LeanSearch found `Summable.tsum_const_smul` for the terminal series interchange but no corrected-lift or finite-network theorem covering the full statement.
-- minimal hypotheses: `[Fintype Node]` supports the two finite contractions, and `[NormedAddCommGroup E] [NormedSpace ℝ E]` support the real-linear finite and infinite sums; `tsum_const_smul''` commutes the outer scalar with `tsum` without a summability hypothesis.

/-- The corrected lift associated with phase weights and transition products is
the infinite sum of the weighted propagated zero-sum state.

Layer: Model | Concept: phase-indexed finite-network corrected lift
Proof: (definitional construction; an infinite sum of phase-weighted matrix propagations of a zero-sum state)
Source: Mathlib finite matrix actions and topological infinite sums, together with the periodic-network corrected-lift series from finite-state Poisson equations
Used in: periodic push-pull influence calculations where a zero-sum pull innovation is propagated through all future communication products and tested against the future left Perron weights
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec/parameters/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def periodicCorrectedLift {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (leftWeight : ℕ → Node → ℝ)
    (transitionProduct : ℕ → ℕ → Matrix Node Node ℝ)
    (t : ℕ) (W : ZeroSumState Node E) : E :=
  ∑' j : ℕ,
    ∑ i : Node,
      leftWeight (t + j + 1) i • Matrix.smulVec (transitionProduct t j) W.1 i

/-- The phase-indexed corrected lift unfolds to its weighted
matrix-propagation series.

Layer: Model | Gap: Level 0 (phase-indexed corrected-lift unfolding)
Proof: by rfl after unfolding `FiniteNetwork.periodicCorrectedLift`.
Source: Mathlib finite matrix actions and topological infinite sums, together with the periodic-network corrected-lift series from finite-state Poisson equations
Used in: identifying a paper-facing Perron-weighted pull-product series with the reusable corrected-lift object before applying its linearity and convergence API
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec/parameters/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem periodicCorrectedLift_def {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (leftWeight : ℕ → Node → ℝ)
    (transitionProduct : ℕ → ℕ → Matrix Node Node ℝ)
    (t : ℕ) (W : ZeroSumState Node E) :
    periodicCorrectedLift leftWeight transitionProduct t W =
      ∑' j : ℕ,
        ∑ i : Node,
          leftWeight (t + j + 1) i •
            Matrix.smulVec (transitionProduct t j) W.1 i := by
  rfl

/-- Scaling a zero-sum state scales its phase-indexed corrected lift by the
same real scalar.

Layer: Model | Gap: Level 1 (homogeneity of a corrected-lift infinite series)
Proof: commute the scalar through both finite matrix contractions using real-module laws, then use `tsum_const_smul''` to commute it through the infinite series.
Source: Mathlib `Finset.smul_sum`, real normed-space scalar associativity, `Matrix.smulVec`, and `tsum_const_smul''`
Used in: solving the two-phase corrected-lift Poisson system by reducing every scalar multiple of a canonical zero-sum innovation to the corresponding multiple of one base corrected-lift value
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec/parameters/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLift_smul {Node E : Type*} [Fintype Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (leftWeight : ℕ → Node → ℝ)
    (transitionProduct : ℕ → ℕ → Matrix Node Node ℝ)
    (t : ℕ) (c : ℝ) (W : ZeroSumState Node E) :
    periodicCorrectedLift leftWeight transitionProduct t
        ⟨fun i : Node => c • W.1 i, by
          change ∑ i : Node, c • W.1 i = 0
          rw [← Finset.smul_sum, W.2, smul_zero]⟩ =
      c • periodicCorrectedLift leftWeight transitionProduct t W := by
  rw [periodicCorrectedLift, periodicCorrectedLift]
  calc
    (∑' j : ℕ,
        ∑ i : Node,
          leftWeight (t + j + 1) i •
            Matrix.smulVec (transitionProduct t j) (fun k => c • W.1 k) i) =
        ∑' j : ℕ, c •
          (∑ i : Node,
            leftWeight (t + j + 1) i •
              Matrix.smulVec (transitionProduct t j) W.1 i) := by
      apply tsum_congr
      intro j
      simp [Matrix.smulVec_apply, Finset.smul_sum, smul_smul,
        mul_comm, mul_assoc]
    _ = c • ∑' j : ℕ,
          ∑ i : Node,
            leftWeight (t + j + 1) i •
              Matrix.smulVec (transitionProduct t j) W.1 i :=
      tsum_const_smul'' c

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_periodicCorrectedLift_add_period_mul.lean`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: invariance of a periodic finite-network corrected lift after any whole number of schedule periods; orig was `correctedLift_blockStart`.
-- generality used: arbitrary finite node carrier with decidable equality, real normed vector state space, matrix and Perron-weight schedules with a common natural period, reference phase, block number, and zero-sum state; no positive-period, stochasticity, positivity, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic consensus, push-sum, push-pull, and gradient-tracking proofs change the communication schedule, Perron weights, state space, reference phase, and block number while identifying the infinite-series corrected lift in any block with the lift at the corresponding reference phase.
-- counterargument checked: this is not paper-local traceability or a pure rename of the summand result because callers need equality of the concrete `periodicCorrectedLift` infinite-series object; the theorem packages the nontrivial transport of every ordered-product summand through `tsum` and strengthens the source's phase-zero statement to every phase.
-- coverage search: `lean_search_symbols` queries "periodic corrected lift equality after adding period multiple periodic matrix Perron weights" and "infinite sum functions equal pointwise periodic terms shifted by period multiple" found `FiniteNetwork.periodicCorrectedLift`, the termwise `FiniteNetwork.periodicCorrectedLiftSeriesTerm_add_period_mul`, and no full-lift periodicity theorem; LeanSearch for "infinite sum of a periodic family is unchanged when the base index is shifted by a multiple of the period" found generic `Function.Periodic` and `Equiv.tsum_eq` results but no theorem for this corrected-lift contract, so coverage is partial rather than duplicative.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite weighted matrix actions and ordered products; `[NormedAddCommGroup E] [NormedSpace Real E]` are exactly the current `periodicCorrectedLift` object's carrier assumptions; `hC` and `hpi` are the only schedule properties used, and neither summability nor period positivity is required because equality is pointwise before `tsum`.

/-- A finite-network corrected lift built from matrix and weight schedules with a
common period is unchanged when its base phase is shifted by any natural
multiple of that period.

Layer: Model | Gap: Level 1 (period-multiple invariance of a corrected-lift infinite series)
Proof: unfold the concrete corrected lift, use `FiniteNetwork.periodicCorrectedLiftSeriesTerm_add_period_mul` for every lag, and lift the pointwise equality through `tsum_congr`.
Source: Mathlib topological infinite sums and `Function.Periodic` natural-multiple laws, together with the SOptLib periodic corrected-lift and consecutive-product Model APIs
Used in: periodic consensus, push-sum, push-pull, and gradient-tracking block arguments that replace a corrected lift at a block phase by the corresponding lift in the reference block
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLift_add_period_mul
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (period t k : Nat) (W : ZeroSumState Node E)
    (hC : Function.Periodic C period) (hpi : Function.Periodic pi period) :
    periodicCorrectedLift pi (fun s j => consecutiveProduct C s j)
        (t + period * k) W =
      periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W := by
  rw [periodicCorrectedLift_def, periodicCorrectedLift_def]
  apply tsum_congr
  intro j
  simpa only [periodicCorrectedLiftSeriesTerm_def] using
    (periodicCorrectedLiftSeriesTerm_add_period_mul C pi period t k j W hC hpi)

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_periodicCorrectedLift_poisson.lean`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: Poisson equation for the phase-indexed corrected lift of a finite-network matrix schedule; orig was `correctedLift_poisson`.
-- generality used: arbitrary finite decidable node carrier, normed real vector state space, real matrix and phase-weight schedules, phase, and zero-sum state; the proof uses only preservation of the zero-sum state by the first matrix and summability of the defining source series, with no nonempty-node, stochasticity, positivity, periodicity, contraction-rate, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: time-varying consensus, push-sum, push-pull, and gradient-tracking proofs change the pull schedule, Perron or absolute-probability family, vector state space, phase, and zero-sum innovation while reusing the same head-plus-transported-tail Poisson equation.
-- counterargument checked: not paper-local traceability or a one-line wrapper because it assembles the concrete corrected-lift object, summable infinite-series head-tail decomposition, termwise noncommutative matrix-product transport, and zero-sum subtype witness into the reusable operator identity; the component transport and summability theorems do not themselves provide this conclusion.
-- coverage search: `lean_search_symbols` queries "corrected lift Poisson identity infinite summable series head successor transported zero sum state" and "tsum equals head plus shifted tail summable" found the staged corrected-lift definition, its geometric summability theorem, and `FiniteNetwork.periodicCorrectedLiftSeriesTerm_succ_transport`, while LeanSearch found only the generic `Summable.tsum_eq_zero_add`; no Mathlib or SOptLib theorem states the full finite-network Poisson identity.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite weighted matrix actions and the ordered square-matrix product, `[NormedAddCommGroup E] [NormedSpace Real E]` are exactly the current corrected-lift object's carrier assumptions, `hzero` is exactly the witness needed to form the transported zero-sum state, and `hseries` is exactly the convergence needed to split the source `tsum`.

/-- A summable phase-indexed corrected lift equals its current weighted head
plus the next corrected lift of the state transported by the current matrix.

Layer: Model | Gap: Level 1 (Poisson equation for a summable finite-network corrected lift)
Proof: split the summable defining series with `Summable.tsum_eq_zero_add`, identify the zero-lag product with the identity, and rewrite every successor summand using `FiniteNetwork.periodicCorrectedLiftSeriesTerm_succ_transport`.
Source: finite-state nonhomogeneous Markov-chain Poisson equations, Mathlib topological infinite sums, and the SOptLib consecutive matrix-product corrected-lift API
Used in: time-varying push-pull gradient tracking, where a Perron-weighted correction is advanced by one communication step and its remaining tail is re-expressed at the next phase
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLift_poisson
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (t : Nat) (W : ZeroSumState Node E)
    (hzero : ∑ i : Node, Matrix.smulVec (C t) W.1 i = 0)
    (hseries : Summable
      (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j W)) :
    periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W =
      (∑ i : Node, pi (t + 1) i • W.1 i) +
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
          ⟨Matrix.smulVec (C t) W.1, hzero⟩ := by
  have hhead :
      periodicCorrectedLiftSeriesTerm C pi t 0 W =
        ∑ i : Node, pi (t + 1) i • W.1 i := by
    simp only [periodicCorrectedLiftSeriesTerm_def, consecutiveProduct_zero,
      Nat.add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.smulVec_apply_eq_self_of_eq_identity]
    intro j
    rfl
  calc
    periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W =
        ∑' j : Nat, periodicCorrectedLiftSeriesTerm C pi t j W := by
      simp only [periodicCorrectedLift_def,
        periodicCorrectedLiftSeriesTerm_def]
    _ = periodicCorrectedLiftSeriesTerm C pi t 0 W +
          ∑' j : Nat, periodicCorrectedLiftSeriesTerm C pi t (j + 1) W :=
      hseries.tsum_eq_zero_add
    _ = (∑ i : Node, pi (t + 1) i • W.1 i) +
          ∑' j : Nat, periodicCorrectedLiftSeriesTerm C pi (t + 1) j
            ⟨Matrix.smulVec (C t) W.1, hzero⟩ := by
      rw [hhead]
      congr 1
      apply tsum_congr
      intro j
      exact periodicCorrectedLiftSeriesTerm_succ_transport C pi t j W hzero
    _ = (∑ i : Node, pi (t + 1) i • W.1 i) +
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
          ⟨Matrix.smulVec (C t) W.1, hzero⟩ := by
      simp only [periodicCorrectedLift_def,
        periodicCorrectedLiftSeriesTerm_def]

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_periodicCorrectedLift_sub.lean`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: subtraction law for the phase-indexed corrected lift on zero-sum finite-network states; orig was `correctedLift_sub`.
-- generality used: arbitrary finite decidable node carrier, normed real vector state space, real matrix and phase-weight schedules, phase, and two zero-sum states; only summability of the two defining series is assumed, with no nonempty-node, stochasticity, positivity, periodicity, contraction-rate, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic consensus, push-sum, push-pull, and gradient-tracking proofs change the communication schedule, phase weights, vector state space, phase, and pair of zero-sum states while using the same subtraction law to turn a corrected-lift value bound into a Lipschitz bound.
-- counterargument checked: Mathlib's `Summable.tsum_sub` handles only the terminal infinite-sum interchange, so this is not a pure wrapper or paper-local traceability; the theorem also proves that the concrete Perron-weighted matrix-propagation summands preserve subtraction on the zero-sum carrier.
-- coverage search: `lean_search_symbols` queries "periodic corrected lift preserves subtraction zero sum states summable series", "tsum subtraction summable functions", and "corrected lift additive linear zero sum carrier" found the staged corrected-lift definition and summand additivity but no full subtraction law; LeanSearch found `Summable.tsum_sub`, whose generic series conclusion covers only the final proof step.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite weighted matrix actions and consecutive square-matrix products, `[NormedAddCommGroup E] [NormedSpace Real E]` are exactly the corrected-lift carrier assumptions, and `hW` and `hV` are precisely the convergence hypotheses required by `Summable.tsum_sub`.

/-- A summable phase-indexed corrected lift preserves subtraction of zero-sum
finite-network states.

Layer: Model | Gap: Level 1 (subtraction law for a summable finite-network corrected lift)
Proof: distribute subtraction through each finite matrix action and weighted sum, then apply Mathlib's `Summable.tsum_sub` to the two convergent corrected-lift series.
Source: Mathlib finite matrix-module actions, finite-sum subtraction, and `Summable.tsum_sub`, together with the SOptLib periodic corrected-lift Model API
Used in: periodic push-pull and gradient-tracking regularity arguments that convert a corrected-lift value estimate on a state difference into a Lipschitz estimate between two zero-sum states
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLift_sub
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (t : Nat) (W V : ZeroSumState Node E)
    (hW : Summable (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j W))
    (hV : Summable (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j V)) :
    periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t
        ⟨W.1 - V.1, by
          change ∑ i : Node, (W.1 i - V.1 i) = 0
          rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩ =
      periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W -
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t V := by
  calc
    periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t
        ⟨W.1 - V.1, by
          change ∑ i : Node, (W.1 i - V.1 i) = 0
          rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩ =
        ∑' j : Nat, periodicCorrectedLiftSeriesTerm C pi t j
          ⟨W.1 - V.1, by
            change ∑ i : Node, (W.1 i - V.1 i) = 0
            rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩ := by
      simp only [periodicCorrectedLift_def, periodicCorrectedLiftSeriesTerm_def]
    _ = ∑' j : Nat, (periodicCorrectedLiftSeriesTerm C pi t j W -
          periodicCorrectedLiftSeriesTerm C pi t j V) := by
      apply tsum_congr
      intro j
      simp only [periodicCorrectedLiftSeriesTerm_def, Matrix.smulVec_apply,
        Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
    _ = (∑' j : Nat, periodicCorrectedLiftSeriesTerm C pi t j W) -
        ∑' j : Nat, periodicCorrectedLiftSeriesTerm C pi t j V :=
      hW.tsum_sub hV
    _ = periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W -
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t V := by
      simp only [periodicCorrectedLift_def, periodicCorrectedLiftSeriesTerm_def]

end FiniteNetwork

/-! Phase 4 batch 5: `FiniteNetwork_periodicInfluence_weightedState_eq_perron_add_correctedLift.lean`. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: weighted-state response identity for a periodic finite-network influence row; orig was `influence_weightedState_identity`.
-- generality used: arbitrary finite node carrier with decidable equality, real matrix and Perron-row schedules, a normed real vector space, one phase, one distributed state, summability of the influence-coefficient series, and the zero-sum condition on the one-step matrix innovation; no nonempty-node, stochasticity, positivity, periodicity, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: periodic push-pull, push-sum, and gradient-tracking analyses change the pull matrices, Perron sequence, phase, and vector-valued distributed state while rewriting the full influence-row action as the next Perron-weighted state plus the corrected lift of the pull innovation.
-- counterargument checked: not paper-local traceability or a one-line wrapper because it lifts the already-staged termwise bridge through a summable infinite response series and connects the independently reusable `periodicInfluence` and `periodicCorrectedLift` Model objects; the abstract-function-plus-formula-hypothesis shape was rejected in favor of those concrete objects.
-- coverage search: lean_search_symbols queries "periodic influence weighted state equals Perron weighted state plus corrected lift zero sum matrix innovation", "weighted infinite sum of influence series coefficients equals infinite sum corrected lift terms", and "continuous linear map commutes with tsum finite weighted sum" found the staged termwise bridge `FiniteNetwork.periodicInfluenceSeriesTerm_weightedState` and the two Model definitions but no full response identity; LeanSearch found Mathlib's `ContinuousLinearMap.map_tsum`, which supplies only the infinite-sum transport step.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite matrix contractions, the matrix identity, and weighted-state sums, `[NormedAddCommGroup E] [NormedSpace ℝ E]` support the continuous weighted-state map and corrected-lift series, `hseries` is exactly the convergence needed to transport the influence tail through that map, and `hzero` is exactly the evidence needed to place the one-step innovation in `ZeroSumState`.

/-- Applying a periodic finite-network influence row to a distributed state
equals the next Perron-weighted state plus the corrected lift of the one-step
matrix innovation.

Layer: Model | Gap: Level 2 (full influence response to corrected-lift identity)
Proof: expand the influence into its Perron base and summable tail, transport the tail through the continuous finite weighted-state map with `ContinuousLinearMap.map_tsum`, and identify every image term using `FiniteNetwork.periodicInfluenceSeriesTerm_weightedState`.
Source: finite-state nonhomogeneous Markov-chain response series, Mathlib continuous linear maps and topological infinite sums, and the SOptLib periodic influence and corrected-lift Model APIs
Used in: periodic push-pull and gradient-tracking center recurrences that replace a pull-influence-weighted oracle table by its next Perron average and zero-sum corrected-lift innovation
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluence_weightedState_eq_perron_add_correctedLift
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (t : Nat) (X : Node -> E)
    (hseries : Summable (fun j : Nat => periodicInfluenceSeriesTerm C pi t j))
    (hzero : ∑ i : Node, Matrix.smulVec (C t - 1) X i = 0) :
    (∑ i : Node, periodicInfluence C pi t i • X i) =
      (∑ i : Node, pi (t + 1) i • X i) +
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
          ⟨Matrix.smulVec (C t - 1) X, hzero⟩ := by
  classical
  let Φ : (Node → ℝ) →L[ℝ] E :=
    ∑ i : Node,
      (ContinuousLinearMap.proj i : (Node → ℝ) →L[ℝ] ℝ).smulRight (X i)
  have hΦ (w : Node → ℝ) : Φ w = ∑ i : Node, w i • X i := by
    simp [Φ]
  rw [periodicInfluence_def]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  congr 1
  rw [← hΦ, Φ.map_tsum hseries]
  rw [periodicCorrectedLift_def]
  apply tsum_congr
  intro j
  rw [hΦ]
  exact (periodicInfluenceSeriesTerm_weightedState C pi t j X hzero).trans
    (periodicCorrectedLiftSeriesTerm_def C pi (t + 1) j
      ⟨Matrix.smulVec (C t - 1) X, hzero⟩)

end FiniteNetwork

/-! Phase 4 batch 5: `Module_End_projectionComplementAction_mem_ker_of_idempotent.lean`. -/


-- Generalization plan (G0):
-- concept/name: the complementary action of an idempotent endomorphism lies in its kernel; orig was `spectralStableComplementVector_projection_kernel`.
-- generality used: arbitrary scalar semiring, additive commutative group, and module, with one endomorphism, its idempotence equation, and one vector; no spectral, normed, topological, finite-dimensional, measure, convexity, smoothness, oracle, or algorithm assumptions are used.
-- portable call pattern: spectral splittings, consensus/disagreement decompositions, and slow-stable recurrences change the module, idempotent endomorphism, and vector while reusing that applying `1 - P` produces a vector killed by `P`.
-- counterargument checked: Mathlib has the stronger submodule identity `IsIdempotentElem.ker_eq_range_one_sub`, but no pointwise theorem exposing the frequently used complemented-vector kernel certificate; this is a direct specialization rather than paper-local traceability or a duplicate statement.
-- coverage search: `lean_search_symbols` queries "endomorphism complementary projection action kernel idempotent", "linear endomorphism idempotent range kernel one minus", and "P P equals P P z minus P P z kernel" found only the source theorem and unrelated projection infrastructure; LeanSearch queries "If a linear endomorphism P is idempotent, then P applied to z minus P z is zero" and "complement of an idempotent linear map has range contained in kernel" found `LinearMap.IsIdempotentElem.ker_eq_range_one_sub` as a stronger structural result, but no pointwise corollary.
-- minimal hypotheses: `[Semiring R] [AddCommGroup E] [Module R E]` are exactly the classes needed for `1 - P`; the source's real scalars, finite coordinate type, and matrix representation are eliminated, and the idempotence equation is the sole explicit hypothesis.
-- destination: SOptLib/Glue/Algebra.lean

namespace Module.End

/-- The action of `1 - P` on any vector belongs to the kernel of an
idempotent endomorphism `P`.

Layer: Glue | Gap: Level 0 (pointwise kernel certificate for the complementary action of an idempotent endomorphism)
Proof: rewrite the kernel as the range of `1 - P` using `IsIdempotentElem.ker_eq_range_one_sub`, then use the original vector as the range witness.
Source: Mathlib linear-algebra projection API for idempotent endomorphisms, specifically `LinearMap.IsIdempotentElem.ker_eq_range_one_sub`
Used in: slow-stable spectral and consensus/disagreement decompositions, where initial states and innovations are projected onto the stable complement before invariant-kernel and Duhamel estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem projectionComplementAction_mem_ker_of_idempotent
    {R E : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    (P : Module.End R E) (hP : P * P = P) (z : E) :
    (1 - P) z ∈ LinearMap.ker P := by
  have hP' : IsIdempotentElem P := hP
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP']
  exact ⟨z, rfl⟩

end Module.End

/-! Phase 4 batch 5: `Module_End_projectionComplementAction_split_step.lean`. -/


-- Generalization plan (G0):
-- concept/name: evolution of a complementary-projection action through an endomorphism split; orig was `spectralStableComplementVector_split_step`.
-- generality used: arbitrary scalar semiring, additive commutative group, and module with commuting scalar actions, with three endomorphisms and a scalar satisfying only the idempotence, split, and two annihilation equations; no spectral, normed, topological, finite-dimensional, measure, convexity, smoothness, oracle, or algorithm assumptions are used.
-- portable call pattern: spectral slow/stable decompositions and consensus/disagreement recurrences change the module, projection, stable remainder, slow eigenvalue, state, and innovation while reusing the same complementary-component affine-step identity.
-- counterargument checked: this is not merely the earlier pointwise kernel certificate or a caller-side notation wrapper; it composes the split and both annihilation directions into the recurrence equation needed before a stable Duhamel unrolling, while no existing Mathlib/SOptLib theorem states that full transition.
-- coverage search: `lean_search_symbols` queries "endomorphism complementary projection affine step split annihilation equality", "projection complement action of idempotent annihilates stable endomorphism", and "one minus P applied to A y plus xi equals F one minus P y plus one minus P xi" found only the paper-local source and the staged kernel certificate; LeanSearch found `LinearMap.IsIdempotentElem.range_eq_ker_one_sub`, `LinearMap.IsIdempotentElem.commute_iff`, and `IsLprojection.mul_compl_self`, which provide structural projection facts but not this affine evolution identity.
-- minimal hypotheses: the source's real scalars, finite coordinate type, matrix representation, and spectral interpretation are eliminated; `SMulCommClass R R E` is exactly the compatibility needed to form `gamma • P` as an endomorphism over a possibly noncommutative semiring, and each displayed endomorphism equation is used.

namespace Module.End

/-- Under an idempotent projection and an annihilating slow/stable split, the
complementary component of an affine step evolves by the stable endomorphism
plus the complementary component of the innovation.

Layer: Model | Gap: Level 1 (complementary-component recurrence under an annihilating endomorphism split)
Proof: expand the split endomorphism and the action of `1 - P`; idempotence and the two annihilation equations cancel the slow component and identify the stable action on the complement.
Source: Mathlib linear-endomorphism ring operations, scalar action, and evaluation identities from `Mathlib.LinearAlgebra.Projection`
Used in: slow/stable spectral and consensus/disagreement decompositions, immediately before unrolling the stable component as a forced linear recurrence or Duhamel response
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem projectionComplementAction_split_step
    {R E : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    [SMulCommClass R R E]
    (P F A : Module.End R E) (gamma : R)
    (hPP : P * P = P)
    (hA : A = gamma • P + F)
    (hPF : P * F = 0)
    (hFP : F * P = 0)
    (y xi : E) :
    (1 - P) (A y + xi) = F ((1 - P) y) + (1 - P) xi := by
  have hPPy : P (P y) = P y := by
    simpa only [mul_apply] using congrArg (fun G : Module.End R E => G y) hPP
  have hPFy : P (F y) = 0 := by
    simpa only [mul_apply, LinearMap.zero_apply] using
      congrArg (fun G : Module.End R E => G y) hPF
  have hFPy : F (P y) = 0 := by
    simpa only [mul_apply, LinearMap.zero_apply] using
      congrArg (fun G : Module.End R E => G y) hFP
  rw [hA]
  simp only [LinearMap.sub_apply, one_apply, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul, hPPy, hPFy, hFPy,
    sub_self, smul_zero, zero_add, sub_zero]

end Module.End

/-! Phase 4 batch 5: `Module_End_spectralRemainder.lean`. -/


-- Generalization plan (G0):
-- concept/name: spectral remainder of an endomorphism after removing a distinguished projected mode; orig was `stableComplementMatrix`.
-- generality used: arbitrary semiring and scalar-module carrier for an operator representation, with an operator, scalar, and projector in that carrier; no topology, norm, multiplication on the carrier, finite-dimensionality, measure, convexity, smoothness, oracle, or algorithm setup assumptions are needed by the construction, while the annihilation theorem specializes the carrier to endomorphisms over a commutative semiring.
-- portable call pattern: spectral perturbation, consensus, Markov-operator, and linear stochastic-recursion proofs change the matrix or endomorphism representation, selected eigenvalue, and projector while reusing the same complementary remainder, decomposition, and endomorphism projector-annihilation identities.
-- counterargument checked: although the construction is one formula, it is not paper-only bookkeeping: the source bundle uses the named remainder across analytic-family, eigenspace, resolvent, and power-decay arguments, and the accompanying decomposition/annihilation API gives it stable mathematical behavior beyond a caller-side abbreviation.
-- coverage search: `lean_search_symbols` queries "spectral remainder endomorphism subtract eigenvalue scalar projection definition", "endomorphism spectral remainder matrix minus eigenvalue scalar times projection", and "Module End projection complement A minus lambda P" found paper-local Riesz-projection contracts and the staged `Module.End.IsIsolatedEigenprojection` API but no Mathlib or SOptLib remainder definition; direct searches for `spectralRemainder`, `spectral_remainder`, and stable-complement terminology likewise found no reusable library declaration.
-- minimal hypotheses: the construction and decomposition API need only `Semiring K`, `AddCommGroup Operator`, and `Module K Operator`; the commutative-semiring and endomorphism structure is introduced only by the companion annihilation theorem, and no field operations, finite basis, decidable equality, norm, completeness, or spectral assumptions are needed.
-- destination: SOptLib/Glue/Algebra.lean

namespace SOptLib

/-- The spectral remainder after removing the mode selected by `P` at
eigenvalue `lambda` from a linear operator representation `A`.

Layer: Glue | Concept: linear-operator spectral remainder
Proof: (definitional construction; subtract the eigenvalue-scaled projector from the endomorphism)
Source: linear spectral decomposition and Riesz-projector calculus for matrix and endomorphism representations
Used in: slow-stable splittings of periodic linearizations and consensus operators before proving projector annihilation and geometric decay of the complementary dynamics
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
def spectralRemainder {K Operator : Type*} [Semiring K]
    [AddCommGroup Operator] [Module K Operator]
    (A P : Operator) (lambda : K) : Operator :=
  A - lambda • P

/-- The spectral remainder unfolds to the endomorphism minus the selected
eigenvalue times its projector.

Layer: Glue | Gap: Level 0 (endomorphism spectral-remainder unfolding)
Proof: by rfl after unfolding `SOptLib.spectralRemainder`.
Source: Mathlib linear-map additive and scalar-module operations
Used in: rewriting a named slow-stable complementary operator into the explicit subtraction required by analytic and matrix calculations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem spectralRemainder_def {K Operator : Type*} [Semiring K]
    [AddCommGroup Operator] [Module K Operator] (A P : Operator) (lambda : K) :
    spectralRemainder A P lambda = A - lambda • P := by
  rfl

/-- Adding the removed projected mode back to the spectral remainder recovers
the original endomorphism.

Layer: Glue | Gap: Level 0 (spectral-remainder decomposition identity)
Proof: unfold the spectral remainder and cancel the scaled projector in the additive group of endomorphisms.
Source: Mathlib additive-group structure on linear endomorphisms
Used in: recovering the exact slow-projector plus stable-remainder decomposition of a perturbed period operator
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem smul_add_spectralRemainder
    {K Operator : Type*} [Semiring K] [AddCommGroup Operator] [Module K Operator]
    (A P : Operator) (lambda : K) :
    lambda • P + spectralRemainder A P lambda = A := by
  simp [spectralRemainder]

end SOptLib

namespace Module.End

-- Preserve qualification used by existing clients without placing the generic
-- declaration itself in the endomorphism namespace.
export SOptLib (spectralRemainder)

/-- A commuting eigenprojector annihilates the spectral remainder on both
sides.

Layer: Glue | Gap: Level 1 (spectral-remainder annihilation by an eigenprojector)
Proof: expand the remainder, distribute composition over subtraction, and use idempotence together with the left and right eigenprojection equations.
Source: Mathlib linear-endomorphism composition, scalar multiplication, and idempotent projector algebra
Used in: separating the one-dimensional slow mode from stable complementary dynamics in Riesz spectral splittings
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem mul_spectralRemainder_eq_zero_and_spectralRemainder_mul_eq_zero
    {K V : Type*} [CommSemiring K] [AddCommGroup V] [Module K V]
    (A P : Module.End K V) (lambda : K)
    (hP : P * P = P) (hAP : A * P = lambda • P)
    (hPA : P * A = lambda • P) :
    P * SOptLib.spectralRemainder A P lambda = 0 ∧
      SOptLib.spectralRemainder A P lambda * P = 0 := by
  constructor
  · apply LinearMap.ext
    intro x
    have hPAx := congrArg (fun T : Module.End K V => T x) hPA
    have hPPx := congrArg (fun T : Module.End K V => T x) hP
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at hPAx hPPx
    simp [SOptLib.spectralRemainder, Module.End.mul_apply, hPAx, hPPx]
  · apply LinearMap.ext
    intro x
    have hAPx := congrArg (fun T : Module.End K V => T x) hAP
    have hPPx := congrArg (fun T : Module.End K V => T x) hP
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at hAPx hPPx
    simp [SOptLib.spectralRemainder, Module.End.mul_apply, hAPx, hPPx]

end Module.End

/-! Phase 4 batch 5: `Module_End_spectralRemainder_decomposition_and_annihilation.lean`. -/


-- Generalization plan (G0):
-- concept/name: exact spectral-remainder decomposition and two-sided projector annihilation; orig was `rieszProjection_stableComplementMatrix_algebra`.
-- generality used: an arbitrary algebra over a commutative semiring whose carrier is a ring; only idempotence and the left/right eigenprojection equations are assumed, with no topology, norm, spectrum, Riesz contour, or finite-dimensionality.
-- portable call pattern: spectral perturbation, Markov-operator, and distributed-consensus proofs vary the endomorphism or square-matrix algebra, selected eigenvalue, and commuting idempotent eigenprojection while reusing the same slow-mode plus complementary-remainder splitting and annihilation conclusions.
-- counterargument checked: the decomposition and annihilation conclusions exist separately in the staged spectral-remainder API, but no declaration packages their conjunction; the compound result is the stable proof boundary consumed by spectral splittings rather than a pure rename or paper-local Riesz wrapper.
-- coverage search: symbol queries for "spectral remainder decomposition equality and annihilation idempotent eigenprojection", "endomorphism equals eigenvalue scalar projector plus remainder projector remainder zero both sides", and "projection complement decomposition annihilates projection on both sides" found `SOptLib.smul_add_spectralRemainder` and `Module.End.mul_spectralRemainder_eq_zero_and_spectralRemainder_mul_eq_zero` as partial component results only; Mathlib LeanSearch found eigenspace and idempotent-projection infrastructure but no compound contract.
-- minimal hypotheses: `CommSemiring K`, `Ring Operator`, and `Algebra K Operator` supply exactly the subtraction, multiplication, and central scalar action used; the original field, Riesz-projection, and spectral assumptions are unnecessary once its three algebraic consequences are exposed directly.

namespace SOptLib

/-- An idempotent left-and-right eigenprojection splits an endomorphism into
its selected mode and spectral remainder, which it annihilates on both sides.

Layer: Glue | Gap: Level 1 (spectral-remainder decomposition with two-sided eigenprojector annihilation)
Proof: use the additive spectral-remainder decomposition, distribute multiplication over subtraction, and rewrite by idempotence and both eigenprojection equations.
Source: Mathlib linear-endomorphism composition and scalar-module algebra, organized as the standard algebraic part of Riesz spectral decomposition
Used in: slow-stable splittings of periodic consensus and push-pull linearizations before bounding the complementary dynamics by a geometric rate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem spectralRemainder_decomposition_and_annihilation
    {K Operator : Type*} [CommSemiring K] [Ring Operator]
    [Algebra K Operator] (A P : Operator) (lambda : K)
    (hP : P * P = P) (hAP : A * P = lambda • P)
    (hPA : P * A = lambda • P) :
    A = lambda • P + SOptLib.spectralRemainder A P lambda ∧
      P * SOptLib.spectralRemainder A P lambda = 0 ∧
        SOptLib.spectralRemainder A P lambda * P = 0 := by
  refine ⟨(SOptLib.smul_add_spectralRemainder A P lambda).symm, ?_⟩
  constructor
  · rw [SOptLib.spectralRemainder_def, mul_sub, hPA, mul_smul_comm,
      hP, sub_self]
  · rw [SOptLib.spectralRemainder_def, sub_mul, hAP, smul_mul_assoc,
      hP, sub_self]

end SOptLib

/-! Phase 4 batch 5: `Module_End_spectralRemainder_spectrum_le_of_eigenprojection.lean`. -/


-- Generalization plan (G0):
-- concept/name: spectral-radius bound for the remainder after removing an isolated eigenprojection; orig was `stableComplementMatrix_base_spectrum_le_of_riesz`.
-- generality used: an arbitrary complex module and two endomorphisms; the eigenprojection is exposed only through its two commuting eigenrelations and fixed-space characterization, with no norm, topology, completeness, finite-dimensionality, rank-one representation, contour integral, measure, convexity, smoothness, oracle, or algorithm setup assumptions on the carrier.
-- portable call pattern: spectral perturbation, consensus, Markov-operator, and linear-stability proofs vary the operator, distinguished eigenvalue, stable radius, and associated eigenprojection while concluding that every eigenvalue of the projection-removed remainder lies in the stable-radius disk.
-- counterargument checked: this is not paper-local traceability or a one-line wrapper; it converts an eigenvalue of a different operator into a non-distinguished eigenvalue of the original operator, deriving projector idempotence and kernel membership along the way.
-- coverage search: `lean_search_symbols` queries "endomorphism spectral remainder eigenvalue spectrum norm bound of eigenprojection annihilation" and "eigenvalue of A minus lambda projection is eigenvalue of A projection kernel" found only the staged remainder definition and its algebraic annihilation lemmas; LeanSearch for "linear map eigenvector of A minus scalar multiple of projection eigenprojection kernel" found Mathlib eigenspace primitives but no theorem with this transfer-and-bound contract.
-- minimal hypotheses: the source's simple dominant eigenpair is reduced to nonnegativity of the radius and the pointwise bound on non-distinguished eigenvalues; the Riesz and rank-one assumptions are reduced to the two eigenprojection equations and fixed-space characterization actually used, omitting spectral separation and finite-dimensionality.

/-- Every eigenvalue of the spectral remainder associated with an isolated
eigenprojection has norm at most the bound for the original operator's
non-distinguished eigenvalues.

Layer: Model | Gap: Level 2 (stable-spectrum transfer through an isolated eigenprojection)
Proof: derive projector idempotence from its fixed-space characterization, use projector annihilation to put every nonzero remainder eigenvector in the projector kernel, and transfer it to a non-distinguished eigenvector of the original operator; handle the zero eigenvalue by radius nonnegativity.
Source: Mathlib endomorphism eigenspaces and complex scalar norms, together with SOptLib isolated-eigenprojection and spectral-remainder algebra
Used in: base-point slow-stable spectral splittings for periodic consensus and push-pull operators before spectral upper-semicontinuity and geometric power estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Module.End.spectralRemainder_spectrum_le_of_eigenprojection
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A P : Module.End ℂ V) (lambda0 : ℂ) (r0 : ℝ)
    (hr0 : 0 ≤ r0)
    (hstable : ∀ z : ℂ, A.HasEigenvalue z → z ≠ lambda0 → ‖z‖ ≤ r0)
    (hAP : A * P = lambda0 • P) (hPA : P * A = lambda0 • P)
    (hfix : ∀ x : V, A x = lambda0 • x → P x = x) :
    ∀ z : ℂ,
      (SOptLib.spectralRemainder A P lambda0).HasEigenvalue z →
        ‖z‖ ≤ r0 := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    simpa using hr0
  · obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
    have hP_idem : P * P = P := by
      apply LinearMap.ext
      intro x
      apply hfix (P x)
      have hAPx := congrArg (fun T : Module.End ℂ V => T x)
        hAP
      simpa only [Module.End.mul_apply, LinearMap.smul_apply] using hAPx
    have hP_remainder : P * SOptLib.spectralRemainder A P lambda0 = 0 :=
      (Module.End.mul_spectralRemainder_eq_zero_and_spectralRemainder_mul_eq_zero
        A P lambda0 hP_idem hAP hPA).1
    have hPv_zero : P v = 0 := by
      have hPFv := congrArg (fun T : Module.End ℂ V => T v) hP_remainder
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at hPFv
      rw [hv.apply_eq_smul, map_smul] at hPFv
      exact (smul_eq_zero.mp hPFv).resolve_left hz0
    have hAv : A v = z • v := by
      simpa [SOptLib.spectralRemainder, hPv_zero] using hv.apply_eq_smul
    have hA_eigenvalue : A.HasEigenvalue z :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hAv, hv.2⟩
    have hz_ne_lambda0 : z ≠ lambda0 := by
      intro hzlambda
      have hPfix : P v = v :=
        hfix v (by simpa [hzlambda] using hAv)
      apply hv.2
      rw [← hPfix, hPv_zero]
    exact hstable z hA_eigenvalue hz_ne_lambda0

/-! Phase 4 batch 5: `FiniteNetwork_consensusError_piLpNorm_le_sqrt_card_mul_statePairwiseDiameter.lean`. -/


noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network consensus-error L2 norm bounded by square-root node count times pairwise state diameter; orig was `stateFrobeniusNorm_consensusError_le_sqrt_card_mul_diameter`.
-- generality used: arbitrary finite node carrier and real seminormed additive state space; no nonemptiness, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or matrix assumptions are used.
-- portable call pattern: consensus, gossip, push-sum, gradient-tracking, and decentralized-optimization proofs change the finite node carrier, normed state space, and node states while reusing the same conversion from range diameter to the finite-product L2 norm of uniform-consensus deviation.
-- counterargument checked: not paper-local or a pure wrapper because it composes uniform-barycenter geometry with a finite L2 aggregation bound; Mathlib's `PiLp.norm_eq_of_L2` and the existing normalized-weight diameter theorem each cover only one part of the contract.
-- coverage search: `lean_search_symbols` queries "finite product L2 norm deviation from arithmetic mean bounded by square root cardinality times diameter", "consensus error pi lp norm sqrt card diameter finite network", and "Pi lp norm bounded by sqrt cardinality times coordinate bound" found the L1-to-L2 geometric transfer and unrelated moment bounds but no matching consensus theorem; LeanSearch found `PiLp.norm_eq_of_L2` and general finite-product norm facts, while `FiniteNetwork.norm_sum_smul_sub_sum_smul_le_diam_range` supplies the needed componentwise barycenter bound, so coverage is partial rather than full.
-- minimal hypotheses: `[Fintype Node]` supports the finite product and averaging sums; the empty carrier is discharged separately, while the nonempty branch obtains a nonzero uniform averaging denominator. `[SeminormedAddCommGroup E] [NormedSpace ℝ E]` are exactly the subtraction, real averaging, seminorm, and diameter structure used; all stronger source assumptions were removed.

/-- The finite-product L2 norm of a state's deviation from its uniform network
mean is at most the square root of the node count times the pairwise diameter.

Layer: Model | Gap: Level 1 (finite consensus-error L2 bound from pairwise diameter)
Proof: bound every consensus-error coordinate by the diameter using the normalized-barycenter diameter theorem, sum the squared coordinate bounds, and use Mathlib's finite `PiLp 2` norm formula.
Source: Mathlib `PiLp.norm_eq_of_L2`, finite-sum order and real square-root monotonicity, together with the finite normalized-barycenter diameter bound
Used in: the row-stochastic half of periodic Push--Pull product contraction, converting an oscillation estimate into a Frobenius consensus-error estimate for arbitrary finite-network states
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusError_piLpNorm_le_sqrt_card_mul_statePairwiseDiameter
    {Node E : Type*} [Fintype Node]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Node → E) :
    ‖WithLp.toLp 2 (consensusError X)‖ ≤
      Real.sqrt (Fintype.card Node : ℝ) * Metric.diam (Set.range X) := by
  classical
  rcases isEmpty_or_nonempty Node with hNode | hNode
  · letI := hNode
    rw [PiLp.norm_eq_of_L2]
    simp
  letI := hNode
  let p : Node → Node → ℝ := fun i j => if i = j then 1 else 0
  let q : Node → ℝ := fun _ => (Fintype.card Node : ℝ)⁻¹
  have hp_nonneg (i j : Node) : 0 ≤ p i j := by
    simp only [p]
    split_ifs <;> norm_num
  have hp_sum (i : Node) : ∑ j : Node, p i j = 1 := by
    simp [p]
  have hq_nonneg (j : Node) : 0 ≤ q j := by
    dsimp [q]
    positivity
  have hq_sum : ∑ j : Node, q j = 1 := by
    simp [q, Fintype.card_ne_zero]
  have hp_value (i : Node) : ∑ j : Node, p i j • X j = X i := by
    simp [p]
  have hq_value :
      ∑ j : Node, q j • X j = meanState X := by
    simp only [q, meanState, SOptLib.finiteUniformAverage]
    rw [← Finset.smul_sum]
  have hcomponent (i : Node) :
      ‖consensusError X i‖ ≤ Metric.diam (Set.range X) := by
    have h := norm_sum_smul_sub_sum_smul_le_diam_range
      (p i) q (hp_nonneg i) hq_nonneg (hp_sum i) hq_sum X
    simpa [consensusError_apply, hp_value, hq_value] using h
  have hsquares :
      (∑ i : Node, ‖consensusError X i‖ ^ 2) ≤
        ∑ _i : Node, Metric.diam (Set.range X) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hcomponent i, norm_nonneg (consensusError X i),
      (Metric.diam_nonneg : 0 ≤ Metric.diam (Set.range X))]
  rw [PiLp.norm_eq_of_L2]
  calc
    Real.sqrt (∑ i : Node, ‖consensusError X i‖ ^ 2) ≤
        Real.sqrt (∑ _i : Node, Metric.diam (Set.range X) ^ 2) :=
      Real.sqrt_le_sqrt hsquares
    _ = Real.sqrt ((Fintype.card Node : ℝ) * Metric.diam (Set.range X) ^ 2) := by
      simp
    _ = Real.sqrt (Fintype.card Node : ℝ) * Metric.diam (Set.range X) := by
      rw [Real.sqrt_mul (by positivity),
        Real.sqrt_sq (Metric.diam_nonneg : 0 ≤ Metric.diam (Set.range X))]

end FiniteNetwork

/-! Phase 4 batch 6: `FiniteNetwork_stateL1Norm`. -/

noncomputable section

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network state L1 norm; orig was stateL1Norm and already had a paper-free mathematical name.
-- generality used: arbitrary finite node type and arbitrary coordinate type carrying only a norm; no additive, scalar, topological, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: consensus, push-sum, and gradient-tracking proofs use the same coordinate-sum norm when proving stochastic-matrix nonexpansiveness, Dobrushin contraction, and comparisons with product L2 norms; the node type and coordinate normed space change while the definition stays fixed.
-- counterargument checked: Mathlib's `PiLp 1` gives an L1 norm on a type synonym, but using it would change ordinary network-state types at matrix-action call sites and its `norm_eq_of_L1` API requires seminormed additive coordinates; this definition directly names the recurring norm of an ordinary finite network state and is accompanied by its unfolding specification.
-- coverage search: lean_search_symbols queries "finite function sum coordinate norms L1 norm" and "stateL1Norm finite network state" found no SOptLib definition; lean_leansearch "finite product L1 norm equals sum of coordinate norms" found `PiLp.norm_eq_of_L1`, which is partial coverage on the distinct `PiLp 1` type synonym under stronger coordinate structure.
-- minimal hypotheses: all already minimal; `[Fintype Node]` supplies the finite sum and `[Norm E]` supplies coordinate magnitudes.

/-- The L1 norm of a finite network state is the sum of its coordinate norms.

Layer: Model | Concept: finite-network state L1 norm
Proof: (definitional construction; finite sum of coordinate norms over all nodes)
Source: Mathlib finite big operators and norm notation; compare the L1 product norm characterized by `PiLp.norm_eq_of_L1`
Used in: column-stochastic nonexpansiveness, Dobrushin contraction of zero-sum tracker states, and L1-to-Frobenius norm conversion in consensus and gradient-tracking analyses
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def stateL1Norm {Node E : Type*} [Fintype Node] [Norm E]
    (X : Node → E) : ℝ :=
  ∑ i : Node, ‖X i‖

/-- The finite-network state L1 norm unfolds to the sum of all coordinate norms.

Layer: Model | Gap: Level 0 (finite-network state L1 norm unfolding)
Proof: by rfl after unfolding `FiniteNetwork.stateL1Norm`.
Source: Mathlib finite big operators and norm notation; compare the L1 product norm characterized by `PiLp.norm_eq_of_L1`
Used in: exposing coordinate sums for stochastic-matrix triangle inequalities, Dobrushin decompositions, and finite-dimensional norm comparisons
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem stateL1Norm_def {Node E : Type*} [Fintype Node] [Norm E]
    (X : Node → E) :
    stateL1Norm X = ∑ i : Node, ‖X i‖ := by
  rfl

/-- The finite-network state L1 norm is subadditive under pointwise addition.

Layer: Model | Gap: Level 0 (finite-network state L1 norm triangle inequality)
Proof: sum the coordinatewise norm triangle inequalities over the finite node set.
Source: Mathlib norm triangle inequality and finite-sum monotonicity
Used in: splitting consensus errors, perturbations, and gradient-tracking states into additive components -/
theorem stateL1Norm_add_le {Node E : Type*} [Fintype Node]
    [SeminormedAddGroup E] (X Y : Node → E) :
    stateL1Norm (X + Y) ≤ stateL1Norm X + stateL1Norm Y := by
  rw [stateL1Norm_def, stateL1Norm_def, stateL1Norm_def,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => norm_add_le (X i) (Y i)

end FiniteNetwork

/-! Phase 4 batch 6: `Matrix_stateL1Norm_smulVec_le_of_mem_colStochastic`. -/

noncomputable section

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: nonexpansiveness of a column-stochastic module-valued matrix action for the finite-state L1 norm; orig was `columnStochastic_stateL1Norm_leftMul_le`.
-- generality used: arbitrary finite decidable node type and seminormed additive commutative group with a real normed-space structure; no inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: consensus, push-sum, and gradient-tracking proofs change the finite node type, real column-stochastic mixing matrix, module-valued state space, and state while retaining the same L1 nonexpansiveness conclusion.
-- counterargument checked: not paper-local because column-stochastic L1 nonexpansiveness is a standard mixing estimate; not a one-line wrapper because it combines the row-wise triangle inequality, scalar norm homogeneity, entry nonnegativity, sum commutation, and unit column sums.
-- coverage search: lean_search_symbols queries "state L1 norm matrix smulVec nonexpansive column stochastic", "sum coordinate norms smulVec upper bound stochastic matrix nonnegative column sums one", and "Matrix stateL1Norm smulVec le of mem colStochastic", plus LeanSearch query "column stochastic matrix nonexpansive sum of norms vector valued", found `Matrix.sum_mulVec_of_mem_colStochastic`, `Matrix.l2_opNorm_le_one_of_mem_doublyStochastic`, staged `Matrix.smulVec`, and staged `FiniteNetwork.stateL1Norm`; all are partial, and none gives this module-valued L1 bound.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` are required by finite sums and Mathlib's stochastic-matrix predicate; `[SeminormedAddCommGroup E] [NormedSpace Real E]` are exactly the triangle inequality and real norm-scaling structure used by the proof.

namespace Matrix

/-- A real column-stochastic matrix acting on a finite module-valued state does
not increase the sum of the coordinate norms.

Layer: Model | Gap: Level 1 (module-valued column-stochastic L1 nonexpansiveness)
Proof: apply the finite-sum triangle inequality row by row, commute the two node sums, use nonnegativity to remove absolute values from real weights, and reduce each coefficient to one using the column-stochastic sum law.
Source: Mathlib column-stochastic matrices, normed real modules, and finite big-operator inequalities, together with SOptLib's module-valued matrix action and finite-network state L1 norm
Used in: pull-based gradient-tracking and push-sum product estimates where column-stochastic communication remainders must be bounded before complete contraction blocks are extracted
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem stateL1Norm_smulVec_le_of_mem_colStochastic
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup E] [NormedSpace Real E]
    {A : Matrix Node Node Real} (X : Node → E)
    (hA : A ∈ colStochastic Real Node) :
    FiniteNetwork.stateL1Norm (smulVec A X) ≤
      FiniteNetwork.stateL1Norm X := by
  rw [FiniteNetwork.stateL1Norm_def, FiniteNetwork.stateL1Norm_def]
  calc
    (∑ i : Node, ‖smulVec A X i‖) ≤
        ∑ i : Node, ∑ j : Node, ‖A i j • X j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [smulVec_apply] using
        (norm_sum_le (s := (Finset.univ : Finset Node))
          (f := fun j : Node => A i j • X j))
    _ = ∑ j : Node, (∑ i : Node, A i j) * ‖X j‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (nonneg_of_mem_colStochastic hA)]
      rw [Finset.sum_mul]
    _ = ∑ j : Node, ‖X j‖ := by
      simp [sum_col_of_mem_colStochastic hA]

end Matrix

/-! Phase 4 batch 6: `FiniteNetwork_consecutiveMatrixProduct_stateL1Norm_le_geometric_of_block_contraction`. -/

noncomputable section

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: arbitrary-window geometric L1 contraction for consecutive column-stochastic matrix products from a uniform block contraction; orig was `pullLiftProduct_stateL1Norm_rate`.
-- generality used: arbitrary finite decidable node carrier, seminormed additive commutative real module, natural-time-indexed real matrix schedule, positive block length, block contraction factor, and compatible per-step rate; no nonempty-node, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, periodicity, or algorithm-setup assumptions are used.
-- portable call pattern: consensus, push-sum, and gradient-tracking proofs supply a column-stochastic schedule and a uniform contraction on zero-sum states over each complete block while changing the finite network, state space, block length, contraction coefficient, and geometric root.
-- counterargument checked: not paper-local or a caller-side wrapper because it packages the nontrivial arbitrary-window strong induction, zero-sum invariance, product composition, stochastic nonexpansiveness on short remainders, and scalar conversion from a block rate to a per-step geometric envelope; the row-stochastic L2 block-minorization theorem has a different invariant and conclusion.
-- coverage search: `lean_search_symbols` queries "consecutive matrix product state L1 norm geometric bound block contraction column stochastic zero sum" and "uniform nonexpansive ell step contraction implies geometric arbitrary window rate" found the source theorem, component stochastic-matrix APIs, and `FiniteNetwork.consensusError_piLpNorm_consecutiveMatrixProduct_le_geometric_of_blockMinorization`; LeanSearch for the same operator contract found fixed-map contraction and geometric-Cauchy results but no nonautonomous finite-product theorem, so coverage is partial rather than full.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite matrices and stochasticity; `[SeminormedAddCommGroup F] [NormedSpace Real F]` are exactly the structures used by the module-valued matrix action and L1 norm; positivity of the block length and contraction factor, the block factor's upper bound by one, rate nonnegativity, and the root identity are precisely the scalar facts used in the arbitrary-window comparison.

/-- Consecutive products of column-stochastic matrices contract the L1 norm of
zero-sum states at a geometric per-step rate when every complete block has a
uniform contraction and the rate is a compatible root of the block factor.

Layer: Model | Gap: Level 2 (arbitrary-window geometric zero-sum L1 contraction from uniform block contraction)
Proof: preserve the zero-sum subspace through each column-stochastic prefix and use strong induction on the window length; a short window is nonexpansive, while a long window splits into a prefix and one complete contracting block, with the root identity reconciling the scalar factors.
Source: finite-state nonhomogeneous Markov-chain contraction, Mathlib column-stochastic matrix submonoids and natural powers, together with SOptLib consecutive-product, module-valued matrix-action, zero-sum-state, and finite-network L1 APIs
Used in: the pull-mixing half of time-varying consensus, push-sum, and gradient-tracking analyses, where blockwise contraction of zero-total-mass tracker states must yield a bound for every communication window
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveMatrixProduct_stateL1Norm_le_geometric_of_block_contraction
    {Node F : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup F] [NormedSpace Real F]
    (A : Nat -> Matrix Node Node Real) (ell : Nat) (delta rate : Real)
    (hell : 0 < ell) (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1)
    (hrate_nonneg : 0 <= rate) (hrate_ell : rate ^ ell = delta)
    (hcol : forall s : Nat, A s ∈ Matrix.colStochastic Real Node)
    (hblock : forall (t : Nat) (W : ZeroSumState Node F),
      stateL1Norm (Matrix.smulVec (consecutiveProduct A t ell) W.1) <=
        delta * stateL1Norm W.1) :
    forall (t j : Nat) (W : ZeroSumState Node F),
      stateL1Norm (Matrix.smulVec (consecutiveProduct A t j) W.1) <=
        delta⁻¹ * rate ^ j * stateL1Norm W.1 := by
  classical
  have hrate_le : rate ≤ 1 := by
    rw [← pow_le_one_iff_of_nonneg hrate_nonneg (Nat.ne_of_gt hell)]
    simpa [hrate_ell] using hdelta_le
  have hproduct_col (t k : Nat) :
      consecutiveProduct A t k ∈ Matrix.colStochastic Real Node := by
    induction k with
    | zero => exact (Matrix.colStochastic Real Node).one_mem
    | succ k ih =>
        rw [consecutiveProduct_succ]
        exact (Matrix.colStochastic Real Node).mul_mem (hcol (t + k)) ih
  have hsmulVec_mul (B C : Matrix Node Node Real) (X : Node -> F) :
      Matrix.smulVec (B * C) X = Matrix.smulVec B (Matrix.smulVec C X) := by
    funext i
    simp only [Matrix.smulVec_apply, Matrix.mul_apply, Finset.smul_sum,
      Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  intro t j
  induction j using Nat.strong_induction_on generalizing t with
  | h j ih =>
      intro W
      by_cases hj : j < ell
      · have hnonexp := Matrix.stateL1Norm_smulVec_le_of_mem_colStochastic
          W.1 (hproduct_col t j)
        have hpow : delta <= rate ^ j := by
          rw [← hrate_ell]
          exact pow_le_pow_of_le_one hrate_nonneg hrate_le (Nat.le_of_lt hj)
        have hcoeff : 1 <= delta⁻¹ * rate ^ j := by
          calc
            (1 : Real) = delta⁻¹ * delta := by field_simp
            _ <= delta⁻¹ * rate ^ j :=
              mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hdelta_pos.le)
        exact hnonexp.trans (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hcoeff
              (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      · let k := j - ell
        have hklt : k < j := by
          dsimp [k]
          omega
        have hj_eq : j = k + ell := by
          dsimp [k]
          omega
        let Wk : ZeroSumState Node F :=
          ⟨Matrix.smulVec (consecutiveProduct A t k) W.1,
            ZeroSumState.smulVec_mem_of_mem_colStochastic W (hproduct_col t k)⟩
        have hblock_k := hblock (t + k) Wk
        have hih := ih k hklt t W
        rw [hj_eq, consecutiveProduct_add, hsmulVec_mul]
        change stateL1Norm
            (Matrix.smulVec (consecutiveProduct A (t + k) ell) Wk.1) <= _
        calc
          _ <= delta * stateL1Norm Wk.1 := hblock_k
          _ <= delta * (delta⁻¹ * rate ^ k * stateL1Norm W.1) :=
            mul_le_mul_of_nonneg_left hih hdelta_pos.le
          _ = delta⁻¹ * rate ^ (k + ell) * stateL1Norm W.1 := by
            rw [pow_add, hrate_ell]
            field_simp

end FiniteNetwork

/-! Phase 4 batch 6: `FiniteNetwork_statePairwiseDiameter_le_two_mul_consensusError_piLpNorm`. -/

noncomputable section

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: finite-network pairwise state diameter bounded by twice the L2 norm of the uniform-consensus error; orig was `statePairwiseDiameter_le_two_mul_consensusError_frobeniusNorm`.
-- generality used: arbitrary finite node carrier (including the empty type) and real seminormed additive module; no norm-compatible scalar action, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or matrix assumptions are used.
-- portable call pattern: consensus, gossip, push-sum, gradient-tracking, and decentralized-optimization proofs change the finite node type and state space while converting an L2 disagreement estimate into a pairwise oscillation estimate with the same factor two.
-- counterargument checked: not paper-local or a pure wrapper because it composes invariance of pairwise differences under subtraction of the network mean, the norm triangle inequality, and two finite-product coordinate bounds; the reverse staged consensus-error bound has the opposite inequality and a cardinality factor.
-- coverage search: `lean_search_symbols` queries "finite network pairwise diameter bounded by twice L2 norm consensus error", "diameter range function less than two times Pi lp norm", "norm coordinate bounded by finite product L2 norm", and "diameter translated finite family bounded by two norm" found only the source theorem, the reverse `consensusError_piLpNorm_le_sqrt_card_mul_statePairwiseDiameter`, and partial APIs; LeanSearch found `PiLp.norm_apply_le`, `Metric.diam_le_of_forall_dist_le`, and `diam_vadd`, but no theorem with the complete consensus-error conclusion.
-- minimal hypotheses: `[Fintype Node]` forms the finite L2 product, while `[SeminormedAddCommGroup E] [Module Real E]` provide exactly the subtraction, norm, and real averaging operations used; the empty-node case is handled separately.

/-- The pairwise diameter of a finite-network state is at most twice the
finite-product L2 norm of its deviation from the uniform network mean.

Layer: Model | Gap: Level 1 (pairwise diameter controlled by finite consensus-error L2 norm)
Proof: rewrite each pairwise difference as the difference of two consensus-error coordinates, apply the norm triangle inequality, and bound both coordinates by the Mathlib `PiLp 2` norm.
Source: Mathlib `Metric.diam_le_of_forall_dist_le`, `norm_sub_le`, and `PiLp.norm_apply_le`, together with the SOptLib finite-network consensus-error model
Used in: the row-stochastic half of periodic Push--Pull product contraction, converting a Frobenius disagreement bound back into an oscillation bound before applying blockwise Dobrushin contraction
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem statePairwiseDiameter_le_two_mul_consensusError_piLpNorm
    {Node E : Type*} [Fintype Node]
    [SeminormedAddCommGroup E] [Module Real E]
    (X : Node -> E) :
    Metric.diam (Set.range X) <=
      2 * ‖WithLp.toLp 2 (consensusError X)‖ := by
  classical
  cases isEmpty_or_nonempty Node with
  | inl hNode =>
      letI := hNode
      rw [Set.range_eq_empty, Metric.diam_empty]
      positivity
  | inr hNode =>
      letI := hNode
      apply Metric.diam_le_of_forall_dist_le_of_nonempty (Set.range_nonempty _)
      rintro xi ⟨i, rfl⟩ xj ⟨j, rfl⟩
      simp only [dist_eq_norm]
      have hrewrite : X i - X j = consensusError X i - consensusError X j := by
        simp only [consensusError_apply]
        abel
      rw [hrewrite]
      calc
        ‖consensusError X i - consensusError X j‖ <=
            ‖consensusError X i‖ + ‖consensusError X j‖ := norm_sub_le _ _
        _ <= ‖WithLp.toLp 2 (consensusError X)‖ +
            ‖WithLp.toLp 2 (consensusError X)‖ :=
          add_le_add
            (PiLp.norm_apply_le (WithLp.toLp 2 (consensusError X)) i)
            (PiLp.norm_apply_le (WithLp.toLp 2 (consensusError X)) j)
        _ = 2 * ‖WithLp.toLp 2 (consensusError X)‖ := by ring

end FiniteNetwork

/-! Phase 4 batch 6: `FiniteNetwork_consensusError_piLpNorm_consecutiveMatrixProduct_le_geometric_of_blockMinorization`. -/

noncomputable section

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: geometric finite-product L2 consensus-error bound for consecutive row-stochastic matrix products under uniform block minorization; orig was `rowConsecutiveProduct_consensusError_frobenius_rate_of_blockMinorization`.
-- generality used: arbitrary finite node carrier and real seminormed additive state module, a natural-time-indexed real matrix schedule, scalar block-minorization and compatible geometric-root data; no nonempty-node, inner-product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, periodicity, or algorithm-setup assumptions are used.
-- portable call pattern: time-varying consensus, gossip, push-sum row dynamics, and decentralized gradient-tracking proofs supply their row-stochastic schedule, block length, common entry floor, block contraction envelope, and compatible per-step root while changing the finite network and state space.
-- counterargument checked: not paper-local or a caller-side wrapper because it packages the nontrivial arbitrary-window strong induction that splits complete minorized blocks from a stochastic remainder and transports diameter contraction to an L2 consensus estimate; existing staged declarations cover only its individual transitions.
-- coverage search: `lean_search_symbols` queries "consecutive matrix product consensus error L2 geometric bound block minorization row stochastic" and "row stochastic matrix product common entry lower bound geometric consensus error" found the source theorem and only component declarations; LeanSearch for a finite time-varying row-stochastic block-minorization geometric consensus bound found stochastic-matrix basics but no complete arbitrary-window theorem, so coverage is partial rather than full.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite matrices, products, and Mathlib's stochastic-matrix predicate; `[SeminormedAddCommGroup E] [NormedSpace Real E]` are exactly the structures required by the diameter and finite-product L2 bounds; positivity and root hypotheses are retained exactly where the arbitrary-window scalar comparison uses them.

/-- Consecutive products of row-stochastic matrices have a geometric
finite-product L2 consensus-error bound when every complete block is uniformly
minorized and the per-step rate is a compatible root of the block rate.

Layer: Model | Gap: Level 2 (arbitrary-window geometric consensus contraction from block minorization)
Proof: use Dobrushin contraction on each complete minorized block and row-stochastic diameter nonexpansiveness on the shorter remainder; strong induction over the window length gives the geometric diameter rate, which the two finite-network diameter/L2 comparison theorems convert to the stated consensus-error bound.
Source: finite-state Dobrushin contraction, Mathlib row-stochastic matrix products and finite `PiLp 2` norms, together with SOptLib consecutive-product and consensus-error APIs
Used in: the row-mixing half of time-varying consensus and Push--Pull analyses, where an arbitrary communication window must inherit a per-step geometric disagreement rate from uniform complete-block entry minorization
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusError_piLpNorm_consecutiveMatrixProduct_le_geometric_of_blockMinorization
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup E] [NormedSpace Real E]
    (A : Nat -> Matrix Node Node Real) (beta delta rate : Real) (ell : Nat)
    (hell : 0 < ell) (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (hrate_nonneg : 0 <= rate) (hrate_ell : rate ^ ell = delta)
    (hdelta_block : 1 - (Fintype.card Node : Real) * beta <= delta)
    (hrow : forall s : Nat, A s ∈ Matrix.rowStochastic Real Node)
    (hblock : forall (t : Nat) (i j : Node),
      beta <= consecutiveProduct A t ell i j) :
    forall (t j : Nat) (X : Node -> E),
      ‖WithLp.toLp 2
          (consensusError (Matrix.smulVec (consecutiveProduct A t j) X))‖ <=
        (2 * Real.sqrt (Fintype.card Node : Real) / delta) * rate ^ j *
          ‖WithLp.toLp 2 (consensusError X)‖ := by
  classical
  have hdelta_ne : delta ≠ 0 := ne_of_gt hdelta_pos
  have hrate_lt : rate < 1 := by
    rw [← pow_lt_one_iff_of_nonneg hrate_nonneg (Nat.ne_of_gt hell)]
    simpa [hrate_ell] using hdelta_lt
  have hsmulVec_mul (B C : Matrix Node Node Real) (Y : Node -> E) :
      Matrix.smulVec (B * C) Y = Matrix.smulVec B (Matrix.smulVec C Y) := by
    funext i
    simp only [Matrix.smulVec_apply, Matrix.mul_apply, Finset.smul_sum,
      Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  have hblock_contraction (t : Nat) (X : Node -> E) :
      Metric.diam (Set.range
          (Matrix.smulVec (consecutiveProduct A t ell) X)) <=
        delta * Metric.diam (Set.range X) := by
    have hminor :=
      Matrix.diam_range_smulVec_le_one_sub_card_mul_of_mem_rowStochastic_of_minorized
        (A := consecutiveProduct A t ell) (beta := beta)
        (consecutiveMatrixProduct_mem_rowStochastic A t ell
          (fun s _ => hrow (t + s)))
        (hblock t) X
    exact hminor.trans (mul_le_mul_of_nonneg_right hdelta_block Metric.diam_nonneg)
  have hdiameter_rate : forall (t j : Nat) (X : Node -> E),
      Metric.diam (Set.range (Matrix.smulVec (consecutiveProduct A t j) X)) <=
        delta⁻¹ * rate ^ j * Metric.diam (Set.range X) := by
    intro t j
    induction j using Nat.strong_induction_on generalizing t with
    | h j ih =>
        intro X
        by_cases hj : j < ell
        · have hnonexp := Matrix.diam_range_smulVec_le_of_mem_rowStochastic
            (A := consecutiveProduct A t j)
            (consecutiveMatrixProduct_mem_rowStochastic A t j
              (fun s _ => hrow (t + s))) X
          have hpow : delta <= rate ^ j := by
            rw [← hrate_ell]
            exact pow_le_pow_of_le_one hrate_nonneg hrate_lt.le (Nat.le_of_lt hj)
          have hcoeff : 1 <= delta⁻¹ * rate ^ j := by
            calc
              (1 : Real) = delta⁻¹ * delta := by field_simp
              _ <= delta⁻¹ * rate ^ j :=
                mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hdelta_pos.le)
          exact hnonexp.trans (by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hcoeff Metric.diam_nonneg)
        · let k := j - ell
          have hklt : k < j := by
            dsimp [k]
            omega
          have hj_eq : j = k + ell := by
            dsimp [k]
            omega
          let Xk : Node -> E := Matrix.smulVec (consecutiveProduct A t k) X
          have hblock_k := hblock_contraction (t + k) Xk
          have hih := ih k hklt t X
          rw [hj_eq, consecutiveProduct_add, hsmulVec_mul]
          change Metric.diam (Set.range
              (Matrix.smulVec (consecutiveProduct A (t + k) ell) Xk)) <= _
          calc
            _ <= delta * Metric.diam (Set.range Xk) := hblock_k
            _ <= delta * (delta⁻¹ * rate ^ k * Metric.diam (Set.range X)) :=
              mul_le_mul_of_nonneg_left hih hdelta_pos.le
            _ = delta⁻¹ * rate ^ (k + ell) * Metric.diam (Set.range X) := by
              rw [pow_add, hrate_ell]
              field_simp
  intro t j X
  have hcoeff_nonneg : 0 <= delta⁻¹ * rate ^ j :=
    mul_nonneg (inv_nonneg.mpr hdelta_pos.le) (pow_nonneg hrate_nonneg _)
  calc
    ‖WithLp.toLp 2
        (consensusError (Matrix.smulVec (consecutiveProduct A t j) X))‖ <=
        Real.sqrt (Fintype.card Node : Real) *
          Metric.diam (Set.range
            (Matrix.smulVec (consecutiveProduct A t j) X)) :=
      consensusError_piLpNorm_le_sqrt_card_mul_statePairwiseDiameter _
    _ <= Real.sqrt (Fintype.card Node : Real) *
          (delta⁻¹ * rate ^ j * Metric.diam (Set.range X)) :=
      mul_le_mul_of_nonneg_left (hdiameter_rate t j X) (Real.sqrt_nonneg _)
    _ <= Real.sqrt (Fintype.card Node : Real) *
          (delta⁻¹ * rate ^ j *
            (2 * ‖WithLp.toLp 2 (consensusError X)‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (statePairwiseDiameter_le_two_mul_consensusError_piLpNorm X)
          hcoeff_nonneg)
        (Real.sqrt_nonneg _)
    _ = (2 * Real.sqrt (Fintype.card Node : Real) / delta) * rate ^ j *
          ‖WithLp.toLp 2 (consensusError X)‖ := by
      field_simp

end FiniteNetwork

/-! Phase 4 batch 6: `FiniteNetwork_consensusError_and_state_rankOne_decomposition_energy_bounds`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: simultaneous consensus-error and raw-state energy bounds for a rank-one three-term decomposition; orig was `trackerState_joint_pointwise_bounds`.
-- generality used: arbitrary finite nonempty node type and real inner-product-space carrier; the tracker, joint coordinates, coefficient rows, aggregate vector, and row-norm bounds are explicit data, with no completeness, finite-dimensionality, measure, convexity, smoothness, oracle, periodicity, or stochastic assumptions.
-- portable call pattern: directed gradient-tracking and push-sum proofs use the same step after decomposing a tracker state into a zero-sum component, a rank-one aggregate component, and noise; the state, coefficient rows, aggregate vector, and supplied raw/projected row bounds change while the paired energy conclusions stay fixed.
-- counterargument checked: the generic three-term norm inequality alone does not supply the rank-one energy conversion, consensus-projection contraction, or paired projected/unprojected conclusions; packaging these together removes a recurring distributed-optimization proof step rather than merely renaming a caller expression.
-- coverage search: `lean_search_symbols` queries for "finite network consensus error state rank one decomposition simultaneous projected unprojected energy bounds", "state decomposition rank one component noise three term squared norm bound", and "consensusError energy bound of decomposition rankOne raw projected bounds" found the canonical `FiniteNetwork.consensusError` API and paper-local component lemmas but no theorem with this paired contract; LeanSearch for the finite three-term squared-norm sum found only `norm_add₃_le`, `norm_sum_le`, and inner-product expansion lemmas, which are partial ingredients.
-- minimal hypotheses: `[Fintype Node] [Nonempty Node]` support the uniform consensus mean and its nonzero cardinality; `[NormedAddCommGroup E] [InnerProductSpace ℝ E]` are exactly what the consensus-energy contraction uses, and all algorithm-specific assumptions have been replaced by the two decomposition equalities and two row-norm bounds.

/-- A rank-one three-term state decomposition gives simultaneous energy bounds
for the state and its finite-network consensus error.

The projected decomposition may use its own scalar coefficient row, as happens
when a consensus projector is applied to a Perron row. Euclidean bounds for the
raw and projected rows control the corresponding rank-one energies, while the
uniform consensus projection cannot increase the noise energy.

Layer: Model | Gap: Level 1 (paired projected and unprojected rank-one decomposition energy bounds)
Proof: apply the three-term squared-norm inequality coordinatewise, identify each rank-one energy from its scalar row norm, and use the Hilbert-space variance identity to contract the noise under `FiniteNetwork.consensusError`.
Source: Mathlib finite sums and real inner-product norm identities, together with the SOptLib finite-network consensus-error model
Used in: directed gradient-tracking and push-sum analyses that bound both the disagreement tracker input and the full tracker state after splitting them into a zero-sum coordinate, Perron rank-one aggregate, and noise coordinate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/20
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consensusError_and_state_rankOne_decomposition_energy_bounds
    {Node E : Type*} [Fintype Node] [Nonempty Node]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Y Theta J : Node → E) (v projectedV : Node → ℝ) (g : E)
    (vMax projectedVMax : ℝ)
    (hprojected :
      consensusError Y =
        Theta + (fun i => projectedV i • g) + consensusError J)
    (hstate : Y = Theta + (fun i => v i • g) + J)
    (hv : Real.sqrt (∑ i : Node, (v i) ^ 2) ≤ vMax)
    (hprojectedV :
      Real.sqrt (∑ i : Node, (projectedV i) ^ 2) ≤ projectedVMax) :
    (∑ i : Node, ‖consensusError Y i‖ ^ 2) ≤
        3 * ∑ i : Node, ‖Theta i‖ ^ 2 +
          3 * projectedVMax ^ 2 * ‖g‖ ^ 2 +
            3 * ∑ i : Node, ‖J i‖ ^ 2 ∧
      (∑ i : Node, ‖Y i‖ ^ 2) ≤
        3 * ∑ i : Node, ‖Theta i‖ ^ 2 +
          3 * vMax ^ 2 * ‖g‖ ^ 2 +
            3 * ∑ i : Node, ‖J i‖ ^ 2 := by
  classical
  let energy : (Node → E) → ℝ := fun X => ∑ i : Node, ‖X i‖ ^ 2
  have henergy_three (X₁ X₂ X₃ : Node → E) :
      energy (X₁ + X₂ + X₃) ≤
        3 * energy X₁ + 3 * energy X₂ + 3 * energy X₃ := by
    dsimp only [energy]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _hi
    have hnorm : ‖X₁ i + X₂ i + X₃ i‖ ≤
        ‖X₁ i‖ + ‖X₂ i‖ + ‖X₃ i‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hsq : ‖X₁ i + X₂ i + X₃ i‖ ^ 2 ≤
        (‖X₁ i‖ + ‖X₂ i‖ + ‖X₃ i‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
    change ‖X₁ i + X₂ i + X₃ i‖ ^ 2 ≤
      3 * ‖X₁ i‖ ^ 2 + 3 * ‖X₂ i‖ ^ 2 + 3 * ‖X₃ i‖ ^ 2
    nlinarith [sq_nonneg (‖X₁ i‖ - ‖X₂ i‖),
      sq_nonneg (‖X₁ i‖ - ‖X₃ i‖),
      sq_nonneg (‖X₂ i‖ - ‖X₃ i‖)]
  have hrank_energy (w : Node → ℝ) :
      energy (fun i => w i • g) = (∑ i : Node, (w i) ^ 2) * ‖g‖ ^ 2 := by
    dsimp only [energy]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hrank_le (w : Node → ℝ) (M : ℝ)
      (hw : Real.sqrt (∑ i : Node, (w i) ^ 2) ≤ M) :
      energy (fun i => w i • g) ≤ M ^ 2 * ‖g‖ ^ 2 := by
    have hsum_nonneg : 0 ≤ ∑ i : Node, (w i) ^ 2 := by positivity
    have hM_nonneg : 0 ≤ M := (Real.sqrt_nonneg _).trans hw
    have hsq : (∑ i : Node, (w i) ^ 2) ≤ M ^ 2 := by
      rw [← Real.sq_sqrt hsum_nonneg]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hM_nonneg).2 hw
    rw [hrank_energy]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hconsensus_energy (X : Node → E) :
      energy (consensusError X) ≤ energy X := by
    let xbar := meanState X
    have hcard_pos : 0 < (Fintype.card Node : ℝ) := by
      exact_mod_cast
        (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Node))
    have hsum : ∑ i : Node, X i = (Fintype.card Node : ℝ) • xbar := by
      dsimp [xbar, meanState, SOptLib.finiteUniformAverage]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hcard_pos), one_smul]
    have hinner :
        ∑ i : Node, inner ℝ (X i) xbar =
          (Fintype.card Node : ℝ) * ‖xbar‖ ^ 2 := by
      rw [← sum_inner, hsum, inner_smul_left, real_inner_self_eq_norm_sq]
      simp
    have hcard : (Finset.univ : Finset Node).card = Fintype.card Node :=
      Finset.card_univ
    dsimp only [energy]
    simp only [consensusError_apply]
    change (∑ i : Node, ‖X i - xbar‖ ^ 2) ≤ ∑ i : Node, ‖X i‖ ^ 2
    simp_rw [norm_sub_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      hcard, nsmul_eq_mul, ← Finset.mul_sum, hinner]
    nlinarith [sq_nonneg ‖xbar‖]
  have hprojected_rank := hrank_le projectedV projectedVMax hprojectedV
  have hraw_rank := hrank_le v vMax hv
  constructor
  · change energy (consensusError Y) ≤
      3 * energy Theta + 3 * projectedVMax ^ 2 * ‖g‖ ^ 2 + 3 * energy J
    rw [hprojected]
    calc
      energy (Theta + (fun i => projectedV i • g) + consensusError J) ≤
          3 * energy Theta +
            3 * energy (fun i => projectedV i • g) +
              3 * energy (consensusError J) :=
        henergy_three _ _ _
      _ ≤ 3 * energy Theta +
            3 * (projectedVMax ^ 2 * ‖g‖ ^ 2) + 3 * energy J := by
        exact add_le_add
          (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hprojected_rank (by norm_num)))
          (mul_le_mul_of_nonneg_left (hconsensus_energy J) (by norm_num))
      _ = _ := by ring
  · change energy Y ≤
      3 * energy Theta + 3 * vMax ^ 2 * ‖g‖ ^ 2 + 3 * energy J
    rw [hstate]
    calc
      energy (Theta + (fun i => v i • g) + J) ≤
          3 * energy Theta + 3 * energy (fun i => v i • g) + 3 * energy J :=
        henergy_three _ _ _
      _ ≤ 3 * energy Theta + 3 * (vMax ^ 2 * ‖g‖ ^ 2) + 3 * energy J := by
        exact add_le_add
          (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hraw_rank (by norm_num))) le_rfl
      _ = _ := by ring

end FiniteNetwork

/-! Phase 4 batch 6: `IsAlgebraicallySimpleEigenpair_outerProjection_apply_eq_self_of_eigenvector`. -/

-- Generalization plan (G0):
-- concept/name: normalized outer projection fixes an eigenvector when the eigenspace is spanned by its distinguished vector; orig was unit_eigenvector_normalized_outer_product_apply_eq.
-- generality used: arbitrary additive commutative complex module, endomorphism, eigenvalue, right eigenvector, algebraic-dual functional, and queried eigenvector; no norm, topology, finite-dimensionality, matrix coordinates, spectral gap, or left-eigenvector hypothesis.
-- portable call pattern: simple-eigenvalue perturbation, Markov-chain stationary-mode, and distributed-consensus proofs vary the operator, eigenvalue, normalized right/left modes, and queried eigenvector while reusing that the associated normalized outer projection fixes the whole eigenspace.
-- counterargument checked: the existing rank-one Riesz-projector constructor proves this internally but requires a spectral gap and both eigenvector relations; exposing the strictly weaker fixed-eigenspace contract avoids rebuilding its scalar-identification argument at future call sites.
-- coverage search: lean_search_symbols queries “outer projection fixes eigenvector algebraically simple eigenpair normalized left functional”, “rank one linear map apply equals self eigenvector eigenspace normalized dual”, and “IsAlgebraicallySimpleEigenpair outerProjection eigenvector” found the defining predicate, its eigenspace-span projection, and the stronger full Riesz-projector constructor, but no theorem with this minimal conclusion; LeanSearch found inner-product rank-one operators and idempotence lemmas, not this algebraic-dual/eigenspace bridge.
-- minimal hypotheses: eigenspace spanning identifies the queried vector as a scalar multiple, normalization identifies that scalar, and the pointwise eigenvector equation is exactly the membership premise; all are minimal for this statement.

/-- A normalized outer projection fixes every eigenvector when the distinguished
right vector spans the corresponding eigenspace.

Layer: Model | Gap: Level 1 (normalized outer projection action on a simple eigenspace)
Proof: the spanning hypothesis writes the queried eigenvector as a scalar multiple of the distinguished right vector; linearity of the dual functional and its normalization reduce the outer projection to that same scalar multiple.
Source: Mathlib linear maps, algebraic duals, scalar actions, and endomorphism eigenspaces
Used in: simple-eigenvalue perturbation and distributed-consensus spectral splittings that identify the normalized rank-one outer projector with the identity on the slow eigenspace
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem IsAlgebraicallySimpleEigenpair.outer_projection_apply_eq_self_of_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (lambda : ℂ) (right x : V)
    (left : Module.Dual ℂ V)
    (hspan : ∀ v : V, A v = lambda • v → ∃ c : ℂ, v = c • right)
    (hnormalized : left right = 1)
    (hx : A x = lambda • x) :
    LinearMap.smulRight left right x = x := by
  obtain ⟨c, rfl⟩ := hspan x hx
  rw [LinearMap.smulRight_apply, map_smul, hnormalized, smul_eq_mul, mul_one]

/-! Phase 4 batch 6: `FiniteNetwork_weightedState_normalizedCoordinateError`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: weighted-state evaluation of a normalized coordinate error; orig was `weightedState_perronCoordinateError`.
-- generality used: arbitrary finite node type and scalar nonassociative ring, two scalar node vectors, a selected node, and only the normalization equality needed to construct `normalizedCoordinateError`; no positivity, stochasticity, Perron dynamics, periodicity, topology, norm, finite-dimensional, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: finite-state Markov, consensus, push-sum, and gradient-tracking proofs change the normalized vector, test-weight vector, and selected coordinate while reusing the same overlap-minus-selected-weight evaluation before a contraction or telescoping argument.
-- counterargument checked: the identity is short, but it is the principal linear-evaluation theorem for the named `normalizedCoordinateError` model object rather than paper-local traceability or a rename; it combines finite-sum distributivity with evaluation of the selected coordinate and lets callers remain at the named-object boundary.
-- coverage search: `lean_search_symbols` query "weighted state normalized coordinate error equals overlap minus selected weight" found the source theorem and the staged `normalizedCoordinateError` API but no evaluation theorem; LeanSearch for the full finite-sum identity found only component lemmas such as `Finset.sum_smul_vsub_eq_weightedVSub_sub` and `Fintype.sum_eq_add_sum_compl`, none of which states this normalized coordinate-error evaluation.
-- minimal hypotheses: `[Fintype Node]` and `[DecidableEq Node]` support the finite sum and selected coordinate, while `[NonAssocRing R]` is exactly the algebra used for subtraction, left distributivity, and multiplication by zero and one; `hsum` is required only by the invariant-carrying normalized-coordinate-error object.

/-- Weighting a normalized coordinate error gives the weighted overlap minus
the weight of the selected coordinate.

Layer: Model | Gap: Level 1 (weighted evaluation of a normalized finite-network coordinate error)
Proof: unfold the pointwise specification of `FiniteNetwork.normalizedCoordinateError`, distribute the finite sum over subtraction, and reduce the Kronecker-coordinate sum to the selected weight.
Source: Mathlib finite-type sums, ring distributivity, and `Fintype.sum_ite_eq'`, together with the `FiniteNetwork.normalizedCoordinateError` model API
Used in: Markov, consensus, push-sum, and gradient-tracking influence proofs that evaluate a centered stationary or Perron vector against a time-dependent left weight before forming a corrected-lift coboundary
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem weightedState_normalizedCoordinateError
    {Node R : Type*} [Fintype Node] [DecidableEq Node] [NonAssocRing R]
    (w v : Node → R) (i : Node) (hsum : ∑ k : Node, v k = 1) :
    (∑ k : Node, w k *
        (normalizedCoordinateError v i hsum : Node → R) k) =
      (∑ k : Node, w k * v k) - w i := by
  simp only [normalizedCoordinateError_apply, mul_sub,
    Finset.sum_sub_distrib]
  simp

end FiniteNetwork

/-! Phase 4 batch 6: `FiniteNetwork_consecutiveMatrixProduct_entry_lowerBound_of_stronglyConnected`. -/

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: entrywise minorization of a consecutive nonnegative matrix product under positive self-loops and strongly connected positive support; orig was windowProduct_entry_lowerBound.
-- generality used: an arbitrary finite node type with selected source and target nodes, a matrix schedule over an ordered semiring, a positive entry floor, and pointwise nonnegativity, positive-diagonal, positive-entry-floor, and strong-connectivity hypotheses; no stochasticity, periodicity, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional assumptions.
-- portable call pattern: consensus, push-sum, gradient-tracking, gossip, and finite nonhomogeneous Markov-chain proofs change the finite node type, matrix schedule, weight floor, start time, and selected entry while reusing the same uniform minorization of every block of max one and node-count-minus-one steps.
-- counterargument checked: Mathlib's irreducible and primitive matrix API concerns powers of one fixed matrix and does not give this quantitative bound for a time-varying schedule; the theorem composes several reusable graph-growth and ordered-product steps, so it is neither a paper-local traceability boundary nor a one-line wrapper.
-- coverage search: lean_search_symbols query "consecutive matrix product entry lower bound positive diagonal strongly connected positive support" found only the paper-local source theorem and the staged supporting predicates; LeanSearch query "finite sequence of nonnegative matrices with positive diagonal and strongly connected support product entries lower bounded" found `Matrix.isPrimitive_iff`, `Matrix.isIrreducible_iff`, and `Matrix.isIrreducible_iff_exists_pow_pos`, all restricted to powers of a single matrix and lacking the uniform entry-floor conclusion.
-- minimal hypotheses: the selected nodes witness nonemptiness, decidable equality supports finite matrix multiplication, the entry floor is nonnegative, and every matrix hypothesis is restricted to the finite product window; row/column stochasticity and periodicity from the algorithm setup are not used.

/-- Every entry of a sufficiently long consecutive product of nonnegative
matrices is bounded below by the corresponding power of a uniform nonnegative
entry floor, provided every factor has positive diagonal and strongly connected
positive support.

Layer: Model | Gap: Level 2 (quantitative minorization of time-varying finite-network matrix products)
Proof: grow the set of rows whose product entry is at least `a ^ k`; positive diagonal preserves reached rows, while a positive edge across every proper reached-set cut adds a new row at each step.
Source: Mathlib finite matrix multiplication, finite-set cardinality, ordered-semiring powers, and relation-closure connectivity via `FiniteNetwork.IsStronglyConnectedPositiveSupport.exists_edge_into`
Used in: block-contraction proofs for time-varying consensus, push-sum, and push-pull products, where a uniform entrywise minorization supplies the Dobrushin contraction coefficient
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem consecutiveMatrixProduct_entry_lowerBound_of_stronglyConnected
    {Node R : Type*} [Fintype Node] [DecidableEq Node]
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (A : Nat → Matrix Node Node R) (a : R)
    (ha : 0 ≤ a) (t : Nat)
    (hA_nonneg : ∀ q < max 1 (Fintype.card Node - 1),
      ∀ i j : Node, 0 ≤ A (t + q) i j)
    (hA_diag : ∀ q < max 1 (Fintype.card Node - 1),
      PositiveDiagonal (A (t + q)))
    (hA_lower : ∀ q < max 1 (Fintype.card Node - 1),
      ∀ i j : Node, 0 < A (t + q) i j → a ≤ A (t + q) i j)
    (hA_conn : ∀ q < max 1 (Fintype.card Node - 1),
      IsStronglyConnectedPositiveSupport (A (t + q)))
    (i j : Node) :
    a ^ max 1 (Fintype.card Node - 1) ≤
      consecutiveProduct A t (max 1 (Fintype.card Node - 1)) i j := by
  classical
  let support : Nat → Finset Node := fun k =>
    Finset.univ.filter fun v => a ^ k ≤ consecutiveProduct A t k v j
  have hsupport_mem {k : Nat} {v : Node} :
      v ∈ support k ↔ a ^ k ≤ consecutiveProduct A t k v j := by
    simp [support]
  have hsupport_card : ∀ k : Nat, k < Fintype.card Node →
      k + 1 ≤ (support k).card := by
    intro k hk
    induction k with
    | zero =>
        have hj : j ∈ support 0 := by
          rw [hsupport_mem]
          simp
        exact Finset.card_pos.mpr ⟨j, hj⟩
    | succ k ih =>
        have hk' : k < Fintype.card Node := by omega
        have hk_window : k < max 1 (Fintype.card Node - 1) := by omega
        have ihcard := ih hk'
        have hsubset : support k ⊆ support (k + 1) := by
          intro v hv
          rw [hsupport_mem] at hv ⊢
          have hdiag_pos := hA_diag k hk_window v
          have hdiag_lower := hA_lower k hk_window v v hdiag_pos
          have hterm : a ^ (k + 1) ≤
              A (t + k) v v * consecutiveProduct A t k v j := by
            calc
              a ^ (k + 1) = a * a ^ k := by rw [pow_succ']
              _ ≤ A (t + k) v v * consecutiveProduct A t k v j :=
                mul_le_mul hdiag_lower hv (pow_nonneg ha k)
                  (le_of_lt hdiag_pos)
          have hle : A (t + k) v v * consecutiveProduct A t k v j ≤
              ∑ u : Node, A (t + k) v u * consecutiveProduct A t k u j := by
            exact Finset.single_le_sum
              (fun u _ => mul_nonneg (hA_nonneg k hk_window v u)
                (consecutiveMatrixProduct_entry_nonneg A t k
                  (fun s hs => hA_nonneg s (hs.trans hk_window)) u j))
              (Finset.mem_univ v)
          exact hterm.trans (by
            simpa only [consecutiveProduct_succ, Matrix.mul_apply] using hle)
        by_cases hfull : support k = Finset.univ
        · have hnext : support (k + 1) = Finset.univ := by
            apply Finset.eq_univ_iff_forall.mpr
            intro v
            exact hsubset (by simpa [hfull])
          rw [hnext, Finset.card_univ]
          simpa using hk
        · have hnonempty : (support k).Nonempty :=
            Finset.card_pos.mp (lt_of_lt_of_le (Nat.zero_lt_succ k) ihcard)
          obtain ⟨v, u, hv, hu, hvu⟩ :=
            IsStronglyConnectedPositiveSupport.exists_edge_into
              (A (t + k)) (hA_conn k hk_window) (support k) hnonempty hfull
          have hu_lower := hsupport_mem.mp hu
          have hentry_lower := hA_lower k hk_window v u hvu
          have hvnext : v ∈ support (k + 1) := by
            rw [hsupport_mem]
            have hterm : a ^ (k + 1) ≤
                A (t + k) v u * consecutiveProduct A t k u j := by
              calc
                a ^ (k + 1) = a * a ^ k := by rw [pow_succ']
                _ ≤ A (t + k) v u * consecutiveProduct A t k u j :=
                  mul_le_mul hentry_lower hu_lower (pow_nonneg ha k)
                    (le_of_lt hvu)
            have hle : A (t + k) v u * consecutiveProduct A t k u j ≤
                ∑ w : Node, A (t + k) v w * consecutiveProduct A t k w j := by
              exact Finset.single_le_sum
                (fun w _ => mul_nonneg (hA_nonneg k hk_window v w)
                  (consecutiveMatrixProduct_entry_nonneg A t k
                    (fun s hs => hA_nonneg s (hs.trans hk_window)) w j))
                (Finset.mem_univ u)
            exact hterm.trans (by
              simpa only [consecutiveProduct_succ, Matrix.mul_apply] using hle)
          have hstrict : support k ⊂ support (k + 1) :=
            Finset.ssubset_iff_subset_ne.mpr
              ⟨hsubset, fun heq => hv (heq ▸ hvnext)⟩
          have hcardlt := Finset.card_lt_card hstrict
          omega
  by_cases hn : Fintype.card Node = 1
  · have hsingle : i = j := by
      apply Fintype.card_le_one_iff.mp
      exact hn.le
    subst i
    have hzero_window : 0 < max 1 (Fintype.card Node - 1) := by omega
    have hdiag_pos := hA_diag 0 hzero_window j
    have hdiag_lower := hA_lower 0 hzero_window j j hdiag_pos
    simpa [hn] using hdiag_lower
  · have hn2 : 2 ≤ Fintype.card Node := by
      have hnpos : 0 < Fintype.card Node := Fintype.card_pos_iff.mpr ⟨i⟩
      omega
    have hwindow : max 1 (Fintype.card Node - 1) = Fintype.card Node - 1 := by
      omega
    rw [hwindow]
    have hcard := hsupport_card (Fintype.card Node - 1) (by omega)
    have hfull : support (Fintype.card Node - 1) = Finset.univ := by
      apply Finset.eq_univ_of_card
      have hle := Finset.card_le_univ (support (Fintype.card Node - 1))
      have heq : (support (Fintype.card Node - 1)).card = Fintype.card Node := by
        have hnsub : Fintype.card Node - 1 + 1 = Fintype.card Node := by omega
        rw [hnsub] at hcard
        omega
      exact heq
    have hi : i ∈ support (Fintype.card Node - 1) := by
      rw [hfull]
      exact Finset.mem_univ i
    exact (@hsupport_mem (Fintype.card Node - 1) i).mp hi

end FiniteNetwork

/-! Phase 4 batch 6: `FiniteNetwork_ZeroSumState_base_eq_neg_sum_compl`. -/

open scoped BigOperators

namespace FiniteNetwork.ZeroSumState

-- Generalization plan (G0):
-- concept/name: reconstruction of a selected coordinate of a finite zero-sum state from its complementary coordinates; orig was `zeroSumState_base_eq_neg_free_sum`.
-- generality used: arbitrary finite node type with decidable equality and arbitrary additive commutative group of coordinate values; no scalar action, order, topology, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: finite-network consensus, push-sum, Push--Pull, gradient-tracking, and constrained-coordinate proofs change the node type, additive coefficient group, selected base node, and zero-sum state while reconstructing the omitted coordinate by the same equality.
-- counterargument checked: this is not paper-local traceability or a pure rename; Mathlib provides the complementary finite-sum decomposition and additive cancellation separately, but no theorem specializes them to the reusable `FiniteNetwork.ZeroSumState` invariant with the complement-subtype coordinate representation.
-- coverage search: `lean_search_symbols` queries "zero sum function base coordinate equals negative sum complement subtype", "FiniteNetwork ZeroSumState base neg sum complement", and "finite sum split selected coordinate complement subtype equality" found the source theorem, the existing `FiniteNetwork.ZeroSumState.sum_coe_eq_zero`, and Mathlib component sum lemmas, but no matching bridge; LeanSearch for a selected value of a zero finite sum equaling the negative complementary sum found `add_eq_zero_iff_neg_eq'` and finite-sum component lemmas only.
-- minimal hypotheses: `[Fintype Node]` indexes the finite total and complementary sums, `[DecidableEq Node]` makes the selected-coordinate complement decidable, and `[AddCommGroup E]` is exactly the additive structure needed for finite sums and negation.

/-- In a finite zero-sum state, a selected coordinate is the negative sum of
all coordinates in its complement.

Layer: Model | Gap: Level 1 (selected-coordinate reconstruction in a finite zero-sum state)
Proof: split the total sum into the selected singleton and its complement using Mathlib finite-sum reindexing, then cancel the zero total in the additive commutative group.
Source: Mathlib finite big operators over complementary subtypes and additive-group cancellation
Used in: restricted-coordinate models of consensus and gradient-tracking dynamics, where one tracker coordinate is eliminated and reconstructed from all non-base coordinates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem base_eq_neg_sum_compl
    {Node E : Type*} [Fintype Node] [DecidableEq Node] [AddCommGroup E]
    (i0 : Node) (W : FiniteNetwork.ZeroSumState Node E) :
    W.1 i0 = -∑ j : {j : Node // j ≠ i0}, W.1 j.1 := by
  have hsplit :
      (∑ i : Node, W.1 i) =
        W.1 i0 + (Finset.univ.erase i0).sum (fun i : Node => W.1 i) := by
    rw [← Finset.sdiff_singleton_eq_erase]
    exact
      (Finset.sum_eq_add_sum_diff_singleton_of_mem
        (s := (Finset.univ : Finset Node))
        (f := fun i : Node => W.1 i) (Finset.mem_univ i0))
  have hcompl :
      (Finset.univ.erase i0).sum (fun i : Node => W.1 i) =
        ∑ j : {j : Node // j ≠ i0}, W.1 j.1 := by
    symm
    refine Finset.sum_bij
      (fun j _hj => (j : {j : Node // j ≠ i0}).1)
      ?_ ?_ ?_ ?_
    · intro j _hj
      simp [j.2]
    · intro a _ha b _hb h
      exact Subtype.ext h
    · intro b hb
      refine ⟨⟨b, ?_⟩, by simp, ?_⟩
      · exact (Finset.mem_erase.mp hb).1
      · rfl
    · intro j _hj
      rfl
  have hsum :
      W.1 i0 + ∑ j : {j : Node // j ≠ i0}, W.1 j.1 = 0 :=
    (hsplit.trans (congrArg (W.1 i0 + ·) hcompl)).symm.trans W.property
  exact (add_eq_zero_iff_eq_neg.mp hsum)

end FiniteNetwork.ZeroSumState

/-! Phase 4 batch 6: `FiniteNetwork_zeroSumStateEquivFreeCoordinates`. -/

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: inverse coordinate maps between finite zero-sum states and the coordinates complementary to a selected base node; orig was `zero_sum_state_coordinate_chart`.
-- generality used: arbitrary finite node type and arbitrary additive commutative group of coordinate values; no scalar action, order, topology, norm, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: consensus, gradient-tracking, Laplacian, and linearly constrained finite-state proofs change the finite index type, additive coefficient group, and omitted base coordinate while reusing the same mutually inverse restriction and reconstruction maps.
-- counterargument checked: this is not merely paper-local traceability or a one-line wrapper; the existing selected-coordinate reconstruction lemma supplies only one inverse-law ingredient, while this theorem constructs a zero-sum extension of arbitrary free coordinates and proves both inverse laws.
-- coverage search: `lean_search_symbols` queries "finite zero sum function equivalence complement selected coordinate inverse maps", "ZeroSumState equivalence complement coordinates", and "kernel sum additive equivalence pi complement singleton" found the source theorem and `FiniteNetwork.ZeroSumState.base_eq_neg_sum_compl` but no existing chart; LeanSearch for functions on a finite type with sum zero equivalent to functions on a point complement found only finite-support and antidiagonal APIs with different contracts.
-- minimal hypotheses: `[Fintype Node]` supplies both finite sums and `[AddCommGroup E]` supplies exactly finite addition, zero, negation, and cancellation; decidable equality is used only as local computational proof infrastructure.

/-- A finite zero-sum state is determined bijectively by all coordinates away
from any selected base index.

The forward map restricts a state to the complement of the base index. The
inverse assigns the negative sum of those free coordinates at the base index.

Layer: Model | Gap: Level 1 (free-coordinate chart for a finite zero-sum state)
Proof: construct restriction and negative-sum reconstruction maps, use finite-sum reindexing to prove reconstruction has zero total, and use `FiniteNetwork.ZeroSumState.base_eq_neg_sum_compl` for the omitted-coordinate inverse law.
Source: Mathlib finite big operators over erased finsets and complementary subtypes, together with additive-group cancellation
Used in: finite-dimensional restricted-state representations for consensus and gradient-tracking spectral arguments, where a zero-total tracker coordinate is omitted before forming a matrix model
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/13/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem ZeroSumState.exists_restrict_compl_inverse
    {Node E : Type*} [Fintype Node] [AddCommGroup E]
    (i0 : Node) :
    ∃ toCoord : ZeroSumState Node E → ({i : Node // i ≠ i0} → E),
    ∃ ofCoord : ({i : Node // i ≠ i0} → E) → ZeroSumState Node E,
      (∀ W : ZeroSumState Node E, ofCoord (toCoord W) = W) ∧
        (∀ y : {i : Node // i ≠ i0} → E, toCoord (ofCoord y) = y) := by
  classical
  let toCoord : ZeroSumState Node E → ({i : Node // i ≠ i0} → E) :=
    fun W i => W.1 i.1
  let ofCoord : ({i : Node // i ≠ i0} → E) → ZeroSumState Node E := fun y =>
    ⟨fun i : Node =>
        if h : i = i0 then -∑ j : {j : Node // j ≠ i0}, y j else y ⟨i, h⟩,
      by
        have hsplit :
            (∑ i : Node,
              (if h : i = i0 then
                -∑ j : {j : Node // j ≠ i0}, y j
              else
                y ⟨i, h⟩)) =
              (-∑ j : {j : Node // j ≠ i0}, y j) +
                (Finset.univ.erase i0).sum (fun i : Node =>
                  if h : i = i0 then
                    -∑ j : {j : Node // j ≠ i0}, y j
                  else
                    y ⟨i, h⟩) := by
          rw [← Finset.sdiff_singleton_eq_erase]
          simpa using
            (Finset.sum_eq_add_sum_diff_singleton_of_mem
              (s := (Finset.univ : Finset Node))
              (f := fun i : Node =>
                if h : i = i0 then
                  -∑ j : {j : Node // j ≠ i0}, y j
                else
                  y ⟨i, h⟩)
              (Finset.mem_univ i0))
        have hcompl :
            (Finset.univ.erase i0).sum (fun i : Node =>
              if h : i = i0 then
                -∑ j : {j : Node // j ≠ i0}, y j
              else
                y ⟨i, h⟩) =
              ∑ j : {j : Node // j ≠ i0}, y j := by
          symm
          refine Finset.sum_bij
            (fun j _hj => (j : {j : Node // j ≠ i0}).1)
            ?_ ?_ ?_ ?_
          · intro j _hj
            simp [j.2]
          · intro a _ha b _hb h
            exact Subtype.ext h
          · intro b hb
            refine ⟨⟨b, ?_⟩, by simp, ?_⟩
            · exact (Finset.mem_erase.mp hb).1
            · rfl
          · intro j _hj
            simp [j.2]
        rw [hsplit, hcompl]
        exact neg_add_cancel _
    ⟩
  refine ⟨toCoord, ofCoord, ?_, ?_⟩
  · intro W
    apply Subtype.ext
    funext i
    by_cases hi : i = i0
    · rw [hi]
      simp [ofCoord, toCoord]
      exact (ZeroSumState.base_eq_neg_sum_compl i0 W).symm
    · simp [ofCoord, toCoord, hi]
  · intro y
    funext i
    simp [ofCoord, toCoord, i.2]

end FiniteNetwork

namespace Matrix

-- Generalization plan (G0):
-- concept/name: Dobrushin L1 contraction on zero-sum states for a uniformly minorized column-stochastic matrix; orig was `columnMinorized_stateL1Norm_contraction`.
-- generality used: arbitrary finite decidable node type and real seminormed module; no nonemptiness, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or algorithm-setup assumptions.
-- portable call pattern: push-sum, gradient-tracking, finite Markov, and pull-consensus proofs change the finite network, column-stochastic matrix, common entry minorization, real normed state space, and zero-sum state while retaining the same `1 - card * beta` L1 contraction.
-- counterargument checked: not paper-local or a caller-side wrapper because it packages the complete Dobrushin residual-mass argument; the coefficient-shift equality and column-stochastic L1 nonexpansiveness cover only components, while the row-stochastic diameter theorem has a different state invariant and conclusion.
-- coverage search: `lean_search_symbols` queries "column stochastic matrix common entry lower bound contracts zero sum module valued state L1 norm one minus cardinality beta", "stateL1Norm smulVec zero sum colStochastic minorized", and "Dobrushin column stochastic zero sum L1 contraction" found only the source theorem, component APIs, and the distinct row-stochastic diameter contraction; LeanSearch found stochastic-matrix membership facts but no zero-sum module-valued L1 contraction.
-- minimal hypotheses: `[Fintype Node] [DecidableEq Node]` support finite sums and Mathlib's stochastic-matrix predicate; `[SeminormedAddCommGroup E] [NormedSpace Real E]` are exactly the triangle inequality, subtraction, and real norm-scaling structures used; `W` supplies the only zero-sum hypothesis needed.

/-- A finite real column-stochastic matrix whose entries share a lower bound
`beta` contracts the L1 norm of every module-valued zero-sum state by the
Dobrushin factor `1 - card Node * beta`.

Layer: Model | Gap: Level 1 (uniformly minorized column-stochastic zero-sum L1 contraction)
Proof: subtract the common `beta` mass from every column using the zero-sum state, apply the finite-sum triangle inequality, and identify each residual column mass as `1 - card Node * beta`.
Source: Mathlib column-stochastic matrices, normed real modules, and finite big-operator inequalities, together with the Dobrushin contraction argument for finite Markov kernels
Used in: blockwise pull-consensus and gradient-tracking estimates where a common positive entry floor contracts a zero-total-mass module-valued tracker state
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/0/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem stateL1Norm_smulVec_le_one_sub_card_mul_of_mem_colStochastic_of_minorized
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup E] [NormedSpace Real E]
    {A : Matrix Node Node Real} {beta : Real}
    (hA : A ∈ colStochastic Real Node)
    (hbeta : ∀ i j : Node, beta ≤ A i j)
    (W : FiniteNetwork.ZeroSumState Node E) :
    FiniteNetwork.stateL1Norm (smulVec A W.1) ≤
      (1 - (Fintype.card Node : Real) * beta) *
        FiniteNetwork.stateL1Norm W.1 := by
  have hrewrite (i : Node) :
      smulVec A W.1 i = ∑ j : Node, (A i j - beta) • W.1 j := by
    rw [smulVec_apply]
    calc
      (∑ j : Node, A i j • W.1 j) =
          ∑ j : Node, ((A i j - beta) • W.1 j + beta • W.1 j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [← add_smul]
        simp
      _ = (∑ j : Node, (A i j - beta) • W.1 j) +
          ∑ j : Node, beta • W.1 j := Finset.sum_add_distrib
      _ = (∑ j : Node, (A i j - beta) • W.1 j) +
          beta • ∑ j : Node, W.1 j := by rw [Finset.smul_sum]
      _ = ∑ j : Node, (A i j - beta) • W.1 j := by
        rw [W.2]
        simp
  rw [FiniteNetwork.stateL1Norm_def, FiniteNetwork.stateL1Norm_def]
  simp_rw [hrewrite]
  calc
    (∑ i : Node, ‖∑ j : Node, (A i j - beta) • W.1 j‖) ≤
        ∑ i : Node, ∑ j : Node, ‖(A i j - beta) • W.1 j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le (s := (Finset.univ : Finset Node))
        (f := fun j : Node => (A i j - beta) • W.1 j)
    _ = ∑ j : Node, (∑ i : Node, (A i j - beta)) * ‖W.1 j‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hbeta _ _))]
      rw [Finset.sum_mul]
    _ = ∑ j : Node,
          (1 - (Fintype.card Node : Real) * beta) * ‖W.1 j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [Finset.sum_sub_distrib, sum_col_of_mem_colStochastic hA]
      simp
    _ = (1 - (Fintype.card Node : Real) * beta) *
          ∑ j : Node, ‖W.1 j‖ := by
      rw [Finset.mul_sum]

end Matrix

/-! Phase 4 batch 9: `FiniteNetwork_periodicCorrectedLiftSeries_summable_of_geometric_contraction`. -/

noncomputable section

open scoped BigOperators Matrix.Module

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: summability of a periodic corrected-lift series from geometric zero-sum product contraction; orig was `correctedLiftSeries_summable`.
-- generality used: arbitrary finite decidable node carrier, complete seminormed additive commutative state group with a norm-compatible real scalar action, real matrix and phase-weight schedules, a positive-tail phase, and an explicit geometric propagated-state bound; no inner product, finite-dimensionality, stochastic-matrix, periodicity, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: periodic consensus, push-sum, and gradient-tracking proofs supply their phase weights in the standard simplex and their own geometric L1 contraction estimate for zero-sum matrix products while changing the network schedule, contraction constants, state space, and starting phase.
-- counterargument checked: the generic `summable_and_norm_tsum_le_of_geometric_bound` covers only the final comparison test; this theorem is not a pure wrapper because it additionally turns simplex-weighted propagated network states and an L1 product contraction into the required norm majorant for the named corrected-lift summand.
-- coverage search: `lean_search_symbols` queries "periodic corrected lift series summable geometric contraction zero sum state simplex weights", "summable norm bounded geometric series weighted state matrix product contraction", and the two component contracts found `FiniteNetwork.periodicCorrectedLiftSeriesTerm`, `norm_finset_sum_smul_le_sum_norm_of_mem_stdSimplex`, `FiniteNetwork.consecutiveMatrixProduct_stateL1Norm_le_geometric_of_block_contraction`, and `summable_and_norm_tsum_le_of_geometric_bound`, but no declaration with this combined corrected-lift conclusion; coverage is partial rather than full.
-- minimal hypotheses: simplex membership and product contraction are required only along the tail beginning at `t`; `0 <= rate` and `rate < 1` are exactly the scalar geometric-series conditions, while no positivity hypothesis on `delta` is needed beyond the supplied contraction bound.

/-- A periodic corrected-lift series is summable when its phase weights lie in
the standard simplex and its zero-sum propagated states satisfy a geometric
L1 contraction bound.

Layer: Model | Gap: Level 1 (corrected-lift summability from geometric zero-sum product contraction)
Proof: bound each simplex-weighted propagated state by its coordinate L1 norm, apply the supplied geometric product estimate, and use the direct comparison test with a scaled geometric majorant.
Source: finite-state nonhomogeneous Markov-chain contraction, Mathlib standard-simplex weighted-sum bounds and normed-group infinite-series comparison, together with the SOptLib corrected-lift summand and finite-network L1 APIs
Used in: periodic consensus, push-sum, and gradient-tracking constructions that define a corrected lift by summing future Perron-weighted propagations of a zero-total-mass network state
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicCorrectedLiftSeries_summable_of_geometric_contraction
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [SeminormedAddCommGroup E] [SMul Real E] [NormSMulClass Real E]
    [CompleteSpace E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (delta rate : Real) (t : Nat) (W : ZeroSumState Node E)
    (hpi : forall j, pi (t + j + 1) ∈ stdSimplex Real Node)
    (hrate_nonneg : 0 <= rate) (hrate_lt_one : rate < 1)
    (hcontraction : forall j,
      stateL1Norm (Matrix.smulVec (consecutiveProduct C t j) W.1) <=
        delta⁻¹ * rate ^ j * stateL1Norm W.1) :
    Summable (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j W) := by
  apply Summable.of_norm_bounded
    (Summable.mul_left (delta⁻¹ * stateL1Norm W.1)
      (summable_geometric_of_lt_one hrate_nonneg hrate_lt_one))
  intro j
  change ‖periodicCorrectedLiftSeriesTerm C pi t j W‖ <= _
  rw [periodicCorrectedLiftSeriesTerm_def]
  calc
    ‖∑ i : Node,
        pi (t + j + 1) i • Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ <=
        stateL1Norm (Matrix.smulVec (consecutiveProduct C t j) W.1) := by
      rw [stateL1Norm_def]
      calc
        ‖∑ i : Node,
            pi (t + j + 1) i • Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ ≤
            ∑ i : Node, ‖pi (t + j + 1) i •
              Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ := by
          simpa only using
            (norm_sum_le (s := (Finset.univ : Finset Node))
              (f := fun i : Node => pi (t + j + 1) i •
                Matrix.smulVec (consecutiveProduct C t j) W.1 i))
        _ = ∑ i : Node, pi (t + j + 1) i *
            ‖Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((hpi j).1 i)]
        _ ≤ ∑ i : Node,
            ‖Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              (mem_Icc_of_mem_stdSimplex (hpi j) i).2
              (norm_nonneg (Matrix.smulVec (consecutiveProduct C t j) W.1 i))
    _ <= delta⁻¹ * rate ^ j * stateL1Norm W.1 := hcontraction j
    _ = (delta⁻¹ * stateL1Norm W.1) * rate ^ j := by ring

end FiniteNetwork

/-! Phase 4 batch 9: `FiniteNetwork_norm_periodicCorrectedLift_le_geometric`. -/

noncomputable section

open scoped BigOperators Matrix.Module

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: geometric norm bound for the periodic finite-network corrected lift; orig was `correctedLift_norm_le_geometric`.
-- generality used: arbitrary finite decidable node carrier and normed real vector space, explicit real matrix and simplex-valued phase-weight schedules, contraction constants, phase, and zero-sum input; no completeness, nonempty-node, inner-product, finite-dimensional, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: periodic consensus, push-sum, gradient-tracking, and network-corrector proofs change the communication schedule, phase weights, geometric contraction constants, phase, and zero-sum state while reusing the same operator-value norm estimate.
-- counterargument checked: Mathlib and the staged generic geometric-series theorem bound an abstract infinite sum, while the existing corrected-lift theorem proves only summability; this result additionally derives the pointwise majorant from simplex weights and network-state L1 contraction and bounds the concrete `periodicCorrectedLift` object, so it is neither paper-local traceability nor a pure wrapper.
-- coverage search: `lean_search_symbols` queries "periodic corrected lift norm upper bound geometric contraction zero sum state simplex weights", "norm infinite sum bounded by scaled geometric series from termwise norm bound", and "weighted propagated zero sum state norm bounded summed geometric contraction" found the concrete corrected-lift definition, its geometric summability theorem, and the generic `summable_and_norm_tsum_le_of_geometric_bound`, but no corrected-lift norm theorem; LeanSearch found Mathlib's `tsum_of_norm_bounded` and related abstract infinite-sum bounds only, so coverage is partial rather than full.
-- minimal hypotheses: simplex membership is required only for the future weights used at phase `t`; the supplied L1 estimate is pointwise in the propagation lag; `0 <= rate` and `rate < 1` are exactly the geometric-series hypotheses, and no positivity assumption on `delta` is needed beyond the supplied contraction bound.

/-- The norm of a periodic corrected lift is bounded by the summed geometric
majorant induced by simplex phase weights and L1 contraction of every
propagated zero-sum state.

Layer: Model | Gap: Level 1 (corrected-lift operator-value bound from geometric zero-sum product contraction)
Proof: bound each Perron-weighted propagated state by its coordinate L1 norm, apply the supplied geometric contraction estimate, and use `tsum_of_norm_bounded` with the scaled geometric majorant.
Source: finite-state nonhomogeneous Markov-chain contraction, Mathlib `tsum_of_norm_bounded`, and the SOptLib periodic corrected-lift, standard-simplex weighted-sum, and network-state L1 APIs
Used in: periodic consensus, push-sum, and gradient-tracking regularity arguments that control a corrected network response before transporting integrability or deriving a Lipschitz estimate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem norm_periodicCorrectedLift_le_geometric
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (delta rate : Real) (t : Nat) (W : ZeroSumState Node E)
    (hpi : forall j, pi (t + j + 1) ∈ stdSimplex Real Node)
    (hrate_nonneg : 0 <= rate) (hrate_lt_one : rate < 1)
    (hcontraction : forall j,
      stateL1Norm (Matrix.smulVec (consecutiveProduct C t j) W.1) <=
        delta⁻¹ * rate ^ j * stateL1Norm W.1) :
    ‖periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W‖ <=
      (delta⁻¹ * stateL1Norm W.1) * ∑' j : Nat, rate ^ j := by
  have hterm : forall j : Nat,
      ‖periodicCorrectedLiftSeriesTerm C pi t j W‖ <=
        (delta⁻¹ * stateL1Norm W.1) * rate ^ j := by
    intro j
    rw [periodicCorrectedLiftSeriesTerm_def]
    calc
      ‖∑ i : Node,
          pi (t + j + 1) i • Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ <=
          stateL1Norm (Matrix.smulVec (consecutiveProduct C t j) W.1) := by
        rw [stateL1Norm_def]
        calc
          ‖∑ i : Node,
              pi (t + j + 1) i • Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ ≤
              ∑ i : Node, ‖pi (t + j + 1) i •
                Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ := by
            simpa only using
              (norm_sum_le (s := (Finset.univ : Finset Node))
                (f := fun i : Node => pi (t + j + 1) i •
                  Matrix.smulVec (consecutiveProduct C t j) W.1 i))
          _ = ∑ i : Node, pi (t + j + 1) i *
              ‖Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((hpi j).1 i)]
          _ ≤ ∑ i : Node,
              ‖Matrix.smulVec (consecutiveProduct C t j) W.1 i‖ := by
            apply Finset.sum_le_sum
            intro i _
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right
                (mem_Icc_of_mem_stdSimplex (hpi j) i).2
                (norm_nonneg (Matrix.smulVec (consecutiveProduct C t j) W.1 i))
      _ <= delta⁻¹ * rate ^ j * stateL1Norm W.1 := hcontraction j
      _ = (delta⁻¹ * stateL1Norm W.1) * rate ^ j := by ring
  have hmajor :
      HasSum (fun j : Nat => (delta⁻¹ * stateL1Norm W.1) * rate ^ j)
        ((delta⁻¹ * stateL1Norm W.1) * ∑' j : Nat, rate ^ j) :=
    (summable_geometric_of_lt_one hrate_nonneg hrate_lt_one).hasSum.mul_left _
  have hbound := tsum_of_norm_bounded hmajor hterm
  simpa only [periodicCorrectedLift_def, periodicCorrectedLiftSeriesTerm_def] using hbound

end FiniteNetwork

/-! Phase 4 batch 9: `FiniteNetwork_exists_lipschitzWith_periodicCorrectedLift`. -/

noncomputable section

open scoped BigOperators Matrix.Module

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: Lipschitz regularity of the periodic finite-network corrected lift under uniform geometric contraction; orig was `correctedLift_exists_lipschitz`.
-- generality used: arbitrary finite decidable node carrier and complete real normed vector state space, with explicit mixing matrices, phase weights, contraction constants, and phase; no nonempty-node, inner-product, finite-dimensional, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: periodic consensus, push-sum, push-pull, and gradient-tracking proofs change the communication stream, Perron weights, contraction constants, phase, and state space while reusing Lipschitz continuity of the corrected lift for continuity, measurability, and Lp transport.
-- counterargument checked: Mathlib's bounded additive-map and continuous-linear-map Lipschitz theorems do not directly apply because the corrected lift is exposed as a concrete infinite series rather than a bundled homomorphism; assembling its summability, subtraction, geometric norm bound, and finite-product norm comparison is a substantive reusable boundary rather than paper-local traceability or a pure wrapper.
-- coverage search: `lean_search_symbols` queries "periodic corrected lift exists Lipschitz geometric contraction zero sum state", "LipschitzWith corrected lift norm bound subtraction zero sum finite network", and "linear map bounded by norm finite pi function subtype Lipschitz exists" found the staged corrected-lift summability, norm-bound, and subtraction theorems but no Lipschitz theorem; LeanSearch found `AddMonoidHomClass.lipschitz_of_bound` and continuous-linear-map Lipschitz lemmas, which require a bundled homomorphism absent from the concrete corrected-lift API, so coverage is partial rather than full.
-- minimal hypotheses: `CompleteSpace E` is needed to derive summability of every corrected-lift series; simplex membership and geometric contraction are assumed only along the tail from `t`; nonnegativity of `delta` and `rate`, together with `rate < 1`, are exactly what makes the explicit Lipschitz constant nonnegative and the geometric series summable.

/-- A periodic finite-network corrected lift is Lipschitz on zero-sum states
when every propagated zero-sum state obeys a uniform geometric L1 contraction
bound and the phase weights lie in the standard simplex.

Layer: Model | Gap: Level 1 (corrected-lift Lipschitz regularity from uniform geometric contraction)
Proof: use corrected-lift summability to obtain its subtraction law, bound the lift of a state difference by the geometric majorant, and compare the finite-network L1 norm with the product sup norm.
Source: finite-state nonhomogeneous Markov-chain contraction, Mathlib finite-product norm comparison and Lipschitz APIs, and the SOptLib periodic corrected-lift summability, subtraction, and norm-bound theorems
Used in: periodic push-pull and gradient-tracking proofs that transport finite-horizon measurability and Lp regularity through the infinite-series network corrector
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/2/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_lipschitzWith_periodicCorrectedLift
    {Node E : Type*} [Fintype Node] [DecidableEq Node]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (delta rate : Real) (t : Nat)
    (hpi : forall j, pi (t + j + 1) ∈ stdSimplex Real Node)
    (hdelta_nonneg : 0 <= delta)
    (hrate_nonneg : 0 <= rate) (hrate_lt_one : rate < 1)
    (hcontraction : forall (W : ZeroSumState Node E) j,
      stateL1Norm (Matrix.smulVec (consecutiveProduct C t j) W.1) <=
        delta⁻¹ * rate ^ j * stateL1Norm W.1) :
    ∃ K : NNReal,
      LipschitzWith K
        (fun W : ZeroSumState Node E =>
          periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W) := by
  have hseries_nonneg : 0 ≤ ∑' j : Nat, rate ^ j :=
    tsum_nonneg fun j => pow_nonneg hrate_nonneg j
  have hinv_nonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta_nonneg
  have hcard_nonneg : 0 ≤ (Fintype.card Node : Real) := by positivity
  let K : NNReal :=
    ⟨delta⁻¹ * (∑' j : Nat, rate ^ j) * (Fintype.card Node : Real),
      mul_nonneg (mul_nonneg hinv_nonneg hseries_nonneg) hcard_nonneg⟩
  refine ⟨K, ?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro W V
  let D : ZeroSumState Node E :=
    ⟨W.1 - V.1, by
      change ∑ i : Node, (W.1 i - V.1 i) = 0
      rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩
  have hsummable (X : ZeroSumState Node E) :
      Summable (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j X) :=
    periodicCorrectedLiftSeries_summable_of_geometric_contraction
      C pi delta rate t X hpi hrate_nonneg hrate_lt_one (hcontraction X)
  have hL1 :
      stateL1Norm D.1 ≤ (Fintype.card Node : Real) * ‖W.1 - V.1‖ := by
    simpa [D, stateL1Norm_def] using
      (Pi.sum_norm_apply_le_norm (f := W.1 - V.1))
  have hdist : ‖W.1 - V.1‖ = dist W V := by
    change ‖W.1 - V.1‖ = dist W.1 V.1
    rw [dist_eq_norm]
  change dist
      (periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t W)
      (periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t V) ≤
    (K : Real) * dist W V
  rw [dist_eq_norm, ← periodicCorrectedLift_sub C pi t W V
    (hsummable W) (hsummable V)]
  calc
    ‖periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t D‖ ≤
        (delta⁻¹ * stateL1Norm D.1) * ∑' j : Nat, rate ^ j :=
      norm_periodicCorrectedLift_le_geometric C pi delta rate t D hpi
        hrate_nonneg hrate_lt_one (hcontraction D)
    _ ≤ (delta⁻¹ *
          ((Fintype.card Node : Real) * ‖W.1 - V.1‖)) *
        ∑' j : Nat, rate ^ j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL1 hinv_nonneg) hseries_nonneg
    _ = (K : Real) * dist W V := by
      rw [← hdist]
      dsimp [K]
      ring

end FiniteNetwork

open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: maximal effective node count characterized by uniform phase-node influence entries; orig was `effectiveNodeCount_eq_nodeCount_iff_influenceEntriesAllEqual`.
-- generality used: arbitrary finite node carrier, natural period, and a real-valued phase-node family with nonzero averaged squared energy; no stochasticity, periodic matrix equations, measure, convexity, smoothness, oracle, topology, normed-space, inner-product, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: periodic push-pull, push-sum, gradient-tracking, and weighted distributed stochastic algorithms change their finite node type, period, and influence family while reusing the characterization of maximal effective parallelism by uniform influence across every phase and node.
-- counterargument checked: the finite scalar Cauchy equality theorem already supplies the flattened algebraic core, but does not connect reciprocal-period gain and second moment to node cardinality; this theorem is therefore a substantive Model bridge rather than paper-local traceability, a pure rename, or a caller-side expression.
-- coverage search: `lean_search_symbols` queries "effective node count equals cardinality if and only if finite influence entries all equal" and "square total divided average square equals finite cardinality iff all entries equal" found only the source theorem, `FiniteNetwork.effective_node_count`, and the partial core `sq_sum_eq_card_mul_sum_sq_iff_pairwise_eq`; LeanSearch found `sq_sum_le_card_mul_sum_sq` but no normalized equality characterization for a phase-node family.
-- minimal hypotheses: `[Fintype Node]` supports the finite sums, while nonzeroness of the averaged squared energy is exactly the denominator condition used to clear the effective-count quotient and itself forces `p` to be nonzero; all nonemptiness and algorithm setup assumptions were removed.

/-- The effective node count of a positive-energy phase-indexed influence family
equals the number of nodes exactly when every phase-node entry is equal.

The gain is the reciprocal-period-scaled sum of all entries, and the second
moment is the reciprocal-period-scaled sum of their squares.

Layer: Model | Gap: Level 1 (maximal effective-node equality characterization)
Proof: flatten the phase-node family to `Fin p × Node`, prove the finite scalar Cauchy equality characterization by summing pairwise squared differences, and clear the positive period and second-moment denominators.
Source: Mathlib finite products, nonnegative finite sums, and real field algebra, together with `FiniteNetwork.effective_node_count`
Used in: periodic distributed stochastic optimization proofs that identify when nonuniform network influence still attains full node-count variance reduction
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem effective_node_count_eq_card_iff_influence_entries_all_equal
    {Node : Type*} [Fintype Node]
    {p : Nat} (b : Fin p -> Node -> Real)
    (hsecondMoment :
      ((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 ≠ 0) :
    effective_node_count
        (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, b r i)
        (((p : Real)⁻¹) * ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2) =
          (Fintype.card Node : Real) ↔
      ∀ r s : Fin p, ∀ i j : Node, b r i = b s j := by
  classical
  let x : Fin p × Node → Real := fun a => b a.1 a.2
  have hflat :
      (∑ a : Fin p × Node, x a) ^ 2 =
          (Fintype.card (Fin p × Node) : Real) *
            ∑ a : Fin p × Node, (x a) ^ 2 ↔
        ∀ a c : Fin p × Node, x a = x c := by
    have hpairwiseIdentity :
        (∑ a : Fin p × Node, ∑ c : Fin p × Node, (x a - x c) ^ 2) =
          2 * ((Fintype.card (Fin p × Node) : Real) *
            ∑ a : Fin p × Node, (x a) ^ 2 -
              (∑ a : Fin p × Node, x a) ^ 2) := by
      simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    constructor
    · intro heq a c
      have hdouble :
          ∑ a : Fin p × Node, ∑ c : Fin p × Node, (x a - x c) ^ 2 = 0 := by
        rw [hpairwiseIdentity, heq]
        ring
      have houter_nonneg : ∀ a ∈ (Finset.univ : Finset (Fin p × Node)),
          0 ≤ ∑ c : Fin p × Node, (x a - x c) ^ 2 := by
        intro d _
        exact Finset.sum_nonneg fun c _ => sq_nonneg _
      have hinner : ∑ c : Fin p × Node, (x a - x c) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg houter_nonneg).mp hdouble a
          (Finset.mem_univ a)
      have hterm : (x a - x c) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun d (_ : d ∈ (Finset.univ : Finset (Fin p × Node))) =>
            sq_nonneg (x a - x d))).mp hinner c (Finset.mem_univ c)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm)
    · intro heq
      cases isEmpty_or_nonempty (Fin p × Node) with
      | inl _ => simp
      | inr hι =>
          letI := hι
          let a₀ : Fin p × Node := Classical.choice hι
          simp_rw [heq _ a₀]
          simp
          ring
  have htotal :
      (∑ a : Fin p × Node, x a) =
        ∑ r : Fin p, ∑ i : Node, b r i := by
    rw [Fintype.sum_prod_type]
  have hsquares :
      (∑ a : Fin p × Node, (x a) ^ 2) =
        ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [htotal, hsquares] at hflat
  have hraw :
      (∑ r : Fin p, ∑ i : Node, b r i) ^ 2 =
          (p : Real) * (Fintype.card Node : Real) *
            ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 ↔
        ∀ r : Fin p, ∀ i : Node, ∀ s : Fin p, ∀ j : Node,
          b r i = b s j := by
    simpa [x, Fintype.card_prod, mul_assoc] using hflat
  have hentries :
      (∑ r : Fin p, ∑ i : Node, b r i) ^ 2 =
          (p : Real) * (Fintype.card Node : Real) *
            ∑ r : Fin p, ∑ i : Node, (b r i) ^ 2 ↔
        ∀ r s : Fin p, ∀ i j : Node, b r i = b s j := by
    constructor
    · intro h r s i j
      exact hraw.mp h r i s j
    · intro h
      exact hraw.mpr fun r i s j => h r s i j
  have hp : (p : Real) ≠ 0 := by
    intro hp
    apply hsecondMoment
    simp [hp]
  rw [effective_node_count_def, div_eq_iff hsecondMoment, ← hentries]
  constructor <;> intro h
  · field_simp [hp] at h ⊢
    exact h
  · field_simp [hp] at h ⊢
    nlinarith

end FiniteNetwork

/-! Phase 4 batch 11: periodic positive Perron-sequence existence. -/


open scoped BigOperators

namespace FiniteNetwork

-- Generalization plan (G0):
-- concept/name: existence of unique positive periodic normalized Perron sequences for paired periodic push-pull schedules; orig was exists_perronSequences.
-- generality used: arbitrary finite nonempty decidable node type, real row/column matrix schedules, and a positive natural period; the proof uses only pointwise row/column stochasticity, positive diagonals, positive-support strong connectivity, and schedule periodicity, with no optimization state, measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses.
-- portable call pattern: periodic push-pull, push-sum, and gradient-tracking developments change the finite node type, row/column schedules, and positive period while obtaining the same unique positive periodic normalized Perron-sequence specification.
-- counterargument checked: the existing `FiniteNetwork.UniquePositivePeriodicPushPullPerronSequences` only defines the target specification, and the staged matrix Perron theorems handle one irreducible stochastic matrix; this theorem adds the nontrivial schedule-level construction, transport between phases, periodicity, and paired uniqueness, so it is neither a duplicate nor paper-local traceability.
-- coverage search: lean_search_symbols queries "periodic stochastic matrix schedules unique positive normalized Perron sequences", "unique positive periodic push pull Perron sequences of strongly connected positive support", and "period product stationary vectors periodic matrix schedule" found the specification predicate, phase-product fixed-point bridge, and single-matrix stationary-vector theorems but no schedule-level existence result; LeanSearch for the same contract found only stochastic-matrix and irreducibility primitives, so coverage is partial.
-- minimal hypotheses: `0 < p` permits each full-period product to expose a strongly connected newest factor; stochasticity supplies nonnegativity, positive diagonals preserve support through accumulated products and transport strict positivity, connectivity supplies phasewise Perron uniqueness, and periodicity identifies shifted products; the source's uniform positive-entry lower bound is not used.

/-- Periodic row- and column-stochastic schedules with positive diagonals and
strongly connected positive support admit unique strictly positive normalized
periodic left and right Perron sequences.

Layer: Model | Gap: Level 2 (schedule-level existence and uniqueness of periodic push-pull Perron sequences)
Proof: form each phase's full-period product, prove it stochastic and irreducible, and select its unique positive normalized stationary vector. Positive diagonals and cyclic product identities transport those vectors through one step; shifted-product identities give periodicity, and phase-product fixed points give uniqueness.
Source: finite-state nonhomogeneous Markov-chain absolute probability sequences and Perron--Frobenius theory, using Mathlib stochastic-matrix submonoids and SOptLib consecutive-product, positive-support connectivity, and stationary-vector APIs
Used in: periodic push-pull, push-sum, and gradient-tracking constructions that canonically select the time-varying left absolute-probability and right Perron weights before weighted-consensus estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_unique_positive_periodic_push_pull_perron_sequences
    {Node : Type*} [Fintype Node] [DecidableEq Node] [Nonempty Node]
    (R C : Nat -> Matrix Node Node Real) (p : Nat) (hp : 0 < p)
    (hR_stochastic : forall t, R t ∈ Matrix.rowStochastic Real Node)
    (hC_stochastic : forall t, C t ∈ Matrix.colStochastic Real Node)
    (hR_diagonal : forall t, PositiveDiagonal (R t))
    (hC_diagonal : forall t, PositiveDiagonal (C t))
    (hR_connected : forall t, IsStronglyConnectedPositiveSupport (R t))
    (hC_connected : forall t, IsStronglyConnectedPositiveSupport (C t))
    (hR_periodic : Function.Periodic R p)
    (hC_periodic : Function.Periodic C p) :
    exists seqs : (Nat -> Node -> Real) × (Nat -> Node -> Real),
      UniquePositivePeriodicPushPullPerronSequences
        R C p seqs Matrix.vecMul Matrix.mulVec (fun w => ∑ i : Node, w i) := by
  classical
  have hvecMul_simplex
      {A : Matrix Node Node Real} (hA : A ∈ Matrix.rowStochastic Real Node)
      {w : Node → Real} (hw : w ∈ stdSimplex Real Node) :
      Matrix.vecMul w A ∈ stdSimplex Real Node := by
    refine ⟨Matrix.nonneg_vecMul_of_mem_rowStochastic hA hw.1, ?_⟩
    have hmass : (Matrix.vecMul w A) ⬝ᵥ (1 : Node → Real) = 1 :=
      Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hA (by
        simpa [dotProduct] using hw.2)
    simpa [dotProduct] using hmass
  have hmulVec_simplex
      {A : Matrix Node Node Real} (hA : A ∈ Matrix.colStochastic Real Node)
      {v : Node → Real} (hv : v ∈ stdSimplex Real Node) :
      Matrix.mulVec A v ∈ stdSimplex Real Node := by
    exact ⟨Matrix.nonneg_mulVec_of_mem_colStochastic hA hv.1,
      (Matrix.sum_mulVec_of_mem_colStochastic hA).trans hv.2⟩
  have hexists_stationary
      (A : Matrix Node Node Real) (hA : A ∈ Matrix.rowStochastic Real Node) :
      ∃ w : Node → Real, w ∈ stdSimplex Real Node ∧ Matrix.vecMul w A = w := by
    let T : (Node → Real) → (Node → Real) := fun w => Matrix.vecMul w A
    let w0 : Node → Real := Pi.single (Classical.arbitrary Node) 1
    have hw0 : w0 ∈ stdSimplex Real Node := by
      simpa [w0] using single_mem_stdSimplex Real (Classical.arbitrary Node)
    have hT_mem : ∀ {w : Node → Real},
        w ∈ stdSimplex Real Node → T w ∈ stdSimplex Real Node := by
      intro w hw
      exact hvecMul_simplex hA hw
    have horbit : ∀ n : Nat, T^[n] w0 ∈ stdSimplex Real Node := by
      intro n
      induction n with
      | zero => simpa using hw0
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          exact hT_mem ih
    let avg : Nat → (Node → Real) :=
      fun n => birkhoffAverage Real T id (n + 1) w0
    have havg : ∀ n : Nat, avg n ∈ stdSimplex Real Node := by
      intro n
      have hmem := (convex_stdSimplex Real Node).sum_mem
        (t := Finset.range (n + 1))
        (w := fun _ : Nat => ((n + 1 : Nat) : Real)⁻¹)
        (z := fun k => T^[k] w0) (by
          intro k hk
          positivity) (by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          exact mul_inv_cancel₀ (by positivity)) (by
          intro k hk
          exact horbit k)
      simpa [avg, birkhoffAverage, birkhoffSum, Finset.smul_sum] using hmem
    obtain ⟨w, hw, φ, hφ, hφlim⟩ :=
      (isCompact_stdSimplex Real Node).isSeqCompact havg
    refine ⟨w, hw, ?_⟩
    have hT_cont : Continuous T := by
      unfold T
      fun_prop
    have horbit_bdd : Bornology.IsBounded (Set.range (fun n => T^[n] w0)) :=
      (isCompact_stdSimplex Real Node).isBounded.subset
        (Set.range_subset_iff.mpr horbit)
    have hresidual :
        Tendsto
          (fun n => birkhoffAverage Real T id n (T w0) -
            birkhoffAverage Real T id n w0) Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_birkhoffAverage_apply_sub_birkhoffAverage (𝕜 := Real)
          (f := T) (g := id) (x := w0) horbit_bdd)
    have hT_avg : ∀ n : Nat,
        T (birkhoffAverage Real T id n w0) =
          birkhoffAverage Real T id n (T w0) := by
      intro n
      funext j
      simp only [T, Matrix.vecMul, dotProduct, birkhoffAverage, birkhoffSum,
        id_eq, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      change (∑ i : Node,
          ((n : Real)⁻¹ * ∑ k ∈ Finset.range n, (T^[k] w0) i) * A i j) =
        (n : Real)⁻¹ * ∑ k ∈ Finset.range n, (T^[k] (T w0)) j
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      change T (T^[k] w0) j = (T^[k] (T w0)) j
      calc
        T (T^[k] w0) j = (T^[k.succ] w0) j :=
          congrFun (Function.iterate_succ_apply' (f := T) k w0).symm j
        _ = (T^[k] (T w0)) j :=
          congrFun (Function.iterate_succ_apply (f := T) k w0) j
    have hsubseq_tendsto : Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
    have hresidual_sub :
        Tendsto
          (fun n => birkhoffAverage Real T id (φ n + 1) (T w0) -
            birkhoffAverage Real T id (φ n + 1) w0)
          Filter.atTop (nhds 0) := by
      exact hresidual.comp ((tendsto_add_atTop_nat 1).comp hsubseq_tendsto)
    have havg_lim : Tendsto (fun n => avg (φ n)) Filter.atTop (nhds w) := by
      simpa [Function.comp_def] using hφlim
    have hTavg_lim : Tendsto (fun n => T (avg (φ n))) Filter.atTop (nhds (T w)) :=
      hT_cont.tendsto w |>.comp havg_lim
    have hdiff_lim : Tendsto (fun n => T (avg (φ n)) - avg (φ n))
        Filter.atTop (nhds (T w - w)) := hTavg_lim.sub havg_lim
    have hdiff_zero : Tendsto (fun n => T (avg (φ n)) - avg (φ n))
        Filter.atTop (nhds 0) := by
      simpa [avg, hT_avg] using hresidual_sub
    have hzero : T w - w = 0 := tendsto_nhds_unique hdiff_lim hdiff_zero
    exact sub_eq_zero.mp hzero
  have hrow_perron
      (A : Matrix Node Node Real) (hA : A ∈ Matrix.rowStochastic Real Node)
      (hirreducible : IsStronglyConnectedPositiveSupport A) :
      ∃! w : Node → Real,
        (∀ i : Node, 0 < w i) ∧ (∑ i : Node, w i) = 1 ∧
          Matrix.vecMul w A = w := by
    obtain ⟨w, hw, hwstationary⟩ := hexists_stationary A hA
    have hwpos : ∀ i : Node, 0 < w i := by
      have hsumpos : 0 < ∑ i : Node, w i := by
        rw [hw.2]
        exact zero_lt_one
      obtain ⟨i₀, _, hi₀⟩ :=
        (Finset.sum_pos_iff_of_nonneg
          (fun i (_ : i ∈ Finset.univ) => hw.1 i)).mp hsumpos
      intro j
      have hstep : ∀ {u v : Node}, 0 < w u → 0 < A u v → 0 < w v := by
        intro u v hwu huv
        have hterm : 0 < w u * A u v := mul_pos hwu huv
        have hle : w u * A u v ≤ ∑ k : Node, w k * A k v :=
          Finset.single_le_sum
            (fun k _ => mul_nonneg (hw.1 k) (hA.1 k v)) (Finset.mem_univ u)
        have hcoord : (∑ k : Node, w k * A k v) = w v := by
          simpa [Matrix.vecMul, dotProduct] using congrFun hwstationary v
        rw [← hcoord]
        exact lt_of_lt_of_le hterm hle
      have hpath := hirreducible i₀ j
      induction hpath with
      | refl => exact hi₀
      | tail hpath huv ih => exact hstep ih huv
    refine ⟨w, ⟨hwpos, hw.2, hwstationary⟩, ?_⟩
    intro z hz
    obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun i : Node => z i / w i) Finset.univ_nonempty
    let c : Real := z i₀ / w i₀
    let d : Node → Real := fun i => z i - c * w i
    have hd_nonneg : ∀ i : Node, 0 ≤ d i := by
      intro i
      have hratio : c ≤ z i / w i := hmin i (Finset.mem_univ i)
      have hmul : c * w i ≤ z i := (le_div_iff₀ (hwpos i)).mp hratio
      simpa [d] using sub_nonneg.mpr hmul
    have hdi₀ : d i₀ = 0 := by
      dsimp [d, c]
      field_simp [ne_of_gt (hwpos i₀)]
      ring
    have hdstationary : Matrix.vecMul d A = d := by
      funext j
      have hzj : (∑ i : Node, z i * A i j) = z j := by
        simpa [Matrix.vecMul, dotProduct] using congrFun hz.2.2 j
      have hwj : (∑ i : Node, w i * A i j) = w j := by
        simpa [Matrix.vecMul, dotProduct] using congrFun hwstationary j
      simp only [Matrix.vecMul, dotProduct, d]
      calc
        (∑ i : Node, (z i - c * w i) * A i j) =
            (∑ i : Node, z i * A i j) - c * ∑ i : Node, w i * A i j := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          simp only [mul_assoc]
        _ = z j - c * w j := by rw [hzj, hwj]
    have hd_zero : d = 0 := by
      funext j
      have hback : ∀ {u v : Node}, d v = 0 → 0 < A u v → d u = 0 := by
        intro u v hdv huv
        have hle : d u * A u v ≤ ∑ k : Node, d k * A k v :=
          Finset.single_le_sum
            (fun k _ => mul_nonneg (hd_nonneg k) (hA.1 k v))
              (Finset.mem_univ u)
        have hsum : (∑ k : Node, d k * A k v) = 0 := by
          calc
            (∑ k : Node, d k * A k v) = d v := by
              simpa [Matrix.vecMul, dotProduct] using congrFun hdstationary v
            _ = 0 := hdv
        have hmul_nonpos : d u * A u v ≤ 0 := hle.trans_eq hsum
        by_contra hdu
        have hdu_pos : 0 < d u := lt_of_le_of_ne (hd_nonneg u) (Ne.symm hdu)
        exact (not_lt_of_ge hmul_nonpos) (mul_pos hdu_pos huv)
      have hpath := hirreducible j i₀
      induction hpath using Relation.ReflTransGen.head_induction_on with
      | refl => exact hdi₀
      | @head a c hac hrest ih => exact hback ih hac
    have hz_eq_cw : ∀ i : Node, z i = c * w i := by
      intro i
      have hi := congrFun hd_zero i
      simpa [d] using sub_eq_zero.mp hi
    have hc : c = 1 := by
      have hsum : (∑ i : Node, z i) = c * ∑ i : Node, w i := by
        calc
          (∑ i : Node, z i) = ∑ i : Node, c * w i :=
            Finset.sum_congr rfl (fun i _ => hz_eq_cw i)
          _ = c * ∑ i : Node, w i := by rw [Finset.mul_sum]
      rw [hz.2.1, hw.2] at hsum
      simpa using hsum.symm
    funext i
    simpa [hc] using hz_eq_cw i
  have hcol_perron
      (A : Matrix Node Node Real) (hA : A ∈ Matrix.colStochastic Real Node)
      (hirreducible : IsStronglyConnectedPositiveSupport A) :
      ∃! v : Node → Real,
        (∀ i : Node, 0 < v i) ∧ (∑ i : Node, v i) = 1 ∧
          Matrix.mulVec A v = v := by
    have htranspose_conn : IsStronglyConnectedPositiveSupport A.transpose := by
      intro i j
      change Relation.ReflTransGen (fun u v : Node => 0 < A v u) i j
      simpa only using (hirreducible j i).swap
    obtain ⟨v, hv, hvunique⟩ := hrow_perron A.transpose
      (Matrix.transpose_mem_rowStochastic_iff_mem_colStochastic.mpr hA)
      htranspose_conn
    refine ⟨v, ⟨hv.1, hv.2.1, ?_⟩, ?_⟩
    · simpa only [Matrix.vecMul_transpose] using hv.2.2
    · intro z hz
      apply hvunique z
      exact ⟨hz.1, hz.2.1,
        by simpa only [Matrix.vecMul_transpose] using hz.2.2⟩
  have hR_product_stochastic (t k : Nat) :
      consecutiveProduct R t k ∈ Matrix.rowStochastic Real Node :=
    consecutiveMatrixProduct_mem_rowStochastic R t k
      (fun s _ => hR_stochastic (t + s))
  have hC_product_stochastic (t k : Nat) :
      consecutiveProduct C t k ∈ Matrix.colStochastic Real Node := by
    induction k with
    | zero => exact (Matrix.colStochastic Real Node).one_mem
    | succ k ih =>
        rw [consecutiveProduct_succ]
        exact (Matrix.colStochastic Real Node).mul_mem (hC_stochastic (t + k)) ih
  have hR_product_diagonal (t k : Nat) : PositiveDiagonal (consecutiveProduct R t k) := by
    induction k with
    | zero => simp [PositiveDiagonal]
    | succ k ih =>
        rw [consecutiveProduct_succ]
        exact (hR_diagonal (t + k)).mul (hR_stochastic (t + k)).1
          (hR_product_stochastic t k).1 ih
  have hC_product_diagonal (t k : Nat) : PositiveDiagonal (consecutiveProduct C t k) := by
    induction k with
    | zero => simp [PositiveDiagonal]
    | succ k ih =>
        rw [consecutiveProduct_succ]
        exact (hC_diagonal (t + k)).mul (hC_stochastic (t + k)).1
          (hC_product_stochastic t k).1 ih
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hR_product_connected (t : Nat) :
      IsStronglyConnectedPositiveSupport (consecutiveProduct R t (q + 1)) := by
    rw [consecutiveProduct_succ]
    exact IsStronglyConnectedPositiveSupport.mul_of_right_positiveDiagonal
      (hR_stochastic (t + q)).1 (hR_product_stochastic t q).1
      (hR_connected (t + q)) (hR_product_diagonal t q)
  have hC_product_connected (t : Nat) :
      IsStronglyConnectedPositiveSupport (consecutiveProduct C t (q + 1)) := by
    rw [consecutiveProduct_succ]
    exact IsStronglyConnectedPositiveSupport.mul_of_right_positiveDiagonal
      (hC_stochastic (t + q)).1 (hC_product_stochastic t q).1
      (hC_connected (t + q)) (hC_product_diagonal t q)
  have hphase :
      (forall t : Nat, ∃! w : Node -> Real,
        (forall i : Node, 0 < w i) ∧ (∑ i : Node, w i) = 1 ∧
          Matrix.vecMul w (consecutiveProduct R t (q + 1)) = w) ∧
      (forall t : Nat, ∃! v : Node -> Real,
        (forall i : Node, 0 < v i) ∧ (∑ i : Node, v i) = 1 ∧
          Matrix.mulVec (consecutiveProduct C t (q + 1)) v = v) := by
    constructor
    · intro t
      exact hrow_perron
        (consecutiveProduct R t (q + 1)) (hR_product_stochastic t (q + 1))
        (hR_product_connected t)
    · intro t
      exact hcol_perron
        (consecutiveProduct C t (q + 1)) (hC_product_stochastic t (q + 1))
        (hC_product_connected t)
  let pi : Nat -> Node -> Real := fun t => Classical.choose (hphase.1 t)
  let v : Nat -> Node -> Real := fun t => Classical.choose (hphase.2 t)
  have hpi (t : Nat) :
      ((forall i : Node, 0 < pi t i) ∧ (∑ i : Node, pi t i) = 1 ∧
        Matrix.vecMul (pi t) (consecutiveProduct R t (q + 1)) = pi t) ∧
      forall z : Node -> Real,
        ((forall i : Node, 0 < z i) ∧ (∑ i : Node, z i) = 1 ∧
          Matrix.vecMul z (consecutiveProduct R t (q + 1)) = z) -> z = pi t :=
    Classical.choose_spec (hphase.1 t)
  have hv (t : Nat) :
      ((forall i : Node, 0 < v t i) ∧ (∑ i : Node, v t i) = 1 ∧
        Matrix.mulVec (consecutiveProduct C t (q + 1)) (v t) = v t) ∧
      forall z : Node -> Real,
        ((forall i : Node, 0 < z i) ∧ (∑ i : Node, z i) = 1 ∧
          Matrix.mulVec (consecutiveProduct C t (q + 1)) z = z) -> z = v t :=
    Classical.choose_spec (hphase.2 t)
  have hpi_simplex (t : Nat) : pi t ∈ stdSimplex Real Node :=
    ⟨fun i => (hpi t).1.1 i |>.le, (hpi t).1.2.1⟩
  have hv_simplex (t : Nat) : v t ∈ stdSimplex Real Node :=
    ⟨fun i => (hv t).1.1 i |>.le, (hv t).1.2.1⟩
  have hleft (t : Nat) : Matrix.vecMul (pi (t + 1)) (R t) = pi t := by
    let w := Matrix.vecMul (pi (t + 1)) (R t)
    have hw_simplex : w ∈ stdSimplex Real Node :=
      hvecMul_simplex (hR_stochastic t) (hpi_simplex (t + 1))
    have hw_pos : forall j : Node, 0 < w j := by
      intro j
      have hterm : 0 < pi (t + 1) j * R t j j :=
        mul_pos ((hpi (t + 1)).1.1 j) (hR_diagonal t j)
      have hle : pi (t + 1) j * R t j j <=
          ∑ i : Node, pi (t + 1) i * R t i j :=
        Finset.single_le_sum
          (fun i _ => mul_nonneg ((hpi (t + 1)).1.1 i |>.le)
            ((hR_stochastic t).1 i j)) (Finset.mem_univ j)
      exact hterm.trans_le (by simpa [w, Matrix.vecMul, dotProduct] using hle)
    have hw_stationary :
        Matrix.vecMul w (consecutiveProduct R t (q + 1)) = w := by
      calc
        Matrix.vecMul w (consecutiveProduct R t (q + 1)) =
            Matrix.vecMul (pi (t + 1))
              (R t * consecutiveProduct R t (q + 1)) := by
                simp [w]
        _ = Matrix.vecMul (pi (t + 1))
              (consecutiveProduct R (t + 1) (q + 1) * R t) := by
                rw [mul_consecutiveProduct_eq_consecutiveProduct_succ_mul_of_endpoint_eq
                  R (q + 1) t (hR_periodic t)]
        _ = Matrix.vecMul
              (Matrix.vecMul (pi (t + 1))
                (consecutiveProduct R (t + 1) (q + 1))) (R t) := by
                rw [Matrix.vecMul_vecMul]
        _ = w := by rw [(hpi (t + 1)).1.2.2]
    exact (hpi t).2 w ⟨hw_pos, hw_simplex.2, hw_stationary⟩
  have hright (t : Nat) : Matrix.mulVec (C t) (v t) = v (t + 1) := by
    let w := Matrix.mulVec (C t) (v t)
    have hw_simplex : w ∈ stdSimplex Real Node :=
      hmulVec_simplex (hC_stochastic t) (hv_simplex t)
    have hw_pos : forall i : Node, 0 < w i := by
      intro i
      have hterm : 0 < C t i i * v t i :=
        mul_pos (hC_diagonal t i) ((hv t).1.1 i)
      have hle : C t i i * v t i <= ∑ j : Node, C t i j * v t j :=
        Finset.single_le_sum
          (fun j _ => mul_nonneg ((hC_stochastic t).1 i j)
            ((hv t).1.1 j |>.le)) (Finset.mem_univ i)
      exact hterm.trans_le (by simpa [w, Matrix.mulVec, dotProduct] using hle)
    have hw_stationary :
        Matrix.mulVec (consecutiveProduct C (t + 1) (q + 1)) w = w := by
      calc
        Matrix.mulVec (consecutiveProduct C (t + 1) (q + 1)) w =
            Matrix.mulVec
              (consecutiveProduct C (t + 1) (q + 1) * C t) (v t) := by
                simp [w]
        _ = Matrix.mulVec
              (C t * consecutiveProduct C t (q + 1)) (v t) := by
                rw [mul_consecutiveProduct_eq_consecutiveProduct_succ_mul_of_endpoint_eq
                  C (q + 1) t (hC_periodic t)]
        _ = Matrix.mulVec (C t)
              (Matrix.mulVec (consecutiveProduct C t (q + 1)) (v t)) := by
                rw [Matrix.mulVec_mulVec]
        _ = w := by rw [(hv t).1.2.2]
    exact (hv (t + 1)).2 w ⟨hw_pos, hw_simplex.2, hw_stationary⟩
  have hpi_periodic (t : Nat) : pi (t + (q + 1)) = pi t := by
    apply (hpi t).2
    refine ⟨(hpi (t + (q + 1))).1.1, (hpi (t + (q + 1))).1.2.1, ?_⟩
    rw [← consecutiveProduct_add_period_eq_of_periodic R (q + 1) t (q + 1)
      hR_periodic]
    exact (hpi (t + (q + 1))).1.2.2
  have hv_periodic (t : Nat) : v (t + (q + 1)) = v t := by
    apply (hv t).2
    refine ⟨(hv (t + (q + 1))).1.1, (hv (t + (q + 1))).1.2.1, ?_⟩
    rw [← consecutiveProduct_add_period_eq_of_periodic C (q + 1) t (q + 1)
      hC_periodic]
    exact (hv (t + (q + 1))).1.2.2
  refine ⟨(pi, v), ?_, ?_, ?_⟩
  · exact ⟨fun t j => congrFun (hleft t) j, fun t => (hpi t).1.2.1,
      fun t i => congrFun (hright t) i, fun t => (hv t).1.2.1⟩
  · exact ⟨fun t i => (hpi t).1.1 i, fun t i => (hv t).1.1 i,
      hpi_periodic, hv_periodic⟩
  · intro other hother_equations hother_positive_periodic
    have hfixed := periodProduct_fixedPoints_of_step_recurrences_of_periodic
      R C (q + 1) other
      (fun t => funext (hother_equations.1 t))
      (fun t => funext (hother_equations.2.2.1 t))
      hother_positive_periodic.2.2.1 hother_positive_periodic.2.2.2
    have hother_left : other.1 = pi := by
      funext t
      exact (hpi t).2 (other.1 t)
        ⟨hother_positive_periodic.1 t, hother_equations.2.1 t, hfixed.1 t⟩
    have hother_right : other.2 = v := by
      funext t
      exact (hv t).2 (other.2 t)
        ⟨hother_positive_periodic.2.1 t, hother_equations.2.2.2 t, hfixed.2 t⟩
    exact Prod.ext hother_left hother_right

end FiniteNetwork


/-! Promoted from Staging/Matrix_sum_vecMul_smul_eq_sum_smul_smulVec.lean. -/

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: associativity between a row-vector matrix product and a module-valued matrix action; orig was `weightedState_rowMulMatrix`.
-- generality used: arbitrary finite row and column index types, a semiring of scalars, and an additive-commutative-monoid-valued module; no square-matrix, order, norm, topology, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: consensus, push-sum, gradient-tracking, and distributed linear-algebra proofs change the row and column types, scalar semiring, module-valued state, row vector, and mixing matrix while reusing the same reassociation from a propagated row weight to the matrix action on the state.
-- counterargument checked: this is a short finite-sum bridge, but not a pure rename or caller-side scalar expression: it connects Mathlib's `Matrix.vecMul` with the separately reusable rectangular module-valued action `Matrix.smulVec`; the same bridge is already rederived inside a periodic influence-series proof.
-- coverage search: `lean_search_symbols` queries "finite sum vecMul scalar matrix equals sum scalar smulVec module valued vector", "Matrix vecMul associativity module smulVec weighted sum equality", and "sum over row vecMul matrix scalar action equals matrix action weighted sum", plus LeanSearch queries for row-vector/matrix associativity on module-valued vectors, found the paper-local theorem, the local rederivation in `FiniteNetwork.periodicInfluenceSeriesTerm_weightedState`, Mathlib's scalar-only `Matrix.dotProduct_mulVec`, and the component APIs `Matrix.vecMul` and `Matrix.smulVec`; none states this rectangular module-valued equality.
-- minimal hypotheses: `[Fintype m] [Fintype n]` provide the two finite contractions, `[Semiring R]` supplies matrix scalar sums and products, and `[AddCommMonoid E] [Module R E]` supply exactly finite addition, distributivity, and scalar-action associativity.

namespace Matrix

/-- Weighting a module-valued vector by a row propagated through a matrix equals
weighting the matrix action on that vector by the original row.

Layer: Glue | Gap: Level 1 (row action associativity for module-valued rectangular matrix multiplication)
Proof: unfold `Matrix.vecMul` and `Matrix.smulVec`, distribute scalar multiplication across both finite sums, use `smul_smul`, and commute the two finite contractions.
Source: Mathlib finite matrix row multiplication, module scalar-action associativity, and finite big operators, together with the rectangular module-valued action `Matrix.smulVec`
Used in: consensus, push-sum, and gradient-tracking proofs that transfer a propagated Perron or influence row from the weights onto a distributed module-valued state
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sum_vecMul_smul_eq_sum_smul_smulVec
    {R m n E : Type*} [Fintype m] [Fintype n]
    [Semiring R] [AddCommMonoid E] [Module R E]
    (w : m -> R) (A : Matrix m n R) (X : n -> E) :
    (∑ j : n, Matrix.vecMul w A j • X j) =
      ∑ i : m, w i • Matrix.smulVec A X i := by
  simp only [Matrix.vecMul, dotProduct, Matrix.smulVec_apply,
    Finset.sum_smul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (smul_smul (w i) (A i j) (X j)).symm

end Matrix

/-! Promoted from Staging/Matrix_rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball.lean. -/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Matrix

-- Generalization plan (G0):
-- concept/name: a circle Riesz projection fixes an eigenvector whose eigenvalue lies inside the contour; orig was `complexRieszProjectionOnCircle_mulVec_eq_self_of_eigen_inside`.
-- generality used: arbitrary finite coordinate type, complex square matrix, complex contour center and eigenvalue, boundary determinant nonvanishing, membership of the eigenvalue in the open ball, and a pointwise eigenvector equation; no real-matrix, algorithm setup, measure, convexity, smoothness, oracle, or additional finite-dimensional-space hypotheses.
-- portable call pattern: finite spectral perturbation, consensus, Markov-chain, and network-matrix proofs vary the complex matrix, circle, enclosed eigenvalue, and eigenvector while reusing that the associated contour projection fixes that spectral vector.
-- counterargument checked: not paper-local and not a one-line wrapper because it combines continuous matrix inversion on the contour, finite-sum integration, inverse-resolvent action, and the Cauchy residue formula; Mathlib has the scalar Cauchy theorem but no finite-matrix Riesz-projection action theorem.
-- coverage search: `lean_search_symbols` queries "matrix Riesz projection on circle fixes eigenvector eigenvalue inside ball spectrum disjoint contour" and "circle resolvent integral mulVec equals vector eigenvalue mem ball determinant nonzero sphere" found the staged projection definition, contour commutation, inverse-resolvent action, and paper-local source theorem but no matching public action theorem; `lean_leansearch` query "Riesz projection defined by contour integral fixes an eigenvector when its eigenvalue is inside the contour" found Mathlib's scalar `circleIntegral.integral_sub_inv_of_mem_ball` and related Cauchy formulas only, so coverage is partial.
-- minimal hypotheses: radius positivity is derived from open-ball membership, determinant nonvanishing is assumed only on the boundary, ball membership is assumed only for the selected eigenvalue, and the eigenvector equation is pointwise for the supplied vector.

/-- The circle Riesz projection of a finite complex matrix fixes every eigenvector
whose eigenvalue lies in the enclosed open ball, provided the contour is in the
resolvent set.

Layer: Model | Gap: Level 2 (finite-matrix circle Riesz-projection action on enclosed eigenvectors)
Proof: move the finite matrix-vector sum through the normalized contour integral, use nonsingular inverse-resolvent action on the eigenvector along the boundary, and evaluate the remaining scalar Cauchy kernel by its residue.
Source: Mathlib complex circle integrals and finite-matrix nonsingular inversion, together with `Matrix.continuousOn_inv_of_det_ne_zero` and `Matrix.nonsing_inv_mulVec_eq_inv_smul_of_mulVec_eq_smul`
Used in: fixed-contour spectral decompositions of finite consensus and push-pull transition matrices, where the slow eigendirection must be identified as fixed by the enclosed spectral projection
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (center lambda : ℂ) (radius : ℝ) (v : ι → ℂ)
    (hspectrum :
      ∀ z : ℂ, ‖z - center‖ = radius →
        @Matrix.det ι (Classical.decEq ι) _ ℂ _
          (z • (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) - A) ≠ 0)
    (hlambda : lambda ∈ Metric.ball center radius)
    (hAv : Matrix.mulVec A v = lambda • v) :
    Matrix.mulVec (rieszProjectionOnCircle A center radius) v = v := by
  classical
  have hradius : 0 < radius := by
    have hdist : dist lambda center < radius := by
      simpa [Metric.mem_ball] using hlambda
    exact lt_of_le_of_lt dist_nonneg hdist
  let M : ℂ → Matrix ι ι ℂ := fun z i j =>
    z * (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) i j - A i j
  let R : ℂ → Matrix ι ι ℂ := fun z => (M z)⁻¹
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  have hM_eq (z : ℂ) : M z = z • (1 : Matrix ι ι ℂ) - A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [M]
    · simp [M, hij]
  have hM_continuous : Continuous M := by
    dsimp only [M]
    fun_prop
  have hR_continuous :
      ContinuousOn R (Metric.sphere center radius) := by
    apply Matrix.continuousOn_inv_of_det_ne_zero M
      (Metric.sphere center radius) hM_continuous.continuousOn
    intro z hz
    have hz_norm : ‖z - center‖ = radius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [hM_eq]
    exact hspectrum z hz_norm
  have hresolvent_entry_circleIntegrable :
      ∀ i j : ι, CircleIntegrable (fun z : ℂ => R z i j) center radius := by
    intro i j
    exact
      ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hR_continuous)).circleIntegrable
          hradius.le
  have hresolvent_action :
      ∀ z : ℂ, z ∈ Metric.sphere center radius →
        Matrix.mulVec (R z) v = (z - lambda)⁻¹ • v := by
    intro z hz
    have hz_norm : ‖z - center‖ = radius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    change Matrix.mulVec (M z)⁻¹ v = (z - lambda)⁻¹ • v
    rw [hM_eq]
    exact Matrix.nonsing_inv_mulVec_eq_inv_smul_of_mulVec_eq_smul
      A lambda z v (isUnit_iff_ne_zero.mpr (hspectrum z hz_norm)) hAv
  ext i
  have hsum_integrable :
      ∀ j ∈ (Finset.univ : Finset ι),
        CircleIntegrable (fun z : ℂ => R z i j * v j) center radius := by
    intro j _hj
    have hj : CircleIntegrable (fun z : ℂ => v j * R z i j) center radius :=
      (hresolvent_entry_circleIntegrable i j).const_smul (a := v j)
    simpa [mul_comm] using hj
  calc
    Matrix.mulVec (rieszProjectionOnCircle A center radius) v i =
        ∑ j : ι, (c * (∮ z in C(center, radius), R z i j)) * v j := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [rieszProjectionOnCircle_apply]
    _ = c * ∑ j : ι, (∮ z in C(center, radius), R z i j) * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = c * ∑ j : ι, (∮ z in C(center, radius), R z i j * v j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      simpa [smul_eq_mul] using
        (circleIntegral.integral_smul_const
          (fun z : ℂ => R z i j) (v j) center radius).symm
    _ = c * (∮ z in C(center, radius), ∑ j : ι, R z i j * v j) := by
      rw [circleIntegral.integral_fun_sum hsum_integrable]
    _ = c * (∮ z in C(center, radius), Matrix.mulVec (R z) v i) := by
      congr 1
    _ = c * (∮ z in C(center, radius), (z - lambda)⁻¹ * v i) := by
      congr 1
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      have haction := congrFun (hresolvent_action z hz) i
      simpa [Pi.smul_apply, smul_eq_mul] using haction
    _ = v i := by
      have hinv :
          (∮ z in C(center, radius), (z - lambda)⁻¹) =
            (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
        circleIntegral.integral_sub_inv_of_mem_ball hlambda
      have hconst :
          (∮ z in C(center, radius), (z - lambda)⁻¹ * v i) =
            v i * (∮ z in C(center, radius), (z - lambda)⁻¹) := by
        rw [show (fun z : ℂ => (z - lambda)⁻¹ * v i) =
            fun z : ℂ => v i * (z - lambda)⁻¹ by
              funext z
              ring]
        exact circleIntegral.integral_const_mul (v i)
          (fun z : ℂ => (z - lambda)⁻¹) center radius
      rw [hconst, hinv]
      rw [mul_comm (v i) ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)]
      rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

end Matrix

/-! Promoted from Staging/Matrix_rieszProjectionOnCircle_apply_eq_of_isolatedEigenprojection.lean. -/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter

namespace Matrix

-- Generalization plan (G0):
-- concept/name: entrywise identification of a circle Riesz projection with a supplied isolated eigenprojection; orig was `fixed_circle_base_resolvent_entry_integral_eq_riesz_entry`.
-- generality used: arbitrary finite decidable coordinate type, complex square matrix, complex isolated eigenvalue and eigenprojection, and positive real contour radius; the proof uses idempotence, right intertwining, a fixed-space/eigenspace equivalence, and determinant nonvanishing only on the punctured closed disk, with no real-matrix, rank-one, measure, convexity, smoothness, oracle, or extra finite-dimensional-space assumptions.
-- portable call pattern: finite-dimensional spectral, Markov-chain, consensus, and network-matrix proofs vary the matrix, isolated eigenvalue, contour radius, and certified eigenprojection while reusing the same contour-projection entry equality.
-- counterargument checked: this is not paper-local or a one-line wrapper because existing results define the circle projection, prove contour independence, or prove its action on one enclosed eigenvector, but none identify it with an independently certified eigenprojection; the proof removes the pole and extends the reduced resolvent holomorphically across the isolated eigenvalue.
-- coverage search: `lean_search_symbols` queries "Riesz projection on circle equals isolated eigenprojection spectrum inside circle", "normalized circle integral resolvent matrix equals projection commuting isolated eigenvalue", and "matrix resolvent contour entry equality eigenprojection unique eigenvalue enclosed" found `Matrix.rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball`, `Matrix.rieszProjectionOnCircle_eq_of_spectrum_disjoint_annulus`, and the projection definition as partial coverage only; `lean_leansearch` for the full finite-matrix contour identification found scalar resolvent and functional-calculus infrastructure but no matching theorem.
-- minimal hypotheses: positivity is needed for the contour and removable-singularity argument; punctured-closed-disk determinant nonvanishing is the exact isolation condition used; idempotence, right intertwining, and the fixed-space characterization are precisely the algebraic eigenprojection facts consumed by the reduced-resolvent proof, with left intertwining following from idempotence and the fixed-space characterization.

/-- An entry of the circle Riesz projection equals the corresponding entry of a
supplied eigenprojection when the center is isolated from the rest of the
spectrum throughout the closed disk.

Layer: Model | Gap: Level 2 (finite-matrix contour identification of an isolated eigenprojection)
Proof: subtract the simple projected pole from the resolvent, identify the remainder near the pole with the shifted inverse on the complementary projection, extend it continuously across the isolated eigenvalue, and apply the punctured-disk Cauchy theorem.
Source: Mathlib complex circle integration and finite-matrix nonsingular inversion, together with `Matrix.scalar_sub_add_projection_det_ne_zero_of_fixed_iff` and `Matrix.nonsing_inv_sub_smul_projection_eq_shifted_inv_mul_compl`
Used in: fixed-contour spectral splittings for finite Markov, consensus, and push-pull matrices, where a contour-defined projection must be identified entrywise with a previously certified isolated eigenprojection
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem rieszProjectionOnCircle_apply_eq_of_isolatedEigenprojection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℂ) (lambda : ℂ) (radius : ℝ) (i j : ι)
    (hradius : 0 < radius)
    (hisolated :
      ∀ z : ℂ, ‖z - lambda‖ ≤ radius → z ≠ lambda →
        Matrix.det (z • (1 : Matrix ι ι ℂ) - A) ≠ 0)
    (hP_idem : P * P = P)
    (hPA : P * A = lambda • P)
    (hfixed : ∀ v : ι → ℂ, P.mulVec v = v ↔ A.mulVec v = lambda • v) :
    rieszProjectionOnCircle A lambda radius i j = P i j := by
  classical
  let M : ℂ → Matrix ι ι ℂ := fun z r c =>
    z * (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) r c - A r c
  have hM_eq (z : ℂ) : M z = z • (1 : Matrix ι ι ℂ) - A := by
    ext r c
    by_cases hrc : r = c
    · subst c
      simp [M]
    · simp [M, hrc]
  have hM_continuous : Continuous M := by
    dsimp only [M]
    fun_prop
  have hdet_boundary :
      ∀ z : ℂ, ‖z - lambda‖ = radius → Matrix.det (M z) ≠ 0 := by
    intro z hz
    rw [hM_eq]
    apply hisolated z (hz.le)
    intro hzl
    subst z
    have hzero : (0 : ℝ) = radius := by simpa using hz
    linarith
  have hAP : A * P = lambda • P := by
    ext r c
    have hP_fixed :
        P.mulVec (fun k => P k c) = fun k => P k c := by
      funext k
      have hentry := congrArg (fun Q : Matrix ι ι ℂ => Q k c) hP_idem
      simpa [Matrix.mul_apply] using hentry
    have heigen := (hfixed (fun k => P k c)).mp hP_fixed
    have hentry := congrFun heigen r
    simpa [Matrix.mul_apply] using hentry
  have hpole :
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (∮ z in C(lambda, radius), (z - lambda)⁻¹ * P i j) = P i j := by
    have hmem : lambda ∈ Metric.ball lambda radius := by
      simpa [Metric.mem_ball] using hradius
    have hinv :
        (∮ z in C(lambda, radius), (z - lambda)⁻¹) =
          (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
      circleIntegral.integral_sub_inv_of_mem_ball hmem
    have hconst :
        (∮ z in C(lambda, radius), (z - lambda)⁻¹ * P i j) =
          P i j * (∮ z in C(lambda, radius), (z - lambda)⁻¹) := by
      rw [show (fun z : ℂ => (z - lambda)⁻¹ * P i j) =
          fun z : ℂ => P i j * (z - lambda)⁻¹ by
            funext z
            ring]
      exact circleIntegral.integral_const_mul (P i j)
        (fun z : ℂ => (z - lambda)⁻¹) lambda radius
    rw [hconst, hinv, mul_comm (P i j), ← mul_assoc,
      inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  have hleft_pole :
      ∀ z : ℂ, Matrix.det (M z) ≠ 0 →
        (z - lambda) • ((M z)⁻¹ * P) = P := by
    intro z hdet
    have hunit : IsUnit (Matrix.det (M z)) := isUnit_iff_ne_zero.mpr hdet
    have hMP : M z * P = (z - lambda) • P := by
      calc
        M z * P = (z • (1 : Matrix ι ι ℂ) - A) * P := by rw [hM_eq]
        _ = z • P - A * P := by simp [sub_mul]
        _ = z • P - lambda • P := by rw [hAP]
        _ = (z - lambda) • P := by
          ext r c
          simp
          ring
    calc
      (z - lambda) • ((M z)⁻¹ * P) =
          (M z)⁻¹ * ((z - lambda) • P) := by
            ext r c
            simp [Matrix.mul_apply, Finset.mul_sum]
            ring
      _ = (M z)⁻¹ * (M z * P) := by rw [hMP]
      _ = ((M z)⁻¹ * M z) * P := by rw [Matrix.mul_assoc]
      _ = P := by rw [Matrix.nonsing_inv_mul (M z) hunit]; simp
  have hright_pole :
      ∀ z : ℂ, Matrix.det (M z) ≠ 0 →
        (z - lambda) • (P * (M z)⁻¹) = P := by
    intro z hdet
    have hunit : IsUnit (Matrix.det (M z)) := isUnit_iff_ne_zero.mpr hdet
    have hPM : P * M z = (z - lambda) • P := by
      calc
        P * M z = P * (z • (1 : Matrix ι ι ℂ) - A) := by rw [hM_eq]
        _ = z • P - P * A := by simp [mul_sub]
        _ = z • P - lambda • P := by rw [hPA]
        _ = (z - lambda) • P := by
          ext r c
          simp
          ring
    calc
      (z - lambda) • (P * (M z)⁻¹) =
          ((z - lambda) • P) * (M z)⁻¹ := by
            ext r c
            simp [Matrix.mul_apply, Finset.mul_sum]
            ring
      _ = (P * M z) * (M z)⁻¹ := by rw [hPM]
      _ = P * (M z * (M z)⁻¹) := by rw [Matrix.mul_assoc]
      _ = P := by rw [Matrix.mul_nonsing_inv (M z) hunit]; simp
  have hshift_det : Matrix.det (M lambda + P) ≠ 0 := by
    simpa [hM_eq] using
      (Matrix.scalar_sub_add_projection_det_ne_zero_of_fixed_iff
        A P lambda hfixed hP_idem hPA)
  have hshift_det_eventually : ∀ᶠ z in 𝓝 lambda, Matrix.det (M z + P) ≠ 0 := by
    have hcont : ContinuousAt (fun z : ℂ => Matrix.det (M z + P)) lambda := by
      exact (hM_continuous.add continuous_const).matrix_det.continuousAt
    exact hcont.eventually_ne hshift_det
  let correctedRemainder : ℂ → ℂ := fun z =>
    if z = lambda then (((M lambda + P)⁻¹ * (1 - P)) i j)
    else ((M z)⁻¹) i j - (z - lambda)⁻¹ * P i j
  let rawRemainder : ℂ → ℂ := fun z =>
    ((M z)⁻¹) i j - (z - lambda)⁻¹ * P i j
  have hreduced_resolvent_identity :
      ∀ z : ℂ, ‖z - lambda‖ ≤ radius → z ≠ lambda →
        Matrix.det (M z + P) ≠ 0 →
          (M z)⁻¹ - (z - lambda)⁻¹ • P =
            (M z + P)⁻¹ * (1 - P) := by
    intro z hz hz_ne hshift_z
    have hdet_z : Matrix.det (M z) ≠ 0 := by
      rw [hM_eq]
      exact hisolated z hz hz_ne
    exact Matrix.nonsing_inv_sub_smul_projection_eq_shifted_inv_mul_compl
      (M z) P (z - lambda) hdet_z hshift_z
      (sub_ne_zero.mpr hz_ne) hP_idem
      (hleft_pole z hdet_z)
      (hright_pole z hdet_z)
  have hcorrected_eventually_shifted :
      ∀ᶠ z in 𝓝 lambda,
        correctedRemainder z = (((M z + P)⁻¹ * (1 - P)) i j) := by
    filter_upwards [hshift_det_eventually,
      Metric.closedBall_mem_nhds lambda hradius] with z hshift_z hzclosed
    by_cases hz : z = lambda
    · simp [correctedRemainder, hz]
    · have hzclosed_norm : ‖z - lambda‖ ≤ radius := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
      have hid := hreduced_resolvent_identity z hzclosed_norm hz hshift_z
      have hentry := congrArg (fun N : Matrix ι ι ℂ => N i j) hid
      simpa [correctedRemainder, hz, Matrix.sub_apply, Pi.smul_apply,
        smul_eq_mul] using hentry
  have hshifted_continuousAt :
      ContinuousAt (fun z : ℂ => (((M z + P)⁻¹ * (1 - P)) i j)) lambda := by
    have hmatrix_cont : ContinuousAt (fun z : ℂ => M z + P) lambda :=
      (hM_continuous.add continuous_const).continuousAt
    have hdetInverse : ContinuousAt Ring.inverse (Matrix.det (M lambda + P)) := by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hshift_det
    have hinvAt : ContinuousAt (fun N : Matrix ι ι ℂ => N⁻¹) (M lambda + P) :=
      continuousAt_matrix_inv (M lambda + P) hdetInverse
    have hinv_comp : ContinuousAt (fun z : ℂ => (M z + P)⁻¹) lambda := by
      simpa only [Function.comp_apply] using
        (ContinuousAt.comp
          (f := fun z : ℂ => M z + P)
          (g := fun N : Matrix ι ι ℂ => N⁻¹)
          hinvAt hmatrix_cont)
    exact (continuous_apply j).continuousAt.comp'
      ((continuous_apply i).continuousAt.comp' (hinv_comp.mul continuousAt_const))
  have hcorrected_continuousAt : ContinuousAt correctedRemainder lambda :=
    hshifted_continuousAt.congr_of_eventuallyEq hcorrected_eventually_shifted
  have hinv_entry_differentiableAt :
      ∀ z : ℂ, Matrix.det (M z) ≠ 0 →
        DifferentiableAt ℂ (fun w : ℂ => ((M w)⁻¹) i j) z := by
    intro z hdet
    have hManalytic :
        ∀ r c : ι, AnalyticAt ℂ (fun w : ℂ => M w r c) z := by
      intro r c
      dsimp only [M]
      exact (analyticAt_id.mul analyticAt_const).sub analyticAt_const
    have hdet_analytic : AnalyticAt ℂ (fun w : ℂ => Matrix.det (M w)) z :=
      Matrix.analyticAt_det_of_entrywise M hManalytic
    have hinv_det : AnalyticAt ℂ (fun w : ℂ => (Matrix.det (M w))⁻¹) z :=
      (analyticAt_inv hdet).comp_of_eq' hdet_analytic rfl
    have hadj :
        AnalyticAt ℂ (fun w : ℂ => Matrix.adjugate (M w) i j) z := by
      simpa [Matrix.adjugate_apply] using
        (Matrix.analyticAt_det_of_entrywise
          (fun w : ℂ => (M w).updateRow j (Pi.single i (1 : ℂ)))
          (x₀ := z) (by
            intro r c
            by_cases hr : r = j
            · subst r
              simpa [Matrix.updateRow] using
                (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
                  (v := ((Pi.single i (1 : ℂ) : ι → ℂ) c)) (x := z))
            · simpa [Matrix.updateRow, hr] using hManalytic r c))
    have hentry :
        AnalyticAt ℂ
          (fun w : ℂ => (Matrix.det (M w))⁻¹ * Matrix.adjugate (M w) i j) z :=
      hinv_det.mul hadj
    exact (by
      simpa [Matrix.inv_def, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using
        hentry.differentiableAt)
  have hraw_differentiableAt :
      ∀ z : ℂ, ‖z - lambda‖ ≤ radius → z ≠ lambda →
        DifferentiableAt ℂ rawRemainder z := by
    intro z hz_closed hz_ne
    have hdet_z : Matrix.det (M z) ≠ 0 := by
      rw [hM_eq]
      exact hisolated z hz_closed hz_ne
    have hinv := hinv_entry_differentiableAt z
      hdet_z
    have hpole_diff :
        DifferentiableAt ℂ (fun w : ℂ => (w - lambda)⁻¹ * P i j) z := by
      exact ((differentiableAt_inv (sub_ne_zero.mpr hz_ne)).comp z
        (differentiableAt_id.sub
          (differentiableAt_const (𝕜 := ℂ) (c := lambda) (x := z)))).mul
            (differentiableAt_const (𝕜 := ℂ) (c := P i j) (x := z))
    simpa [rawRemainder] using hinv.sub hpole_diff
  have hcorrected_continuousOn :
      ContinuousOn correctedRemainder (Metric.closedBall lambda radius) := by
    intro z hzclosed
    by_cases hz : z = lambda
    · subst z
      exact hcorrected_continuousAt.continuousWithinAt
    · have hzclosed_norm : ‖z - lambda‖ ≤ radius := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
      have hraw_cont : ContinuousAt rawRemainder z :=
        (hraw_differentiableAt z hzclosed_norm hz).continuousAt
      have heq : correctedRemainder =ᶠ[𝓝 z] rawRemainder := by
        filter_upwards [isOpen_ne.eventually_mem hz] with w hw
        simp [correctedRemainder, rawRemainder, hw]
      exact (hraw_cont.congr_of_eventuallyEq heq).continuousWithinAt
  have hcorrected_differentiableAt :
      ∀ z ∈ Metric.ball lambda radius \ ({lambda} : Set ℂ),
        DifferentiableAt ℂ correctedRemainder z := by
    intro z hz
    have hz_ne : z ≠ lambda := by
      intro hzl
      exact hz.2 (by simp [hzl])
    have hz_lt : ‖z - lambda‖ < radius := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz.1
    have hraw_diff := hraw_differentiableAt z (le_of_lt hz_lt) hz_ne
    have heq : correctedRemainder =ᶠ[𝓝 z] rawRemainder := by
      filter_upwards [isOpen_ne.eventually_mem hz_ne] with w hw
      simp [correctedRemainder, rawRemainder, hw]
    exact hraw_diff.congr_of_eventuallyEq heq
  have hcorrected_integral_zero :
      (∮ z in C(lambda, radius), correctedRemainder z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hradius.le (Set.countable_singleton lambda) hcorrected_continuousOn
      hcorrected_differentiableAt
  have hraw_integral_zero :
      (∮ z in C(lambda, radius), rawRemainder z) = 0 := by
    rw [← hcorrected_integral_zero]
    refine circleIntegral.integral_congr hradius.le ?_
    intro z hz
    have hz_norm : ‖z - lambda‖ = radius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz_ne : z ≠ lambda := by
      intro hzl
      subst z
      have hzero : (0 : ℝ) = radius := by simpa using hz_norm
      linarith
    simp [correctedRemainder, rawRemainder, hz_ne]
  have hresolvent_integrable :
      CircleIntegrable (fun z : ℂ => ((M z)⁻¹) i j) lambda radius := by
    have hcont : ContinuousOn (fun z : ℂ => (M z)⁻¹)
        (Metric.sphere lambda radius) :=
      Matrix.continuousOn_inv_of_det_ne_zero M (Metric.sphere lambda radius)
        hM_continuous.continuousOn (by
          intro z hz
          apply hdet_boundary z
          simpa [Metric.mem_sphere, dist_eq_norm] using hz)
    exact ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hcont)).circleIntegrable hradius.le
  have hpole_integrable :
      CircleIntegrable (fun z : ℂ => (z - lambda)⁻¹ * P i j) lambda radius := by
    have hcont : ContinuousOn (fun z : ℂ => (z - lambda)⁻¹ * P i j)
        (Metric.sphere lambda radius) := by
      intro z hz
      have hz_norm : ‖z - lambda‖ = radius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hz_ne : z ≠ lambda := by
        intro hzl
        subst z
        have hzero : (0 : ℝ) = radius := by simpa using hz_norm
        linarith
      exact (((differentiableAt_inv (sub_ne_zero.mpr hz_ne)).comp z
        (differentiableAt_id.sub
          (differentiableAt_const (𝕜 := ℂ) (c := lambda) (x := z)))).mul
            (differentiableAt_const (𝕜 := ℂ) (c := P i j) (x := z))).continuousAt.continuousWithinAt
    exact hcont.circleIntegrable hradius.le
  have hraw_integral_sub :
      (∮ z in C(lambda, radius), rawRemainder z) =
        (∮ z in C(lambda, radius), ((M z)⁻¹) i j) -
          ∮ z in C(lambda, radius), (z - lambda)⁻¹ * P i j := by
    simpa [rawRemainder] using
      circleIntegral.integral_sub hresolvent_integrable hpole_integrable
  have hintegral_eq :
      (∮ z in C(lambda, radius), ((M z)⁻¹) i j) =
        ∮ z in C(lambda, radius), (z - lambda)⁻¹ * P i j := by
    apply sub_eq_zero.mp
    simpa [hraw_integral_sub] using hraw_integral_zero
  rw [rieszProjectionOnCircle_apply]
  have hintegral_eq' :
      (∮ z in C(lambda, radius),
          (@Inv.inv (Matrix ι ι ℂ)
            (@Matrix.inv ι ℂ _ (Classical.decEq ι) _)
            (fun k l : ι =>
              z * (@Matrix.diagonal ι ℂ (Classical.decEq ι) _ (fun _ => 1)) k l -
                A k l)) i j) =
        ∮ z in C(lambda, radius), (z - lambda)⁻¹ * P i j := by
    have hdec : (inferInstance : DecidableEq ι) = (Classical.decEq ι) :=
      Subsingleton.elim _ _
    cases hdec
    simpa only [M] using hintegral_eq
  rw [hintegral_eq']
  exact hpole

end Matrix

/-! Promoted from Staging/Matrix_rieszProjectionOnCircle_isRankOneRieszProjectionAt_of_rankOne_and_mem_ball.lean. -/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: a rank-one circle Riesz projection is the rank-one Riesz projection at an enclosed eigenvalue; orig was `fixed_circle_rank_one_contour_projection_is_riesz_at_inside_eigenvalue`.
-- generality used: arbitrary finite nonempty coordinate type, real square matrix, arbitrary real contour center and enclosed real eigenvalue, positive radius, rank-one real descent of the circle projection, boundary resolvent condition, eigenvalue existence, and open-ball membership; no algorithm setup, parameter family, measure, convexity, smoothness, oracle, or optimization-state hypotheses.
-- portable call pattern: finite-dimensional perturbation, consensus, Markov-chain, and distributed-operator proofs vary the real matrix, real circle center, radius, enclosed eigenvalue, and rank-one contour projection while reusing the same bundled rank-one Riesz-projection conclusion.
-- counterargument checked: this is not paper-local traceability or a one-line wrapper because it composes real descent of the complex contour integral, enclosed-eigenspace fixation, rank-one spectral action, contour commutation, fixed-space identification, and finite-spectrum isolation; the real-matrix/real-center restriction is retained because that is the validated source endpoint for the real projection used by the caller.
-- coverage search: `lean_search_symbols` queries "matrix Riesz projection on circle rank one Riesz projection at eigenvalue inside ball spectrum disjoint boundary" and "rank one projection eigenspace fixed circle resolvent enclosed eigenvalue" found the component theorems `Matrix.rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball`, `Matrix.mul_rieszProjectionOnCircle_eq_rieszProjectionOnCircle_mul_of_spectrum_disjoint`, and `Module.End.exists_sphere_disjoint_spectrum`, plus the strictly stronger-family theorem `Matrix.rieszProjectionOnCircle_isRankOneRieszProjectionAt_on_Icc`; LeanSearch found no pointwise theorem with this complete contract, so coverage is partial rather than duplicative.
-- minimal hypotheses: the contour center was generalized from `1` to an arbitrary real scalar; positivity, rank one, boundary spectral disjointness, selected-eigenvalue existence, and open-ball membership are all consumed, while the ambient optimization space and finite-dimensional typeclass were removed.

/-- A rank-one real circle Riesz projection is the Riesz projection at every
real eigenvalue lying in the enclosed open ball.

The circle must lie in the resolvent set. The result packages the two spectral
actions, exact fixed-space identification, and a local separating circle at the
selected eigenvalue.

Layer: Model | Gap: Level 2 (rank-one finite-matrix circle Riesz projection at an enclosed eigenvalue)
Proof: descend the complex circle projection to real entries, use the contour residue theorem to fix the enclosed eigenspace, combine rank one with contour commutation for both spectral actions, and obtain local isolation from finiteness of the endomorphism spectrum.
Source: finite-dimensional holomorphic functional calculus, Mathlib complex circle integrals and matrix spectrum, together with `Matrix.rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball`, `Matrix.mul_rieszProjectionOnCircle_eq_rieszProjectionOnCircle_mul_of_spectrum_disjoint`, and `Module.End.exists_sphere_disjoint_spectrum`
Used in: identifying the fixed-contour slow projection of a perturbed finite network matrix with the rank-one Riesz projection at its enclosed moving real eigenvalue
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Matrix.rieszProjectionOnCircle_isRankOneRieszProjectionAt_of_rankOne_and_mem_ball
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (center lambda radius : ℝ)
    (hradius : 0 < radius)
    (hrank :
      let Aℂ : Matrix ι ι ℂ := fun i j => (A i j : ℂ)
      let Q := Matrix.rieszProjectionOnCircle Aℂ (center : ℂ) radius
      Matrix.IsNormalizedRankOneProjection (fun i j => (Q i j).re))
    (hspectrum :
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
        Matrix.det (fun i j : ι =>
          z * (1 : Matrix ι ι ℂ) i j - (A i j : ℂ)) ≠ 0)
    (hlambdaEigen :
      ∃ v : ι → ℂ, v ≠ 0 ∧
        Matrix.mulVec (fun i j => (A i j : ℂ)) v = (lambda : ℂ) • v)
    (hlambdaInside : ‖(lambda : ℂ) - (center : ℂ)‖ < radius) :
    let Aℂ : Matrix ι ι ℂ := fun i j => (A i j : ℂ)
    let Q := Matrix.rieszProjectionOnCircle Aℂ (center : ℂ) radius
    let P : Matrix ι ι ℝ := fun i j => (Q i j).re
    Matrix.IsNormalizedRankOneProjection P ∧
      A * P = lambda • P ∧
      P * A = lambda • P ∧
      (∀ x : ι → ℝ, Matrix.mulVec P x = x ↔
        Matrix.mulVec A x = lambda • x) ∧
      ∃ localRadius : ℝ, 0 < localRadius ∧
        ∀ z : ℂ, ‖z - (lambda : ℂ)‖ = localRadius →
          ¬ ∃ v : ι → ℂ, v ≠ 0 ∧ Matrix.mulVec Aℂ v = z • v := by
  classical
  have hdec : (inferInstance : DecidableEq ι) = Classical.decEq ι :=
    Subsingleton.elim _ _
  cases hdec
  let Aℂ : Matrix ι ι ℂ := fun i j => (A i j : ℂ)
  let Q : Matrix ι ι ℂ :=
    Matrix.rieszProjectionOnCircle Aℂ (center : ℂ) radius
  let P : Matrix ι ι ℝ := fun i j => (Q i j).re
  have hdet :
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
        Matrix.det (fun i j : ι =>
          z * (1 : Matrix ι ι ℂ) i j - Aℂ i j) ≠ 0 := by
    intro z hz
    simpa [Aℂ] using hspectrum z hz
  have hQreal : ∀ i j : ι, (Q i j).im = 0 := by
    have hconj :=
      (Matrix.rieszProjectionOnCircle_idempotent_and_map_conj_eq_self_of_spectrum_disjoint
        A center radius hradius (by
          intro z hz
          simpa [Aℂ, Matrix.sub_apply, Pi.smul_apply, smul_eq_mul] using hdet z hz)).2
    exact (Matrix.map_conj_eq_self_iff_forall_im_eq_zero Q).1 (by
      simpa [Aℂ, Q] using hconj)
  have hcomplexOfReal : P.map (algebraMap ℝ ℂ) = Q := by
    ext i j
    apply Complex.ext
    · change (Q i j).re = (Q i j).re
      rfl
    · change 0 = (Q i j).im
      exact (hQreal i j).symm
  have hcomplex_fixed :
      ∀ v : ι → ℂ,
        Matrix.mulVec Aℂ v = (lambda : ℂ) • v →
          Matrix.mulVec (P.map (algebraMap ℝ ℂ)) v = v := by
    intro v hv
    have hfix :=
      Matrix.rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball
        (A := Aℂ) (center := (center : ℂ)) (lambda := (lambda : ℂ))
        (radius := radius) (v := v)
        (by
          intro z hz
          simpa only [Pi.smul_apply, smul_eq_mul, Matrix.sub_apply] using hdet z hz)
        (by simpa [Metric.mem_ball, dist_eq_norm] using hlambdaInside)
        hv
    rw [hcomplexOfReal]
    exact hfix
  have hleft : A * P = lambda • P := by
    exact
      Matrix.IsNormalizedRankOneProjection.mul_left_eq_smul_of_eigenspace_le_fixed_space
        (A := A) (P := P) (lambda := lambda) hrank
        (by simpa [Aℂ, Matrix.map_apply] using hlambdaEigen) hcomplex_fixed
  have hcomplexComm : Aℂ * Q = Q * Aℂ := by
    exact Matrix.mul_rieszProjectionOnCircle_eq_rieszProjectionOnCircle_mul_of_spectrum_disjoint
      Aℂ (center : ℂ) radius hradius.le hdet
  have hcomm : P * A = A * P := by
    have hc : (P * A).map (algebraMap ℝ ℂ) =
        (A * P).map (algebraMap ℝ ℂ) := by
      simp only [Matrix.map_mul]
      rw [hcomplexOfReal]
      change Q * Aℂ = Aℂ * Q
      exact hcomplexComm.symm
    ext i j
    exact Complex.ofReal_injective
      (congrFun (congrFun hc i) j)
  have hright : P * A = lambda • P := by
    rw [hcomm, hleft]
  have heigen_fixed :
      ∀ x : ι → ℝ,
        Matrix.mulVec A x = lambda • x →
          Matrix.mulVec P x = x := by
    intro x hx
    have hxℂ :
        Matrix.mulVec Aℂ (fun i => (x i : ℂ)) =
          (lambda : ℂ) • (fun i => (x i : ℂ)) := by
      funext i
      have hi := congrFun hx i
      simpa [Aℂ, Matrix.mulVec, dotProduct, Pi.smul_apply] using
        congrArg (fun t : ℝ => (t : ℂ)) hi
    have hPx := hcomplex_fixed (fun i => (x i : ℂ)) hxℂ
    funext i
    have hi := congrFun hPx i
    exact Complex.ofReal_injective (by
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hi)
  have hfixed :
      ∀ x : ι → ℝ,
        Matrix.mulVec P x = x ↔ Matrix.mulVec A x = lambda • x := by
    intro x
    constructor
    · intro hPx
      exact Module.End.apply_eq_smul_of_comp_eq_smul_and_fixed
        (Matrix.mulVecLin A) (Matrix.mulVecLin P) lambda x
        (by
          rw [← Matrix.mulVecLin_mul,
            ← (Matrix.mulVecBilin ℝ ℝ).map_smul]
          apply congrArg Matrix.mulVecLin
          simpa [Matrix.mul_apply] using hleft)
        hPx
    · exact heigen_fixed x
  have hseparating :
      ∃ localRadius : ℝ, 0 < localRadius ∧
        ∀ z : ℂ, ‖z - (lambda : ℂ)‖ = localRadius →
          ¬ ∃ v : ι → ℂ, v ≠ 0 ∧ Matrix.mulVec Aℂ v = z • v := by
    obtain ⟨localRadius, hlocalRadius, hsphere⟩ :=
      Module.End.exists_sphere_disjoint_spectrum Aℂ.toLin' (lambda : ℂ)
    refine ⟨localRadius, hlocalRadius, ?_⟩
    intro z hz ⟨v, hvne, hv⟩
    apply hsphere z hz
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hvne⟩
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hv
  exact ⟨hrank, hleft, hright, hfixed, hseparating⟩

/-! Phase 4 batch 20: normalized-column influence and averaging bridges. -/

open scoped BigOperators Matrix

namespace FiniteNetwork

/-- Left matrix multiplication transports the normalized coordinate error of a
matrix column to the difference between the corresponding columns of the
product and the left factor.

Layer: Model | Gap: Level 1 (matrix action on a normalized column innovation)
Proof: distribute matrix-vector multiplication over the column difference,
identify the first term with a product column, and evaluate the identity column
Source: Mathlib finite matrix multiplication and `Matrix.mulVec_single_one`
Used in: consensus, push-sum, and gradient-tracking arguments that propagate a
single normalized mixing-column increment through a preceding matrix product
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem mulVec_normalizedCoordinateError_of_column
    {Node Row R : Type*} [Fintype Node] [DecidableEq Node] [NonAssocRing R]
    (B : Matrix Row Node R) (A : Matrix Node Node R) (i : Node)
    (hAi : ∑ k : Node, A k i = 1) :
    B *ᵥ (normalizedCoordinateError (fun k => A k i) i hAi).1 =
      fun r => (B * A) r i - B r i := by
  ext r
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    normalizedCoordinateError, mul_sub, Finset.sum_sub_distrib]

/-- The periodic influence-tail series is summable when every column of the
current mixing matrix sums to one, the future phase weights lie in the standard
simplex, and the following product window contracts every zero-sum state at a
geometric rate.

Layer: Model | Gap: Level 1 (row-valued influence-tail summability from geometric zero-sum product contraction)
Proof: construct each column of `C r - 1` as a normalized coordinate error, apply corrected-lift summability to that coordinate using the supplied shifted-window contraction, identify the two scalar summands, and conclude with `Pi.summable`.
Source: finite-state nonhomogeneous Markov-chain influence series, Mathlib column-stochastic matrices and product-space infinite sums, together with SOptLib's normalized-coordinate-error and corrected-lift summability APIs
Used in: periodic push-pull, push-sum, and gradient-tracking analyses when defining the influence row as a Perron base term plus the absolutely convergent propagated pull-innovation tail
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceSeries_summable_of_geometric_contraction
    {Node : Type*} [Fintype Node] [DecidableEq Node]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (delta rate : Real) (r : Nat)
    (hC : forall i, ∑ k, C r k i = 1)
    (hpi : forall j, pi (r + j + 2) ∈ stdSimplex Real Node)
    (hrate_nonneg : 0 <= rate) (hrate_lt_one : rate < 1)
    (hcontraction : forall j (W : ZeroSumState Node Real),
      stateL1Norm (Matrix.smulVec (consecutiveProduct C (r + 1) j) W.1) <=
        delta⁻¹ * rate ^ j * stateL1Norm W.1) :
    Summable (fun j : Nat => periodicInfluenceSeriesTerm C pi r j) := by
  apply Pi.summable.mpr
  intro i
  have hcolumn : ∑ k : Node, C r k i = 1 := hC i
  let W : ZeroSumState Node Real :=
    normalizedCoordinateError (fun k => C r k i) i hcolumn
  have hsummable : Summable
      (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi (r + 1) j W) := by
    apply periodicCorrectedLiftSeries_summable_of_geometric_contraction
      C pi delta rate (r + 1) W
    · intro j
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpi j
    · exact hrate_nonneg
    · exact hrate_lt_one
    · intro j
      exact hcontraction j W
  have heq :
      (fun j : Nat => periodicInfluenceSeriesTerm C pi r j i) =
        fun j : Nat => periodicCorrectedLiftSeriesTerm C pi (r + 1) j W := by
    funext j
    simp [periodicInfluenceSeriesTerm_apply,
      periodicCorrectedLiftSeriesTerm_def, W, Matrix.smulVec_apply,
      Matrix.mulVec, dotProduct, normalizedCoordinateError, Matrix.one_apply,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [heq]
  exact hsummable

/-- One coordinate of a periodic finite-network influence row is its shifted
base-weight coordinate plus the corrected lift of the corresponding normalized
matrix-column error.

Layer: Model | Gap: Level 1 (coordinate response of a periodic influence row)
Proof: specialize `FiniteNetwork.periodicInfluence_weightedState_eq_perron_add_correctedLift` to the selected coordinate probe, identify the resulting matrix action with `FiniteNetwork.normalizedCoordinateError`, and reduce the two weighted sums to their selected coordinates.
Source: finite-state nonhomogeneous Markov-chain response series, Mathlib finite matrix actions and coordinate sums, and the SOptLib periodic influence, corrected-lift, and normalized-coordinate-error Model APIs
Used in: periodic push-pull unit-noise and concrete phase-coefficient calculations that replace one pull-influence entry by its Perron entry and the propagated response of the matching pull column
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluence_apply_eq_perron_add_correctedLift_normalizedColumnError
    {Node : Type*} [Fintype Node] [DecidableEq Node]
    (C : Nat -> Matrix Node Node Real) (pi : Nat -> Node -> Real)
    (t : Nat) (i : Node)
    (hseries : Summable (fun j : Nat => periodicInfluenceSeriesTerm C pi t j))
    (hcolumn : ∑ k : Node, C t k i = 1) :
    periodicInfluence C pi t i = pi (t + 1) i +
      periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
        (normalizedCoordinateError (fun k => C t k i) i hcolumn) := by
  classical
  let e : Node → ℝ := fun k => if k = i then 1 else 0
  have hinnovation :
      Matrix.smulVec (C t - 1) e =
        (normalizedCoordinateError (fun k => C t k i) i hcolumn : Node → ℝ) := by
    funext k
    simp [e, Matrix.smulVec_apply, normalizedCoordinateError, Matrix.one_apply]
  have hzero : ∑ k : Node, Matrix.smulVec (C t - 1) e k = 0 := by
    rw [hinnovation]
    exact (normalizedCoordinateError (fun k => C t k i) i hcolumn).2
  have hresponse :=
    periodicInfluence_weightedState_eq_perron_add_correctedLift
      C pi t e hseries hzero
  have hinnovationSubtype :
      (⟨Matrix.smulVec (C t - 1) e, hzero⟩ : ZeroSumState Node ℝ) =
        normalizedCoordinateError (fun k => C t k i) i hcolumn := by
    apply Subtype.ext
    exact hinnovation
  rw [hinnovationSubtype] at hresponse
  simpa [e] using hresponse

end FiniteNetwork

namespace FiniteNetwork

/-- Each coordinate of a finite-network influence row is the overlap of the
next left weight with the current normalized right weight, plus the coboundary
of the corresponding corrected normalized-coordinate-error lifts.

Layer: Model | Gap: Level 2 (influence-coordinate overlap and corrected-lift coboundary decomposition)
Proof: rewrite the selected influence coordinate through its normalized column error, identify that error as the difference of consecutive normalized coordinate errors, and combine corrected-lift subtraction with its Poisson equation and the weighted coordinate-error overlap identity.
Source: finite-state nonhomogeneous Markov-chain Poisson equations, Mathlib finite matrix actions and sums, and the SOptLib periodic influence, normalized-coordinate-error, and corrected-lift Model APIs
Used in: periodic push-pull and gradient-tracking DC-gain arguments where phasewise influence entries are averaged and the corrected-lift coboundary telescopes over a communication period
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluence_apply_eq_overlap_add_correctedLift_coboundary
    {Node : Type*} [Fintype Node] [DecidableEq Node]
    (C : Nat -> Matrix Node Node Real) (pi v : Nat -> Node -> Real)
    (t : Nat) (i : Node)
    (hInfluence : Summable (fun j : Nat => periodicInfluenceSeriesTerm C pi t j))
    (hC : forall j : Node, ∑ k : Node, C t k j = 1)
    (hv : ∑ k : Node, v t k = 1)
    (hvNext : ∑ k : Node, v (t + 1) k = 1)
    (hstep : Matrix.smulVec (C t) (v t) = v (t + 1))
    (hLiftCurrent : Summable (fun j : Nat =>
      periodicCorrectedLiftSeriesTerm C pi t j
        (normalizedCoordinateError (v t) i hv)))
    (hLiftNext : Summable (fun j : Nat =>
      periodicCorrectedLiftSeriesTerm C pi (t + 1) j
        (normalizedCoordinateError (v (t + 1)) i hvNext))) :
    periodicInfluence C pi t i =
      (∑ k : Node, pi (t + 1) k * v t k) +
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
          (normalizedCoordinateError (v (t + 1)) i hvNext) -
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t
          (normalizedCoordinateError (v t) i hv) := by
  let Et : ZeroSumState Node Real := normalizedCoordinateError (v t) i hv
  let Enext : ZeroSumState Node Real :=
    normalizedCoordinateError (v (t + 1)) i hvNext
  have htransportZero :
      ∑ k : Node, Matrix.smulVec (C t) Et.1 k = 0 := by
    simp only [Matrix.smulVec_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc
      (∑ j : Node, ∑ k : Node, C t k j * Et.1 j) =
          ∑ j : Node, (∑ k : Node, C t k j) * Et.1 j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ = ∑ j : Node, Et.1 j := by simp only [hC, one_mul]
      _ = 0 := Et.2
  let transported : ZeroSumState Node Real :=
    ⟨Matrix.smulVec (C t) Et.1, htransportZero⟩
  have hLiftEt :
      Summable (fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j Et) := by
    simpa only [Et] using hLiftCurrent
  have hLiftEnext : Summable (fun j : Nat =>
      periodicCorrectedLiftSeriesTerm C pi (t + 1) j Enext) := by
    simpa only [Enext] using hLiftNext
  have hLiftTransported : Summable (fun j : Nat =>
      periodicCorrectedLiftSeriesTerm C pi (t + 1) j transported) := by
    have htail : Summable (fun j : Nat =>
        periodicCorrectedLiftSeriesTerm C pi t (j + 1) Et) := by
      exact (summable_nat_add_iff
        (f := fun j : Nat => periodicCorrectedLiftSeriesTerm C pi t j Et) 1).2
          hLiftEt
    apply htail.congr
    intro j
    change periodicCorrectedLiftSeriesTerm C pi t (j + 1) Et =
      periodicCorrectedLiftSeriesTerm C pi (t + 1) j
        ⟨Matrix.smulVec (C t) Et.1, htransportZero⟩
    exact periodicCorrectedLiftSeriesTerm_succ_transport
      C pi t j Et htransportZero
  have hinnovation :
      normalizedCoordinateError (fun k => C t k i) i (hC i) =
        ⟨Enext.1 - transported.1, by
          change ∑ k : Node, (Enext.1 k - transported.1 k) = 0
          rw [Finset.sum_sub_distrib, Enext.2, transported.2, sub_self]⟩ := by
    apply Subtype.ext
    change (normalizedCoordinateError (fun k => C t k i) i (hC i) : Node -> Real) =
      (normalizedCoordinateError (v (t + 1)) i hvNext : Node -> Real) -
        Matrix.smulVec (C t) (normalizedCoordinateError (v t) i hv : Node -> Real)
    exact columnInnovation_eq_normalizedCoordinateError_sub_smulVec
      (C t) (v t) (v (t + 1)) i (hC i) hv hvNext hstep
  rw [periodicInfluence_apply_eq_perron_add_correctedLift_normalizedColumnError
    C pi t i hInfluence (hC i), hinnovation]
  rw [periodicCorrectedLift_sub C pi (t + 1) Enext transported
    hLiftEnext hLiftTransported]
  have hpoisson :
      periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t Et =
        (∑ k : Node, pi (t + 1) k * Et.1 k) +
          periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
            transported := by
    simpa [transported] using
      (periodicCorrectedLift_poisson C pi t Et htransportZero hLiftEt)
  have hweighted :
      (∑ k : Node, pi (t + 1) k * Et.1 k) =
        (∑ k : Node, pi (t + 1) k * v t k) - pi (t + 1) i := by
    simpa [Et] using weightedState_normalizedCoordinateError
      (pi (t + 1)) (v t) i hv
  rw [hweighted] at hpoisson
  change pi (t + 1) i +
      (periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1) Enext -
        periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) (t + 1)
          transported) = _
  linarith

/-- The average of a periodic finite-network influence sequence is the constant
row whose entry is the average overlap of the shifted left weights with the
current normalized right weights.

Layer: Model | Gap: Level 2 (period-average influence and Perron-overlap identity)
Proof: apply the influence-coordinate overlap/corrected-lift decomposition at every phase, telescope the lift coboundary with `Finset.sum_range_sub`, and use schedule/left-weight periodicity together with right-weight endpoint equality to identify its two endpoints.
Source: finite-state nonhomogeneous Markov-chain Poisson equations, Mathlib finite-period sums, and the SOptLib periodic influence, corrected-lift, and average Perron-overlap Model APIs
Used in: periodic push-pull, push-sum, and gradient-tracking DC-gain arguments that replace the phase-average influence row by a constant row before deriving gain positivity and effective-network-size bounds
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodicInfluenceAverage_eq_averagePerronOverlap
    {Node : Type*} [Fintype Node] [DecidableEq Node]
    {p : Nat} (C : Nat -> Matrix Node Node Real)
    (pi v : Nat -> Node -> Real)
    (hC_periodic : Function.Periodic C p)
    (hpi_periodic : Function.Periodic pi p)
    (hv_endpoint : v p = v 0)
    (hInfluence : forall t : Nat, t < p ->
      Summable (fun j : Nat => periodicInfluenceSeriesTerm C pi t j))
    (hC : forall t : Nat, t < p -> forall j : Node,
      ∑ k : Node, C t k j = 1)
    (hv : forall t : Nat, t ≤ p -> ∑ k : Node, v t k = 1)
    (hstep : forall t : Nat, t < p ->
      Matrix.smulVec (C t) (v t) = v (t + 1))
    (hLift : forall t : Nat, (ht : t ≤ p) -> forall i : Node,
      Summable (fun j : Nat =>
        periodicCorrectedLiftSeriesTerm C pi t j
          (normalizedCoordinateError (v t) i (hv t ht)))) :
    (fun i : Node =>
      ((p : Real)⁻¹) * ∑ r : Fin p, periodicInfluence C pi r.1 i) =
      (fun _ : Node => averagePeriodicPerronOverlap (p := p) pi v) := by
  classical
  funext i
  rw [averagePeriodicPerronOverlap_def]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
      (fun r : Nat => periodicInfluence C pi r i),
    Fin.sum_univ_eq_sum_range
      (fun r : Nat => ∑ k : Node, pi (r + 1) k * v r k)]
  let q : Nat -> Real := fun t =>
    if ht : t ≤ p then
      periodicCorrectedLift pi (fun s j => consecutiveProduct C s j) t
        (normalizedCoordinateError (v t) i (hv t ht))
    else 0
  have herror :
      normalizedCoordinateError (v p) i (hv p le_rfl) =
        normalizedCoordinateError (v 0) i (hv 0 (Nat.zero_le p)) := by
    apply Subtype.ext
    simp only [normalizedCoordinateError]
    rw [hv_endpoint]
  have hq_period : q p = q 0 := by
    dsimp [q]
    rw [dif_pos le_rfl]
    rw [herror]
    simpa using
      (periodicCorrectedLift_add_period_mul C pi p 0 1
        (normalizedCoordinateError (v 0) i (hv 0 (Nat.zero_le p)))
        hC_periodic hpi_periodic)
  calc
    ∑ t ∈ Finset.range p, periodicInfluence C pi t i =
        ∑ t ∈ Finset.range p,
          ((∑ k : Node, pi (t + 1) k * v t k) + q (t + 1) - q t) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htp : t < p := Finset.mem_range.mp ht
      have ht_le : t ≤ p := Nat.le_of_lt htp
      have ht1_le : t + 1 ≤ p := by omega
      simpa only [q, dif_pos ht_le, dif_pos ht1_le] using
        (periodicInfluence_apply_eq_overlap_add_correctedLift_coboundary
          C pi v t i (hInfluence t htp) (hC t htp)
          (hv t ht_le) (hv (t + 1) ht1_le) (hstep t htp)
          (hLift t ht_le i) (hLift (t + 1) ht1_le i))
    _ = (∑ t ∈ Finset.range p,
          ∑ k : Node, pi (t + 1) k * v t k) +
          ∑ t ∈ Finset.range p, (q (t + 1) - q t) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = (∑ t ∈ Finset.range p,
          ∑ k : Node, pi (t + 1) k * v t k) + (q p - q 0) := by
      rw [Finset.sum_range_sub]
    _ = ∑ t ∈ Finset.range p,
          ∑ k : Node, pi (t + 1) k * v t k := by
      rw [hq_period, sub_self, add_zero]

end FiniteNetwork
