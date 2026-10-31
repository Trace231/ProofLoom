import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Logic.Equiv.Prod
import SOptLib.Model.OperatorMeans
import SOptLib.Model.ParameterChoices

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: dependent tensor coordinate index; orig was MultiIndex
-- generality used: an arbitrary mode type and an arbitrary type of coordinates in each
--   mode; no finiteness, decidable equality, algebraic, measure, or regularity assumptions
-- portable call pattern: tensor adaptive-gradient and multilinear algorithms use one
--   coordinate per mode while changing the mode type and the coordinate types
-- counterargument checked: this is not paper-local traceability or a value-formula wrapper;
--   it is a transparent type synonym that gives the recurring dependent coordinate space a
--   stable domain name across tensor definitions and theorems
-- coverage search: symbol search for "dependent tensor coordinate index one coordinate per
--   mode" found only the local MultiIndex; Mathlib semantic search found HolorIndex, whose
--   list/subtype representation does not cover arbitrary mode and coordinate types
-- minimal hypotheses: all already minimal; the dependent function type needs no typeclasses

/-- The type of tensor-entry indices with one coordinate chosen in every mode.

Unlike list-shaped tensor indices, the coordinate type may depend on an arbitrary mode type.

Layer: Model | Concept: dependent tensor coordinate index
Proof: (definitional construction; dependent function type selecting one coordinate in each mode)
Source: Lean dependent function types and Mathlib's list-shaped `HolorIndex` tensor-coordinate model
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that index entries, matricizations, and flattened operators by a common heterogeneous tensor shape
Book citation: book/research/Source.json#/algorithm_spec
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
abbrev TensorIndex {ι : Type u} (dims : ι → Type v) := (i : ι) → dims i

end SOptLib

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: scalar-valued tensor space; orig was TensorSpace
-- generality used: an arbitrary mode type, a dependent coordinate type in each mode,
--   and an arbitrary scalar type; no finiteness, decidable equality, or algebraic assumptions
-- portable call pattern: tensor adaptive-gradient and multilinear algorithms represent
--   iterates and gradients as scalar-valued functions while changing tensor shapes and scalars
-- counterargument checked: although this is a transparent type alias, it is not a synonym for
--   an existing tensor construction; it names the recurring function-space representation of
--   tensors and distinguishes it from Mathlib's algebraic tensor products
-- coverage search: symbol searches for "scalar valued tensor dependent finite coordinate index
--   function space" and "TensorSpace tensor index scalar functions" found no matching project
--   or SOptLib declaration; Mathlib semantic search returned `PiTensorProduct`, whose algebraic
--   quotient construction does not represent arrays indexed by a dependent coordinate product
-- minimal hypotheses: all already minimal; the dependent function space needs no typeclasses

/-- The space of tensors whose entries have values in `R` and whose coordinates are indexed by
one choice from each member of the dependent family `dims`.

Layer: Model | Concept: scalar-valued tensors on a dependent multi-index
Proof: (definitional construction; function space from the full dependent coordinate index to the scalar type)
Source: Lean dependent function types, together with `SOptLib.TensorIndex` for heterogeneous tensor coordinates
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that represent iterates, gradients, and mode-wise transformations over varying tensor shapes and scalar types
Book citation: book/research/Source.json#/setup/variable_space
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
abbrev TensorSpace {ι : Type u} (dims : ι → Type v) (R : Type w) :=
  TensorIndex dims → R

end SOptLib


namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: tensor matricization complement-coordinate column index; orig was ModeColumn
-- generality used: an arbitrary mode type and an arbitrary coordinate type in each mode;
--   no finiteness, decidable equality, scalar, algebraic, or measure assumptions
-- portable call pattern: tensor matricization and modewise preconditioning use the coordinates
--   outside a selected mode as a column index while changing the mode and coordinate families
-- counterargument checked: this is a transparent type synonym and specializes TensorIndex, but
--   its complement-mode domain is the canonical second factor in mode matricization rather than
--   an unrestricted caller-side expression, and it recurs in matricization and reindexing APIs
-- coverage search: symbol searches for "tensor mode column complement coordinates selected mode
--   dependent tuple" and "dependent function indices excluding selected index" found no covering
--   SOptLib declaration; Mathlib semantic search found Equiv.piSplitAt, which uses this type as a
--   codomain factor but does not name the tensor-matricization column-index concept
-- minimal hypotheses: all already minimal; forming the complement subtype and dependent function
--   type does not require DecidableEq or Fintype

/-- The column-index type of a tensor matricization at mode `i`, consisting of one coordinate
from every mode other than `i`.

Layer: Model | Concept: tensor matricization complement-coordinate column index
Proof: (definitional construction; `TensorIndex` over the subtype of modes unequal to the selected mode)
Source: Mathlib's `Equiv.piSplitAt` complement-coordinate factor and `SOptLib.TensorIndex` for dependent tensor coordinates
Used in: mode matricization, transposed mode vectorization, and modewise Kronecker-preconditioning steps that separate one row coordinate from all remaining tensor coordinates
Book citation: book/research/Source.json#/definitions/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
abbrev TensorModeColumn {ι : Type u} (dims : ι → Type v) (i : ι) :=
  TensorIndex (fun j : {j : ι // j ≠ i} => dims j.1)

end SOptLib


namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: selected-mode tensor matricization; orig was matricization
-- generality used: an arbitrary mode type with decidable equality, arbitrary
--   mode-dependent coordinate types, and an arbitrary scalar type; no finiteness,
--   algebraic, topological, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: tensor adaptive-gradient, tensor decomposition, and multilinear
--   algorithms form a matrix from a tensor at a selected mode while changing the mode
--   family, tensor shape, scalar type, tensor value, and selected mode
-- counterargument checked: the construction is entrywise and uses `Equiv.piSplitAt`, but
--   it is the standard named matricization operation rather than a paper-local wrapper;
--   rank, Gram, vectorization, and mode-product laws all use it as their shared object
-- coverage search: symbol searches for "tensor matricization selected mode row complementary
--   coordinates matrix" and "dependent pi split selected coordinate complement inverse
--   equality" found no covering declaration; Mathlib semantic search returned tensor-product
--   matrix and block APIs, while the inspected `Equiv.piSplitAt` signature supplies only the
--   underlying dependent-product equivalence, not tensor matricization
-- minimal hypotheses: `DecidableEq` on the mode type is exactly what `Equiv.piSplitAt`
--   requires; neither the mode family nor its coordinate types need finiteness

/-- Matricize a tensor at mode `i`, using that mode's coordinate as the row index and all
complementary coordinates as the column index.

Layer: Model | Concept: selected-mode tensor matricization
Proof: (definitional construction; precompose tensor evaluation with the inverse of the selected-coordinate dependent-product split)
Source: Mathlib's `Equiv.piSplitAt` decomposition of dependent function spaces and function-valued matrices
Used in: modewise tensor preconditioners and tensor decompositions that express contraction Gramians, matricization rank bounds, vectorization identities, and mode products
Book citation: book/research/Source.json#/definitions/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorMatricization
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v} {R : Type w}
    (A : TensorSpace dims R) (i : ι) :
    Matrix (dims i) (TensorModeColumn dims i) R :=
  fun row col => A ((Equiv.piSplitAt i dims).symm (row, col))

/-- An entry of a selected-mode tensor matricization is the tensor entry obtained by
reassembling its row coordinate with its complementary column coordinates.

Layer: Model | Gap: Level 0 (entrywise specification of selected-mode tensor matricization)
Proof: by rfl after unfolding `tensorMatricization`
Source: Mathlib's inverse law interface for `Equiv.piSplitAt` and function-valued matrix evaluation
Used in: entrywise proofs of tensor contraction, matricization rank bounds, vectorization identities, and compatibility of matricization with mode products
Book citation: book/research/Source.json#/definitions/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorMatricization_def
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v} {R : Type w}
    (A : TensorSpace dims R) (i : ι)
    (row : dims i) (col : TensorModeColumn dims i) :
    tensorMatricization A i row col =
      A ((Equiv.piSplitAt i dims).symm (row, col)) := by
  rfl

/-- Splitting a tensor index into its selected coordinate and complementary coordinates,
then looking up the corresponding matricization entry, recovers the original tensor entry. -/
@[simp]
theorem tensorMatricization_apply_piSplitAt
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v} {R : Type w}
    (A : TensorSpace dims R) (i : ι) (idx : TensorIndex dims) :
    tensorMatricization A i
        ((Equiv.piSplitAt i dims idx).1) ((Equiv.piSplitAt i dims idx).2) = A idx := by
  change A ((Equiv.piSplitAt i dims).symm ((Equiv.piSplitAt i dims) idx)) = A idx
  rw [Equiv.symm_apply_apply]

/-- Matricization at any fixed mode loses no tensor entries. -/
theorem tensorMatricization_injective
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v} {R : Type w} (i : ι) :
    Function.Injective (fun A : TensorSpace dims R => tensorMatricization A i) := by
  intro A B h
  funext idx
  simpa only [tensorMatricization_apply_piSplitAt] using
    congrFun (congrFun h ((Equiv.piSplitAt i dims idx).1))
      ((Equiv.piSplitAt i dims idx).2)

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: rank-one tensor from a finite dependent family of coordinate vectors;
--   orig was rankOneTensor and the concept-derived name remains appropriate
-- generality used: an arbitrary finite mode type, arbitrary mode-dependent coordinate
--   types, and coefficients in a commutative monoid; no coordinate finiteness,
--   decidable equality, topology, norm, or measure structure is needed
-- portable call pattern: tensor adaptive-gradient, tensor decomposition, and multilinear
--   preconditioning proofs construct a separable tensor while changing the mode type,
--   coordinate types, coefficient monoid, and component vectors
-- counterargument checked: although the construction is entrywise and short, rank-one
--   tensors are a standard named multilinear object whose stable constructor and application
--   theorem support later matricization and vectorization APIs; it is not merely paper tracing
-- coverage search: searches for "rank one tensor pointwise dependent product coordinate
--   vectors" and "dependent product of coordinate functions finite product tensor" found no
--   SOptLib or project declaration; Mathlib provides binary matrix outer products and the
--   `Holor.CPRankMax1` predicate, but neither constructs this heterogeneous function-space tensor
-- minimal hypotheses: `Fintype` on the mode type and `CommMonoid` on coefficients are exactly
--   what the unordered finite product requires; all other source restrictions were removed

/-- The rank-one tensor generated by a finite dependent family of coordinate vectors.

At a multi-index, its entry is the product of the corresponding component from every mode.

Layer: Model | Concept: rank-one tensor from a dependent family of vectors
Proof: (definitional construction; pointwise finite product of the selected vector coordinates)
Source: Mathlib finite commutative products and the coordinate formula for CP rank-one tensors
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that vectorize or matricize separable tensors assembled from modewise vectors
Book citation: book/research/Source.json#/key_lemmas/13
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def rankOneTensor {ι : Type u} [Fintype ι] {R : Type w} [CommMonoid R]
    {dims : ι → Type v} (u : (i : ι) → dims i → R) : TensorSpace dims R :=
  fun idx => ∏ i : ι, u i (idx i)

/-- A rank-one tensor is the pointwise finite product of its component vectors. -/
@[simp]
theorem rankOneTensor_def {ι : Type u} [Fintype ι]
    {R : Type w} [CommMonoid R] {dims : ι → Type v}
    (u : (i : ι) → dims i → R) :
    rankOneTensor u = fun idx => ∏ i : ι, u i (idx i) := by
  rfl

/-- Evaluating a rank-one tensor selects one coordinate from each component vector and
multiplies the resulting finite family.

Layer: Model | Gap: Level 0 (rank-one tensor coordinate formula)
Proof: by rfl after unfolding `rankOneTensor`.
Source: Mathlib finite commutative products and dependent function application
Used in: entrywise vectorization and matricization calculations for separable tensors in tensor preconditioners
Book citation: book/research/Source.json#/key_lemmas/13
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem rankOneTensor_apply {ι : Type u} [Fintype ι]
    {R : Type w} [CommMonoid R] {dims : ι → Type v}
    (u : (i : ι) → dims i → R) (idx : TensorIndex dims) :
    rankOneTensor u idx = ∏ i : ι, u i (idx i) := by
  rfl

/-- Taking the rank-one tensor of componentwise products is the pointwise product of the
corresponding rank-one tensors. -/
theorem rankOneTensor_mul {ι : Type u} [Fintype ι]
    {R : Type w} [CommMonoid R] {dims : ι → Type v}
    (u v : (i : ι) → dims i → R) :
    rankOneTensor (fun i x => u i x * v i x) = rankOneTensor u * rankOneTensor v := by
  funext idx
  simp only [rankOneTensor_apply, Pi.mul_apply, Finset.prod_mul_distrib]

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: selected-mode matricization formula for a rank-one tensor; orig was
--   lemma14_rankOneTensor_matricization_block
-- generality used: an arbitrary finite mode type with decidable equality, arbitrary
--   mode-dependent coordinate types, and coefficients in a commutative monoid; no coordinate
--   finiteness, topology, norm, measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: tensor decompositions and mode-wise preconditioners rewrite the
--   selected-mode matricization of a separable tensor while changing the mode family,
--   coordinate types, coefficient monoid, selected mode, and component vectors
-- counterargument checked: this is not paper-local traceability or a pure wrapper; Mathlib's
--   product-splitting theorem does not perform the dependent mode-index assembly or connect
--   that split to the rank-one tensor constructor, and no SOptLib theorem covers this equality
-- coverage search: symbol search for "rank one tensor matricization selected mode vector
--   complementary coordinate product" found only `rankOneTensor` and an unrelated Loewner-order
--   transport theorem; Mathlib semantic search found `Fintype.prod_eq_mul_prod_subtype_ne`, which
--   supplies the product split but not the tensor-matricization contract
-- minimal hypotheses: `Fintype` and `DecidableEq` on the mode type support the complementary
--   subtype product and dependent selected-mode index; `CommMonoid` is exactly what the finite
--   unordered product requires, and coordinate types need no finiteness or decidable equality

/-- The selected-mode matricization of a rank-one tensor factors into the selected component
vector and the product of all complementary component coordinates.

The left side writes matricization entrywise: a row coordinate and a dependent column of all
other coordinates are assembled into one full tensor index.

Layer: Model | Gap: Level 1 (rank-one tensor selected-mode matricization factorization)
Proof: unfold rank-one tensor evaluation, split the finite product at the selected mode with `Fintype.prod_eq_mul_prod_subtype_ne`, and simplify the dependent assembled index on the selected and complementary modes.
Source: Mathlib finite commutative products over a distinguished index and dependent function types for heterogeneous tensor coordinates
Used in: tensor decomposition and mode-wise preconditioner proofs that rewrite a separable tensor matricization as a row factor times its complementary-coordinate product
Book citation: book/research/Source.json#/key_lemmas/13
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorMatricization_rankOneTensor
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommMonoid R] {dims : ι → Type v}
    (u : (j : ι) → dims j → R) (i : ι) :
    (fun (row : dims i) (col : (j : {j : ι // j ≠ i}) → dims j.1) =>
        rankOneTensor u (fun j =>
          if h : j = i then
            _root_.cast (by rw [h]) row
          else
            col ⟨j, h⟩)) =
      fun row col => u i row * ∏ j : {j : ι // j ≠ i}, u j.1 (col j) := by
  funext row col
  let idx : (j : ι) → dims j := fun j =>
    if h : j = i then
      _root_.cast (by rw [h]) row
    else
      col ⟨j, h⟩
  change rankOneTensor u idx = _
  rw [rankOneTensor_apply,
    Fintype.prod_eq_mul_prod_subtype_ne (fun j => u j (idx j)) i]
  apply congrArg₂ (fun x y : R => x * y)
  · simp [idx]
  · apply Finset.prod_congr rfl
    intro j _hj
    simp [idx, j.property]

end SOptLib


namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: modewise tensor self-contraction, named `tensorContraction`; the
--   original name already denotes the standard contraction Gramian used here
-- generality used: an arbitrary mode type with decidable equality, arbitrary
--   mode-dependent coordinate types, and coefficients with commutative finite addition
--   together with multiplication; only the complementary matricization column type is finite
-- portable call pattern: tensor adaptive-gradient and multilinear algorithms form a
--   selected-mode Gram accumulator increment while changing the tensor shape, scalar
--   type, tensor value, and selected mode
-- counterargument checked: the construction composes matricization with `Matrix.leftGram`,
--   but modewise tensor contraction is a recognized recurring object whose tensor-level
--   name and entrywise API are used across PSD accumulators, rank bounds, and mode embeddings
-- coverage search: symbol searches for "modewise tensor self contraction left Gram matrix
--   matricization" and "tensor contraction matricization transpose matrix product" found no
--   covering SOptLib declaration; Mathlib semantic search found `Matrix.gram`, which uses an
--   inner product (and conjugation over complex scalars), while staged `Matrix.leftGram`
--   covers only the underlying matrix operation and not the tensor contraction object
-- minimal hypotheses: `DecidableEq` on modes is required by tensor matricization,
--   `Fintype (TensorModeColumn dims i)` is exactly the contracted finite sum, and `Mul`
--   with `AddCommMonoid` are precisely the assumptions used by matrix multiplication

/-- Contract a tensor with itself along every coordinate except mode `i`, equivalently taking
the left Gram matrix of its mode-`i` matricization.

Layer: Model | Concept: modewise tensor self-contraction Gram matrix
Proof: (definitional construction; apply `Matrix.leftGram` to the selected-mode tensor matricization)
Source: Mathlib finite matrix multiplication and transpose, composed with `SOptLib.tensorMatricization` and `Matrix.leftGram`
Used in: tensor adaptive-gradient accumulator updates that add a positive-semidefinite modewise Gram increment before applying matrix powers
Book citation: book/research/Source.json#/definitions/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorContraction
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v} {R : Type w}
    [Mul R] [AddCommMonoid R] (A : TensorSpace dims R) (i : ι)
    [Fintype (TensorModeColumn dims i)] : Matrix (dims i) (dims i) R :=
  tensorMatricization A i * (tensorMatricization A i).transpose

/-- A modewise tensor self-contraction unfolds to the matricization multiplied by its
transpose.

Layer: Model | Gap: Level 0 (modewise tensor contraction unfolding rule)
Proof: by rfl after unfolding `tensorContraction`, `Matrix.leftGram`, and the matrix transpose product
Source: Mathlib `Matrix.transpose` and finite matrix multiplication through `Matrix.leftGram`
Used in: rewriting tensor preconditioner accumulator increments into explicit matricization Gram products for positivity and rank arguments
Book citation: book/research/Source.json#/definitions/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorContraction_def
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v} {R : Type w}
    [Mul R] [AddCommMonoid R] (A : TensorSpace dims R) (i : ι)
    [Fintype (TensorModeColumn dims i)] :
    tensorContraction A i =
      tensorMatricization A i * (tensorMatricization A i).transpose := by
  rfl

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: dependent finite-family Kronecker product of square matrices;
--   orig was tensorKronecker and the concept-derived name remains appropriate
-- generality used: an arbitrary finite mode type, arbitrary mode-dependent coordinate
--   types, and coefficients in a commutative monoid; coordinate finiteness and decidable
--   equality are not needed to form the entrywise product
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning proofs
--   form one product-index operator from modewise matrices while changing the mode type,
--   coordinate types, coefficient semiring, and matrix family
-- counterargument checked: this is not a paper-only caller expression or thin rename;
--   the dependent finite-family operator is the stable object needed by multiplication,
--   order, positivity, power, and trace APIs, while Mathlib exposes only binary Kronecker
--   products over ordinary product indices
-- coverage search: lean_search_symbols queries for dependent finite Kronecker products
--   found no project or SOptLib declaration; Mathlib semantic search returned the binary
--   Matrix.kronecker and Matrix.kroneckerMap definitions, which do not cover a dependent
--   family indexed by an arbitrary finite mode type
-- minimal hypotheses: Fintype on the mode type and CommMonoid on coefficients are exactly
--   what the finite product requires; no assumptions on the coordinate types are used

/-- The Kronecker product of a finite dependent family of square matrices, represented on
the full dependent product of their coordinate types.

Each entry is the product of the corresponding entry in every modewise matrix.

Layer: Model | Concept: dependent finite-family Kronecker product
Proof: (definitional construction; entrywise finite product across the mode-indexed matrix family)
Source: Mathlib finite commutative products and the entrywise definition of `Matrix.kronecker`
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that assemble modewise preconditioners into one flattened product-index operator
Book citation: book/research/Source.json#/definitions/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorKronecker {ι : Type u} [Fintype ι] {R : Type w} [CommMonoid R]
    {dims : ι → Type v} (M : (i : ι) → Matrix (dims i) (dims i) R) :
    Matrix (TensorIndex dims) (TensorIndex dims) R :=
  fun a b => ∏ i : ι, M i (a i) (b i)

/-- An entry of a dependent finite-family Kronecker product is the product of the
corresponding entries of all its modewise factors.

Layer: Model | Gap: Level 0 (dependent Kronecker product entry formula)
Proof: by rfl after unfolding `tensorKronecker`.
Source: Mathlib finite commutative products and matrix function application
Used in: entrywise multiplication, order, positivity, power, and trace calculations for tensor preconditioners
Book citation: book/research/Source.json#/definitions/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorKronecker_apply {ι : Type u} [Fintype ι]
    {R : Type w} [CommMonoid R] {dims : ι → Type v}
    (M : (i : ι) → Matrix (dims i) (dims i) R) (a b : TensorIndex dims) :
    tensorKronecker M a b = ∏ i : ι, M i (a i) (b i) := by
  rfl

/-- Matrix multiplication of dependent finite-family Kronecker products is the
dependent Kronecker product of the modewise matrix multiplications.

Layer: Model | Gap: Level 1 (dependent Kronecker product multiplication)
Proof: expand matrix multiplication entrywise and exchange the sum over the finite
dependent product with the product of the coordinatewise sums.
Source: Mathlib finite sums over dependent products and matrix multiplication
Used in: tensor and multilinear preconditioning arguments that compose modewise operators
-/
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq α

theorem tensorKronecker_mul {ι : Type u} [Fintype ι]
    {R : Type w} [CommSemiring R] {dims : ι → Type v}
    [∀ i, Fintype (dims i)]
    (X Y : (i : ι) → Matrix (dims i) (dims i) R) :
    tensorKronecker X * tensorKronecker Y =
      tensorKronecker (fun i => X i * Y i) := by
  classical
  ext a b
  calc
    (tensorKronecker X * tensorKronecker Y) a b =
        ∑ x : TensorIndex dims,
          ∏ i : ι, X i (a i) (x i) * Y i (x i) (b i) := by
          simp [Matrix.mul_apply, Finset.prod_mul_distrib]
    _ = ∏ i : ι, ∑ s : dims i, X i (a i) s * Y i s (b i) := by
          simpa [Fintype.piFinset_univ] using
            (Finset.prod_univ_sum
              (fun i : ι => (Finset.univ : Finset (dims i)))
              (fun i s => X i (a i) s * Y i s (b i))).symm
    _ = tensorKronecker (fun i => X i * Y i) a b := by
          simp [Matrix.mul_apply]

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq α

-- Generalization plan (G0):
-- concept/name: trace of a dependent finite-family Kronecker product; orig was
--   `genericTrace_tensorKronecker_eq_prod_trace`, renamed `tensorKronecker_trace`
-- generality used: arbitrary finite mode type, arbitrary finite mode-dependent coordinate
--   types, and coefficients in a commutative semiring; no order, topology,
--   finite-dimensional-space, measure, or optimization assumptions
-- portable call pattern: a tensor optimizer or multilinear preconditioner assembles
--   changing modewise square matrices over a changing finite tensor shape and rewrites
--   the assembled operator's trace as the product of its component traces
-- counterargument checked: Mathlib's binary `Matrix.trace_kronecker` is the closest
--   result, but it does not cover an arbitrary dependent finite family; this theorem
--   is the natural trace API for the already-staged `tensorKronecker`, not paper-local
--   traceability or a rename of one existing declaration
-- coverage search: symbol queries for "trace dependent finite family Kronecker product
--   equals product traces" and "tensorKronecker trace product" found the defining
--   `tensorKronecker` API but no trace theorem; Mathlib semantic search found only the
--   binary `Matrix.trace_kronecker` and tensor-product linear-map trace theorems
-- minimal hypotheses: `Fintype` for modes and every coordinate type make both traces
--   finite, and `CommSemiring` is exactly what exchanges the dependent sum and product;
--   decidable equality is supplied classically as an implementation detail

/-- The trace of a dependent finite-family Kronecker product is the product of the
traces of its modewise factors.

Layer: Model | Gap: Level 1 (dependent finite-family Kronecker trace factorization)
Proof: unfold matrix trace and the entry formula for `tensorKronecker`, then exchange the sum over the finite dependent coordinate product with the product of coordinatewise sums using `Finset.prod_univ_sum`.
Source: Mathlib finite dependent sums and products, `Matrix.trace`, and the binary `Matrix.trace_kronecker` identity
Used in: tensor adaptive-gradient regret proofs that factor the terminal flattened preconditioner trace into the product of modewise powered-accumulator traces
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_trace {ι : Type u} [Fintype ι]
    {R : Type w} [CommSemiring R] {dims : ι → Type v}
    [∀ i, Fintype (dims i)]
    (M : (i : ι) → Matrix (dims i) (dims i) R) :
    Matrix.trace (tensorKronecker M) =
      ∏ i : ι, Matrix.trace (M i) := by
  classical
  unfold Matrix.trace
  simpa [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum
      (fun i : ι => (Finset.univ : Finset (dims i)))
      (fun i x => M i x x)).symm

end SOptLib


open scoped BigOperators Kronecker MatrixOrder

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: transport of a vector outer-product Loewner bound between a tensor's mode matricization and its full coordinates; orig was Lemma_15_matricized_psd_equivalence.
-- generality used: arbitrary finite mode type and arbitrary finite coordinate type in every mode, with decidable equality only for matrix identities and Loewner order; no measure, convexity, smoothness, oracle, topology, normed-space, or algorithm-state hypotheses.
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioner proofs call the same transport while changing the tensor, selected mode, coordinate types, and comparison matrix.
-- counterargument checked: not paper-local or a pure rename because the theorem constructs the canonical dependent-function reindexing and transports both the vector outer product and Kronecker comparison matrix in one reusable call; Mathlib only supplies the lower-level PSD-submatrix equivalence.
-- coverage search: lean_search_symbols "tensor matricization vector outer Loewner bound equivalent mode embedded Kronecker matrix" found only private Shampoo-local helpers; "matrix Loewner order invariant under equivalence reindexing" found the private local transport lemma; lean_leansearch "matrix Loewner order equivalence after reindexing rows and columns" found Matrix reindexing APIs but no theorem with this tensor/Kronecker contract.
-- minimal hypotheses: finiteness is required by matrix Loewner order and decidable equality by identity matrices and reindexAlgEquiv; all paper setup, rank, positivity, and natural-dimension restrictions were removed.

/-- A vector outer-product Loewner bound in mode-matricized tensor coordinates
is equivalent to its full-coordinate bound after canonically reindexing the
Kronecker comparison matrix.

Layer: Model | Gap: Level 1 (tensor matricization Loewner-order reindexing)
Proof: construct the canonical equivalence between a selected-mode row paired with all remaining coordinates and the full dependent tensor index, then use `Matrix.posSemidef_submatrix_equiv` to transport Loewner order and simplify the reindexed vector outer product.
Source: Mathlib matrix Loewner order, positive-semidefinite submatrix equivalence, dependent function types, and Kronecker products
Used in: converting a mode-matricized rank bound into the full tensor-vector preconditioner inequality in tensor adaptive-gradient analyses
Book citation: book/research/Source.json#/key_lemmas/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorMatricization_vecMulVec_le_kronecker_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {dims : ι → Type*} [(j : ι) → Fintype (dims j)]
    [(j : ι) → DecidableEq (dims j)]
    (G : ((j : ι) → dims j) → ℝ) (i : ι)
    (B : Matrix (dims i) (dims i) ℝ) :
    let e :
        (dims i × ((j : {j : ι // j ≠ i}) → dims j.1)) ≃
          ((j : ι) → dims j) :=
      { toFun := fun rc j =>
          if h : j = i then
            _root_.cast (by rw [h]) rc.1
          else
            rc.2 ⟨j, h⟩
        invFun := fun idx => (idx i, fun j => idx j.1)
        left_inv := by
          intro rc
          rcases rc with ⟨row, col⟩
          apply Prod.ext
          · simp
          · funext j
            simp [j.property]
        right_inv := by
          intro idx
          funext j
          by_cases h : j = i
          · subst j
            simp
          · simp [h] }
    Matrix.vecMulVec (fun rc => G (e rc)) (fun rc => G (e rc)) ≤
        B ⊗ₖ (1 : Matrix ((j : {j : ι // j ≠ i}) → dims j.1)
          ((j : {j : ι // j ≠ i}) → dims j.1) ℝ) ↔
      Matrix.vecMulVec G G ≤
        fun a b => B (a i) (b i) *
          ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : ℝ) else 0 := by
  let e :
      (dims i × ((j : {j : ι // j ≠ i}) → dims j.1)) ≃
        ((j : ι) → dims j) :=
    { toFun := fun rc j =>
        if h : j = i then
          _root_.cast (by rw [h]) rc.1
        else
          rc.2 ⟨j, h⟩
      invFun := fun idx => (idx i, fun j => idx j.1)
      left_inv := by
        intro rc
        rcases rc with ⟨row, col⟩
        apply Prod.ext
        · simp
        · funext j
          simp [j.property]
      right_inv := by
        intro idx
        funext j
        by_cases h : j = i
        · subst j
          simp
        · simp [h] }
  change Matrix.vecMulVec (fun rc => G (e rc)) (fun rc => G (e rc)) ≤
      B ⊗ₖ (1 : Matrix ((j : {j : ι // j ≠ i}) → dims j.1)
        ((j : {j : ι // j ≠ i}) → dims j.1) ℝ) ↔
    Matrix.vecMulVec G G ≤
      fun a b => B (a i) (b i) *
        ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : ℝ) else 0
  have hreindex :
      Matrix.reindexAlgEquiv ℝ ℝ e
          (Matrix.vecMulVec (fun rc => G (e rc)) (fun rc => G (e rc))) =
        Matrix.vecMulVec G G := by
    ext x y
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.vecMulVec_apply]
  have hone (c c' : (j : {j : ι // j ≠ i}) → dims j.1) :
      (1 : Matrix ((j : {j : ι // j ≠ i}) → dims j.1)
        ((j : {j : ι // j ≠ i}) → dims j.1) ℝ) c c' =
        ∏ j : {j : ι // j ≠ i}, if c j = c' j then (1 : ℝ) else 0 := by
    by_cases h : c = c'
    · subst h
      simp
    · have hne : ∃ j : {j : ι // j ≠ i}, c j ≠ c' j := by
        by_contra hnone
        apply h
        funext j
        by_contra hj
        exact hnone ⟨j, hj⟩
      rcases hne with ⟨j, hj⟩
      rw [Matrix.one_apply_ne h]
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  have hcomparison :
      Matrix.reindexAlgEquiv ℝ ℝ e
          (B ⊗ₖ (1 : Matrix ((j : {j : ι // j ≠ i}) → dims j.1)
            ((j : {j : ι // j ≠ i}) → dims j.1) ℝ)) =
        fun a b => B (a i) (b i) *
          ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : ℝ) else 0 := by
    ext a b
    simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    rw [Matrix.kroneckerMap_apply, hone]
    rfl
  rw [← hcomparison, ← hreindex]
  rw [Matrix.le_iff, Matrix.le_iff, ← map_sub]
  simpa [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
    (Matrix.posSemidef_submatrix_equiv
      (M := (B ⊗ₖ (1 : Matrix ((j : {j : ι // j ≠ i}) → dims j.1)
        ((j : {j : ι // j ≠ i}) → dims j.1) ℝ)) -
          Matrix.vecMulVec (fun rc => G (e rc)) (fun rc => G (e rc)))
      e.symm).symm

end SOptLib


namespace Matrix

universe u v

-- Generalization plan (G0):
-- concept/name: diagonal part of a square matrix; orig was diagonalPart and the
--   concept-derived name remains appropriate
-- generality used: arbitrary index and entry types with only decidable equality on
--   indices and a zero entry; no finiteness, ring, order, topology, or measure assumptions
-- portable call pattern: diagonal and coordinate-adaptive matrix algorithms project Gram
--   or accumulator matrices onto diagonal matrices while changing index types and scalars
-- counterargument checked: although the construction composes two small Mathlib operations,
--   the recurring diagonal projection is a stable mathematical operator used throughout
--   accumulator updates and deserves a named object plus a characterizing entry theorem
-- coverage search: symbol searches for "matrix diagonal projection keeps diagonal entries
--   zeros off diagonal" and "Matrix diag diagonal" found no project or SOptLib equivalent;
--   Mathlib semantic search found the component definitions Matrix.diag and Matrix.diagonal,
--   but no declaration for their projection-shaped composition
-- minimal hypotheses: DecidableEq on the index and Zero on entries are exactly the
--   assumptions required by Matrix.diagonal; Matrix.diag itself needs no typeclass

/-- The diagonal part of a square matrix, retaining diagonal entries and replacing all
off-diagonal entries by zero.

Layer: Model | Concept: diagonal projection of a square matrix
Proof: (definitional construction; apply `Matrix.diagonal` to `Matrix.diag`)
Source: Mathlib `Matrix.diag` and `Matrix.diagonal` from finite-dimensional matrix algebra
Used in: diagonal adaptive-matrix accumulator updates that retain coordinatewise Gram information while discarding off-diagonal correlations
Book citation: book/research/Source.json#/additional_algorithm_specs/1/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 -/
def diagonalPart {ι : Type u} {R : Type v} [DecidableEq ι] [Zero R]
    (A : Matrix ι ι R) : Matrix ι ι R :=
  diagonal (diag A)

/-- Unfolding rule for the diagonal-part projection. -/
@[simp]
theorem diagonalPart_def {ι : Type u} {R : Type v} [DecidableEq ι] [Zero R]
    (A : Matrix ι ι R) :
    diagonalPart A = diagonal (diag A) :=
  rfl

/-- The diagonal-part projection agrees with the input on the diagonal and is zero
off the diagonal.

Layer: Model | Gap: Level 0 (entrywise characterization of the diagonal-part projection)
Proof: by rfl after unfolding `Matrix.diagonalPart`, `Matrix.diag`, and `Matrix.diagonal`.
Source: Mathlib `Matrix.diagonal_apply` and `Matrix.diag_apply` entry formulas
Used in: positivity, summation, and coordinatewise accumulator calculations for diagonal adaptive-matrix preconditioners
Book citation: book/research/Source.json#/additional_algorithm_specs/1/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 -/
@[simp]
theorem diagonalPart_apply {ι : Type u} {R : Type v} [DecidableEq ι] [Zero R]
    (A : Matrix ι ι R) (i j : ι) :
    diagonalPart A i j = if i = j then A i i else 0 := by
  rfl

/-- The diagonal part of the zero matrix is zero.

Layer: Model | Gap: Level 0 (diagonal-part projection of zero)
Proof: extensionality followed by the entrywise specification of `Matrix.diagonalPart`.
Source: Mathlib matrix zero entries and `Matrix.diagonal_apply`
Used in: masked diagonal accumulator sums where inactive stochastic-gradient updates reduce to zero matrices
Book citation: book/research/Source.json#/additional_algorithm_specs/1/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 -/
@[simp]
theorem diagonalPart_zero {ι : Type u} {R : Type v} [DecidableEq ι] [Zero R] :
    diagonalPart (0 : Matrix ι ι R) = 0 := by
  simp

end Matrix


open scoped BigOperators

section TensorModeProductsPrivate

universe u v w

-- Generalization plan (G0):
-- concept/name: reproduction by the product Kronecker-delta kernel on a finite
--   dependent product; orig was `multiIndex_delta_sum_eq`
-- generality used: an arbitrary finite decidable coordinate index type, finite dependent
--   coordinate types with decidable equality, and an arbitrary commutative
--   semiring codomain; no tensor dimensions, order, topology, measure,
--   convexity, oracle, or algorithm data
-- portable call pattern: finite tensor-coordinate expansions and categorical
--   product kernels collapse a sum onto a selected multi-index while changing
--   the dependent coordinate family, selected index, coefficient semiring, and
--   function being reproduced
-- counterargument checked: Mathlib has the one-index `Finset.sum_boole_mul`,
--   and the staged selected-coordinate contraction handles one projection, but
--   neither packages the support argument for a product of coordinate deltas
--   on a dependent function type
-- coverage search: searches for `finite dependent product Kronecker delta sum
--   reproduces function selected multi-index`, `sum product if coordinates
--   equal one zero multiply function equals function`, and `sum over functions
--   of product of Kronecker deltas times F` found Mathlib's
--   `Finset.sum_boole_mul`, `Fintype.sum_ite_eq`, and `Fintype.sum_ite_eq'`, plus
--   staged `Fintype.sum_selected_pi_kroneckerDelta_mul`; all are partial, with
--   no full dependent-product delta-kernel theorem
-- minimal hypotheses: `Fintype` instances make finite products and coordinate
--   enumerations; index `DecidableEq` constructs the dependent-function
--   `Fintype`, coordinate `DecidableEq` instances form the delta factors, and
--   `CommSemiring` supplies the commutative finite product and its absorbing zero

/-- A product of coordinate Kronecker deltas reproduces a function at the
selected point of a finite dependent product.

Layer: Glue | Gap: Level 1 (finite dependent-product delta-kernel reproduction)
Proof: isolate the selected dependent function with `Finset.sum_eq_single`; any
  other function differs in one coordinate, whose zero delta factor annihilates
  the finite product by `Finset.prod_eq_zero`.
Source: Mathlib finite products and sums, especially `Finset.sum_eq_single` and
  `Finset.prod_eq_zero` for semiring-valued big operators
Used in: tensor mode-product coordinate expansions where the identity kernel on
  all modes collapses the base-case multi-index sum to the original tensor entry
Book citation: book/research/Source.json#/key_lemmas/12
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 2 -/
private theorem Fintype.sum_pi_kronecker_delta_mul
    {ι : Type u} {R : Type w} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    {dims : ι → Type v} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (idx : ∀ i, dims i) (F : (∀ i, dims i) → R) :
    (∑ j : ∀ i, dims i,
        (∏ i : ι, if j i = idx i then (1 : R) else 0) * F j) = F idx := by
  classical
  calc
    (∑ j : ∀ i, dims i,
        (∏ i : ι, if j i = idx i then (1 : R) else 0) * F j) =
        (∏ i : ι, if idx i = idx i then (1 : R) else 0) * F idx := by
          refine Finset.sum_eq_single
            (s := (Finset.univ : Finset (∀ i, dims i))) (a := idx)
            (f := fun j : ∀ i, dims i =>
              (∏ i : ι, if j i = idx i then (1 : R) else 0) * F j) ?_ ?_
          · intro j _hj hne
            have hcoord : ∃ i : ι, j i ≠ idx i := by
              by_contra h
              apply hne
              funext i
              exact of_not_not (by intro hij; exact h ⟨i, hij⟩)
            obtain ⟨i, hi⟩ := hcoord
            have hfactor : (if j i = idx i then (1 : R) else 0) = 0 := by
              simp [hi]
            have hprod :
                (∏ i : ι, if j i = idx i then (1 : R) else 0) = 0 := by
              exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor
            simp [hprod]
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ idx))
    _ = F idx := by
      simp


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted selected-coordinate Kronecker-delta collapse on a
--   finite dependent product; orig was `multiIndex_selected_delta_sum`
-- generality used: an arbitrary finite index type, finite dependent coordinate
--   types with decidable equality, and an arbitrary non-associative semiring
--   codomain; no tensor
--   dimensions, order, topology, measure, convexity, oracle, or algorithm data
-- portable call pattern: tensor contractions, block-coordinate expansions, and
--   finite-state kernels sum over a selected coordinate and then collapse its
--   equality indicator, while changing the dependent family, selected coordinate,
--   scalar weights, and residual summand
-- counterargument checked: the result is short after sum interchange, but it is
--   not a pure rename: Mathlib only supplies the inner singleton-sum collapse,
--   and the existing tensor-index split theorem does not package the weighted
--   delta contraction that callers otherwise rederive
-- coverage search: searches for `finite sum selected coordinate kronecker delta
--   dependent function equals coordinate weight`, `sum if function coordinate
--   equals selected value multiply`, and `Fintype sum ite equality selected term
--   semiring` found Mathlib's `Fintype.sum_ite_eq` and
--   `Fintype.sum_ite_eq'` as proof ingredients and SOptLib's staged
--   `sum_tensorIndex_eq_sum_mode_coordinate_complement` as a reindexing result,
--   but no declaration with this weighted dependent-product conclusion
-- minimal hypotheses: finiteness and decidable equality on the outer index
--   construct the finite dependent function space; coordinate decidable equality
--   forms the indicator; `NonAssocSemiring` supplies zero, one, finite addition,
--   multiplication, and distributivity, with no use of multiplicative
--   associativity or commutativity

/-- Summing a weighted selected-coordinate Kronecker delta over a finite dependent
product weights every dependent index by its selected coordinate.

Layer: Glue | Gap: Level 1 (weighted selected-coordinate delta contraction)
Proof: distribute the outer weights through the dependent-index sums, interchange
  the two finite sums, and collapse the selected-coordinate sum with Mathlib's
  finite singleton-sum simplification.
Source: Mathlib finite big-operator distributivity, `Finset.sum_comm`, and
  `Fintype.sum_ite_eq'` for equality-selected finite sums
Used in: tensor mode-product and block-coordinate expansions where a selected
  coordinate indicator is contracted before the remaining dependent-index sum
Book citation: book/research/Source.json#/key_lemmas/12
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 2 -/
private theorem tensorsPrivate_sum_selected_pi_kroneckerDelta_mul
    {ι : Type u} {R : Type w} [Fintype ι] [DecidableEq ι] [NonAssocSemiring R]
    {dims : ι → Type v} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (i : ι) (c : dims i → R) (B : (∀ j, dims j) → R) :
    (∑ s : dims i,
        c s * ∑ j : ∀ j, dims j, (if j i = s then (1 : R) else 0) * B j) =
      ∑ j : ∀ j, dims j, c (j i) * B j := by
  classical
  calc
    (∑ s : dims i,
        c s * ∑ j : ∀ j, dims j, (if j i = s then (1 : R) else 0) * B j) =
        ∑ s : dims i, ∑ j : ∀ j, dims j,
          c s * ((if j i = s then (1 : R) else 0) * B j) := by
            simp_rw [Finset.mul_sum]
    _ = ∑ j : ∀ j, dims j, ∑ s : dims i,
          c s * ((if j i = s then (1 : R) else 0) * B j) := by
            rw [Finset.sum_comm]
    _ = ∑ j : ∀ j, dims j, c (j i) * B j := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [eq_comm]

end TensorModeProductsPrivate

open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: multiplication of a tensor by a square matrix in one selected mode;
--   orig was tensorModeProduct and already used the standard mathematical name
-- generality used: an arbitrary mode type with decidable equality, arbitrary
--   mode-dependent coordinate types whose selected coordinate is finite, and coefficients
--   with commutative finite addition and multiplication;
--   no finiteness of the mode type, topology, measure, or optimization assumptions
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning, and tensor
--   decomposition algorithms apply a changing mode matrix to a tensor while the mode family,
--   shape, coefficient semiring, tensor, selected mode, and matrix all change
-- counterargument checked: this is a single coordinate formula, but it is the standard named
--   mode product rather than paper bookkeeping, and its matricization multiplication law gives
--   it stable API value beyond an inline caller expression
-- coverage search: symbol searches for "tensor mode product square matrix coordinate finite
--   sum selected mode" and "tensor mode product matricization matrix multiplication" found
--   only the Shampoo-local definition and the complementary staged matricization API; Mathlib
--   semantic search returned algebraic tensor-product and Holor operations but no mode product
-- minimal hypotheses: DecidableEq on modes is required by the dependent coordinate update,
--   only the selected coordinate type is finite for the contracted sum, AddCommMonoid supplies
--   finite addition, and Mul supplies the contraction products; the mode type itself and all
--   unselected coordinate types need not be finite

/-- Multiply a tensor by a square matrix along one selected mode, contracting the matrix's
column coordinate against that tensor coordinate while leaving every other coordinate fixed.

Layer: Model | Concept: selected-mode tensor--matrix product
Proof: (definitional construction; finite coordinate contraction after a dependent conditional update of the selected tensor mode)
Source: Mathlib finite sums, function-valued matrices, and dependent equality transport for coordinate replacement
Used in: tensor adaptive-gradient and multilinear preconditioning steps that successively apply mode-specific matrix powers to a gradient tensor
Book citation: book/research/Source.json#/definitions/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorModeProduct
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v}
    {R : Type w} [AddCommMonoid R] [Mul R] (A : TensorSpace dims R) (i : ι)
    [Fintype (dims i)]
    (M : Matrix (dims i) (dims i) R) : TensorSpace dims R :=
  fun idx =>
    ∑ s : dims i, M ((Equiv.piSplitAt i dims idx).1) s *
      A ((Equiv.piSplitAt i dims).symm (s, (Equiv.piSplitAt i dims idx).2))

/-- A coordinate of a selected-mode tensor--matrix product is the finite contraction over the
selected input coordinate, with all complementary coordinates unchanged.

Layer: Model | Gap: Level 0 (entrywise specification of a selected-mode tensor--matrix product)
Proof: by rfl after unfolding `tensorModeProduct`
Source: Mathlib finite sums and dependent equality transport
Used in: entrywise expansions of successive mode preconditioners and flattened Kronecker actions on tensor gradients
Book citation: book/research/Source.json#/definitions/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeProduct_def
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v}
    {R : Type w} [AddCommMonoid R] [Mul R] (A : TensorSpace dims R) (i : ι)
    [Fintype (dims i)]
    (M : Matrix (dims i) (dims i) R) (idx : TensorIndex dims) :
    tensorModeProduct A i M idx =
      ∑ s : dims i, M ((Equiv.piSplitAt i dims idx).1) s *
        A ((Equiv.piSplitAt i dims).symm (s, (Equiv.piSplitAt i dims idx).2)) := by
  rfl

/-- For natural-number tensor shapes, mode-product coordinates use `Fin.cast` to replace the
selected coordinate and leave all other coordinates fixed.

Layer: Model | Gap: Level 0 (finite-shape coordinate specification of a tensor--matrix mode product)
Proof: expand `tensorModeProduct`; extensionality and proof irrelevance identify dependent equality transport with `Fin.cast`
Source: Mathlib's `Fin.cast`, finite sums, and dependent equality transport
Used in: finite-dimensional tensor adaptive-gradient recurrences whose coordinate proofs expose shape-index casts while expanding successive mode products
Book citation: book/research/Source.json#/definitions/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeProduct_apply_fin
    {ι : Type u} [DecidableEq ι] {dims : ι → ℕ}
    {R : Type w} [AddCommMonoid R] [Mul R]
    (A : TensorSpace (fun j => Fin (dims j)) R) (i : ι)
    (M : Matrix (Fin (dims i)) (Fin (dims i)) R)
    (idx : TensorIndex (fun j => Fin (dims j))) :
    tensorModeProduct A i M idx =
      ∑ s : Fin (dims i), M (idx i) s *
        A (fun j => if h : j = i then Fin.cast (by rw [h]) s else idx j) := by
  rw [tensorModeProduct_def]
  apply Finset.sum_congr rfl
  intro s _hs
  apply congrArg (fun z : R => M (idx i) s * z)
  apply congrArg A
  funext j
  by_cases hji : j = i
  · subst j
    rfl
  · simp [hji]

/-- Applying a finite-shape mode product to an index reassembled from a matricization row and
column contracts over replacement rows while preserving that column.

Layer: Model | Gap: Level 0 (finite-shape mode-product coordinate in matricized indices)
Proof: expand the finite-shape coordinate formula, then use function extensionality and the selected/complement branches of `Equiv.piSplitAt`
Source: Mathlib matrix coordinate sums, `Fin.cast`, and `Equiv.piSplitAt` inverse evaluation
Used in: matricization proofs that turn entrywise tensor mode products into ordinary matrix multiplication
Book citation: book/research/Source.json#/definitions/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeProduct_apply_piSplitAt_fin
    {ι : Type u} [DecidableEq ι] {dims : ι → ℕ}
    {R : Type w} [AddCommMonoid R] [Mul R]
    (A : TensorSpace (fun j => Fin (dims j)) R) (i : ι)
    (M : Matrix (Fin (dims i)) (Fin (dims i)) R) (row : Fin (dims i))
    (col : TensorModeColumn (fun j => Fin (dims j)) i) :
    tensorModeProduct A i M
        ((Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) =
      ∑ s : Fin (dims i), M row s *
        A ((Equiv.piSplitAt i (fun j => Fin (dims j))).symm (s, col)) := by
  rw [tensorModeProduct_apply_fin]
  rw [show (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col) i = row by
    simp [Equiv.piSplitAt]]
  apply Finset.sum_congr rfl
  intro s _hs
  apply congrArg (fun z : R => M row s * z)
  apply congrArg A
  funext j
  by_cases hji : j = i
  · subst j
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, hji]

/-- Matricizing a selected-mode tensor--matrix product at that same mode turns the operation
into ordinary matrix multiplication.

Layer: Model | Gap: Level 1 (mode-product compatibility with tensor matricization)
Proof: extensionality reduces the matrix identity to one entry; the split-coordinate inverse laws identify the finite contraction with `Matrix.mul_apply`
Source: Mathlib matrix multiplication and `Equiv.piSplitAt` inverse laws for dependent products
Used in: tensor Shampoo rank and Kronecker-preconditioning arguments that translate mode-wise tensor updates into matrix algebra
Book citation: book/research/Source.json#/definitions/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorMatricization_tensorModeProduct
    {ι : Type u} [DecidableEq ι] {dims : ι → Type v}
    {R : Type w} [AddCommMonoid R] [Mul R] (A : TensorSpace dims R) (i : ι)
    [Fintype (dims i)]
    (M : Matrix (dims i) (dims i) R) :
    tensorMatricization (tensorModeProduct A i M) i = M * tensorMatricization A i := by
  ext row col
  simp [tensorModeProduct_def, tensorMatricization, Matrix.mul_apply]

end SOptLib


namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: ordered prefix of modewise tensor--matrix products, named
--   `tensorModeProductsPrefix`; orig was `tensorModeProductsNat`
-- generality used: arbitrary mode-dependent coordinate types and coefficient type;
--   every coordinate type is finite, while coefficients need only commutative finite
--   addition and multiplication; no topology, measure, or optimization assumptions
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning, and
--   tensor decomposition algorithms successively apply a changing family of mode matrices
--   while the tensor shape, coefficient type, input tensor, matrix family, and prefix vary
-- counterargument checked: this is not a caller-side alias or a one-call wrapper: it is the
--   canonical bounded recursion that records the order and saturation behavior of successive
--   mode products, and its zero/successor equations form a reusable induction API
-- coverage search: symbol searches for "tensor successive mode products prefix natural
--   recursion matrices" and "prefix fold applying indexed operations until bound then
--   constant" found no covering Mathlib or SOptLib declaration; Mathlib semantic search for
--   successive mode multiplication returned tensor-power and Holor products with different
--   objects and contracts, while `SOptLib.tensorModeProduct` covers only one selected mode
-- minimal hypotheses: `Fintype (dims i)` is needed for the contraction at every mode that
--   can occur in the prefix; `AddCommMonoid R` and `Mul R` are exactly the algebra used by
--   each mode product, and no `DecidableEq` on coordinate types or semiring laws are needed

/-- Apply the matrices for tensor modes `0, ..., q - 1` successively, with prefixes beyond
the number of modes remaining constant.

Layer: Model | Concept: ordered prefix of modewise tensor--matrix products
Proof: (definitional construction; bounded natural recursion applies `tensorModeProduct` at the next finite mode and leaves out-of-range prefixes unchanged)
Source: Mathlib natural-number recursion and finite dependent indices, composed with `SOptLib.tensorModeProduct`
Used in: tensor adaptive-gradient and multilinear preconditioning steps that build a preconditioned tensor by successively applying each mode-specific matrix
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorModeProductsPrefix
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R) :
    Nat → TensorSpace dims R
  | 0 => A
  | q + 1 =>
      if hq : q < k then
        tensorModeProduct (tensorModeProductsPrefix A M q) ⟨q, hq⟩ (M ⟨q, hq⟩)
      else
        tensorModeProductsPrefix A M q

/-- The empty prefix of successive tensor mode products is the input tensor.

Layer: Model | Gap: Level 0 (base equation for an ordered prefix of tensor mode products)
Proof: by rfl after unfolding `tensorModeProductsPrefix` at zero
Source: Mathlib natural-number recursion through `SOptLib.tensorModeProductsPrefix`
Used in: base cases of inductions over successive modewise tensor preconditioners
Book citation: book/research/Source.json#/algorithm_spec/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeProductsPrefix_zero
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R) :
    tensorModeProductsPrefix A M 0 = A := by
  rfl

/-- Extending a prefix applies the next mode matrix when that mode exists and otherwise
leaves the accumulated tensor unchanged.

Layer: Model | Gap: Level 0 (successor equation for an ordered prefix of tensor mode products)
Proof: by rfl after unfolding `tensorModeProductsPrefix` at a successor
Source: Mathlib natural-number recursion and finite index construction through `SOptLib.tensorModeProduct`
Used in: inductive expansions of tensor preconditioners and coordinate formulas for flattened Kronecker actions
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeProductsPrefix_succ
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R)
    (q : Nat) :
    tensorModeProductsPrefix A M (q + 1) =
      if hq : q < k then
        tensorModeProduct (tensorModeProductsPrefix A M q) ⟨q, hq⟩ (M ⟨q, hq⟩)
      else
        tensorModeProductsPrefix A M q := by
  rfl

/-- Once every tensor mode has been processed, extending the prefix leaves the result
unchanged.

Layer: Model | Gap: Level 0 (saturation of an ordered prefix of tensor mode products)
Proof: write the longer prefix as the number of modes plus an offset and induct on the
  offset; every additional recursion step takes the out-of-range branch
Source: Mathlib natural-number addition and induction through
  `SOptLib.tensorModeProductsPrefix_succ`
Used in: replacing overlong or externally specified tensor-preconditioning loop bounds by
  the tensor's actual number of modes
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Algorithm 2 -/
theorem tensorModeProductsPrefix_eq_length_of_le
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R)
    {q : Nat} (hq : k ≤ q) :
    tensorModeProductsPrefix A M q = tensorModeProductsPrefix A M k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ, tensorModeProductsPrefix_succ]
      simp only [Nat.not_lt.mpr (Nat.le_add_right k n), dite_false]
      exact ih (Nat.le_add_right k n)

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: coordinate expansion of an ordered prefix of modewise tensor--matrix
--   products, named `tensorModeProductsPrefix_apply`; orig was
--   `tensorModeProductsNat_coord_prefix`
-- generality used: arbitrary finite mode-dependent coordinate types and an arbitrary
--   commutative semiring of coefficients; no topology, measure, optimization, or
--   finite-dimensional vector-space assumptions
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning, and tensor
--   decomposition proofs expand a changing prefix of mode operators while the tensor shape,
--   coefficient semiring, matrices, input tensor, output coordinate, and prefix length vary
-- counterargument checked: the statement is not paper traceability or a one-call wrapper;
--   it composes the recursive mode-product API with a nontrivial dependent-index contraction
--   and exposes the reusable kernel of processed matrix entries and unprocessed deltas
-- coverage search: symbol searches for "tensor mode products prefix coordinate expansion
--   matrices unprocessed coordinate delta" and "successive modewise tensor matrix product
--   coordinate sum prefix" found only the staged one-mode and prefix-recursion APIs;
--   Mathlib semantic searches returned Kronecker and abstract tensor-product coordinate laws,
--   but no theorem for successive mode products on dependent function tensors
-- minimal hypotheses: coordinate `Fintype` instances support all contractions and coordinate
--   `DecidableEq` instances form the unprocessed Kronecker deltas; `CommSemiring` supplies the
--   finite sums/products, distributivity, and factor rearrangements used by the expansion

/-- A coordinate of a prefix of successive tensor mode products is the sum over input
multi-indices of the processed matrix entries, identity deltas on unprocessed modes, and the
input tensor coordinate.

Layer: Model | Gap: Level 2 (coordinate kernel for an ordered prefix of tensor mode products)
Proof: induct on the prefix length; expand the next mode contraction, isolate its selected
  coordinate in the finite product, and collapse the resulting Kronecker delta sum.
Source: Mathlib finite dependent-function sums and products, together with
  `SOptLib.tensorModeProduct_def`, `Fintype.sum_pi_kronecker_delta_mul`, and
  `Fintype.sum_selected_pi_kroneckerDelta_mul`
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that identify a
  sequential family of mode matrices with its entrywise multi-index contraction kernel
Book citation: book/research/Source.json#/definitions/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorModeProductsPrefix_apply
    {k : Nat} {dims : Fin k → Type u} {R : Type v} [CommSemiring R]
    [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (G : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R) :
    ∀ q (idx : TensorIndex dims), q ≤ k →
      tensorModeProductsPrefix G M q idx =
        ∑ j : TensorIndex dims,
          ((∏ i : Fin k,
              if i.1 < q then M i (idx i) (j i)
              else if j i = idx i then (1 : R) else 0) * G j) := by
  classical
  have prod_split (i : Fin k) (f : Fin k → R) :
      (∏ j : Fin k, f j) = f i * ∏ j : {j : Fin k // j ≠ i}, f j.1 := by
    have hcompl :
        (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j) =
          ∏ j : {j : Fin k // j ≠ i}, f j.1 := by
      exact Finset.prod_subtype ((Finset.univ : Finset (Fin k)).erase i)
        (by intro j; simp) f
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) f
      (Finset.mem_univ i), hcompl]
  intro q
  induction q with
  | zero =>
      intro idx _hq
      simpa using (Fintype.sum_pi_kronecker_delta_mul idx G).symm
  | succ q ih =>
      intro idx hsucc
      have hq : q < k := Nat.lt_of_succ_le hsucc
      have hqle : q ≤ k := Nat.le_of_lt hq
      let qFin : Fin k := ⟨q, hq⟩
      let replacement (s : dims qFin) : TensorIndex dims :=
        (Equiv.piSplitAt qFin dims).symm
          (s, (Equiv.piSplitAt qFin dims idx).2)
      let Bprod : TensorIndex dims → R := fun j =>
        ∏ i : Fin k,
          if i.1 < q then M i (idx i) (j i)
          else if i = qFin then (1 : R)
          else if j i = idx i then (1 : R) else 0
      have hreplace : ∀ s : dims qFin, ∀ j : TensorIndex dims,
          (∏ i : Fin k,
              if i.1 < q then M i (replacement s i) (j i)
              else if j i = replacement s i then (1 : R) else 0) =
            (if j qFin = s then (1 : R) else 0) * Bprod j := by
        intro s j
        rw [prod_split qFin
          (fun i : Fin k =>
            if i.1 < q then M i (replacement s i) (j i)
            else if j i = replacement s i then (1 : R) else 0)]
        dsimp only [Bprod]
        rw [prod_split qFin
          (fun i : Fin k =>
            if i.1 < q then M i (idx i) (j i)
            else if i = qFin then (1 : R)
            else if j i = idx i then (1 : R) else 0)]
        have hprod :
            (∏ x : {i : Fin k // i ≠ qFin},
                if x.1.1 < q then M x.1 (replacement s x.1) (j x.1)
                else if j x.1 = replacement s x.1 then (1 : R) else 0) =
              ∏ x : {i : Fin k // i ≠ qFin},
                if x.1.1 < q then M x.1 (idx x.1) (j x.1)
                else if x.1 = qFin then (1 : R)
                else if j x.1 = idx x.1 then (1 : R) else 0 := by
          apply Finset.prod_congr rfl
          intro x _hx
          simp [replacement, Equiv.piSplitAt, x.property]
        rw [hprod]
        simp [qFin, replacement, Equiv.piSplitAt]
      have hsuccprod : ∀ j : TensorIndex dims,
          (∏ i : Fin k,
              if i.1 ≤ q then M i (idx i) (j i)
              else if j i = idx i then (1 : R) else 0) =
            M qFin (idx qFin) (j qFin) * Bprod j := by
        intro j
        rw [prod_split qFin
          (fun i : Fin k =>
            if i.1 ≤ q then M i (idx i) (j i)
            else if j i = idx i then (1 : R) else 0)]
        dsimp only [Bprod]
        rw [prod_split qFin
          (fun i : Fin k =>
            if i.1 < q then M i (idx i) (j i)
            else if i = qFin then (1 : R)
            else if j i = idx i then (1 : R) else 0)]
        have hprod :
            (∏ x : {i : Fin k // i ≠ qFin},
                if x.1.1 ≤ q then M x.1 (idx x.1) (j x.1)
                else if j x.1 = idx x.1 then (1 : R) else 0) =
              ∏ x : {i : Fin k // i ≠ qFin},
                if x.1.1 < q then M x.1 (idx x.1) (j x.1)
                else if x.1 = qFin then (1 : R)
                else if j x.1 = idx x.1 then (1 : R) else 0 := by
          apply Finset.prod_congr rfl
          intro x _hx
          have hle_iff_lt : x.1.1 ≤ q ↔ x.1.1 < q := by
            constructor
            · intro hxle
              exact Nat.lt_of_le_of_ne hxle (by
                intro hval
                apply x.property
                apply Fin.ext
                exact hval)
            · exact Nat.le_of_lt
          simp [propext hle_iff_lt, x.property]
        rw [hprod]
        simp [qFin]
      rw [tensorModeProductsPrefix_succ]
      simp only [hq, dite_true]
      rw [tensorModeProduct_def]
      have hrow : (Equiv.piSplitAt qFin dims idx).1 = idx qFin := by
        simp [Equiv.piSplitAt]
      rw [hrow]
      simp_rw [ih _ hqle]
      change
        (∑ s : dims qFin,
            M qFin (idx qFin) s *
              ∑ j : TensorIndex dims,
                (∏ i : Fin k,
                    if i.1 < q then M i (replacement s i) (j i)
                    else if j i = replacement s i then (1 : R) else 0) * G j) = _
      calc
        (∑ s : dims qFin,
            M qFin (idx qFin) s *
              ∑ j : TensorIndex dims,
                (∏ i : Fin k,
                    if i.1 < q then M i (replacement s i) (j i)
                    else if j i = replacement s i then (1 : R) else 0) * G j) =
            ∑ s : dims qFin,
              M qFin (idx qFin) s *
                ∑ j : TensorIndex dims,
                  (if j qFin = s then (1 : R) else 0) * (Bprod j * G j) := by
              apply Finset.sum_congr rfl
              intro s _hs
              congr 1
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hreplace s j]
              ring
        _ = ∑ j : TensorIndex dims,
              M qFin (idx qFin) (j qFin) * (Bprod j * G j) := by
              simpa using tensorsPrivate_sum_selected_pi_kroneckerDelta_mul qFin
                (fun s : dims qFin => M qFin (idx qFin) s)
                (fun j : TensorIndex dims => Bprod j * G j)
        _ = ∑ j : TensorIndex dims,
              (∏ i : Fin k,
                  if i.1 ≤ q then M i (idx i) (j i)
                  else if j i = idx i then (1 : R) else 0) * G j := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hsuccprod j]
              ring
        _ = ∑ j : TensorIndex dims,
              (∏ i : Fin k,
                  if i.1 < q + 1 then M i (idx i) (j i)
                  else if j i = idx i then (1 : R) else 0) * G j := by
              simp only [Nat.lt_succ_iff]

end SOptLib


namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: full ordered family of modewise tensor--matrix products, named
--   `tensorModeProducts`; the original name already exposes the standard operation
-- generality used: arbitrary mode-dependent finite coordinate types and an arbitrary
--   coefficient type with commutative finite addition and multiplication; no topology,
--   measure, optimization, or decidable-equality assumptions
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning, and tensor
--   decomposition algorithms apply one operator at every mode while the tensor shape,
--   coefficient type, input tensor, and modewise operator family change
-- counterargument checked: although the construction is the terminal value of the prefix
--   recursion, it is the canonical full multilinear action used by callers; naming it hides
--   the recursion bound and supplies a stable endpoint for Kronecker--vectorization bridges
-- coverage search: symbol searches for "apply matrices along every tensor mode ordered
--   modewise products" and "tensor mode products full prefix length" found no covering
--   Mathlib or SOptLib declaration; Mathlib semantic search returned algebraic
--   `PiTensorProduct.map` operations on a different tensor representation, while
--   `SOptLib.tensorModeProduct` and `SOptLib.tensorModeProductsPrefix` cover only one mode
--   and a caller-selected prefix, respectively
-- minimal hypotheses: `Fintype (dims i)` supplies each finite contraction;
--   `AddCommMonoid R` and `Mul R` are exactly the algebra used by the underlying mode
--   products, so neither `CommSemiring R` nor `DecidableEq (dims i)` is required

/-- Apply a square matrix along every mode of a tensor, successively in finite-mode order.

Layer: Model | Concept: full ordered family of modewise tensor--matrix products
Proof: (definitional construction; evaluate `SOptLib.tensorModeProductsPrefix` at the number of tensor modes)
Source: Mathlib finite dependent indices and natural-number recursion, composed with `SOptLib.tensorModeProductsPrefix`
Used in: tensor adaptive-gradient and multilinear preconditioning steps that transform a gradient by every mode-specific preconditioner before the iterate update
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorModeProducts
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R) :
    TensorSpace dims R :=
  tensorModeProductsPrefix A M k

/-- Applying all mode matrices is the ordered prefix evaluated at the number of modes.

Layer: Model | Gap: Level 0 (defining equation for the full ordered modewise tensor action)
Proof: by rfl after unfolding `tensorModeProducts`
Source: The defining equation of `SOptLib.tensorModeProducts` over Mathlib finite dependent indices
Used in: unfolding a fully mode-preconditioned tensor into the prefix recursion for induction and entrywise Kronecker--vectorization proofs
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeProducts_def
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R) :
    tensorModeProducts A M = tensorModeProductsPrefix A M k := by
  rfl

/-- Every prefix that has processed at least the number of tensor modes is the full
modewise product.

Layer: Model | Gap: Level 1 (bridge from saturated prefixes to the named full action)
Proof: combine prefix saturation with the defining equation of `tensorModeProducts`
Source: `SOptLib.tensorModeProductsPrefix_eq_length_of_le` and the defining equation of
  `SOptLib.tensorModeProducts`
Used in: replacing externally bounded tensor-preconditioning loops by the canonical full
  multilinear action once every mode has been processed
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Algorithm 2 -/
theorem tensorModeProductsPrefix_eq_tensorModeProducts_of_le
    {k : Nat} {dims : Fin k → Type u} {R : Type v}
    [AddCommMonoid R] [Mul R] [∀ i, Fintype (dims i)]
    (A : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R)
    {q : Nat} (hq : k ≤ q) :
    tensorModeProductsPrefix A M q = tensorModeProducts A M := by
  rw [tensorModeProducts_def]
  exact tensorModeProductsPrefix_eq_length_of_le A M hq

end SOptLib


namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: dependent finite-family Kronecker action on a tensor vectorization,
--   named `tensorKronecker_mulVec_tensorVectorization`; orig was
--   `Lemma_12_tensor_kron_vec`
-- generality used: a natural-number-indexed finite family of arbitrary finite coordinate
--   types and coefficients in an arbitrary commutative semiring; no topology, measure,
--   order, vector-space structure, or positivity assumptions are used
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning, and tensor
--   decomposition proofs replace a sequence of modewise matrix actions by one flattened
--   Kronecker matrix action while the tensor shape, scalar semiring, tensor, and matrix
--   family change
-- counterargument checked: Mathlib's binary `Matrix.kronecker_mulVec_vec` handles a
--   two-factor ordinary matrix vectorization, but does not cover a dependent finite family
--   or its equality with successive tensor mode products; this theorem is the missing
--   representation bridge rather than a paper-local rename or caller-side expression
-- coverage search: symbol queries for "dependent tensor Kronecker mulVec equals successive
--   modewise matrix products" and "tensorKronecker mulVec tensorModeProducts equality
--   CommSemiring" found only the component definitions and prefix-coordinate theorem;
--   Mathlib semantic search found `Matrix.kronecker_mulVec_vec`, which is binary and uses
--   ordinary matrix vectorization, so coverage is partial
-- minimal hypotheses: `CommSemiring R` supplies the finite sum/product rearrangement in the
--   coordinate expansion, and `Fintype` for each coordinate type supports contraction sums;
--   the proof obtains decidable equality locally via `classical`

/-- Multiplying a tensor vectorization by the dependent Kronecker product of its mode
matrices equals vectorizing the result of applying those matrices successively by mode.

Layer: Model | Gap: Level 1 (dependent Kronecker action to successive mode products)
Proof: expand the full ordered mode action with `tensorModeProductsPrefix_apply`; after all
  modes are processed, simplify its kernel to the entrywise `Matrix.mulVec` contraction.
Source: Mathlib finite dependent-function sums, matrix-vector multiplication, and finite
  products, together with `SOptLib.tensorModeProductsPrefix_apply`
Used in: tensor adaptive-gradient and multilinear preconditioning updates that turn a
  mode-by-mode preconditioned gradient into one flattened Kronecker-preconditioned vector
Book citation: book/research/Source.json#/key_lemmas/12
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_mulVec_tensorVectorization
    {k : Nat} {R : Type v} [CommSemiring R]
    {dims : Fin k → Type u} [∀ i, Fintype (dims i)]
    (G : TensorSpace dims R) (M : (i : Fin k) → Matrix (dims i) (dims i) R) :
    (tensorKronecker M).mulVec G = tensorModeProducts G M := by
  classical
  ext idx
  have hprefix := tensorModeProductsPrefix_apply G M k idx le_rfl
  change Matrix.mulVec (tensorKronecker M) G idx = tensorModeProductsPrefix G M k idx
  rw [hprefix]
  simp [Matrix.mulVec, tensorKronecker, dotProduct]

end SOptLib

namespace TensorsProofSupport

universe u v w

open _root_.Matrix


open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: Loewner domination of a real self outer product by the identity
--   from a unit squared Euclidean norm bound; orig was
--   `vectorOuter_le_one_of_sum_sq_le_one`, renamed
--   `Matrix.vecMulVec_le_one_of_sum_sq_le_one`
-- generality used: arbitrary finite coordinate type with decidable equality and
--   a real vector; no concrete dimension, measure, convexity, smoothness,
--   oracle, or algorithm assumptions are used
-- portable call pattern: rank-one domination, covariance, normalized-feature,
--   and orthonormal-factor proofs vary the finite coordinate type and vector
--   while retaining the unit squared-norm premise and identity Loewner bound
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it packages Cauchy--Schwarz with the positive-semidefinite matrix
--   order characterization to produce a reusable rank-one operator bound
-- coverage search: symbol searches for `vector self outer product less than
--   identity of sum squares less than one` and `vecMulVec Loewner bound identity
--   squared norm` found only the private source theorem and distinct outer-sum
--   and spectral-support lemmas; Mathlib semantic searches found
--   `Matrix.posSemidef_vecMulVec_self_star`, `InnerProductSpace.norm_rankOne`,
--   and scalar Cauchy--Schwarz ingredients, but no matching Loewner upper bound
-- minimal hypotheses: `[Fintype ι]` is required for the coordinate sums and
--   matrix quadratic form, and `[DecidableEq ι]` for the identity matrix;
--   the squared-norm upper bound is the sole data hypothesis

/-- A real vector's self outer product is bounded by the identity matrix when
its sum of squared coordinates is at most one.

Layer: Glue | Gap: Level 1 (unit-vector rank-one Loewner domination)
Proof: characterize Loewner order by positive semidefiniteness and test the
  identity-minus-outer-product quadratic form; finite Cauchy--Schwarz and the
  unit squared-norm hypothesis make that form nonnegative.
Source: Mathlib positive-semidefinite matrix order and finite-sum
  Cauchy--Schwarz inequalities
Used in: rank-one matrix and tensor decomposition proofs that replace normalized
  factor self outer products by identity matrices inside monotone constructions
Book citation: book/research/Source.json#/key_lemmas/10/proof/5
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem vecMulVec_le_one_of_sum_sq_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (hu : ∑ i : ι, u i ^ 2 ≤ 1) :
    Matrix.vecMulVec u u ≤ (1 : Matrix ι ι ℝ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have houterHerm : (Matrix.vecMulVec u u).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      change star (u j * u i) = u i * u j
      simp [mul_comm]
    exact Matrix.IsHermitian.sub Matrix.isHermitian_one houterHerm
  · intro x
    have hone_mul : ((1 : Matrix ι ι ℝ).mulVec x) = x := by
      simp
    have hquad_eq :
        dotProduct (star x)
            (((1 : Matrix ι ι ℝ) - Matrix.vecMulVec u u).mulVec x) =
          (∑ i : ι, x i ^ 2) - (∑ i : ι, x i * u i) ^ 2 := by
      calc
        dotProduct (star x)
            (((1 : Matrix ι ι ℝ) - Matrix.vecMulVec u u).mulVec x) =
            dotProduct (star x)
              (((1 : Matrix ι ι ℝ).mulVec x) -
                (Matrix.vecMulVec u u).mulVec x) := by
              rw [Matrix.sub_mulVec]
        _ = dotProduct (star x) ((1 : Matrix ι ι ℝ).mulVec x) -
              dotProduct (star x) ((Matrix.vecMulVec u u).mulVec x) := by
              rw [dotProduct_sub]
        _ = (∑ i : ι, x i ^ 2) - (∑ i : ι, x i * u i) ^ 2 := by
              rw [hone_mul]
              simp [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, pow_two,
                Finset.mul_sum, Finset.sum_comm, mul_left_comm, mul_comm]
    rw [hquad_eq]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset ι)) (f := x) (g := u)
    have hx_nonneg : 0 ≤ ∑ i : ι, x i ^ 2 :=
      Finset.sum_nonneg (by intro i _hi; exact sq_nonneg (x i))
    have hu_nonneg : 0 ≤ ∑ i : ι, u i ^ 2 :=
      Finset.sum_nonneg (by intro i _hi; exact sq_nonneg (u i))
    have hmul_le :
        (∑ i : ι, x i ^ 2) * (∑ i : ι, u i ^ 2) ≤ ∑ i : ι, x i ^ 2 := by
      nlinarith
    nlinarith

end Matrix


open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: rank-many outer-product decomposition with orthonormal left
--   factors; orig was `matrix_rank_column_space_orthonormal_rank_one_expansion`
-- generality used: arbitrary finite row and column index types for a real
--   matrix, with decidable row equality for the identity-matrix bound; no
--   measure, convexity, smoothness, oracle, or algorithm assumptions are used
-- portable call pattern: low-rank covariance, sketching, factorized-gradient,
--   and preconditioner proofs vary the finite matrix and index types while
--   reusing a rank-indexed factorization with orthonormal left factors
-- counterargument checked: the staged normalized-factor decomposition is
--   weaker because it does not expose pairwise orthonormality, while Mathlib's
--   orthonormal-basis APIs do not package the matrix factorization or its bound
-- coverage search: symbol and semantic searches for `finite real matrix equals
--   sum outer products indexed by rank with orthonormal left vectors` and
--   `matrix factorization using an orthonormal basis of the column space`
--   found `OrthonormalBasis.orthogonalProjection_eq_sum_rankOne`,
--   `InnerProductSpace.toMatrix_rankOne`, and the distinct staged theorem
--   `Matrix.exists_rank_one_sum_eq_with_left_norm_le_one`; none has this
--   rank-indexed orthonormal-left matrix-factorization conclusion
-- minimal hypotheses: finiteness of both index types supports matrix rank,
--   finite coordinate sums, and the column-space orthonormal basis; decidable
--   row equality is needed only for the identity matrix in the Loewner bound

/-- Every finite real matrix is a sum of as many outer products as its rank,
with an orthonormal family of left factors whose self outer products are
bounded by the identity matrix.

Layer: Glue | Gap: Level 2 (orthonormal rank-many outer-product factorization)
Proof: choose an orthonormal basis of the Euclidean column space, expand each
  column in that basis, and derive each rank-one identity bound from the
  diagonal orthonormality equation.
Source: Mathlib matrix rank as column-map range finrank, finite-dimensional
  Euclidean orthonormal-basis expansion, and positive-semidefinite matrix order.
Used in: low-rank covariance, sketching, and matrix-preconditioner arguments
  that need both a column-space factorization and orthonormal-factor Gram laws.
Book citation: book/research/Source.json#/key_lemmas/10/proof/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem exists_rank_one_sum_eq_with_orthonormal_left
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (G : Matrix ι κ ℝ) :
    ∃ (u : Fin G.rank → ι → ℝ) (b : Fin G.rank → κ → ℝ),
      G = ∑ a : Fin G.rank, vecMulVec (u a) (b a) ∧
        (∀ a a' : Fin G.rank,
          ∑ i : ι, u a i * u a' i = if a = a' then 1 else 0) ∧
        ∀ a : Fin G.rank, vecMulVec (u a) (u a) ≤ (1 : Matrix ι ι ℝ) := by
  classical
  let L : (κ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    (((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm : (ι → ℝ) ≃ₗ[ℝ]
        EuclideanSpace ℝ ι).toLinearMap.comp (Matrix.toLin' G))
  let E := LinearMap.range L
  have hrank : Module.finrank ℝ (LinearMap.range (Matrix.toLin' G)) = G.rank := by
    change Module.finrank ℝ (LinearMap.range (Matrix.toLin' G)) =
      Module.finrank ℝ (LinearMap.range G.mulVecLin)
    rw [Matrix.toLin'_apply']
  have hfin : Module.finrank ℝ E = G.rank := by
    let e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
    calc
      Module.finrank ℝ E =
          Module.finrank ℝ (LinearMap.range (e.toLinearMap.comp (Matrix.toLin' G))) := by
            rfl
      _ = Module.finrank ℝ ((LinearMap.range (Matrix.toLin' G)).map e.toLinearMap) := by
            rw [LinearMap.range_comp]
      _ = Module.finrank ℝ (LinearMap.range (Matrix.toLin' G)) := by
            exact e.finrank_map_eq (LinearMap.range (Matrix.toLin' G))
      _ = G.rank := hrank
  let B : OrthonormalBasis (Fin G.rank) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hfin)
  have hcol (j : κ) :
      (WithLp.toLp 2 (G.col j) : EuclideanSpace ℝ ι) ∈ LinearMap.range L := by
    refine ⟨Pi.single j (1 : ℝ), ?_⟩
    change ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm)
        (Matrix.toLin' G (Pi.single j (1 : ℝ))) =
      (WithLp.toLp 2 (G.col j) : EuclideanSpace ℝ ι)
    apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
    ext i
    simp [Matrix.toLin'_apply, Matrix.col_apply]
  let u : Fin G.rank → ι → ℝ :=
    fun a i => (B a : EuclideanSpace ℝ ι) i
  let b : Fin G.rank → κ → ℝ :=
    fun a j => B.repr
      ⟨(WithLp.toLp 2 (G.col j) : EuclideanSpace ℝ ι), hcol j⟩ a
  have hG : G = ∑ a : Fin G.rank, vecMulVec (u a) (b a) := by
    ext i j
    let x : E :=
      ⟨(WithLp.toLp 2 (G.col j) : EuclideanSpace ℝ ι), hcol j⟩
    have hrepr := congr_arg (fun y : E => (y : EuclideanSpace ℝ ι) i)
      (B.sum_repr x)
    simpa [u, b, x, Matrix.sum_apply, Matrix.col_apply, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hrepr.symm
  have horth : ∀ a a' : Fin G.rank,
      ∑ i : ι, u a i * u a' i = if a = a' then 1 else 0 := by
    intro a a'
    have hinnerE :
        inner ℝ (B a : E) (B a' : E) = if a = a' then (1 : ℝ) else 0 := by
      simpa using (orthonormal_iff_ite.mp B.orthonormal a a')
    have hinnerAmbient :
        inner ℝ (B a : EuclideanSpace ℝ ι)
          (B a' : EuclideanSpace ℝ ι) = if a = a' then 1 else 0 := by
      change inner ℝ (B a : E) (B a' : E) = if a = a' then (1 : ℝ) else 0
      exact hinnerE
    have hcoords :=
      EuclideanSpace.inner_eq_star_dotProduct
        (B a : EuclideanSpace ℝ ι) (B a' : EuclideanSpace ℝ ι)
    calc
      (∑ i : ι, u a i * u a' i) =
          dotProduct (B a : EuclideanSpace ℝ ι)
            (B a' : EuclideanSpace ℝ ι) := by
              rfl
      _ = dotProduct (B a' : EuclideanSpace ℝ ι)
            (B a : EuclideanSpace ℝ ι) := by
              rw [dotProduct_comm]
      _ = dotProduct (B a' : EuclideanSpace ℝ ι)
            (star (B a : EuclideanSpace ℝ ι)) := by
              simp
      _ = inner ℝ (B a : EuclideanSpace ℝ ι)
            (B a' : EuclideanSpace ℝ ι) := hcoords.symm
      _ = if a = a' then 1 else 0 := hinnerAmbient
  refine ⟨u, b, hG, horth, ?_⟩
  intro a
  apply Matrix.vecMulVec_le_one_of_sum_sq_le_one
  have haa := horth a a
  simpa [pow_two] using haa.le

end Matrix


open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: rank-many outer-product decomposition with orthonormal right
--   factors; orig was `matrix_rank_row_space_orthonormal_rank_one_expansion`
-- generality used: arbitrary finite row and column index types for a real
--   matrix, with decidable column equality for the identity-matrix bound; no
--   measure, convexity, smoothness, oracle, or algorithm assumptions are used
-- portable call pattern: low-rank covariance, sketching, factorized-gradient,
--   and preconditioner proofs vary the finite matrix and index types while
--   reusing a rank-indexed factorization with orthonormal right factors
-- counterargument checked: although symmetric to the orthonormal-left theorem,
--   this is not a pure rename or caller-side expression; transposition changes
--   the rank index type, so the reusable result packages a nontrivial reindexing
-- coverage search: symbol and semantic searches for `finite real matrix equals
--   sum outer products indexed by rank with orthonormal right vectors` and
--   `matrix rank row space orthonormal rank one expansion right factor identity
--   bound` found `OrthonormalBasis.orthogonalProjection_eq_sum_rankOne`,
--   `InnerProductSpace.toMatrix_rankOne`, and the distinct staged theorem
--   `Matrix.exists_rank_one_sum_eq_with_orthonormal_left`; none has this
--   rank-indexed orthonormal-right matrix-factorization conclusion
-- minimal hypotheses: finiteness of both index types supports matrix rank and
--   finite coordinate sums; decidable equality on the column index is needed
--   only for the identity matrix in the right-factor Loewner bound

/-- Every finite real matrix is a sum of as many outer products as its rank,
with an orthonormal family of right factors whose self outer products are
bounded by the identity matrix.

Layer: Glue | Gap: Level 2 (right-orthonormal rank-many outer-product factorization)
Proof: apply the orthonormal-left factorization to the transposed matrix, swap
  the two factor families, and transport the sum across equality of transpose rank.
Source: Mathlib matrix transposition and rank invariance, together with the
  finite-dimensional Euclidean orthonormal-left matrix factorization.
Used in: low-rank covariance, sketching, and matrix-preconditioner arguments
  that need both a row-space factorization and orthonormal-factor Gram laws.
Book citation: book/research/Source.json#/key_lemmas/10/proof/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem exists_rank_one_sum_eq_with_orthonormal_right
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (G : Matrix ι κ ℝ) :
    ∃ (u : Fin G.rank → ι → ℝ) (b : Fin G.rank → κ → ℝ),
      G = ∑ a : Fin G.rank, vecMulVec (u a) (b a) ∧
        (∀ a a' : Fin G.rank,
          ∑ j : κ, b a j * b a' j = if a = a' then 1 else 0) ∧
        ∀ a : Fin G.rank, vecMulVec (b a) (b a) ≤ (1 : Matrix κ κ ℝ) := by
  classical
  obtain ⟨uT, bT, hGT, horthT, huboundT⟩ :=
    Matrix.exists_rank_one_sum_eq_with_orthonormal_left G.transpose
  have hrankT : G.transpose.rank = G.rank := by
    simpa using Matrix.rank_transpose G
  let e : Fin G.rank ≃ Fin G.transpose.rank := finCongr hrankT.symm
  refine ⟨fun a i => bT (e a) i, fun a j => uT (e a) j, ?_, ?_, ?_⟩
  · ext i j
    have h := congr_fun (congr_fun hGT j) i
    calc
      G i j = ∑ c : Fin G.transpose.rank, uT c j * bT c i := by
        simpa [Matrix.transpose_apply, Matrix.sum_apply] using h
      _ = ∑ a : Fin G.rank, uT (e a) j * bT (e a) i := by
        exact (Fintype.sum_equiv e
          (fun a => uT (e a) j * bT (e a) i)
          (fun c => uT c j * bT c i) (by intro a; rfl)).symm
      _ = (∑ a : Fin G.rank,
            vecMulVec (fun i => bT (e a) i) (fun j => uT (e a) j)) i j := by
        simp [Matrix.sum_apply, Matrix.vecMulVec, mul_comm]
  · intro a a'
    have h := horthT (e a) (e a')
    simpa [e.injective.eq_iff] using h
  · intro a
    exact huboundT (e a)

end Matrix


namespace Matrix


-- Generalization plan (G0):
-- concept/name: left Gram matrix, named `Matrix.leftGram`; orig was `matrixGramLeft`
-- generality used: arbitrary row and column index types and arbitrary entries with
--   multiplication and finite addition; only the contracted column index is finite
-- portable call pattern: full-matrix adaptive-gradient and tensor-matricization algorithms
--   form row Gram accumulators while changing matrix shapes, index types, and scalar rings
-- counterargument checked: the body is a short product, but left Gram matrices are a
--   recognized recurring object and the entrywise API hides transpose/multiplication plumbing
-- coverage search: searches for "matrix left Gram matrix product transpose" and
--   "Matrix.leftGram G * G.transpose" found no Mathlib/SOptLib definition; Mathlib's
--   `Matrix.gram` is only a partial hit because it uses inner products (and conjugation over
--   complex scalars), rather than the general transpose product defined here
-- minimal hypotheses: `Fintype κ`, `Mul R`, and `AddCommMonoid R` are exactly those used
--   by rectangular matrix multiplication; no finiteness on the uncontracted row index is used

/-- The left Gram matrix of a rectangular matrix, obtained by multiplying the matrix by its
transpose.

Layer: Model | Concept: left Gram matrix of a rectangular matrix
Proof: (definitional construction; rectangular matrix multiplication by the transpose)
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: row-covariance accumulator updates for full-matrix adaptive-gradient and tensor-matricization preconditioners
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
def leftGram {ι : Type u} {κ : Type v} {R : Type w} [Fintype κ] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) : Matrix ι ι R :=
  G * G.transpose

/-- The left Gram matrix unfolds to multiplication by the transpose.

Layer: Model | Gap: Level 0 (left Gram matrix unfolding rule)
Proof: by rfl after unfolding `Matrix.leftGram`.
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: rewriting row-Gram accumulator updates into the matrix products used by spectral and positive-semidefinite arguments
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem leftGram_def {ι : Type u} {κ : Type v} {R : Type w} [Fintype κ] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) :
    leftGram G = G * G.transpose :=
  rfl

end Matrix


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite orthonormal-coordinate bilinear Parseval collapse; orig
--   was `finite_orthonormal_coordinate_gram_collapse`
-- generality used: arbitrary finite coefficient and coordinate index types over
--   a commutative semiring; no matrix dimensions, finite-dimensional ambient space,
--   measure, convexity, smoothness, oracle, or algorithm assumptions are used
-- portable call pattern: low-rank matrix decompositions, orthogonal feature
--   expansions, and finite-frame calculations collapse the coordinate pairing
--   of two synthesized vectors while changing the coordinate family and both
--   coefficient vectors
-- counterargument checked: Mathlib's `Orthonormal.inner_sum` gives the abstract
--   inner-product theorem, but does not directly consume a raw coordinate Gram
--   identity or produce this transposed coordinate-sum form; this bridge avoids
--   rebuilding an `Orthonormal` family at matrix-coordinate call sites
-- coverage search: searches for `bilinear coordinate sum synthesis orthonormal
--   family equals coefficient dot product`, `finite sum product sums orthonormal
--   kronecker delta collapse`, and the corresponding Mathlib semantic query
--   found `Orthonormal.inner_sum`, `Orthonormal.inner_finsupp_eq_sum_right`, and
--   SOptLib's `norm_sq_sum_smul_orthonormalBasis`; these cover abstract or
--   quadratic Parseval forms, not the raw bilinear coordinate contract here
-- minimal hypotheses: both `Fintype` instances form the finite sums, and
--   `DecidableEq ι` is exactly what the Kronecker-delta orthonormality
--   hypothesis requires; all source-local matrix and rank parameters are absent

/-- The bilinear coordinate sum of two syntheses by a finite orthonormal family
equals the coefficient dot product.

Layer: Glue | Gap: Level 1 (raw-coordinate bilinear Parseval collapse)
Proof: distribute the two finite syntheses, commute the three finite sums, and
  replace the coordinate Gram sum by the supplied Kronecker-delta identity.
Source: Mathlib finite big-operator distributivity and finite-dimensional
  orthonormal-family Parseval identities in `Analysis.InnerProductSpace.Orthonormal`.
Used in: low-rank matrix decompositions, where orthonormal singular-vector
  coordinates collapse expanded left and right Gram matrix entries.
Book citation: book/research/Source.json#/key_lemmas/10
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem finite_orthonormal_coordinate_bilinear_collapse
    {R : Type*} [CommSemiring R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (u : ι → κ → R) (x y : ι → R)
    (horth : ∀ a a' : ι, ∑ k : κ, u a k * u a' k = if a = a' then 1 else 0) :
    ∑ k : κ, (∑ a : ι, u a k * x a) * (∑ a' : ι, u a' k * y a') =
      ∑ a : ι, x a * y a := by
  classical
  calc
    ∑ k : κ, (∑ a : ι, u a k * x a) * (∑ a' : ι, u a' k * y a') =
        ∑ k : κ, ∑ a : ι, ∑ a' : ι, (u a k * x a) * (u a' k * y a') := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ a : ι, ∑ a' : ι, ∑ k : κ, (u a k * x a) * (u a' k * y a') := by
          rw [Finset.sum_comm]
          congr with a
          rw [Finset.sum_comm]
    _ = ∑ a : ι, ∑ a' : ι, x a * y a' * (∑ k : κ, u a k * u a' k) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.sum_congr rfl ?_
          intro a' _ha'
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ = ∑ a : ι, ∑ a' : ι, x a * y a' * (if a = a' then 1 else 0) := by
          simp [horth]
    _ = ∑ a : ι, x a * y a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          calc
            ∑ a' : ι, x a * y a' * (if a = a' then 1 else 0) =
                x a * y a * (if a = a then 1 else 0) := by
                  refine Finset.sum_eq_single a ?_ ?_
                  · intro b _hb hba
                    have hab : a ≠ b := fun h => hba h.symm
                    simp [hab]
                  · intro hnot
                    exact (hnot (Finset.mem_univ a)).elim
            _ = x a * y a := by simp


open scoped BigOperators

namespace Matrix

-- Generalization plan (G0):
-- concept/name: Gram matrix of a finite rank-one expansion with orthonormal right
--   factors; orig was
--   `matrixGramLeft_eq_sum_vectorOuter_of_row_orthonormal_rank_one_expansion`
-- generality used: arbitrary row index type and finite column and factor index
--   types over a commutative semiring; no Euclidean dimension, matrix rank,
--   measure, convexity, smoothness, oracle, or algorithm assumptions are used
-- portable call pattern: low-rank matrix factorizations, singular-vector
--   expansions, and finite feature decompositions compute a row Gram matrix
--   while changing the matrix, factor family, coefficient semiring, and index types
-- counterargument checked: this is not merely the source's `matrixGramLeft`
--   notation wrapper; it connects matrix multiplication, a rank-one expansion,
--   right-factor orthonormality, and the resulting sum of left outer products
-- coverage search: searches for `matrix multiplication transpose equals sum outer
--   products orthonormal right factors`, `mul transpose sum vecMulVec
--   orthonormal`, and the full semantic statement found Mathlib's
--   `Matrix.isSymm_mul_transpose_self` and
--   `Matrix.mul_transpose_self_isDiag_iff_hasOrthogonalRows`, but neither computes
--   the Gram matrix of a rank-one expansion; no matching SOptLib theorem was found
-- minimal hypotheses: `Fintype κ` forms the matrix product, `Fintype ρ` forms
--   the factor sum, `DecidableEq ρ` states the Kronecker-delta identity, and
--   `CommSemiring R` supplies exactly the commutative finite-sum algebra used

/-- Multiplying a finite rank-one expansion by its transpose gives the sum of
the left-factor outer products when the right factors are orthonormal.

Layer: Glue | Gap: Level 1 (orthonormal rank-one expansion Gram identity)
Proof: expand both matrix factors entrywise and apply the raw-coordinate
  bilinear Parseval collapse to the orthonormal right-factor family.
Source: Mathlib finite matrix multiplication and `Matrix.vecMulVec`, together
  with the finite orthonormal-coordinate bilinear Parseval identity.
Used in: low-rank adaptive-gradient analyses that rewrite row Gram accumulators
  from orthonormal rank-one or singular-vector decompositions.
Book citation: book/research/Source.json#/key_lemmas/10/proof/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem mul_transpose_eq_sum_vecMulVec_of_orthonormal_right
    {R ι κ ρ : Type*} [CommSemiring R] [Fintype κ] [Fintype ρ]
    [DecidableEq ρ] (G : Matrix ι κ R) (u : ρ → ι → R) (b : ρ → κ → R)
    (hG : G = ∑ a : ρ, vecMulVec (u a) (b a))
    (horth : ∀ a a' : ρ, ∑ j : κ, b a j * b a' j = if a = a' then 1 else 0) :
    G * G.transpose = ∑ a : ρ, vecMulVec (u a) (u a) := by
  classical
  ext i k
  have hcollapse :=
    finite_orthonormal_coordinate_bilinear_collapse
      (u := b) (x := fun a : ρ => u a i) (y := fun a : ρ => u a k) horth
  have hG_apply : ∀ i j, G i j = ∑ a : ρ, u a i * b a j := by
    intro i j
    have h := congrFun (congrFun hG i) j
    simpa [Matrix.sum_apply, vecMulVec_apply] using h
  calc
    (G * G.transpose) i k = ∑ j : κ, G i j * G k j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ j : κ, (∑ a : ρ, b a j * u a i) *
          (∑ a' : ρ, b a' j * u a' k) := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hG_apply i j, hG_apply k j]
      simp [mul_comm]
    _ = ∑ a : ρ, u a i * u a k := hcollapse
    _ = (∑ a : ρ, vecMulVec (u a) (u a)) i k := by
      simp [Matrix.sum_apply, vecMulVec_apply]

end Matrix


namespace Matrix


-- Generalization plan (G0):
-- concept/name: right Gram matrix, named `Matrix.rightGram`; orig was `matrixGramRight`
-- generality used: arbitrary row and column index types and arbitrary entries with
--   multiplication and finite addition; only the contracted row index is finite
-- portable call pattern: full-matrix adaptive-gradient and tensor-matricization algorithms
--   form column Gram accumulators while changing matrix shapes, index types, and scalar rings
-- counterargument checked: the body is a short product, but right Gram matrices are a
--   recognized recurring object and the entrywise API hides transpose/multiplication plumbing
-- coverage search: searches for "right Gram matrix transpose multiplied by matrix" and
--   "Matrix rightGram transpose mul" found no Mathlib/SOptLib definition; Mathlib's
--   `Matrix.gram` is only a partial hit because it uses inner products (and conjugation over
--   complex scalars), rather than the general transpose product defined here
-- minimal hypotheses: `Fintype ι`, `Mul R`, and `AddCommMonoid R` are exactly those used
--   by rectangular matrix multiplication; no finiteness on the uncontracted column index is used

/-- The right Gram matrix of a rectangular matrix, obtained by multiplying its transpose by the
matrix.

Layer: Model | Concept: right Gram matrix of a rectangular matrix
Proof: (definitional construction; transpose multiplied by the rectangular matrix)
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: column-covariance accumulator updates for full-matrix adaptive-gradient and tensor-matricization preconditioners
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
def rightGram {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) : Matrix κ κ R :=
  G.transpose * G

/-- The right Gram matrix unfolds to multiplication of the transpose by the matrix.

Layer: Model | Gap: Level 0 (right Gram matrix unfolding rule)
Proof: by rfl after unfolding `Matrix.rightGram`.
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: rewriting column-Gram accumulator updates into the matrix products used by spectral and positive-semidefinite arguments
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem rightGram_def {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) :
    rightGram G = G.transpose * G :=
  rfl

/-- An entry of the right Gram matrix is the finite sum of the products of the
corresponding column entries.

Layer: Model | Gap: Level 0 (right Gram matrix entrywise specification)
Proof: unfold `Matrix.rightGram` and matrix multiplication.
Source: Mathlib `Matrix.mul_apply` and `Matrix.transpose_apply`
Used in: entrywise calculations for column-covariance accumulators and right Gram matrices
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem rightGram_apply {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) (j k : κ) :
    rightGram G j k = ∑ i, G i j * G i k := by
  simp [rightGram, Matrix.mul_apply]

/-- Over commutative multiplication, the right Gram matrix is invariant under transpose.

Layer: Model | Gap: Level 0 (right Gram matrix symmetry)
Proof: transpose the defining product, reverse its factors, and cancel the double transpose.
Source: Mathlib `Matrix.transpose_mul` and `Matrix.transpose_transpose`
Used in: symmetry and positive-semidefinite arguments for column-covariance accumulators
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem transpose_rightGram {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι]
    [AddCommMonoid R] [CommMagma R] (G : Matrix ι κ R) :
    (rightGram G).transpose = rightGram G := by
  simp [rightGram, Matrix.transpose_mul]

end Matrix


open scoped ComplexOrder Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: joint Loewner monotonicity of the binary matrix Kronecker
--   product on the positive-semidefinite cone; orig was the local block
--   `binary_kronecker_mono_of_posSemidef_of_le`
-- generality used: arbitrary `RCLike` scalars and arbitrary finite row/column
--   index types for both square matrices; no fixed dimensions, decidable
--   equality, optimization, measure, convexity, or oracle assumptions are used
-- portable call pattern: matrix and tensor adaptive-gradient proofs compare
--   Kronecker-assembled preconditioners while changing both factor spaces, all
--   four factors, and the two factorwise Loewner bounds
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; it packages joint monotonicity, whereas Mathlib only provides PSD
--   closure of a single binary Kronecker product
-- coverage search: symbol searches for `kronecker_mono_of_posSemidef_of_le`
--   and natural-language searches for Kronecker Loewner monotonicity found
--   `Matrix.PosSemidef.kronecker` and the staged dependent-family theorem
--   `SOptLib.tensorKronecker_mono_of_forall_le`; the former is only a proof
--   ingredient and the latter concerns the distinct named dependent product
-- minimal hypotheses: only the two lower factors are assumed PSD; positivity
--   of the upper factors follows from their Loewner bounds, and `Finite`
--   suffices because Mathlib's binary Kronecker PSD theorem uses that class

/-- The binary Kronecker product is jointly monotone in Loewner order when its
two lower factors are positive semidefinite.

Layer: Glue | Gap: Level 1 (binary Kronecker joint Loewner monotonicity)
Proof: derive positivity of the upper right factor, decompose the Kronecker-product difference into two Kronecker products of PSD matrices, and add their positivity witnesses.
Source: Mathlib matrix Loewner order and `Matrix.PosSemidef.kronecker`
Used in: matrix and tensor adaptive-gradient arguments that lift simultaneous factorwise accumulator bounds to an assembled Kronecker preconditioner bound
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1 and 2 -/
theorem kronecker_mono_of_posSemidef_of_le
    {𝕜 : Type u} [RCLike 𝕜]
    {m : Type v} [Finite m] {n : Type w} [Finite n]
    (A B : Matrix m m 𝕜) (C D : Matrix n n 𝕜)
    (hA : A.PosSemidef) (hC : C.PosSemidef)
    (hAB : A ≤ B) (hCD : C ≤ D) :
    A ⊗ₖ C ≤ B ⊗ₖ D := by
  rw [Matrix.le_iff]
  have hD : D.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (le_trans hC.nonneg hCD)
  have hLeft : ((B - A) ⊗ₖ D).PosSemidef := hAB.kronecker hD
  have hRight : (A ⊗ₖ (D - C)).PosSemidef := hA.kronecker hCD
  have hSum : (((B - A) ⊗ₖ D) + (A ⊗ₖ (D - C))).PosSemidef :=
    hLeft.add hRight
  have hDiff :
      B ⊗ₖ D - A ⊗ₖ C = (B - A) ⊗ₖ D + A ⊗ₖ (D - C) := by
    ext ij kl
    rcases ij with ⟨i, k⟩
    rcases kl with ⟨j, l⟩
    simp [sub_mul, mul_sub]
  simpa [hDiff] using hSum

end Matrix


namespace Matrix


-- Generalization plan (G0):
-- concept/name: self outer product of a product-index vector factorization;
--   orig was `vectorKronecker_outer_eq_kron_outer`, renamed
--   `Matrix.vecMulVec_vectorKronecker_self`
-- generality used: arbitrary index types and coefficients in a commutative semigroup;
--   no finiteness, decidable equality, additive, topological, measure, convexity,
--   smoothness, or oracle assumptions are used
-- portable call pattern: matrix and tensor rank-one decomposition proofs rewrite the
--   self outer product of a vectorized rank-one factor into the Kronecker product of
--   factor Gram matrices while changing both index types, scalar type, and factors
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it connects `Matrix.vecMulVec`, function uncurrying, and `Matrix.kronecker` in a
--   reusable representation identity not supplied by either primitive alone
-- coverage search: project symbol searches for "vector outer product Kronecker product
--   equality" and "vecMulVec self outer Kronecker" found only the private source lemma;
--   Mathlib semantic search found `Matrix.kronecker`, `Matrix.kroneckerMap_apply`, and
--   `Matrix.mul_kronecker_mul`, but no outer-product identity, so coverage is partial
-- minimal hypotheses: `[CommSemigroup R]` is exactly the associativity and commutativity
--   needed to reorder the four coordinate factors; all source finiteness and real-scalar
--   restrictions were removed

/-- The self outer product of an uncurried vector outer product is the Kronecker product
of the self outer products of its two vector factors.

Layer: Model | Gap: Level 1 (vector outer-product and matrix Kronecker representation bridge)
Proof: extensionality reduces the matrix identity to four scalar factors; associativity and commutativity put the factors in the Kronecker coordinate order
Source: Mathlib `Matrix.vecMulVec`, `Matrix.kronecker`, and their coordinate formulas
Used in: matrix and tensor adaptive-gradient rank-domination proofs that rewrite vectorized rank-one outer products into Kronecker products of factor Gram matrices
Book citation: book/research/Source.json#/key_lemmas/10/proof/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem vecMulVec_vectorKronecker_self
    {ι : Type u} {κ : Type v} {R : Type w} [CommSemigroup R]
    (u : ι → R) (v : κ → R) :
    Matrix.vecMulVec (Function.uncurry (Matrix.vecMulVec u v))
        (Function.uncurry (Matrix.vecMulVec u v)) =
      Matrix.kronecker (Matrix.vecMulVec u u) (Matrix.vecMulVec v v) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Function.uncurry, Matrix.vecMulVec_apply, Matrix.kroneckerMap_apply,
    mul_left_comm, mul_comm]

end Matrix


open scoped BigOperators Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: finite-sum Loewner domination for self outer products of
--   product-index vectors; orig was
--   `sum_vectorKronecker_outer_le_one_kron_sum_outer`, renamed
--   `Matrix.sum_vecMulVec_product_le_one_kronecker_sum_vecMulVec`
-- generality used: arbitrary finite family, left-coordinate, and right-coordinate
--   types over real matrices; no fixed dimensions, ranks, measures, convexity,
--   smoothness, stochastic-oracle assumptions, or algorithm state are used
-- portable call pattern: covariance and low-rank decomposition proofs vary the
--   finite family and both vector factors while retaining pointwise domination of
--   the left self outer products by the identity and the same Kronecker sum bound
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it packages a reusable passage from pointwise factor bounds to a product-vector
--   covariance bound, including the factorization and finite-sum distribution steps
-- coverage search: symbol searches for "sum outer product of product vectors bounded
--   by identity Kronecker sum outer products" and "vecMulVec kronecker finite sum
--   Loewner order" found only the private Shampoo source variants; Mathlib semantic
--   search found tensor-product sum distribution but no matching matrix-order bound,
--   while `Matrix.posSemidef_vecMulVec_self_star`,
--   `Matrix.vecMulVec_vectorKronecker_self`, and
--   `Matrix.kronecker_mono_of_posSemidef_of_le` cover only proof components
-- minimal hypotheses: `[Fintype ρ]` is used for the family sum, while `Finite`
--   suffices for both coordinate-index matrix orders and `[DecidableEq ι]`
--   constructs the left identity matrix; the pointwise left-factor Loewner bound
--   is the sole data hypothesis

/-- A finite sum of self outer products of product-index vectors is bounded by the
identity Kronecker the sum of the right-factor self outer products when every
left-factor self outer product is bounded by the identity.

Layer: Glue | Gap: Level 1 (finite product-vector covariance Kronecker domination)
Proof: factor each product-vector self outer product as a matrix Kronecker product, apply binary Kronecker monotonicity using positivity of self outer products, sum the pointwise inequalities, and distribute the fixed identity through the finite sum.
Source: Mathlib positive-semidefinite matrix order, self outer products, finite sums, and matrix Kronecker products
Used in: matrix and tensor adaptive-gradient rank-decomposition proofs that bound a vectorized rank-one covariance family by an identity tensored with the corresponding factor Gram sum
Book citation: book/research/Source.json#/key_lemmas/10/proof/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem sum_vecMulVec_product_le_one_kronecker_sum_vecMulVec
    {ρ : Type u} {ι : Type v} {κ : Type w}
    [Fintype ρ] [Finite ι] [DecidableEq ι] [Finite κ]
    (u : ρ → ι → ℝ) (b : ρ → κ → ℝ)
    (hu : ∀ a : ρ,
      Matrix.vecMulVec (u a) (u a) ≤ (1 : Matrix ι ι ℝ)) :
    (∑ a : ρ,
        Matrix.vecMulVec
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
      (1 : Matrix ι ι ℝ) ⊗ₖ
        (∑ a : ρ, Matrix.vecMulVec (b a) (b a)) := by
  classical
  have hterm : ∀ a : ρ,
      Matrix.vecMulVec
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
          (Function.uncurry (Matrix.vecMulVec (u a) (b a))) ≤
        (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.vecMulVec (b a) (b a) := by
    intro a
    rw [Matrix.vecMulVec_vectorKronecker_self]
    exact Matrix.kronecker_mono_of_posSemidef_of_le
      (Matrix.vecMulVec (u a) (u a)) (1 : Matrix ι ι ℝ)
      (Matrix.vecMulVec (b a) (b a)) (Matrix.vecMulVec (b a) (b a))
      (by simpa using Matrix.posSemidef_vecMulVec_self_star (u a))
      (by simpa using Matrix.posSemidef_vecMulVec_self_star (b a))
      (hu a) le_rfl
  have hsum :
      (∑ a : ρ,
          Matrix.vecMulVec
            (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
            (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
        ∑ a : ρ, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.vecMulVec (b a) (b a) :=
    Finset.sum_le_sum (s := Finset.univ) (fun a _ha => hterm a)
  calc
    (∑ a : ρ,
        Matrix.vecMulVec
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
        ∑ a : ρ, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.vecMulVec (b a) (b a) := hsum
    _ = (1 : Matrix ι ι ℝ) ⊗ₖ
        (∑ a : ρ, Matrix.vecMulVec (b a) (b a)) := by
      ext ij kl
      simp_rw [Matrix.sum_apply, Matrix.kroneckerMap_apply]
      rw [Matrix.sum_apply, Finset.mul_sum]

end Matrix


open scoped BigOperators Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: finite-sum Loewner domination for self outer products of
--   product-index vectors; orig was
--   `sum_vectorKronecker_outer_le_sum_outer_kron_one`, renamed
--   `Matrix.sum_vecMulVec_product_le_sum_vecMulVec_kronecker_one`
-- generality used: arbitrary finite family, left-coordinate, and right-coordinate
--   types over real matrices; no fixed dimensions, ranks, measures, convexity,
--   smoothness, stochastic-oracle assumptions, or algorithm state are used
-- portable call pattern: covariance and low-rank decomposition proofs vary the
--   finite family and both vector factors while retaining pointwise domination of
--   the right self outer products by the identity and the same Kronecker sum bound
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it packages the reusable right-factor counterpart of the existing left-factor
--   domination theorem, including factorization and finite-sum distribution
-- coverage search: symbol searches for "sum outer products of product vectors
--   bounded by sum first-factor outer products Kronecker identity" found only the
--   private Shampoo theorem and the opposite-orientation staged companion; Mathlib
--   semantic search found Kronecker sum distribution but no matching matrix-order
--   bound, while `Matrix.vecMulVec_vectorKronecker_self` and
--   `Matrix.kronecker_mono_of_posSemidef_of_le` cover only proof components
-- minimal hypotheses: `[Fintype ρ]` is used for the family sum, while `Finite`
--   suffices for both coordinate-index matrix orders and `[DecidableEq κ]`
--   constructs the right identity matrix; the pointwise right-factor Loewner bound
--   is the sole data hypothesis

/-- A finite sum of self outer products of product-index vectors is bounded by the
sum of the left-factor self outer products Kronecker the identity when every
right-factor self outer product is bounded by the identity.

Layer: Glue | Gap: Level 1 (finite product-vector covariance Kronecker domination)
Proof: factor each product-vector self outer product as a matrix Kronecker product, apply binary Kronecker monotonicity using positivity of self outer products, sum the pointwise inequalities, and distribute the fixed identity through the finite sum.
Source: Mathlib positive-semidefinite matrix order, self outer products, finite sums, and matrix Kronecker products
Used in: matrix and tensor adaptive-gradient rank-decomposition proofs that bound a vectorized rank-one covariance family by the corresponding factor Gram sum tensored with an identity
Book citation: book/research/Source.json#/key_lemmas/10/proof/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem sum_vecMulVec_product_le_sum_vecMulVec_kronecker_one
    {ρ : Type u} {ι : Type v} {κ : Type w}
    [Fintype ρ] [Finite ι] [Finite κ] [DecidableEq κ]
    (u : ρ → ι → ℝ) (b : ρ → κ → ℝ)
    (hb : ∀ a : ρ,
      Matrix.vecMulVec (b a) (b a) ≤ (1 : Matrix κ κ ℝ)) :
    (∑ a : ρ,
        Matrix.vecMulVec
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
      (∑ a : ρ, Matrix.vecMulVec (u a) (u a)) ⊗ₖ
        (1 : Matrix κ κ ℝ) := by
  classical
  have hterm : ∀ a : ρ,
      Matrix.vecMulVec
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
          (Function.uncurry (Matrix.vecMulVec (u a) (b a))) ≤
        Matrix.vecMulVec (u a) (u a) ⊗ₖ (1 : Matrix κ κ ℝ) := by
    intro a
    rw [Matrix.vecMulVec_vectorKronecker_self]
    exact Matrix.kronecker_mono_of_posSemidef_of_le
      (Matrix.vecMulVec (u a) (u a)) (Matrix.vecMulVec (u a) (u a))
      (Matrix.vecMulVec (b a) (b a)) (1 : Matrix κ κ ℝ)
      (by simpa using Matrix.posSemidef_vecMulVec_self_star (u a))
      (by simpa using Matrix.posSemidef_vecMulVec_self_star (b a))
      le_rfl (hb a)
  have hsum :
      (∑ a : ρ,
          Matrix.vecMulVec
            (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
            (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
        ∑ a : ρ, Matrix.vecMulVec (u a) (u a) ⊗ₖ (1 : Matrix κ κ ℝ) :=
    Finset.sum_le_sum (s := Finset.univ) (fun a _ha => hterm a)
  calc
    (∑ a : ρ,
        Matrix.vecMulVec
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
          (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
        ∑ a : ρ, Matrix.vecMulVec (u a) (u a) ⊗ₖ (1 : Matrix κ κ ℝ) := hsum
    _ = (∑ a : ρ, Matrix.vecMulVec (u a) (u a)) ⊗ₖ
        (1 : Matrix κ κ ℝ) := by
      ext ij kl
      simp_rw [Matrix.sum_apply, Matrix.kroneckerMap_apply]
      rw [Matrix.sum_apply, Finset.sum_mul]

end Matrix


open scoped BigOperators

namespace Matrix

-- Generalization plan (G0):
-- concept/name: Gram matrix of a finite rank-one expansion with orthonormal left
--   factors; orig was
--   `matrixGramRight_eq_sum_vectorOuter_of_orthonormal_rank_one_expansion`
-- generality used: arbitrary finite row and factor index types and arbitrary
--   column index type over a commutative semiring; no Euclidean dimension,
--   matrix rank, measure, convexity, smoothness, oracle, or algorithm assumptions
--   are used
-- portable call pattern: low-rank matrix factorizations, singular-vector
--   expansions, and finite feature decompositions compute a column Gram matrix
--   while changing the matrix, factor family, coefficient semiring, and index types
-- counterargument checked: this is not merely the source's `matrixGramRight`
--   notation wrapper or a duplicate of the companion row-Gram theorem; it links
--   transpose multiplication to an orthonormal-left rank-one expansion and the
--   resulting sum of right outer products
-- coverage search: searches for `matrix transpose multiply self equals sum vector
--   outer products orthonormal left factors rank one expansion`,
--   `transpose_mul_self sum vecMulVec orthonormal`, and the full semantic statement
--   found Mathlib's `Matrix.isSymm_transpose_mul_self` and
--   `Matrix.transpose_mul_self_isDiag_iff_hasOrthogonalCols`, plus the staged dual
--   `Matrix.mul_transpose_eq_sum_vecMulVec_of_orthonormal_right`; none computes
--   this column Gram matrix from an orthonormal-left rank-one expansion
-- minimal hypotheses: `Fintype ι` forms the matrix product, `Fintype ρ` forms
--   the factor sum, `DecidableEq ρ` states the Kronecker-delta identity, and
--   `CommSemiring R` supplies exactly the commutative finite-sum algebra used

/-- Multiplying the transpose of a finite rank-one expansion by itself gives the
sum of the right-factor outer products when the left factors are orthonormal.

Layer: Glue | Gap: Level 1 (orthonormal rank-one expansion column-Gram identity)
Proof: expand both matrix factors entrywise and apply the raw-coordinate
  bilinear Parseval collapse to the orthonormal left-factor family.
Source: Mathlib finite matrix multiplication and `Matrix.vecMulVec`, together
  with the finite orthonormal-coordinate bilinear Parseval identity.
Used in: low-rank adaptive-gradient analyses that rewrite column Gram
  accumulators from orthonormal rank-one or singular-vector decompositions.
Book citation: book/research/Source.json#/key_lemmas/10/proof/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem transpose_mul_self_eq_sum_vecMulVec_of_orthonormal_left
    {R ι κ ρ : Type*} [CommSemiring R] [Fintype ι] [Fintype ρ]
    [DecidableEq ρ] (G : Matrix ι κ R) (u : ρ → ι → R) (b : ρ → κ → R)
    (hG : G = ∑ a : ρ, vecMulVec (u a) (b a))
    (horth : ∀ a a' : ρ, ∑ i : ι, u a i * u a' i = if a = a' then 1 else 0) :
    G.transpose * G = ∑ a : ρ, vecMulVec (b a) (b a) := by
  classical
  ext j l
  have hcollapse :=
    finite_orthonormal_coordinate_bilinear_collapse
      (u := u) (x := fun a : ρ => b a j) (y := fun a : ρ => b a l) horth
  have hG_apply : ∀ i j, G i j = ∑ a : ρ, u a i * b a j := by
    intro i j
    have h := congrFun (congrFun hG i) j
    simpa [Matrix.sum_apply, vecMulVec_apply] using h
  calc
    (G.transpose * G) j l = ∑ i : ι, G i j * G i l := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ i : ι, (∑ a : ρ, u a i * b a j) *
          (∑ a' : ρ, u a' i * b a' l) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [hG_apply i j, hG_apply i l]
    _ = ∑ a : ρ, b a j * b a l := hcollapse
    _ = (∑ a : ρ, vecMulVec (b a) (b a)) j l := by
      simp [Matrix.sum_apply, vecMulVec_apply]

end Matrix


open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: Loewner-order finite-sum Cauchy--Schwarz for self outer products;
--   orig was `vector_sum_outer_le_card_smul_sum_outer`, renamed
--   `Matrix.vecMulVec_sum_le_card_smul_sum_vecMulVec`
-- generality used: arbitrary finite family and coordinate index types over real
--   scalars; no matrix dimensions, decidable equality, measure, convexity,
--   smoothness, oracle, or algorithm assumptions are used
-- portable call pattern: low-rank decomposition, covariance, mini-batch, and
--   matrix-factorization proofs bound the self outer product of a finite vector
--   sum while changing the finite family, coordinate type, and vectors
-- counterargument checked: this is neither paper-local traceability nor a pure
--   wrapper; it lifts finite-sum Cauchy--Schwarz into matrix Loewner order, a
--   reusable relation not provided by the scalar inequality or `vecMulVec` alone
-- coverage search: symbol searches for `vecMulVec sum card smul positive
--   semidefinite order` found only the private source theorem and scalar/norm
--   relatives; Mathlib semantic search found `sq_sum_le_card_mul_sum_sq` and
--   `Matrix.posSemidef_vecMulVec_self_star`, but no matching matrix-order bound,
--   so existing coverage supplies proof ingredients only
-- minimal hypotheses: `[Fintype ι]` forms both finite sums and supplies the
--   cardinality; `[Finite α]` suffices because a `Fintype α` instance is only
--   needed locally for finite-matrix quadratic forms; all source-local notation
--   was replaced by `Matrix.vecMulVec`

/-- The self outer product of a finite vector sum is bounded in Loewner order by
the family cardinality times the sum of the individual self outer products.

Layer: Glue | Gap: Level 1 (finite-sum outer-product Loewner Cauchy--Schwarz bound)
Proof: test the matrix difference on an arbitrary vector, expand each self outer
  product into the square of a scalar pairing, and apply Mathlib's finite-sum
  square Cauchy--Schwarz inequality.
Source: Mathlib finite-sum Chebyshev inequalities and positive-semidefinite matrix
  quadratic-form characterization
Used in: low-rank and matrix-factorization analyses that control the rank-one
  matrix of a summed decomposition before comparing factor Gram matrices
Book citation: book/research/Source.json#/key_lemmas/10/proof/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic
  Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem vecMulVec_sum_le_card_smul_sum_vecMulVec
    {ι α : Type*} [Fintype ι] [Finite α] (w : ι → α → ℝ) :
    Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
        (fun a : α => ∑ i : ι, w i a) ≤
      (Fintype.card ι : ℝ) •
        ∑ i : ι, Matrix.vecMulVec (w i) (w i) := by
  letI := Fintype.ofFinite α
  classical
  have vecMulVec_dotProduct_mulVec (x g : α → ℝ) :
      dotProduct (star x) ((Matrix.vecMulVec g g).mulVec x) =
        (∑ a : α, x a * g a) ^ 2 := by
    simp [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, pow_two,
      Finset.mul_sum, Finset.sum_comm, mul_left_comm, mul_comm]
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have hsumHerm :
        (∑ i : ι, Matrix.vecMulVec (w i) (w i)).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro a b
      rw [Matrix.sum_apply, Matrix.sum_apply]
      change star (∑ i : ι, w i b * w i a) = ∑ i : ι, w i a * w i b
      rw [star_sum]
      exact Finset.sum_congr rfl (by intro i _hi; simp [mul_comm])
    have houterHerm :
        (Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
          (fun a : α => ∑ i : ι, w i a)).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro a b
      change star ((∑ i : ι, w i b) * (∑ i : ι, w i a)) =
        (∑ i : ι, w i a) * (∑ i : ι, w i b)
      simp [mul_comm]
    exact (hsumHerm.smul (by simp [isSelfAdjoint_iff])).sub houterHerm
  · intro x
    let beta : ι → ℝ := fun i => ∑ a : α, x a * w i a
    have hsum_beta :
        (∑ a : α, x a * (∑ i : ι, w i a)) = ∑ i : ι, beta i := by
      calc
        (∑ a : α, x a * (∑ i : ι, w i a)) =
            ∑ a : α, ∑ i : ι, x a * w i a := by
              simp [Finset.mul_sum]
        _ = ∑ i : ι, ∑ a : α, x a * w i a := by
              rw [Finset.sum_comm]
        _ = ∑ i : ι, beta i := by
              simp [beta]
    have hsum_quad :
        dotProduct (star x)
            (((∑ i : ι, Matrix.vecMulVec (w i) (w i)).mulVec x)) =
          ∑ i : ι, beta i ^ 2 := by
      calc
        dotProduct (star x)
            (((∑ i : ι, Matrix.vecMulVec (w i) (w i)).mulVec x)) =
            dotProduct (star x)
              (∑ i : ι, (Matrix.vecMulVec (w i) (w i)).mulVec x) := by
                rw [Matrix.sum_mulVec]
        _ = ∑ i : ι,
            dotProduct (star x) ((Matrix.vecMulVec (w i) (w i)).mulVec x) := by
              simpa using
                (dotProduct_sum (star x) (Finset.univ : Finset ι)
                  (fun i : ι => (Matrix.vecMulVec (w i) (w i)).mulVec x))
        _ = ∑ i : ι, beta i ^ 2 := by
              exact Finset.sum_congr rfl (by
                intro i _hi
                simpa [beta] using vecMulVec_dotProduct_mulVec x (w i))
    have houter_quad :
        dotProduct (star x)
            ((Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
              (fun a : α => ∑ i : ι, w i a)).mulVec x) =
          (∑ i : ι, beta i) ^ 2 := by
      rw [vecMulVec_dotProduct_mulVec, hsum_beta]
    have hquad_eq :
        dotProduct (star x)
            (((Fintype.card ι : ℝ) •
                (∑ i : ι, Matrix.vecMulVec (w i) (w i)) -
              Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
                (fun a : α => ∑ i : ι, w i a)).mulVec x) =
          (Fintype.card ι : ℝ) * (∑ i : ι, beta i ^ 2) -
            (∑ i : ι, beta i) ^ 2 := by
      calc
        dotProduct (star x)
            (((Fintype.card ι : ℝ) •
                (∑ i : ι, Matrix.vecMulVec (w i) (w i)) -
              Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
                (fun a : α => ∑ i : ι, w i a)).mulVec x) =
          dotProduct (star x)
            ((((Fintype.card ι : ℝ) •
                (∑ i : ι, Matrix.vecMulVec (w i) (w i))).mulVec x) -
              (Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
                (fun a : α => ∑ i : ι, w i a)).mulVec x) := by
            rw [Matrix.sub_mulVec]
        _ = dotProduct (star x)
              (((Fintype.card ι : ℝ) •
                (∑ i : ι, Matrix.vecMulVec (w i) (w i))).mulVec x) -
            dotProduct (star x)
              ((Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
                (fun a : α => ∑ i : ι, w i a)).mulVec x) := by
            rw [dotProduct_sub]
        _ = (Fintype.card ι : ℝ) *
              dotProduct (star x)
                (((∑ i : ι, Matrix.vecMulVec (w i) (w i)).mulVec x)) -
            dotProduct (star x)
              ((Matrix.vecMulVec (fun a : α => ∑ i : ι, w i a)
                (fun a : α => ∑ i : ι, w i a)).mulVec x) := by
            rw [Matrix.smul_mulVec, dotProduct_smul]
            simp [smul_eq_mul]
        _ = (Fintype.card ι : ℝ) * (∑ i : ι, beta i ^ 2) -
            (∑ i : ι, beta i) ^ 2 := by
              rw [hsum_quad, houter_quad]
    rw [hquad_eq]
    have hscalar := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ι)) (f := beta)
    simpa using sub_nonneg.mpr hscalar

end Matrix


open scoped BigOperators Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: inverse-rank Loewner domination of a matrix-vectorization outer
--   product by Kronecker products of its left and right Gram matrices; orig was
--   `Lemma_9_single_matrix_rank_domination`, renamed
--   `Matrix.inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams`
-- generality used: arbitrary finite row and column index types for a real matrix,
--   decidable equality for the two identity matrices, and a positive natural rank
--   cap; no fixed dimensions, measure, convexity, smoothness, oracle, or algorithm
--   assumptions are used
-- portable call pattern: low-rank matrix-gradient, covariance, sketching, and
--   structured-preconditioner proofs change the finite matrix and positive rank
--   cap while reusing the same two Loewner bounds for its vectorized outer product
-- counterargument checked: the theorem is not paper-local traceability or a pure
--   wrapper; it composes rank-indexed orthonormal factorizations, a matrix-order
--   finite-sum Cauchy--Schwarz bound, Gram identities, inverse-rank scaling, and two
--   distinct Kronecker domination arguments behind one standard matrix contract
-- coverage search: symbol searches for "inverse rank scaled outer product matrix
--   vectorization bounded identity Kronecker right Gram left Gram Kronecker
--   identity", "vecMulVec vectorization rank kronecker gram Loewner bound", and
--   "matrix rank vectorization outer product gram domination" found only the
--   private Shampoo theorem and its staged proof components; Mathlib semantic
--   search returned `Matrix.gram`, vectorization/Kronecker identities, and
--   `Matrix.rank_vecMulVec_le`, but no theorem with either full Loewner bound
-- minimal hypotheses: both index types must be finite for rank, Gram products,
--   and Loewner order; decidable equality constructs both identity matrices; the
--   positivity of `r` is exactly what permits inverse-rank cancellation

/-- If a finite real matrix has rank at most a positive natural number `r`, then
`r⁻¹` times the self outer product of its row-column vectorization is bounded
both by the row identity Kronecker its right Gram matrix and by its left Gram
matrix Kronecker the column identity.

Layer: Glue | Gap: Level 2 (inverse-rank matrix-vectorization Gram domination)
Proof: expand the matrix into rank-many outer products with orthonormal left or right factors, bound the outer product of their vectorized sum by rank times the sum of outer products, cancel against the positive rank cap, and apply the corresponding finite-sum Kronecker domination and Gram identity.
Source: Mathlib finite real matrix rank, positive-semidefinite Loewner order, matrix Gram products, vector outer products, and Kronecker products
Used in: low-rank matrix-gradient and structured-preconditioner analyses that compare a vectorized gradient covariance with both row- and column-Gram Kronecker preconditioners
Book citation: book/research/Source.json#/key_lemmas/10
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) (hrank : G.rank ≤ r) :
    ((r : ℝ)⁻¹ •
          Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
        (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.rightGram G) ∧
      ((r : ℝ)⁻¹ •
          Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
        Matrix.leftGram G ⊗ₖ (1 : Matrix κ κ ℝ)) := by
  classical
  have hrReal : 0 < (r : ℝ) := by
    exact_mod_cast hr
  have hcard_le : (Fintype.card (Fin G.rank) : ℝ) ≤ (r : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hrank
  have hcoef_le_one :
      (r : ℝ)⁻¹ * (Fintype.card (Fin G.rank) : ℝ) ≤ 1 := by
    calc
      (r : ℝ)⁻¹ * (Fintype.card (Fin G.rank) : ℝ) ≤
          (r : ℝ)⁻¹ * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hcard_le (inv_nonneg.mpr hrReal.le)
      _ = 1 := inv_mul_cancel₀ hrReal.ne'
  have smul_le_self_of_nonneg_le_one_posSemidef
      (A : Matrix (ι × κ) (ι × κ) ℝ) {c : ℝ}
      (hA : A.PosSemidef) (hc : c ≤ 1) : c • A ≤ A := by
    rw [Matrix.le_iff]
    have hdiff : A - c • A = (1 - c) • A := by
      ext i j
      simp [sub_mul]
    rw [hdiff]
    exact hA.smul (sub_nonneg.mpr hc)
  have rank_scaled_outer_le_sum
      (w : Fin G.rank → (ι × κ) → ℝ)
      (hsum :
        Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
          (Fintype.card (Fin G.rank) : ℝ) •
            ∑ a : Fin G.rank, Matrix.vecMulVec (w a) (w a)) :
      (r : ℝ)⁻¹ •
          Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
        ∑ a : Fin G.rank, Matrix.vecMulVec (w a) (w a) := by
    let S : Matrix (ι × κ) (ι × κ) ℝ :=
      ∑ a : Fin G.rank, Matrix.vecMulVec (w a) (w a)
    have hSpsd : S.PosSemidef := by
      dsimp [S]
      simpa using Matrix.posSemidef_sum
        (Finset.univ : Finset (Fin G.rank))
        (fun a _ha => by
          simpa using Matrix.posSemidef_vecMulVec_self_star (w a))
    have hscaled :
        (r : ℝ)⁻¹ •
            Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
          (r : ℝ)⁻¹ •
            ((Fintype.card (Fin G.rank) : ℝ) • S) :=
      smul_le_smul_of_nonneg_left (by simpa [S] using hsum)
        (inv_nonneg.mpr hrReal.le)
    have hcoef :
        (r : ℝ)⁻¹ • ((Fintype.card (Fin G.rank) : ℝ) • S) ≤ S := by
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
        smul_le_self_of_nonneg_le_one_posSemidef S hSpsd hcoef_le_one
    exact hscaled.trans hcoef
  obtain ⟨u, b, hG, horth, hubound⟩ :=
    Matrix.exists_rank_one_sum_eq_with_orthonormal_left G
  have hgramR :
      Matrix.rightGram G =
        ∑ a : Fin G.rank, Matrix.vecMulVec (b a) (b a) := by
    simpa [Matrix.rightGram] using
      Matrix.transpose_mul_self_eq_sum_vecMulVec_of_orthonormal_left
        G u b hG horth
  have hvec :
      Function.uncurry G = fun ij : ι × κ =>
        ∑ a : Fin G.rank,
          Function.uncurry (Matrix.vecMulVec (u a) (b a)) ij := by
    funext ij
    rcases ij with ⟨i, j⟩
    have h := congrFun (congrFun hG i) j
    simpa [Function.uncurry, Matrix.vecMulVec, Matrix.sum_apply] using h
  have hsum_vec :
      Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
        (Fintype.card (Fin G.rank) : ℝ) •
          ∑ a : Fin G.rank,
            Matrix.vecMulVec
              (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
              (Function.uncurry (Matrix.vecMulVec (u a) (b a))) := by
    simpa [hvec] using
      Matrix.vecMulVec_sum_le_card_smul_sum_vecMulVec
        (fun a : Fin G.rank =>
          Function.uncurry (Matrix.vecMulVec (u a) (b a)))
  have hscaled :
      (r : ℝ)⁻¹ •
          Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
        ∑ a : Fin G.rank,
          Matrix.vecMulVec
            (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
            (Function.uncurry (Matrix.vecMulVec (u a) (b a))) :=
    rank_scaled_outer_le_sum
      (fun a : Fin G.rank =>
        Function.uncurry (Matrix.vecMulVec (u a) (b a))) hsum_vec
  constructor
  · exact hscaled.trans (by
      rw [hgramR]
      exact Matrix.sum_vecMulVec_product_le_one_kronecker_sum_vecMulVec
        u b hubound)
  · obtain ⟨uL, bL, hGL, horthL, hbbound⟩ :=
      Matrix.exists_rank_one_sum_eq_with_orthonormal_right G
    have hgramL :
        Matrix.leftGram G =
          ∑ a : Fin G.rank, Matrix.vecMulVec (uL a) (uL a) := by
      simpa [Matrix.leftGram] using
        Matrix.mul_transpose_eq_sum_vecMulVec_of_orthonormal_right
          G uL bL hGL horthL
    have hvecL :
        Function.uncurry G = fun ij : ι × κ =>
          ∑ a : Fin G.rank,
            Function.uncurry (Matrix.vecMulVec (uL a) (bL a)) ij := by
      funext ij
      rcases ij with ⟨i, j⟩
      have h := congrFun (congrFun hGL i) j
      simpa [Function.uncurry, Matrix.vecMulVec, Matrix.sum_apply] using h
    have hsum_vecL :
        Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
          (Fintype.card (Fin G.rank) : ℝ) •
            ∑ a : Fin G.rank,
              Matrix.vecMulVec
                (Function.uncurry (Matrix.vecMulVec (uL a) (bL a)))
                (Function.uncurry (Matrix.vecMulVec (uL a) (bL a))) := by
      simpa [hvecL] using
        Matrix.vecMulVec_sum_le_card_smul_sum_vecMulVec
          (fun a : Fin G.rank =>
            Function.uncurry (Matrix.vecMulVec (uL a) (bL a)))
    have hscaledL :
        (r : ℝ)⁻¹ •
            Matrix.vecMulVec (Function.uncurry G) (Function.uncurry G) ≤
          ∑ a : Fin G.rank,
            Matrix.vecMulVec
              (Function.uncurry (Matrix.vecMulVec (uL a) (bL a)))
              (Function.uncurry (Matrix.vecMulVec (uL a) (bL a))) :=
      rank_scaled_outer_le_sum
        (fun a : Fin G.rank =>
          Function.uncurry (Matrix.vecMulVec (uL a) (bL a))) hsum_vecL
    exact hscaledL.trans (by
      rw [hgramL]
      exact Matrix.sum_vecMulVec_product_le_sum_vecMulVec_kronecker_one
        uL bL hbbound)

end Matrix


open scoped BigOperators Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: regularized inverse-rank finite-family vectorized matrix outer-product
--   domination by the two corresponding Kronecker Gram accumulators; orig was
--   `matrix_rank_domination_two_upper_bounds`, renamed
--   `Matrix.regularized_inv_rank_vecMulVec_sum_le_kronecker_gram_bounds`
-- generality used: arbitrary finite family, row, and column index types for real
--   matrices, decidable equality for the two identity matrices, a positive natural
--   rank cap, and an arbitrary real common ridge; no dimension encoding, measure,
--   convexity, smoothness, oracle, or algorithm-state assumptions are used
-- portable call pattern: structured adaptive-matrix and low-rank covariance methods
--   change the finite matrix family, row and column types, positive rank cap, and
--   common ridge while retaining the same paired regularized Kronecker upper bounds
-- counterargument checked: this is not a pure rename or paper-local wrapper; unlike
--   the existing single-matrix theorem, it packages finite-family order aggregation,
--   ridge transport to both Kronecker accumulators, and the paired final contract
-- coverage search: symbol searches for "regularized inverse rank scaled sum matrix
--   vectorization outer product bounded identity Kronecker sum right Gram and sum
--   left Gram Kronecker identity" found the strictly pointwise
--   `Matrix.inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams` and tensor-mode
--   analogues, but no matrix-family theorem with both regularized conclusions;
--   Mathlib semantic search found Gram, vectorization, and Kronecker primitives only
-- minimal hypotheses: finite row and column types support rank and Gram products;
--   decidable equality constructs identities; `0 < r` is required by the pointwise
--   inverse-rank bound; no sign assumption on the common ridge is used

/-- A common ridge plus the inverse-rank-scaled sum of vectorized matrix outer products
is bounded both by the row identity Kronecker the regularized right-Gram sum and by the
regularized left-Gram sum Kronecker the column identity.

Layer: Glue | Gap: Level 2 (regularized finite-family matrix rank domination)
Proof: sum the pointwise inverse-rank Kronecker Gram bounds, transport scalar multiplication through the finite sums, distribute each Kronecker product over its Gram sum, and add the common ridge to both inequalities.
Source: Mathlib finite real matrix rank, positive-semidefinite Loewner order, finite sums, matrix Gram products, vector outer products, and Kronecker-product distributivity
Used in: low-rank structured adaptive-matrix analyses that compare an accumulated vectorized gradient covariance with both regularized row- and column-Gram Kronecker preconditioners
Book citation: book/research/Source.json#/key_lemmas/9/proof/1
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem regularized_inv_rank_vecMulVec_sum_le_kronecker_gram_bounds
    {α : Type u} {ι : Type v} {κ : Type w}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : α → Matrix ι κ ℝ) (r : ℕ) (epsilon : ℝ)
    (hr : 0 < r) (hrank : ∀ t : α, (G t).rank ≤ r) :
    let A : Matrix ι ι ℝ :=
      epsilon • (1 : Matrix ι ι ℝ) + ∑ t : α, Matrix.leftGram (G t)
    let B : Matrix κ κ ℝ :=
      epsilon • (1 : Matrix κ κ ℝ) + ∑ t : α, Matrix.rightGram (G t)
    let M : Matrix (ι × κ) (ι × κ) ℝ :=
      epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
        (r : ℝ)⁻¹ •
          ∑ t : α, Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))
    M ≤ (1 : Matrix ι ι ℝ) ⊗ₖ B ∧ M ≤ A ⊗ₖ (1 : Matrix κ κ ℝ) := by
  classical
  intro A B M
  have hsum_right :
      (r : ℝ)⁻¹ •
          (∑ t : α,
            Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))) ≤
        ∑ t : α, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.rightGram (G t) := by
    simpa only [Finset.smul_sum] using
      Finset.sum_le_sum (fun t _ht =>
        (Matrix.inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams
          (G t) r hr (hrank t)).1)
  have hsum_left :
      (r : ℝ)⁻¹ •
          (∑ t : α,
            Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))) ≤
        ∑ t : α, Matrix.leftGram (G t) ⊗ₖ (1 : Matrix κ κ ℝ) := by
    simpa only [Finset.smul_sum] using
      Finset.sum_le_sum (fun t _ht =>
        (Matrix.inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams
          (G t) r hr (hrank t)).2)
  have ridge_eq_one_kronecker :
      epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) =
        (1 : Matrix ι ι ℝ) ⊗ₖ (epsilon • (1 : Matrix κ κ ℝ)) := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        simp [Matrix.kroneckerMap_apply]
      · simp [Matrix.kroneckerMap_apply, hjl]
    · simp [Matrix.kroneckerMap_apply, hik]
  have ridge_eq_kronecker_one :
      epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) =
        (epsilon • (1 : Matrix ι ι ℝ)) ⊗ₖ (1 : Matrix κ κ ℝ) := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        simp [Matrix.kroneckerMap_apply]
      · simp [Matrix.kroneckerMap_apply, hjl]
    · simp [Matrix.kroneckerMap_apply, hik]
  have one_kronecker_sum :
      (1 : Matrix ι ι ℝ) ⊗ₖ (∑ t : α, Matrix.rightGram (G t)) =
        ∑ t : α, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.rightGram (G t) := by
    ext ij kl
    simp_rw [Matrix.sum_apply, Matrix.kroneckerMap_apply]
    rw [Matrix.sum_apply, Finset.mul_sum]
  have sum_kronecker_one :
      (∑ t : α, Matrix.leftGram (G t)) ⊗ₖ (1 : Matrix κ κ ℝ) =
        ∑ t : α, Matrix.leftGram (G t) ⊗ₖ (1 : Matrix κ κ ℝ) := by
    ext ij kl
    simp_rw [Matrix.sum_apply, Matrix.kroneckerMap_apply]
    rw [Matrix.sum_apply, Finset.sum_mul]
  have hright_rewrite :
      (1 : Matrix ι ι ℝ) ⊗ₖ B =
        epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
          ∑ t : α, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.rightGram (G t) := by
    calc
      (1 : Matrix ι ι ℝ) ⊗ₖ B =
          (1 : Matrix ι ι ℝ) ⊗ₖ
            (epsilon • (1 : Matrix κ κ ℝ) +
              ∑ t : α, Matrix.rightGram (G t)) := rfl
      _ = (1 : Matrix ι ι ℝ) ⊗ₖ (epsilon • (1 : Matrix κ κ ℝ)) +
            (1 : Matrix ι ι ℝ) ⊗ₖ
              (∑ t : α, Matrix.rightGram (G t)) := by
          rw [Matrix.kronecker_add]
      _ = epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
            ∑ t : α, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.rightGram (G t) := by
          rw [← ridge_eq_one_kronecker, one_kronecker_sum]
  have hleft_rewrite :
      A ⊗ₖ (1 : Matrix κ κ ℝ) =
        epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
          ∑ t : α, Matrix.leftGram (G t) ⊗ₖ (1 : Matrix κ κ ℝ) := by
    calc
      A ⊗ₖ (1 : Matrix κ κ ℝ) =
          (epsilon • (1 : Matrix ι ι ℝ) +
              ∑ t : α, Matrix.leftGram (G t)) ⊗ₖ
            (1 : Matrix κ κ ℝ) := rfl
      _ = (epsilon • (1 : Matrix ι ι ℝ)) ⊗ₖ (1 : Matrix κ κ ℝ) +
            (∑ t : α, Matrix.leftGram (G t)) ⊗ₖ
              (1 : Matrix κ κ ℝ) := by
          rw [Matrix.add_kronecker]
      _ = epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
            ∑ t : α, Matrix.leftGram (G t) ⊗ₖ (1 : Matrix κ κ ℝ) := by
          rw [← ridge_eq_kronecker_one, sum_kronecker_one]
  constructor
  · rw [hright_rewrite]
    change
      epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
          (r : ℝ)⁻¹ •
            (∑ t : α,
              Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))) ≤
        epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
          ∑ t : α, (1 : Matrix ι ι ℝ) ⊗ₖ Matrix.rightGram (G t)
    exact add_le_add (le_refl _) hsum_right
  · rw [hleft_rewrite]
    change
      epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
          (r : ℝ)⁻¹ •
            (∑ t : α,
              Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))) ≤
        epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
          ∑ t : α, Matrix.leftGram (G t) ⊗ₖ (1 : Matrix κ κ ℝ)
    exact add_le_add (le_refl _) hsum_left

end Matrix


open scoped ComplexOrder Kronecker

namespace Matrix.IsHermitian


-- Generalization plan (G0):
-- concept/name: factorwise spectral decomposition of a Hermitian
--   matrix Kronecker product; orig was
--   `kronecker_unitary_diagonalization_for_psd`
-- generality used: arbitrary `RCLike` scalars and arbitrary finite index types
--   with decidable equality; no optimization, measure, convexity, or oracle
--   assumptions are used
-- portable call pattern: spectral matrix-power and tensor-preconditioner proofs
--   diagonalize a binary Kronecker product while changing both finite factor
--   spaces and both Hermitian factor matrices
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it packages the nontrivial compatibility of two spectral
--   decompositions with Kronecker multiplication, adjoints, and diagonals
-- coverage search: symbol and semantic searches for Kronecker spectral
--   decomposition found `Matrix.IsHermitian.spectral_theorem`,
--   `Matrix.mul_kronecker_mul`, `Matrix.conjTranspose_kronecker`, and
--   `Matrix.diagonal_kronecker_diagonal` as separate ingredients, but no
--   Mathlib or SOptLib declaration with the combined product-eigenvalue result
-- minimal hypotheses: finite decidable index types are required by Mathlib's
--   chosen eigenbasis and diagonal APIs, and Hermitian factor matrices are the
--   exact hypothesis required by the factor spectral decompositions

/-- The Kronecker product of two Hermitian matrices is diagonalized
in the Kronecker product of their chosen eigenbases, with pairwise products of
the factor eigenvalues on the diagonal.

Layer: Glue | Gap: Level 1 (Kronecker compatibility of finite-matrix spectral decompositions)
Proof: expand each factor with `Matrix.IsHermitian.spectral_theorem`, distribute Kronecker products over matrix multiplication, and use compatibility with adjoints and diagonal matrices.
Source: Mathlib finite Hermitian matrix spectral theory and matrix Kronecker-product algebra
Used in: spectral matrix-power and tensor-preconditioner proofs that identify a power of a Kronecker-assembled Hermitian preconditioner with the Kronecker product of the powered factors
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 3(iii) -/
theorem kronecker_spectral_decomposition
    {𝕜 : Type w} [RCLike 𝕜]
    {m : Type u} [Fintype m] [DecidableEq m]
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ⊗ₖ B =
      ((hA.eigenvectorUnitary : Matrix m m 𝕜) ⊗ₖ
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) *
        Matrix.diagonal
          (fun ij : m × n =>
            RCLike.ofReal (hA.eigenvalues ij.1) *
              RCLike.ofReal (hB.eigenvalues ij.2)) *
        star
          ((hA.eigenvectorUnitary : Matrix m m 𝕜) ⊗ₖ
            (hB.eigenvectorUnitary : Matrix n n 𝕜)) := by
  classical
  let UA : Matrix m m 𝕜 := hA.eigenvectorUnitary
  let UB : Matrix n n 𝕜 := hB.eigenvectorUnitary
  let DA : Matrix m m 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let DB : Matrix n n 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have hAspec : A = UA * DA * star UA := by
    simpa [UA, DA, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hBspec : B = UB * DB * star UB := by
    simpa [UB, DB, Unitary.conjStarAlgAut_apply] using hB.spectral_theorem
  calc
    A ⊗ₖ B = (UA * DA * star UA) ⊗ₖ (UB * DB * star UB) := by
      rw [hAspec, hBspec]
    _ = ((UA ⊗ₖ UB) * (DA ⊗ₖ DB)) * (star UA ⊗ₖ star UB) := by
      rw [Matrix.mul_assoc UA DA (star UA), Matrix.mul_assoc UB DB (star UB)]
      rw [Matrix.mul_kronecker_mul UA (DA * star UA) UB (DB * star UB)]
      rw [Matrix.mul_kronecker_mul DA (star UA) DB (star UB)]
      rw [Matrix.mul_assoc]
    _ = ((UA ⊗ₖ UB) * (DA ⊗ₖ DB)) * star (UA ⊗ₖ UB) := by
      have hstar : star (UA ⊗ₖ UB) = star UA ⊗ₖ star UB := by
        simpa only [Matrix.star_eq_conjTranspose] using
          (Matrix.conjTranspose_kronecker UA UB)
      rw [hstar]
    _ = (UA ⊗ₖ UB) * (DA ⊗ₖ DB) * star (UA ⊗ₖ UB) := by
      rw [Matrix.mul_assoc]
    _ = (UA ⊗ₖ UB) *
          Matrix.diagonal
            (fun ij : m × n =>
              RCLike.ofReal (hA.eigenvalues ij.1) *
                RCLike.ofReal (hB.eigenvalues ij.2)) *
          star (UA ⊗ₖ UB) := by
      simp only [DA, DB, Matrix.diagonal_kronecker_diagonal,
        Function.comp_apply]

end Matrix.IsHermitian


-- Generalization plan (G0):
-- concept/name: polynomial algebra evaluation on a diagonal matrix; orig was
--   `polynomial_aeval_diagonal`
-- generality used: arbitrary commutative semiring and arbitrary finite decidable index type;
--   no order, topology, star, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: spectral matrix proofs evaluate an interpolating or approximating
--   polynomial on a diagonalized operator while the index type, diagonal entries, coefficient
--   semiring, and polynomial vary
-- counterargument checked: not paper-local or a pure rename; Mathlib provides the diagonal
--   algebra homomorphism and polynomial-evaluation naturality separately, but no declaration
--   packaging their pointwise diagonal conclusion
-- coverage search: queries "polynomial evaluation diagonal matrix equals diagonal pointwise
--   evaluation", "aeval diagonal matrix polynomial", and the exact component names found
--   `Polynomial.aeval_algHom_apply`, `Polynomial.aeval_pi_apply`, and
--   `Matrix.diagonalAlgHom`, but no full Mathlib or SOptLib theorem
-- minimal hypotheses: `CommSemiring R` supports polynomial algebra evaluation, while `Fintype`
--   and `DecidableEq` supply the square-matrix semiring and diagonal algebra homomorphism

/-- Evaluating a polynomial on a finite diagonal matrix applies that polynomial to every
diagonal entry and leaves all off-diagonal entries zero.

Layer: Glue | Gap: Level 1 (polynomial evaluation through the diagonal matrix algebra homomorphism)
Proof: transport polynomial evaluation through `Matrix.diagonalAlgHom` using `Polynomial.aeval_algHom_apply`, then identify tuple evaluation coordinatewise with `Polynomial.aeval_pi_apply`.
Source: Mathlib polynomial algebra-map evaluation and finite matrix diagonal algebra homomorphisms
Used in: spectral functional-calculus proofs that replace a polynomial of a diagonal eigenvalue matrix by pointwise scalar evaluations before returning to a unitary basis
Book citation: book/research/Source.json#/algorithm_spec
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
@[simp] theorem Matrix.polynomial_aeval_diagonal
    {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (d : ι → R) (p : Polynomial R) :
    Polynomial.aeval (Matrix.diagonal d : Matrix ι ι R) p =
      Matrix.diagonal (fun i : ι => p.eval (d i)) := by
  calc
    Polynomial.aeval (Matrix.diagonal d : Matrix ι ι R) p =
        (Matrix.diagonalAlgHom R : (ι → R) →ₐ[R] Matrix ι ι R)
          (Polynomial.aeval d p) := by
      simpa using
        (Polynomial.aeval_algHom_apply
          (f := (Matrix.diagonalAlgHom R : (ι → R) →ₐ[R] Matrix ι ι R))
          (x := d) (p := p))
    _ = Matrix.diagonal (fun i : ι => p.eval (d i)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Polynomial.aeval_pi_apply]
      · simp [hij]


-- Generalization plan (G0):
-- concept/name: coordinatewise real CFC powers of diagonal matrices; orig was
--   `cfc_rpow_diagonal_nonneg`, renamed `Matrix.cfc_rpow_diagonal`
-- generality used: arbitrary finite decidable index type, real diagonal entries and exponent,
--   with no sign restriction on the diagonal; no algorithm, measure, or optimization data
-- portable call pattern: spectral adaptive-preconditioner and matrix-analysis proofs evaluate a
--   CFC real power after diagonalization while the finite index, eigenvalues, and exponent vary
-- counterargument checked: not paper-local or a pure wrapper; the proof combines spectrum
--   identification, finite interpolation, CFC congruence, and polynomial diagonal evaluation
-- coverage search: queries "continuous functional calculus real power diagonal matrix entrywise
--   nonnegative" and "cfc rpow diagonal of nonnegative entries equality" found `CFC.rpow`,
--   `CFC.rpow_eq_cfc_real`, and `Matrix.polynomial_aeval_diagonal`, but no theorem with this result
-- minimal hypotheses: a real diagonal matrix is self-adjoint without a sign restriction

/-- The real continuous-functional-calculus power of a finite diagonal matrix is
the diagonal matrix of the entrywise real powers.

Layer: Glue | Gap: Level 1 (coordinatewise CFC real powers of diagonal matrices)
Proof: interpolate the scalar real-power function on the finite diagonal spectrum, replace the CFC by polynomial evaluation using spectral congruence, and evaluate that polynomial coordinatewise.
Source: Mathlib finite Hermitian matrix spectra, continuous functional calculus congruence, Lagrange interpolation, and polynomial evaluation on diagonal matrices
Used in: spectral adaptive-preconditioner proofs that evaluate fractional powers of diagonal eigenvalue matrices and diagonal accumulator matrices coordinatewise
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem Matrix.cfc_rpow_diagonal
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (d : iota → ℝ) (s : ℝ) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.diagonal d : Matrix iota iota ℝ) =
      Matrix.diagonal (fun i : iota => (d i) ^ s) := by
  classical
  let D : Matrix iota iota ℝ := Matrix.diagonal d
  let q : Polynomial ℝ :=
    Lagrange.interpolate (Finset.univ : Finset {x : ℝ // x ∈ Set.range d})
      (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
      (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ) ^ s)
  have hD : IsSelfAdjoint D := by
    change D.IsHermitian
    simpa only [D] using
      Matrix.isHermitian_diagonal_of_self_adjoint d (IsSelfAdjoint.all d)
  have hinj : Set.InjOn
      (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
      ((Finset.univ : Finset {x : ℝ // x ∈ Set.range d}) :
        Set {x : ℝ // x ∈ Set.range d}) := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have hq_eval : ∀ i : iota, q.eval (d i) = (d i) ^ s := by
    intro i
    have hnode := Lagrange.eval_interpolate_at_node
      (s := (Finset.univ : Finset {x : ℝ // x ∈ Set.range d}))
      (v := fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
      (r := fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ) ^ s)
      hinj (Finset.mem_univ (⟨d i, ⟨i, rfl⟩⟩ : {x : ℝ // x ∈ Set.range d}))
    simpa [q] using hnode
  have hspec : spectrum ℝ D = Set.range d := by
    change spectrum ℝ (Matrix.diagonal d) = Set.range d
    exact spectrum_diagonal (R := ℝ) (n := iota) (d := d)
  have hfg : (spectrum ℝ D).EqOn (fun x : ℝ => x ^ s) q.eval := by
    rw [hspec]
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact (hq_eval i).symm
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.diagonal d : Matrix iota iota ℝ) =
        cfc (R := ℝ) (p := IsSelfAdjoint) q.eval D := by
          simpa [D] using
            (cfc_congr (R := ℝ) (A := Matrix iota iota ℝ)
              (p := IsSelfAdjoint) (a := D) hfg)
    _ = Polynomial.aeval D q := by
          simpa using
            (cfc_polynomial (R := ℝ) (A := Matrix iota iota ℝ)
              (p := IsSelfAdjoint) q D (ha := hD))
    _ = Matrix.diagonal (fun i : iota => (d i) ^ s) := by
          rw [Matrix.polynomial_aeval_diagonal]
          ext i j
          by_cases hij : i = j
          · subst j
            simp [hq_eval]
          · simp [hij]


-- Generalization plan (G0):
-- concept/name: equivariance of finite-matrix continuous functional calculus under
--   unitary conjugation; orig was cfc_unitary_conj, retained as Matrix.cfc_unitary_conj
-- generality used: arbitrary finite index type, arbitrary RCLike scalar type, arbitrary
--   real scalar function, unitary square matrix, and self-adjoint square matrix
-- portable call pattern: finite-dimensional spectral proofs transport a scalar function
--   through a unitary diagonalization while the index type, function, unitary, and matrix vary
-- counterargument checked: not paper-local or a pure rename; Mathlib provides generic CFC
--   naturality, but callers otherwise must rebuild continuity and self-adjointness obligations
--   for the conjugation automorphism and prove arbitrary-function continuity on a finite spectrum
-- coverage search: queried CFC/unitary/conjugation equality and inspected
--   StarAlgHom.map_cfc, Unitary.conjStarAlgAut, and unitary spectrum lemmas; these cover
--   components only, and neither Mathlib nor SOptLib has this finite-matrix specialization
-- minimal hypotheses: all already minimal for arbitrary f; self-adjointness is required by
--   the real CFC, while finiteness makes every f continuous on the matrix spectrum

/-- Continuous functional calculus commutes with conjugation of a finite self-adjoint matrix
over an `RCLike` scalar type by a unitary matrix.

Layer: Glue | Gap: Level 1 (finite-matrix CFC equivariance under unitary conjugation)
Proof: apply `StarAlgHom.map_cfc` to the unitary conjugation star-algebra automorphism; finite Hermitian spectral theory supplies continuity of the arbitrary scalar function on the spectrum, while unitary congruence preserves self-adjointness.
Source: Mathlib continuous-functional-calculus naturality, unitary inner star-algebra automorphisms, and finite Hermitian matrix spectra
Used in: spectral matrix-power and adaptive-preconditioner proofs that move a scalar functional calculus through a unitary diagonalization
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem Matrix.cfc_unitary_conj
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (U : unitary (Matrix ι ι 𝕜)) (D : Matrix ι ι 𝕜)
    (hD : IsSelfAdjoint D) :
    cfc (R := ℝ) (p := IsSelfAdjoint) f
        (((U : Matrix ι ι 𝕜) * D) * star (U : Matrix ι ι 𝕜)) =
      ((U : Matrix ι ι 𝕜) *
          cfc (R := ℝ) (p := IsSelfAdjoint) f D) *
        star (U : Matrix ι ι 𝕜) := by
  classical
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι 𝕜) U
  have hcontφ : Continuous (φ : Matrix ι ι 𝕜 → Matrix ι ι 𝕜) := by
    simpa [φ, Unitary.conjStarAlgAut_apply] using
      (show Continuous (fun X : Matrix ι ι 𝕜 =>
        (U : Matrix ι ι 𝕜) * X * star (U : Matrix ι ι 𝕜)) from by fun_prop)
  have hfD : ContinuousOn f (spectrum ℝ D) := by
    have hfin : (spectrum ℝ D).Finite := by
      rw [(show Matrix.IsHermitian D from hD).spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hφD : IsSelfAdjoint (φ D) := by
    change IsSelfAdjoint (((U : Matrix ι ι 𝕜) * D) * star (U : Matrix ι ι 𝕜))
    exact (Matrix.isHermitian_mul_mul_conjTranspose
      (U : Matrix ι ι 𝕜) (show Matrix.IsHermitian D from hD)).isSelfAdjoint
  have hmap := (φ : Matrix ι ι 𝕜 →⋆ₐ[ℝ] Matrix ι ι 𝕜).map_cfc
      f D (hf := hfD) (hφ := hcontφ) (ha := hD) (hφa := hφD)
  simpa [φ, Unitary.conjStarAlgAut_apply] using hmap.symm


-- Generalization plan (G0):
-- concept/name: real CFC power in a supplied unitary eigenbasis; orig was
--   `cfc_rpow_eq_of_unitary_diagonalization`, retained as
--   `Matrix.cfc_rpow_eq_of_unitary_diagonalization`
-- generality used: arbitrary finite decidable index type, real square matrix, real exponent,
--   supplied unitary matrix and real diagonal values; no positivity or optimization assumptions
-- portable call pattern: spectral adaptive-gradient and matrix-function proofs evaluate a real
--   power in a caller-supplied eigenbasis while the matrix, basis, eigenvalues, and exponent vary
-- counterargument checked: not paper-local or a pure rename; it composes CFC equivariance with
--   coordinatewise diagonal evaluation into the reusable supplied-diagonalization contract
-- coverage search: queries "real continuous functional calculus power unitary diagonalization
--   equality nonnegative eigenvalues", "CFC rpow unitary conjugation diagonal matrix explicit
--   eigenvalues", and LeanSearch's equivalent semantic query found `Matrix.IsHermitian.cfcAux_apply`,
--   `Matrix.cfc_unitary_conj`, and `Matrix.cfc_rpow_diagonal`, but no full covering theorem
-- minimal hypotheses: source assumptions `C.PosSemidef` and pointwise nonnegativity of the
--   diagonal are unused and omitted; the supplied real unitary diagonalization is sufficient

/-- Applying a real power by continuous functional calculus to a real matrix with a supplied
unitary diagonalization applies that power coordinatewise to the supplied diagonal values.

Layer: Glue | Gap: Level 1 (CFC real power in a supplied unitary eigenbasis)
Proof: rewrite by the supplied diagonalization, move the CFC through unitary conjugation using
  `Matrix.cfc_unitary_conj`, and evaluate the diagonal CFC with `Matrix.cfc_rpow_diagonal`.
Source: Mathlib finite Hermitian matrix continuous functional calculus and unitary spectral theory
Used in: spectral adaptive-preconditioner proofs that evaluate fractional positive and negative
  matrix powers in an explicitly supplied eigenbasis
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Algorithms 1--3 -/
theorem Matrix.cfc_rpow_eq_of_unitary_diagonalization
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (C : Matrix iota iota Real) (s : Real)
    (U : unitary (Matrix iota iota Real)) (lambda : iota → Real)
    (hdiag : C = (U : Matrix iota iota Real) * Matrix.diagonal lambda *
      star (U : Matrix iota iota Real)) :
    cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s) C =
      (U : Matrix iota iota Real) * Matrix.diagonal (fun i => (lambda i) ^ s) *
        star (U : Matrix iota iota Real) := by
  have hlambda : IsSelfAdjoint (Matrix.diagonal lambda : Matrix iota iota Real) := by
    change (Matrix.diagonal lambda : Matrix iota iota Real).IsHermitian
    exact Matrix.isHermitian_diagonal_of_self_adjoint lambda (IsSelfAdjoint.all lambda)
  rw [hdiag]
  calc
    cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
        (((U : Matrix iota iota Real) * Matrix.diagonal lambda) *
          star (U : Matrix iota iota Real)) =
        ((U : Matrix iota iota Real) *
          cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
            (Matrix.diagonal lambda)) * star (U : Matrix iota iota Real) := by
      exact Matrix.cfc_unitary_conj (fun x : Real => x ^ s) U
        (Matrix.diagonal lambda) hlambda
    _ = (U : Matrix iota iota Real) * Matrix.diagonal (fun i => (lambda i) ^ s) *
        star (U : Matrix iota iota Real) := by
      rw [Matrix.cfc_rpow_diagonal]


open scoped Kronecker

namespace Matrix


-- Generalization plan (G0):
-- concept/name: factorization of a diagonal matrix of real powers of pairwise
--   products as a Kronecker product of powered diagonal matrices; orig was
--   `kronecker_diagonal_power_rewrite`
-- generality used: arbitrary index types with decidable equality, real-valued
--   families, a real exponent, and pointwise nonnegativity; no finiteness,
--   measure, convexity, smoothness, oracle, or optimization assumptions are used
-- portable call pattern: spectral functional-calculus proofs for Kronecker
--   products change the two eigenvalue families and exponent while using the
--   same factorization of the powered spectral diagonal
-- counterargument checked: the result is not a pure rename of Mathlib's
--   diagonal-Kronecker theorem; it composes that matrix identity with the
--   nonnegative real-power product law, a recurring spectral proof boundary
-- coverage search: symbol and semantic searches for "diagonal real powers of
--   pairwise products" and "Matrix diagonal Kronecker diagonal equality" found
--   `Matrix.diagonal_kronecker_diagonal` and `Real.mul_rpow`, but no declaration
--   stating their composed powered-diagonal factorization
-- minimal hypotheses: `Fintype` is unnecessary; `DecidableEq` is required by
--   diagonal matrices and pointwise nonnegativity is exactly what
--   `Real.mul_rpow` consumes

/-- The diagonal of real powers of pairwise products of two nonnegative families
factors as the Kronecker product of their powered diagonal matrices.

Layer: Glue | Gap: Level 0 (diagonal Kronecker factorization of real powers)
Proof: rewrite the Kronecker product of diagonal matrices with `Matrix.diagonal_kronecker_diagonal`, then apply `Real.mul_rpow` pointwise using the two nonnegativity hypotheses.
Source: Mathlib real-power product laws and matrix Kronecker-product diagonal API
Used in: spectral functional-calculus proofs that distribute a real matrix power across a Kronecker product by factoring the powered eigenvalue diagonal
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 3(iii) -/
theorem diagonal_rpow_mul_eq_kronecker_diagonal_rpow
    {ι : Type u} {κ : Type v} [DecidableEq ι] [DecidableEq κ]
    (lam : ι → ℝ) (mu : κ → ℝ) (s : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j) :
    diagonal (fun ij : ι × κ => (lam ij.1 * mu ij.2) ^ s) =
      diagonal (fun i : ι => (lam i) ^ s) ⊗ₖ
        diagonal (fun j : κ => (mu j) ^ s) := by
  rw [diagonal_kronecker_diagonal]
  congr 1
  funext ij
  exact Real.mul_rpow (hlam ij.1) (hmu ij.2)

end Matrix


open scoped ComplexOrder Kronecker

namespace Matrix


-- Generalization plan (G0):
-- concept/name: compatibility of real continuous-functional-calculus powers
--   with Kronecker products of positive-semidefinite matrices; orig was
--   `psdMatrixPower_kronecker`, renamed `Matrix.cfc_rpow_kronecker`
-- generality used: arbitrary `RCLike` coefficient fields, finite decidable
--   index types, two positive-semidefinite square matrices, and an arbitrary
--   real exponent; no algorithm state, measure, convexity, smoothness, or
--   oracle assumptions
-- portable call pattern: matrix AdaGrad, Shampoo, and tensor-preconditioner
--   proofs change the two finite coordinate types, PSD factors, and exponent
--   while distributing the same CFC power through a Kronecker product
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes factorwise spectral decomposition, CFC evaluation in
--   a unitary eigenbasis, real-power multiplicativity on nonnegative
--   eigenvalues, and Kronecker multiplication into one reusable theorem
-- coverage search: symbol and semantic searches for "continuous functional
--   calculus real power Kronecker product positive semidefinite matrices
--   equality" found Mathlib's `CFC.rpow_eq_rpow_prod` for product algebras and
--   the staged spectral and powered-diagonal component lemmas, but no theorem
--   for matrix Kronecker products with this conclusion
-- minimal hypotheses: positive semidefiniteness supplies Hermitian spectral
--   decompositions and nonnegative eigenvalues; finite decidable index types
--   are required by the finite-matrix eigenbasis and multiplication APIs

/-- The real continuous-functional-calculus power of a Kronecker product of
two finite positive-semidefinite matrices over an `RCLike` field is the
Kronecker product of their corresponding powers.

Layer: Glue | Gap: Level 2 (CFC real powers of positive-semidefinite Kronecker products)
Proof: diagonalize the Kronecker product in the tensor product of the factor eigenbases, evaluate the CFC power on that diagonal, factor the powered eigenvalue diagonal using nonnegativity, and reassemble the two factor powers.
Source: Mathlib finite Hermitian spectral theory, matrix Kronecker-product algebra, and scalar real-power multiplicativity on nonnegative inputs
Used in: matrix and tensor adaptive-preconditioner proofs that separate a fractional power of a Kronecker-assembled PSD accumulator into independently powered mode factors
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 3(iii) -/
theorem cfc_rpow_kronecker
    {𝕜 : Type w} [RCLike 𝕜]
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι 𝕜) (B : Matrix κ κ 𝕜) (s : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (A ⊗ₖ B) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A ⊗ₖ
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) B := by
  classical
  let UAunit : unitary (Matrix ι ι 𝕜) := hA.1.eigenvectorUnitary
  let UBunit : unitary (Matrix κ κ 𝕜) := hB.1.eigenvectorUnitary
  let UAB : unitary (Matrix (ι × κ) (ι × κ) 𝕜) :=
    ⟨(UAunit : Matrix ι ι 𝕜) ⊗ₖ (UBunit : Matrix κ κ 𝕜),
      Matrix.kronecker_mem_unitary UAunit.property UBunit.property⟩
  let lam : ι × κ → ℝ :=
    fun ij => hA.1.eigenvalues ij.1 * hB.1.eigenvalues ij.2
  have hdiag :
      A ⊗ₖ B =
        (UAB : Matrix (ι × κ) (ι × κ) 𝕜) *
          Matrix.diagonal (RCLike.ofReal ∘ lam) *
          star (UAB : Matrix (ι × κ) (ι × κ) 𝕜) := by
    have hd :
        (Matrix.diagonal (RCLike.ofReal ∘ lam) :
          Matrix (ι × κ) (ι × κ) 𝕜) =
          Matrix.diagonal (fun ij : ι × κ =>
            RCLike.ofReal (hA.1.eigenvalues ij.1) *
              RCLike.ofReal (hB.1.eigenvalues ij.2)) := by
      congr 1
      funext ij
      exact RCLike.ofReal_mul _ _
    rw [hd]
    simpa [UAB, UAunit, UBunit] using
      Matrix.IsHermitian.kronecker_spectral_decomposition A B hA.1 hB.1
  have hlam : ∀ ij : ι × κ, 0 ≤ lam ij := by
    intro ij
    exact mul_nonneg (hA.eigenvalues_nonneg ij.1) (hB.eigenvalues_nonneg ij.2)
  let scalarCast : ℝ →⋆ₐ[ℝ] 𝕜 :=
    StarAlgHom.mk RCLike.ofRealAm (by intro x; simp)
  let matrixCast : Matrix (ι × κ) (ι × κ) ℝ →⋆ₐ[ℝ]
      Matrix (ι × κ) (ι × κ) 𝕜 :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let Dreal : Matrix (ι × κ) (ι × κ) ℝ := Matrix.diagonal lam
  let D : Matrix (ι × κ) (ι × κ) 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ lam)
  have hDreal : IsSelfAdjoint Dreal := by
    change Dreal.IsHermitian
    simpa only [Dreal] using
      Matrix.isHermitian_diagonal_of_self_adjoint lam (IsSelfAdjoint.all lam)
  have hD : IsSelfAdjoint D := by
    change D.IsHermitian
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    exact funext fun ij => by simp [Function.comp_apply]
  have hcastD : matrixCast Dreal = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [matrixCast, scalarCast, Dreal, D, Function.comp_def]
    · simp [matrixCast, scalarCast, Dreal, D, Function.comp_def, hij]
  have hcontinuous : Continuous matrixCast := by
    change Continuous (fun M : Matrix (ι × κ) (ι × κ) ℝ =>
      Matrix.map M scalarCast)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun M : Matrix (ι × κ) (ι × κ) ℝ =>
      RCLike.ofReal (M i j))
    fun_prop
  have hf : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ Dreal) := by
    have hfinite : (spectrum ℝ Dreal).Finite := by
      rw [(show Matrix.IsHermitian Dreal from hDreal).spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfinite.continuousOn _
  have hmap := matrixCast.map_cfc (fun x : ℝ => x ^ s) Dreal
    (hf := hf) (hφ := hcontinuous) (ha := hDreal) (hφa := hcastD ▸ hD)
  have hcfcD :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) D =
        Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) := by
    rw [← hcastD, ← hmap, Matrix.cfc_rpow_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [matrixCast, scalarCast, Function.comp_def]
    · simp [matrixCast, scalarCast, Function.comp_def, hij]
  rw [hdiag]
  rw [Matrix.cfc_unitary_conj (fun x : ℝ => x ^ s) UAB D hD]
  rw [hcfcD, hA.1.cfc_eq, hB.1.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_apply]
  let UA : Matrix ι ι 𝕜 := hA.1.eigenvectorUnitary
  let UB : Matrix κ κ 𝕜 := hB.1.eigenvectorUnitary
  let DApow : Matrix ι ι 𝕜 :=
    Matrix.diagonal (fun i : ι => RCLike.ofReal (hA.1.eigenvalues i ^ s))
  let DBpow : Matrix κ κ 𝕜 :=
    Matrix.diagonal (fun j : κ => RCLike.ofReal (hB.1.eigenvalues j ^ s))
  have hdiagpow :
      Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) =
      DApow ⊗ₖ DBpow := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext ij
    simp only [lam, DApow, DBpow, Function.comp_apply]
    rw [Real.mul_rpow (hA.eigenvalues_nonneg ij.1)
      (hB.eigenvalues_nonneg ij.2)]
    exact RCLike.ofReal_mul _ _
  calc
    (UAB : Matrix (ι × κ) (ι × κ) 𝕜) *
          Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) *
          star (UAB : Matrix (ι × κ) (ι × κ) 𝕜) =
        (UA ⊗ₖ UB) *
          Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) *
          star (UA ⊗ₖ UB) := by
      simp [UAB, UAunit, UBunit, UA, UB]
    _ = (UA ⊗ₖ UB) * (DApow ⊗ₖ DBpow) * star (UA ⊗ₖ UB) := by
      rw [hdiagpow]
    _ = ((UA ⊗ₖ UB) * (DApow ⊗ₖ DBpow)) *
          (star UA ⊗ₖ star UB) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
        Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    _ = (UA * DApow * star UA) ⊗ₖ (UB * DBpow * star UB) := by
      rw [Matrix.mul_assoc UA DApow (star UA),
        Matrix.mul_assoc UB DBpow (star UB)]
      rw [Matrix.mul_kronecker_mul UA (DApow * star UA) UB (DBpow * star UB)]
      rw [Matrix.mul_kronecker_mul DApow (star UA) DBpow (star UB)]
      rw [Matrix.mul_assoc]
    _ = ((hA.1.eigenvectorUnitary : Matrix ι ι 𝕜) *
          Matrix.diagonal
            (fun i : ι => RCLike.ofReal (hA.1.eigenvalues i ^ s)) *
          star (hA.1.eigenvectorUnitary : Matrix ι ι 𝕜)) ⊗ₖ
        ((hB.1.eigenvectorUnitary : Matrix κ κ 𝕜) *
          Matrix.diagonal
            (fun j : κ => RCLike.ofReal (hB.1.eigenvalues j ^ s)) *
          star (hB.1.eigenvectorUnitary : Matrix κ κ 𝕜)) := by
      simp [UA, UB, DApow, DBpow]

end Matrix


-- Generalization plan (G0):
-- concept/name: ordered `List.ofFn` product after removing an identity-valued
--   coordinate; orig was `orderedMatrixProduct_delete_one`
-- generality used: arbitrary carrier with multiplication, an identity, and a lawful
--   left-identity instance; no associativity, right identity, matrix, order, topology,
--   measure, convexity, or oracle assumptions
-- portable call pattern: ordered operator-product proofs remove a factor known to
--   be the identity while the monoid, finite family, and removed position vary
-- counterargument checked: this is not a pure rename or caller-side expression; it
--   packages the distinct removal-oriented contract and its equality hypothesis
-- coverage search: searches for "ordered list product of function remove coordinate
--   equal one preserves product monoid" and "List prod ofFn removeNth eq one" found
--   `Fin.mul_prod_removeNth` only for commutative products and
--   `Fin.partialProd_contractNth` for adjacent-factor contraction; neither covers
--   deletion from an order-sensitive `List.ofFn` product in an arbitrary monoid
-- minimal hypotheses: multiplication, one, lawful left identity, and the pointwise
--   equality `A p = 1`; associativity and right identity are not used

/-- Removing an identity-valued coordinate preserves an ordered finite-family product.

Layer: Glue | Gap: Level 1 (identity deletion from an ordered finite-family product)
Proof: induct on the family length, split the removed position into zero or successor,
  delete a leading identity with `List.prod_one_cons`, and recurse on the tail.
Source: Mathlib finite tuples and noncommutative list products
Used in: finite-family geometric-mean induction after a zero exponent turns one
  preconditioner factor into the identity without requiring the other factors to commute
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, finite-family geometric-mean induction -/
@[simp] theorem List.prod_ofFn_removeNth_of_eq_one {M : Type*} [Mul M] [One M]
    [Std.LawfulLeftIdentity (fun x y : M => x * y) 1] {q : Nat}
    (A : Fin (q + 1) → M) (p : Fin (q + 1)) (hp : A p = 1) :
    (List.ofFn A).prod = (List.ofFn (p.removeNth A)).prod := by
  induction q with
  | zero =>
      have hp0 : p = 0 := Fin.eq_zero p
      subst p
      rw [Fin.removeNth_zero, List.ofFn_succ, hp]
      exact List.prod_one_cons
  | succ q ih =>
      induction p using Fin.cases with
      | zero =>
          rw [Fin.removeNth_zero, List.ofFn_succ, hp]
          exact List.prod_one_cons
      | succ p =>
          have hremove :
              List.ofFn (p.succ.removeNth A) =
                A 0 :: List.ofFn (p.removeNth fun i => A i.succ) := by
            rw [List.ofFn_succ]
            simp [Fin.removeNth]
            rfl
          rw [List.ofFn_succ, hremove, List.prod_cons, List.prod_cons,
            ih (fun i => A i.succ) p (by simpa using hp)]


-- Generalization plan (G0):
-- concept/name: scalar-identity shift of a supplied unitary diagonalization; orig was
--   matrix_add_nnnreal_one_diagonalization
-- generality used: arbitrary finite decidable index type, square matrix over a commutative
--   star semiring, supplied unitary diagonalization, arbitrary scalar; no positivity or spectral
--   assumptions
-- portable call pattern: spectral regularization proofs for adaptive matrix methods reuse a fixed
--   unitary eigenbasis while the regularization scalar and diagonal values vary
-- counterargument checked: not paper-local or a pure wrapper; Mathlib supplies the component
--   diagonal and unitary identities but no declaration packaging preservation of a supplied basis
-- coverage search: queries "matrix unitary diagonalization adding scalar multiple identity shifts
--   diagonal eigenvalues", "add smul one equal unitary diagonalization add", and the precise
--   semantic statement found Matrix.IsHermitian.spectral_theorem, Matrix.diagonal_add,
--   Matrix.smul_one_eq_diagonal, and Unitary.coe_mul_star_self, but no full covering theorem
-- minimal hypotheses: Fintype and DecidableEq are required by matrix multiplication and identity;
--   all source nonnegativity and positive-semidefiniteness assumptions are omitted

/-- Adding a scalar multiple of the identity to a matrix with a supplied unitary
diagonalization shifts every diagonal value by that scalar and preserves the unitary basis.

Layer: Glue | Gap: Level 1 (scalar shift of a supplied unitary diagonalization)
Proof: distribute unitary conjugation over the diagonal sum, cancel the unitary product with its
  adjoint, and identify the scalar identity and diagonal sum entrywise.
Source: Mathlib finite matrix diagonal algebra and unitary star-multiplication identities
Used in: spectral regularization of adaptive matrix preconditioners while retaining a fixed
  eigenbasis for continuity and matrix-power arguments
Book citation: book/research/Source.json#/algorithm_spec/parameters/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Algorithms 1--3 -/
theorem Matrix.add_smul_one_eq_unitary_diagonalization_add
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R] [StarRing R]
    (A : Matrix ι ι R) (U : unitary (Matrix ι ι R)) (lam : ι → R)
    (hdiag : A = U.1 * Matrix.diagonal lam * star U.1) (ε : R) :
    A + ε • (1 : Matrix ι ι R) =
      U.1 * Matrix.diagonal (fun i : ι => lam i + ε) * star U.1 := by
  calc
    A + ε • (1 : Matrix ι ι R) =
        U.1 * Matrix.diagonal lam * star U.1 + ε • (1 : Matrix ι ι R) := by
          rw [hdiag]
    _ = U.1 * (Matrix.diagonal lam + ε • (1 : Matrix ι ι R)) * star U.1 := by
          simp [mul_add, add_mul, Matrix.mul_assoc]
    _ = U.1 * Matrix.diagonal (fun i : ι => lam i + ε) * star U.1 := by
          congr 2
          ext i j
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]


-- Generalization plan (G0):
-- concept/name: preservation of almost-everywhere Loewner order by the Bochner
--   integral on finite complex C-star matrices; orig was
--   cstarMatrix_integral_mono_ae_via_quadratic_forms
-- generality used: arbitrary measurable source type and measure, arbitrary finite
--   square index type, and two Bochner-integrable complex C-star-matrix functions;
--   no probability, finite-measure, or optimization assumptions are used
-- portable call pattern: matrix-valued expectation and integral comparisons in
--   adaptive preconditioning, covariance estimation, and operator-mean proofs;
--   the measure, index type, and integrands may all change
-- counterargument checked: this is not paper-local or a thin wrapper because
--   Mathlib's generic integral_mono_ae requires an IsOrderedModule instance that
--   the canonical spectral order on complex CStarMatrix does not provide
-- coverage search: queried "C-star matrix Bochner integral preserves almost
--   everywhere Loewner order", "Loewner order integral CStarMatrix", and
--   "positive semidefinite integral quadratic form finite complex matrix";
--   Mathlib integral_mono_ae and integral_nonneg_of_ae are partial hits requiring
--   IsOrderedModule, and no SOptLib theorem covers the CStarMatrix order bridge
-- minimal hypotheses: both integrability hypotheses are required for integral_sub;
--   the order hypothesis is only almost everywhere and the measure is arbitrary

open scoped ComplexOrder MatrixOrder

/-- Bochner integration preserves almost-everywhere Loewner order for finite
complex C-star matrices.

Layer: Glue | Gap: Level 1 (Bochner monotonicity for finite complex matrix spectral order)
Proof: integrate the pointwise nonnegative difference, commute every continuous quadratic-form functional through the integral, and reconstruct positive semidefiniteness from all vector quadratic forms.
Source: Mathlib Bochner integral continuous-linear-map commutation, finite complex matrix quadratic-form characterization of positive semidefiniteness, and CStarMatrix matrix equivalence
Used in: matrix-valued integral representations of fractional preconditioner powers, where pointwise Loewner monotonicity must pass through the representing measure
Book citation: book/research/Source.json#/source_outline
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem CStarMatrix.integral_mono_ae
    {X ι : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [Fintype ι]
    {f g : X → CStarMatrix ι ι ℂ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  classical
  let h : X → CStarMatrix ι ι ℂ := fun x => g x - f x
  have hh : MeasureTheory.Integrable h μ := hg.sub hf
  have hh_nonneg : ∀ᵐ x ∂μ, 0 ≤ h x := by
    filter_upwards [hfg] with x hx
    exact sub_nonneg.mpr hx
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] CStarMatrix ι ι ℂ :=
    CStarMatrix.ofMatrixStarAlgEquiv
  let H : CStarMatrix ι ι ℂ := ∫ x, h x ∂μ
  have hH_self : IsSelfAdjoint H := by
    change star H = H
    calc
      star H = ∫ x, star (h x) ∂μ := by
        symm
        exact ContinuousLinearMap.integral_comp_comm
          (starL' ℝ : CStarMatrix ι ι ℂ ≃L[ℝ] CStarMatrix ι ι ℂ).toContinuousLinearMap hh
      _ = ∫ x, h x ∂μ := MeasureTheory.integral_congr_ae <|
        hh_nonneg.mono fun x hx => (IsSelfAdjoint.of_nonneg hx).star_eq
      _ = H := rfl
  let M : Matrix ι ι ℂ := e.symm H
  have hM_self : M.IsHermitian := by
    change star M = M
    calc
      star M = e.symm (star H) := (map_star e.symm H).symm
      _ = e.symm H := congrArg e.symm hH_self.star_eq
      _ = M := rfl
  have hM_psd : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM_self
    intro v
    letI : FiniteDimensional ℂ (CStarMatrix ι ι ℂ) :=
      (CStarMatrix.ofMatrixₗ (R := ℂ)).finiteDimensional
    let qComplexLinear : CStarMatrix ι ι ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun N => dotProduct (star v) ((e.symm N : Matrix ι ι ℂ).mulVec v)
        map_add' := by
          intro N₁ N₂
          rw [map_add, Matrix.add_mulVec, dotProduct_add]
        map_smul' := by
          intro c N
          rw [map_smul, Matrix.smul_mulVec, dotProduct_smul]
          simp only [RingHom.id_apply] }
    let qComplex : CStarMatrix ι ι ℂ →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap qComplexLinear
    let q : CStarMatrix ι ι ℂ →L[ℝ] ℝ :=
      { toFun := fun N => Complex.re (qComplex N)
        map_add' := by
          intro N₁ N₂
          rw [map_add, Complex.add_re]
        map_smul' := by
          intro r N
          change Complex.re (dotProduct (star v)
              ((e.symm (r • N) : Matrix ι ι ℂ).mulVec v)) =
            r * Complex.re (dotProduct (star v)
              ((e.symm N : Matrix ι ι ℂ).mulVec v))
          rw [Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply ℝ ℂ (CStarMatrix ι ι ℂ) r]
          rw [← Algebra.smul_def, map_smul, Matrix.smul_mulVec, dotProduct_smul]
          simp [Complex.mul_re]
        cont := Complex.reCLM.continuous.comp qComplex.continuous }
    have hq_nonneg_of_nonneg (N : CStarMatrix ι ι ℂ) (hN : 0 ≤ N) :
        0 ≤ q N := by
      have hMN : 0 ≤ e.symm N := by
        apply (map_le_map_iff e).mp
        simpa using hN
      have hquad := (Matrix.nonneg_iff_posSemidef.mp hMN).dotProduct_mulVec_nonneg v
      simpa [q, qComplex, qComplexLinear] using (Complex.nonneg_iff.mp hquad).1
    have hqH_nonneg : 0 ≤ q H := by
      have hq_integral : q H = ∫ x, q (h x) ∂μ := by
        symm
        exact ContinuousLinearMap.integral_comp_comm q hh
      let scalar : X → ℝ := fun x => if 0 ≤ h x then q (h x) else 0
      have hscalar_nonneg : ∀ x, 0 ≤ scalar x := by
        intro x
        simp only [scalar]
        split_ifs with hx
        · exact hq_nonneg_of_nonneg (h x) hx
        · exact le_rfl
      have hscalar_ae : (fun x => q (h x)) =ᵐ[μ] scalar := by
        filter_upwards [hh_nonneg] with x hx
        simp [scalar, hx]
      rw [hq_integral, MeasureTheory.integral_congr_ae hscalar_ae]
      exact MeasureTheory.integral_nonneg hscalar_nonneg
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa [q, qComplex, qComplexLinear, M] using hqH_nonneg
    · simpa using (hM_self.im_star_dotProduct_mulVec_self v).symm
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM_psd
  have hH_nonneg : 0 ≤ H := by
    have heM : e 0 ≤ e M := (map_le_map_iff e).2 hM_nonneg
    simpa [M] using heM
  rw [← sub_nonneg, ← MeasureTheory.integral_sub hg hf]
  exact hH_nonneg


open scoped ContinuousFunctionalCalculus MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: binary weighted Kubo--Ando geometric mean of finite real matrices,
--   named `Matrix.binaryWeightedGeometricMean`; orig was `binaryWeightedGeometricMean`
-- generality used: arbitrary finite index type with decidable equality, two real square
--   matrices, and a real weight; positivity and a unit-interval weight are deliberately
--   absent because Mathlib's continuous functional calculus is totalized
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights,
--   and operator-interpolation proofs change the finite dimension, positive matrices,
--   and weight while using the same perspective object and its positivity, endpoint,
--   commuting-evaluation, and monotonicity specifications
-- counterargument checked: although the body is one formula, it is the standard
--   noncommutative perspective defining the Kubo--Ando weighted geometric mean, and its
--   surrounding positivity, endpoint, commuting-evaluation, and joint-monotonicity API
--   makes it a stable mathematical object rather than paper-local caller syntax
-- coverage search: symbol searches for "binary weighted operator geometric mean positive
--   matrices perspective" and "matrix geometric mean positive definite real power
--   congruence" found only the Shampoo-local definition and its theorems; Mathlib semantic
--   search found no named finite-matrix weighted geometric mean, so coverage is absent
-- minimal hypotheses: `Fintype` and `DecidableEq` are exactly those used by finite-matrix
--   multiplication and Hermitian continuous functional calculus; no positivity is needed
--   by the definitional construction

/-- The binary weighted Kubo--Ando geometric mean of finite real square matrices.

This is the noncommutative perspective
`A^(1/2) * (A^(-1/2) * B * A^(-1/2))^t * A^(1/2)`, with all real powers
formed by Mathlib's continuous functional calculus.

Layer: Model | Concept: binary weighted Kubo--Ando geometric mean
Proof: (definitional construction; continuous-functional-calculus powers combined by the noncommutative matrix perspective)
Source: Kubo--Ando operator means and Mathlib Hermitian matrix continuous functional calculus for real powers
Used in: recursive finite-family operator interpolation inside matrix-preconditioned regret proofs, where positivity, endpoint evaluation, commuting reduction, and joint monotonicity are required
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
noncomputable def binaryWeightedGeometricMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
    (Aneg * B * Aneg) * Ahalf

/-- The binary weighted geometric mean unfolds to its CFC matrix-perspective formula.

Layer: Model | Gap: Level 0 (defining formula for the binary weighted Kubo--Ando geometric mean)
Proof: by rfl after unfolding `Matrix.binaryWeightedGeometricMean`
Source: Kubo--Ando operator means and Mathlib Hermitian matrix continuous functional calculus for real powers
Used in: expanding the operator mean when proving positive definiteness, endpoint identities, commuting evaluation, and Löwner-order monotonicity for matrix preconditioners
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
theorem binaryWeightedGeometricMean_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) :
    binaryWeightedGeometricMean A B t =
      let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
      let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
      Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
        (Aneg * B * Aneg) * Ahalf :=
  rfl

/-- At weight zero, the binary weighted geometric mean is its left endpoint.

Layer: Model | Gap: Level 0 (zero-weight endpoint of the binary weighted Kubo--Ando geometric mean)
Proof: the middle CFC real power at exponent zero is the identity, after which the two outer half-powers multiply back to the positive-semidefinite left input
Source: Mathlib continuous-functional-calculus real-power zero, addition, and one laws
Used in: endpoint cases of operator-mean monotonicity and recursive finite-family interpolation
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
theorem binaryWeightedGeometricMean_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    binaryWeightedGeometricMean A B 0 = A := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg_self : IsSelfAdjoint Aneg := by
    dsimp only [Aneg]
    cfc_tac
  have hAneg_conjTranspose : Matrix.conjTranspose Aneg = Aneg := hAneg_self
  have hmiddle_self : IsSelfAdjoint (Aneg * B * Aneg) := by
    show Matrix.conjTranspose (Aneg * B * Aneg) = Aneg * B * Aneg
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hAneg_conjTranspose, hB, Matrix.mul_assoc]
  change Ahalf *
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (0 : ℝ))
        (Aneg * B * Aneg) * Ahalf = A
  simp_rw [Real.rpow_zero]
  rw [cfc_const_one ℝ (Aneg * B * Aneg) hmiddle_self, mul_one]
  change cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) A *
    cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) A = A
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := (1 / 2 : ℝ)) hA.nonneg,
    ← CFC.sqrt_eq_rpow, CFC.sqrt_mul_sqrt_self A hA.nonneg]

end Matrix


open scoped ContinuousFunctionalCalculus MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: strict positivity of the binary weighted Kubo--Ando geometric mean;
--   orig was `Shampoo.binaryWeightedGeometricMean_posDef`
-- generality used: arbitrary finite index type with decidable equality, two real square
--   matrices, an unrestricted real weight, and pointwise positive-definiteness hypotheses
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights,
--   and operator-interpolation proofs vary the finite dimension, positive-definite inputs,
--   and real weight while retaining strict positivity of the same binary operator mean
-- counterargument checked: this is not paper-local traceability or a one-lemma rename;
--   it composes strict positivity of arbitrary CFC real powers with two noncommutative
--   positive-definite congruences for the named operator-mean construction
-- coverage search: symbol queries for "binary weighted operator geometric mean positive
--   definite matrices" and "continuous functional calculus real power positive definite
--   congruence" found the staged mean definition and Mathlib's component lemmas
--   `IsStrictlyPositive.rpow` and `Matrix.PosDef.conjTranspose_mul_mul_same`, but no theorem
--   stating positivity of the binary weighted matrix geometric mean; coverage is partial
-- minimal hypotheses: both input matrices must be positive definite for arbitrary real
--   weights; the proof uses no interval restriction on the weight and no extra assumptions

/-- The binary weighted geometric mean of positive-definite real matrices is positive definite
for every real weight.

Layer: Model | Gap: Level 1 (strict positivity of the binary weighted Kubo--Ando geometric mean)
Proof: use `IsStrictlyPositive.rpow` for the inverse half-power, half-power, and middle real power, then apply positive-definite congruence twice using invertibility of the outer factors
Source: Mathlib `IsStrictlyPositive.rpow`, `Matrix.isStrictlyPositive_iff_posDef`, `CFC.rpow_eq_cfc_real`, and `Matrix.PosDef.conjTranspose_mul_mul_same`
Used in: recursive operator interpolation for matrix and tensor preconditioners, where each binary interpolation step must preserve invertibility and positive definiteness
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
theorem binaryWeightedGeometricMean_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (binaryWeightedGeometricMean A B t).PosDef := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg : Aneg.PosDef := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ)))
  have hAhalf : Ahalf.PosDef := by
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (1 / 2 : ℝ))
  have hAneg_conjTranspose : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hAhalf_conjTranspose : Matrix.conjTranspose Ahalf = Ahalf := hAhalf.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_conjTranspose] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hmiddlePow :
      (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
        (Aneg * B * Aneg)).PosDef := by
    rw [← CFC.rpow_eq_cfc_real hmiddle.posSemidef.nonneg]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hmiddle.isStrictlyPositive.rpow (Aneg * B * Aneg) t)
  change (Ahalf *
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
      (Aneg * B * Aneg) * Ahalf).PosDef
  simpa only [hAhalf_conjTranspose] using
    hmiddlePow.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hAhalf.isUnit)

end Matrix


open scoped ContinuousFunctionalCalculus MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: unit-weight endpoint of the binary weighted Kubo--Ando geometric mean;
--   orig was `Shampoo.binaryWeightedGeometricMean_one`
-- generality used: arbitrary finite index type with decidable equality, a positive-definite
--   left real square matrix, and a positive-semidefinite right real square matrix
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights,
--   and operator-interpolation proofs vary the finite dimension and endpoint matrices while
--   using the same unit-weight identity to close a boundary case
-- counterargument checked: this is an endpoint specification of the already named operator
--   mean rather than paper-local traceability; it is not a pure rename because its proof
--   combines CFC first-power evaluation, positive-semidefinite congruence, and cancellation
--   of inverse half-powers
-- coverage search: symbol searches for "binary weighted operator geometric mean equals right
--   input at weight one positive definite" and "matrix geometric mean one equals second
--   endpoint" found only the Shampoo-local candidate and the staged definition/zero endpoint;
--   Mathlib semantic search returned scalar mean inequalities, so coverage is absent
-- minimal hypotheses: positive definiteness of the left input supplies invertibility for the
--   opposite half-powers; the source's right-input positive definiteness is weakened to
--   positive semidefiniteness, exactly what the middle first-power evaluation requires

/-- At weight one, the binary weighted geometric mean is its right endpoint.

Layer: Model | Gap: Level 0 (unit-weight endpoint of the binary weighted Kubo--Ando geometric mean)
Proof: evaluate the middle CFC real power at one, reassociate the perspective product, and cancel the positive-definite left input's opposite half-powers with `CFC.rpow_mul_rpow_neg` and `CFC.rpow_neg_mul_rpow`
Source: Mathlib continuous-functional-calculus real-power one and opposite-power cancellation laws, together with positive-semidefinite matrix congruence
Used in: boundary cases of joint operator-mean monotonicity and recursive finite-family interpolation for matrix and tensor preconditioners
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
theorem binaryWeightedGeometricMean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosSemidef) :
    binaryWeightedGeometricMean A B 1 = B := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg : Aneg.PosDef := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ)))
  have hAneg_self : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosSemidef := by
    simpa only [hAneg_self] using hB.conjTranspose_mul_mul_same Aneg
  have hhalf_neg : Ahalf * Aneg = 1 := by
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA.isStrictlyPositive
  have hneg_half : Aneg * Ahalf = 1 := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hA.isStrictlyPositive
  change Ahalf *
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 : ℝ))
        (Aneg * B * Aneg) * Ahalf = B
  rw [← CFC.rpow_eq_cfc_real hmiddle.nonneg,
    CFC.rpow_one (Aneg * B * Aneg) hmiddle.nonneg]
  calc
    Ahalf * (Aneg * B * Aneg) * Ahalf =
        (Ahalf * Aneg) * B * (Aneg * Ahalf) := by simp only [mul_assoc]
    _ = B := by rw [hhalf_neg, hneg_half, one_mul, mul_one]

end Matrix


-- Generalization plan (G0):
-- concept/name: evaluation of the real-power integral kernel by matrix continuous functional
--   calculus as an affine resolvent; orig was `cfc_rpowIntegrand_eq_resolvent_kernel`
-- generality used: an arbitrary finite decidable index type, a real positive-semidefinite square
--   matrix, an unrestricted real exponent, and a positive real resolvent parameter; no measure,
--   convexity, oracle, or algorithm assumptions
-- portable call pattern: operator-power integral proofs for full-matrix adaptive methods evaluate
--   the same CFC kernel before comparing resolvents; the PSD matrix, exponent, parameter, and
--   finite coordinate type vary while the equality is unchanged
-- counterargument checked: this is not paper-local traceability or a pure rename; it composes the
--   scalar integrand formula with CFC preservation of constants, subtraction, and inversion, and
--   bridges the CFC ring inverse to Mathlib's matrix nonsingular inverse
-- coverage search: queries "rpowIntegrand₀₁ cfc resolvent inverse positive semidefinite matrix"
--   and "continuous functional calculus inverse affine resolvent spectrum nonzero" found the
--   scalar `Real.rpowIntegrand₀₁`, generic CFC component lemmas, and scaling identities, but
--   no Mathlib, SOptLib, or current-round declaration with this exact matrix equality
-- minimal hypotheses: `X.PosSemidef` supplies self-adjointness and nonnegative spectrum, while
--   `0 < s` is exactly what keeps the shifted spectrum away from zero; all are already minimal

/-- The real matrix continuous functional calculus evaluates `Real.rpowIntegrand₀₁` as a
scalar multiple of the difference between a scalar identity and an affine resolvent.

Layer: Glue | Gap: Level 1 (matrix CFC evaluation of the real-power resolvent kernel)
Proof: unfold the scalar kernel, establish nonvanishing of the positive spectral shift, and use
  the CFC constant, subtraction, scalar-multiplication, and inversion laws; finally identify the
  CFC ring inverse with the matrix nonsingular inverse.
Source: Mathlib continuous functional calculus for real powers, Hermitian matrix spectra, and
  finite-matrix nonsingular inverse APIs
Used in: operator-monotone matrix-power proofs that turn each functional-calculus integrand into
  an explicit resolvent before applying harmonic-resolvent order comparisons
Book citation: book/research/Source.json#/key_lemmas/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Lemma 6 operator-monotone powers -/
theorem Matrix.cfc_rpowIntegrand₀₁_eq_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℝ) (p s : ℝ) (hX : X.PosSemidef) (hs : 0 < s) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (Real.rpowIntegrand₀₁ p s) X =
      (s ^ p) • ((s⁻¹) • (1 : Matrix ι ι ℝ) -
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹) := by
  have hnonzero : ∀ x ∈ spectrum ℝ X, s + x ≠ 0 := by
    intro x hx
    have hx_nonneg : 0 ≤ x := by
      rw [hX.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hX.eigenvalues_nonneg i
    exact ne_of_gt (add_pos_of_pos_of_nonneg hs hx_nonneg)
  change cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => (s ^ p) * (s⁻¹ - (s + x)⁻¹)) X = _
  have hcont_add :
      ContinuousOn (fun x : ℝ => s + x) (spectrum ℝ X) :=
    continuousOn_const.add continuousOn_id
  have hcont_inv :
      ContinuousOn (fun x : ℝ => (s + x)⁻¹) (spectrum ℝ X) :=
    hcont_add.inv₀ hnonzero
  have hcont_diff :
      ContinuousOn (fun x : ℝ => s⁻¹ - (s + x)⁻¹) (spectrum ℝ X) :=
    continuousOn_const.sub hcont_inv
  have hconst :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun _ : ℝ => s⁻¹) X =
        (s⁻¹) • (1 : Matrix ι ι ℝ) := by
    rw [cfc_const (R := ℝ) (p := IsSelfAdjoint) s⁻¹ X hX.1]
    simp [Algebra.smul_def]
  have hadd :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => s + x) X =
        s • (1 : Matrix ι ι ℝ) + X := by
    rw [cfc_const_add (R := ℝ) (p := IsSelfAdjoint) s (fun x : ℝ => x) X
      continuousOn_id hX.1]
    rw [cfc_id' (p := IsSelfAdjoint) ℝ X hX.1]
    simp [Algebra.smul_def]
  have hinv :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X =
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹ := by
    rw [cfc_inv (p := IsSelfAdjoint) (f := fun x : ℝ => s + x) (a := X)
      hnonzero hcont_add hX.1]
    rw [hadd]
    exact (Matrix.nonsing_inv_eq_ringInverse
      (A := s • (1 : Matrix ι ι ℝ) + X)).symm
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => (s ^ p) * (s⁻¹ - (s + x)⁻¹)) X =
        (s ^ p) • cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => s⁻¹ - (s + x)⁻¹) X :=
      cfc_const_mul (R := ℝ) (p := IsSelfAdjoint) (s ^ p)
        (fun x : ℝ => s⁻¹ - (s + x)⁻¹) X hcont_diff
    _ = (s ^ p) •
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun _ : ℝ => s⁻¹) X -
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X) := by
      rw [cfc_sub (R := ℝ) (p := IsSelfAdjoint)
        (fun _ : ℝ => s⁻¹) (fun x : ℝ => (s + x)⁻¹) X
        continuousOn_const hcont_inv]
    _ = (s ^ p) • ((s⁻¹) • (1 : Matrix ι ι ℝ) -
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹) := by rw [hconst, hinv]


namespace SOptLib


-- Generalization plan (G0):
-- concept/name: star-algebra complexification of finite real square matrices;
--   orig was helperModulePrivate_realMatrixComplexification, renamed
--   realMatrixComplexification
-- generality used: an arbitrary finite index type with decidable equality; no fixed
--   matrix dimension, order hypothesis, topology, measure, convexity, smoothness, or
--   oracle assumptions are needed
-- portable call pattern: finite-dimensional matrix optimization arguments change the
--   index type and real matrix, then use the same embedding to transport Loewner-order
--   or continuous-functional-calculus facts to complex C-star matrices
-- counterargument checked: this is not merely paper traceability or a caller-side cast;
--   it bundles entrywise real-to-complex conversion, matrix multiplication, the star
--   operation, real scalar action, and the CStarMatrix representation into one canonical
--   homomorphism, and the source already repeats that construction at independent call sites
-- coverage search: symbol queries for finite real matrix complexification and star-algebra
--   embeddings found only the two Shampoo-local copies; Mathlib semantic search found
--   CStarMatrix.mapₙₐ, AlgHom.mapMatrix, and CStarMatrix.ofMatrixStarAlgEquiv, which are
--   construction components but do not provide this unital real-linear embedding
-- minimal hypotheses: Fintype supports matrix multiplication and CStarMatrix algebra
--   structure; DecidableEq supplies identity matrices required by the unital algebras

/-- Entrywise complexification as a real star-algebra homomorphism from finite real square
matrices to complex C-star matrices.

Layer: Glue | Concept: finite real matrix complexification into a complex C-star algebra
Proof: (definitional construction; compose the entrywise real-to-complex star-algebra map with the matrix-to-CStarMatrix star-algebra equivalence)
Source: Mathlib `Complex.ofReal`, `AlgHom.mapMatrix`, and `CStarMatrix.ofMatrixStarAlgEquiv`
Used in: matrix adaptive-gradient proofs that transport Loewner-order and continuous-functional-calculus statements from real positive-semidefinite preconditioners to complex C-star matrices
Book citation: book/research/Source.json#/source_outline
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
noncomputable def realMatrixComplexification
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ →⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro A
        change Matrix.map (star A) scalarCast = star (Matrix.map A scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  StarAlgHom.mk (e.toAlgEquiv.toAlgHom.comp matrixCast.toAlgHom)
    (by
      intro A
      change e (matrixCast (star A)) = star (e (matrixCast A))
      rw [map_star matrixCast, map_star e])

/-- Complexifying a real matrix coerces each entry from `ℝ` to `ℂ`.

Layer: Glue | Gap: Level 0 (coordinate specification of real matrix complexification)
Proof: by rfl after unfolding `realMatrixComplexification` and its entrywise matrix map
Source: Mathlib `Complex.ofReal`, `Matrix.map`, and `CStarMatrix.ofMatrix`
Used in: entrywise checks that the complex C-star matrix embedding preserves real matrix identities, adjoints, and quadratic-form order witnesses
Book citation: book/research/Source.json#/source_outline
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
@[simp]
theorem realMatrixComplexification_apply
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    realMatrixComplexification A i j = (A i j : ℂ) := by
  rfl

/-- Entrywise complexification of finite real square matrices is injective.

Layer: Glue | Gap: Level 1 (faithfulness of real matrix complexification)
Proof: compare entries of equal complexifications and use injectivity of the real embedding
into the complex numbers
Source: Mathlib `Complex.ofReal_injective` and matrix extensionality
Used in: reflecting equalities of complex C-star matrices back to real matrix identities
Book citation: book/research/Source.json#/source_outline
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem realMatrixComplexification_injective
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Function.Injective (realMatrixComplexification (ι := ι)) := by
  intro A B hAB
  ext i j
  apply Complex.ofReal_injective
  simpa using congrArg (fun C : CStarMatrix ι ι ℂ => C i j) hAB

end SOptLib


open scoped ComplexOrder MatrixOrder

namespace SOptLib


-- Generalization plan (G0):
-- concept/name: antitonicity of the nonsingular matrix inverse on the positive-definite
--   cone; orig was nonsing_inv_antitone_of_posDef, retained in the Matrix namespace
-- generality used: arbitrary finite index type with decidable equality and real matrix
--   entries; no fixed dimension, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: adaptive matrix and tensor preconditioner proofs vary the finite
--   coordinate type and positive-definite matrices while using the same implication
--   `A ≤ B → B⁻¹ ≤ A⁻¹` to compare dual metrics or harmonic resolvents
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   Mathlib's inverse-order theorem is for units in a C-star algebra, while this theorem
--   supplies the nontrivial order-reflecting transport to real matrices and their
--   nonsingular inverse
-- coverage search: queries for positive-definite matrix inverse antitonicity found
--   `CStarAlgebra.inv_le_inv` and `CStarAlgebra.rpow_neg_one_le_rpow_neg_one` for C-star
--   algebras, plus `Matrix.PosDef.inv` for positivity only; none states the real-matrix
--   Loewner-order conclusion
-- minimal hypotheses: positive-definiteness of `A` and `A ≤ B` imply
--   positive-definiteness of `B`; Fintype and DecidableEq are required by matrix
--   multiplication and nonsingular inversion

private theorem starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  rw [← sub_nonneg, ← map_sub]
  exact map_nonneg f.toNonUnitalStarAlgHom (sub_nonneg.mpr hab)

private theorem starAlgEquiv_le_iff
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃⋆ₐ[R] B) (a b : A) : e a ≤ e b ↔ a ≤ b := by
  constructor
  · intro h
    simpa using starAlgHom_mono_of_le
      (StarAlgHom.mk e.symm.toAlgEquiv.toAlgHom
        (fun x => by simpa using map_star e.symm x)) h
  · exact starAlgHom_mono_of_le
      (StarAlgHom.mk e.toAlgEquiv.toAlgHom
        (fun x => by simpa using map_star e x))

private theorem realMatrixComplexification_nonneg_iff
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : 0 ≤ realMatrixComplexification A ↔ 0 ≤ A := by
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix ι ι ℂ := Matrix.map A scalarCast
  have hcomplexify : realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [starAlgEquiv_le_iff e 0 castA]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, scalarCast] using hcast_psd.1.apply i j
    · intro v
      let vc : ι →₀ ℂ :=
        v.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
      have hv := hcast_psd.2 vc
      have heq :
          vc.sum (fun i vi => vc.sum fun j vj => star vi * castA i j * vj) =
            ((v.sum fun i vi => v.sum fun j vj => star vi * A i j * vj : ℝ) : ℂ) := by
        dsimp [vc]
        rw [Finsupp.sum_mapRange_index (by intro; simp)]
        simp only [Finsupp.sum,
          Finsupp.support_mapRange_of_injective Complex.ofReal_zero v
            Complex.ofReal_injective,
          castA, scalarCast, Matrix.map_apply, StarAlgHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact map_nonneg matrixCast.toNonUnitalStarAlgHom hA

/-- Nonsingular inversion reverses the Loewner order on positive-definite finite real
square matrices.

Layer: Glue | Gap: Level 1 (real-matrix inverse antitonicity under Loewner order)
Proof: complexify the real matrices through the order-reflecting star-algebra embedding, apply `CStarAlgebra.inv_le_inv` to the corresponding units, and reflect nonnegativity of the inverse difference back to real matrices.
Source: Mathlib `CStarAlgebra.inv_le_inv`, matrix positive-definiteness and nonsingular-inverse APIs, and `CStarMatrix.ofMatrixStarAlgEquiv`
Used in: adaptive matrix and tensor preconditioner analyses comparing inverse metrics and proving joint monotonicity of positive-definite harmonic resolvents
Book citation: book/research/Source.json#/source_outline
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem _root_.Matrix.nonsing_inv_antitone_of_posDef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB : B.PosDef := by
    convert hA.add_posSemidef (Matrix.le_iff.mp hAB) using 1
    abel
  let φ := realMatrixComplexification (ι := ι)
  let a : (Matrix ι ι ℝ)ˣ := hA.isUnit.unit
  let b : (Matrix ι ι ℝ)ˣ := hB.isUnit.unit
  let φa : (CStarMatrix ι ι ℂ)ˣ := Units.map φ.toMonoidHom a
  let φb : (CStarMatrix ι ι ℂ)ˣ := Units.map φ.toMonoidHom b
  have hcomplex_order : (φa : CStarMatrix ι ι ℂ) ≤ φb := by
    simpa [φa, φb, φ, a, b, IsUnit.unit_spec] using
      starAlgHom_mono_of_le φ hAB
  have hcomplex_A_nonneg : 0 ≤ (φa : CStarMatrix ι ι ℂ) := by
    simpa [φa, φ, a, IsUnit.unit_spec] using
      (realMatrixComplexification_nonneg_iff A).2 hA.posSemidef.nonneg
  have hcomplex_inv :
      (↑φb⁻¹ : CStarMatrix ι ι ℂ) ≤ (↑φa⁻¹ : CStarMatrix ι ι ℂ) :=
    CStarAlgebra.inv_le_inv hcomplex_A_nonneg hcomplex_order
  have himage_inv : φ B⁻¹ ≤ φ A⁻¹ := by
    simpa [φa, φb, φ, a, b, IsUnit.unit_spec, Matrix.coe_units_inv] using hcomplex_inv
  rw [Matrix.le_iff]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (realMatrixComplexification_nonneg_iff (A⁻¹ - B⁻¹)).mp
  rw [map_sub]
  exact sub_nonneg.mpr himage_inv

end SOptLib


open scoped ComplexOrder ContinuousFunctionalCalculus MatrixOrder NNReal


-- Generalization plan (G0):
-- concept/name: joint Löwner monotonicity of the binary weighted Kubo--Ando
--   geometric mean, named `Matrix.binaryWeightedGeometricMean_mono`; orig was
--   `Shampoo.binaryWeightedGeometricMean_mono_joint`
-- generality used: arbitrary finite index type with decidable equality, four real
--   positive-definite square matrices, coordinatewise Löwner order, and a real
--   weight in the unit interval; no optimization, probability, or setup assumptions
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights,
--   and operator-interpolation proofs change all four positive metrics and the weight
--   while retaining coordinatewise order and the same joint-monotonicity conclusion
-- counterargument checked: this is neither paper-local traceability nor a one-line
--   wrapper; it is the principal order law for the staged operator mean and requires
--   a harmonic-resolvent integral representation plus real/complex CFC transport
-- coverage search: symbol queries for "binary weighted geometric mean joint monotonicity
--   positive definite matrices Loewner order" and "operator geometric mean monotone
--   coordinatewise positive matrices" found no Mathlib/SOptLib theorem; Mathlib semantic
--   search returned only scalar geometric-mean inequalities and generic Loewner order
-- minimal hypotheses: positive definiteness supplies all inverses in the perspective and
--   harmonic resolvents; `0 ≤ t ≤ 1` is exactly the operator-monotone power range

namespace MatrixBinaryWeightedGeometricMeanMono

private noncomputable def matrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A

private theorem matrixRpow_posDef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosDef) :
    (matrixRpow A t).PosDef := by
  rw [matrixRpow, ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (hA.isStrictlyPositive.rpow A t)

private theorem matrixRpow_zero
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    matrixRpow A 0 = 1 := by
  rw [matrixRpow, ← CFC.rpow_eq_cfc_real hA.nonneg]
  exact CFC.rpow_zero A

private theorem matrixRpow_add
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (s t : ℝ) (hA : A.PosDef) :
    matrixRpow A (s + t) = matrixRpow A s * matrixRpow A t := by
  rw [matrixRpow, matrixRpow, matrixRpow,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact CFC.rpow_add hA.isUnit

private theorem matrixRpow_neg_half_mul_half
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    matrixRpow A (-(1 / 2 : ℝ)) * matrixRpow A (1 / 2 : ℝ) = 1 := by
  rw [← matrixRpow_add A _ _ hA]
  norm_num
  exact matrixRpow_zero A hA.posSemidef

private theorem matrixRpow_half_mul_neg_half
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    matrixRpow A (1 / 2 : ℝ) * matrixRpow A (-(1 / 2 : ℝ)) = 1 := by
  rw [← matrixRpow_add A _ _ hA]
  norm_num
  exact matrixRpow_zero A hA.posSemidef

private theorem matrixRpow_half_mul_half
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    matrixRpow A (1 / 2 : ℝ) * matrixRpow A (1 / 2 : ℝ) = A := by
  rw [← matrixRpow_add A _ _ hA]
  norm_num
  rw [matrixRpow, ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact CFC.rpow_one A hA.posSemidef.nonneg

@[reducible] private noncomputable def complexCStarMatrixRealCFC
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

@[reducible] private noncomputable def complexCStarMatrixNonnegSpectrum
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

private noncomputable def complexMatrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (t : ℝ) : CStarMatrix ι ι ℂ := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix ι ι ℂ) IsSelfAdjoint := complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  exact @CFC.rpow _ inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hCFC hNS A t

private theorem starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  exact OrderHomClass.mono f hab

private theorem realMatrixComplexification_nonneg_iff
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    0 ≤ SOptLib.realMatrixComplexification A ↔ 0 ≤ A := by
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix ι ι ℂ := Matrix.map A scalarCast
  have hcomplexify : SOptLib.realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [map_le_map_iff e]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, scalarCast] using hcast_psd.1.apply i j
    · intro v
      let vc : ι →₀ ℂ :=
        v.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
      have hv := hcast_psd.2 vc
      have heq :
          vc.sum (fun i vi => vc.sum fun j vj => star vi * castA i j * vj) =
            ((v.sum fun i vi => v.sum fun j vj => star vi * A i j * vj : ℝ) : ℂ) := by
        dsimp [vc]
        rw [Finsupp.sum_mapRange_index (by intro; simp)]
        simp only [Finsupp.sum,
          Finsupp.support_mapRange_of_injective Complex.ofReal_zero v
            Complex.ofReal_injective,
          castA, scalarCast, Matrix.map_apply, StarAlgHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact map_nonneg matrixCast.toNonUnitalStarAlgHom hA

private theorem realMatrixComplexification_matrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosSemidef) :
    SOptLib.realMatrixComplexification (matrixRpow A t) =
      complexMatrixRpow (SOptLib.realMatrixComplexification A) t := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix ι ι ℂ) IsSelfAdjoint := complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  letI hSemi : IsSemitopologicalRing (CStarMatrix ι ι ℂ) := inferInstance
  letI hT2 : T2Space (CStarMatrix ι ι ℂ) := inferInstance
  have hnonneg : 0 ≤ SOptLib.realMatrixComplexification A :=
    (realMatrixComplexification_nonneg_iff A).2 hA.nonneg
  have hrpow_eq :
      complexMatrixRpow (SOptLib.realMatrixComplexification A) t =
        cfc (fun x : ℝ => x ^ t) (SOptLib.realMatrixComplexification A) := by
    rw [complexMatrixRpow]
    exact @CFC.rpow_eq_cfc_real _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hCFC hNS hSemi hT2
      (SOptLib.realMatrixComplexification A) t hnonneg
  rw [matrixRpow, hrpow_eq]
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [hA.1.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hφ : Continuous (SOptLib.realMatrixComplexification (ι := ι)) := by
    change Continuous (fun M : Matrix ι ι ℝ =>
      CStarMatrix.ofMatrix (Matrix.map M fun r : ℝ => (r : ℂ)))
    have hcast : Continuous (fun M : Matrix ι ι ℝ =>
        Matrix.map M fun r : ℝ => (r : ℂ)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun M : Matrix ι ι ℝ => (M i j : ℂ))
      fun_prop
    exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp hcast
  exact (SOptLib.realMatrixComplexification (ι := ι)).map_cfc
    (fun x : ℝ => x ^ t) A
    (hf := hf) (hφ := hφ) (ha := hA.1)
    (hφa := (show IsSelfAdjoint A from hA.1).map
      (SOptLib.realMatrixComplexification (ι := ι)))

private noncomputable def weightedHarmonicResolvent
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  (A⁻¹ + s • B⁻¹)⁻¹

private theorem weightedHarmonicResolvent_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℝ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 < s) :
    weightedHarmonicResolvent A B s ≤ weightedHarmonicResolvent C D s := by
  have hCinv_Ainv : C⁻¹ ≤ A⁻¹ :=
    Matrix.nonsing_inv_antitone_of_posDef A C hA hAC
  have hDinv_Binv : D⁻¹ ≤ B⁻¹ :=
    Matrix.nonsing_inv_antitone_of_posDef B D hB hBD
  have hsum : C⁻¹ + s • D⁻¹ ≤ A⁻¹ + s • B⁻¹ :=
    add_le_add hCinv_Ainv (smul_le_smul_of_nonneg_left hDinv_Binv hs.le)
  exact Matrix.nonsing_inv_antitone_of_posDef
    (C⁻¹ + s • D⁻¹) (A⁻¹ + s • B⁻¹)
    (hC.inv.add (hD.inv.smul hs)) hsum

private theorem weightedHarmonicResolvent_eq_rpow_perspective_integrand
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    matrixRpow A (1 / 2 : ℝ) *
          ((s⁻¹) • (1 : Matrix ι ι ℝ) -
            (s • (1 : Matrix ι ι ℝ) +
              matrixRpow A (-(1 / 2 : ℝ)) * B *
                matrixRpow A (-(1 / 2 : ℝ)))⁻¹) *
        matrixRpow A (1 / 2 : ℝ) =
      (s⁻¹) • weightedHarmonicResolvent A B s := by
  classical
  let P : Matrix ι ι ℝ := matrixRpow A (1 / 2 : ℝ)
  let Q : Matrix ι ι ℝ := matrixRpow A (-(1 / 2 : ℝ))
  let K : Matrix ι ι ℝ := s • A + B
  have hK_pd : K.PosDef := (hA.smul hs).add hB
  have hP_Q : P * Q = (1 : Matrix ι ι ℝ) := by
    simpa [P, Q] using matrixRpow_half_mul_neg_half A hA
  have hQ_P : Q * P = (1 : Matrix ι ι ℝ) := by
    simpa [P, Q] using matrixRpow_neg_half_mul_half A hA
  have hP_P : P * P = A := by
    simpa [P] using matrixRpow_half_mul_half A hA
  have hKinv_K : K⁻¹ * K = (1 : Matrix ι ι ℝ) := by
    have hdet : K.det ≠ 0 := ne_of_gt hK_pd.det_pos
    letI : Invertible K.det := invertibleOfNonzero hdet
    letI : Invertible K := Matrix.invertibleOfDetInvertible K
    exact Matrix.inv_mul_of_invertible K
  have hB_Binv : B * B⁻¹ = (1 : Matrix ι ι ℝ) := by
    have hdet : B.det ≠ 0 := ne_of_gt hB.det_pos
    letI : Invertible B.det := invertibleOfNonzero hdet
    letI : Invertible B := Matrix.invertibleOfDetInvertible B
    exact Matrix.mul_inv_of_invertible B
  have hA_Ainv : A * A⁻¹ = (1 : Matrix ι ι ℝ) := by
    have hdet : A.det ≠ 0 := ne_of_gt hA.det_pos
    letI : Invertible A.det := invertibleOfNonzero hdet
    letI : Invertible A := Matrix.invertibleOfDetInvertible A
    exact Matrix.mul_inv_of_invertible A
  have hmiddle :
      s • (1 : Matrix ι ι ℝ) + Q * B * Q = Q * K * Q := by
    have hQAQ : Q * A * Q = (1 : Matrix ι ι ℝ) := by
      rw [← hP_P]
      calc
        Q * (P * P) * Q = (Q * P) * (P * Q) := by noncomm_ring
        _ = 1 := by rw [hQ_P, hP_Q, one_mul]
    dsimp [K]
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hQAQ]
  have hmiddle_inv :
      (s • (1 : Matrix ι ι ℝ) + Q * B * Q)⁻¹ = P * K⁻¹ * P := by
    rw [hmiddle]
    apply Matrix.inv_eq_left_inv
    calc
      (P * K⁻¹ * P) * (Q * K * Q) =
          P * K⁻¹ * (P * Q) * K * Q := by noncomm_ring
      _ = P * (K⁻¹ * K) * Q := by rw [hP_Q]; simp [mul_assoc]
      _ = 1 := by rw [hKinv_K, mul_one, hP_Q]
  have hresolver_inv :
      weightedHarmonicResolvent A B s = A * K⁻¹ * B := by
    unfold weightedHarmonicResolvent
    apply Matrix.inv_eq_left_inv
    calc
      (A * K⁻¹ * B) * (A⁻¹ + s • B⁻¹) =
          A * K⁻¹ * (B + s • A) * A⁻¹ := by
            noncomm_ring [hA_Ainv, hB_Binv]
      _ = A * (K⁻¹ * K) * A⁻¹ := by
            rw [show B + s • A = K by simp [K, add_comm]]
            simp [mul_assoc]
      _ = 1 := by rw [hKinv_K, mul_one, hA_Ainv]
  change P * ((s⁻¹) • (1 : Matrix ι ι ℝ) -
      (s • (1 : Matrix ι ι ℝ) + Q * B * Q)⁻¹) * P =
    (s⁻¹) • weightedHarmonicResolvent A B s
  rw [hmiddle_inv, hresolver_inv]
  rw [mul_sub, sub_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one]
  have hconj : P * (P * K⁻¹ * P) * P = A * K⁻¹ * A := by
    calc
      P * (P * K⁻¹ * P) * P = (P * P) * K⁻¹ * (P * P) := by
        noncomm_ring
      _ = A * K⁻¹ * A := by rw [hP_P]
  rw [hconj]
  have hexpand : A = s • (A * K⁻¹ * A) + A * K⁻¹ * B := by
    calc
      A = A * (K⁻¹ * K) := by rw [hKinv_K, mul_one]
      _ = s • (A * K⁻¹ * A) + A * K⁻¹ * B := by
        dsimp [K]
        simp only [mul_add, mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  have hscaled :
      (s⁻¹) • A = A * K⁻¹ * A + (s⁻¹) • (A * K⁻¹ * B) := by
    calc
      (s⁻¹) • A = (s⁻¹) • (s • (A * K⁻¹ * A) + A * K⁻¹ * B) :=
        congrArg ((s⁻¹) • ·) hexpand
      _ = A * K⁻¹ * A + (s⁻¹) • (A * K⁻¹ * B) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hP_P, hscaled]
  module

private theorem rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let Aneg := matrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := matrixRpow A (1 / 2 : ℝ)
    Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf =
      (s ^ (p - 1)) • weightedHarmonicResolvent A B s := by
  classical
  let Aneg := matrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := matrixRpow A (1 / 2 : ℝ)
  have hAneg : Aneg.PosDef := matrixRpow_posDef A _ hA
  have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_star] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hcfc := Matrix.cfc_rpowIntegrand₀₁_eq_resolvent
    (Aneg * B * Aneg) p s hmiddle.posSemidef hs
  have hperspective := weightedHarmonicResolvent_eq_rpow_perspective_integrand
    A B s hA hB hs
  change Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf = _
  rw [hcfc]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hperspective, smul_smul]
  congr 1
  rw [Real.rpow_sub_one hs.ne' p]
  exact (div_eq_mul_inv (s ^ p) s).symm

private theorem complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    [ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ)]
    (A B : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let φ := SOptLib.realMatrixComplexification (ι := ι)
    let Aneg := matrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := matrixRpow A (1 / 2 : ℝ)
    φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf =
      (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) := by
  let φ := SOptLib.realMatrixComplexification (ι := ι)
  let Aneg := matrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := matrixRpow A (1 / 2 : ℝ)
  have hAneg : Aneg.PosDef := matrixRpow_posDef A _ hA
  have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_star] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hf : ContinuousOn (Real.rpowIntegrand₀₁ p s)
      (spectrum ℝ (Aneg * B * Aneg)) := by
    have hnonzero : ∀ x ∈ spectrum ℝ (Aneg * B * Aneg), s + x ≠ 0 := by
      intro x hx
      have hx_nonneg : 0 ≤ x := by
        rw [hmiddle.1.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hmiddle.posSemidef.eigenvalues_nonneg i
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs hx_nonneg)
    unfold Real.rpowIntegrand₀₁
    fun_prop (disch := assumption)
  have hmap_cfc :
      φ (cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg)) =
        cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ (Aneg * B * Aneg)) := by
    exact φ.map_cfc (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg)
      (hf := hf)
      (hφ := by
        change Continuous (fun M : Matrix ι ι ℝ =>
          CStarMatrix.ofMatrix (Matrix.map M fun r : ℝ => (r : ℂ)))
        have hcast : Continuous (fun M : Matrix ι ι ℝ =>
            Matrix.map M fun r : ℝ => (r : ℂ)) := by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          change Continuous (fun M : Matrix ι ι ℝ => (M i j : ℂ))
          fun_prop
        exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp
          hcast)
      (ha := hmiddle.1)
      (hφa := (show IsSelfAdjoint (Aneg * B * Aneg) from hmiddle.1).map φ)
  have hsource := congrArg φ
    (rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent
      A B p s hA hB hs)
  change φ (Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf) =
    φ ((s ^ (p - 1)) • weightedHarmonicResolvent A B s) at hsource
  rw [map_mul, map_mul, hmap_cfc, map_mul, map_mul, map_smul] at hsource
  change φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf = _
  exact hsource

private theorem complexifiedRpowPerspectiveIntegrand_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    [ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ)]
    (A B C D : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 < s) :
    let φ := SOptLib.realMatrixComplexification (ι := ι)
    let Aneg := matrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := matrixRpow A (1 / 2 : ℝ)
    let Cneg := matrixRpow C (-(1 / 2 : ℝ))
    let Chalf := matrixRpow C (1 / 2 : ℝ)
    φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf ≤
      φ Chalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Cneg * φ D * φ Cneg) * φ Chalf := by
  let φ := SOptLib.realMatrixComplexification (ι := ι)
  let Aneg := matrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := matrixRpow A (1 / 2 : ℝ)
  let Cneg := matrixRpow C (-(1 / 2 : ℝ))
  let Chalf := matrixRpow C (1 / 2 : ℝ)
  change φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
        (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf ≤
    φ Chalf * cfc (R := ℝ) (p := IsSelfAdjoint)
        (Real.rpowIntegrand₀₁ p s) (φ Cneg * φ D * φ Cneg) * φ Chalf
  rw [complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent A B p s hA hB hs,
    complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent C D p s hC hD hs]
  have hreal :
      (s ^ (p - 1)) • weightedHarmonicResolvent A B s ≤
        (s ^ (p - 1)) • weightedHarmonicResolvent C D s :=
    smul_le_smul_of_nonneg_left
      (weightedHarmonicResolvent_mono A B C D s hA hB hC hD hAC hBD hs)
      (Real.rpow_nonneg hs.le _)
  change (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) ≤
    (s ^ (p - 1)) • φ (weightedHarmonicResolvent C D s)
  calc
    (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) =
        φ ((s ^ (p - 1)) • weightedHarmonicResolvent A B s) :=
      (map_smul φ (s ^ (p - 1)) (weightedHarmonicResolvent A B s)).symm
    _ ≤ φ ((s ^ (p - 1)) • weightedHarmonicResolvent C D s) :=
      starAlgHom_mono_of_le φ hreal
    _ = (s ^ (p - 1)) • φ (weightedHarmonicResolvent C D s) :=
      map_smul φ (s ^ (p - 1)) (weightedHarmonicResolvent C D s)

/-- The binary weighted Kubo--Ando geometric mean is jointly monotone on
positive-definite finite real matrices for weights in the unit interval.

Layer: Model | Gap: Level 2 (joint Löwner monotonicity of the binary weighted operator geometric mean)
Proof: represent the interior real power by Mathlib's nonunital-CFC Bochner integral, identify each perspective integrand with a positive multiple of a jointly monotone harmonic resolvent, integrate the pointwise order, and handle the two endpoint weights by the staged endpoint identities.
Source: Kubo--Ando operator means; Mathlib nonunital continuous-functional-calculus integral representation of fractional powers, inverse antitonicity, and finite complex C-star-matrix Bochner integration
Used in: recursive matrix and tensor preconditioner interpolation, where coordinatewise growth of two positive-definite metric inputs must imply growth of their weighted operator mean
Book citation: book/research/Source.json#/key_lemmas/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 6 operator-mean monotonicity support -/
private theorem binaryWeightedGeometricMean_mono_local
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℝ) (t : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Matrix.binaryWeightedGeometricMean A B t ≤
      Matrix.binaryWeightedGeometricMean C D t := by
  rcases lt_or_eq_of_le ht0 with htpos | rfl
  · rcases lt_or_eq_of_le ht1 with htlt | rfl
    · let hSemiCanonical : IsSemitopologicalRing
          (CStarMatrix ι ι ℂ) := inferInstance
      let hT2Canonical : T2Space (CStarMatrix ι ι ℂ) := inferInstance
      let hSMulCanonical : SMul ℝ (CStarMatrix ι ι ℂ) := inferInstance
      letI hSMul : SMul ℝ (CStarMatrix ι ι ℂ) := hSMulCanonical
      let hModuleCanonical : Module ℝ (CStarMatrix ι ι ℂ) := inferInstance
      letI hModule : Module ℝ (CStarMatrix ι ι ℂ) := hModuleCanonical
      letI hTower : IsScalarTower ℝ (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) :=
        IsScalarTower.of_algebraMap_smul fun r X => by
          rw [Algebra.smul_def]
          simp only [smul_eq_mul]
      letI hCFC : ContinuousFunctionalCalculus ℝ
          (CStarMatrix ι ι ℂ) IsSelfAdjoint := complexCStarMatrixRealCFC
      have hTowerCheck : IsScalarTower ℝ
          (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) := hTower
      letI hSmulComm : SMulCommClass ℝ
          (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) := by
        constructor
        intro r X Y
        change r • (X * Y) = X * (r • Y)
        ext i j
        simp [Matrix.mul_apply, Finset.mul_sum]
      letI hNCFC : @NonUnitalContinuousFunctionalCalculus ℝ
          (CStarMatrix ι ι ℂ) IsSelfAdjoint
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance hModule hTower
          hSmulComm :=
        let hNCFCAlgebra := @ContinuousFunctionalCalculus.toNonUnital
          ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance hCFC
        hNCFCAlgebra
      let cfcN := @cfcₙ ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint
        inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hModule hTower
        hSmulComm hNCFC
      letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
        complexCStarMatrixNonnegSpectrum
      let nnrpowN := @CFC.nnrpow (CStarMatrix ι ι ℂ)
        inferInstance inferInstance inferInstance inferInstance hModule hSmulComm
        hTower inferInstance hNCFC hNS
      let φ := SOptLib.realMatrixComplexification (ι := ι)
      let Aneg := matrixRpow A (-(1 / 2 : ℝ))
      let Ahalf := matrixRpow A (1 / 2 : ℝ)
      let Cneg := matrixRpow C (-(1 / 2 : ℝ))
      let Chalf := matrixRpow C (1 / 2 : ℝ)
      let XA : CStarMatrix ι ι ℂ := φ Aneg * φ B * φ Aneg
      let XC : CStarMatrix ι ι ℂ := φ Cneg * φ D * φ Cneg
      let q : ℝ≥0 := ⟨t, ht0⟩
      have hq : q ∈ Set.Ioo (0 : ℝ≥0) 1 := by
        constructor
        · exact_mod_cast htpos
        · exact_mod_cast htlt
      have hAneg : Aneg.PosDef := matrixRpow_posDef A _ hA
      have hCneg : Cneg.PosDef := matrixRpow_posDef C _ hC
      have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
      have hCneg_star : Matrix.conjTranspose Cneg = Cneg := hCneg.1
      have hmiddleA : (Aneg * B * Aneg).PosDef := by
        simpa only [hAneg_star] using
          hB.conjTranspose_mul_mul_same
            (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
      have hmiddleC : (Cneg * D * Cneg).PosDef := by
        simpa only [hCneg_star] using
          hD.conjTranspose_mul_mul_same
            (Matrix.mulVec_injective_of_isUnit hCneg.isUnit)
      have hXA : 0 ≤ XA := by
        have himage := map_nonneg φ.toNonUnitalStarAlgHom hmiddleA.posSemidef.nonneg
        simpa only [XA, map_mul] using himage
      have hXC : 0 ≤ XC := by
        have himage := map_nonneg φ.toNonUnitalStarAlgHom hmiddleC.posSemidef.nonneg
        simpa only [XC, map_mul] using himage
      obtain ⟨μ, hμ⟩ :=
        CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
          (CStarMatrix ι ι ℂ) hq
      have hμA := hμ XA hXA
      have hμC := hμ XC hXC
      change MeasureTheory.IntegrableOn
          (fun s => cfcN (Real.rpowIntegrand₀₁ q s) XA) (Set.Ioi 0) μ ∧
          nnrpowN XA q =
            ∫ s in Set.Ioi 0, cfcN (Real.rpowIntegrand₀₁ q s) XA ∂μ at hμA
      change MeasureTheory.IntegrableOn
          (fun s => cfcN (Real.rpowIntegrand₀₁ q s) XC) (Set.Ioi 0) μ ∧
          nnrpowN XC q =
            ∫ s in Set.Ioi 0, cfcN (Real.rpowIntegrand₀₁ q s) XC ∂μ at hμC
      let LA := ContinuousLinearMap.mulLeftRight ℂ
        (CStarMatrix ι ι ℂ) (φ Ahalf) (φ Ahalf)
      let LC := ContinuousLinearMap.mulLeftRight ℂ
        (CStarMatrix ι ι ℂ) (φ Chalf) (φ Chalf)
      have hintA : MeasureTheory.IntegrableOn
          (fun s => LA (cfcN (Real.rpowIntegrand₀₁ q s) XA)) (Set.Ioi 0) μ :=
        LA.integrable_comp hμA.1
      have hintC : MeasureTheory.IntegrableOn
          (fun s => LC (cfcN (Real.rpowIntegrand₀₁ q s) XC)) (Set.Ioi 0) μ :=
        LC.integrable_comp hμC.1
      have hintegral :
          (∫ s in Set.Ioi 0, LA (cfcN (Real.rpowIntegrand₀₁ q s) XA) ∂μ) ≤
            ∫ s in Set.Ioi 0, LC (cfcN (Real.rpowIntegrand₀₁ q s) XC) ∂μ := by
        apply CStarMatrix.integral_mono_ae hintA hintC
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
        have hfA : ContinuousOn (Real.rpowIntegrand₀₁ q s)
            (quasispectrum ℝ XA) := by
          exact (Real.continuousOn_rpowIntegrand₀₁_Ici
            (show (t : ℝ) ∈ Set.Ioo 0 1 from ⟨htpos, htlt⟩) hs).mono (by
              intro x hx
              exact quasispectrum_nonneg_of_nonneg XA hXA x hx)
        have hfC : ContinuousOn (Real.rpowIntegrand₀₁ q s)
            (quasispectrum ℝ XC) := by
          exact (Real.continuousOn_rpowIntegrand₀₁_Ici
            (show (t : ℝ) ∈ Set.Ioo 0 1 from ⟨htpos, htlt⟩) hs).mono (by
              intro x hx
              exact quasispectrum_nonneg_of_nonneg XC hXC x hx)
        change φ Ahalf * cfcN (Real.rpowIntegrand₀₁ q s) XA * φ Ahalf ≤
          φ Chalf * cfcN (Real.rpowIntegrand₀₁ q s) XC * φ Chalf
        have hcfA : cfcN (Real.rpowIntegrand₀₁ q s) XA =
            cfc (Real.rpowIntegrand₀₁ q s) XA := by
          exact cfcₙ_eq_cfc (hf := hfA) (hf0 := Real.rpowIntegrand₀₁_zero_right)
        have hcfC : cfcN (Real.rpowIntegrand₀₁ q s) XC =
            cfc (Real.rpowIntegrand₀₁ q s) XC := by
          exact cfcₙ_eq_cfc (hf := hfC) (hf0 := Real.rpowIntegrand₀₁_zero_right)
        rw [hcfA, hcfC]
        simpa only [XA, XC, q] using
          (complexifiedRpowPerspectiveIntegrand_mono
            A B C D t s hA hB hC hD hAC hBD hs)
      have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq.1
      have hnnA : nnrpowN XA q = cfcN (fun x : ℝ => x ^ (q : ℝ)) XA := by
        exact @CFC.nnrpow_eq_cfcₙ_real
          (CStarMatrix ι ι ℂ) inferInstance inferInstance
          inferInstance inferInstance hModule hSmulComm hTower inferInstance
          hNCFC hNS inferInstance inferInstance XA q hXA
      have hnnC : nnrpowN XC q = cfcN (fun x : ℝ => x ^ (q : ℝ)) XC := by
        exact @CFC.nnrpow_eq_cfcₙ_real
          (CStarMatrix ι ι ℂ) inferInstance inferInstance
          inferInstance inferInstance hModule hSmulComm hTower inferInstance
          hNCFC hNS inferInstance inferInstance XC q hXC
      have hcfPowA : cfcN (fun x : ℝ => x ^ (q : ℝ)) XA =
          cfc (fun x : ℝ => x ^ (q : ℝ)) XA := by
        exact cfcₙ_eq_cfc
          (hf := (Real.continuous_rpow_const hqreal.le).continuousOn)
          (hf0 := Real.zero_rpow hqreal.ne')
      have hcfPowC : cfcN (fun x : ℝ => x ^ (q : ℝ)) XC =
          cfc (fun x : ℝ => x ^ (q : ℝ)) XC := by
        exact cfcₙ_eq_cfc
          (hf := (Real.continuous_rpow_const hqreal.le).continuousOn)
          (hf0 := Real.zero_rpow hqreal.ne')
      have hpowA : complexMatrixRpow XA t = nnrpowN XA q := by
        calc
          complexMatrixRpow XA t = cfc (fun x : ℝ => x ^ t) XA := by
            simpa only [complexMatrixRpow] using
              (@CFC.rpow_eq_cfc_real
                (CStarMatrix ι ι ℂ) inferInstance inferInstance
                inferInstance inferInstance inferInstance inferInstance hCFC hNS
                hSemiCanonical hT2Canonical XA t hXA)
          _ = cfc (fun x : ℝ => x ^ (q : ℝ)) XA := by rfl
          _ = cfcN (fun x : ℝ => x ^ (q : ℝ)) XA := hcfPowA.symm
          _ = nnrpowN XA q := hnnA.symm
      have hpowC : complexMatrixRpow XC t = nnrpowN XC q := by
        calc
          complexMatrixRpow XC t = cfc (fun x : ℝ => x ^ t) XC := by
            simpa only [complexMatrixRpow] using
              (@CFC.rpow_eq_cfc_real
                (CStarMatrix ι ι ℂ) inferInstance inferInstance
                inferInstance inferInstance inferInstance inferInstance hCFC hNS
                hSemiCanonical hT2Canonical XC t hXC)
          _ = cfc (fun x : ℝ => x ^ (q : ℝ)) XC := by rfl
          _ = cfcN (fun x : ℝ => x ^ (q : ℝ)) XC := hcfPowC.symm
          _ = nnrpowN XC q := hnnC.symm
      have hmeanA : φ (Matrix.binaryWeightedGeometricMean A B t) =
          ∫ s in Set.Ioi 0, LA (cfcN (Real.rpowIntegrand₀₁ q s) XA) ∂μ := by
        change φ (Ahalf * matrixRpow (Aneg * B * Aneg) t * Ahalf) = _
        rw [map_mul, map_mul,
          realMatrixComplexification_matrixRpow
            (Aneg * B * Aneg) t hmiddleA.posSemidef]
        rw [map_mul, map_mul]
        change φ Ahalf * complexMatrixRpow XA t * φ Ahalf = _
        rw [hpowA, hμA.2]
        exact (LA.integral_comp_comm hμA.1).symm
      have hmeanC : φ (Matrix.binaryWeightedGeometricMean C D t) =
          ∫ s in Set.Ioi 0, LC (cfcN (Real.rpowIntegrand₀₁ q s) XC) ∂μ := by
        change φ (Chalf * matrixRpow (Cneg * D * Cneg) t * Chalf) = _
        rw [map_mul, map_mul,
          realMatrixComplexification_matrixRpow
            (Cneg * D * Cneg) t hmiddleC.posSemidef]
        rw [map_mul, map_mul]
        change φ Chalf * complexMatrixRpow XC t * φ Chalf = _
        rw [hpowC, hμC.2]
        exact (LC.integral_comp_comm hμC.1).symm
      rw [← hmeanA, ← hmeanC] at hintegral
      rw [Matrix.le_iff]
      apply Matrix.nonneg_iff_posSemidef.mp
      apply (realMatrixComplexification_nonneg_iff
        (Matrix.binaryWeightedGeometricMean C D t -
          Matrix.binaryWeightedGeometricMean A B t)).mp
      rw [map_sub]
      exact sub_nonneg.mpr hintegral
    · rw [Matrix.binaryWeightedGeometricMean_one A B hA hB.posSemidef,
        Matrix.binaryWeightedGeometricMean_one C D hC hD.posSemidef]
      exact hBD
  · rw [Matrix.binaryWeightedGeometricMean_zero A B hA.posSemidef hB.1,
      Matrix.binaryWeightedGeometricMean_zero C D hC.posSemidef hD.1]
    exact hAC

end MatrixBinaryWeightedGeometricMeanMono


namespace SOptLib


-- Generalization plan (G0):
-- concept/name: continuity of finite real-matrix complexification; orig was
--   continuous_realMatrixComplexification and its concept-derived name is retained
-- generality used: an arbitrary finite index type with decidable equality; no fixed
--   matrix dimension, measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: full-matrix adaptive-gradient and matrix
--   multiplicative-weights proofs change the finite index type and convergent matrix
--   family while using the same continuous complexification to transport limits or
--   continuous-functional-calculus identities into a complex C-star matrix algebra
-- counterargument checked: this is a short composition theorem, but not a pure rename
--   or caller-side expression; it supplies the missing topological API for the canonical
--   staged complexification and is independently needed by limit and CFC transport steps
-- coverage search: queries for "continuous real matrix complexification finite matrix
--   entrywise cast star algebra homomorphism" and "continuity of entrywise map on finite
--   matrices induced by a continuous scalar function" found the staged
--   realMatrixComplexification definition and Mathlib Continuous.matrix_map, but no
--   theorem giving continuity of the composite into CStarMatrix
-- minimal hypotheses: Fintype is needed for the CStarMatrix norm topology comparison;
--   DecidableEq is inherited from the unital star-algebra complexification definition

/-- Entrywise complexification from finite real square matrices to complex C-star matrices
is continuous.

Layer: Glue | Gap: Level 1 (continuity of finite real-matrix complexification)
Proof: prove continuity of the entrywise real-to-complex cast in the product topology, then compose it with the continuous matrix-to-CStarMatrix uniform embedding.
Source: Mathlib matrix product topology and `CStarMatrix.uniformEmbedding_ofMatrix`
Used in: adaptive-matrix limit arguments and continuous-functional-calculus transport from convergent real preconditioner families to complex C-star matrices
Book citation: book/research/Source.json#/source_outline
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem continuous_realMatrixComplexification
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Continuous (realMatrixComplexification (ι := ι)) := by
  change Continuous (fun M : Matrix ι ι ℝ =>
    CStarMatrix.ofMatrix (Matrix.map M fun r : ℝ => (r : ℂ)))
  have hcast : Continuous (fun M : Matrix ι ι ℝ =>
      Matrix.map M fun r : ℝ => (r : ℂ)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun M : Matrix ι ι ℝ => (M i j : ℂ))
    fun_prop
  exact
    CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp hcast

end SOptLib


open Topology
open scoped ComplexOrder MatrixOrder


-- Generalization plan (G0):
-- concept/name: closure of finite real-matrix Loewner order under filtered limits;
--   orig was squareMatrix_le_of_tendsto_of_tendsto, renamed
--   Matrix.le_of_tendsto_of_tendsto
-- generality used: arbitrary finite matrix index type, arbitrary source type,
--   and an arbitrary nontrivial filter; no fixed dimension, measure, convexity,
--   smoothness, oracle, or algorithm-state assumptions are used
-- portable call pattern: matrix AdaGrad, Shampoo, and matrix multiplicative-weights
--   proofs vary the regularized matrix families, filter, and limiting matrices while
--   using eventual Loewner domination to compare the singular endpoint limits
-- counterargument checked: Mathlib has the abstract closed-order theorem with the same
--   filter shape, but finite real matrices lack the required OrderClosedTopology
--   instance; this theorem supplies the nontrivial complexification and order-reflection
--   bridge rather than merely renaming the abstract theorem
-- coverage search: queries for "Lowner order limit tendsto eventual inequality matrices",
--   "le_of_tendsto_of_tendsto", and "positive semidefinite matrices closed set topology"
--   found Mathlib.le_of_tendsto_of_tendsto for OrderClosedTopology and the staged
--   continuous real-matrix complexification, but no real-matrix theorem or closed-order
--   instance; the closest SOptLib result is the strictly more specialized finite-sum
--   scalar theorem Filter.sum_le_mul_of_tendsto_of_eventually
-- minimal hypotheses: Finite supports finite square-matrix algebra and complexification
--   after installing computational instances locally; Filter.NeBot is required by passage
--   of eventual order to limits; convergence and eventual Loewner order are all minimal

/-- Limits of finite real square matrices preserve an eventual Loewner inequality.

If two matrix families converge along a nontrivial filter and the first is eventually
Loewner-bounded by the second, then their limits satisfy the same inequality.

Layer: Glue | Gap: Level 1 (closedness of finite real-matrix Loewner order under limits)
Proof: continuously complexify both convergent families, pass the eventual inequality to their limits using Mathlib's closed order on complex C-star matrices, and reflect positivity of the limiting difference back to real matrices.
Source: Mathlib `le_of_tendsto_of_tendsto`, finite-matrix positive-semidefiniteness, and `CStarMatrix` closed-order topology; SOptLib real-matrix complexification
Used in: regularization-limit steps for commuting PSD matrix products in Shampoo, matrix AdaGrad, and matrix multiplicative-weights analyses
Book citation: book/research/Source.json#/key_lemmas/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1 and 2 -/
theorem Matrix.le_of_tendsto_of_tendsto
    {ι : Type u} [Finite ι]
    {Z : Type v} {l : Filter Z} [l.NeBot]
    (f g : Z → Matrix ι ι ℝ) (A B : Matrix ι ι ℝ)
    (hf : Filter.Tendsto f l (nhds A))
    (hg : Filter.Tendsto g l (nhds B))
    (hfg : ∀ᶠ z in l, f z ≤ g z) :
    A ≤ B := by
  classical
  letI := Fintype.ofFinite ι
  let φ := SOptLib.realMatrixComplexification (ι := ι)
  have hφ_cont : Continuous φ :=
    SOptLib.continuous_realMatrixComplexification
  have hφ_nonneg_reflect (M : Matrix ι ι ℝ) (hM : 0 ≤ φ M) : 0 ≤ M := by
    let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
      (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
    let castM : Matrix ι ι ℂ := Matrix.map M fun r : ℝ => (r : ℂ)
    have hcomplexify : φ M = e castM := by rfl
    have hcast : 0 ≤ castM := by
      rw [← map_le_map_iff e]
      simpa [hcomplexify] using hM
    have hM_complex : castM.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castM] using hM_complex.1.apply i j
    · intro x
      let xc : ι →₀ ℂ :=
        x.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
      have hx := hM_complex.2 xc
      have hquadratic :
          xc.sum (fun i xi => xc.sum fun j xj => star xi * castM i j * xj) =
            ((x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj : ℝ) : ℂ) := by
        dsimp [xc]
        rw [Finsupp.sum_mapRange_index (by intro; simp)]
        simp only [Finsupp.sum,
          Finsupp.support_mapRange_of_injective Complex.ofReal_zero x
            Complex.ofReal_injective,
          castM, Matrix.map_apply]
        push_cast
        simp [Finsupp.mapRange_apply]
      rw [hquadratic] at hx
      exact (Complex.nonneg_iff.mp hx).1
  have hf_complex : Filter.Tendsto (fun z => φ (f z)) l (nhds (φ A)) :=
    hφ_cont.continuousAt.tendsto.comp hf
  have hg_complex : Filter.Tendsto (fun z => φ (g z)) l (nhds (φ B)) :=
    hφ_cont.continuousAt.tendsto.comp hg
  have hcomplex : φ A ≤ φ B :=
    _root_.le_of_tendsto_of_tendsto hf_complex hg_complex <|
      hfg.mono fun _ hz => OrderHomClass.mono φ hz
  rw [Matrix.le_iff]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply hφ_nonneg_reflect
  rw [map_sub]
  exact sub_nonneg.mpr hcomplex


-- Generalization plan (G0):
-- concept/name: logarithm of a commuting product; orig was cfc_log_mul_of_commute
-- generality used: complete normed real star-algebra with a real continuous functional
--   calculus, star order, and nonnegative spectra; two pointwise strict-positivity hypotheses
-- portable call pattern: operator preconditioner proofs rewriting the logarithm of a product
--   of commuting positive invertible factors; the carrier and factors may vary
-- counterargument checked: not paper-local or a pure wrapper; Mathlib's CFC logarithm module
--   explicitly records this commuting-product law as a missing theorem
-- coverage search: searched "continuous functional calculus logarithm product equality sum
--   commuting strictly positive" and "CFC.log mul commute strictly positive"; Mathlib has
--   `Real.log_mul`, `CFC.exp_log`, `CFC.log_exp`, and commutation transport, but not this theorem
-- minimal hypotheses: strict positivity is pointwise; completeness is used only by the
--   Banach-algebra exponential product law, and no finite-dimensional assumption is used

/-- The continuous-functional-calculus logarithm sends a product of commuting strictly positive
elements to the sum of their logarithms.

Layer: Glue | Gap: Level 1 (CFC logarithm of a commuting positive product)
Proof: transport commutation through the real functional calculus, express the product as the
  exponential of the sum of logarithms, then cancel exponential with `CFC.log_exp`.
Source: Mathlib continuous functional calculus `CFC.exp_log`, `CFC.log_exp`,
  `Commute.cfc_real`, and Banach-algebra `NormedSpace.exp_add_of_commute`
Used in: splitting logarithms of commuting positive operator preconditioner factors when proving
  multiplicativity of real operator powers
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization -/
theorem CFC.log_mul_of_commute
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a b : A) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hab : Commute a b) :
    CFC.log (a * b) = CFC.log a + CFC.log b := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hlogcomm : Commute (CFC.log a) (CFC.log b) :=
    ((hab.cfc_real Real.log).symm.cfc_real Real.log).symm
  calc
    CFC.log (a * b) =
        CFC.log (NormedSpace.exp (CFC.log a + CFC.log b)) := by
      rw [NormedSpace.exp_add_of_commute hlogcomm,
        CFC.exp_log a ha, CFC.exp_log b hb]
    _ = CFC.log a + CFC.log b :=
      CFC.log_exp _ (IsSelfAdjoint.log.add IsSelfAdjoint.log)


-- Generalization plan (G0):
-- concept/name: exponential-logarithm representation of a CFC real power; orig was
--   positiveMatrixRpow_eq_exp_log
-- generality used: normed real star-algebra with a real continuous functional
--   calculus, star order, and nonnegative spectra; one pointwise strict-positivity hypothesis
-- portable call pattern: positive operator-power proofs rewrite `CFC.rpow a t` as the
--   exponential of `t • CFC.log a`; the carrier, positive operator, and real exponent vary
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it composes
--   CFC power, logarithm, scalar multiplication, and exponential through a nontrivial CFC
--   composition argument, and Mathlib's rpow module explicitly lists the relation as a TODO
-- coverage search: queried "continuous functional calculus real power equals exponential scalar
--   multiple logarithm strictly positive" and "CFC rpow equality exp smul log of strictly
--   positive"; Mathlib has `Real.rpow_def_of_pos`, `CFC.rpow_eq_cfc_real`, and
--   `CFC.real_exp_eq_normedSpace_exp`, while SOptLib has no theorem covering this equality
-- minimal hypotheses: strict positivity is pointwise and supplies positivity of spectral values;
--   no completeness or finite-dimensional assumption is used

/-- The real continuous-functional-calculus power of a strictly positive element is the
exponential of the exponent scaling its logarithm.

Layer: Glue | Gap: Level 1 (CFC real power exponential-logarithm representation)
Proof: rewrite the power and scaled logarithm as real continuous functional calculi, use
  `Real.rpow_def_of_pos` on the strictly positive spectrum, and compose with the exponential CFC.
Source: Mathlib continuous functional calculus `CFC.rpow_eq_cfc_real`, `CFC.log`,
  `CFC.real_exp_eq_normedSpace_exp`, `cfc_comp'`, and scalar `Real.rpow_def_of_pos`
Used in: positive operator geometric-mean proofs that convert real powers into exponentials so
  commuting logarithms can be split and exponential product laws applied
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization -/
theorem CFC.rpow_eq_exp_smul_log
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a : A) (t : ℝ) (ha : IsStrictlyPositive a) :
    CFC.rpow a t = NormedSpace.exp (t • CFC.log a) := by
  have hlogcont : ContinuousOn Real.log (spectrum ℝ a) := by
    fun_prop (disch := intro x hx; exact ne_of_gt (ha.spectrum_pos hx))
  have hself : IsSelfAdjoint (t • CFC.log a) := by
    rw [CFC.log, ← cfc_const_mul (R := ℝ) t Real.log a (hf := hlogcont)]
    exact cfc_predicate _ a
  have hmulcont : ContinuousOn (fun x : ℝ => t * Real.log x) (spectrum ℝ a) := by
    fun_prop (disch := intro x hx; exact ne_of_gt (ha.spectrum_pos hx))
  have hexpcont : ContinuousOn Real.exp
      ((fun x : ℝ => t * Real.log x) '' spectrum ℝ a) :=
    Real.continuous_exp.continuousOn
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha.nonneg]
  rw [← CFC.real_exp_eq_normedSpace_exp hself]
  rw [CFC.log, ← cfc_const_mul (R := ℝ) t Real.log a (hf := hlogcont)]
  calc
    cfc (fun x : ℝ => x ^ t) a =
        cfc (fun x : ℝ => Real.exp (t * Real.log x)) a := by
      apply cfc_congr
      intro x hx
      change x ^ t = Real.exp (t * Real.log x)
      rw [Real.rpow_def_of_pos (ha.spectrum_pos hx)]
      congr 1
      ring
    _ = cfc Real.exp (cfc (fun x : ℝ => t * Real.log x) a) :=
      cfc_comp' (R := ℝ) Real.exp (fun x : ℝ => t * Real.log x) a
        (hg := hexpcont) (hf := hmulcont) (ha := ha.isSelfAdjoint)


-- Generalization plan (G0):
-- concept/name: multiplicativity of real CFC powers on commuting strictly positive elements;
--   orig was positiveMatrixRpow_mul_of_commute
-- generality used: complete normed real star-algebra with a real continuous functional
--   calculus, star order, and nonnegative spectra; two pointwise strict-positivity hypotheses
-- portable call pattern: matrix, operator-mean, and adaptive-preconditioner proofs distribute
--   a common real power over commuting positive invertible factors; carrier, factors, and
--   exponent may vary while the multiplicative conclusion is unchanged
-- counterargument checked: this is not paper-local traceability or a pure rename; it composes
--   strict positivity of a commuting product, logarithmic additivity, commutation transport,
--   and the Banach-algebra exponential product law into the standard power law
-- coverage search: queried "continuous functional calculus real power product equality
--   commuting strictly positive" and "CFC rpow mul commute"; Mathlib supplies
--   `IsStrictlyPositive.commute_iff` and `NormedSpace.exp_add_of_commute`, and staged Glue
--   supplies `CFC.log_mul_of_commute` and `CFC.rpow_eq_exp_smul_log`, but no declaration has
--   the resulting multiplicativity statement, so coverage is partial
-- minimal hypotheses: strict positivity is pointwise, commutation is a single `Commute`
--   hypothesis, completeness is required by the exponential product law, and no
--   finite-dimensional assumption is used

/-- A real continuous-functional-calculus power distributes over the product of two commuting
strictly positive elements.

Layer: Glue | Gap: Level 1 (multiplicativity of CFC real powers on commuting positive elements)
Proof: rewrite each real power as an exponential of a scaled logarithm, split the product
  logarithm with `CFC.log_mul_of_commute`, and apply `NormedSpace.exp_add_of_commute` after
  transporting commutation through the real functional calculus.
Source: Mathlib `IsStrictlyPositive.commute_iff`, `Commute.cfc_real`, and Banach-algebra
  `NormedSpace.exp_add_of_commute`, together with the CFC logarithm and rpow exponential bridges
Used in: distributing a common real power across commuting positive-definite factors in ordered
  preconditioner products and weighted operator geometric-mean arguments
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization -/
theorem CFC.rpow_mul_of_commute
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a b : A) (t : ℝ) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hab : Commute a b) :
    CFC.rpow (a * b) t = CFC.rpow a t * CFC.rpow b t := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hprod : IsStrictlyPositive (a * b) := (ha.commute_iff hb).mp hab
  have hlogcomm : Commute (CFC.log a) (CFC.log b) :=
    ((hab.cfc_real Real.log).symm.cfc_real Real.log).symm
  rw [CFC.rpow_eq_exp_smul_log (a * b) t hprod,
    CFC.rpow_eq_exp_smul_log a t ha, CFC.rpow_eq_exp_smul_log b t hb,
    CFC.log_mul_of_commute a b ha hb hab, smul_add]
  exact NormedSpace.exp_add_of_commute ((hlogcomm.smul_left t).smul_right t)


-- Generalization plan (G0):
-- concept/name: strict positivity of a product of pairwise-commuting elements; orig was
--   orderedMatrixProduct_posDef_of_pairwise_comm
-- generality used: ordered real star-algebra with real continuous functional calculus and
--   nonnegative spectra; an arbitrary list, with pointwise strict positivity and pairwise commute
-- portable call pattern: finite products of commuting positive-invertible operator
--   preconditioners; the carrier, list length, factors, and indexing construction may vary
-- counterargument checked: the binary closure step is Mathlib's
--   `IsStrictlyPositive.commute_iff`, but neither Mathlib nor SOptLib lifts it to list products;
--   the induction and head-to-tail-product commutation are reusable beyond the paper
-- coverage search: searched "list product strictly positive pairwise commute", "IsStrictlyPositive
--   product commute", and Mathlib sources for `IsStrictlyPositive` with `List.prod`; top hits were
--   the binary `IsStrictlyPositive.commute_iff` and `Commute.list_prod_right`, so coverage is partial
-- minimal hypotheses: list membership hypotheses replace the matrix-indexed family assumptions;
--   pairwise commutation suffices, and no norm, completeness, or finite-dimensionality is used

/-- The product of a pairwise-commuting list of strictly positive elements is strictly positive.

Layer: Glue | Gap: Level 1 (strict positivity of finite commuting products)
Proof: induct on the list, commute the head with the tail product using
  `Commute.list_prod_right`, and apply Mathlib's binary `IsStrictlyPositive.commute_iff`.
Source: Mathlib ordered star-algebra strict positivity, real continuous functional calculus,
  and noncommutative list-product commutation APIs
Used in: proving that an ordered product of commuting positive-definite operator powers is a
  positive-definite preconditioner in the multivariate geometric-mean monotonicity step
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization -/
theorem List.prod_isStrictlyPositive_of_pairwise_commute
    {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A]
    (l : List A) (hpos : ∀ a ∈ l, IsStrictlyPositive a) (hcomm : l.Pairwise Commute) :
    IsStrictlyPositive l.prod := by
  induction l with
  | nil =>
      exact isStrictlyPositive_one
  | cons a l ih =>
      rw [List.pairwise_cons] at hcomm
      rw [List.prod_cons]
      apply ((hpos a (by simp)).commute_iff
        (ih (fun b hb => hpos b (by simp [hb])) hcomm.2)).mp
      exact Commute.list_prod_right l a hcomm.1


-- Generalization plan (G0):
-- concept/name: multiplicativity of real CFC powers over finite pairwise-commuting products;
--   orig was positiveMatrixRpow_orderedMatrixProduct
-- generality used: an arbitrary complete normed real star-algebra with star order, nonnegative
--   spectra, and real continuous functional calculus; an arbitrary list and real exponent
-- portable call pattern: finite operator-product and preconditioner proofs distribute a common
--   real power over pairwise-commuting positive-invertible factors; the carrier, factors, list
--   length, and exponent may vary while the equality has the same shape
-- counterargument checked: this is not paper-local traceability or a pure wrapper; the binary
--   multiplication law and strict positivity of commuting list products exist, but their finite
--   induction with preservation of the ordered product is a reusable missing API theorem
-- coverage search: queried "real CFC power finite list product pairwise commuting strictly
--   positive" and "rpow product commute strictly positive" with project symbol search and
--   Mathlib LeanSearch; top hits were `CFC.rpow_mul_of_commute`,
--   `List.prod_isStrictlyPositive_of_pairwise_commute`, scalar `Real.list_prod_map_rpow`, and
--   product-type maps `CFC.rpow_map_prod`, so coverage is partial rather than duplicative
-- minimal hypotheses: strict positivity is required only for members of the list and pairwise
--   commutation suffices; completeness supports the binary exponential proof, with no
--   finite-dimensional or matrix-specific assumption

/-- A real continuous-functional-calculus power distributes over a finite ordered product of
pairwise-commuting strictly positive elements.

Layer: Glue | Gap: Level 1 (multiplicativity of CFC real powers over finite commuting products)
Proof: induct on the list, derive strict positivity of each commuting tail product, and apply
  `CFC.rpow_mul_of_commute` after lifting head-to-factor commutation to the tail product.
Source: Mathlib noncommutative list products and real continuous functional calculus, together
  with the binary CFC rpow multiplication and commuting-list strict-positivity bridges
Used in: distributing a common operator power through the ordered product of commuting
  positive-definite preconditioner factors in a multivariate geometric-mean argument
Book citation: book/research/Source.json#/key_lemmas/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization -/
theorem CFC.rpow_list_prod_of_pairwise_commute
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (l : List A) (t : ℝ)
    (hpos : ∀ a ∈ l, IsStrictlyPositive a) (hcomm : l.Pairwise Commute) :
    CFC.rpow l.prod t = (l.map fun a => CFC.rpow a t).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons] at hcomm
      have ha : IsStrictlyPositive a := hpos a (by simp)
      have htail_pos : ∀ b ∈ l, IsStrictlyPositive b := by
        intro b hb
        exact hpos b (by simp [hb])
      have hprod_pos : IsStrictlyPositive l.prod :=
        List.prod_isStrictlyPositive_of_pairwise_commute l htail_pos hcomm.2
      have haprod : Commute a l.prod := Commute.list_prod_right l a hcomm.1
      rw [List.prod_cons, CFC.rpow_mul_of_commute a l.prod t ha hprod_pos haprod,
        ih htail_pos hcomm.2, List.map_cons, List.prod_cons]


open scoped ContinuousFunctionalCalculus MatrixOrder Matrix.Norms.Operator

namespace Matrix

-- Generalization plan (G0):
-- concept/name: commuting evaluation of the binary weighted Kubo--Ando geometric mean;
--   orig was `Shampoo.binaryWeightedGeometricMean_eq_rpow_mul_of_commute`
-- generality used: arbitrary finite index type with decidable equality, two positive-definite
--   real square matrices, an unrestricted real weight, and a `Commute` hypothesis
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights, and
--   operator-interpolation proofs vary the finite dimension, positive-definite matrices, and
--   weight while reducing the same binary operator mean to complementary commuting powers
-- counterargument checked: this is not paper-local traceability or a caller-side rewrite;
--   it is the standard commutative specification theorem for the named noncommutative mean,
--   and it combines conjugation, iterated-power, product-power, and exponent-addition laws
-- coverage search: queries for "binary weighted geometric mean equals complementary real
--   powers product commuting positive definite matrices" and "weighted geometric mean of
--   commuting positive definite matrices equals product of powers" found the staged mean API,
--   Mathlib CFC power laws, and `CFC.rpow_mul_of_commute`, but no full evaluation theorem
-- minimal hypotheses: positive definiteness of both inputs supplies all negative powers and
--   product strict positivity; commutation is pointwise and no unit-interval bound on the
--   weight is used

/-- For commuting positive-definite real matrices, the binary weighted geometric mean is the
product of the complementary real powers of its inputs.

Layer: Model | Gap: Level 1 (commuting evaluation of the binary weighted Kubo--Ando geometric mean)
Proof: commute the inverse half-power through the right input, distribute the middle CFC power over the resulting positive product, collapse the iterated inverse power, and combine the remaining powers of the left input
Source: Kubo--Ando operator means; Mathlib `CFC.rpow_add`, `CFC.rpow_rpow`, and commutation through continuous functional calculus, together with `CFC.rpow_mul_of_commute`
Used in: normalized finite-family operator interpolation for Shampoo-style matrix and tensor preconditioners, where a recursive binary mean of commuting factors must be converted back to an explicit weighted power product
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, commuting operator-mean evaluation -/
theorem binaryWeightedGeometricMean_eq_rpow_mul_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : Commute A B) :
    binaryWeightedGeometricMean A B t =
      CFC.rpow A (1 - t) * CFC.rpow B t := by
  let H := CFC.rpow A (1 / 2 : ℝ)
  let Aneg := CFC.rpow A (-(1 / 2 : ℝ))
  let N := CFC.rpow A (-1 : ℝ)
  let Npow := CFC.rpow A (-t)
  let Q := CFC.rpow B t
  have hN : IsStrictlyPositive N := by
    dsimp only [N]
    exact hA.isStrictlyPositive.rpow A (-1 : ℝ)
  have hNB : Commute N B := by
    dsimp only [N, CFC.rpow]
    exact hAB.cfc_nnreal (fun x => x ^ (-1 : ℝ))
  have hmiddle : IsStrictlyPositive (N * B) :=
    (hN.commute_iff hB.isStrictlyPositive).mp hNB
  have hAnegB : Commute Aneg B := by
    dsimp only [Aneg, CFC.rpow]
    exact hAB.cfc_nnreal (fun x => x ^ (-(1 / 2 : ℝ)))
  have hmiddle_eq : Aneg * B * Aneg = N * B := by
    calc
      Aneg * B * Aneg = (Aneg * Aneg) * B := by
        rw [mul_assoc, hAnegB.symm.eq, ← mul_assoc]
      _ = N * B := by
        congr 1
        dsimp only [Aneg, N]
        rw [show CFC.rpow A (-(1 / 2 : ℝ)) * CFC.rpow A (-(1 / 2 : ℝ)) =
            CFC.rpow A ((-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ))) by
          simpa only [CFC.rpow_eq_pow] using
            (CFC.rpow_add (a := A) (x := -(1 / 2 : ℝ))
              (y := -(1 / 2 : ℝ)) hA.isUnit).symm]
        congr 1
        ring
  have hQH : Commute Q H := by
    dsimp only [Q, H, CFC.rpow]
    exact (hAB.cfc_nnreal (fun x => x ^ (1 / 2 : ℝ))).symm.cfc_nnreal
      (fun x => x ^ t)
  change
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A *
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
          (cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A * B *
            cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A) *
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A =
      CFC.rpow A (1 - t) * Q
  have hHcfc :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A = H :=
    (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm
  have hAnegcfc :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A =
        Aneg :=
    (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm
  rw [hHcfc, hAnegcfc, hmiddle_eq,
    ← CFC.rpow_eq_cfc_real hmiddle.nonneg]
  change H * CFC.rpow (N * B) t * H = CFC.rpow A (1 - t) * Q
  rw [CFC.rpow_mul_of_commute N B t hN hB.isStrictlyPositive hNB]
  rw [show CFC.rpow (CFC.rpow A (-1 : ℝ)) t = CFC.rpow A ((-1 : ℝ) * t) by
    simpa only [CFC.rpow_eq_pow] using
      CFC.rpow_rpow A (-1 : ℝ) t (by norm_num) hA.isStrictlyPositive]
  rw [show (-1 : ℝ) * t = -t by ring]
  change H * (Npow * Q) * H = CFC.rpow A (1 - t) * Q
  calc
    H * (Npow * Q) * H = H * (Npow * (Q * H)) := by
      simp only [mul_assoc]
    _ = H * (Npow * (H * Q)) := by rw [hQH.eq]
    _ = (H * Npow * H) * Q := by simp only [mul_assoc]
    _ = CFC.rpow A (((1 / 2 : ℝ) + (-t)) + (1 / 2 : ℝ)) * Q := by
      dsimp only [H, Npow]
      rw [show CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A (-t) =
          CFC.rpow A ((1 / 2 : ℝ) + (-t)) by
        simpa only [CFC.rpow_eq_pow] using
          (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ)) (y := -t) hA.isUnit).symm]
      rw [show CFC.rpow A ((1 / 2 : ℝ) + (-t)) * CFC.rpow A (1 / 2 : ℝ) =
          CFC.rpow A (((1 / 2 : ℝ) + (-t)) + (1 / 2 : ℝ)) by
        simpa only [CFC.rpow_eq_pow] using
          (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ) + (-t))
            (y := (1 / 2 : ℝ)) hA.isUnit).symm]
    _ = CFC.rpow A (1 - t) * Q := by
      congr 2
      ring

end Matrix


open scoped BigOperators ContinuousFunctionalCalculus MatrixOrder Matrix.Norms.Operator

namespace Matrix

-- Generalization plan (G0):
-- concept/name: normalized head--tail factorization of a finite product of commuting
--   positive-definite matrix powers; orig was
--   `Shampoo.orderedMatrixProduct_eq_binaryMean_cons_normalized`
-- generality used: arbitrary finite matrix index type, an arbitrary positive tail length,
--   positive-definite real matrices, pairwise commutation, and strictly positive tail weights
--   summing with the head weight to one; the redundant positive-definiteness premise for the
--   normalized tail product is derived from these hypotheses
-- portable call pattern: finite operator-mean inductions in full-matrix adaptive-gradient,
--   matrix multiplicative-weights, and tensor-preconditioner proofs vary the commuting
--   family and normalized weights while splitting the same weighted product into its head
--   and normalized tail
-- counterargument checked: this is not a caller-side expression or paper-local wrapper;
--   it combines head--tail reindexing, positivity and commutation of a finite product,
--   distribution of a CFC power over that product, and normalization of every exponent
-- coverage search: queries for "product real powers commuting positive definite family
--   equals binary weighted geometric mean head normalized tail" and "list product rpow
--   normalized weights binary geometric mean" found the component theorems
--   `CFC.rpow_list_prod_of_pairwise_commute` and
--   `Matrix.binaryWeightedGeometricMean_eq_rpow_mul_of_commute`, but no theorem with this
--   normalized finite-family conclusion
-- minimal hypotheses: tail nonemptiness is needed for positivity of its weight sum;
--   positive definiteness supplies all real powers, pairwise commutation is pointwise,
--   and no separate positivity hypothesis on the normalized tail product is retained

/-- A finite ordered product of powers of commuting positive-definite matrices is the binary
weighted geometric mean of its head and the product of its normalized tail powers.

Layer: Glue | Gap: Level 2 (normalized head--tail factorization of a commuting weighted matrix product)
Proof: split the `List.ofFn` product at its head, derive positivity and commutation of the normalized tail product, evaluate the binary mean on commuting inputs, distribute its tail power with `CFC.rpow_list_prod_of_pairwise_commute`, and cancel the normalization in each exponent
Source: Kubo--Ando weighted geometric means, Mathlib finite-list products, and continuous-functional-calculus real-power laws
Used in: finite-family operator-mean induction for matrix and tensor preconditioners, where the induction hypothesis compares normalized tails before binary joint monotonicity is applied
Book citation: book/research/Source.json#/key_lemmas/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 5 finite commuting operator-mean induction -/
theorem prod_rpow_eq_binaryWeightedGeometricMean_cons_normalized
    {q : ℕ} [Nonempty (Fin q)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin (q + 1) → Matrix ι ι ℝ) (β : Fin (q + 1) → ℝ)
    (hA : ∀ i, (A i).PosDef) (hcomm : ∀ i j, Commute (A i) (A j))
    (hβ : ∀ i : Fin q, 0 < β i.succ) (hβ_sum : (∑ i, β i) = 1) :
    let s := ∑ i : Fin q, β i.succ
    let P := (List.ofFn fun i : Fin q => CFC.rpow (A i.succ) (β i.succ / s)).prod
    (List.ofFn fun i : Fin (q + 1) => CFC.rpow (A i) (β i)).prod =
      binaryWeightedGeometricMean (A 0) P s := by
  classical
  dsimp only
  let s : ℝ := ∑ i : Fin q, β i.succ
  let F : Fin q → Matrix ι ι ℝ := fun i =>
    CFC.rpow (A i.succ) (β i.succ / s)
  have hs_pos : 0 < s := by
    apply Finset.sum_pos'
    · intro i _hi
      exact (hβ i).le
    · let i : Fin q := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, hβ i⟩
  have hs_eq : β 0 + s = 1 := by
    simpa only [s] using (Fin.sum_univ_succ β).symm.trans hβ_sum
  have hhead : 1 - s = β 0 := by
    linarith
  have hFpos : ∀ a ∈ List.ofFn F, IsStrictlyPositive a := by
    rw [List.forall_mem_ofFn_iff]
    intro i
    exact (hA i.succ).isStrictlyPositive.rpow (A i.succ) (β i.succ / s)
  have hFcomm : (List.ofFn F).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _hij
    dsimp only [F, CFC.rpow]
    exact ((hcomm i.succ j.succ).cfc_nnreal
      (fun x => x ^ (β i.succ / s))).symm.cfc_nnreal
        (fun x => x ^ (β j.succ / s)) |>.symm
  have hPpos : IsStrictlyPositive (List.ofFn F).prod :=
    List.prod_isStrictlyPositive_of_pairwise_commute (List.ofFn F) hFpos hFcomm
  have hheadF : ∀ a ∈ List.ofFn F, Commute (A 0) a := by
    rw [List.forall_mem_ofFn_iff]
    intro i
    dsimp only [F, CFC.rpow]
    exact ((hcomm i.succ 0).cfc_nnreal
      (fun x => x ^ (β i.succ / s))).symm
  have hheadP : Commute (A 0) (List.ofFn F).prod :=
    Commute.list_prod_right (List.ofFn F) (A 0) hheadF
  have hdistributed :
      CFC.rpow (List.ofFn F).prod s =
        (List.ofFn fun i => CFC.rpow (F i) s).prod := by
    calc
      CFC.rpow (List.ofFn F).prod s =
          ((List.ofFn F).map fun a => CFC.rpow a s).prod :=
        CFC.rpow_list_prod_of_pairwise_commute (List.ofFn F) s hFpos hFcomm
      _ = (List.ofFn fun i => CFC.rpow (F i) s).prod := by
        rw [← List.ofFn_comp']
  have hfactor_evaluation :
      (fun i => CFC.rpow (F i) s) =
        (fun i : Fin q => CFC.rpow (A i.succ) (β i.succ)) := by
    funext i
    dsimp only [F]
    rw [show CFC.rpow (CFC.rpow (A i.succ) (β i.succ / s)) s =
        CFC.rpow (A i.succ) ((β i.succ / s) * s) by
      simpa only [CFC.rpow_eq_pow] using
        CFC.rpow_rpow (A i.succ) (β i.succ / s) s
          (div_ne_zero (hβ i).ne' hs_pos.ne') (hA i.succ).isStrictlyPositive]
    have hexponent : (β i.succ / s) * s = β i.succ := by
      field_simp [hs_pos.ne']
    rw [hexponent]
  rw [show (List.ofFn fun i : Fin (q + 1) => CFC.rpow (A i) (β i)).prod =
      CFC.rpow (A 0) (β 0) *
        (List.ofFn fun i : Fin q => CFC.rpow (A i.succ) (β i.succ)).prod by
    rw [List.ofFn_succ, List.prod_cons]]
  rw [binaryWeightedGeometricMean_eq_rpow_mul_of_commute
    (A 0) (List.ofFn F).prod s (hA 0)
    (Matrix.isStrictlyPositive_iff_posDef.mp hPpos) hheadP,
    hdistributed, hfactor_evaluation, hhead]

end Matrix


open scoped BigOperators ContinuousFunctionalCalculus MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: Loewner monotonicity of a normalized weighted `List.ofFn` product
--   of powers of two internally commuting PSD matrix families; orig was
--   `Shampoo.Lemma_5_Ando_geometric_mean`, renamed
--   `Matrix.list_prod_cfc_rpow_mono_of_pairwise_commute`
-- generality used: arbitrary family length and arbitrary finite decidable matrix-coordinate
--   type, two real PSD matrix families, coordinatewise Loewner order, internal pairwise
--   commutation, and nonnegative weights summing to one; no optimization setup is retained
-- portable call pattern: operator-mean, full-matrix adaptive-gradient, and tensor-mode
--   preconditioner proofs vary the two commuting PSD families, finite matrix coordinate type,
--   and normalized weights while retaining the same weighted-product Loewner inequality
-- counterargument checked: this is not paper-local traceability or a one-line wrapper; it
--   assembles positive-definite finite-family operator-mean induction, deletion of zero-weight
--   factors, singular PSD regularization, continuity of spectral powers, and closedness of
--   Loewner order under limits
-- coverage search: queries for "weighted product matrix powers Loewner order commuting
--   families" and "list product cfc rpow monotone positive semidefinite pairwise commute"
--   found the component declarations `Matrix.binaryWeightedGeometricMean_mono`,
--   `Matrix.prod_rpow_eq_binaryWeightedGeometricMean_cons_normalized`,
--   `List.prod_ofFn_removeNth_of_eq_one`, and `Matrix.le_of_tendsto_of_tendsto`, but no
--   declaration with this multivariate singular-PSD conclusion
-- minimal hypotheses: matrix coordinates are generalized from `Fin n`; nonnegative weights
--   and their normalization are sharp, while pairwise commutation is required only within
--   each family and no cross-family commutation is assumed

/-- Coordinatewise Loewner order between two internally commuting PSD matrix families lifts
to the ordered products of their continuous-functional-calculus powers at normalized
nonnegative weights.

Layer: Glue | Gap: Level 2 (multivariate weighted-product Loewner monotonicity for commuting PSD matrices)
Proof: prove the positive-definite case by normalized head--tail induction and binary Kubo--Ando monotonicity, remove zero-weight factors by finite reindexing, then regularize singular PSD inputs by positive scalar identities and pass the product inequality to the limit.
Source: Ando--Li--Mathias multivariate geometric means, Kubo--Ando binary operator means, and Mathlib finite-matrix continuous functional calculus and Loewner order
Used in: matrix and tensor adaptive-preconditioner domination steps that compare normalized products of fractional powers of commuting accumulator families
Book citation: book/research/Source.json#/key_lemmas/6
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 5 -/
theorem list_prod_cfc_rpow_mono_of_pairwise_commute
    {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X Y : Fin q → Matrix κ κ ℝ) (alpha : Fin q → ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef)
    (hXY : ∀ i, X i ≤ Y i)
    (hXcomm : ∀ i j, Commute (X i) (X j))
    (hYcomm : ∀ i j, Commute (Y i) (Y j))
    (halpha_nonneg : ∀ i, 0 ≤ alpha i)
    (halpha_sum : (∑ i, alpha i) = 1) :
    (List.ofFn fun i =>
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ alpha i) (X i)).prod ≤
      (List.ofFn fun i =>
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ alpha i) (Y i)).prod := by
  classical
  have hXrpow : (fun i => CFC.rpow (X i) (alpha i)) =
      (fun i => cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ alpha i) (X i)) := by
    funext i
    change (X i) ^ alpha i = _
    exact CFC.rpow_eq_cfc_real (hX i).nonneg
  have hYrpow : (fun i => CFC.rpow (Y i) (alpha i)) =
      (fun i => cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ alpha i) (Y i)) := by
    funext i
    change (Y i) ^ alpha i = _
    exact CFC.rpow_eq_cfc_real (hY i).nonneg
  rw [← hXrpow, ← hYrpow]
  have hpositive_pd_order : ∀ {r : ℕ}
      (A B : Fin r → Matrix κ κ ℝ) (beta : Fin r → ℝ),
      (hA : ∀ i, (A i).PosDef) → (hB : ∀ i, (B i).PosDef) →
      (∀ i, A i ≤ B i) →
      (∀ i j, Commute (A i) (A j)) →
      (∀ i j, Commute (B i) (B j)) →
      (∀ i, 0 < beta i) → (∑ i, beta i) = 1 →
      (List.ofFn fun i => CFC.rpow (A i) (beta i)).prod ≤
        (List.ofFn fun i => CFC.rpow (B i) (beta i)).prod := by
    intro r
    induction r with
    | zero =>
        intro A B beta hA hB hAB hAcomm hBcomm hbeta hbeta_sum
        simp at hbeta_sum
    | succ r ih =>
        intro A B beta hA hB hAB hAcomm hBcomm hbeta hbeta_sum
        cases r with
        | zero =>
            have hbeta0 : beta 0 = 1 := by
              simpa [Fin.sum_univ_one] using hbeta_sum
            rw [List.ofFn_succ, List.ofFn_succ]
            simp only [List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, hbeta0]
            change (A 0) ^ (1 : ℝ) ≤ (B 0) ^ (1 : ℝ)
            rw [CFC.rpow_one (A 0) (hA 0).posSemidef.nonneg,
              CFC.rpow_one (B 0) (hB 0).posSemidef.nonneg]
            exact hAB 0
        | succ r =>
            let Atail : Fin (r + 1) → Matrix κ κ ℝ := fun i => A i.succ
            let Btail : Fin (r + 1) → Matrix κ κ ℝ := fun i => B i.succ
            let s : ℝ := ∑ i : Fin (r + 1), beta i.succ
            let gamma : Fin (r + 1) → ℝ := fun i => beta i.succ / s
            have hs_pos : 0 < s := by
              apply Finset.sum_pos'
              · intro i _hi
                exact (hbeta i.succ).le
              · exact ⟨(0 : Fin (r + 1)), Finset.mem_univ _, hbeta (0 : Fin (r + 1)).succ⟩
            have hgamma_pos : ∀ i, 0 < gamma i := by
              intro i
              exact div_pos (hbeta i.succ) hs_pos
            have hgamma_sum : (∑ i : Fin (r + 1), gamma i) = 1 := by
              simp only [gamma, ← Finset.sum_div]
              exact div_self hs_pos.ne'
            have hAtail : ∀ i, (Atail i).PosDef := fun i => hA i.succ
            have hBtail : ∀ i, (Btail i).PosDef := fun i => hB i.succ
            have hABtail : ∀ i, Atail i ≤ Btail i := fun i => hAB i.succ
            have hAtail_comm : ∀ i j, Commute (Atail i) (Atail j) :=
              fun i j => hAcomm i.succ j.succ
            have hBtail_comm : ∀ i j, Commute (Btail i) (Btail j) :=
              fun i j => hBcomm i.succ j.succ
            have htail_order := ih Atail Btail gamma hAtail hBtail hABtail
              hAtail_comm hBtail_comm hgamma_pos hgamma_sum
            let PA := (List.ofFn fun i : Fin (r + 1) =>
              CFC.rpow (Atail i) (gamma i)).prod
            let PB := (List.ofFn fun i : Fin (r + 1) =>
              CFC.rpow (Btail i) (gamma i)).prod
            have hPA : PA.PosDef := by
              change ((List.ofFn fun i : Fin (r + 1) =>
                CFC.rpow (Atail i) (gamma i)).prod).PosDef
              rw [← Matrix.isStrictlyPositive_iff_posDef]
              apply List.prod_isStrictlyPositive_of_pairwise_commute
              · rw [List.forall_mem_ofFn_iff]
                intro i
                exact (hAtail i).isStrictlyPositive.rpow (Atail i) (gamma i)
              · rw [List.pairwise_ofFn]
                intro i j _hij
                exact ((hAtail_comm i j).cfc_nnreal
                  (fun x => x ^ (gamma i))).symm.cfc_nnreal
                    (fun x => x ^ (gamma j)) |>.symm
            have hPB : PB.PosDef := by
              change ((List.ofFn fun i : Fin (r + 1) =>
                CFC.rpow (Btail i) (gamma i)).prod).PosDef
              rw [← Matrix.isStrictlyPositive_iff_posDef]
              apply List.prod_isStrictlyPositive_of_pairwise_commute
              · rw [List.forall_mem_ofFn_iff]
                intro i
                exact (hBtail i).isStrictlyPositive.rpow (Btail i) (gamma i)
              · rw [List.pairwise_ofFn]
                intro i j _hij
                exact ((hBtail_comm i j).cfc_nnreal
                  (fun x => x ^ (gamma i))).symm.cfc_nnreal
                    (fun x => x ^ (gamma j)) |>.symm
            have hPA_PB : PA ≤ PB := by
              exact htail_order
            have hs_eq : beta 0 + s = 1 := by
              simpa only [s] using (Fin.sum_univ_succ beta).symm.trans hbeta_sum
            have hs_nonneg : 0 ≤ s := hs_pos.le
            have hs_le_one : s ≤ 1 := by
              linarith [hbeta (0 : Fin (r + 2))]
            have hmean := Matrix.binaryWeightedGeometricMean_mono
              (A 0) PA (B 0) PB s (hA 0) hPA (hB 0) hPB
              (hAB 0) hPA_PB hs_nonneg hs_le_one
            have hevalA := Matrix.prod_rpow_eq_binaryWeightedGeometricMean_cons_normalized
              A beta hA hAcomm (fun i : Fin (r + 1) => hbeta i.succ) hbeta_sum
            have hevalB := Matrix.prod_rpow_eq_binaryWeightedGeometricMean_cons_normalized
              B beta hB hBcomm (fun i : Fin (r + 1) => hbeta i.succ) hbeta_sum
            dsimp only at hevalA hevalB
            rw [hevalA, hevalB]
            simpa [PA, PB, Atail, Btail, gamma, s] using hmean
  have hnonnegative_pd_order : ∀ (r : ℕ)
      (A B : Fin r → Matrix κ κ ℝ) (beta : Fin r → ℝ),
      (hA : ∀ i, (A i).PosDef) → (hB : ∀ i, (B i).PosDef) →
      (∀ i, A i ≤ B i) →
      (∀ i j, Commute (A i) (A j)) →
      (∀ i j, Commute (B i) (B j)) →
      (∀ i, 0 ≤ beta i) → (∑ i, beta i) = 1 →
      (List.ofFn fun i => CFC.rpow (A i) (beta i)).prod ≤
        (List.ofFn fun i => CFC.rpow (B i) (beta i)).prod := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro A B beta hA hB hAB hAcomm hBcomm hbeta_nonneg hbeta_sum
        by_cases hzero : ∃ p : Fin r, beta p = 0
        · rcases hzero with ⟨p, hp⟩
          cases r with
          | zero => exact Fin.elim0 p
          | succ r =>
              let A' : Fin r → Matrix κ κ ℝ := fun j => A (p.succAbove j)
              let B' : Fin r → Matrix κ κ ℝ := fun j => B (p.succAbove j)
              let beta' : Fin r → ℝ := fun j => beta (p.succAbove j)
              have hA' : ∀ j, (A' j).PosDef := fun j => hA (p.succAbove j)
              have hB' : ∀ j, (B' j).PosDef := fun j => hB (p.succAbove j)
              have hAB' : ∀ j, A' j ≤ B' j := fun j => hAB (p.succAbove j)
              have hAcomm' : ∀ i j, Commute (A' i) (A' j) :=
                fun i j => hAcomm (p.succAbove i) (p.succAbove j)
              have hBcomm' : ∀ i j, Commute (B' i) (B' j) :=
                fun i j => hBcomm (p.succAbove i) (p.succAbove j)
              have hbeta_nonneg' : ∀ j, 0 ≤ beta' j :=
                fun j => hbeta_nonneg (p.succAbove j)
              have hbeta_sum' : (∑ j, beta' j) = 1 := by
                have hs := Fin.sum_univ_succAbove beta p
                rw [hp, zero_add, hbeta_sum] at hs
                exact hs.symm
              have hsmall := ih r (Nat.lt_succ_self r) A' B' beta' hA' hB'
                hAB' hAcomm' hBcomm' hbeta_nonneg' hbeta_sum'
              have hApow_one : CFC.rpow (A p) (beta p) = 1 := by
                rw [hp]
                exact CFC.rpow_zero (A p) (hA p).posSemidef.nonneg
              have hBpow_one : CFC.rpow (B p) (beta p) = 1 := by
                rw [hp]
                exact CFC.rpow_zero (B p) (hB p).posSemidef.nonneg
              calc
                (List.ofFn fun i => CFC.rpow (A i) (beta i)).prod =
                    (List.ofFn fun j => CFC.rpow (A' j) (beta' j)).prod := by
                      simpa [A', beta'] using
                        (List.prod_ofFn_removeNth_of_eq_one
                          (fun i => CFC.rpow (A i) (beta i)) p hApow_one)
                _ ≤ (List.ofFn fun j => CFC.rpow (B' j) (beta' j)).prod := hsmall
                _ = (List.ofFn fun i => CFC.rpow (B i) (beta i)).prod := by
                      symm
                      simpa [B', beta'] using
                        (List.prod_ofFn_removeNth_of_eq_one
                          (fun i => CFC.rpow (B i) (beta i)) p hBpow_one)
        · apply hpositive_pd_order A B beta hA hB hAB hAcomm hBcomm
          · intro i
            exact lt_of_le_of_ne (hbeta_nonneg i) (Ne.symm (fun hi => hzero ⟨i, hi⟩))
          · exact hbeta_sum
  have hregularized_posSemidef (A : Matrix κ κ ℝ) (hA : A.PosSemidef)
      (delta : NNReal) :
      (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)).PosSemidef :=
    hA.add (Matrix.PosSemidef.one.smul delta.coe_nonneg)
  have hregularized_posDef (A : Matrix κ κ ℝ) (hA : A.PosSemidef)
      (delta : NNReal) (hdelta : 0 < delta) :
      (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)).PosDef :=
    Matrix.PosDef.posSemidef_add hA
      (Matrix.PosDef.one.smul (by exact_mod_cast hdelta))
  have hregularized_rpow_tendsto (A : Matrix κ κ ℝ) (a : ℝ)
      (hA : A.PosSemidef) (ha : 0 ≤ a) :
      Filter.Tendsto
        (fun delta : NNReal =>
          CFC.rpow (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)) a)
        (nhds 0) (nhds (CFC.rpow A a)) := by
    let U : unitary (Matrix κ κ ℝ) := hA.1.eigenvectorUnitary
    let lam : κ → ℝ := hA.1.eigenvalues
    let D : Matrix κ κ ℝ := Matrix.diagonal lam
    have hdiag : A = (U : Matrix κ κ ℝ) * D * star (U : Matrix κ κ ℝ) := by
      simpa [U, D, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hA.1.spectral_theorem
    have hpow : ∀ delta : NNReal,
        CFC.rpow (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)) a =
          (U : Matrix κ κ ℝ) *
            Matrix.diagonal (fun i => (lam i + (delta : ℝ)) ^ a) *
              star (U : Matrix κ κ ℝ) := by
      intro delta
      change (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)) ^ a = _
      rw [CFC.rpow_eq_cfc_real
        (hregularized_posSemidef A hA delta).nonneg]
      exact Matrix.cfc_rpow_eq_of_unitary_diagonalization
        (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)) a U
        (fun i => lam i + (delta : ℝ))
        (Matrix.add_smul_one_eq_unitary_diagonalization_add A U lam
          (by simpa [D] using hdiag) (delta : ℝ))
    have hpow_zero : CFC.rpow A a =
        (U : Matrix κ κ ℝ) * Matrix.diagonal (fun i => (lam i) ^ a) *
          star (U : Matrix κ κ ℝ) := by
      change A ^ a = _
      rw [CFC.rpow_eq_cfc_real hA.nonneg]
      exact Matrix.cfc_rpow_eq_of_unitary_diagonalization A a U lam hdiag
    let spectral : NNReal → Matrix κ κ ℝ := fun delta =>
      (U : Matrix κ κ ℝ) *
        Matrix.diagonal (fun i => (lam i + (delta : ℝ)) ^ a) *
          star (U : Matrix κ κ ℝ)
    have hcont : Continuous spectral := by
      have hentry : ∀ i : κ,
          Continuous (fun delta : NNReal => (lam i + (delta : ℝ)) ^ a) := by
        intro i
        exact (Real.continuous_rpow_const ha).comp
          (continuous_const.add NNReal.continuous_coe)
      have hdiag_cont : Continuous (fun delta : NNReal =>
          (Matrix.diagonal (fun i : κ => (lam i + (delta : ℝ)) ^ a) :
            Matrix κ κ ℝ)) := by
        apply continuous_matrix
        intro i j
        by_cases hij : i = j
        · subst j
          simpa using hentry i
        · simpa [Matrix.diagonal_apply, hij] using
            (continuous_const : Continuous (fun _ : NNReal => (0 : ℝ)))
      simpa only [spectral] using
        (continuous_const.mul hdiag_cont).mul continuous_const
    have hzero : spectral 0 = CFC.rpow A a := by
      rw [hpow_zero]
      simp only [spectral, NNReal.coe_zero, add_zero]
    have ht : Filter.Tendsto spectral (nhds 0) (nhds (CFC.rpow A a)) := by
      have ht0 : Filter.Tendsto spectral (nhds 0) (nhds (spectral 0)) :=
        hcont.continuousAt
      rw [hzero] at ht0
      exact ht0
    exact ht.congr' (Filter.Eventually.of_forall fun delta => by
      change spectral delta = CFC.rpow
        (A + (delta : ℝ) • (1 : Matrix κ κ ℝ)) a
      exact (hpow delta).symm)
  let epsilon : ℕ → NNReal := fun k => 1 / (k + 1)
  have hepsilon_pos : ∀ k, 0 < epsilon k := by
    intro k
    simp [epsilon]
  have hepsilon_tendsto : Filter.Tendsto epsilon Filter.atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun k : ℕ => (1 / (k + 1) : NNReal)) Filter.atTop (nhds 0))
  let Xreg : NNReal → Fin q → Matrix κ κ ℝ := fun delta i =>
    X i + (delta : ℝ) • (1 : Matrix κ κ ℝ)
  let Yreg : NNReal → Fin q → Matrix κ κ ℝ := fun delta i =>
    Y i + (delta : ℝ) • (1 : Matrix κ κ ℝ)
  let XregPow : NNReal → Fin q → Matrix κ κ ℝ := fun delta i =>
    CFC.rpow (Xreg delta i) (alpha i)
  let YregPow : NNReal → Fin q → Matrix κ κ ℝ := fun delta i =>
    CFC.rpow (Yreg delta i) (alpha i)
  have hregularized_order : ∀ k,
      (List.ofFn (XregPow (epsilon k))).prod ≤
        (List.ofFn (YregPow (epsilon k))).prod := by
    intro k
    have hXreg_pd : ∀ i, (Xreg (epsilon k) i).PosDef := by
      intro i
      exact hregularized_posDef (X i) (hX i) (epsilon k) (hepsilon_pos k)
    have hYreg_pd : ∀ i, (Yreg (epsilon k) i).PosDef := by
      intro i
      exact hregularized_posDef (Y i) (hY i) (epsilon k) (hepsilon_pos k)
    have hXYreg : ∀ i, Xreg (epsilon k) i ≤ Yreg (epsilon k) i := by
      intro i
      simpa [Xreg, Yreg, add_comm] using
        (add_le_add_right (hXY i)
          ((epsilon k : ℝ) • (1 : Matrix κ κ ℝ)))
    have hXreg_comm : ∀ i j, Commute (Xreg (epsilon k) i) (Xreg (epsilon k) j) := by
      intro i j
      show Xreg (epsilon k) i * Xreg (epsilon k) j =
        Xreg (epsilon k) j * Xreg (epsilon k) i
      dsimp [Xreg]
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      rw [(hXcomm i j).eq]
      simp only [smul_add]
      abel
    have hYreg_comm : ∀ i j, Commute (Yreg (epsilon k) i) (Yreg (epsilon k) j) := by
      intro i j
      show Yreg (epsilon k) i * Yreg (epsilon k) j =
        Yreg (epsilon k) j * Yreg (epsilon k) i
      dsimp [Yreg]
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      rw [(hYcomm i j).eq]
      simp only [smul_add]
      abel
    exact hnonnegative_pd_order q (Xreg (epsilon k)) (Yreg (epsilon k)) alpha
      hXreg_pd hYreg_pd hXYreg hXreg_comm hYreg_comm halpha_nonneg halpha_sum
  have hXfactor_tendsto : ∀ i,
      Filter.Tendsto (fun k => XregPow (epsilon k) i) Filter.atTop
        (nhds (CFC.rpow (X i) (alpha i))) := by
    intro i
    dsimp [XregPow, Xreg]
    exact (hregularized_rpow_tendsto (X i) (alpha i) (hX i)
      (halpha_nonneg i)).comp hepsilon_tendsto
  have hYfactor_tendsto : ∀ i,
      Filter.Tendsto (fun k => YregPow (epsilon k) i) Filter.atTop
        (nhds (CFC.rpow (Y i) (alpha i))) := by
    intro i
    dsimp [YregPow, Yreg]
    exact (hregularized_rpow_tendsto (Y i) (alpha i) (hY i)
      (halpha_nonneg i)).comp hepsilon_tendsto
  have hXproduct_tendsto :
      Filter.Tendsto (fun k => (List.ofFn (XregPow (epsilon k))).prod)
        Filter.atTop
        (nhds ((List.ofFn fun i => CFC.rpow (X i) (alpha i)).prod)) := by
    simpa only [List.map_ofFn] using
      (tendsto_list_prod (List.ofFn (fun i : Fin q => i)) (fun i _hi =>
        hXfactor_tendsto i))
  have hYproduct_tendsto :
      Filter.Tendsto (fun k => (List.ofFn (YregPow (epsilon k))).prod)
        Filter.atTop
        (nhds ((List.ofFn fun i => CFC.rpow (Y i) (alpha i)).prod)) := by
    simpa only [List.map_ofFn] using
      (tendsto_list_prod (List.ofFn (fun i : Fin q => i)) (fun i _hi =>
        hYfactor_tendsto i))
  exact Matrix.le_of_tendsto_of_tendsto _ _ _ _ hXproduct_tendsto
    hYproduct_tendsto (Filter.Eventually.of_forall hregularized_order)

end Matrix


open scoped ContinuousFunctionalCalculus Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: geometric-mean domination from complementary Kronecker upper bounds;
--   orig was `Shampoo.two_kron_upper_bounds_geometric_mean`, renamed
--   `Matrix.le_cfc_sqrt_kronecker_cfc_sqrt_of_two_kronecker_bounds`
-- generality used: arbitrary finite decidable row and column index types, a real PSD matrix
--   on their product, two real PSD factor matrices, and the two pointwise Loewner bounds;
--   no algorithm state, rank assumption, regularizer, or spectral proof witness is retained
-- portable call pattern: matrix AdaGrad, Shampoo, and tensor-matricization preconditioner
--   proofs vary the PSD lower matrix and the two factor accumulators while using the same
--   identity-Kronecker upper bounds to obtain a factorwise square-root preconditioner bound
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it
--   combines multivariate operator-mean monotonicity, commutation of complementary
--   Kronecker factors, CFC powers of Kronecker products, and PSD square-root cancellation
-- coverage search: symbol queries for "two Kronecker upper bounds square root geometric
--   mean matrix order" and "cfc sqrt kronecker product positive semidefinite monotone
--   commuting" plus LeanSearch found `Matrix.list_prod_cfc_rpow_mono_of_pairwise_commute`,
--   `Matrix.cfc_rpow_kronecker`, `Matrix.PosSemidef.kronecker`, and `CFC.sq_sqrt`, but no
--   Mathlib or SOptLib declaration with this complementary-two-bound conclusion
-- minimal hypotheses: all three PSD assumptions are used by operator-mean monotonicity and
--   square-root laws; finite decidable index types are required by finite-matrix CFC APIs

/-- If a positive-semidefinite matrix on a product index is bounded by both the identity
Kronecker a PSD right factor and a PSD left factor Kronecker the identity, then it is bounded
by the Kronecker product of the factors' CFC square roots.

Layer: Glue | Gap: Level 2 (geometric-mean domination from complementary Kronecker bounds)
Proof: apply normalized two-factor commuting CFC-power monotonicity to two copies of the lower matrix and the complementary Kronecker bounds, cancel the squared lower square root, distribute square roots through Kronecker products, and multiply the resulting factors.
Source: Ando multivariate geometric-mean monotonicity, Mathlib finite-matrix Loewner order and CFC square-root laws, and matrix Kronecker-product calculus
Used in: structured adaptive-gradient proofs that turn left- and right-Gram Kronecker bounds on a flattened covariance into a Kronecker square-root preconditioner bound
Book citation: book/research/Source.json#/key_lemmas/9/proof/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem le_cfc_sqrt_kronecker_cfc_sqrt_of_two_kronecker_bounds
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix (ι × κ) (ι × κ) ℝ)
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hM : M.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hM_le_one_kronecker : M ≤ (1 : Matrix ι ι ℝ) ⊗ₖ B)
    (hM_le_kronecker_one : M ≤ A ⊗ₖ (1 : Matrix κ κ ℝ)) :
    M ≤ CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  classical
  let IB : Matrix (ι × κ) (ι × κ) ℝ := (1 : Matrix ι ι ℝ) ⊗ₖ B
  let AI : Matrix (ι × κ) (ι × κ) ℝ := A ⊗ₖ (1 : Matrix κ κ ℝ)
  have hIι : (1 : Matrix ι ι ℝ).PosSemidef := Matrix.PosSemidef.one
  have hIκ : (1 : Matrix κ κ ℝ).PosSemidef := Matrix.PosSemidef.one
  have hIB : IB.PosSemidef := by
    simpa [IB] using hIι.kronecker hB
  have hAI : AI.PosSemidef := by
    simpa [AI] using hA.kronecker hIκ
  let X : Fin 2 → Matrix (ι × κ) (ι × κ) ℝ := fun _ => M
  let Y : Fin 2 → Matrix (ι × κ) (ι × κ) ℝ :=
    fun i => if i = 0 then IB else AI
  let alpha : Fin 2 → ℝ := fun _ => (1 / 2 : ℝ)
  have hmono := Matrix.list_prod_cfc_rpow_mono_of_pairwise_commute
    X Y alpha
    (fun _ => hM)
    (fun i => by fin_cases i <;> simp [Y, hIB, hAI])
    (fun i => by
      fin_cases i
      · simpa [X, Y, IB] using hM_le_one_kronecker
      · simpa [X, Y, AI] using hM_le_kronecker_one)
    (fun _ _ => Commute.refl M)
    (fun i j => by
      fin_cases i <;> fin_cases j
      · exact Commute.refl IB
      · show IB * AI = AI * IB
        calc
          IB * AI = A ⊗ₖ B := by
            simpa [IB, AI] using
              (Matrix.mul_kronecker_mul
                (1 : Matrix ι ι ℝ) A B (1 : Matrix κ κ ℝ)).symm
          _ = AI * IB := by
            simpa [IB, AI] using
              (Matrix.mul_kronecker_mul
                A (1 : Matrix ι ι ℝ) (1 : Matrix κ κ ℝ) B)
      · show AI * IB = IB * AI
        calc
          AI * IB = A ⊗ₖ B := by
            simpa [IB, AI] using
              (Matrix.mul_kronecker_mul
                A (1 : Matrix ι ι ℝ) (1 : Matrix κ κ ℝ) B).symm
          _ = IB * AI := by
            simpa [IB, AI] using
              (Matrix.mul_kronecker_mul
                (1 : Matrix ι ι ℝ) A B (1 : Matrix κ κ ℝ))
      · exact Commute.refl AI)
    (fun _ => by norm_num [alpha])
    (by norm_num [alpha, Fin.sum_univ_two])
  have hraw_cfc :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) M *
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) M ≤
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) IB *
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) AI := by
    simpa [X, Y, alpha] using hmono
  have hsqrt_cfc (C : Matrix (ι × κ) (ι × κ) ℝ) (hC : C.PosSemidef) :
      CFC.sqrt C =
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) C := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hC.nonneg]
  have hraw :
      CFC.sqrt M * CFC.sqrt M ≤ CFC.sqrt IB * CFC.sqrt AI := by
    simpa only [hsqrt_cfc M hM, hsqrt_cfc IB hIB, hsqrt_cfc AI hAI] using hraw_cfc
  have hleft : CFC.sqrt M * CFC.sqrt M = M := by
    simpa [pow_two] using CFC.sq_sqrt M hM.nonneg
  have hIBsqrt : CFC.sqrt IB = (1 : Matrix ι ι ℝ) ⊗ₖ CFC.sqrt B := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hIB.nonneg]
    rw [show IB = (1 : Matrix ι ι ℝ) ⊗ₖ B by rfl]
    rw [Matrix.cfc_rpow_kronecker (1 : Matrix ι ι ℝ) B (1 / 2 : ℝ) hIι hB]
    rw [← CFC.rpow_eq_cfc_real hIι.nonneg, ← CFC.rpow_eq_cfc_real hB.nonneg]
    rw [← CFC.sqrt_eq_rpow, ← CFC.sqrt_eq_rpow]
    simp
  have hAIsqrt : CFC.sqrt AI = CFC.sqrt A ⊗ₖ (1 : Matrix κ κ ℝ) := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hAI.nonneg]
    rw [show AI = A ⊗ₖ (1 : Matrix κ κ ℝ) by rfl]
    rw [Matrix.cfc_rpow_kronecker A (1 : Matrix κ κ ℝ) (1 / 2 : ℝ) hA hIκ]
    rw [← CFC.rpow_eq_cfc_real hA.nonneg, ← CFC.rpow_eq_cfc_real hIκ.nonneg]
    rw [← CFC.sqrt_eq_rpow, ← CFC.sqrt_eq_rpow]
    simp
  calc
    M = CFC.sqrt M * CFC.sqrt M := hleft.symm
    _ ≤ CFC.sqrt IB * CFC.sqrt AI := hraw
    _ = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
      rw [hIBsqrt, hAIsqrt]
      simpa using
        (Matrix.mul_kronecker_mul
          (1 : Matrix ι ι ℝ) (CFC.sqrt A)
          (CFC.sqrt B) (1 : Matrix κ κ ℝ)).symm

end Matrix


open scoped BigOperators ContinuousFunctionalCalculus Kronecker MatrixOrder

namespace Matrix


-- Generalization plan (G0):
-- concept/name: regularized inverse-rank vectorized covariance domination by
--   Kronecker square roots of the two Gram accumulators; orig was
--   `Lemma_8_matrix_rank_domination`, renamed
--   `Matrix.regularized_inv_rank_vecMulVec_sum_le_cfc_sqrt_kronecker_grams`
-- generality used: arbitrary finite family, row, and column index types for real
--   matrices, a positive natural rank cap, and a nonnegative real ridge; no
--   dimension encoding, measure, convexity, oracle, or algorithm state is used
-- portable call pattern: Shampoo-like and structured AdaGrad proofs change the
--   finite low-rank matrix-gradient family, rank cap, and ridge while comparing
--   the same full vectorized covariance with factored Gram square roots
-- counterargument checked: the two-bound and abstract geometric-mean ingredients
--   are already staged, but neither exposes this complete rank-to-square-root
--   contract; composing them also requires proving PSD of all three accumulators
-- coverage search: symbol searches for "regularized inverse rank vectorized matrix
--   outer product sum bounded by Kronecker square roots of left and right Gram
--   sums" found the two strictly weaker ingredients
--   `Matrix.regularized_inv_rank_vecMulVec_sum_le_kronecker_gram_bounds` and
--   `Matrix.le_cfc_sqrt_kronecker_cfc_sqrt_of_two_kronecker_bounds`; Mathlib
--   semantic search found only PSD closure under sums and nonnegative scaling
-- minimal hypotheses: finite and decidable row/column types support matrix CFC,
--   rank, identities, and Gram products; positivity of `r` supports inverse-rank
--   scaling, and nonnegativity of `epsilon` is exactly what PSD closure needs

/-- A nonnegative ridge plus an inverse-rank-scaled finite sum of vectorized matrix
self outer products is bounded by the Kronecker product of the CFC square roots of
the corresponding regularized left- and right-Gram sums.

Layer: Glue | Gap: Level 2 (regularized low-rank covariance domination by factored Gram square roots)
Proof: obtain the complementary identity-Kronecker Gram bounds from finite-family rank domination, prove the covariance and both Gram accumulators positive semidefinite by finite-sum and nonnegative-scaling closure, then apply complementary-bound geometric-mean domination.
Source: Mathlib finite real matrix rank, positive-semidefinite Loewner order and continuous functional calculus, together with finite Gram sums and matrix Kronecker products
Used in: Shampoo-like and structured AdaGrad regret proofs that compare a full vectorized low-rank gradient covariance with a factored row/column Gram square-root preconditioner
Book citation: book/research/Source.json#/key_lemmas/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem regularized_inv_rank_vecMulVec_sum_le_cfc_sqrt_kronecker_grams
    {α : Type u} {ι : Type v} {κ : Type w}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : α → Matrix ι κ ℝ) (r : ℕ) (epsilon : ℝ)
    (hr : 0 < r) (hrank : ∀ t : α, (G t).rank ≤ r) (hepsilon : 0 ≤ epsilon) :
    let A : Matrix ι ι ℝ :=
      epsilon • (1 : Matrix ι ι ℝ) + ∑ t : α, Matrix.leftGram (G t)
    let B : Matrix κ κ ℝ :=
      epsilon • (1 : Matrix κ κ ℝ) + ∑ t : α, Matrix.rightGram (G t)
    let M : Matrix (ι × κ) (ι × κ) ℝ :=
      epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
        (r : ℝ)⁻¹ •
          ∑ t : α, Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))
    M ≤ CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  classical
  intro A B M
  have hbounds :=
    Matrix.regularized_inv_rank_vecMulVec_sum_le_kronecker_gram_bounds
      G r epsilon hr hrank
  have hA : A.PosSemidef := by
    have hsum : (∑ t : α, Matrix.leftGram (G t)).PosSemidef := by
      simpa using Matrix.posSemidef_sum
        (Finset.univ : Finset α)
        (fun t _ht => by
          simpa [Matrix.leftGram] using
            (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := G t)))
    exact (Matrix.PosSemidef.one.smul hepsilon).add hsum
  have hB : B.PosSemidef := by
    have hsum : (∑ t : α, Matrix.rightGram (G t)).PosSemidef := by
      simpa using Matrix.posSemidef_sum
        (Finset.univ : Finset α)
        (fun t _ht => by
          simpa [Matrix.rightGram] using
            (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := G t)))
    exact (Matrix.PosSemidef.one.smul hepsilon).add hsum
  have hM : M.PosSemidef := by
    have hsum :
        (∑ t : α,
          Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))).PosSemidef := by
      simpa using Matrix.posSemidef_sum
        (Finset.univ : Finset α)
        (fun t _ht => by
          simpa using Matrix.posSemidef_vecMulVec_self_star (Function.uncurry (G t)))
    have hinv_nonneg : 0 ≤ (r : ℝ)⁻¹ :=
      inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le r))
    exact (Matrix.PosSemidef.one.smul hepsilon).add (hsum.smul hinv_nonneg)
  exact Matrix.le_cfc_sqrt_kronecker_cfc_sqrt_of_two_kronecker_bounds
    M A B hM hA hB hbounds.1 hbounds.2

end Matrix


open scoped ComplexOrder ContinuousFunctionalCalculus MatrixOrder


-- Generalization plan (G0):
-- concept/name: Loewner--Heinz monotonicity for continuous-functional-calculus
--   powers of finite real PSD matrices; orig was `positiveMatrixRpow_mono`, renamed
--   `Matrix.cfc_rpow_mono_of_posSemidef`
-- generality used: arbitrary finite decidable index type, two real square matrices,
--   and a real exponent in the unit interval; no fixed dimension, optimization state,
--   measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: matrix AdaGrad, Shampoo, and block-preconditioned analyses vary
--   the finite coordinate type, PSD accumulator pair, and fractional exponent while using
--   the same implication `A ≤ B → cfc (fun x ↦ x ^ t) A ≤ cfc (fun x ↦ x ^ t) B`
-- counterargument checked: this is not a pure rename of `CFC.monotone_rpow`; that theorem
--   applies in a complex C-star algebra, whereas the reusable gap is order-preserving and
--   functional-calculus-compatible transport for ordinary finite real matrices
-- coverage search: symbol queries for real PSD matrix CFC-power monotonicity found only
--   Shampoo-local copies; Mathlib semantic search found `CFC.monotone_rpow` and
--   `CFC.rpow_le_rpow`, while project search found `SOptLib.realMatrixComplexification`;
--   these cover the complex theorem and embedding separately but not the real-matrix result
-- minimal hypotheses: positive semidefiniteness of the upper matrix is omitted because it
--   follows from positive semidefiniteness of `A` and `A ≤ B`; all remaining hypotheses
--   are used, and finiteness is required by finite-matrix CFC and complexification

namespace MatrixCfcRpowMono

@[reducible] private noncomputable def complexCStarMatrixRealCFC
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

@[reducible] private noncomputable def complexCStarMatrixNonnegSpectrum
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

private noncomputable def complexMatrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (t : ℝ) : CStarMatrix ι ι ℂ := by
  letI hCFC : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  exact @CFC.rpow _ inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hCFC hNS A t

private theorem complexMatrixRpow_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hAB : A ≤ B) :
    complexMatrixRpow A t ≤ complexMatrixRpow B t := by
  letI hCFC : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  simpa only [complexMatrixRpow] using CFC.monotone_rpow ht hAB

private theorem starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  rw [← sub_nonneg, ← map_sub]
  exact map_nonneg f.toNonUnitalStarAlgHom (sub_nonneg.mpr hab)

private theorem starAlgEquiv_le_iff
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃⋆ₐ[R] B) (a b : A) : e a ≤ e b ↔ a ≤ b := by
  constructor
  · intro h
    simpa using starAlgHom_mono_of_le
      (StarAlgHom.mk e.symm.toAlgEquiv.toAlgHom
        (fun x => by simpa using map_star e.symm x)) h
  · exact starAlgHom_mono_of_le
      (StarAlgHom.mk e.toAlgEquiv.toAlgHom
        (fun x => by simpa using map_star e x))

private theorem realMatrixComplexification_nonneg_iff
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    0 ≤ SOptLib.realMatrixComplexification A ↔ 0 ≤ A := by
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix ι ι ℂ := Matrix.map A scalarCast
  have hcomplexify : SOptLib.realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [starAlgEquiv_le_iff e 0 castA]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, scalarCast] using hcast_psd.1.apply i j
    · intro v
      let vc : ι →₀ ℂ :=
        v.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
      have hv := hcast_psd.2 vc
      have heq :
          vc.sum (fun i vi => vc.sum fun j vj => star vi * castA i j * vj) =
            ((v.sum fun i vi => v.sum fun j vj => star vi * A i j * vj : ℝ) : ℂ) := by
        dsimp [vc]
        rw [Finsupp.sum_mapRange_index (by intro; simp)]
        simp only [Finsupp.sum,
          Finsupp.support_mapRange_of_injective Complex.ofReal_zero v
            Complex.ofReal_injective,
          castA, scalarCast, Matrix.map_apply, StarAlgHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact map_nonneg matrixCast.toNonUnitalStarAlgHom hA

private theorem realMatrixComplexification_cfc_rpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosSemidef) :
    SOptLib.realMatrixComplexification
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A) =
      complexMatrixRpow (SOptLib.realMatrixComplexification A) t := by
  letI hCFC : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  letI hSemi : IsSemitopologicalRing (CStarMatrix ι ι ℂ) := inferInstance
  letI hT2 : T2Space (CStarMatrix ι ι ℂ) := inferInstance
  have hnonneg : 0 ≤ SOptLib.realMatrixComplexification A :=
    (realMatrixComplexification_nonneg_iff A).2 hA.nonneg
  have hrpow_eq :
      complexMatrixRpow (SOptLib.realMatrixComplexification A) t =
        cfc (fun x : ℝ => x ^ t) (SOptLib.realMatrixComplexification A) := by
    rw [complexMatrixRpow]
    exact @CFC.rpow_eq_cfc_real _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hCFC hNS hSemi hT2
      (SOptLib.realMatrixComplexification A) t hnonneg
  rw [hrpow_eq]
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [hA.1.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hφ : Continuous (SOptLib.realMatrixComplexification (ι := ι)) := by
    change Continuous (fun M : Matrix ι ι ℝ =>
      CStarMatrix.ofMatrix (Matrix.map M fun r : ℝ => (r : ℂ)))
    have hcast : Continuous (fun M : Matrix ι ι ℝ =>
        Matrix.map M fun r : ℝ => (r : ℂ)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun M : Matrix ι ι ℝ => (M i j : ℂ))
      fun_prop
    exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp hcast
  exact (SOptLib.realMatrixComplexification (ι := ι)).map_cfc
    (fun x : ℝ => x ^ t) A
    (hf := hf)
    (hφ := hφ)
    (ha := hA.1)
    (hφa := (show IsSelfAdjoint A from hA.1).map
      (SOptLib.realMatrixComplexification (ι := ι)))

end MatrixCfcRpowMono

/-- Continuous-functional-calculus powers with exponent in `[0, 1]` preserve the
Loewner order of finite real positive-semidefinite matrices.

Layer: Glue | Gap: Level 1 (Loewner--Heinz monotonicity for finite real matrix CFC powers)
Proof: complexify the real matrices through an order-reflecting star-algebra embedding, apply `CFC.monotone_rpow` in the complex C-star algebra, use CFC naturality, and reflect the resulting Loewner inequality back to real matrices.
Source: Mathlib `CFC.monotone_rpow`, `StarAlgHom.map_cfc`, finite real Hermitian functional calculus, and `CStarMatrix.ofMatrixStarAlgEquiv`
Used in: Shampoo, matrix AdaGrad, and block-preconditioner proofs that transfer monotonicity of PSD accumulator chains to fractional matrix-power chains
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1--3 -/
theorem Matrix.cfc_rpow_mono_of_posSemidef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ)
    (hA : A.PosSemidef) (hAB : A ≤ B) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A ≤
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) B := by
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans hAB)
  have hcomplex_order :
      SOptLib.realMatrixComplexification A ≤
        SOptLib.realMatrixComplexification B :=
    MatrixCfcRpowMono.starAlgHom_mono_of_le
      (SOptLib.realMatrixComplexification (ι := ι)) hAB
  have hcomplex_power :=
    MatrixCfcRpowMono.complexMatrixRpow_mono
      (SOptLib.realMatrixComplexification A)
      (SOptLib.realMatrixComplexification B) t ht hcomplex_order
  have himage_power :
      SOptLib.realMatrixComplexification
          (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A) ≤
        SOptLib.realMatrixComplexification
          (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) B) := by
    rw [MatrixCfcRpowMono.realMatrixComplexification_cfc_rpow A t hA,
      MatrixCfcRpowMono.realMatrixComplexification_cfc_rpow B t hB]
    exact hcomplex_power
  rw [Matrix.le_iff]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (MatrixCfcRpowMono.realMatrixComplexification_nonneg_iff
    (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) B -
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A)).mp
  rw [map_sub]
  exact sub_nonneg.mpr himage_power


-- Generalization plan (G0):
-- concept/name: homogeneity of finite positive-semidefinite matrix CFC real powers;
--   orig was psdMatrixPower_smul_nonneg, renamed Matrix.cfc_rpow_smul_of_nonneg
-- generality used: arbitrary finite index type, real square matrix, nonnegative scalar,
--   positive-semidefinite matrix, and arbitrary real exponent
-- portable call pattern: adaptive-matrix and operator-mean proofs normalize a scaled
--   PSD preconditioner while the dimension, matrix, scale, and exponent all vary
-- counterargument checked: not paper-local or a pure wrapper; the proof combines CFC
--   composition and scalar extraction with rpow multiplicativity on a finite PSD spectrum
-- coverage search: queried CFC/rpow/scalar-multiplication equality and inspected
--   CFC.rpow_eq_cfc_real, cfc_comp_const_mul, and cfc_const_mul; these are component
--   results only, and neither Mathlib nor SOptLib contains the full homogeneity statement
-- minimal hypotheses: the scaled-matrix PSD proof was dropped because it follows from
--   Matrix.PosSemidef.smul; finite dimensionality is needed for arbitrary-exponent
--   continuity on the finite spectrum

/-- The real continuous-functional-calculus power of a nonnegative scalar multiple of a
finite positive-semidefinite matrix factors into the scalar power and the matrix power.

Layer: Glue | Gap: Level 1 (homogeneity of finite PSD matrix CFC real powers)
Proof: compose the CFC with scalar multiplication, identify scalar real powers on the nonnegative finite spectrum using `Real.mul_rpow`, then extract the constant factor with `cfc_const_mul`.
Source: Mathlib finite Hermitian matrix spectrum, continuous functional calculus composition and scalar-linearity, and `Real.mul_rpow`
Used in: adaptive matrix and tensor preconditioner domination steps that normalize rank-scaled PSD factors before applying operator means or square-root monotonicity
Book citation: book/research/Source.json#/key_lemmas/11/proof/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem Matrix.cfc_rpow_smul_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c α : ℝ) (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (hc : 0 ≤ c) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ α) (c • A) =
      c ^ α • cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ α) A := by
  classical
  let f : ℝ → ℝ := fun x => x ^ α
  let g : ℝ → ℝ := fun x => (c * x) ^ α
  let h : ℝ → ℝ := fun x => c ^ α * x ^ α
  have hspec_nonneg : ∀ x ∈ spectrum ℝ A, 0 ≤ x := by
    intro x hx
    rw [(show Matrix.IsHermitian A from hA.1).spectrum_real_eq_range_eigenvalues] at hx
    rcases hx with ⟨i, rfl⟩
    exact hA.eigenvalues_nonneg i
  have hfg : (spectrum ℝ A).EqOn g h := by
    intro x hx
    dsimp [g, h]
    rw [Real.mul_rpow hc (hspec_nonneg x hx)]
  have hcont_f_smul : ContinuousOn f ((c * ·) '' spectrum ℝ A) := by
    have hfin : ((c * ·) '' spectrum ℝ A).Finite :=
      (show (spectrum ℝ A).Finite from by
        rw [(show Matrix.IsHermitian A from hA.1).spectrum_real_eq_range_eigenvalues]
        exact Set.finite_range _).image _
    exact hfin.continuousOn _
  have hcont_f : ContinuousOn f (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [(show Matrix.IsHermitian A from hA.1).spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint) f (c • A) =
        cfc (R := ℝ) (p := IsSelfAdjoint) g A := by
          rw [← cfc_comp_const_mul (R := ℝ) (A := Matrix ι ι ℝ)
            (p := IsSelfAdjoint) c f A (hf := hcont_f_smul) (ha := hA.1)]
    _ = cfc (R := ℝ) (p := IsSelfAdjoint) h A := by
          exact cfc_congr (R := ℝ) (A := Matrix ι ι ℝ)
            (p := IsSelfAdjoint) (a := A) hfg
    _ = c ^ α • cfc (R := ℝ) (p := IsSelfAdjoint) f A := by
          rw [cfc_const_mul (R := ℝ) (A := Matrix ι ι ℝ)
            (p := IsSelfAdjoint) (c ^ α) f A (hf := hcont_f)]


-- Generalization plan (G0):
-- concept/name: composition of finite-matrix real CFC powers on the positive cone; orig was
--   `psdMatrixPower_matrixPower_mul`, renamed `Matrix.cfc_rpow_cfc_rpow_of_posSemidef`
-- generality used: arbitrary finite decidable index type, real positive-semidefinite square
--   matrix, and two arbitrary real exponents; no invertibility or exponent-sign assumptions
-- portable call pattern: spectral adaptive-gradient and tensor-preconditioner proofs collapse
--   two successive real matrix powers while the finite index type, PSD accumulator, and both
--   exponents vary
-- counterargument checked: Mathlib has an iterated CFC-power theorem for invertible bases and
--   another for two nonnegative exponents, but neither covers singular PSD matrices with
--   arbitrary real exponents; finite spectral diagonalization supplies the stronger contract
-- coverage search: queries "CFC real power of real power equals product exponent positive
--   semidefinite matrix", "rpow rpow multiplication exponent positive semidefinite", and the
--   corresponding LeanSearch query found `CFC.rpow_rpow`,
--   `CFC.rpow_rpow_of_exponent_nonneg`, `Real.rpow_mul`, and the partial spectral bridge
--   `Matrix.cfc_rpow_eq_of_unitary_diagonalization`, but no theorem with this full signature
-- minimal hypotheses: `A.PosSemidef` is needed for nonnegative eigenvalues; the source proof's
--   separate positive-semidefiniteness proof for the inner power is unnecessary and omitted

/-- For a finite real positive-semidefinite matrix, applying two arbitrary real CFC powers in
succession is the CFC power at the product of the exponents.

Layer: Glue | Gap: Level 1 (iterated real CFC powers of a singular PSD matrix)
Proof: diagonalize the PSD matrix, evaluate both CFC powers in the same unitary eigenbasis, and
  combine each nonnegative eigenvalue's exponents using `Real.rpow_mul`.
Source: Mathlib finite Hermitian matrix spectral theory, continuous functional calculus, and
  `Real.rpow_mul`
Used in: tensor adaptive-preconditioner proofs collapsing a square root of a fractional PSD
  accumulator power to the matrix power at the multiplied exponent
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Algorithms 1--3 -/
theorem Matrix.cfc_rpow_cfc_rpow_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Real) (a b : Real) (hA : A.PosSemidef) :
    cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ b)
        (cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ a) A) =
      cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ (a * b)) A := by
  classical
  let U : unitary (Matrix ι ι Real) := hA.1.eigenvectorUnitary
  let lambda : ι → Real := hA.1.eigenvalues
  have hdiag :
      A = (U : Matrix ι ι Real) * Matrix.diagonal lambda *
        star (U : Matrix ι ι Real) := by
    simpa [U, lambda, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hA.1.spectral_theorem
  have hpow_diag :
      cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ a) A =
        (U : Matrix ι ι Real) * Matrix.diagonal (fun i => (lambda i) ^ a) *
          star (U : Matrix ι ι Real) := by
    exact Matrix.cfc_rpow_eq_of_unitary_diagonalization A a U lambda hdiag
  calc
    cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ b)
        (cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ a) A) =
        (U : Matrix ι ι Real) *
          Matrix.diagonal (fun i => ((lambda i) ^ a) ^ b) *
          star (U : Matrix ι ι Real) := by
      exact Matrix.cfc_rpow_eq_of_unitary_diagonalization
        (cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ a) A)
        b U (fun i => (lambda i) ^ a) hpow_diag
    _ = (U : Matrix ι ι Real) *
          Matrix.diagonal (fun i => (lambda i) ^ (a * b)) *
          star (U : Matrix ι ι Real) := by
      congr 2
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq]
        exact (Real.rpow_mul (hA.eigenvalues_nonneg i) a b).symm
      · simp [Matrix.diagonal, hij]
    _ = cfc (R := Real) (p := IsSelfAdjoint)
          (fun x : Real => x ^ (a * b)) A := by
      exact (Matrix.cfc_rpow_eq_of_unitary_diagonalization
        A (a * b) U lambda hdiag).symm

end TensorsProofSupport



namespace Matrix

universe u v

-- Generalization plan (G0):
-- concept/name: positive-semidefiniteness of a matrix's diagonal part; orig was
--   diagonalPart_posSemidef_of_posSemidef, renamed Matrix.diagonalPart_posSemidef
-- generality used: arbitrary index and coefficient types with Ring, PartialOrder,
--   StarRing, StarOrderedRing, and DecidableEq; no finiteness or measure assumptions
-- portable call pattern: diagonal preconditioners and coordinate-adaptive methods replace
--   a PSD Gram or accumulator matrix by its diagonal part while the index type and matrix vary
-- counterargument checked: the proof composes short Mathlib facts, but it is not a pure rename;
--   it records the reusable preservation law for the separately named diagonal-part operator
-- coverage search: searches for "diagonal part positive semidefinite of positive semidefinite
--   matrix" and "Matrix diagonal PosSemidef diag_nonneg" found the staged diagonalPart API
--   and Mathlib PosSemidef.diagonal/diag_nonneg components, but no composite preservation theorem
-- minimal hypotheses: Fintype was dropped because neither PosSemidef.diagonal nor diag_nonneg
--   requires it; the remaining algebraic and decidable-equality typeclasses are used by Mathlib

/-- Taking the diagonal part of a positive-semidefinite matrix preserves
positive-semidefiniteness.

Layer: Model | Gap: Level 0 (positive-semidefinite diagonal-part preservation)
Proof: apply `Matrix.PosSemidef.diagonal` to the diagonal-entry nonnegativity supplied by `Matrix.PosSemidef.diag_nonneg`.
Source: Mathlib positive-semidefinite matrix API in `Mathlib.LinearAlgebra.Matrix.PosDef`
Used in: diagonal matrix and tensor preconditioners proving that projected Gram-matrix increments preserve positive-semidefinite accumulators
Book citation: book/research/Source.json#/additional_algorithm_specs/1/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 -/
theorem diagonalPart_posSemidef {ι : Type u} {R : Type v}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : A.PosSemidef) :
    (diagonalPart A).PosSemidef := by
  exact Matrix.PosSemidef.diagonal fun i => hA.diag_nonneg (i := i)

end Matrix


open scoped ComplexOrder MatrixOrder

namespace Matrix

universe u

-- Generalization plan (G0):
-- concept/name: monotonicity of the diagonal-part projection for the Loewner order;
--   orig was generic_diagonal_mono_of_matrix_le, renamed Matrix.diagonalPart_mono
-- generality used: arbitrary index type and RCLike scalar with decidable equality;
--   no finiteness, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: coordinate-adaptive and diagonal-preconditioned methods compare
--   matrix accumulators in Loewner order and project both sides onto their diagonal parts
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it
--   composes the Loewner-order characterization with PSD preservation by a named matrix
--   projection, yielding the order-homomorphism law future callers otherwise reprove
-- coverage search: queries "diagonal part preserves Loewner order matrix monotone" and
--   "Matrix diagonal order inequality positive semidefinite diagonal entries" found
--   Matrix.diagonalPart_posSemidef and Mathlib Matrix.le_iff as partial ingredients, but
--   no Mathlib or SOptLib declaration with the complete monotonicity signature
-- minimal hypotheses: Fintype was dropped because diagonal-part PSD preservation and the
--   MatrixOrder preorder need no finite enumeration; RCLike supplies the existing order

/-- Taking diagonal parts preserves the Loewner order on square matrices.

Layer: Model | Gap: Level 1 (Loewner monotonicity of diagonal projection)
Proof: unfold Loewner order with `Matrix.le_iff`, preserve positive-semidefiniteness using `Matrix.diagonalPart_posSemidef`, and identify the projected difference entrywise.
Source: Mathlib matrix Loewner order in `Mathlib.Analysis.Matrix.Order` and positive-semidefinite diagonal matrices in `Mathlib.LinearAlgebra.Matrix.PosDef`
Used in: coordinate-adaptive and diagonal Shampoo comparisons that project a full accumulator inequality onto coordinatewise diagonal preconditioners
Book citation: book/research/Source.json#/additional_algorithm_specs/1/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 -/
theorem diagonalPart_mono {𝕜 : Type*} [RCLike 𝕜] {ι : Type u} [DecidableEq ι]
    {A B : Matrix ι ι 𝕜} (hAB : A ≤ B) :
    diagonalPart A ≤ diagonalPart B := by
  rw [Matrix.le_iff] at hAB ⊢
  have hdiag := diagonalPart_posSemidef hAB
  convert hdiag using 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

end Matrix


namespace Matrix

universe u v w

-- Generalization plan (G0):
-- concept/name: left Gram matrix, named `Matrix.leftGram`; orig was `matrixGramLeft`
-- generality used: arbitrary row and column index types and arbitrary entries with
--   multiplication and finite addition; only the contracted column index is finite
-- portable call pattern: full-matrix adaptive-gradient and tensor-matricization algorithms
--   form row Gram accumulators while changing matrix shapes, index types, and scalar rings
-- counterargument checked: the body is a short product, but left Gram matrices are a
--   recognized recurring object and the entrywise API hides transpose/multiplication plumbing
-- coverage search: searches for "matrix left Gram matrix product transpose" and
--   "Matrix.leftGram G * G.transpose" found no Mathlib/SOptLib definition; Mathlib's
--   `Matrix.gram` is only a partial hit because it uses inner products (and conjugation over
--   complex scalars), rather than the general transpose product defined here
-- minimal hypotheses: `Fintype κ`, `Mul R`, and `AddCommMonoid R` are exactly those used
--   by rectangular matrix multiplication; no finiteness on the uncontracted row index is used

/-- The left Gram matrix of a rectangular matrix, obtained by multiplying the matrix by its
transpose.

Layer: Model | Concept: left Gram matrix of a rectangular matrix
Proof: (definitional construction; rectangular matrix multiplication by the transpose)
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: row-covariance accumulator updates for full-matrix adaptive-gradient and tensor-matricization preconditioners
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
def leftGram {ι : Type u} {κ : Type v} {R : Type w} [Fintype κ] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) : Matrix ι ι R :=
  G * G.transpose

/-- The left Gram matrix unfolds to multiplication by the transpose.

Layer: Model | Gap: Level 0 (left Gram matrix unfolding rule)
Proof: by rfl after unfolding `Matrix.leftGram`.
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: rewriting row-Gram accumulator updates into the matrix products used by spectral and positive-semidefinite arguments
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem leftGram_def {ι : Type u} {κ : Type v} {R : Type w} [Fintype κ] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) :
    leftGram G = G * G.transpose :=
  rfl

end Matrix


namespace Matrix

universe u v w

-- Generalization plan (G0):
-- concept/name: right Gram matrix, named `Matrix.rightGram`; orig was `matrixGramRight`
-- generality used: arbitrary row and column index types and arbitrary entries with
--   multiplication and finite addition; only the contracted row index is finite
-- portable call pattern: full-matrix adaptive-gradient and tensor-matricization algorithms
--   form column Gram accumulators while changing matrix shapes, index types, and scalar rings
-- counterargument checked: the body is a short product, but right Gram matrices are a
--   recognized recurring object and the entrywise API hides transpose/multiplication plumbing
-- coverage search: searches for "right Gram matrix transpose multiplied by matrix" and
--   "Matrix rightGram transpose mul" found no Mathlib/SOptLib definition; Mathlib's
--   `Matrix.gram` is only a partial hit because it uses inner products (and conjugation over
--   complex scalars), rather than the general transpose product defined here
-- minimal hypotheses: `Fintype ι`, `Mul R`, and `AddCommMonoid R` are exactly those used
--   by rectangular matrix multiplication; no finiteness on the uncontracted column index is used

/-- The right Gram matrix of a rectangular matrix, obtained by multiplying its transpose by the
matrix.

Layer: Model | Concept: right Gram matrix of a rectangular matrix
Proof: (definitional construction; transpose multiplied by the rectangular matrix)
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: column-covariance accumulator updates for full-matrix adaptive-gradient and tensor-matricization preconditioners
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
def rightGram {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) : Matrix κ κ R :=
  G.transpose * G

/-- The right Gram matrix unfolds to multiplication of the transpose by the matrix.

Layer: Model | Gap: Level 0 (right Gram matrix unfolding rule)
Proof: by rfl after unfolding `Matrix.rightGram`.
Source: Mathlib `Matrix.transpose` and finite matrix multiplication from `Mathlib.Data.Matrix.Mul`
Used in: rewriting column-Gram accumulator updates into the matrix products used by spectral and positive-semidefinite arguments
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem rightGram_def {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) :
    rightGram G = G.transpose * G :=
  rfl

/-- An entry of the right Gram matrix is the finite sum of the products of the
corresponding column entries.

Layer: Model | Gap: Level 0 (right Gram matrix entrywise specification)
Proof: unfold `Matrix.rightGram` and matrix multiplication.
Source: Mathlib `Matrix.mul_apply` and `Matrix.transpose_apply`
Used in: entrywise calculations for column-covariance accumulators and right Gram matrices
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem rightGram_apply {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι] [Mul R]
    [AddCommMonoid R] (G : Matrix ι κ R) (j k : κ) :
    rightGram G j k = ∑ i, G i j * G i k := by
  simp [rightGram, Matrix.mul_apply]

/-- Over commutative multiplication, the right Gram matrix is invariant under transpose.

Layer: Model | Gap: Level 0 (right Gram matrix symmetry)
Proof: transpose the defining product, reverse its factors, and cancel the double transpose.
Source: Mathlib `Matrix.transpose_mul` and `Matrix.transpose_transpose`
Used in: symmetry and positive-semidefinite arguments for column-covariance accumulators
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 -/
@[simp]
theorem transpose_rightGram {ι : Type u} {κ : Type v} {R : Type w} [Fintype ι]
    [AddCommMonoid R] [CommMagma R] (G : Matrix ι κ R) :
    (rightGram G).transpose = rightGram G := by
  simp [rightGram, Matrix.transpose_mul]

end Matrix


namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: finite tensor-index sum split at a selected mode; orig was
--   multiIndex_sum_split_mode, renamed sum_tensorIndex_eq_sum_mode_coordinate_complement
-- generality used: an arbitrary finite mode type with decidable equality, arbitrary finite
--   coordinate types, an arbitrary additive commutative monoid codomain, a selected mode,
--   and an arbitrary summand; no ordered, scalar, topological, or measure assumptions
-- portable call pattern: tensor preconditioning, block-coordinate, and multilinear proofs
--   turn a sum over all dependent coordinates into an outer sum over one selected coordinate
--   and an inner sum over its complement while changing every index type and the summand
-- counterargument checked: Mathlib supplies the underlying equivalence and product-sum law,
--   but no single theorem states their selected-coordinate dependent-product composition;
--   this is a stable reindexing step rather than paper-local traceability or a pure rename
-- coverage search: searches for "finite sum dependent product equals iterated sum selected
--   coordinate complement" and "piSplitAt sum equivalence sigma" found no SOptLib result;
--   Mathlib semantic search found Fintype.sum_prod_type and Fintype.sum_sigma, while inspection
--   of Equiv.piSplitAt confirmed that none states the composed tensor-index equality
-- minimal hypotheses: Fintype on the mode and every coordinate type makes both dependent
--   index factors finite; DecidableEq is required by Equiv.piSplitAt; AddCommMonoid is the
--   minimal codomain structure used by finite sums

/-- A finite sum over dependent tensor indices is the iterated sum over one selected
coordinate and all complementary coordinates.

Layer: Model | Gap: Level 1 (selected-coordinate finite dependent-product sum decomposition)
Proof: Reindex the finite sum with `Equiv.piSplitAt`, then apply `Fintype.sum_prod_type` to the resulting product index.
Source: Mathlib's `Equiv.piSplitAt` dependent-product equivalence and `Fintype.sum_prod_type` finite-sum decomposition
Used in: tensor mode-product and block-coordinate proofs that isolate one mode's row coordinate before simplifying contractions or Kronecker-preconditioned updates
Book citation: book/research/Source.json#/key_lemmas/12
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem sum_tensorIndex_eq_sum_mode_coordinate_complement
    {ι : Type u} {M : Type w} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    {dims : ι → Type v} [∀ i, Fintype (dims i)]
    (i : ι) (F : TensorIndex dims → M) :
    (∑ idx : TensorIndex dims, F idx) =
      ∑ row : dims i, ∑ col : TensorModeColumn dims i,
        F ((Equiv.piSplitAt i dims).symm (row, col)) := by
  calc
    (∑ idx : TensorIndex dims, F idx) =
        ∑ rc : dims i × TensorModeColumn dims i,
          F ((Equiv.piSplitAt i dims).symm rc) := by
      simpa only [Equiv.symm_apply_apply] using
        ((Equiv.piSplitAt i dims).sum_comp
          (fun rc : dims i × TensorModeColumn dims i =>
            F ((Equiv.piSplitAt i dims).symm rc)))
    _ = ∑ row : dims i, ∑ col : TensorModeColumn dims i,
          F ((Equiv.piSplitAt i dims).symm (row, col)) := by
      rw [Fintype.sum_prod_type]

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: embedding of a single-mode matrix into the full tensor index space;
--   orig was modeEmbeddedMatrix, renamed tensorModeEmbedding
-- generality used: an arbitrary finite mode type, arbitrary mode-dependent coordinate
--   types with decidable equality, and coefficients in a commutative monoid equipped
--   with a zero;
--   no additive, order, topology, measure, or optimization assumptions are required
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning, and
--   block-coordinate proofs lift a changing selected-mode operator to the full tensor
--   index space while the mode type, tensor shape, coefficient type, and operator change
-- counterargument checked: although the body is entrywise, the construction is not a
--   paper-local wrapper; its stable identity-on-complement semantics supports reusable
--   commutation, positivity, linearity, and Kronecker-product laws across tensor methods
-- coverage search: lean_search_symbols queries for tensor-mode matrix embeddings and
--   single-mode dependent Kronecker products found only Shampoo-local helpers; Mathlib
--   semantic search returned LinearMap.single and Matrix.piEquiv, neither of which acts
--   by a square matrix on one dependent-product coordinate and identically on the rest
-- minimal hypotheses: Fintype and DecidableEq on modes form the complement product,
--   pointwise DecidableEq forms its Kronecker deltas, CommMonoid supplies finite
--   products and multiplication, and Zero supplies the off-diagonal delta value

/-- Embed a square matrix acting on one tensor mode into the full dependent tensor index
space, acting as the identity on every coordinate outside the selected mode.

Layer: Model | Concept: single-mode matrix embedding into a tensor index space
Proof: (definitional construction; multiply the selected-mode matrix entry by Kronecker deltas on every complementary mode)
Source: Mathlib finite commutative products, matrix function representation, and Kronecker-delta identity entries
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that compare, compose, and take powers of modewise operators on one flattened tensor space
Book citation: book/research/Source.json#/key_lemmas/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
def tensorModeEmbedding {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommMonoid R] [Zero R] {dims : ι → Type v}
    [∀ j, DecidableEq (dims j)] (i : ι) (B : Matrix (dims i) (dims i) R) :
    Matrix (TensorIndex dims) (TensorIndex dims) R :=
  fun a b =>
    B (a i) (b i) *
      ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : R) else 0

/-- The single-mode tensor embedding unfolds to the selected matrix entry times
Kronecker deltas on all complementary coordinates. -/
@[simp]
theorem tensorModeEmbedding_def {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommMonoid R] [Zero R] {dims : ι → Type v}
    [∀ j, DecidableEq (dims j)] (i : ι) (B : Matrix (dims i) (dims i) R) :
    tensorModeEmbedding i B = fun a b =>
      B (a i) (b i) *
        ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : R) else 0 := by
  rfl

/-- Evaluating a single-mode tensor embedding gives the selected matrix entry times
Kronecker deltas on all complementary coordinates.

Layer: Model | Gap: Level 0 (single-mode tensor embedding entry formula)
Proof: by rfl after unfolding `tensorModeEmbedding`.
Source: Mathlib finite commutative products and matrix function application
Used in: entrywise reindexing, positivity, commutation, linearity, and identity calculations for modewise tensor preconditioners
Book citation: book/research/Source.json#/key_lemmas/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorModeEmbedding_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommMonoid R] [Zero R] {dims : ι → Type v}
    [∀ j, DecidableEq (dims j)] (i : ι) (B : Matrix (dims i) (dims i) R)
    (a b : TensorIndex dims) :
    tensorModeEmbedding i B a b =
      B (a i) (b i) *
        ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : R) else 0 := by
  rfl

/-- Embedding the identity on one mode gives the identity on the full tensor index
space. -/
@[simp]
theorem tensorModeEmbedding_one {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommMonoidWithZero R] {dims : ι → Type v}
    [∀ j, DecidableEq (dims j)] (i : ι) :
    tensorModeEmbedding i (1 : Matrix (dims i) (dims i) R) =
      (1 : Matrix (TensorIndex dims) (TensorIndex dims) R) := by
  ext a b
  by_cases h : a = b
  · subst b
    simp
  · have hne_coord : ∃ j : ι, a j ≠ b j := by
      by_contra hnone
      apply h
      funext j
      by_contra hj
      exact hnone ⟨j, hj⟩
    rcases hne_coord with ⟨j, hj⟩
    rw [Matrix.one_apply_ne h]
    by_cases hji : j = i
    · subst j
      simp [hj]
    · have hprod_zero :
          (∏ x : {j : ι // j ≠ i},
              if a x.1 = b x.1 then (1 : R) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ ⟨j, hji⟩) (by simp [hj])
      simp [hprod_zero]

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: a single-mode tensor embedding is the dependent finite-family
--   Kronecker product with the selected factor and identity factors elsewhere;
--   orig was modeEmbeddedMatrix_eq_tensorKronecker_single_for_Lemma11, renamed
--   tensorModeEmbedding_eq_tensorKronecker_single
-- generality used: an arbitrary finite mode type with decidable equality,
--   arbitrary mode-dependent coordinate types with decidable equality, and a
--   commutative monoid with zero of coefficients; no coordinate finiteness,
--   additive, order, topology, measure, or optimization assumptions are used
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning,
--   and block-coordinate proofs rewrite a changing selected-mode operator as a
--   full Kronecker family while the mode type, tensor shape, coefficient type,
--   selected mode, and factor operator vary
-- counterargument checked: this is not paper-local traceability or a pure rename;
--   it bridges two independently useful tensor operator representations and is
--   consumed by product, commutation, and modewise operator arguments
-- coverage search: lean_search_symbols queries for tensor-mode embeddings equal
--   to a single nonidentity Kronecker factor found only the parent definitions;
--   Mathlib semantic search found binary tensor-product identity-map facts, not
--   this dependent finite-family matrix identity
-- minimal hypotheses: Fintype and DecidableEq on modes support the selected-factor
--   split, pointwise DecidableEq supplies identity-matrix entries, and
--   CommMonoid supplies finite products and identities, while Zero supplies zero entries

/-- A matrix embedded in one tensor mode is the dependent Kronecker product whose
selected factor is that matrix and whose other factors are identity matrices.

Layer: Model | Gap: Level 1 (single-mode embedding to dependent Kronecker-family bridge)
Proof: split the finite product at the selected mode, simplify that factor to the given matrix entry, and identify the complementary product with the embedding's Kronecker deltas.
Source: Mathlib finite-product singleton splitting, subtype products, and matrix identity entries
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that convert modewise embeddings into a common Kronecker representation for products and commutation
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorModeEmbedding_eq_tensorKronecker_single
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommMonoid R] [Zero R]
    {dims : ι → Type v} [∀ j, DecidableEq (dims j)]
    (i : ι) (B : Matrix (dims i) (dims i) R) :
    tensorModeEmbedding i B =
      tensorKronecker
        (fun j : ι =>
          if h : j = i then
            by
              subst j
              exact B
          else
            (1 : Matrix (dims j) (dims j) R)) := by
  classical
  ext a b
  let f : ι → R :=
    fun j =>
      (if h : j = i then
        by
          subst j
          exact B
      else
        (1 : Matrix (dims j) (dims j) R)) (a j) (b j)
  change
    B (a i) (b i) *
        (∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : R) else 0) =
      ∏ j : ι, f j
  have hsplit :
      (∏ j : ι, f j) =
        f i * ∏ j ∈ (Finset.univ \ {i}), f j := by
    simpa using
      (Finset.prod_eq_mul_prod_diff_singleton_of_mem
        (s := (Finset.univ : Finset ι)) (i := i)
        (f := f) (Finset.mem_univ i))
  have hfi : f i = B (a i) (b i) := by
    simp [f]
  have hrest :
      (∏ j ∈ (Finset.univ \ {i}), f j) =
        ∏ j : {j : ι // j ≠ i}, if a j.1 = b j.1 then (1 : R) else 0 := by
    have hoff :
        (∏ j ∈ (Finset.univ \ {i}), f j) =
          ∏ j ∈ (Finset.univ \ {i}), if a j = b j then (1 : R) else 0 := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by
        simpa using hj
      by_cases hab : a j = b j
      · simp [f, hji, hab, Matrix.one_apply]
      · simp [f, hji, hab]
    rw [hoff]
    simpa using
      (Finset.prod_subtype
        (F := inferInstance)
        (s := (Finset.univ \ {i} : Finset ι))
        (p := fun j : ι => j ≠ i)
        (by intro j; simp)
        (fun j : ι => if a j = b j then (1 : R) else 0))
  rw [hsplit, hfi, hrest]

end SOptLib


namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: single-mode tensor embeddings commute when their selected modes
--   are distinct; orig was modeEmbeddedMatrix_comm_of_ne_for_Lemma11, renamed
--   tensorModeEmbedding_comm_of_ne
-- generality used: an arbitrary finite mode type with decidable equality,
--   arbitrary finite mode-dependent coordinate types with decidable equality,
--   and coefficients in a commutative semiring; no order, topology, measure,
--   vector-space, or optimization assumptions are used
-- portable call pattern: tensor adaptive-gradient, multilinear preconditioning,
--   and block-coordinate proofs reorder two changing modewise operators while
--   the tensor shape, coefficient semiring, selected modes, and matrices vary
-- counterargument checked: the result follows through the Kronecker representation,
--   but is not a pure rename or paper-local wrapper; it packages the reusable
--   disjoint-mode commutation invariant needed to reorder full tensor operators
-- coverage search: lean_search_symbols queries for tensor-mode embeddings commuting
--   on distinct modes and embedded matrices commuting at unequal indices found no
--   project or SOptLib declaration; Mathlib semantic search found `Commute.tmul`
--   and `Commute.tprod`, whose abstract tensor-product conclusions do not state
--   equality for these dependent-index matrix embeddings
-- minimal hypotheses: `Fintype` on modes and coordinates supports the dependent
--   Kronecker multiplication law, decidable equality forms identity-matrix entries,
--   `CommSemiring` supplies matrix multiplication and commutes the two selected factors,
--   and `i ≠ j` is precisely the condition separating their supports

/-- Matrices embedded into two distinct modes of a finite dependent tensor space
commute under multiplication on the full tensor index space.

Layer: Model | Gap: Level 1 (commutation of distinct single-mode tensor embeddings)
Proof: rewrite both embeddings as dependent Kronecker products, distribute matrix multiplication modewise, and simplify separately at the two selected modes.
Source: Mathlib finite dependent products and matrix multiplication, together with `tensorModeEmbedding_eq_tensorKronecker_single` and `tensorKronecker_mul`
Used in: tensor adaptive-gradient, multilinear preconditioning, and block-coordinate arguments that reorder modewise preconditioners before forming an ordered product
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorModeEmbedding_comm_of_ne
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommSemiring R]
    {dims : ι → Type v} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (i j : ι) (hij : i ≠ j)
    (B : Matrix (dims i) (dims i) R) (C : Matrix (dims j) (dims j) R) :
    tensorModeEmbedding i B * tensorModeEmbedding j C =
      tensorModeEmbedding j C * tensorModeEmbedding i B := by
  classical
  have hmul (X Y : (l : ι) → Matrix (dims l) (dims l) R) :
      tensorKronecker X * tensorKronecker Y =
        tensorKronecker (fun l => X l * Y l) := by
    ext a b
    have h := congrFun (congrFun (tensorKronecker_mul X Y) a) b
    simp only [tensorKronecker_apply, Matrix.mul_apply] at h ⊢
    rw [← h]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _hx
      rfl
  rw [tensorModeEmbedding_eq_tensorKronecker_single i B,
    tensorModeEmbedding_eq_tensorKronecker_single j C, hmul, hmul]
  apply congrArg tensorKronecker
  funext l
  by_cases hli : l = i
  · subst l
    simp [hij]
  · by_cases hlj : l = j
    · subst l
      simp [hli]
    · simp [hli, hlj]

end SOptLib


open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: positive semidefiniteness of a single-mode tensor embedding;
--   orig was modeEmbeddedMatrix_posSemidef_for_Lemma11, renamed
--   tensorModeEmbedding_posSemidef
-- generality used: an arbitrary finite mode type, arbitrary finite
--   mode-dependent coordinate types with decidable equality, and an arbitrary
--   RCLike scalar; no optimization, measure, topology, or paper setup is used
-- portable call pattern: tensor adaptive-gradient, multilinear
--   preconditioning, and tensor block-coordinate proofs promote a changing
--   positive-semidefinite mode operator to the full tensor coordinate space
--   while the mode family, selected mode, scalar field, and operator vary
-- counterargument checked: the result is not paper-local traceability or a
--   pure rename; it composes Kronecker positivity with an index-equivalence
--   transport into the reusable tensor-mode embedding API
-- coverage search: symbol queries for positive-semidefinite tensor-mode
--   embeddings found only `tensorModeEmbedding` and its entrywise API;
--   Mathlib semantic search found `Matrix.PosSemidef.kronecker` and
--   `Matrix.posSemidef_submatrix_equiv`, which provide the two proof edges but
--   no theorem for the dependent single-mode embedding itself
-- minimal hypotheses: finiteness of each coordinate type is required by
--   Kronecker-product positivity; mode finiteness and pointwise decidable
--   equality are exactly those required to define `tensorModeEmbedding`

/-- Embedding a positive-semidefinite matrix in one mode of a finite dependent
tensor space produces a positive-semidefinite matrix on the full tensor index.

Layer: Model | Gap: Level 1 (positive semidefiniteness of a single-mode tensor embedding)
Proof: identify the embedding, up to the canonical dependent-product reindexing, with the Kronecker product of the mode matrix and an identity matrix; apply `Matrix.PosSemidef.kronecker` and transport positivity with `Matrix.posSemidef_submatrix_equiv`.
Source: Mathlib matrix positive-semidefinite order, Kronecker products, and `Equiv.piSplitAt` for dependent function types
Used in: tensor adaptive-gradient and multilinear preconditioning arguments that lift positive-semidefinite mode accumulators to commuting operators on the flattened tensor space
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorModeEmbedding_posSemidef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {𝕜 : Type w} [RCLike 𝕜]
    {dims : ι → Type v} [∀ j, Finite (dims j)] [∀ j, DecidableEq (dims j)]
    (i : ι) (B : Matrix (dims i) (dims i) 𝕜) (hB : B.PosSemidef) :
    (tensorModeEmbedding i B).PosSemidef := by
  classical
  letI (j : ι) : Fintype (dims j) := Fintype.ofFinite (dims j)
  let e := (Equiv.piSplitAt i dims).symm
  let C := (j : {j : ι // j ≠ i}) → dims j.1
  have hBI : (B ⊗ₖ (1 : Matrix C C 𝕜)).PosSemidef :=
    hB.kronecker (Matrix.PosSemidef.one : (1 : Matrix C C 𝕜).PosSemidef)
  have hreindex :
      (Matrix.reindexAlgEquiv 𝕜 𝕜 e (B ⊗ₖ (1 : Matrix C C 𝕜))).PosSemidef := by
    simpa [e, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv e.symm).2 hBI)
  have hone (a b : C) :
      (1 : Matrix C C 𝕜) a b =
        ∏ j : {j : ι // j ≠ i}, if a j = b j then (1 : 𝕜) else 0 := by
    by_cases h : a = b
    · subst b
      simp
    · have hne : ∃ j : {j : ι // j ≠ i}, a j ≠ b j := by
        by_contra hnone
        apply h
        funext j
        by_contra hj
        exact hnone ⟨j, hj⟩
      rcases hne with ⟨j, hj⟩
      rw [Matrix.one_apply_ne h]
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  have hmatrix :
      Matrix.reindexAlgEquiv 𝕜 𝕜 e (B ⊗ₖ (1 : Matrix C C 𝕜)) =
        tensorModeEmbedding i B := by
    ext a b
    simp [e, C, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      tensorModeEmbedding, Matrix.kroneckerMap_apply, Equiv.piSplitAt, hone]
  simpa [hmatrix] using hreindex

end SOptLib


open scoped ContinuousFunctionalCalculus Kronecker

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: real functional-calculus powers commute with a single-mode tensor
--   embedding; orig was psdMatrixPower_modeEmbeddedMatrix_for_Lemma11, renamed
--   tensorModeEmbedding_cfc_rpow
-- generality used: an arbitrary finite mode type and arbitrary finite
--   mode-dependent coordinate types with decidable equality, a selected mode,
--   a real Hermitian mode matrix, and an arbitrary real exponent;
--   no algorithm state, measure, convexity, or stochastic assumptions are used
-- portable call pattern: tensor adaptive-gradient, multilinear
--   preconditioning, and tensor block-coordinate proofs move a fractional real
--   power through a changing selected-mode embedding while the finite mode
--   family, selected mode, Hermitian factor, and exponent vary
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; `StarAlgHom.map_cfc` supplies only the generic naturality edge,
--   while this theorem constructs and validates the nontrivial unital
--   star-algebra homomorphism represented by `tensorModeEmbedding`
-- coverage search: symbol and semantic queries for functional calculus under
--   tensor-mode embeddings found `StarAlgHom.map_cfc`,
--   `tensorModeEmbedding_posSemidef`, matrix reindexing, and Kronecker identity
--   laws, but no declaration with this specialized equality; these are partial
--   proof components rather than full coverage
-- minimal hypotheses: finite coordinate types are required for matrix
--   multiplication, Hermitian spectral calculus, finite-dimensional continuity,
--   and the full tensor index; Hermitianity supplies source self-adjointness,
--   and star preservation supplies it after the tensor-mode embedding

/-- Applying a real functional-calculus power after embedding a Hermitian
matrix in one tensor mode equals embedding the powered mode matrix.

Layer: Model | Gap: Level 1 (functional-calculus naturality for single-mode tensor embeddings)
Proof: bundle Kronecker product with the complementary identity followed by dependent-product reindexing as a continuous unital star-algebra homomorphism, use star preservation to map self-adjointness, then apply `StarAlgHom.map_cfc`.
Source: Mathlib continuous functional calculus naturality for star-algebra homomorphisms, Hermitian finite-matrix spectra, Kronecker products, and dependent-product reindexing
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that move real functional-calculus powers of Hermitian mode operators between modewise and flattened tensor operators
Book citation: book/research/Source.json#/key_lemmas/11/proof/3
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorModeEmbedding_cfc_rpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {dims : ι → Type v} [∀ j, Fintype (dims j)] [∀ j, DecidableEq (dims j)]
    (i : ι) (B : Matrix (dims i) (dims i) ℝ) (s : ℝ)
    (hB : B.IsHermitian) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (tensorModeEmbedding i B) =
      tensorModeEmbedding i
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) B) := by
  classical
  let C := (j : {j : ι // j ≠ i}) → dims j.1
  let e : dims i × C ≃ TensorIndex dims := (Equiv.piSplitAt i dims).symm
  let rightIdentity :
      Matrix (dims i) (dims i) ℝ →⋆ₐ[ℝ]
        Matrix (dims i × C) (dims i × C) ℝ := {
    toFun A := A ⊗ₖ (1 : Matrix C C ℝ)
    commutes' r := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        Matrix.smul_kronecker r
          (1 : Matrix (dims i) (dims i) ℝ) (1 : Matrix C C ℝ)
    map_zero' := by
      simpa using Matrix.zero_kronecker (1 : Matrix C C ℝ)
    map_add' A D := by
      simpa using Matrix.add_kronecker A D (1 : Matrix C C ℝ)
    map_one' := by
      simpa using
        (Matrix.one_kronecker_one :
          (1 : Matrix (dims i) (dims i) ℝ) ⊗ₖ (1 : Matrix C C ℝ) = 1)
    map_mul' A D := by
      simpa using
        (Matrix.mul_kronecker_mul A D
          (1 : Matrix C C ℝ) (1 : Matrix C C ℝ))
    map_star' A := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.conjTranspose_kronecker A (1 : Matrix C C ℝ)).symm
    }
  let reindex :
      Matrix (dims i × C) (dims i × C) ℝ →⋆ₐ[ℝ]
        Matrix (TensorIndex dims) (TensorIndex dims) ℝ :=
    { (Matrix.reindexAlgEquiv ℝ ℝ e).toAlgHom with
      map_star' := by
        intro A
        simpa [Matrix.reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose] using
          (Matrix.conjTranspose_reindex e e A).symm }
  let φ :
      Matrix (dims i) (dims i) ℝ →⋆ₐ[ℝ]
        Matrix (TensorIndex dims) (TensorIndex dims) ℝ :=
    reindex.comp rightIdentity
  have hone (a b : C) :
      (1 : Matrix C C ℝ) a b =
        ∏ j : {j : ι // j ≠ i}, if a j = b j then (1 : ℝ) else 0 := by
    by_cases h : a = b
    · subst b
      simp
    · have hne : ∃ j : {j : ι // j ≠ i}, a j ≠ b j := by
        by_contra hnone
        apply h
        funext j
        by_contra hj
        exact hnone ⟨j, hj⟩
      rcases hne with ⟨j, hj⟩
      rw [Matrix.one_apply_ne h]
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  have hφ (A : Matrix (dims i) (dims i) ℝ) :
      φ A = tensorModeEmbedding i A := by
    ext a b
    simp [φ, reindex, rightIdentity, e, C, Matrix.reindexAlgEquiv_apply,
      Matrix.reindex_apply, tensorModeEmbedding, Matrix.kroneckerMap_apply,
      Equiv.piSplitAt, hone]
  have hf : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ B) := by
    have hfin : (spectrum ℝ B).Finite := by
      rw [hB.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hmap :
      φ (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) B) =
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (φ B) := by
    exact φ.map_cfc (fun x : ℝ => x ^ s) B (hf := hf)
      (hφ := φ.toLinearMap.continuous_of_finiteDimensional)
      (ha := hB)
      (hφa := (show IsSelfAdjoint B from hB).map φ)
  rw [← hφ B, ← hφ]
  exact hmap.symm

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: identity law for the dependent finite-family Kronecker product;
--   orig was tensorKronecker_one_for_Lemma11
-- generality used: an arbitrary finite mode type, arbitrary mode-dependent coordinate
--   types with decidable equality, and coefficients in a commutative monoid with zero
-- portable call pattern: tensor and multilinear preconditioning proofs simplify an
--   assembled operator whose modewise factors are identities while changing the mode
--   type, coordinate family, coefficient type, and surrounding recurrence
-- counterargument checked: Mathlib's binary Matrix.one_kronecker_one is related but does
--   not cover an arbitrary dependent finite family; this is a basic law of the staged
--   tensorKronecker object rather than paper-local traceability or a pure rename
-- coverage search: symbol search found tensorKronecker_apply and tensorKronecker_mul but
--   no identity theorem; Mathlib semantic search found Matrix.one_kronecker_one only for
--   the binary ordinary-product construction, so coverage is partial rather than full
-- minimal hypotheses: coordinate finiteness and additive structure are unused; Fintype
--   on modes, dependent decidable equality, and CommMonoidWithZero are sufficient

/-- The dependent finite-family Kronecker product of identity matrices is the identity
matrix on the full dependent product of their coordinate types.

Layer: Model | Gap: Level 0 (dependent finite-family Kronecker identity law)
Proof: compare entries; equal dependent indices give a product of ones, while unequal indices differ in one mode and hence contribute a zero factor.
Source: Mathlib finite commutative products, dependent function extensionality, and matrix identity entries; generalizes the binary `Matrix.one_kronecker_one` law
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that initialize or cancel a product-index operator assembled from modewise identity factors
Book citation: book/research/Source.json#/assumptions/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
@[simp]
theorem tensorKronecker_one {ι : Type u} [Fintype ι]
    {R : Type w} [CommMonoidWithZero R] {dims : ι → Type v}
    [∀ i, DecidableEq (dims i)] :
    tensorKronecker (fun i : ι => (1 : Matrix (dims i) (dims i) R)) =
      (1 : Matrix (TensorIndex dims) (TensorIndex dims) R) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [tensorKronecker]
  · have hne : ∃ i : ι, a i ≠ b i := by
      by_contra hnone
      apply hab
      funext i
      by_contra hi
      exact hnone ⟨i, hi⟩
    rcases hne with ⟨i, hi⟩
    rw [Matrix.one_apply_ne hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end SOptLib


open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: positive semidefiniteness of a dependent finite-family Kronecker
--   product; orig was tensorKronecker_posSemidef_of_forall_posSemidef, renamed
--   tensorKronecker_posSemidef
-- generality used: a `Fin k` mode family, arbitrary finite mode-dependent coordinate
--   types, and an arbitrary RCLike scalar; no optimization, measure, or paper setup
--   assumptions are used
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs assemble a positive-semidefinite full-space operator from changing
--   modewise PSD accumulators while the tensor order, coordinate types, scalar field,
--   and component matrices vary
-- counterargument checked: Mathlib's binary Kronecker positivity theorem is only the
--   induction step; the dependent finite-family conclusion is not a pure rename,
--   caller-side expression, or paper-local traceability wrapper
-- coverage search: `lean_search_symbols` for finite tensor Kronecker positivity found
--   the staged dependent-family definition and multiplication law but no positivity
--   theorem; Mathlib semantic search found `Matrix.PosSemidef.kronecker`, whose binary
--   ordinary-product conclusion is strictly smaller than this dependent-family result
-- minimal hypotheses: pointwise positive semidefiniteness and finite coordinate types
--   are sufficient; coordinate decidable equality and Fintype data are supplied
--   classically inside the proof, and no positive-definiteness assumption is needed

/-- The dependent Kronecker product of a `Fin`-indexed family of positive-semidefinite
square matrices is positive semidefinite on the full dependent tensor index.

Layer: Model | Gap: Level 1 (dependent finite-family Kronecker positivity)
Proof: induct on the number of modes, identify the successor family up to the head-tail index equivalence with a binary Kronecker product, apply `Matrix.PosSemidef.kronecker`, and transport positivity through matrix reindexing.
Source: Mathlib matrix positive-semidefinite order, binary Kronecker-product positivity, and positivity transport along index equivalences
Used in: tensor adaptive-gradient and multilinear preconditioning arguments that assemble a full tensor preconditioner from positive-semidefinite mode accumulators
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_posSemidef {k : Nat} {𝕜 : Type u} [RCLike 𝕜]
    {dims : Fin k → Type v} [∀ i, Finite (dims i)]
    (M : (i : Fin k) → Matrix (dims i) (dims i) 𝕜)
    (hM : ∀ i : Fin k, (M i).PosSemidef) :
    (tensorKronecker M).PosSemidef := by
  classical
  induction k with
  | zero =>
      have h1 :
          tensorKronecker M =
            (1 : Matrix (TensorIndex dims) (TensorIndex dims) 𝕜) := by
        ext a b
        have hab : a = b := Subsingleton.elim _ _
        subst b
        simp [tensorKronecker]
      rw [h1]
      exact Matrix.PosSemidef.one
  | succ k ih =>
      letI (i : Fin (k + 1)) : Fintype (dims i) := Fintype.ofFinite (dims i)
      let e : TensorIndex dims ≃
          dims 0 × TensorIndex (fun i : Fin k => dims i.succ) :=
        { toFun := fun idx => (idx 0, fun i => idx i.succ)
          invFun := fun rc => Fin.cases rc.1 rc.2
          left_inv := by
            intro idx
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j
              rfl
          right_inv := by
            intro rc
            rcases rc with ⟨head, tail⟩
            apply Prod.ext
            · rfl
            · funext i
              rfl }
      have htail :
          (tensorKronecker (fun i : Fin k => M i.succ)).PosSemidef := by
        exact ih (M := fun i : Fin k => M i.succ) (fun i => hM i.succ)
      have hkron :
          ((M 0) ⊗ₖ tensorKronecker (fun i : Fin k => M i.succ)).PosSemidef := by
        exact (hM 0).kronecker htail
      have heq :
          Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker M) =
            (M 0) ⊗ₖ tensorKronecker (fun i : Fin k => M i.succ) := by
        ext rc rc'
        rcases rc with ⟨head, tail⟩
        rcases rc' with ⟨head', tail'⟩
        simp [e, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
          Matrix.kroneckerMap_apply, tensorKronecker, Fin.prod_univ_succ]
      have hreindex :
          (Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker M)).PosSemidef := by
        rw [heq]
        exact hkron
      have hsub :
          ((tensorKronecker M).submatrix e.symm e.symm).PosSemidef := by
        simpa [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using hreindex
      exact (Matrix.posSemidef_submatrix_equiv e.symm).1 hsub

end SOptLib


namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: invertibility of a dependent finite-family Kronecker product;
--   orig was tensorKronecker_isUnit_of_forall_posDef, renamed to expose the
--   minimal pointwise invertibility hypothesis
-- generality used: an arbitrary finite mode type, arbitrary finite mode-dependent
--   coordinate types, and coefficients in a commutative ring; positivity,
--   ordered-field structure, and real scalars are not used
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs certify an assembled tensor operator as invertible while changing the
--   mode family, coordinate types, coefficient ring, and invertible factors
-- counterargument checked: Mathlib supplies the binary theorem
--   Matrix.IsUnit.kronecker, but not the dependent finite-family result; this
--   composes the full staged tensorKronecker API rather than merely renaming it
-- coverage search: symbol searches for tensor Kronecker units found only the
--   paper-local positive-definite theorem and the staged multiplication and identity
--   laws; Mathlib semantic search found Matrix.IsUnit.kronecker, which covers two
--   ordinary factors but not an arbitrary dependent finite family
-- minimal hypotheses: pointwise IsUnit replaces positive definiteness; CommRing,
--   finite mode and coordinate types, and decidable equality on both are exactly what
--   the coherent dependent finite matrix-unit and determinant APIs require

/-- A dependent finite-family Kronecker product is a unit when every modewise
factor is a unit.

Layer: Model | Gap: Level 1 (dependent finite-family Kronecker invertibility)
Proof: choose a unit above each factor and assemble its modewise inverses; the dependent Kronecker multiplication and identity laws verify both unit equations.
Source: Mathlib general linear groups and `Matrix.IsUnit.kronecker`, generalized from binary Kronecker products using SOptLib's dependent finite-family Kronecker laws
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that certify an assembled full-coordinate preconditioner as invertible from modewise certificates
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_isUnit_of_forall_isUnit
    {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type w} [CommRing R]
    {dims : ι → Type v} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (M : (i : ι) → Matrix (dims i) (dims i) R)
    (hM : ∀ i : ι, IsUnit (M i)) :
    IsUnit (tensorKronecker M) := by
  let U : (i : ι) → (Matrix (dims i) (dims i) R)ˣ := fun i => (hM i).unit
  let A : (i : ι) → Matrix (dims i) (dims i) R := fun i => U i
  let B : (i : ι) → Matrix (dims i) (dims i) R := fun i => ↑((U i)⁻¹)
  have hA : A = M := by
    funext i
    exact (hM i).unit_spec
  have hAB (i : ι) : A i * B i = (1 : Matrix (dims i) (dims i) R) := by
    dsimp [A, B]
    exact Units.mul_inv (U i)
  have hBA (i : ι) : B i * A i = (1 : Matrix (dims i) (dims i) R) := by
    dsimp [A, B]
    exact Units.inv_mul (U i)
  have hmul (X Y : (i : ι) → Matrix (dims i) (dims i) R) :
      tensorKronecker X * tensorKronecker Y =
        tensorKronecker (fun i : ι => X i * Y i) := by
    ext a b
    have h := congrFun (congrFun (tensorKronecker_mul X Y) a) b
    simp only [tensorKronecker_apply, Matrix.mul_apply] at h ⊢
    rw [← h]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _hx
      rfl
  have hval_inv : tensorKronecker A * tensorKronecker B = 1 := by
    calc
      tensorKronecker A * tensorKronecker B =
          tensorKronecker (fun i : ι => A i * B i) := hmul A B
      _ = tensorKronecker
          (fun i : ι => (1 : Matrix (dims i) (dims i) R)) := by
            apply congrArg tensorKronecker
            funext i
            exact hAB i
      _ = 1 := tensorKronecker_one
  have hinv_val : tensorKronecker B * tensorKronecker A = 1 := by
    calc
      tensorKronecker B * tensorKronecker A =
          tensorKronecker (fun i : ι => B i * A i) := hmul B A
      _ = tensorKronecker
          (fun i : ι => (1 : Matrix (dims i) (dims i) R)) := by
            apply congrArg tensorKronecker
            funext i
            exact hBA i
      _ = 1 := tensorKronecker_one
  rw [← hA]
  exact ({
    val := tensorKronecker A
    inv := tensorKronecker B
    val_inv := hval_inv
    inv_val := hinv_val
  } : (Matrix (TensorIndex dims) (TensorIndex dims) R)ˣ).isUnit

end SOptLib


open scoped ComplexOrder MatrixOrder

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: positive definiteness of a dependent finite-family Kronecker
--   product; orig was tensorKronecker_posDef_of_forall_posDef, renamed
--   tensorKronecker_posDef
-- generality used: an arbitrary RCLike scalar, a `Fin k` mode family, and arbitrary
--   finite mode-dependent coordinate types; no optimization, measure, stochastic,
--   or paper-specific setup assumptions are used
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs certify an assembled full-space operator as positive definite while the
--   tensor order, coordinate types, scalar field, and modewise preconditioners vary
-- counterargument checked: Mathlib's binary `Matrix.PosDef.kronecker` does not cover
--   a dependent finite family; the staged PSD and unit results cover separate parts
--   of the contract but neither alone supplies the positive-definite conclusion
-- coverage search: symbol searches for dependent finite-family Kronecker positive
--   definiteness found only the paper-local declaration and the staged PSD/unit API;
--   Mathlib semantic search found `Matrix.PosDef.kronecker`, restricted to two factors
-- minimal hypotheses: pointwise positive definiteness and finite coordinate types are
--   sufficient; Fintype and decidable-equality data are chosen classically in the proof

/-- The dependent Kronecker product of a `Fin`-indexed family of positive-definite
square matrices is positive definite on the full dependent tensor index.

Layer: Model | Gap: Level 1 (dependent finite-family Kronecker positive definiteness)
Proof: combine dependent-family positive-semidefinite closure with dependent-family invertibility, then use the equivalence between positive definiteness and invertibility for a positive-semidefinite matrix.
Source: Mathlib matrix positive-definite order and `Matrix.PosDef.kronecker`, extended through SOptLib's dependent finite-family Kronecker PSD and unit laws
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that assemble an invertible positive tensor preconditioner from positive-definite modewise accumulators
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_posDef {k : Nat} {𝕜 : Type u} [RCLike 𝕜]
    {dims : Fin k → Type v} [∀ i, Finite (dims i)]
    (M : (i : Fin k) → Matrix (dims i) (dims i) 𝕜)
    (hM : ∀ i : Fin k, (M i).PosDef) :
    (tensorKronecker M).PosDef := by
  classical
  letI (i : Fin k) : Fintype (dims i) := Fintype.ofFinite (dims i)
  have hunit : IsUnit (tensorKronecker M) :=
    tensorKronecker_isUnit_of_forall_isUnit M (fun i => (hM i).isUnit)
  have hpsd : (tensorKronecker M).PosSemidef :=
    tensorKronecker_posSemidef M (fun i => (hM i).posSemidef)
  exact (hpsd.posDef_iff_isUnit).2 hunit

end SOptLib


open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: Loewner monotonicity of a dependent finite-family Kronecker
--   product; orig was tensorKronecker_mono_of_forall_le and already has a
--   concept-derived, paper-free name
-- generality used: an arbitrary RCLike scalar, a `Fin k` family of arbitrary
--   finite coordinate types, and pointwise PSD/order hypotheses; no optimization,
--   measure, stochastic-process, or algorithm setup assumptions are used
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs compare assembled full-space preconditioners while changing the mode
--   dimensions, scalar field, and the two pointwise ordered mode-operator families
-- counterargument checked: this is neither paper-local traceability nor a one-line
--   wrapper; Mathlib only supplies binary Kronecker PSD closure, so the dependent
--   finite-family monotonicity and its reindexing induction would otherwise recur
-- coverage search: `lean_search_symbols` for dependent finite-family Kronecker
--   Loewner monotonicity found only `tensorKronecker_posSemidef` and the underlying
--   definition; Mathlib semantic search found `Matrix.PosSemidef.kronecker`, whose
--   binary PSD conclusion does not compare two dependent families
-- minimal hypotheses: PSD is required only for each lower factor; upper-factor PSD
--   follows from the pointwise Loewner inequalities, and `Finite` coordinate types
--   suffice because decidable equality and enumerations are chosen classically

/-- A dependent finite-family Kronecker product is monotone in Loewner order when
each lower factor is positive semidefinite and below its corresponding upper factor.

Layer: Model | Gap: Level 1 (dependent finite-family Kronecker Loewner monotonicity)
Proof: induct on the number of modes, decompose each successor product into a binary head-tail Kronecker product, prove its difference PSD from binary Kronecker positivity, and transport the order through the canonical head-tail reindexing.
Source: Mathlib matrix Loewner order, `Matrix.PosSemidef.kronecker`, finite products, and positive-semidefinite transport along index equivalences
Used in: tensor Shampoo and multilinear adaptive-gradient proofs that lift modewise monotonicity of powered accumulators to monotonicity of the assembled tensor preconditioner
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_mono_of_forall_le {k : Nat} {𝕜 : Type u} [RCLike 𝕜]
    {dims : Fin k → Type v} [∀ i, Finite (dims i)]
    (A B : (i : Fin k) → Matrix (dims i) (dims i) 𝕜)
    (hApsd : ∀ i : Fin k, (A i).PosSemidef)
    (hAB : ∀ i : Fin k, A i ≤ B i) :
    tensorKronecker A ≤ tensorKronecker B := by
  classical
  induction k with
  | zero =>
      have hA1 :
          tensorKronecker A =
            (1 : Matrix (TensorIndex dims) (TensorIndex dims) 𝕜) := by
        ext a b
        have hab : a = b := Subsingleton.elim _ _
        subst b
        simp [tensorKronecker]
      have hB1 :
          tensorKronecker B =
            (1 : Matrix (TensorIndex dims) (TensorIndex dims) 𝕜) := by
        ext a b
        have hab : a = b := Subsingleton.elim _ _
        subst b
        simp [tensorKronecker]
      rw [hA1, hB1]
  | succ k ih =>
      letI (i : Fin (k + 1)) : Fintype (dims i) := Fintype.ofFinite (dims i)
      let e : TensorIndex dims ≃
          dims 0 × TensorIndex (fun i : Fin k => dims i.succ) :=
        { toFun := fun idx => (idx 0, fun i => idx i.succ)
          invFun := fun rc => Fin.cases rc.1 rc.2
          left_inv := by
            intro idx
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j
              rfl
          right_inv := by
            intro rc
            rcases rc with ⟨head, tail⟩
            apply Prod.ext
            · rfl
            · funext i
              rfl }
      have htail_psd :
          (tensorKronecker (fun i : Fin k => A i.succ)).PosSemidef := by
        exact tensorKronecker_posSemidef
          (fun i : Fin k => A i.succ) (fun i => hApsd i.succ)
      have htail_le :
          tensorKronecker (fun i : Fin k => A i.succ) ≤
            tensorKronecker (fun i : Fin k => B i.succ) := by
        exact ih
          (dims := fun i : Fin k => dims i.succ)
          (A := fun i : Fin k => A i.succ)
          (B := fun i : Fin k => B i.succ)
          (fun i => hApsd i.succ)
          (fun i => hAB i.succ)
      have hkron :
          (A 0 ⊗ₖ tensorKronecker (fun i : Fin k => A i.succ)) ≤
            (B 0 ⊗ₖ tensorKronecker (fun i : Fin k => B i.succ)) := by
        rw [Matrix.le_iff]
        have hBpsd : (B 0).PosSemidef :=
          Matrix.nonneg_iff_posSemidef.mp (le_trans (hApsd 0).nonneg (hAB 0))
        have htailBpsd :
            (tensorKronecker (fun i : Fin k => B i.succ)).PosSemidef :=
          Matrix.nonneg_iff_posSemidef.mp (le_trans htail_psd.nonneg htail_le)
        have hLeft :
            ((B 0 - A 0) ⊗ₖ
              tensorKronecker (fun i : Fin k => B i.succ)).PosSemidef :=
          (hAB 0).kronecker htailBpsd
        have hRight :
            (A 0 ⊗ₖ
              (tensorKronecker (fun i : Fin k => B i.succ) -
                tensorKronecker (fun i : Fin k => A i.succ))).PosSemidef :=
          (hApsd 0).kronecker htail_le
        have hSum :
            (((B 0 - A 0) ⊗ₖ
                tensorKronecker (fun i : Fin k => B i.succ)) +
              (A 0 ⊗ₖ
                (tensorKronecker (fun i : Fin k => B i.succ) -
                  tensorKronecker (fun i : Fin k => A i.succ)))).PosSemidef :=
          hLeft.add hRight
        have hDiff :
            (B 0 ⊗ₖ tensorKronecker (fun i : Fin k => B i.succ)) -
                (A 0 ⊗ₖ tensorKronecker (fun i : Fin k => A i.succ)) =
              ((B 0 - A 0) ⊗ₖ
                tensorKronecker (fun i : Fin k => B i.succ)) +
                (A 0 ⊗ₖ
                  (tensorKronecker (fun i : Fin k => B i.succ) -
                    tensorKronecker (fun i : Fin k => A i.succ))) := by
          ext ij kl
          rcases ij with ⟨i, tail⟩
          rcases kl with ⟨j, tail'⟩
          simp [sub_mul, mul_sub]
        simpa [hDiff] using hSum
      have hA_reindex :
          Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker A) =
            A 0 ⊗ₖ tensorKronecker (fun i : Fin k => A i.succ) := by
        ext rc rc'
        rcases rc with ⟨head, tail⟩
        rcases rc' with ⟨head', tail'⟩
        simp [e, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
          Matrix.kroneckerMap_apply, tensorKronecker, Fin.prod_univ_succ]
      have hB_reindex :
          Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker B) =
            B 0 ⊗ₖ tensorKronecker (fun i : Fin k => B i.succ) := by
        ext rc rc'
        rcases rc with ⟨head, tail⟩
        rcases rc' with ⟨head', tail'⟩
        simp [e, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
          Matrix.kroneckerMap_apply, tensorKronecker, Fin.prod_univ_succ]
      have hreindexed :
          Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker A) ≤
            Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker B) := by
        rw [hA_reindex, hB_reindex]
        exact hkron
      have hreindex_iff :
          tensorKronecker A ≤ tensorKronecker B ↔
            Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker A) ≤
              Matrix.reindexAlgEquiv 𝕜 𝕜 e (tensorKronecker B) := by
        rw [Matrix.le_iff, Matrix.le_iff, ← map_sub]
        simpa [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
          (Matrix.posSemidef_submatrix_equiv
            (M := tensorKronecker B - tensorKronecker A) e.symm).symm
      exact hreindex_iff.mpr hreindexed

end SOptLib


namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: nonsingular inverse of a dependent finite-family Kronecker product;
--   orig was tensorKronecker_inv_eq_tensorKronecker_pd_neg_power, renamed
--   tensorKronecker_nonsing_inv to expose the underlying matrix operation
-- generality used: an arbitrary finite mode type, arbitrary finite mode-dependent
--   coordinate types, coefficients in a commutative ring, and pointwise `IsUnit`
--   hypotheses; real scalars, positive definiteness, and spectral powers are unused
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs invert an assembled product-index operator while changing the mode family,
--   coordinate types, coefficient ring, and invertible component operators
-- counterargument checked: Mathlib's binary `Matrix.inv_kronecker` is related, but
--   does not cover an arbitrary dependent finite family; the result is a structural
--   inverse law for the staged tensor object rather than paper-local power bookkeeping
-- coverage search: symbol searches for dependent tensor Kronecker inverse laws found
--   no SOptLib or project declaration; Mathlib semantic search found only the binary
--   `Matrix.inv_kronecker`, so coverage is partial rather than full
-- minimal hypotheses: pointwise `IsUnit` replaces all positivity assumptions and
--   already implies invertibility of the assembled product; mode and coordinate
--   finiteness and decidable equality are exactly those required to enumerate the
--   dependent product index and form finite matrix nonsingular inverses

/-- The nonsingular inverse of a dependent finite-family Kronecker product of units
is the dependent Kronecker product of their nonsingular inverses.

Layer: Model | Gap: Level 1 (dependent finite-family Kronecker inverse law)
Proof: multiply by the proposed inverse, distribute matrix multiplication through the dependent Kronecker product, and use pointwise nonsingular-inverse cancellation plus the dependent identity law.
Source: Mathlib `Matrix.inv_eq_right_inv`, `Matrix.mul_nonsing_inv`, and the binary `Matrix.inv_kronecker`, extended through SOptLib's dependent finite-family Kronecker multiplication and identity laws
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that rewrite an inverse full-coordinate preconditioner as modewise inverse factors
Book citation: book/research/Source.json#/algorithm_spec/steps/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_nonsing_inv
    {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type w} [CommRing R]
    {dims : ι → Type v} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (M : (i : ι) → Matrix (dims i) (dims i) R)
    (hM : ∀ i : ι, IsUnit (M i)) :
    (tensorKronecker M)⁻¹ = tensorKronecker (fun i => (M i)⁻¹) := by
  have hmul (X Y : (i : ι) → Matrix (dims i) (dims i) R) :
      tensorKronecker X * tensorKronecker Y =
        tensorKronecker (fun i => X i * Y i) := by
    ext a b
    have h := congrFun (congrFun (tensorKronecker_mul X Y) a) b
    simp only [tensorKronecker_apply, Matrix.mul_apply] at h ⊢
    rw [← h]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _hx
      rfl
  apply Matrix.inv_eq_right_inv
  calc
    tensorKronecker M * tensorKronecker (fun i => (M i)⁻¹) =
        tensorKronecker (fun i => M i * (M i)⁻¹) :=
      hmul M (fun i => (M i)⁻¹)
    tensorKronecker (fun i => M i * (M i)⁻¹) =
        tensorKronecker (fun i => (1 : Matrix (dims i) (dims i) R)) := by
      apply congrArg tensorKronecker
      funext i
      exact Matrix.mul_nonsing_inv (M i) ((M i).isUnit_iff_isUnit_det.mp (hM i))
    _ = 1 := tensorKronecker_one

end SOptLib


open scoped BigOperators

namespace SOptLib

universe u v w

-- Generalization plan (G0):
-- concept/name: the ordered product of all single-mode tensor embeddings is the
--   dependent finite-family Kronecker operator; orig was
--   orderedMatrixProduct_reindexed_modeEmbeddedMatrix_for_Lemma11, renamed
--   List.prod_ofFn_tensorModeEmbedding_eq_tensorKronecker
-- generality used: an arbitrary finite mode type with decidable equality and an explicit
--   `Fin n` enumeration, arbitrary mode-dependent finite coordinate
--   types, an arbitrary target index type equivalent to their dependent product, and
--   coefficients in a commutative semiring; no topology, measure, or optimization assumptions
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs assemble a changing finite family of mode operators on a flattened index
--   space while the tensor shape, factors, coefficients, and flattening equivalence vary
-- counterargument checked: this is not merely paper traceability or a pure wrapper;
--   it composes the single-mode embedding bridge across a noncommutative matrix list
--   and transports the resulting operator through an arbitrary index equivalence
-- coverage search: lean_search_symbols for an ordered product of mode embeddings equal
--   to a tensor Kronecker operator found only the staged single-mode bridge,
--   multiplication law, and identity law; Mathlib has List.prod_ofFn and matrix
--   reindexing APIs but no dependent tensor-mode assembly theorem
-- minimal hypotheses: CommSemiring supports matrix multiplication and the dependent
--   Kronecker multiplication law; the mode Fintype and explicit equivalence fix
--   the traversal, while mode, coordinate, and target DecidableEq instances are exactly
--   those required by square-matrix multiplication and identities

/-- The ordered list product of all reindexed single-mode tensor embeddings is the
reindexed dependent finite-family Kronecker operator.

The modes are traversed by the supplied `Fin n` enumeration; the
factors commute across distinct modes, while the stated order also supports direct use
with noncommutative matrix products.

Layer: Model | Gap: Level 1 (finite product of mode embeddings to tensor Kronecker operator)
Proof: induct on prefixes of `List.ofFn`, rewriting each new embedding as a one-factor dependent Kronecker product and using Kronecker multiplicativity; then transport the product through the matrix reindexing algebra equivalence.
Source: Mathlib finite-list products and matrix algebra equivalences, together with SOptLib's dependent Kronecker multiplication, identity, and single-mode embedding bridge
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that identify the product of flattened modewise preconditioners with the full tensor Kronecker preconditioner
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem List.prod_ofFn_tensorModeEmbedding_eq_tensorKronecker
    {n : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type w} [CommSemiring R]
    {dims : ι → Type u} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    {flat : Type v} [Fintype flat] [DecidableEq flat]
    (modeOrder : Fin n ≃ ι)
    (e : TensorIndex dims ≃ flat)
    (B : (i : ι) → Matrix (dims i) (dims i) R) :
    (List.ofFn (fun p : Fin n ↦
      Matrix.reindexAlgEquiv R R e
        (tensorModeEmbedding (modeOrder p) (B (modeOrder p))))).prod =
      Matrix.reindexAlgEquiv R R e (tensorKronecker B) := by
  classical
  let factors : List (Matrix (TensorIndex dims) (TensorIndex dims) R) :=
    List.ofFn (fun p : Fin n ↦
      tensorModeEmbedding (modeOrder p) (B (modeOrder p)))
  have hmul (X Y : (i : ι) → Matrix (dims i) (dims i) R) :
      tensorKronecker X * tensorKronecker Y =
        tensorKronecker (fun i ↦ X i * Y i) := by
    ext a b
    have h := congrFun (congrFun (tensorKronecker_mul X Y) a) b
    simp only [tensorKronecker_apply, Matrix.mul_apply] at h ⊢
    rw [← h]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _hx
      rfl
  have hprefix : ∀ a : Nat, a ≤ n →
      (factors.take a).prod =
        tensorKronecker
          (fun j : ι ↦
            if _h : (modeOrder.symm j).1 < a then B j else
              (1 : Matrix (dims j) (dims j) R)) := by
    intro a ha
    induction a with
    | zero =>
        simp [factors, tensorKronecker_one]
    | succ a ih =>
        have hlt : a < n := Nat.lt_of_succ_le ha
        have hle : a ≤ n := Nat.le_of_succ_le ha
        calc
          (factors.take (a + 1)).prod =
              (factors.take a).prod *
                tensorModeEmbedding (modeOrder ⟨a, hlt⟩) (B (modeOrder ⟨a, hlt⟩)) := by
                rw [List.prod_take_succ factors a]
                · simp [factors]
                · simpa [factors] using hlt
          _ =
              tensorKronecker
                (fun j : ι ↦
                  if _h : (modeOrder.symm j).1 < a then B j else
                    (1 : Matrix (dims j) (dims j) R)) *
                tensorModeEmbedding (modeOrder ⟨a, hlt⟩) (B (modeOrder ⟨a, hlt⟩)) := by
                  rw [ih hle]
          _ =
              tensorKronecker
                (fun j : ι ↦
                  if _h : (modeOrder.symm j).1 < a + 1 then B j else
                    (1 : Matrix (dims j) (dims j) R)) := by
                rw [tensorModeEmbedding_eq_tensorKronecker_single, hmul]
                apply congrArg tensorKronecker
                funext j
                by_cases hja : (modeOrder.symm j).1 < a
                · have hne : j ≠ modeOrder ⟨a, hlt⟩ := by
                    intro h
                    have : (modeOrder.symm j).1 = a := by
                      simpa using congrArg Fin.val (congrArg modeOrder.symm h)
                    omega
                  simp [hja, Nat.lt_trans hja (Nat.lt_succ_self a), hne]
                · by_cases hjeq : j = modeOrder ⟨a, hlt⟩
                  · subst j
                    simp
                  · have hnot : ¬ (modeOrder.symm j).1 < a + 1 := by
                      intro hj
                      have hle_a : (modeOrder.symm j).1 ≤ a := Nat.le_of_lt_succ hj
                      have hge_a : a ≤ (modeOrder.symm j).1 := Nat.le_of_not_gt hja
                      have hval : (modeOrder.symm j).1 = a := le_antisymm hle_a hge_a
                      apply hjeq
                      have hp : modeOrder.symm j = ⟨a, hlt⟩ := Fin.ext hval
                      simpa using congrArg modeOrder hp
                    simp [hja, hjeq, hnot]
  have hall : factors.prod = tensorKronecker B := by
    have h := hprefix n le_rfl
    calc
      factors.prod = (factors.take n).prod := by
        rw [List.take_of_length_le]
        simp [factors]
      _ = tensorKronecker
          (fun j : ι ↦
            if _h : (modeOrder.symm j).1 < n then B j else
              (1 : Matrix (dims j) (dims j) R)) := h
      _ = tensorKronecker B := by
        apply congrArg tensorKronecker
        funext j
        simp [(modeOrder.symm j).2]
  rw [List.ofFn_comp']
  change (factors.map (Matrix.reindexAlgEquiv R R e)).prod = _
  rw [List.prod_hom factors (Matrix.reindexAlgEquiv R R e), hall]

end SOptLib


open scoped BigOperators ContinuousFunctionalCalculus

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: weighted ordered product normalization for real CFC powers of
--   tensor-mode embeddings; orig was ordered_product_scaled_mode_power_normalization,
--   renamed List.prod_tensorModeEmbedding_cfc_rpow_smul
-- generality used: arbitrary finite mode and mode-dependent coordinate types,
--   an arbitrary finite enumeration and flattening equivalence, real scalar weights,
--   Hermitian real mode matrices, and a common real exponent; no positivity,
--   measure, convexity, stochastic, or algorithm-state assumptions are used
-- portable call pattern: tensor adaptive-gradient and multilinear preconditioning
--   proofs assemble scalar-weighted equal powers of commuting mode operators while
--   the tensor shape, flattening, weights, mode factors, and exponent vary
-- counterargument checked: this is not paper-local traceability or a caller-side
--   expression; it combines CFC naturality, scalar extraction from a noncommutative
--   matrix product, and full mode-embedding assembly into one reusable normalization
-- coverage search: symbol searches for weighted products of tensor-mode CFC powers
--   found only List.prod_ofFn_tensorModeEmbedding_eq_tensorKronecker and
--   tensorModeEmbedding_cfc_rpow; Mathlib semantic search found generic List.smul_prod
--   and Finset.prod_smul lemmas, neither of which supplies this dependent tensor bridge
-- minimal hypotheses: Hermitianity is exactly what the real CFC naturality theorem
--   consumes; finite coordinate types and decidable equality support matrix products,
--   embeddings, and reindexing; Nonempty and nonnegativity assumptions are unnecessary

/-- The ordered product of scalar-weighted real functional-calculus powers of all
single-mode tensor embeddings is the powered scalar product times the dependent
Kronecker product of the powered mode factors, transported through a flattening.

Layer: Model | Gap: Level 1 (weighted CFC-power product normalization for tensor-mode embeddings)
Proof: move each CFC power through its mode embedding, extract central real scalars from the noncommutative matrix-list product, and apply the finite product of mode embeddings theorem.
Source: Mathlib real continuous functional calculus, scalar actions on matrix algebras, finite list products, and SOptLib tensor-mode embedding/Kronecker bridges
Used in: tensor adaptive-gradient preconditioner proofs that normalize the product of scalar-weighted fractional mode powers into one flattened Kronecker preconditioner
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem List.prod_tensorModeEmbedding_cfc_rpow_smul
    {n : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {dims : ι → Type u} [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    {flat : Type v} [Fintype flat] [DecidableEq flat]
    (modeOrder : Fin n ≃ ι) (e : TensorIndex dims ≃ flat)
    (c : ι → ℝ) (A : (i : ι) → Matrix (dims i) (dims i) ℝ) (s : ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (List.ofFn (fun p : Fin n =>
      Matrix.reindexAlgEquiv ℝ ℝ e
        ((c (modeOrder p) ^ s) •
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
            (tensorModeEmbedding (modeOrder p) (A (modeOrder p)))))).prod =
      Matrix.reindexAlgEquiv ℝ ℝ e
        ((∏ i : ι, c i ^ s) •
          tensorKronecker (fun i =>
            cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (A i))) := by
  classical
  let B : (i : ι) → Matrix (dims i) (dims i) ℝ := fun i =>
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (A i)
  have hpower (i : ι) :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
          (tensorModeEmbedding i (A i)) =
        tensorModeEmbedding i (B i) := by
    simpa [B] using tensorModeEmbedding_cfc_rpow i (A i) s (hA i)
  have hscaledList
      (l : List (ℝ × Matrix flat flat ℝ)) :
      (l.map (fun z => z.1 • z.2)).prod =
        (l.map Prod.fst).prod • (l.map Prod.snd).prod := by
    induction l with
    | nil => simp
    | cons z l ih =>
        simp only [List.map_cons, List.prod_cons, ih]
        rw [smul_mul_smul_comm]
  let factors : Fin n → Matrix flat flat ℝ := fun p =>
    Matrix.reindexAlgEquiv ℝ ℝ e
      (tensorModeEmbedding (modeOrder p) (B (modeOrder p)))
  have hfactorFun :
      (fun p : Fin n =>
        Matrix.reindexAlgEquiv ℝ ℝ e
          ((c (modeOrder p) ^ s) •
            cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
              (tensorModeEmbedding (modeOrder p) (A (modeOrder p))))) =
        (fun p : Fin n => (c (modeOrder p) ^ s) • factors p) := by
    funext p
    rw [hpower]
    rfl
  calc
    (List.ofFn (fun p : Fin n =>
      Matrix.reindexAlgEquiv ℝ ℝ e
        ((c (modeOrder p) ^ s) •
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
            (tensorModeEmbedding (modeOrder p) (A (modeOrder p)))))).prod =
        (List.ofFn (fun p : Fin n =>
          (c (modeOrder p) ^ s) • factors p)).prod := by
          exact congrArg (fun f => (List.ofFn f).prod) hfactorFun
    _ = (∏ i : ι, c i ^ s) • (List.ofFn factors).prod := by
      have h := hscaledList
        (List.ofFn (fun p : Fin n => (c (modeOrder p) ^ s, factors p)))
      simp only [List.map_ofFn, Function.comp_apply, List.prod_ofFn] at h
      rw [modeOrder.prod_comp (fun i => c i ^ s)] at h
      exact h
    _ = (∏ i : ι, c i ^ s) •
        Matrix.reindexAlgEquiv ℝ ℝ e (tensorKronecker B) := by
      rw [List.prod_ofFn_tensorModeEmbedding_eq_tensorKronecker
        (modeOrder := modeOrder) (e := e) (B := B)]
    _ = Matrix.reindexAlgEquiv ℝ ℝ e
        ((∏ i : ι, c i ^ s) • tensorKronecker B) := by
      rfl
    _ = Matrix.reindexAlgEquiv ℝ ℝ e
        ((∏ i : ι, c i ^ s) •
          tensorKronecker (fun i =>
            cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (A i))) := by
      rfl

end SOptLib


open scoped ComplexOrder ContinuousFunctionalCalculus Kronecker

namespace SOptLib

private theorem tensorsPrivate_polynomial_aeval_diagonal
    {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (d : ι → R) (p : Polynomial R) :
    Polynomial.aeval (Matrix.diagonal d : Matrix ι ι R) p =
      Matrix.diagonal (fun i : ι => p.eval (d i)) := by
  calc
    Polynomial.aeval (Matrix.diagonal d : Matrix ι ι R) p =
        (Matrix.diagonalAlgHom R : (ι → R) →ₐ[R] Matrix ι ι R)
          (Polynomial.aeval d p) := by
      simpa using
        (Polynomial.aeval_algHom_apply
          (f := (Matrix.diagonalAlgHom R : (ι → R) →ₐ[R] Matrix ι ι R))
          (x := d) (p := p))
    _ = Matrix.diagonal (fun i : ι => p.eval (d i)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Polynomial.aeval_pi_apply]
      · simp [hij]

private theorem tensorsPrivate_cfc_rpow_diagonal
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (d : iota → ℝ) (s : ℝ) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.diagonal d : Matrix iota iota ℝ) =
      Matrix.diagonal (fun i : iota => (d i) ^ s) := by
  classical
  let D : Matrix iota iota ℝ := Matrix.diagonal d
  let q : Polynomial ℝ :=
    Lagrange.interpolate (Finset.univ : Finset {x : ℝ // x ∈ Set.range d})
      (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
      (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ) ^ s)
  have hD : IsSelfAdjoint D := by
    change D.IsHermitian
    simpa only [D] using
      Matrix.isHermitian_diagonal_of_self_adjoint d (IsSelfAdjoint.all d)
  have hinj : Set.InjOn
      (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
      ((Finset.univ : Finset {x : ℝ // x ∈ Set.range d}) :
        Set {x : ℝ // x ∈ Set.range d}) := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have hq_eval : ∀ i : iota, q.eval (d i) = (d i) ^ s := by
    intro i
    have hnode := Lagrange.eval_interpolate_at_node
      (s := (Finset.univ : Finset {x : ℝ // x ∈ Set.range d}))
      (v := fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
      (r := fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ) ^ s)
      hinj (Finset.mem_univ (⟨d i, ⟨i, rfl⟩⟩ : {x : ℝ // x ∈ Set.range d}))
    simpa [q] using hnode
  have hspec : spectrum ℝ D = Set.range d := by
    change spectrum ℝ (Matrix.diagonal d) = Set.range d
    exact spectrum_diagonal (R := ℝ) (n := iota) (d := d)
  have hfg : (spectrum ℝ D).EqOn (fun x : ℝ => x ^ s) q.eval := by
    rw [hspec]
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact (hq_eval i).symm
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.diagonal d : Matrix iota iota ℝ) =
        cfc (R := ℝ) (p := IsSelfAdjoint) q.eval D := by
          simpa [D] using
            (cfc_congr (R := ℝ) (A := Matrix iota iota ℝ)
              (p := IsSelfAdjoint) (a := D) hfg)
    _ = Polynomial.aeval D q := by
          simpa using
            (cfc_polynomial (R := ℝ) (A := Matrix iota iota ℝ)
              (p := IsSelfAdjoint) q D (ha := hD))
    _ = Matrix.diagonal (fun i : iota => (d i) ^ s) := by
          rw [tensorsPrivate_polynomial_aeval_diagonal]
          ext i j
          by_cases hij : i = j
          · subst j
            simp [hq_eval]
          · simp [hij]

private theorem tensorsPrivate_cfc_unitary_conj
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (U : unitary (Matrix ι ι 𝕜)) (D : Matrix ι ι 𝕜)
    (hD : IsSelfAdjoint D) :
    cfc (R := ℝ) (p := IsSelfAdjoint) f
        (((U : Matrix ι ι 𝕜) * D) * star (U : Matrix ι ι 𝕜)) =
      ((U : Matrix ι ι 𝕜) *
          cfc (R := ℝ) (p := IsSelfAdjoint) f D) *
        star (U : Matrix ι ι 𝕜) := by
  classical
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι 𝕜) U
  have hcontφ : Continuous (φ : Matrix ι ι 𝕜 → Matrix ι ι 𝕜) := by
    simpa [φ, Unitary.conjStarAlgAut_apply] using
      (show Continuous (fun X : Matrix ι ι 𝕜 =>
        (U : Matrix ι ι 𝕜) * X * star (U : Matrix ι ι 𝕜)) from by fun_prop)
  have hfD : ContinuousOn f (spectrum ℝ D) := by
    have hfin : (spectrum ℝ D).Finite := by
      rw [(show Matrix.IsHermitian D from hD).spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hφD : IsSelfAdjoint (φ D) := by
    change IsSelfAdjoint (((U : Matrix ι ι 𝕜) * D) * star (U : Matrix ι ι 𝕜))
    exact (Matrix.isHermitian_mul_mul_conjTranspose
      (U : Matrix ι ι 𝕜) (show Matrix.IsHermitian D from hD)).isSelfAdjoint
  have hmap := (φ : Matrix ι ι 𝕜 →⋆ₐ[ℝ] Matrix ι ι 𝕜).map_cfc
      f D (hf := hfD) (hφ := hcontφ) (ha := hD) (hφa := hφD)
  simpa [φ, Unitary.conjStarAlgAut_apply] using hmap.symm

private theorem tensorsPrivate_kronecker_spectral_decomposition
    {𝕜 : Type w} [RCLike 𝕜]
    {m : Type u} [Fintype m] [DecidableEq m]
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ⊗ₖ B =
      ((hA.eigenvectorUnitary : Matrix m m 𝕜) ⊗ₖ
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) *
        Matrix.diagonal
          (fun ij : m × n =>
            RCLike.ofReal (hA.eigenvalues ij.1) *
              RCLike.ofReal (hB.eigenvalues ij.2)) *
        star
          ((hA.eigenvectorUnitary : Matrix m m 𝕜) ⊗ₖ
            (hB.eigenvectorUnitary : Matrix n n 𝕜)) := by
  classical
  let UA : Matrix m m 𝕜 := hA.eigenvectorUnitary
  let UB : Matrix n n 𝕜 := hB.eigenvectorUnitary
  let DA : Matrix m m 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let DB : Matrix n n 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have hAspec : A = UA * DA * star UA := by
    simpa [UA, DA, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hBspec : B = UB * DB * star UB := by
    simpa [UB, DB, Unitary.conjStarAlgAut_apply] using hB.spectral_theorem
  calc
    A ⊗ₖ B = (UA * DA * star UA) ⊗ₖ (UB * DB * star UB) := by
      rw [hAspec, hBspec]
    _ = ((UA ⊗ₖ UB) * (DA ⊗ₖ DB)) * (star UA ⊗ₖ star UB) := by
      rw [Matrix.mul_assoc UA DA (star UA), Matrix.mul_assoc UB DB (star UB)]
      rw [Matrix.mul_kronecker_mul UA (DA * star UA) UB (DB * star UB)]
      rw [Matrix.mul_kronecker_mul DA (star UA) DB (star UB)]
      rw [Matrix.mul_assoc]
    _ = ((UA ⊗ₖ UB) * (DA ⊗ₖ DB)) * star (UA ⊗ₖ UB) := by
      have hstar : star (UA ⊗ₖ UB) = star UA ⊗ₖ star UB := by
        simpa only [Matrix.star_eq_conjTranspose] using
          (Matrix.conjTranspose_kronecker UA UB)
      rw [hstar]
    _ = (UA ⊗ₖ UB) * (DA ⊗ₖ DB) * star (UA ⊗ₖ UB) := by
      rw [Matrix.mul_assoc]
    _ = (UA ⊗ₖ UB) *
          Matrix.diagonal
            (fun ij : m × n =>
              RCLike.ofReal (hA.eigenvalues ij.1) *
                RCLike.ofReal (hB.eigenvalues ij.2)) *
          star (UA ⊗ₖ UB) := by
      simp only [DA, DB, Matrix.diagonal_kronecker_diagonal,
        Function.comp_apply]

private theorem tensorsPrivate_cfc_rpow_kronecker
    {𝕜 : Type w} [RCLike 𝕜]
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι 𝕜) (B : Matrix κ κ 𝕜) (s : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (A ⊗ₖ B) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A ⊗ₖ
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) B := by
  classical
  let UAunit : unitary (Matrix ι ι 𝕜) := hA.1.eigenvectorUnitary
  let UBunit : unitary (Matrix κ κ 𝕜) := hB.1.eigenvectorUnitary
  let UAB : unitary (Matrix (ι × κ) (ι × κ) 𝕜) :=
    ⟨(UAunit : Matrix ι ι 𝕜) ⊗ₖ (UBunit : Matrix κ κ 𝕜),
      Matrix.kronecker_mem_unitary UAunit.property UBunit.property⟩
  let lam : ι × κ → ℝ :=
    fun ij => hA.1.eigenvalues ij.1 * hB.1.eigenvalues ij.2
  have hdiag :
      A ⊗ₖ B =
        (UAB : Matrix (ι × κ) (ι × κ) 𝕜) *
          Matrix.diagonal (RCLike.ofReal ∘ lam) *
          star (UAB : Matrix (ι × κ) (ι × κ) 𝕜) := by
    have hd :
        (Matrix.diagonal (RCLike.ofReal ∘ lam) :
          Matrix (ι × κ) (ι × κ) 𝕜) =
          Matrix.diagonal (fun ij : ι × κ =>
            RCLike.ofReal (hA.1.eigenvalues ij.1) *
              RCLike.ofReal (hB.1.eigenvalues ij.2)) := by
      congr 1
      funext ij
      exact RCLike.ofReal_mul _ _
    rw [hd]
    simpa [UAB, UAunit, UBunit] using
      tensorsPrivate_kronecker_spectral_decomposition A B hA.1 hB.1
  have hlam : ∀ ij : ι × κ, 0 ≤ lam ij := by
    intro ij
    exact mul_nonneg (hA.eigenvalues_nonneg ij.1) (hB.eigenvalues_nonneg ij.2)
  let scalarCast : ℝ →⋆ₐ[ℝ] 𝕜 :=
    StarAlgHom.mk RCLike.ofRealAm (by intro x; simp)
  let matrixCast : Matrix (ι × κ) (ι × κ) ℝ →⋆ₐ[ℝ]
      Matrix (ι × κ) (ι × κ) 𝕜 :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let Dreal : Matrix (ι × κ) (ι × κ) ℝ := Matrix.diagonal lam
  let D : Matrix (ι × κ) (ι × κ) 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ lam)
  have hDreal : IsSelfAdjoint Dreal := by
    change Dreal.IsHermitian
    simpa only [Dreal] using
      Matrix.isHermitian_diagonal_of_self_adjoint lam (IsSelfAdjoint.all lam)
  have hD : IsSelfAdjoint D := by
    change D.IsHermitian
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    exact funext fun ij => by simp [Function.comp_apply]
  have hcastD : matrixCast Dreal = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [matrixCast, scalarCast, Dreal, D, Function.comp_def]
    · simp [matrixCast, scalarCast, Dreal, D, Function.comp_def, hij]
  have hcontinuous : Continuous matrixCast := by
    change Continuous (fun M : Matrix (ι × κ) (ι × κ) ℝ =>
      Matrix.map M scalarCast)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun M : Matrix (ι × κ) (ι × κ) ℝ =>
      RCLike.ofReal (M i j))
    fun_prop
  have hf : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ Dreal) := by
    have hfinite : (spectrum ℝ Dreal).Finite := by
      rw [(show Matrix.IsHermitian Dreal from hDreal).spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfinite.continuousOn _
  have hmap := matrixCast.map_cfc (fun x : ℝ => x ^ s) Dreal
    (hf := hf) (hφ := hcontinuous) (ha := hDreal) (hφa := hcastD ▸ hD)
  have hcfcD :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) D =
        Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) := by
    rw [← hcastD, ← hmap, tensorsPrivate_cfc_rpow_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [matrixCast, scalarCast, Function.comp_def]
    · simp [matrixCast, scalarCast, Function.comp_def, hij]
  rw [hdiag]
  rw [tensorsPrivate_cfc_unitary_conj (fun x : ℝ => x ^ s) UAB D hD]
  rw [hcfcD, hA.1.cfc_eq, hB.1.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_apply]
  let UA : Matrix ι ι 𝕜 := hA.1.eigenvectorUnitary
  let UB : Matrix κ κ 𝕜 := hB.1.eigenvectorUnitary
  let DApow : Matrix ι ι 𝕜 :=
    Matrix.diagonal (fun i : ι => RCLike.ofReal (hA.1.eigenvalues i ^ s))
  let DBpow : Matrix κ κ 𝕜 :=
    Matrix.diagonal (fun j : κ => RCLike.ofReal (hB.1.eigenvalues j ^ s))
  have hdiagpow :
      Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) =
      DApow ⊗ₖ DBpow := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext ij
    simp only [lam, DApow, DBpow, Function.comp_apply]
    rw [Real.mul_rpow (hA.eigenvalues_nonneg ij.1)
      (hB.eigenvalues_nonneg ij.2)]
    exact RCLike.ofReal_mul _ _
  calc
    (UAB : Matrix (ι × κ) (ι × κ) 𝕜) *
          Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) *
          star (UAB : Matrix (ι × κ) (ι × κ) 𝕜) =
        (UA ⊗ₖ UB) *
          Matrix.diagonal (RCLike.ofReal ∘ fun ij : ι × κ => lam ij ^ s) *
          star (UA ⊗ₖ UB) := by
      simp [UAB, UAunit, UBunit, UA, UB]
    _ = (UA ⊗ₖ UB) * (DApow ⊗ₖ DBpow) * star (UA ⊗ₖ UB) := by
      rw [hdiagpow]
    _ = ((UA ⊗ₖ UB) * (DApow ⊗ₖ DBpow)) *
          (star UA ⊗ₖ star UB) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
        Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    _ = (UA * DApow * star UA) ⊗ₖ (UB * DBpow * star UB) := by
      rw [Matrix.mul_assoc UA DApow (star UA),
        Matrix.mul_assoc UB DBpow (star UB)]
      rw [Matrix.mul_kronecker_mul UA (DApow * star UA) UB (DBpow * star UB)]
      rw [Matrix.mul_kronecker_mul DApow (star UA) DBpow (star UB)]
      rw [Matrix.mul_assoc]
    _ = ((hA.1.eigenvectorUnitary : Matrix ι ι 𝕜) *
          Matrix.diagonal
            (fun i : ι => RCLike.ofReal (hA.1.eigenvalues i ^ s)) *
          star (hA.1.eigenvectorUnitary : Matrix ι ι 𝕜)) ⊗ₖ
        ((hB.1.eigenvectorUnitary : Matrix κ κ 𝕜) *
          Matrix.diagonal
            (fun j : κ => RCLike.ofReal (hB.1.eigenvalues j ^ s)) *
          star (hB.1.eigenvectorUnitary : Matrix κ κ 𝕜)) := by
      simp [UA, UB, DApow, DBpow]

private theorem tensorsPrivate_reindexAlgEquiv_cfc_rpow
    {iota : Type u} {kappa : Type v}
    [Fintype iota] [Fintype kappa] [DecidableEq iota] [DecidableEq kappa]
    (e : iota ≃ kappa) (A : Matrix iota iota ℝ) (s : ℝ)
    (hA : A.IsHermitian) :
    Matrix.reindexAlgEquiv ℝ ℝ e
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.reindexAlgEquiv ℝ ℝ e A) := by
  classical
  let phi : Matrix iota iota ℝ →⋆ₐ[ℝ] Matrix kappa kappa ℝ := by
    change CStarMatrix iota iota ℝ →⋆ₐ[ℝ] CStarMatrix kappa kappa ℝ
    exact StarAlgHomClass.toStarAlgHom (CStarMatrix.reindexₐ ℝ ℝ e)
  have hf : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [hA.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hphiA : (phi A).IsHermitian := by
    change (Matrix.reindex e e A).IsHermitian
    exact hA.reindex e
  have hmap :
      phi (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A) =
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (phi A) := by
    exact
      (phi : Matrix iota iota ℝ →⋆ₐ[ℝ] Matrix kappa kappa ℝ).map_cfc
        (fun x : ℝ => x ^ s) A (hf := hf)
        (hφ := by
          simpa [phi, CStarMatrix.reindexₐ, CStarMatrix.reindexₗ,
            Matrix.reindexAlgEquiv_apply] using
            (Matrix.reindexLinearEquiv ℝ ℝ e e).toLinearMap.continuous_of_finiteDimensional)
        (ha := hA) (hφa := hphiA)
  calc
    Matrix.reindexAlgEquiv ℝ ℝ e
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A) =
        phi (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A) := by
          rfl
    _ = cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) (phi A) := hmap
    _ = cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.reindexAlgEquiv ℝ ℝ e A) := by
          rfl

universe u

-- Generalization plan (G0):
-- concept/name: compatibility of real continuous-functional-calculus powers
--   with dependent finite-family Kronecker products; orig was
--   `psdMatrixPower_tensorKronecker`, renamed `tensorKronecker_cfc_rpow`
-- generality used: arbitrary finite dependent coordinate types, real square
--   matrices, an arbitrary real exponent, and pointwise positive
--   semidefiniteness; no optimization, measure, or algorithm-state assumptions
-- portable call pattern: tensor AdaGrad, Shampoo, and multilinear
--   preconditioner proofs change the number of modes, dependent coordinate
--   types, PSD mode matrices, and exponent while distributing a CFC power
--   through the same assembled tensor operator
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; the staged binary Kronecker theorem handles only one induction
--   step, while this result packages the dependent-family reindexing, empty
--   product, PSD closure, and arbitrary-mode induction needed by future callers
-- coverage search: symbol queries for "dependent finite tensor Kronecker product
--   continuous functional calculus real power equality positive semidefinite"
--   and "tensorKronecker cfc rpow", plus the corresponding Mathlib semantic
--   query, found `tensorsPrivate_cfc_rpow_kronecker`, `CFC.rpow_eq_rpow_prod`, and
--   `tensorKronecker_posSemidef` as partial components but no full-family theorem
-- minimal hypotheses: pointwise positive semidefiniteness is sufficient because
--   `tensorKronecker_posSemidef` derives positivity of the assembled operator;
--   finite decidable coordinate types are required by finite matrix CFC

/-- The real continuous-functional-calculus power of a dependent finite-family
Kronecker product of positive-semidefinite matrices is the dependent Kronecker
product of their corresponding powers.

Layer: Model | Gap: Level 2 (CFC real powers of dependent finite-family Kronecker products)
Proof: induct on the number of modes, split each successor family into its head and tail through the canonical dependent-index equivalence, apply binary `tensorsPrivate_cfc_rpow_kronecker`, and transport the CFC power through matrix reindexing.
Source: Mathlib finite Hermitian matrix continuous functional calculus and Kronecker-product algebra, together with SOptLib's dependent tensor Kronecker identity and positive-semidefinite closure laws
Used in: tensor adaptive-gradient and multilinear preconditioning proofs that separate a fractional power of an assembled tensor operator into independently powered mode factors
Book citation: book/research/Source.json#/key_lemmas/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem tensorKronecker_cfc_rpow {k : Nat} {dims : Fin k → Type u}
    [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (M : (i : Fin k) → Matrix (dims i) (dims i) Real) (s : Real)
    (hM : ∀ i : Fin k, (M i).PosSemidef) :
    cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
        (tensorKronecker M) =
      tensorKronecker (fun i : Fin k =>
        cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s) (M i)) := by
  classical
  induction k with
  | zero =>
      have hbase :
          tensorKronecker M =
            (1 : Matrix (TensorIndex dims) (TensorIndex dims) Real) := by
        rw [show M = fun i : Fin 0 =>
          (1 : Matrix (dims i) (dims i) Real) by
            funext i
            exact Fin.elim0 i]
        exact tensorKronecker_one (dims := dims) (R := Real)
      have hpow_one :
          tensorKronecker (fun i : Fin 0 =>
            cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s) (M i)) =
              (1 : Matrix (TensorIndex dims) (TensorIndex dims) Real) := by
        rw [show (fun i : Fin 0 =>
          cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s) (M i)) =
            fun i : Fin 0 => (1 : Matrix (dims i) (dims i) Real) by
              funext i
              exact Fin.elim0 i]
        exact tensorKronecker_one (dims := dims) (R := Real)
      rw [hbase, hpow_one]
      simp
  | succ k ih =>
      let e : TensorIndex dims ≃
          dims 0 × TensorIndex (fun i : Fin k => dims i.succ) :=
        { toFun := fun idx => (idx 0, fun i => idx i.succ)
          invFun := fun rc => Fin.cases rc.1 rc.2
          left_inv := by
            intro idx
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j
              rfl
          right_inv := by
            intro rc
            rcases rc with ⟨head, tail⟩
            apply Prod.ext
            · rfl
            · funext i
              rfl }
      let tailM : (i : Fin k) → Matrix (dims i.succ) (dims i.succ) Real :=
        fun i => M i.succ
      have hfull : (tensorKronecker M).PosSemidef :=
        tensorKronecker_posSemidef M hM
      have htail : (tensorKronecker tailM).PosSemidef :=
        tensorKronecker_posSemidef tailM (fun i => hM i.succ)
      have heq :
          Matrix.reindexAlgEquiv Real Real e (tensorKronecker M) =
            (M 0) ⊗ₖ tensorKronecker tailM := by
        ext rc rc'
        rcases rc with ⟨head, tail⟩
        rcases rc' with ⟨head', tail'⟩
        simp [e, tailM, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
          Matrix.kroneckerMap_apply, tensorKronecker, Fin.prod_univ_succ]
      have htail_pow :
          cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
              (tensorKronecker tailM) =
            tensorKronecker (fun i : Fin k =>
              cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                (tailM i)) := by
        exact ih tailM (fun i => hM i.succ)
      have hpow_reindex :
          Matrix.reindexAlgEquiv Real Real e
              (tensorKronecker (fun i : Fin (k + 1) =>
                cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                  (M i))) =
            cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                (M 0) ⊗ₖ
              tensorKronecker (fun i : Fin k =>
                cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                  (tailM i)) := by
        ext rc rc'
        rcases rc with ⟨head, tail⟩
        rcases rc' with ⟨head', tail'⟩
        simp [e, tailM, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
          Matrix.kroneckerMap_apply, tensorKronecker, Fin.prod_univ_succ]
      have hleft_reindex :
          Matrix.reindexAlgEquiv Real Real e
              (cfc (R := Real) (p := IsSelfAdjoint)
                (fun x : Real => x ^ s) (tensorKronecker M)) =
            cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                (M 0) ⊗ₖ
              tensorKronecker (fun i : Fin k =>
                cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                  (tailM i)) := by
        calc
          Matrix.reindexAlgEquiv Real Real e
              (cfc (R := Real) (p := IsSelfAdjoint)
                (fun x : Real => x ^ s) (tensorKronecker M)) =
              cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                (Matrix.reindexAlgEquiv Real Real e (tensorKronecker M)) := by
                  exact tensorsPrivate_reindexAlgEquiv_cfc_rpow e
                    (tensorKronecker M) s hfull.1
          _ = cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                ((M 0) ⊗ₖ tensorKronecker tailM) := by rw [heq]
          _ = cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                  (M 0) ⊗ₖ
                cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                  (tensorKronecker tailM) := by
                    exact tensorsPrivate_cfc_rpow_kronecker
                      (M 0) (tensorKronecker tailM) s (hM 0) htail
          _ = cfc (R := Real) (p := IsSelfAdjoint) (fun x : Real => x ^ s)
                  (M 0) ⊗ₖ
                tensorKronecker (fun i : Fin k =>
                  cfc (R := Real) (p := IsSelfAdjoint)
                    (fun x : Real => x ^ s) (tailM i)) := by rw [htail_pow]
      exact (Matrix.reindexAlgEquiv Real Real e).injective
        (hleft_reindex.trans hpow_reindex.symm)

end SOptLib



namespace Matrix

universe u v w

-- Generalization plan (G0):
-- concept/name: self outer product of a product-index vector factorization;
--   orig was `vectorKronecker_outer_eq_kron_outer`, renamed
--   `Matrix.vecMulVec_vectorKronecker_self`
-- generality used: arbitrary index types and coefficients in a commutative semigroup;
--   no finiteness, decidable equality, additive, topological, measure, convexity,
--   smoothness, or oracle assumptions are used
-- portable call pattern: matrix and tensor rank-one decomposition proofs rewrite the
--   self outer product of a vectorized rank-one factor into the Kronecker product of
--   factor Gram matrices while changing both index types, scalar type, and factors
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it connects `Matrix.vecMulVec`, function uncurrying, and `Matrix.kronecker` in a
--   reusable representation identity not supplied by either primitive alone
-- coverage search: project symbol searches for "vector outer product Kronecker product
--   equality" and "vecMulVec self outer Kronecker" found only the private source lemma;
--   Mathlib semantic search found `Matrix.kronecker`, `Matrix.kroneckerMap_apply`, and
--   `Matrix.mul_kronecker_mul`, but no outer-product identity, so coverage is partial
-- minimal hypotheses: `[CommSemigroup R]` is exactly the associativity and commutativity
--   needed to reorder the four coordinate factors; all source finiteness and real-scalar
--   restrictions were removed

/-- The self outer product of an uncurried vector outer product is the Kronecker product
of the self outer products of its two vector factors.

Layer: Model | Gap: Level 1 (vector outer-product and matrix Kronecker representation bridge)
Proof: extensionality reduces the matrix identity to four scalar factors; associativity and commutativity put the factors in the Kronecker coordinate order
Source: Mathlib `Matrix.vecMulVec`, `Matrix.kronecker`, and their coordinate formulas
Used in: matrix and tensor adaptive-gradient rank-domination proofs that rewrite vectorized rank-one outer products into Kronecker products of factor Gram matrices
Book citation: book/research/Source.json#/key_lemmas/10/proof/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem vecMulVec_vectorKronecker_self
    {ι : Type u} {κ : Type v} {R : Type w} [CommSemigroup R]
    (u : ι → R) (v : κ → R) :
    Matrix.vecMulVec (Function.uncurry (Matrix.vecMulVec u v))
        (Function.uncurry (Matrix.vecMulVec u v)) =
      Matrix.kronecker (Matrix.vecMulVec u u) (Matrix.vecMulVec v v) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Function.uncurry, Matrix.vecMulVec_apply, Matrix.kroneckerMap_apply,
    mul_left_comm, mul_comm]

end Matrix



open scoped BigOperators ContinuousFunctionalCalculus MatrixOrder

namespace SOptLib

universe u v

-- Generalization plan (G0):
-- concept/name: prefix closure of regularized finite-family tensor rank domination;
--   orig was `theorem10_prefix_rank_domination`
-- generality used: an arbitrary finite nonempty mode type, arbitrary finite decidable
--   mode-dependent coordinate types, a finite tensor family, positive-natural modewise
--   rank caps, a nonnegative real ridge, and an arbitrary prefix endpoint
-- portable call pattern: an online tensor adaptive method applies a full-family
--   tensor-rank domination theorem to the zero-masked prefix while changing the tensor
--   sequence, horizon, endpoint, rank caps, ridge, mode type, and tensor dimensions
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it
--   packages the nontrivial preservation of every matricization-rank hypothesis under
--   prefix masking together with simultaneous outer-product and contraction-sum rewrites
-- coverage search: symbol searches for "regularized tensor rank prefix outer sum upper
--   bound geometric mean tensor Kronecker contraction", "finite family tensor rank
--   domination outer product sum contraction matrix powers", and "tensor rank domination
--   geometric mean Kronecker contraction" found no covering SOptLib declaration; Mathlib
--   semantic search returned only binary Kronecker-product and rank-one matrix primitives
-- minimal hypotheses: coordinate finiteness and decidable equality support matrix rank,
--   multiplication, and Loewner order; nonempty finite modes support the positive-natural
--   geometric mean; rank control is required only on the retained prefix, and the supplied
--   full-family principle is specialized to the fixed ridge used in the conclusion

/-- A regularized prefix sum of tensor vector outer products inherits finite-family
rank domination by the geometric mean of the modewise rank caps times the Kronecker
product of the corresponding regularized contraction-prefix powers.

The full-family domination premise at the fixed ridge is applied to the family obtained by
replacing every tensor after the prefix endpoint by zero; the rank hypothesis is required
only for tensors retained by that mask.

Layer: Model | Gap: Level 2 (prefix closure of finite-family tensor rank domination)
Proof: zero-mask the tensor family after the endpoint, preserve each matricization rank bound, apply the supplied full-family domination principle, and rewrite the masked outer-product and contraction sums as prefix sums
Source: Mathlib finite sums, matrix rank of zero, Loewner order, continuous functional calculus real powers, and SOptLib tensor matricization, contraction, Kronecker product, and positive-natural geometric mean APIs
Used in: online tensor adaptive-gradient analyses that compare a regularized flattened gradient outer-product prefix with powered modewise contraction accumulators at the same time endpoint
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 tensor Shampoo -/
theorem regularized_tensor_rank_prefix_outer_sum_le_geometricMean_smul_tensorKronecker_contraction_prefix
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {T : Nat} {dims : ι → Type v}
    [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (G : Fin T → TensorSpace dims ℝ) (rankBound : ι → ℕ+)
    (epsilon : ℝ) (N : Fin (T + 1))
    (hrank : ∀ i : ι, ∀ t : Fin T,
      t.1 < N.1 →
      (tensorMatricization (G t) i).rank ≤ (rankBound i : ℕ))
    (full_family_domination :
      ∀ (H : Fin T → TensorSpace dims ℝ),
        (∀ i : ι, ∀ t : Fin T,
          (tensorMatricization (H t) i).rank ≤ (rankBound i : ℕ)) →
        epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
            ∑ t : Fin T, Matrix.vecMulVec (H t) (H t) ≤
          positiveNatGeometricMean rankBound •
            tensorKronecker (fun i : ι =>
              cfc (R := ℝ) (p := IsSelfAdjoint)
                (fun x : ℝ => x ^ (1 / (Fintype.card ι : ℝ)))
                (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
                  ∑ t : Fin T, tensorContraction (H t) i))) :
    epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
        (∑ t : Fin T,
          if t.1 < N.1 then Matrix.vecMulVec (G t) (G t) else 0) ≤
      positiveNatGeometricMean rankBound •
        tensorKronecker (fun i : ι =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / (Fintype.card ι : ℝ)))
            (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
              ∑ t : Fin T,
                if t.1 < N.1 then tensorContraction (G t) i else 0)) := by
  classical
  let H : Fin T → TensorSpace dims ℝ :=
    fun t => if t.1 < N.1 then G t else 0
  have hrankH : ∀ i : ι, ∀ t : Fin T,
      (tensorMatricization (H t) i).rank ≤ (rankBound i : ℕ) := by
    intro i t
    by_cases ht : t.1 < N.1
    · simpa [H, ht] using hrank i t ht
    · have hzero : tensorMatricization (H t) i = 0 := by
        ext row col
        simp [H, ht, tensorMatricization]
      rw [hzero, Matrix.rank_zero]
      exact Nat.zero_le _
  have hOuter :
      (∑ t : Fin T, Matrix.vecMulVec (H t) (H t)) =
        ∑ t : Fin T,
          if t.1 < N.1 then Matrix.vecMulVec (G t) (G t) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    by_cases ht : t.1 < N.1
    · simp [H, ht]
    · ext a b
      simp [H, ht, Matrix.vecMulVec]
  have hContraction : ∀ i : ι,
      (∑ t : Fin T, tensorContraction (H t) i) =
        ∑ t : Fin T,
          if t.1 < N.1 then tensorContraction (G t) i else 0 := by
    intro i
    refine Finset.sum_congr rfl ?_
    intro t _ht
    by_cases ht : t.1 < N.1
    · simp [H, ht]
    · ext a b
      simp [H, ht, tensorContraction, Matrix.leftGram, tensorMatricization,
        Matrix.mul_apply]
  have hbound := full_family_domination H hrankH
  rw [hOuter] at hbound
  have hright :
      tensorKronecker (fun i : ι =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / (Fintype.card ι : ℝ)))
            (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
              ∑ t : Fin T, tensorContraction (H t) i)) =
        tensorKronecker (fun i : ι =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / (Fintype.card ι : ℝ)))
            (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
              ∑ t : Fin T,
                if t.1 < N.1 then tensorContraction (G t) i else 0)) := by
    apply congrArg tensorKronecker
    funext i
    rw [hContraction i]
  rw [hright] at hbound
  exact hbound

end SOptLib



open scoped Kronecker MatrixOrder

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: inverse-rank Loewner domination of a tensor-vectorization outer
--   product by an embedded mode contraction; orig was `tensor_single_mode_rank_bound`
-- generality used: an arbitrary finite mode type, arbitrary finite coordinate
--   types in every mode, real tensor entries, and a positive natural rank cap;
--   no measure, convexity, smoothness, oracle, topology, or algorithm-state assumptions
-- portable call pattern: low-rank tensor adaptive-gradient and multilinear
--   preconditioner proofs change the tensor, selected mode, tensor shape, and positive
--   rank cap while reusing the same full-coordinate Loewner bound
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it composes a substantive matrix inverse-rank Gram domination theorem with the
--   canonical matricization-to-full-tensor Loewner transport behind one tensor contract
-- coverage search: symbol searches for "inverse rank scaled tensor vectorization outer
--   product bounded by mode embedding contraction matricization rank" and "tensor
--   matricization vector outer Loewner mode embedding contraction rank bound" found
--   only the source-local theorem and the two strictly lower-level staged ingredients;
--   Mathlib semantic search found rank inequalities for matrices but no tensor bound
-- minimal hypotheses: finiteness supports matrix rank, Gram products, and Loewner
--   order; decidable equality supports identity matrices and mode embedding; `0 < r`
--   is exactly the positivity needed by the inverse-rank matrix theorem

/-- If one matricization of a finite real tensor has rank at most a positive natural
number `r`, then `r⁻¹` times the self outer product of its vectorization is bounded in
Loewner order by the corresponding mode contraction embedded in the full tensor space.

Layer: Model | Gap: Level 2 (inverse-rank tensor-vectorization mode-contraction domination)
Proof: apply the inverse-rank matrix-vectorization Gram bound to the selected matricization, then transport its left-Gram Kronecker bound through the canonical matricization/full-tensor Loewner equivalence.
Source: Mathlib finite real matrix rank, positive-semidefinite Loewner order, Gram matrices, Kronecker products, and dependent-product reindexing
Used in: low-rank tensor adaptive-gradient analyses that bound each gradient outer product by one embedded modewise contraction before summing and combining mode preconditioners
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 -/
theorem inv_rank_smul_tensorVectorization_vecMulVec_le_tensorModeEmbedding_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {dims : ι → Type*} [(j : ι) → Fintype (dims j)]
    [(j : ι) → DecidableEq (dims j)]
    (G : TensorSpace dims ℝ) (i : ι) (r : ℕ) (hr : 0 < r)
    (hrank : (tensorMatricization G i).rank ≤ r) :
    (r : ℝ)⁻¹ •
        Matrix.vecMulVec G G ≤
      tensorModeEmbedding i (tensorContraction G i) := by
  let c : ℝ := Real.sqrt (r : ℝ)⁻¹
  let H : TensorSpace dims ℝ := fun idx => c * G idx
  have hc : c * c = (r : ℝ)⁻¹ := by
    exact Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hmat :=
    (Matrix.inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams
      (tensorMatricization G i) r hr hrank).2
  have hscaledMat :
      Matrix.vecMulVec (Function.uncurry (tensorMatricization H i))
          (Function.uncurry (tensorMatricization H i)) =
        (r : ℝ)⁻¹ •
          Matrix.vecMulVec (Function.uncurry (tensorMatricization G i))
            (Function.uncurry (tensorMatricization G i)) := by
    ext rc rc'
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    change (c * _) * (c * _) = (r : ℝ)⁻¹ * (_ * _)
    ring_nf
    rw [show c ^ 2 = (r : ℝ)⁻¹ by simpa [pow_two] using hc]
    ring
    simp [tensorMatricization, Function.uncurry]
  have hmatH :
      Matrix.vecMulVec (Function.uncurry (tensorMatricization H i))
          (Function.uncurry (tensorMatricization H i)) ≤
        tensorContraction G i ⊗ₖ
          (1 : Matrix (TensorModeColumn dims i) (TensorModeColumn dims i) ℝ) := by
    rw [hscaledMat]
    simpa [tensorContraction] using hmat
  have hsplit (rc : dims i × TensorModeColumn dims i) :
      (fun j => if h : j = i then
          _root_.cast (by rw [h]) rc.1 else rc.2 ⟨j, h⟩) =
        (Equiv.piSplitAt i dims).symm rc := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt, hji]
  have htensor :=
    (tensorMatricization_vecMulVec_le_kronecker_iff
      H i (tensorContraction G i)).1 (by
        convert hmatH using 1
        ext rc rc'
        simp [Matrix.vecMulVec_apply, tensorMatricization, Function.uncurry,
          hsplit])
  have hscaledTensor :
      Matrix.vecMulVec H H =
        (r : ℝ)⁻¹ •
          Matrix.vecMulVec G G := by
    ext idx idx'
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    change (c * _) * (c * _) = (r : ℝ)⁻¹ * (_ * _)
    ring_nf
    rw [show c ^ 2 = (r : ℝ)⁻¹ by simpa [pow_two] using hc]
    ring
  rw [← hscaledTensor]
  simpa [tensorModeEmbedding] using htensor

end SOptLib



open scoped BigOperators MatrixOrder

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: regularized finite-family tensor-vector outer-product domination by
--   a rank-scaled embedded mode-contraction sum; orig was `tensor_mode_accumulated_bound`
-- generality used: arbitrary finite family and mode types, arbitrary finite decidable
--   coordinate types, real tensor entries, a positive natural rank cap, a pointwise
--   matricization-rank bound, and a nonnegative real ridge; no algorithm state,
--   measure, convexity, smoothness, oracle, or topology assumptions
-- portable call pattern: modewise low-rank tensor preconditioners change the finite
--   tensor family, selected mode, tensor shape, positive rank cap, and nonnegative ridge
--   while reusing the same regularized accumulated Loewner bound
-- counterargument checked: this is not paper-local traceability or a one-line wrapper;
--   it lifts the single-tensor inverse-rank bound through a finite sum, removes the
--   inverse-rank scaling, absorbs the regularizer, and moves all terms through the
--   canonical tensor-mode embedding
-- coverage search: symbol queries for "regularized sum tensor vectorization outer
--   products bounded by rank times tensor mode embedding sum contractions" and
--   "nonnegative regularization identity plus sum outer products rank upper bound mode
--   embedding contraction" found the strictly pointwise inverse-rank tensor bound and a
--   later prefix-closure theorem that assumes a full-family domination principle, but no
--   declaration covering this accumulated modewise bound; Mathlib semantic search found
--   generic Loewner-order and positive-semidefinite sum facts but no tensor statement
-- minimal hypotheses: `0 < r` is exactly what removes inverse-rank scaling and implies
--   the ridge coefficient bound; pointwise rank control and `0 ≤ epsilon` are used
--   directly, while finiteness and decidable equality support sums, ranks, identities,
--   contractions, and tensor-mode embedding

/-- A nonnegative ridge plus the sum of self outer products of a finite tensor family is
bounded in Loewner order by the rank cap times the selected-mode embedding of the ridge
plus the sum of the corresponding tensor contractions.

Layer: Model | Gap: Level 2 (regularized finite-family tensor mode-rank domination)
Proof: sum the pointwise inverse-rank tensor-vectorization bounds, rescale by the positive rank cap, absorb the nonnegative identity ridge using `1 ≤ r`, and distribute the tensor-mode embedding over the resulting finite sum
Source: Mathlib finite sums and positive-semidefinite matrix Loewner order, together with SOptLib tensor vectorization, matricization rank, mode contraction, and single-mode embedding APIs
Used in: modewise low-rank tensor adaptive-gradient analyses that dominate an accumulated flattened gradient Gram matrix by one regularized mode-contraction accumulator before combining mode preconditioners
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 tensor Shampoo -/
theorem regularized_tensor_vecMulVec_sum_le_rank_smul_tensorModeEmbedding_contraction_sum
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {dims : ι → Type*} [∀ j, Fintype (dims j)] [∀ j, DecidableEq (dims j)]
    (G : α → TensorSpace dims ℝ) (i : ι) (r : ℕ) (epsilon : ℝ)
    (hr : 0 < r)
    (hrank : ∀ t : α, (tensorMatricization (G t) i).rank ≤ r)
    (hepsilon : 0 ≤ epsilon) :
    epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
        ∑ t : α, Matrix.vecMulVec (G t) (G t) ≤
      (r : ℝ) • tensorModeEmbedding i
        (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
          ∑ t : α, tensorContraction (G t) i) := by
  classical
  let S : Matrix (TensorIndex dims) (TensorIndex dims) ℝ :=
    ∑ t : α, Matrix.vecMulVec (G t) (G t)
  let E : Matrix (TensorIndex dims) (TensorIndex dims) ℝ :=
    tensorModeEmbedding i (∑ t : α, tensorContraction (G t) i)
  have hEmbedding_add (B C : Matrix (dims i) (dims i) ℝ) :
      tensorModeEmbedding i (B + C) =
        tensorModeEmbedding i B + tensorModeEmbedding i C := by
    ext a b
    simp [tensorModeEmbedding, add_mul]
  have hEmbedding_smul (c : ℝ) (B : Matrix (dims i) (dims i) ℝ) :
      tensorModeEmbedding i (c • B) = c • tensorModeEmbedding i B := by
    ext a b
    simp [tensorModeEmbedding, mul_assoc]
  have hEmbedding_sum (B : α → Matrix (dims i) (dims i) ℝ) :
      tensorModeEmbedding i (∑ t : α, B t) =
        ∑ t : α, tensorModeEmbedding i (B t) := by
    ext a b
    simp [tensorModeEmbedding, Matrix.sum_apply, Finset.sum_mul]
  have hsum_scaled : (r : ℝ)⁻¹ • S ≤ E := by
    have hsum :
        (r : ℝ)⁻¹ •
            (∑ t : α, Matrix.vecMulVec (G t) (G t)) ≤
          ∑ t : α, tensorModeEmbedding i (tensorContraction (G t) i) := by
      simpa only [Finset.smul_sum] using
        Finset.sum_le_sum (fun t _ht =>
          inv_rank_smul_tensorVectorization_vecMulVec_le_tensorModeEmbedding_contraction
            (G t) i r hr (hrank t))
    rw [← hEmbedding_sum] at hsum
    simpa [S, E] using hsum
  have hsum_unscaled : S ≤ (r : ℝ) • E := by
    have hscale :=
      smul_le_smul_of_nonneg_left hsum_scaled (Nat.cast_nonneg r : 0 ≤ (r : ℝ))
    have hrne : (r : ℝ) ≠ 0 := by
      exact_mod_cast hr.ne'
    calc
      S = (r : ℝ) • ((r : ℝ)⁻¹ • S) := by
        rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
      _ ≤ (r : ℝ) • E := hscale
  have hepsilon_bound :
      epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) ≤
        (r : ℝ) •
          (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ)) := by
    have hr_ge_one : (1 : ℝ) ≤ r := by
      exact_mod_cast hr
    rw [Matrix.le_iff]
    have hdiff :
        (r : ℝ) •
              (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ)) -
            epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) =
          ((r : ℝ) - 1) •
            (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ)) := by
      ext a b
      simp [sub_mul]
    have hscale : 0 ≤ (r : ℝ) - 1 := sub_nonneg.mpr hr_ge_one
    have hbase :
        (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ)).PosSemidef :=
      Matrix.PosSemidef.one.smul hepsilon
    simpa [hdiff] using hbase.smul hscale
  calc
    epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
        ∑ t : α, Matrix.vecMulVec (G t) (G t) ≤
      (r : ℝ) •
          (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ)) +
        (r : ℝ) • E := by
      simpa [S] using add_le_add hepsilon_bound hsum_unscaled
    _ = (r : ℝ) •
        (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) + E) := by
      rw [smul_add]
    _ = (r : ℝ) • tensorModeEmbedding i
        (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
          ∑ t : α, tensorContraction (G t) i) := by
      congr 1
      change
        epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
            tensorModeEmbedding i (∑ t : α, tensorContraction (G t) i) =
          tensorModeEmbedding i
            (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
              ∑ t : α, tensorContraction (G t) i)
      rw [hEmbedding_add, hEmbedding_smul, tensorModeEmbedding_one]

end SOptLib



open scoped BigOperators ContinuousFunctionalCalculus Kronecker MatrixOrder

namespace Matrix

universe u v

-- Generalization plan (G0):
-- concept/name: regularized low-rank matrix-prefix covariance domination by
--   Kronecker square roots of the corresponding Gram prefixes; orig was
--   `theorem7_prefix_rank_domination`, renamed
--   `Matrix.regularized_rank_prefix_vecMulVec_sum_le_cfc_sqrt_kronecker_gram_prefixes`
-- generality used: an arbitrary finite real-matrix stream with arbitrary finite
--   decidable row and column types, a positive natural rank cap, a nonnegative
--   real ridge, and an arbitrary strict-prefix endpoint; no algorithm state,
--   measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: online matrix AdaGrad, Shampoo-like, and low-rank
--   covariance-adaptive proofs change the matrix stream, horizon, endpoint,
--   rank cap, ridge, and matrix dimensions while retaining the same prefix
--   covariance-to-factored-Gram domination conclusion
-- counterargument checked: the full-family domination theorem is already
--   staged, but this is not a pure rename or paper-local wrapper because it
--   packages rank preservation under prefix masking and the simultaneous
--   rewrites of the vectorized covariance and both Gram accumulators
-- coverage search: symbol searches for "regularized prefix vectorized matrix
--   outer product rank bound Kronecker square roots left right Gram sums" and
--   "prefix sum vecMulVec rank domination kronecker Gram" found the full-family
--   `Matrix.regularized_inv_rank_vecMulVec_sum_le_cfc_sqrt_kronecker_grams`
--   and an analogous tensor-prefix theorem, but no matrix-prefix declaration;
--   Mathlib semantic search found only Loewner-order and Kronecker primitives
-- minimal hypotheses: finite decidable row and column types support matrix
--   rank, identities, Gram products, and CFC square roots; rank control is
--   needed only on the retained prefix, positivity of the natural cap supports
--   inverse-rank scaling, and ridge nonnegativity supplies PSD accumulators

/-- A regularized strict-prefix sum of vectorized matrix self outer products,
scaled by the inverse of a positive rank cap, is bounded by the Kronecker product
of the CFC square roots of the corresponding left- and right-Gram prefixes.

Layer: Model | Gap: Level 2 (prefix closure of regularized low-rank matrix covariance domination)
Proof: replace matrices after the endpoint by zero, preserve the rank bound on the masked family, apply finite-family rank domination, and rewrite its covariance and two Gram sums as strict-prefix sums.
Source: Mathlib finite real-matrix rank, finite sums, matrix Gram products, Loewner order, Kronecker products, and continuous-functional-calculus square roots
Used in: online matrix AdaGrad and Shampoo-like regret analyses that compare a regularized vectorized gradient covariance prefix with the factored row/column Gram preconditioner at the same endpoint
Book citation: book/research/Source.json#/key_lemmas/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem regularized_rank_prefix_vecMulVec_sum_le_cfc_sqrt_kronecker_gram_prefixes
    {T : Nat} {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : Fin T → Matrix ι κ ℝ) (rankBound : ℕ) (epsilon : ℝ)
    (N : Fin (T + 1)) (hrankBound : 0 < rankBound)
    (hrank : ∀ t : Fin T, t.1 < N.1 → (G t).rank ≤ rankBound)
    (hepsilon : 0 ≤ epsilon) :
    epsilon • (1 : Matrix (ι × κ) (ι × κ) ℝ) +
        (rankBound : ℝ)⁻¹ •
          (∑ t : Fin T,
            if t.1 < N.1 then
              Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))
            else 0) ≤
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (epsilon • (1 : Matrix ι ι ℝ) +
            ∑ t : Fin T, if t.1 < N.1 then Matrix.leftGram (G t) else 0) ⊗ₖ
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (epsilon • (1 : Matrix κ κ ℝ) +
            ∑ t : Fin T, if t.1 < N.1 then Matrix.rightGram (G t) else 0) := by
  classical
  let H : Fin T → Matrix ι κ ℝ :=
    fun t => if t.1 < N.1 then G t else 0
  have hrankH : ∀ t : Fin T, (H t).rank ≤ rankBound := by
    intro t
    by_cases ht : t.1 < N.1
    · simpa [H, ht] using hrank t ht
    · simp [H, ht, Matrix.rank_zero]
  have hOuter :
      (∑ t : Fin T,
          Matrix.vecMulVec (Function.uncurry (H t)) (Function.uncurry (H t))) =
        ∑ t : Fin T,
          if t.1 < N.1 then
            Matrix.vecMulVec (Function.uncurry (G t)) (Function.uncurry (G t))
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    by_cases ht : t.1 < N.1
    · simp [H, ht]
    · ext a b
      simp [H, ht, Matrix.vecMulVec, Function.uncurry]
  have hLeft :
      (∑ t : Fin T, Matrix.leftGram (H t)) =
        ∑ t : Fin T, if t.1 < N.1 then Matrix.leftGram (G t) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    by_cases ht : t.1 < N.1
    · simp [H, ht]
    · ext a b
      simp [H, ht, Matrix.leftGram, Matrix.mul_apply]
  have hRight :
      (∑ t : Fin T, Matrix.rightGram (H t)) =
        ∑ t : Fin T, if t.1 < N.1 then Matrix.rightGram (G t) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    by_cases ht : t.1 < N.1
    · simp [H, ht]
    · ext a b
      simp [H, ht, Matrix.rightGram, Matrix.mul_apply]
  have hLeftPsd :
      (epsilon • (1 : Matrix ι ι ℝ) +
        ∑ t : Fin T, if t.1 < N.1 then Matrix.leftGram (G t) else 0).PosSemidef := by
    rw [← hLeft]
    have hsum : (∑ t : Fin T, Matrix.leftGram (H t)).PosSemidef := by
      simpa using Matrix.posSemidef_sum
        (Finset.univ : Finset (Fin T))
        (fun t _ht => by
          simpa [Matrix.leftGram] using
            (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := H t)))
    exact (Matrix.PosSemidef.one.smul hepsilon).add hsum
  have hRightPsd :
      (epsilon • (1 : Matrix κ κ ℝ) +
        ∑ t : Fin T, if t.1 < N.1 then Matrix.rightGram (G t) else 0).PosSemidef := by
    rw [← hRight]
    have hsum : (∑ t : Fin T, Matrix.rightGram (H t)).PosSemidef := by
      simpa using Matrix.posSemidef_sum
        (Finset.univ : Finset (Fin T))
        (fun t _ht => by
          simpa [Matrix.rightGram] using
            (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := H t)))
    exact (Matrix.PosSemidef.one.smul hepsilon).add hsum
  have h :=
    TensorsProofSupport.Matrix.regularized_inv_rank_vecMulVec_sum_le_cfc_sqrt_kronecker_grams
      H rankBound epsilon hrankBound hrankH hepsilon
  have hLeft' :
      (∑ t : Fin T, TensorsProofSupport.Matrix.leftGram (H t)) =
        ∑ t : Fin T, if t.1 < N.1 then Matrix.leftGram (G t) else 0 := by
    simpa [TensorsProofSupport.Matrix.leftGram, Matrix.leftGram] using hLeft
  have hRight' :
      (∑ t : Fin T, TensorsProofSupport.Matrix.rightGram (H t)) =
        ∑ t : Fin T, if t.1 < N.1 then Matrix.rightGram (G t) else 0 := by
    simpa [TensorsProofSupport.Matrix.rightGram, Matrix.rightGram] using hRight
  dsimp only at h
  rw [hOuter, hLeft', hRight'] at h
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hLeftPsd.nonneg,
    CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hRightPsd.nonneg] at h
  exact h

end Matrix



open scoped BigOperators ContinuousFunctionalCalculus MatrixOrder

namespace SOptLib

universe u

-- Generalization plan (G0):
-- concept/name: square-root consequence of regularized tensor-prefix rank domination;
--   orig was `theorem10_tensor_hhat_order_from_prefix_rank_domination`
-- generality used: arbitrary finite mode-dependent coordinate types, a nonempty finite
--   mode family, a finite real tensor stream, positive-natural modewise rank caps, a
--   nonnegative ridge, a prefix endpoint, and the prefix rank-domination inequality itself
-- portable call pattern: tensor AdaGrad, Shampoo, and multilinear adaptive methods vary
--   the tensor stream, dimensions, horizon, prefix, rank caps, and ridge while converting
--   the same rank-domination inequality into a bound between powered preconditioners
-- counterargument checked: this is not paper-local traceability or a one-line wrapper;
--   it composes Loewner--Heinz monotonicity, scalar-power extraction, dependent Kronecker
--   power distribution, and iterated mode-power normalization in one reusable transition
-- coverage search: queries for "positive semidefinite matrix square root upper bound scalar
--   square root tensor Kronecker half powers from Loewner domination", "cfc square root
--   scalar multiplication tensor Kronecker matrix powers order domination", and
--   "regularized tensor rank prefix geometric mean square root Kronecker contraction half
--   power" found the component declarations `Matrix.cfc_rpow_mono_of_posSemidef`,
--   `Matrix.cfc_rpow_smul_of_nonneg`, `tensorKronecker_cfc_rpow`, and
--   `Matrix.cfc_rpow_cfc_rpow_of_posSemidef`, but no theorem with this composite contract
-- minimal hypotheses: nonnegative ridge derives both flattened and modewise prefix
--   positive-semidefiniteness; rank assumptions are intentionally absent because the proof
--   uses only their already-established Loewner domination consequence

/-- If a regularized tensor outer-product prefix is rank-dominated by the geometric mean
of modewise rank caps times the Kronecker product of powered contraction prefixes, then its
operator square root is dominated by the square root of that geometric mean times the
Kronecker product of the corresponding half-scaled mode powers.

Layer: Model | Gap: Level 2 (powered consequence of tensor-prefix rank domination)
Proof: establish positivity of the regularized flattened and modewise prefixes, apply finite-matrix Loewner--Heinz monotonicity at exponent one half, extract the nonnegative scalar power, distribute the CFC power through the dependent Kronecker product, and collapse the two mode powers by multiplying their exponents.
Source: Mathlib finite positive-semidefinite matrix order and continuous functional calculus, together with SOptLib regularized prefix Gram, tensor contraction, dependent Kronecker, geometric-mean, and CFC real-power APIs
Used in: tensor AdaGrad and Shampoo regret proofs that turn low-rank domination of a regularized gradient outer-product prefix into domination of the square-root metric by half-powered mode accumulators
Book citation: book/research/Source.json#/key_lemmas/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 2 tensor Shampoo -/
theorem regularized_tensor_rank_prefix_cfc_sqrt_le_sqrt_geometricMean_smul_tensorKronecker_half_contractions
    {k T : Nat} [Nonempty (Fin k)] {dims : Fin k → Type u}
    [∀ i, Fintype (dims i)] [∀ i, DecidableEq (dims i)]
    (G : Fin T → TensorSpace dims ℝ) (rankBound : Fin k → ℕ+)
    (epsilon : ℝ) (N : Fin (T + 1)) (hepsilon : 0 ≤ epsilon)
    (hdom :
      epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
          (∑ t : Fin T,
            if t.1 < N.1 then Matrix.vecMulVec (G t) (G t) else 0) ≤
        positiveNatGeometricMean rankBound •
          tensorKronecker (fun i : Fin k =>
            cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (1 / (k : ℝ)))
              (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
                ∑ t : Fin T,
                  if t.1 < N.1 then tensorContraction (G t) i else 0))) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
        (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
          ∑ t : Fin T,
            if t.1 < N.1 then Matrix.vecMulVec (G t) (G t) else 0) ≤
      Real.sqrt (positiveNatGeometricMean rankBound) •
        tensorKronecker (fun i : Fin k =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / ((2 : ℝ) * (k : ℝ))))
            (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
              ∑ t : Fin T,
                if t.1 < N.1 then tensorContraction (G t) i else 0)) := by
  classical
  let Hhat : Matrix (TensorIndex dims) (TensorIndex dims) ℝ :=
    epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
      ∑ t : Fin T, if t.1 < N.1 then Matrix.vecMulVec (G t) (G t) else 0
  let A : (i : Fin k) → Matrix (dims i) (dims i) ℝ := fun i =>
    epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
      ∑ t : Fin T, if t.1 < N.1 then tensorContraction (G t) i else 0
  let M : (i : Fin k) → Matrix (dims i) (dims i) ℝ := fun i =>
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / (k : ℝ))) (A i)
  let K : Matrix (TensorIndex dims) (TensorIndex dims) ℝ := tensorKronecker M
  let r : ℝ := positiveNatGeometricMean rankBound
  have hHhat : Hhat.PosSemidef := by
    simpa [Hhat, Matrix.regularizedPrefixGram] using
      (Matrix.regularizedPrefixGram_posSemidef G hepsilon N)
  have hcontraction : ∀ (i : Fin k) (t : Fin T),
      (tensorContraction (G t) i).PosSemidef := by
    intro i t
    simpa [tensorContraction] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same
        (B := tensorMatricization (G t) i))
  have hA : ∀ i : Fin k, (A i).PosSemidef := by
    intro i
    have hprefix :
        (∑ t : Fin T,
          if t.1 < N.1 then tensorContraction (G t) i else 0).PosSemidef := by
      exact Finset.sum_induction
        (fun t : Fin T => if t.1 < N.1 then tensorContraction (G t) i else 0)
        (fun B : Matrix (dims i) (dims i) ℝ => B.PosSemidef)
        (fun _ _ hB hC => hB.add hC)
        Matrix.PosSemidef.zero
        (by
          intro t _ht
          by_cases htN : t.1 < N.1
          · simpa [htN] using hcontraction i t
          · simpa [htN] using
              (Matrix.PosSemidef.zero :
                (0 : Matrix (dims i) (dims i) ℝ).PosSemidef))
    exact (Matrix.PosSemidef.one.smul hepsilon).add hprefix
  have hM : ∀ i : Fin k, (M i).PosSemidef := by
    intro i
    let U : unitary (Matrix (dims i) (dims i) ℝ) := (hA i).1.eigenvectorUnitary
    let lambda : dims i → ℝ := (hA i).1.eigenvalues
    have hdiag :
        A i = (U : Matrix (dims i) (dims i) ℝ) * Matrix.diagonal lambda *
          star (U : Matrix (dims i) (dims i) ℝ) := by
      simpa [U, lambda, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        (hA i).1.spectral_theorem
    have hpow :
        M i = (U : Matrix (dims i) (dims i) ℝ) *
            Matrix.diagonal (fun j => (lambda j) ^ (1 / (k : ℝ))) *
              star (U : Matrix (dims i) (dims i) ℝ) := by
      simpa [M] using
        TensorsProofSupport.Matrix.cfc_rpow_eq_of_unitary_diagonalization
        (A i) (1 / (k : ℝ)) U lambda hdiag
    have hdiag_psd :
        (Matrix.diagonal (fun j => (lambda j) ^ (1 / (k : ℝ))) :
          Matrix (dims i) (dims i) ℝ).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro j
      exact Real.rpow_nonneg ((hA i).eigenvalues_nonneg j) _
    have hU : IsUnit (U : Matrix (dims i) (dims i) ℝ) := (Unitary.toUnits U).isUnit
    rw [hpow]
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU).mpr hdiag_psd
  have hK : K.PosSemidef := by
    exact tensorKronecker_posSemidef M hM
  have hr_nonneg : 0 ≤ r := (positiveNatGeometricMean_pos rankBound).le
  have hdom' : Hhat ≤ r • K := by
    simpa [Hhat, A, M, K, r] using hdom
  have hmono :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) Hhat ≤
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (r • K) := by
    exact TensorsProofSupport.Matrix.cfc_rpow_mono_of_posSemidef
      Hhat (r • K) (1 / 2 : ℝ)
      hHhat hdom' (by constructor <;> norm_num)
  have hscale :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (r • K) =
        r ^ (1 / 2 : ℝ) •
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) K := by
    exact TensorsProofSupport.Matrix.cfc_rpow_smul_of_nonneg
      r (1 / 2 : ℝ) K hK hr_nonneg
  have hk_pos : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk_pos)
  have hexponent :
      (1 / (k : ℝ)) * (1 / 2 : ℝ) = 1 / ((2 : ℝ) * (k : ℝ)) := by
    field_simp [hk_ne]
  have hKsqrt :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) K =
        tensorKronecker (fun i : Fin k =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / ((2 : ℝ) * (k : ℝ)))) (A i)) := by
    calc
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) K =
          tensorKronecker (fun i : Fin k =>
            cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (1 / 2 : ℝ)) (M i)) := by
        simpa [K] using tensorKronecker_cfc_rpow M (1 / 2 : ℝ) hM
      _ = tensorKronecker (fun i : Fin k =>
            cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (1 / ((2 : ℝ) * (k : ℝ)))) (A i)) := by
        apply congrArg tensorKronecker
        funext i
        rw [show M i = cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => x ^ (1 / (k : ℝ))) (A i) by rfl]
        rw [TensorsProofSupport.Matrix.cfc_rpow_cfc_rpow_of_posSemidef
          (A i) (1 / (k : ℝ)) (1 / 2 : ℝ) (hA i)]
        rw [hexponent]
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
        (epsilon • (1 : Matrix (TensorIndex dims) (TensorIndex dims) ℝ) +
          ∑ t : Fin T,
            if t.1 < N.1 then Matrix.vecMulVec (G t) (G t) else 0) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
        Hhat := by rfl
    _ ≤ cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
        (r • K) := hmono
    _ = r ^ (1 / 2 : ℝ) •
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) K := hscale
    _ = Real.sqrt r • tensorKronecker (fun i : Fin k =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / ((2 : ℝ) * (k : ℝ)))) (A i)) := by
      rw [hKsqrt, Real.sqrt_eq_rpow]
    _ = Real.sqrt (positiveNatGeometricMean rankBound) •
        tensorKronecker (fun i : Fin k =>
          cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / ((2 : ℝ) * (k : ℝ))))
            (epsilon • (1 : Matrix (dims i) (dims i) ℝ) +
              ∑ t : Fin T,
                if t.1 < N.1 then tensorContraction (G t) i else 0)) := by
      rfl

end SOptLib

