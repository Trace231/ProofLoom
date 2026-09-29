import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite positive-definite matrix metric on Euclidean coordinate space; orig was `IsPositiveDefiniteMatrix` / `positiveDefiniteWeightedNorm_sq`.
-- generality used: finite coordinate type `{ι : Type*}` with `[Fintype ι] [DecidableEq ι]`, real matrix kernel `Q : ι -> ι -> ℝ`, and vector `x : EuclideanSpace ℝ ι`; no measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: adaptive-gradient, projected-gradient, and diagonal-metric projection proofs square the positive-definite matrix weighted norm while varying the coordinate type, metric matrix, and displacement vector.
-- counterargument checked: not paper-local traceability because the statement exposes the standard finite `xᵀQx` positive-definite metric API; not a pure wrapper because the nonnegativity needed by `Real.sq_sqrt` is derived from the positive-definite contract including the zero vector case.
-- coverage search: queried "positive definite finite matrix quadratic form weighted norm square sqrt", "finite matrix positive definite quadratic form x transpose Q x positive", and LeanSearch "positive definite matrix quadratic form sqrt square equals quadratic form nonnegative"; hits were local AMSGrad declarations plus unrelated SOptLib Bregman/prox/finite weighted norm facts, while LeanSearch returned HTTP 500, so coverage is partial and no full duplicate was found.
-- minimal hypotheses: all already minimal for this concrete finite matrix API; symmetry is retained as part of the positive-definite matrix predicate even though the square proof only consumes positivity.

/-- Matrix-vector multiplication for a finite real matrix acting on a Euclidean
coordinate vector.

Layer: Model | Concept: finite positive-definite matrix metric
Proof: (definitional construction; finite coordinate sum for matrix-vector multiplication)
Source: finite-dimensional linear algebra over real coordinate spaces and Mathlib finite sums
Used in: adaptive-gradient weighted projection metrics formed from finite coordinate matrices
Book citation: book/ICLR2018/AMSGrad.json#/declarations
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad -/
noncomputable def finiteMatrixVec {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i : ι => ∑ j, Q i j * x j)

/-- The quadratic form `xᵀQx` for a finite real matrix.

Layer: Model | Concept: finite positive-definite matrix metric
Proof: (definitional construction; finite dot product of a vector with its matrix image)
Source: finite-dimensional quadratic forms over real coordinate spaces and Mathlib finite sums
Used in: adaptive-gradient projection proofs that compare matrix-weighted squared distances
Book citation: book/ICLR2018/AMSGrad.json#/declarations
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad -/
noncomputable def finiteMatrixQuadraticForm {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, x i * (finiteMatrixVec Q x i)

/-- Positive definiteness for a finite real matrix expressed through its
quadratic form on Euclidean coordinate vectors.

Layer: Model | Concept: finite positive-definite matrix metric
Proof: (definitional construction; symmetry plus strict positivity of the associated quadratic form)
Source: finite-dimensional real symmetric positive-definite matrices and quadratic forms
Used in: adaptive-gradient metric-domain checks for matrix-weighted projections
Book citation: book/ICLR2018/AMSGrad.json#/declarations
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad -/
def IsPositiveDefiniteFiniteMatrix {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) : Prop :=
  (∀ i j, Q i j = Q j i) ∧
    ∀ x : EuclideanSpace ℝ ι, x ≠ 0 -> 0 < finiteMatrixQuadraticForm Q x

/-- The weighted norm associated with a finite positive-definite matrix,
represented as `sqrt (xᵀQx)`.

Layer: Model | Concept: finite positive-definite matrix metric
Proof: (definitional construction; square root of the finite matrix quadratic form)
Source: finite-dimensional real matrix norms induced by positive-definite quadratic forms
Used in: adaptive-gradient projected updates written with `Q^(1/2)` weighted norms
Book citation: book/ICLR2018/AMSGrad.json#/declarations
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad -/
noncomputable def positiveDefiniteFiniteMatrixWeightedNorm {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (finiteMatrixQuadraticForm Q x)

/-- A finite positive-definite matrix weighted norm squares to its quadratic form.

For a finite symmetric positive-definite matrix `Q`, the expression
`sqrt (xᵀQx)` has square exactly `xᵀQx` for every coordinate vector `x`.

Layer: Model | Gap: Level 0 (finite positive-definite matrix weighted-norm square)
Proof: derive nonnegativity of the quadratic form by splitting on whether the vector is zero, then apply `Real.sq_sqrt`.
Source: finite-dimensional positive-definite quadratic forms and Mathlib real square-root arithmetic
Used in: adaptive-gradient projection arguments that convert weighted-norm minimization into quadratic-form comparison
Book citation: book/ICLR2018/AMSGrad.json#/declarations
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad -/
theorem isPositiveDefiniteFiniteMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Q : ι -> ι -> ℝ)
    (hQ : IsPositiveDefiniteFiniteMatrix Q)
    (x : EuclideanSpace ℝ ι) :
    positiveDefiniteFiniteMatrixWeightedNorm Q x ^ 2 =
      finiteMatrixQuadraticForm Q x := by
  have hnonneg : 0 ≤ finiteMatrixQuadraticForm Q x := by
    by_cases hx : x = 0
    · subst x
      simp [finiteMatrixQuadraticForm, finiteMatrixVec]
    · exact le_of_lt (hQ.2 x hx)
  simpa [positiveDefiniteFiniteMatrixWeightedNorm] using Real.sq_sqrt hnonneg

end SOptLib
