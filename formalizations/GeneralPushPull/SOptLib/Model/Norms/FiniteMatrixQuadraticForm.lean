import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped BigOperators

namespace SOptLib

/-- Representation definitions retained for the already approved weighted projection API. -/
noncomputable def finiteMatrixVec {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i : ι => ∑ j, Q i j * x j)

noncomputable def finiteMatrixQuadraticForm {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, x i * (finiteMatrixVec Q x i)

noncomputable def positiveDefiniteFiniteMatrixWeightedNorm {ι : Type*} [Fintype ι]
    (Q : ι -> ι -> ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (finiteMatrixQuadraticForm Q x)

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-matrix dual quadratic form; orig was dualQuadraticForm
-- generality used: an arbitrary finite index type with decidable equality, a real square
--   matrix, and a vector in the associated Euclidean coordinate space; no positivity,
--   invertibility, probability, convexity, smoothness, or oracle assumptions
-- portable call pattern: adaptive-gradient, online mirror-descent, and matrix-metric proofs
--   evaluate a gradient in the inverse current metric while changing the finite index type,
--   vector, and metric and retaining total matrix-inverse semantics
-- counterargument checked: this is not the underlying quadratic form or a paper-only alias;
--   it exposes the recurring inverse-metric specialization that represents a squared dual
--   Mahalanobis size, with a companion theorem connecting its exact coordinate formula to the
--   existing quadratic form
-- coverage search: symbol searches for "finite matrix inverse quadratic form dual Mahalanobis
--   norm square", "quadratic form inverse matrix vector", and "dual norm squared inverse
--   metric" found only SOptLib.finiteMatrixQuadraticForm and paper-local Shampoo declarations;
--   Mathlib semantic search found Matrix.toQuadraticMap' and Matrix.posDef_inv_iff, neither of
--   which names the inverse-metric specialization; coverage is partial, not duplicative
-- minimal hypotheses: Fintype is required by the finite quadratic-form sums and matrix inverse;
--   DecidableEq is required by Mathlib's total matrix inverse; all assumptions are minimal

/-- The inverse-metric quadratic form of a vector in a finite real coordinate space.

This is the squared dual Mahalanobis quantity associated with a matrix metric. Matrix inversion
uses Mathlib's total inverse, so the definition remains meaningful without a nonsingularity or
positive-definiteness hypothesis.

Layer: Model | Concept: finite-dimensional inverse-metric dual quadratic form
Proof: specialize the existing finite-matrix quadratic form to the total matrix inverse of the metric
Source: Mathlib finite matrices and total matrix inversion, together with SOptLib finite-matrix quadratic forms
Used in: adaptive-gradient and online mirror-descent regret decompositions that measure each gradient in the inverse current preconditioner
Book citation: book/research/Source.json#/key_lemmas/0/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
noncomputable def finiteMatrixDualQuadraticForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ j, g i * H⁻¹ i j * g j

/-- The coordinate formula for the finite-matrix dual quadratic form.

Layer: Model | Gap: Level 0 (inverse-metric dual quadratic-form coordinate specification)
Proof: unfold the specialized quadratic form and reassociate the coordinate products.
Source: Mathlib finite sums, finite matrices, and total matrix inversion
Used in: adaptive-gradient and online mirror-descent proofs that unfold named squared dual metric size into coordinatewise inverse-matrix algebra
Book citation: book/research/Source.json#/key_lemmas/0/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
@[simp]
theorem finiteMatrixDualQuadraticForm_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) :
    finiteMatrixDualQuadraticForm H g = ∑ i, ∑ j, g i * H⁻¹ i j * g j :=
  rfl

/-- The finite-matrix dual quadratic form is the ordinary quadratic form for the inverse metric.

Layer: Model | Gap: Level 0 (dual quadratic form to inverse-metric quadratic form bridge)
Proof: by the defining specialization of `finiteMatrixDualQuadraticForm`.
Source: SOptLib finite-matrix quadratic forms, Mathlib finite-sum distributivity, and total matrix inversion
Used in: matrix-metric optimization proofs that switch between the named squared dual Mahalanobis quantity and generic quadratic-form API
Book citation: book/research/Source.json#/key_lemmas/0/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
theorem finiteMatrixDualQuadraticForm_eq_finiteMatrixQuadraticForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) :
    finiteMatrixDualQuadraticForm H g =
      finiteMatrixQuadraticForm (H⁻¹ : Matrix ι ι ℝ) g :=
  by
    simp [finiteMatrixDualQuadraticForm, finiteMatrixQuadraticForm, finiteMatrixVec,
      Finset.mul_sum, mul_assoc]

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: inverse-metric quadratic form as a trace against a rank-one matrix;
--   orig was dualQuadraticForm_eq_trace_vectorOuter_mul_inv
-- generality used: an arbitrary finite index type with decidable equality, a real vector,
--   and a real square matrix; no symmetry, positivity, probability, convexity, smoothness,
--   oracle, or algorithm-state assumptions
-- portable call pattern: adaptive-metric, covariance-potential, and online mirror-descent
--   proofs rewrite inverse-metric gradient energy as a trace pairing while the finite index
--   type, gradient, and metric vary
-- counterargument checked: this is not a paper-local traceability wrapper; Mathlib's
--   trace_vecMulVec omits the multiplied inverse metric, while this theorem connects the
--   staged dual quadratic form to the trace representation needed by matrix potentials
-- coverage search: searches for "finite matrix dual quadratic form equals trace vector outer
--   product times inverse positive definite" and "trace vecMulVec matrix multiplication
--   quadratic form" found no SOptLib declaration; Mathlib semantic search found
--   Matrix.trace_vecMulVec and Matrix.toBilin'_apply', which cover only component identities
-- minimal hypotheses: Fintype supports the sums and DecidableEq supports matrix inversion;
--   no matrix regularity hypothesis is needed because the finite summation indices can be swapped

/-- The dual quadratic form for a finite matrix is the trace of the vector's
rank-one outer product multiplied by the inverse matrix.

Layer: Model | Gap: Level 1 (inverse-metric quadratic energy to rank-one trace representation)
Proof: expand the finite sums, swap the two summation indices, and normalize commutative products.
Source: Mathlib finite-matrix trace, outer-product multiplication, and finite-sum commutation
Used in: adaptive-metric and covariance-potential arguments that turn gradient dual energy into a trace objective for positive-definite preconditioners
Book citation: book/research/Source.json#/key_lemmas/1/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, follow-the-leader/be-the-leader potential step -/
theorem finiteMatrixDualQuadraticForm_eq_trace_vecMulVec_mul_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (K : Matrix ι ι ℝ) :
    finiteMatrixDualQuadraticForm K (WithLp.toLp 2 g) =
      Matrix.trace (Matrix.vecMulVec g g * K⁻¹) := by
  classical
  unfold finiteMatrixDualQuadraticForm Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec, Matrix.of_apply]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_comm]

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: nonnegativity of a finite-matrix quadratic form under positive
--   semidefiniteness; orig was quadraticForm_nonneg_of_posSemidef
-- generality used: an arbitrary finite index type, a vector in the associated real
--   Euclidean coordinate space, and a real square matrix; no decidable equality,
--   finite-dimensional-space, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: adaptive-metric and preconditioned-gradient proofs certify that
--   a terminal potential or dual energy is nonnegative while changing the finite index
--   type, vector, and positive-semidefinite metric
-- counterargument checked: Mathlib directly proves nonnegativity of its dot-product/matrix-
--   vector representation, but this is not a pure rename because it supplies the missing API
--   theorem for SOptLib's separately named finite-matrix quadratic form
-- coverage search: searches for "finite matrix quadratic form nonnegative positive
--   semidefinite" and "quadratic form nonnegative of positive semidefinite matrix" found
--   SOptLib.finiteMatrixQuadraticForm and Mathlib's
--   Matrix.PosSemidef.dotProduct_mulVec_nonneg, but no theorem connecting them; coverage is
--   partial, and the Mathlib result is the proof engine
-- minimal hypotheses: Fintype is required by the finite sums and by Mathlib's matrix
--   positive-semidefinite API; all other structure is fixed by the real coordinate model

/-- A positive-semidefinite finite real matrix has a nonnegative quadratic form.

Layer: Model | Gap: Level 0 (named finite-matrix quadratic-form nonnegativity)
Proof: unfold the named quadratic form and apply `Matrix.PosSemidef.dotProduct_mulVec_nonneg` to its dot-product representation.
Source: Mathlib positive-semidefinite matrices in `Mathlib.LinearAlgebra.Matrix.PosDef` and SOptLib finite-matrix quadratic forms
Used in: adaptive-metric and preconditioned-gradient potential arguments that discard a nonnegative terminal quadratic energy
Book citation: book/research/Source.json#/key_lemmas/0/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
theorem finiteMatrixQuadraticForm_nonneg_of_posSemidef
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    0 ≤ finiteMatrixQuadraticForm M x := by
  have hdot := hM.dotProduct_mulVec_nonneg x
  simpa [finiteMatrixQuadraticForm, finiteMatrixVec, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc] using hdot

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: subtraction linearity of a finite-matrix quadratic form in its
--   matrix argument; orig was `quadraticForm_sub_matrix`
-- generality used: an arbitrary finite index type, a vector in the associated
--   real Euclidean coordinate space, and two real square matrices; no decidable
--   equality, finite-dimensional-space, symmetry, positivity, measure,
--   convexity, smoothness, or oracle assumptions are used
-- portable call pattern: adaptive-metric, mirror-descent, and preconditioned
--   proofs split a changing-metric quadratic potential into its new-metric and
--   old-metric terms while the finite index type, vector, and metrics vary
-- counterargument checked: Mathlib's generic
--   `LinearMap.BilinMap.toQuadraticMap_sub` expresses the underlying algebra,
--   but it does not provide the API theorem for SOptLib's named finite-matrix
--   quadratic form and its matrix conversion requires decidable equality
-- coverage search: searches for "finite matrix quadratic form subtraction
--   equality matrix argument" and "quadratic form is additive in the bilinear
--   form or matrix" found the unrelated vector-difference expansion
--   `finiteMatrixQuadraticForm_sub_expansion` and Mathlib's generic
--   `LinearMap.BilinMap.toQuadraticMap_sub`; neither has this statement at its
--   minimal typeclass level, so coverage is partial
-- minimal hypotheses: `Fintype` is required by the defining finite sums; all
--   other structure is fixed by the real coordinate model

/-- A finite real matrix quadratic form preserves subtraction in its matrix
argument.

Layer: Model | Gap: Level 0 (named finite-matrix quadratic-form subtraction linearity)
Proof: unfold the named matrix-vector product and quadratic form, distribute multiplication over matrix-entry subtraction, and distribute both finite sums over subtraction.
Source: Mathlib finite sums and pointwise additive structure on matrices, together with SOptLib finite-matrix quadratic forms
Used in: changing-metric mirror-descent and preconditioned-gradient potential arguments that split a quadratic energy for a metric increment into new- and old-metric energies
Book citation: book/research/Source.json#/key_lemmas/0/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
theorem finiteMatrixQuadraticForm_sub_matrix
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (A B : Matrix ι ι ℝ) :
    finiteMatrixQuadraticForm (A - B) x =
      finiteMatrixQuadraticForm A x - finiteMatrixQuadraticForm B x := by
  classical
  unfold finiteMatrixQuadraticForm finiteMatrixVec
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simp
  ring

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: transport of a trace-inverse prefix minimizer inequality to the equivalent
--   dual-quadratic prefix objective; orig was prefix_minimizer_inequality_generic
-- generality used: an arbitrary finite coordinate type with decidable equality, a finite
--   vector sequence, one prefix outer-product matrix, two candidate matrices, an arbitrary
--   scalar potential, and a pointwise trace-objective inequality
-- portable call pattern: follow-the-leader metric proofs reuse the same minimizer transport
--   while changing the coordinate type, cost vectors, prefix covariance, candidate metrics,
--   potential, and prefix endpoint
-- counterargument checked: this is not paper-local traceability or a pure rename; it packages
--   two nontrivial prefix trace/dual-quadratic conversions around a minimizer comparison, while
--   avoiding an abstract-function equality wrapper by retaining the concrete matrix objectives
-- coverage search: symbol searches for `prefix dual quadratic objective inequality trace inverse
--   minimizer`, `trace inverse objective minimizer implies sum dual quadratic forms inequality`,
--   and `objective inequality transport equality prefix outer sum inverse matrix` found the
--   staged equality bridge `trace_prefix_outer_sum_mul_inv_add_eq_sum_dualQuadraticForm_add`
--   but no inequality transport; Mathlib semantic search found `Matrix.trace_sum` and
--   trace-extensionality lemmas only, so coverage is partial and this statement is differentiated
-- minimal hypotheses: the prefix formula and minimizer comparison are required only at the
--   selected endpoint; positivity, invertibility, a full matrix trajectory, and global minimizer
--   hypotheses are unnecessary because Mathlib matrix inverse is total

/-- A minimizer comparison for a trace-inverse prefix objective gives the corresponding
comparison for the equivalent sum of dual quadratic forms.

Layer: Glue | Gap: Level 1 (prefix trace-objective minimizer transport)
Proof: rewrite both sides with the prefix outer-product trace identity, then apply the supplied pointwise trace-objective comparison.
Source: Mathlib finite matrices, total matrix inversion, and trace linearity, together with SOptLib finite-matrix dual quadratic forms
Used in: follow-the-leader adaptive-metric proofs that turn a trace-inverse minimizer property at a selected covariance prefix into the dual-cost inequality used by be-the-leader induction
Book citation: book/research/Source.json#/key_lemmas/1/proof/4
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, follow-the-leader/be-the-leader potential step -/
theorem prefix_dualQuadratic_objective_le_of_trace_inverse_minimizer
    {T : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) (A H K : Matrix ι ι ℝ)
    (Phi : Matrix ι ι ℝ → ℝ) (N : Fin (T + 1))
    (hA : A = ∑ s : Fin T,
      if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0)
    (hmin : Matrix.trace (A * H⁻¹) + Phi H ≤
      Matrix.trace (A * K⁻¹) + Phi K) :
    (∑ s : Fin T, if s.1 < N.1 then
        finiteMatrixDualQuadraticForm H (WithLp.toLp 2 (g s)) else 0) + Phi H ≤
      (∑ s : Fin T, if s.1 < N.1 then
        finiteMatrixDualQuadraticForm K (WithLp.toLp 2 (g s)) else 0) + Phi K := by
  classical
  have htrace (Q : Matrix ι ι ℝ) :
      Matrix.trace (A * Q⁻¹) =
        ∑ s : Fin T, if s.1 < N.1 then
          finiteMatrixDualQuadraticForm Q (WithLp.toLp 2 (g s)) else 0 := by
    calc
      Matrix.trace (A * Q⁻¹) =
          Matrix.trace (((∑ s : Fin T,
            if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0) :
              Matrix ι ι ℝ) * Q⁻¹) := by rw [hA]
      _ = Matrix.trace (∑ s : Fin T,
          (if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0) * Q⁻¹) := by
            congr
            simp [Finset.sum_mul]
      _ = ∑ s : Fin T,
          Matrix.trace ((if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0) * Q⁻¹) := by
            rw [Matrix.trace_sum]
      _ = ∑ s : Fin T, if s.1 < N.1 then
          finiteMatrixDualQuadraticForm Q (WithLp.toLp 2 (g s)) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro s _hs
            by_cases hlt : s.1 < N.1
            · rw [if_pos hlt, if_pos hlt]
              exact (finiteMatrixDualQuadraticForm_eq_trace_vecMulVec_mul_inv (g s) Q).symm
            · simp [hlt]
  calc
    (∑ s : Fin T, if s.1 < N.1 then
        finiteMatrixDualQuadraticForm H (WithLp.toLp 2 (g s)) else 0) + Phi H =
        Matrix.trace (A * H⁻¹) + Phi H := by rw [htrace H]
    _ ≤ Matrix.trace (A * K⁻¹) + Phi K := hmin
    _ = (∑ s : Fin T, if s.1 < N.1 then
        finiteMatrixDualQuadraticForm K (WithLp.toLp 2 (g s)) else 0) + Phi K := by
          rw [htrace K]

end SOptLib
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: trace of a prefix outer-product sum against an inverse matrix as a sum of
--   dual quadratic forms; orig was prefix_objective_eq_genericTrace_objective
-- generality used: an arbitrary finite coordinate type with decidable equality, a finite
--   gradient sequence, a matrix satisfying the prefix outer-product formula at the selected
--   endpoint, an arbitrary common scalar addend, and Mathlib's total matrix inverse
-- portable call pattern: covariance-potential and adaptive-preconditioner proofs rewrite a
--   prefix trace objective as accumulated dual gradient costs while changing the coordinate
--   type, gradient sequence, prefix covariance, common addend, endpoint, and candidate metric
-- counterargument checked: the unchanged addend is simple congruence, but the theorem is
--   not merely a caller-side wrapper because it packages matrix multiplication over a finite
--   prefix sum, trace linearity, and the rank-one trace/dual-quadratic bridge in one reusable
--   objective conversion
-- coverage search: symbol searches for `trace prefix sum outer product inverse equals sum dual
--   quadratic form` and `matrix trace sum multiplication equals sum trace finite` found the
--   per-vector SOptLib bridge `finiteMatrixDualQuadraticForm_eq_trace_vecMulVec_mul_inv` and
--   Mathlib's `Matrix.trace_sum`; neither covers the prefix aggregation, so coverage is partial
-- minimal hypotheses: Fintype supports trace and finite sums and DecidableEq supports total
--   matrix inversion; positive definiteness is removed because the proof never uses it

/-- A trace objective for a prefix sum of vector outer products equals the corresponding
sum of inverse-metric dual quadratic forms, with any common scalar added.

Layer: Glue | Gap: Level 1 (prefix rank-one trace objective aggregation)
Proof: substitute the prefix outer-product formula, distribute right multiplication and trace over the finite sum, then apply the rank-one trace representation of each dual quadratic form.
Source: Mathlib finite-matrix multiplication and trace linearity, together with SOptLib finite-matrix dual quadratic forms
Used in: follow-the-leader covariance-potential arguments that convert each candidate preconditioner's prefix trace objective into accumulated adaptive dual costs
Book citation: book/research/Source.json#/key_lemmas/1/statement_math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, follow-the-leader/be-the-leader potential step -/
theorem trace_prefix_outer_sum_mul_inv_add_eq_sum_dualQuadraticForm_add
    {T : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) (A : Matrix ι ι ℝ)
    (N : Fin (T + 1))
    (hA : A = ∑ s : Fin T,
      if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0)
    (K : Matrix ι ι ℝ) (c : ℝ) :
    Matrix.trace (A * K⁻¹) + c =
      (∑ s : Fin T, if s.1 < N.1 then
        finiteMatrixDualQuadraticForm K (WithLp.toLp 2 (g s)) else 0) + c := by
  classical
  have htrace :
      Matrix.trace (A * K⁻¹) =
        ∑ s : Fin T, if s.1 < N.1 then
          finiteMatrixDualQuadraticForm K (WithLp.toLp 2 (g s)) else 0 := by
    calc
      Matrix.trace (A * K⁻¹) =
          Matrix.trace (((∑ s : Fin T,
            if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0) :
              Matrix ι ι ℝ) * K⁻¹) := by
            rw [hA]
      _ = Matrix.trace (∑ s : Fin T,
          (if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0) * K⁻¹) := by
            congr
            simp [Finset.sum_mul]
      _ = ∑ s : Fin T,
          Matrix.trace ((if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0) * K⁻¹) := by
            rw [Matrix.trace_sum]
      _ = ∑ s : Fin T, if s.1 < N.1 then
          finiteMatrixDualQuadraticForm K (WithLp.toLp 2 (g s)) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro s _hs
            by_cases hlt : s.1 < N.1
            · rw [if_pos hlt, if_pos hlt]
              exact (finiteMatrixDualQuadraticForm_eq_trace_vecMulVec_mul_inv (g s) K).symm
            · simp [hlt]
  rw [htrace]

end SOptLib
