import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

open scoped BigOperators

namespace SOptLib

/-- A symmetric real bilinear form expands on an affine line as a quadratic
polynomial in the scalar parameter.

This is the bilinear algebra core used by finite matrix quadratic forms,
projection objectives, and line-search arguments: bilinearity expands the two
arguments, and symmetry combines the two cross terms. -/
theorem bilin_form_add_smul_self {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x)
    (a b : E) (t : ℝ) :
    B (a + t • b) (a + t • b) =
      B a a + 2 * t * B a b + t ^ 2 * B b b := by
  have hcomm : B b a = B a b := hB b a
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.smul_left, hcomm]
  ring

/-- A finite symmetric matrix quadratic form expands along a line segment as a
quadratic polynomial in the segment parameter.

For the Mathlib matrix bilinear form attached to a symmetric real finite
matrix `Q`, evaluating the quadratic form at `a + t • b` gives the constant
term at `a`, twice the symmetric cross term, and the quadratic term at `b`.

This finite-matrix specialization states the result directly for Mathlib's
`Matrix.toBilin'` API over an arbitrary finite index type; the reusable
bilinear-form theorem is `bilin_form_add_smul_self`. -/
theorem matrix_toBilin_add_smul_self_of_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (a b : ι → ℝ) (t : ℝ) :
    Matrix.toBilin' Q (a + t • b) (a + t • b) =
      Matrix.toBilin' Q a a + 2 * t * Matrix.toBilin' Q a b +
        t ^ 2 * Matrix.toBilin' Q b b := by
  have hB : ∀ x y : ι → ℝ,
      Matrix.toBilin' Q x y = Matrix.toBilin' Q y x := by
    intro x y
    rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, x i * Q i j * y j)
          = ∑ j, ∑ i, x i * Q i j * y j := by
              rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, y j * Q j i * x i := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [hQ i j]
              ring
      _ = ∑ i, ∑ j, y i * Q i j * x j := rfl
  have h := bilin_form_add_smul_self (Matrix.toBilin' Q) hB
    a b t
  simpa using h

end SOptLib
