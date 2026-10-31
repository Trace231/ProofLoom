import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic
import SOptLib.Model.Norms.finiteMatrixQuadraticForm_segment_expansion
namespace SOptLib

/-- Two one-sided projection variational inequalities imply contraction of a
symmetric nonnegative quadratic form.

The result is the algebraic nonexpansiveness step for metric projections:
the two projection points may be supplied by any construction that proves the
displayed variational inequalities, independently of how those inequalities
were obtained. -/
theorem quadratic_distance_contraction_of_projection_variational
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E)
    (hB_symm : ∀ x y, B x y = B y x)
    (hB_nonneg : ∀ x, 0 ≤ B x x)
    (z₁ z₂ u₁ u₂ : E)
    (hvi₁ : 0 ≤ B (u₁ - z₁) (u₂ - u₁))
    (hvi₂ : 0 ≤ B (u₂ - z₂) (u₁ - u₂)) :
    B (u₁ - u₂) (u₁ - u₂) ≤ B (z₁ - z₂) (z₁ - z₂) := by
  let p : E := u₁ - u₂
  let q : E := z₁ - z₂
  let a : E := u₁ - z₁
  let b : E := u₂ - z₂
  have hdir₁ : u₂ - u₁ = -p := by
    dsimp [p]
    abel
  have hvi₁p : B a p ≤ 0 := by
    have hneg : 0 ≤ -B a p := by
      rw [← LinearMap.BilinForm.neg_right (B₁ := B)]
      simpa [a, p] using hvi₁
    linarith
  have hvi₂p : 0 ≤ B b p := by
    simpa [b, p] using hvi₂
  have hdecomp : q = p - a + b := by
    dsimp [p, q, a, b]
    abel
  have hBdecomp :
      B q p = B p p - B a p + B b p := by
    rw [hdecomp, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.sub_left]
  have hleB : B p p ≤ B q p := by
    nlinarith [hvi₁p, hvi₂p, hBdecomp]
  have hnonneg : 0 ≤ B (q - p) (q - p) :=
    hB_nonneg (q - p)
  have hexp :
      B (q - p) (q - p) = B q q - 2 * B q p + B p p := by
    have h := bilin_form_add_smul_self B hB_symm q p (-1)
    simpa [sub_eq_add_neg, pow_two] using h
  have hupper : B q p ≤ (B q q + B p p) / 2 := by
    nlinarith [hexp, hnonneg]
  have hpq : B p p ≤ B q q := by
    nlinarith [hleB, hupper]
  simpa [p, q] using hpq

end SOptLib
