import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-!
The single-sided Bregman inequality from cocoercivity and a convex gradient image.

This is the bridge in Wachsmuth--Wachsmuth (2022), Lemma 3.3.  We use repeated
midpoint subdivision in gradient space instead of uniform n-point subdivision.
No differentiability or open-domain hypothesis is hidden in this algebraic lemma:
its callers must provide support inequalities and cocoercivity for the same field.
-/

open scoped InnerProductSpace
open Filter Topology

namespace SOptLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bregman_gap_of_cocoercive_convex_gradient_image
    (f : E → ℝ) (G : E → E) (U : Set E) (L : ℝ)
    (hL : 0 < L)
    (hsupport : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ f x - f y - ⟪G y, x - y⟫_ℝ)
    (hcoco : ∀ x ∈ U, ∀ y ∈ U,
      ‖G x - G y‖ ^ 2 ≤ L * ⟪G x - G y, x - y⟫_ℝ)
    (himage : Convex ℝ (G '' U))
    (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U) :
    ‖G x - G y‖ ^ 2 ≤ 2 * L * (f x - f y - ⟪G y, x - y⟫_ℝ) := by
  have happrox : ∀ n : ℕ, ∀ a ∈ U, ∀ b ∈ U,
      ((1 - (1 / 2 : ℝ) ^ n) / 2) * ‖G a - G b‖ ^ 2 ≤
        L * (f a - f b - ⟪G b, a - b⟫_ℝ) := by
    intro n
    induction n with
    | zero =>
        intro a ha b hb
        simpa using mul_nonneg hL.le (hsupport a ha b hb)
    | succ n ih =>
        intro a ha b hb
        obtain ⟨z, hz, hgz⟩ := himage
          (Set.mem_image_of_mem G ha) (Set.mem_image_of_mem G hb)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
        have haz : G a - G z = (1 / 2 : ℝ) • (G a - G b) := by
          rw [hgz]
          module
        have hzb : G z - G b = (1 / 2 : ℝ) • (G a - G b) := by
          rw [hgz]
          module
        have hnaz : ‖G a - G z‖ ^ 2 = (1 / 4 : ℝ) * ‖G a - G b‖ ^ 2 := by
          rw [haz, norm_smul, Real.norm_eq_abs]
          norm_num
          ring
        have hnzb : ‖G z - G b‖ ^ 2 = (1 / 4 : ℝ) * ‖G a - G b‖ ^ 2 := by
          rw [hzb, norm_smul, Real.norm_eq_abs]
          norm_num
          ring
        have hcross := hcoco a ha z hz
        have heq : G a - G z = G z - G b := haz.trans hzb.symm
        rw [hnaz, heq] at hcross
        have h1 := ih a ha z hz
        have h2 := ih z hz b hb
        rw [hnaz] at h1
        rw [hnzb] at h2
        have hgap :
            f a - f b - ⟪G b, a - b⟫_ℝ =
              (f a - f z - ⟪G z, a - z⟫_ℝ) +
              (f z - f b - ⟪G b, z - b⟫_ℝ) +
              ⟪G z - G b, a - z⟫_ℝ := by
          simp only [inner_sub_left, inner_sub_right]
          ring
        rw [hgap, pow_succ]
        nlinarith
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto
      (fun n : ℕ => ((1 - (1 / 2 : ℝ) ^ n) / 2) * ‖G x - G y‖ ^ 2)
      atTop (𝓝 ((1 / 2 : ℝ) * ‖G x - G y‖ ^ 2)) := by
    convert ((tendsto_const_nhds.sub hp).div_const 2).mul_const
      (‖G x - G y‖ ^ 2) using 1 <;> norm_num
  have hlim := le_of_tendsto ht (Filter.Eventually.of_forall fun n => happrox n x hx y hy)
  linarith

end SOptLib

#print axioms SOptLib.bregman_gap_of_cocoercive_convex_gradient_image
