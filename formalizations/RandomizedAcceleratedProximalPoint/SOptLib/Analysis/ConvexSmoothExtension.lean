import SOptLib.Glue.Calculus
import SOptLib.Model.Norms
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Convex smooth extensions and their proved one-sided Bregman estimates.
The extension agrees with the carrier's values and selected intrinsic gradient.
Smoothness is expressed by its global quadratic upper model in the original norm.
This is an explicit additional mathematical condition, not a source assumption.
-/

open scoped InnerProductSpace
namespace SOptLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure ConvexSmoothExtensionOn (X : Set E)
    (v : {x : E // x ∈ X} → ℝ) (g : {x : E // x ∈ X} → E)
    (p : Seminorm ℝ E) (L : ℝ) where
  value : E → ℝ
  grad : E → E
  convex : ConvexOn ℝ Set.univ value
  hasGradient : ∀ x, HasGradientAt value (grad x) x
  value_eq : ∀ x : {x : E // x ∈ X}, value x.1 = v x
  grad_eq : ∀ x : {x : E // x ∈ X}, grad x.1 = g x
  smooth_upper : ∀ x y,
    value x ≤ value y + ⟪grad y, x - y⟫_ℝ + (L / 2) * p (x - y) ^ 2

namespace ConvexSmoothExtensionOn
variable {X : Set E} {v : {x : E // x ∈ X} → ℝ}
  {g : {x : E // x ∈ X} → E} {p : Seminorm ℝ E} {L : ℝ}

theorem support (ext : ConvexSmoothExtensionOn X v g p L) (x y : E) :
    0 ≤ ext.value x - ext.value y - ⟪ext.grad y, x - y⟫_ℝ := by
  have h := ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
    (X := Set.univ) (f := ext.value) convex_univ ext.convex
    (Set.mem_univ y) (Set.mem_univ x)
    (hasGradientWithinAt_univ.mpr (ext.hasGradient y))
  linarith
end ConvexSmoothExtensionOn

theorem global_bregman_gap_of_support_and_smooth_upper
    {psi : E → ℝ} {p : E → E} {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ x y : E, 0 ≤ psi x - psi y - inner ℝ (p y) (x - y))
    (hupper :
      ∀ x y : E,
        psi x - psi y - inner ℝ (p y) (x - y) ≤ (L / 2) * ‖x - y‖ ^ 2)
    (u v : E) :
    (1 / (2 * L)) * ‖p u - p v‖ ^ 2 ≤
      psi u - psi v - inner ℝ (p v) (u - v) := by
  let r : E := p u - p v
  let z : E := u - (1 / L) • r
  have hstep :
      psi v + inner ℝ (p v) (z - v) ≤
        psi u + inner ℝ (p u) (z - u) + (L / 2) * ‖z - u‖ ^ 2 := by
    have hsupport_zv := hsupport z v
    have hupper_zu := hupper z u
    linarith only [hsupport_zv, hupper_zu]
  have hzinv_pos : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have hnorm_zu :
      ‖z - u‖ ^ 2 = (1 / L) ^ 2 * ‖r‖ ^ 2 := by
    have hzu : z - u = -((1 / L) • r) := by
      simp [z, sub_eq_add_neg, add_assoc]
    rw [hzu, norm_neg, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos hzinv_pos]
    ring
  have hmain :
      psi v + inner ℝ (p v) (u - v) + (1 / L) * ‖r‖ ^ 2 ≤
        psi u + (L / 2) * ((1 / L) ^ 2 * ‖r‖ ^ 2) := by
    have hzv : z - v = (u - v) - (1 / L) • r := by
      simp [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hzu : z - u = -((1 / L) • r) := by
      simp [z, sub_eq_add_neg, add_assoc]
    have hleft :
        inner ℝ (p v) (z - v) =
          inner ℝ (p v) (u - v) - (1 / L) * inner ℝ (p v) r := by
      rw [hzv, inner_sub_right, inner_smul_right]
    have hright :
        inner ℝ (p u) (z - u) = - (1 / L) * inner ℝ (p u) r := by
      rw [hzu, inner_neg_right, inner_smul_right]
      ring
    have hrnorm :
        inner ℝ (p u) r - inner ℝ (p v) r = ‖r‖ ^ 2 := by
      have hpu : p u = r + p v := by
        simp [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpu, inner_add_left, real_inner_self_eq_norm_sq]
      ring
    have hrnorm_scaled :
        (1 / L) * inner ℝ (p u) r - (1 / L) * inner ℝ (p v) r =
          (1 / L) * ‖r‖ ^ 2 := by
      calc
        (1 / L) * inner ℝ (p u) r - (1 / L) * inner ℝ (p v) r =
            (1 / L) * (inner ℝ (p u) r - inner ℝ (p v) r) := by ring
        _ = (1 / L) * ‖r‖ ^ 2 := by rw [hrnorm]
    have hstep' := hstep
    rw [hleft, hright, hnorm_zu] at hstep'
    linarith only [hstep', hrnorm_scaled]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hcoef :
      (L / 2) * ((1 / L) ^ 2 * ‖r‖ ^ 2) =
        (1 / (2 * L)) * ‖r‖ ^ 2 := by
    field_simp [hL_ne]
  rw [hcoef] at hmain
  have hcoef_one :
      (1 / L) * ‖r‖ ^ 2 =
        2 * ((1 / (2 * L)) * ‖r‖ ^ 2) := by
    field_simp [hL_ne]
  rw [hcoef_one] at hmain
  change (1 / (2 * L)) * ‖r‖ ^ 2 ≤
    psi u - psi v - inner ℝ (p v) (u - v)
  linarith only [hmain]

theorem global_unit_direction_bregman_gap
    (F : E → ℝ) (G : E → E) (p : Seminorm ℝ E) (L : ℝ)
    (hLpos : 0 < L)
    (hsupport : ∀ x y, 0 ≤ F x - F y - ⟪G y, x - y⟫_ℝ)
    (hupper : ∀ x y, F x ≤ F y + ⟪G y, x - y⟫_ℝ + (L / 2) * p (x - y) ^ 2)
    (x z d : E) (hpd : p d ≤ 1) :
    |⟪G x - G z, d⟫_ℝ| ^ 2 ≤
      2 * L * (F x - F z - ⟪G z, x - z⟫_ℝ) := by
  let a : ℝ := ⟪G x - G z, d⟫_ℝ
  let y : E := x - (a / L) • d
  have hsupport_yz := hsupport y z
  have hupper_xy := hupper y x
  have hy_sub : y - x = - (a / L) • d := by
    simp [y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hprimal_yx :
      p (y - x) ≤ |a| / L := by
    have hnorm_nonneg : 0 ≤ ‖a / L‖ := norm_nonneg _
    have hscale :
        p (y - x) = ‖a / L‖ * p d := by
      rw [hy_sub]
      simp [map_smul_eq_mul]
    have hmul : ‖a / L‖ * p d ≤ ‖a / L‖ * 1 :=
      mul_le_mul_of_nonneg_left hpd hnorm_nonneg
    calc
      p (y - x) = ‖a / L‖ * p d := hscale
      _ ≤ ‖a / L‖ * 1 := hmul
      _ = |a| / L := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hLpos]
        ring
  have hprimal_sq :
      p (y - x) ^ 2 ≤ (|a| / L) ^ 2 := by
    exact (sq_le_sq₀ (apply_nonneg p (y - x))
      (div_nonneg (abs_nonneg a) hLpos.le)).2 hprimal_yx
  have hinner_yx :
      ⟪G x - G z, y - x⟫_ℝ = - a ^ 2 / L := by
    rw [hy_sub]
    simp [a, inner_smul_right]
    ring
  have hphi_upper :
      F y - F z - ⟪G z, y - z⟫_ℝ ≤
        (F x - F z - ⟪G z, x - z⟫_ℝ) -
          a ^ 2 / L +
            (L / 2) * p (y - x) ^ 2 := by
    calc
      F y - F z - ⟪G z, y - z⟫_ℝ
          ≤ (F x + ⟪G x, y - x⟫_ℝ +
              (L / 2) * p (y - x) ^ 2) -
              F z - ⟪G z, y - z⟫_ℝ := by
            linarith [hupper_xy]
      _ = (F x - F z - ⟪G z, x - z⟫_ℝ) +
            ⟪G x - G z, y - x⟫_ℝ +
              (L / 2) * p (y - x) ^ 2 := by
            have hyz : y - z = (x - z) + (y - x) := by abel
            rw [hyz, inner_add_right, inner_sub_left]
            ring
      _ = (F x - F z - ⟪G z, x - z⟫_ℝ) -
            a ^ 2 / L +
              (L / 2) * p (y - x) ^ 2 := by
            rw [hinner_yx]
            ring
  have hquad_le :
      (L / 2) * p (y - x) ^ 2 ≤
        a ^ 2 / (2 * L) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hprimal_sq (by nlinarith [hLpos] :
        0 ≤ L / 2)
    have habs_sq : |a| ^ 2 = a ^ 2 := by exact sq_abs a
    calc
      (L / 2) * p (y - x) ^ 2
          ≤ (L / 2) * (|a| / L) ^ 2 := hmul
      _ = a ^ 2 / (2 * L) := by
        rw [div_pow, habs_sq]
        field_simp [hLpos.ne']
  have hgap_lower :
      a ^ 2 / (2 * L) ≤
        F x - F z - ⟪G z, x - z⟫_ℝ := by
    let gap : ℝ := F x - F z - ⟪G z, x - z⟫_ℝ
    let phi_y : ℝ := F y - F z - ⟪G z, y - z⟫_ℝ
    have hphi_le2 : phi_y ≤ gap - a ^ 2 / L + a ^ 2 / (2 * L) := by
      dsimp [phi_y, gap]
      nlinarith [hphi_upper, hquad_le]
    have hnonneg : 0 ≤ gap - a ^ 2 / L + a ^ 2 / (2 * L) := by
      exact le_trans (by simpa [phi_y] using hsupport_yz) hphi_le2
    have hrewrite :
        gap - a ^ 2 / L + a ^ 2 / (2 * L) =
          gap - a ^ 2 / (2 * L) := by
      field_simp [hLpos.ne']
      ring
    have : 0 ≤ gap - a ^ 2 / (2 * L) := by
      simpa [hrewrite] using hnonneg
    dsimp [gap] at this ⊢
    linarith
  have hmul_nonneg : 0 ≤ 2 * L := by nlinarith
  have hscaled :
      a ^ 2 ≤
        2 * L *
          (F x - F z - ⟪G z, x - z⟫_ℝ) := by
    have h := mul_le_mul_of_nonneg_left hgap_lower hmul_nonneg
    field_simp [hLpos.ne'] at h
    nlinarith
  simpa [a, sq_abs] using hscaled

namespace ConvexSmoothExtensionOn
variable {X : Set E} {v : {x : E // x ∈ X} → ℝ}
  {g : {x : E // x ∈ X} → E} {L : ℝ}

theorem norm_gap (ext : ConvexSmoothExtensionOn X v g (normSeminorm ℝ E) L)
    (hL : 0 < L) (x y : {x : E // x ∈ X}) :
    (1 / (2 * L)) * ‖g x - g y‖ ^ 2 ≤ v x - v y - ⟪g y, x.1 - y.1⟫_ℝ := by
  have h := global_bregman_gap_of_support_and_smooth_upper
    (psi := ext.value) (p := ext.grad) hL ext.support
    (fun a b => by
      have hu := ext.smooth_upper a b
      change ext.value a ≤ ext.value b + ⟪ext.grad b, a - b⟫_ℝ +
        (L / 2) * ‖a - b‖ ^ 2 at hu
      linarith) x.1 y.1
  simpa only [ext.value_eq, ext.grad_eq] using h

theorem affineDual_gap {p : Seminorm ℝ E}
    (ext : ConvexSmoothExtensionOn X v g p L) (hL : 0 < L)
    (x y : {x : E // x ∈ X}) :
    (1 / (2 * L)) * affineDirectionDualNorm X p (g x - g y) ^ 2 ≤
      v x - v y - ⟪g y, x.1 - y.1⟫_ℝ := by
  let C := 2 * L * (v x - v y - ⟪g y, x.1 - y.1⟫_ℝ)
  have hgap : 0 ≤ v x - v y - ⟪g y, x.1 - y.1⟫_ℝ := by
    simpa only [ext.value_eq, ext.grad_eq] using ext.support x.1 y.1
  have hC : 0 ≤ C := mul_nonneg (by positivity) hgap
  have hunit : ∀ d : E, p d ≤ 1 → |⟪g x - g y, d⟫_ℝ| ^ 2 ≤ C := by
    intro d hd
    simpa only [ext.value_eq, ext.grad_eq] using
      global_unit_direction_bregman_gap ext.value ext.grad p L hL ext.support
        ext.smooth_upper x.1 y.1 d hd
  let A : Set ℝ := {r : ℝ | ∃ d : E,
    d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧ r = |⟪g x - g y, d⟫_ℝ|}
  have hA : A.Nonempty := by
    refine ⟨0, 0, (affineSpan ℝ X).direction.zero_mem, ?_, ?_⟩ <;> simp
  have hbound : ∀ r ∈ A, r ≤ Real.sqrt C := by
    rintro r ⟨d, _, hd, rfl⟩
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg C)).1
    simpa only [Real.sq_sqrt hC] using hunit d hd
  have hdual : affineDirectionDualNorm X p (g x - g y) ≤ Real.sqrt C :=
    csSup_le hA hbound
  have hsquare := (sq_le_sq₀ (affineDirectionDualNorm_nonneg X p (g x - g y))
    (Real.sqrt_nonneg C)).2 hdual
  rw [Real.sq_sqrt hC] at hsquare
  have ht := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 1 / (2 * L))
  have heq : (1 / (2 * L)) * C = v x - v y - ⟪g y, x.1 - y.1⟫_ℝ := by
    dsimp [C]
    field_simp
  rwa [heq] at ht
end ConvexSmoothExtensionOn
end SOptLib

#print axioms SOptLib.ConvexSmoothExtensionOn.norm_gap
#print axioms SOptLib.ConvexSmoothExtensionOn.affineDual_gap
