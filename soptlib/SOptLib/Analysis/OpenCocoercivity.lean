import SOptLib.Analysis.BregmanFromCocoercivity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Open-domain Baillon--Haddad via feasible local descent steps and a uniform
subdivision of the segment. This proves the PAV conclusion directly, avoiding
the historical generalized-Hessian proof's unfinished dependencies.
-/

open scoped InnerProductSpace
open Set

namespace SOptLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem gap_bound_of_feasible_step
    (f : E → ℝ) (G : E → E) (U : Set E) (L : ℝ) (hL : 0 < L)
    (hs : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ f x - f y - ⟪G y, x - y⟫_ℝ)
    (hu : ∀ x ∈ U, ∀ y ∈ U,
      f y ≤ f x + ⟪G x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U)
    (hz : x - L⁻¹ • (G x - G y) ∈ U) :
    ‖G x - G y‖ ^ 2 ≤ 2 * L * (f x - f y - ⟪G y, x - y⟫_ℝ) := by
  let d := G x - G y
  let z := x - L⁻¹ • d
  have h1 := hs z hz y hy
  have h2 := hu x hx z hz
  have hzx : z - x = -L⁻¹ • d := by dsimp [z]; module
  have hzy : z - y = (x - y) - L⁻¹ • d := by dsimp [z]; module
  have hn : ‖z - x‖ ^ 2 = L⁻¹ ^ 2 * ‖d‖ ^ 2 := by
    rw [hzx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hL)]
    ring
  have hi : ⟪G x, z - x⟫_ℝ - ⟪G y, z - y⟫_ℝ =
      -L⁻¹ * ‖d‖ ^ 2 - ⟪G y, x - y⟫_ℝ := by
    rw [hzx, hzy]
    simp only [inner_smul_right, inner_sub_right, neg_mul]
    have hd : ‖d‖ ^ 2 = ⟪G x, d⟫_ℝ - ⟪G y, d⟫_ℝ := by
      rw [← inner_sub_left]
      exact (real_inner_self_eq_norm_sq d).symm
    rw [hd]
    ring
  have h3 : 0 ≤ f x - f y - ⟪G y, x - y⟫_ℝ - (1 / (2 * L)) * ‖d‖ ^ 2 := by
    have hc : -L⁻¹ * ‖d‖ ^ 2 + L / 2 * (L⁻¹ ^ 2 * ‖d‖ ^ 2) =
        -(1 / (2 * L)) * ‖d‖ ^ 2 := by field_simp; ring
    rw [hn] at h2
    linarith
  have h4 := mul_nonneg (show 0 ≤ 2 * L by positivity) h3
  have he : 2 * L * ((1 / (2 * L)) * ‖d‖ ^ 2) = ‖d‖ ^ 2 := by
    field_simp [ne_of_gt hL]
  dsimp [d] at *
  nlinarith

private theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hn := norm_sum_le s v
  have hs : 0 ≤ ∑ i ∈ s, ‖v i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (v i))
  have hsq : ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hs).mpr hn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) s
    (fun _ : ι => (1 : ℝ)) (fun i => ‖v i‖)
  exact hsq.trans (by simpa using hcs)

theorem open_cocoercivity_of_support_upper_lipschitz
    (f : E → ℝ) (G : E → E) (U : Set E) (L : ℝ) (hL : 0 < L)
    (ho : IsOpen U) (hc : Convex ℝ U)
    (hs : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ f x - f y - ⟪G y, x - y⟫_ℝ)
    (hu : ∀ x ∈ U, ∀ y ∈ U,
      f y ≤ f x + ⟪G x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (hl : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U) :
    ‖G x - G y‖ ^ 2 ≤ L * ⟪G x - G y, x - y⟫_ℝ := by
  obtain ⟨rx, hrx, hbx⟩ := Metric.isOpen_iff.mp ho x hx
  obtain ⟨ry, hry, hby⟩ := Metric.isOpen_iff.mp ho y hy
  let r := min rx ry
  have hr : 0 < r := lt_min hrx hry
  obtain ⟨n, hn⟩ := exists_nat_gt (max (‖y - x‖ / r) 0)
  have hnR : 0 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnN : 0 < n := by exact_mod_cast hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hstep : ‖y - x‖ / (n : ℝ) < r := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hr).mp (lt_of_le_of_lt (le_max_left _ _) hn)
    nlinarith
  let p : ℕ → E := fun k => (1 - (k : ℝ) / n) • x + ((k : ℝ) / n) • y
  have hp0 : p 0 = x := by simp [p]
  have hpn : p n = y := by simp [p, hn0]
  have htube : ∀ k ≤ n, ∀ e : E, ‖e‖ < r → p k + e ∈ U := by
    intro k hk e he
    have ht0 : 0 ≤ (k : ℝ) / n := div_nonneg (Nat.cast_nonneg k) hnR.le
    have ht1 : (k : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hk)
    have hx' : x + e ∈ U := hbx (by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa using he.trans_le (min_le_left rx ry))
    have hy' : y + e ∈ U := hby (by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa using he.trans_le (min_le_right rx ry))
    have h := hc hx' hy' (sub_nonneg.mpr ht1) ht0 (sub_add_cancel _ _)
    convert h using 1
    dsimp [p]
    module
  have hp : ∀ k ≤ n, p k ∈ U := by
    intro k hk
    simpa using htube k hk 0 (by simpa using hr)
  have hinc : ∀ k, p (k + 1) - p k = (n : ℝ)⁻¹ • (y - x) := by
    intro k
    dsimp [p]
    push_cast
    simp only [div_eq_mul_inv]
    module
  have hclose : ∀ k, ‖p (k + 1) - p k‖ < r := by
    intro k
    rw [hinc, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnR)]
    simpa [div_eq_mul_inv, mul_comm] using hstep
  have hlocal : ∀ k < n,
      ‖G (p (k + 1)) - G (p k)‖ ^ 2 ≤
        L * ⟪G (p (k + 1)) - G (p k), p (k + 1) - p k⟫_ℝ := by
    intro k hk
    have hk1 : k + 1 ≤ n := by omega
    have hk0 : k ≤ n := by omega
    have hfeas : ∀ a b : ℕ, a ≤ n → b ≤ n → ‖p a - p b‖ < r →
        p a - L⁻¹ • (G (p a) - G (p b)) ∈ U := by
      intro a b ha hb hab
      have hnrm : ‖-L⁻¹ • (G (p a) - G (p b))‖ < r := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hL)]
        calc
          L⁻¹ * ‖G (p a) - G (p b)‖ ≤ L⁻¹ * (L * ‖p a - p b‖) :=
            mul_le_mul_of_nonneg_left (hl _ (hp a ha) _ (hp b hb)) (inv_nonneg.mpr hL.le)
          _ = ‖p a - p b‖ := by field_simp [ne_of_gt hL]
          _ < r := hab
      simpa [sub_eq_add_neg, neg_smul, add_comm] using htube a ha _ hnrm
    have h1 := gap_bound_of_feasible_step f G U L hL hs hu
      _ (hp (k + 1) hk1) _ (hp k hk0) (hfeas _ _ hk1 hk0 (hclose k))
    have h2 := gap_bound_of_feasible_step f G U L hL hs hu
      _ (hp k hk0) _ (hp (k + 1) hk1)
      (hfeas _ _ hk0 hk1 (by simpa [norm_sub_rev] using hclose k))
    rw [norm_sub_rev (G (p k)) (G (p (k + 1)))] at h2
    simp only [inner_sub_left, inner_sub_right] at *
    nlinarith
  let v : ℕ → E := fun k => G (p (k + 1)) - G (p k)
  have htel : ∑ k ∈ Finset.range n, v k = G y - G x := by
    simpa [v, hp0, hpn] using Finset.sum_range_sub (fun k => G (p k)) n
  have hsum : ∑ k ∈ Finset.range n, ‖v k‖ ^ 2 ≤
      (L / n) * ⟪G y - G x, y - x⟫_ℝ := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, L * ⟪v k, (n : ℝ)⁻¹ • (y - x)⟫_ℝ := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [v, hinc] using hlocal k (Finset.mem_range.mp hk)
      _ = _ := by
        simp only [inner_smul_right, ← Finset.mul_sum, ← sum_inner]
        rw [htel]
        ring
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq (Finset.range n) v
  rw [htel, Finset.card_range] at hcs
  have hmul := mul_le_mul_of_nonneg_left hsum hnR.le
  have hcancel : (n : ℝ) * ((L / n) * ⟪G y - G x, y - x⟫_ℝ) =
      L * ⟪G y - G x, y - x⟫_ℝ := by field_simp
  rw [hcancel] at hmul
  have hresult := hcs.trans hmul
  have hi : ⟪G y - G x, y - x⟫_ℝ = ⟪G x - G y, x - y⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rwa [norm_sub_rev (G y) (G x), hi] at hresult

end SOptLib

#print axioms SOptLib.open_cocoercivity_of_support_upper_lipschitz
