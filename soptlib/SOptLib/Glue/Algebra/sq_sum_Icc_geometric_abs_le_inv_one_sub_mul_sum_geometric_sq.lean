import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted geometric finite-history Cauchy-Schwarz bound; orig was amsgrad_weighted_geometric_cauchy_sq.
-- generality used: real scalar weights indexed by natural time, with nonnegative base below one; no measure, filtration, optimization, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: momentum and exponentially weighted-history proofs instantiate beta and a scalar history g, while the horizon and algorithm-specific recurrence change; the weighted absolute-sum square conclusion stays fixed.
-- counterargument checked: this is not paper-local traceability or a caller-side expression because it packages finite Cauchy-Schwarz together with the geometric-tail budget; Mathlib's finite Cauchy theorem and geometric-sum identity are only partial components.
-- coverage search: searched `square geometrically weighted absolute sum bounded by reciprocal tail mass weighted square sum` and `finite Cauchy Schwarz geometric weighted sum`; Mathlib supplied `Real.sum_mul_le_sqrt_mul_sqrt` and `geom_sum_mul_neg`, while SOptLib had no declaration with this combined interval-weighted conclusion.
-- minimal hypotheses: the algorithm-specific history and momentum setup are replaced by `(beta : ℝ)`, `(t : ℕ)`, and `(g : ℕ → ℝ)`; nonnegativity and strict upper bound on beta are exactly the hypotheses used by the square-root and tail arguments.

/-- The square of a nonnegative geometrically weighted absolute history is
bounded by the reciprocal geometric tail mass times the corresponding weighted
square history.

Layer: Glue | Gap: Level 1 (finite geometric weighted Cauchy-Schwarz bound)
Proof: apply finite Cauchy-Schwarz after splitting each weight into two square
roots, then bound the resulting geometric weight sum using the finite geometric
series identity and `0 ≤ beta < 1`.
Source: Mathlib finite Cauchy-Schwarz, real square-root identities, finite sums
over intervals, and ordered real geometric-series algebra
Used in: momentum and exponentially weighted-history estimates that convert a
weighted absolute numerator into a weighted second-moment sum with a reciprocal
tail-mass factor
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/2/proof/2
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem sq_sum_Icc_geometric_abs_le_inv_one_sub_mul_sum_geometric_sq
    (beta : ℝ) (hbeta_nonneg : 0 ≤ beta) (hbeta_lt : beta < 1)
    (t : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 t, beta ^ (t - j) * |g j|) ^ 2 ≤
      (1 / (1 - beta)) *
        (∑ j ∈ Finset.Icc 1 t, beta ^ (t - j) * (g j) ^ 2) := by
  let s := Finset.Icc 1 t
  let w : ℕ → ℝ := fun j => beta ^ (t - j)
  have hw_nonneg : ∀ j, 0 ≤ w j := fun j => pow_nonneg hbeta_nonneg _
  have hsumw_nonneg : 0 ≤ ∑ j ∈ s, w j := by
    exact Finset.sum_nonneg (fun j _hj => hw_nonneg j)
  have hsumg_nonneg : 0 ≤ ∑ j ∈ s, w j * (g j) ^ 2 := by
    exact Finset.sum_nonneg (fun j _hj =>
      mul_nonneg (hw_nonneg j) (sq_nonneg _))
  have hleft_nonneg :
      0 ≤ ∑ j ∈ s, w j * |g j| := by
    exact Finset.sum_nonneg (fun j _hj =>
      mul_nonneg (hw_nonneg j) (abs_nonneg _))
  have hcs_raw :=
    Real.sum_mul_le_sqrt_mul_sqrt s
      (fun j => Real.sqrt (w j))
      (fun j => Real.sqrt (w j) * |g j|)
  have hleft_eq :
      (∑ j ∈ s, Real.sqrt (w j) *
          (Real.sqrt (w j) * |g j|)) =
        ∑ j ∈ s, w j * |g j| := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [← mul_assoc, ← sq]
    rw [Real.sq_sqrt (hw_nonneg j)]
  have hfirst_eq :
      (∑ j ∈ s, (Real.sqrt (w j)) ^ 2) =
        ∑ j ∈ s, w j := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    exact Real.sq_sqrt (hw_nonneg j)
  have hsecond_eq :
      (∑ j ∈ s, (Real.sqrt (w j) * |g j|) ^ 2) =
        ∑ j ∈ s, w j * (g j) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [mul_pow, sq_abs, Real.sq_sqrt (hw_nonneg j)]
  have hcs :
      (∑ j ∈ s, w j * |g j|) ≤
        Real.sqrt (∑ j ∈ s, w j) *
          Real.sqrt (∑ j ∈ s, w j * (g j) ^ 2) := by
    simpa [hleft_eq, hfirst_eq, hsecond_eq] using hcs_raw
  have hsquared :
      (∑ j ∈ s, w j * |g j|) ^ 2 ≤
        (∑ j ∈ s, w j) * (∑ j ∈ s, w j * (g j) ^ 2) := by
    have hrhs_nonneg :
        0 ≤ Real.sqrt (∑ j ∈ s, w j) *
          Real.sqrt (∑ j ∈ s, w j * (g j) ^ 2) := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have habs :
        |((∑ j ∈ s, w j * |g j|) : ℝ)| ≤
          |(Real.sqrt (∑ j ∈ s, w j) *
            Real.sqrt (∑ j ∈ s, w j * (g j) ^ 2) : ℝ)| := by
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hrhs_nonneg] using hcs
    have hsq_le := sq_le_sq.2 habs
    calc
      (∑ j ∈ s, w j * |g j|) ^ 2
          ≤ (Real.sqrt (∑ j ∈ s, w j) *
              Real.sqrt (∑ j ∈ s, w j * (g j) ^ 2)) ^ 2 := hsq_le
      _ = (∑ j ∈ s, w j) * (∑ j ∈ s, w j * (g j) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hsumw_nonneg,
            Real.sq_sqrt hsumg_nonneg]
  have hgeom :
      (∑ j ∈ s, w j) ≤ 1 / (1 - beta) := by
    have hrewrite :
        (∑ j ∈ s, w j) =
          ∑ k ∈ Finset.range t, beta ^ k := by
      dsimp [s, w]
      by_cases ht_pos : 1 ≤ t
      · have hbij :
            (∑ j ∈ Finset.Icc 1 t, beta ^ (t - j)) =
              ∑ k ∈ Finset.range t, beta ^ k := by
          refine Finset.sum_bij (fun j _hj => t - j) ?_ ?_ ?_ ?_
          · intro j hj
            have hjb := Finset.mem_Icc.mp hj
            change t - j ∈ Finset.range t
            exact Finset.mem_range.mpr (by omega)
          · intro a ha b hb hab
            have hab' : t - a = t - b := hab
            have ha_le : a ≤ t := (Finset.mem_Icc.mp ha).2
            have hb_le : b ≤ t := (Finset.mem_Icc.mp hb).2
            omega
          · intro k hk
            have hk_lt : k < t := Finset.mem_range.mp hk
            refine ⟨t - k, ?_, ?_⟩
            · change t - k ∈ Finset.Icc 1 t
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            · change t - (t - k) = k
              exact Nat.sub_sub_self (Nat.le_of_lt hk_lt)
          · intro j hj
            rfl
        exact hbij
      · have ht_zero : t = 0 := by omega
        subst t
        simp
    have hden_pos : 0 < 1 - beta := by linarith
    have hpow_nonneg : 0 ≤ beta ^ t := pow_nonneg hbeta_nonneg t
    have hmul_eq :
        (∑ k ∈ Finset.range t, beta ^ k) * (1 - beta) =
          1 - beta ^ t := by
      simpa using (geom_sum_mul_neg beta t)
    have hmul_le :
        (∑ k ∈ Finset.range t, beta ^ k) * (1 - beta) ≤ 1 := by
      rw [hmul_eq]
      linarith
    rw [hrewrite]
    exact (le_div_iff₀ hden_pos).2 hmul_le
  calc
    (∑ j ∈ Finset.Icc 1 t, beta ^ (t - j) * |g j|) ^ 2
        = (∑ j ∈ s, w j * |g j|) ^ 2 := by rfl
    _ ≤ (∑ j ∈ s, w j) * (∑ j ∈ s, w j * (g j) ^ 2) := hsquared
    _ ≤ (1 / (1 - beta)) * (∑ j ∈ s, w j * (g j) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hgeom hsumg_nonneg
    _ = (1 / (1 - beta)) *
        (∑ j ∈ Finset.Icc 1 t, beta ^ (t - j) * (g j) ^ 2) := by
        rfl
