import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: geometric second-moment history-term lower bound from a recurrence; orig was generatedVSeq_coord_lower_single_history_term, renamed away from generated AMSGrad state and coordinate vocabulary.
-- generality used: scalar sequences over a linearly ordered commutative ring, zero initialization, a one-based finite-horizon second-moment recurrence, and nonnegative recurrence coefficients; no measure, filtration, optimization, oracle, norm, inner-product, convexity, smoothness, or finite-dimensional assumptions are used.
-- portable call pattern: Adam-, AdaGrad-, and AMSGrad-style scalar accumulator proofs instantiate `v` with a coordinate or scalar second-moment sequence and `g` with the corresponding gradient/residual; the recurrence witnesses, coefficient, and horizon vary while the pointwise history lower bound stays the same.
-- counterargument checked: not paper-local traceability or a caller-side expression because the theorem packages the nontrivial finite-horizon induction that preserves one selected historical square; it is not covered by the staged nonnegativity lemma, which proves only `0 ≤ v t`.
-- coverage search: searched `single geometric weighted square history term lower bound from recurrence`, `recurrence weighted square single history term lower bound`, and `geometric second moment history term`; closest hits were `nonneg_of_geometric_square_recurrence` and `abs_recurrence_le_geometric_history_of_coeff_le`, whose conclusions are respectively nonnegativity and an absolute-history sum, so coverage is partial rather than full.
-- minimal hypotheses: the paper setup is reduced to `v 0 = 0`, the pointwise recurrence on `Finset.Icc 1 T`, and the two coefficient nonnegativity assumptions actually used.

/-- A scalar second-moment recurrence retains every historical square with its
geometric coefficient.

If `v 0 = 0` and, on `1..T`, `v t` is updated by
`beta * v (t - 1) + (1 - beta) * (g t)^2`, then every `g j` with
`1 ≤ j ≤ t ≤ T` contributes the lower-bound term
`(1 - beta) * beta^(t-j) * (g j)^2` to `v t`.

Layer: Glue | Gap: Level 1 (finite-horizon geometric second-moment history lower bound)
Proof: Induct on time and propagate the selected historical term through the
recurrence; the current-time case uses square nonnegativity and the earlier
case scales the induction hypothesis by the nonnegative coefficient `beta`.
Source: Mathlib ordered-ring arithmetic, square nonnegativity, natural-number induction, and finite interval membership
Used in: Adam-, AdaGrad-, and AMSGrad-style denominator arguments that lower-bound an adaptive second-moment coordinate by one selected past gradient square before taking square roots or transporting quotients
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/2
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond - AMSGrad Algorithm 2 -/
theorem geometric_second_moment_history_term_le_of_recurrence
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (v g : ℕ → R) (beta : R) (T : ℕ)
    (hv_zero : v 0 = 0)
    (hrec : ∀ t ∈ Finset.Icc 1 T,
      v t = beta * v (t - 1) + (1 - beta) * (g t) ^ 2)
    (hbeta_nonneg : 0 ≤ beta)
    (hone_minus_beta_nonneg : 0 ≤ 1 - beta) :
    ∀ t ∈ Finset.Icc 1 T, ∀ j ∈ Finset.Icc 1 t,
      (1 - beta) * beta ^ (t - j) * (g j) ^ 2 ≤ v t := by
  have hnonneg : ∀ t, t ≤ T → 0 ≤ v t := by
    intro t
    induction t with
    | zero =>
        intro _ht
        simpa [hv_zero]
    | succ n ih =>
        intro hle
        have ht_mem : n + 1 ∈ Finset.Icc 1 T :=
          Finset.mem_Icc.mpr ⟨Nat.succ_pos n, hle⟩
        have hprev_nonneg : 0 ≤ v n := ih (by omega)
        have hbeta_part : 0 ≤ beta * v n :=
          mul_nonneg hbeta_nonneg hprev_nonneg
        have hcurrent_part : 0 ≤ (1 - beta) * (g (n + 1)) ^ 2 :=
          mul_nonneg hone_minus_beta_nonneg (sq_nonneg _)
        rw [hrec (n + 1) ht_mem]
        exact add_nonneg hbeta_part hcurrent_part
  intro t ht
  induction t with
  | zero =>
      simp at ht
  | succ n ih =>
      intro j hj
      cases n with
      | zero =>
          have hj_eq : j = 1 := by
            have hj_bounds := Finset.mem_Icc.mp hj
            omega
          subst j
          have hrec_one :
              v 1 = beta * v 0 + (1 - beta) * (g 1) ^ 2 := by
            simpa using hrec 1 ht
          calc
            (1 - beta) * beta ^ (1 - 1) * (g 1) ^ 2 =
                (1 - beta) * (g 1) ^ 2 := by norm_num
            _ = beta * 0 + (1 - beta) * (g 1) ^ 2 := by ring
            _ ≤ v (0 + 1) := by
              exact le_of_eq (by simpa [hv_zero] using hrec_one.symm)
      | succ n =>
          have hprev_mem : n + 1 ∈ Finset.Icc 1 T := by
            have ht_bounds := Finset.mem_Icc.mp ht
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hrec_current :
              v (n + 2) =
                beta * v (n + 1) + (1 - beta) * (g (n + 2)) ^ 2 := by
            simpa using hrec (n + 2) (by simpa using ht)
          by_cases hj_top : j = n + 2
          · subst j
            have hprev_nonneg : 0 ≤ beta * v (n + 1) :=
              mul_nonneg hbeta_nonneg
                (hnonneg (n + 1) (Finset.mem_Icc.mp hprev_mem).2)
            have hpow : beta ^ (n + 2 - (n + 2)) = 1 := by
              norm_num
            calc
              (1 - beta) * beta ^ (n + 2 - (n + 2)) * (g (n + 2)) ^ 2 =
                  (1 - beta) * (g (n + 2)) ^ 2 := by rw [hpow]; ring
              _ ≤ beta * v (n + 1) + (1 - beta) * (g (n + 2)) ^ 2 :=
                le_add_of_nonneg_left hprev_nonneg
              _ = v (n + 2) := hrec_current.symm
          · have hj_prev : j ∈ Finset.Icc 1 (n + 1) := by
              have hj_bounds := Finset.mem_Icc.mp hj
              exact Finset.mem_Icc.mpr ⟨hj_bounds.1, by omega⟩
            have hih := ih hprev_mem j hj_prev
            have hshift : n + 2 - j = (n + 1 - j) + 1 := by
              have hj_bounds := Finset.mem_Icc.mp hj
              omega
            have hterm_shift :
                (1 - beta) * beta ^ (n + 2 - j) * (g j) ^ 2 =
                  beta * ((1 - beta) * beta ^ (n + 1 - j) * (g j) ^ 2) := by
              rw [hshift, pow_succ]
              ring
            have hscaled :
                beta * ((1 - beta) * beta ^ (n + 1 - j) * (g j) ^ 2) ≤
                  beta * v (n + 1) :=
              mul_le_mul_of_nonneg_left hih hbeta_nonneg
            have hcurrent_nonneg : 0 ≤ (1 - beta) * (g (n + 2)) ^ 2 :=
              mul_nonneg hone_minus_beta_nonneg (sq_nonneg _)
            calc
              (1 - beta) * beta ^ (n + 2 - j) * (g j) ^ 2 =
                  beta * ((1 - beta) * beta ^ (n + 1 - j) * (g j) ^ 2) :=
                hterm_shift
              _ ≤ beta * v (n + 1) := hscaled
              _ ≤ beta * v (n + 1) + (1 - beta) * (g (n + 2)) ^ 2 := by
                exact le_add_of_nonneg_right hcurrent_nonneg
              _ = v (n + 2) := by
                simpa using hrec_current.symm
