import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: nonnegativity preservation for a geometric square recurrence; orig was generatedVSeq_coord_nonneg_on_horizon, renamed away from generated AMSGrad state and coordinate vocabulary.
-- generality used: natural-time scalar sequences over a linearly ordered commutative ring with a zero initial value, a one-based finite-horizon recurrence, and nonnegative recurrence coefficients; no measure, filtration, optimization, oracle, norm, inner-product, convexity, smoothness, or finite-dimensional assumptions are used.
-- portable call pattern: adaptive-gradient and recursive second-moment proofs instantiate `v` with a coordinate accumulator and `inc` with the current scalar gradient or residual; beta, horizon, and recurrence witnesses vary while the finite-horizon nonnegativity conclusion stays unchanged.
-- counterargument checked: not paper-local traceability because the statement is the reusable induction behind deterministic second-moment accumulators before square-root or denominator lower-bound arguments; not a pure wrapper around `sq_nonneg`, since it packages recurrence propagation across a horizon.
-- coverage search: searched `nonnegative scalar sequence geometric recurrence squared increment`, `sequence nonnegative recurrence square increment beta`, and `nonnegativity finite horizon recurrence square`; closest hits were `abs_recurrence_le_geometric_history_of_coeff_le`, geometric weighted Cauchy bounds, and broader stochastic second-moment recurrences, none of which give this pointwise nonnegativity preservation statement.
-- minimal hypotheses: all paper setup fields are reduced to `v 0 = 0`, the pointwise recurrence on `Finset.Icc 1 T`, and the two coefficient nonnegativity assumptions actually used.

/-- A geometric recurrence with a squared increment preserves nonnegativity on a
finite horizon.

If `v 0 = 0` and, on `1..T`, each `v t` is `beta` times the previous value plus
a nonnegative-coefficient multiple of a square, then every `v t` up to `T` is
nonnegative.

Layer: Glue | Gap: Level 1 (finite-horizon square-recurrence nonnegativity)
Proof: induct on natural time; the successor step rewrites by the supplied
  recurrence and uses nonnegativity of the previous value and of a square.
Source: Mathlib ordered-ring arithmetic, square nonnegativity, natural-number
  induction, and finite interval membership
Used in: adaptive second-moment accumulator proofs before taking coordinate
  square roots or deriving denominator lower bounds
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/2
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem nonneg_of_geometric_square_recurrence
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (v inc : ℕ → R) (beta : R) (T : ℕ)
    (hv_zero : v 0 = 0)
    (hrec : ∀ t ∈ Finset.Icc 1 T,
      v t = beta * v (t - 1) + (1 - beta) * (inc t) ^ 2)
    (hbeta_nonneg : 0 ≤ beta)
    (hone_minus_beta_nonneg : 0 ≤ 1 - beta) :
    ∀ t, t ≤ T → 0 ≤ v t := by
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
      have hinc_part : 0 ≤ (1 - beta) * (inc (n + 1)) ^ 2 :=
        mul_nonneg hone_minus_beta_nonneg (sq_nonneg _)
      rw [hrec (n + 1) ht_mem]
      exact add_nonneg hbeta_part hinc_part
