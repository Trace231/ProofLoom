import SOptLib.Glue.Algebra

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-window current-plus-previous shifted-sum domination; orig was `generated_previous_momentum_sum_le_current_core_block`
-- generality used: an ordered commutative semiring with monotone addition and nonnegative multiplication, scalar sequences indexed by natural time, a finite one-based horizon, a nonnegative scale, nonnegative core terms, same-index current domination, and predecessor-indexed previous domination after the zero first term
-- portable call pattern: adaptive-momentum, delayed-gradient, and finite-memory convergence proofs bound a current contribution and a one-step-shifted previous contribution by one common nonnegative core sum; the sequences, horizon, and scale change while the `2 * c` conclusion stays fixed
-- counterargument checked: this is not paper-local traceability or a caller-side addition of two already aggregated bounds because the theorem packages the nontrivial predecessor-window reindexing and its nonnegative finite-sum transport; no existing Mathlib/SOptLib declaration matched this combined current/previous contract
-- coverage search: searched `finite shifted sum current previous nonnegative core`, `current previous shift sum bounded by two times core`, and `sum current add previous`; `SOptLib.sum_Icc_one_eq_terminal_add_lagged` supplies only the interval split, while existing recurrence and telescope lemmas have different hypotheses and conclusions
-- minimal hypotheses: only nonnegativity of the terminal core term and the scale are needed; no measure, filtration, norm, convexity, smoothness, oracle, or finite-dimensional assumptions are used

/-- A current finite-window sum plus a one-step-shifted previous sum is bounded by
twice a common nonnegative core sum.

Layer: Glue | Gap: Level 1 (finite-window shifted-sum domination)
Proof: Sum the same-index current bound, split the previous window into its zero
first term and predecessor-indexed tail, use the finite-window lagged-sum split,
and transport the tail bound through nonnegative scalar multiplication.
Source: Mathlib finite sums over natural intervals, ordered-semiring monotonicity,
and SOptLib's one-based terminal lagged-sum identity
`sum_Icc_one_eq_terminal_add_lagged`.
Used in: adaptive-momentum convergence estimates where current and delayed
momentum contributions are each charged to a shared nonnegative core sequence.
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps
Origin algorithm: Reddi, Kale, and Kumar - On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem sum_current_add_previous_shift_le_two_mul_core_of_nonneg
    {R : Type*} [Semiring R] [Preorder R] [IsOrderedAddMonoid R] [PosMulMono R]
    (core current previous : ℕ → R) (T : ℕ) (c : R)
    (hc_nonneg : 0 ≤ c)
    (hcore_terminal_nonneg : 0 ≤ core T)
    (hcurrent_le : ∀ t ∈ Finset.Icc 1 T, current t ≤ c * core t)
    (hprevious_one : previous 1 = 0)
    (hprevious_shift :
      ∀ t ∈ Finset.Icc 2 T, previous t ≤ c * core (t - 1)) :
    (∑ t ∈ Finset.Icc 1 T, current t) +
        ∑ t ∈ Finset.Icc 1 T, previous t ≤
      (2 * c) * (∑ t ∈ Finset.Icc 1 T, core t) := by
  classical
  by_cases hT : T = 0
  · subst T
    simp
  have hT_pos : 1 ≤ T := by omega
  have hcurrent_sum :
      (∑ t ∈ Finset.Icc 1 T, current t) ≤
        c * (∑ t ∈ Finset.Icc 1 T, core t) := by
    calc
      (∑ t ∈ Finset.Icc 1 T, current t) ≤
          ∑ t ∈ Finset.Icc 1 T, c * core t := by
            refine Finset.sum_le_sum ?_
            intro t ht
            exact hcurrent_le t ht
      _ = c * (∑ t ∈ Finset.Icc 1 T, core t) := by
        rw [Finset.mul_sum]
  have hcore_tail_le :
      (∑ t ∈ Finset.Icc 2 T, core (t - 1)) ≤
        ∑ t ∈ Finset.Icc 1 T, core t := by
    have hsplit :=
      sum_Icc_one_eq_terminal_add_lagged core T hT_pos
    rw [hsplit]
    exact le_add_of_nonneg_left hcore_terminal_nonneg
  have hprevious_sum :
      (∑ t ∈ Finset.Icc 1 T, previous t) ≤
        c * (∑ t ∈ Finset.Icc 1 T, core t) := by
    have hsplit :=
      sum_Icc_one_eq_first_add_tail previous T hT_pos
    calc
      (∑ t ∈ Finset.Icc 1 T, previous t) =
          previous 1 + ∑ t ∈ Finset.Icc 2 T, previous t := hsplit
      _ = ∑ t ∈ Finset.Icc 2 T, previous t := by
        rw [hprevious_one, zero_add]
      _ ≤ ∑ t ∈ Finset.Icc 2 T, c * core (t - 1) := by
        refine Finset.sum_le_sum ?_
        intro t ht
        exact hprevious_shift t ht
      _ = c * (∑ t ∈ Finset.Icc 2 T, core (t - 1)) := by
        rw [Finset.mul_sum]
      _ ≤ c * (∑ t ∈ Finset.Icc 1 T, core t) := by
        exact mul_le_mul_of_nonneg_left hcore_tail_le hc_nonneg
  calc
    (∑ t ∈ Finset.Icc 1 T, current t) +
          ∑ t ∈ Finset.Icc 1 T, previous t ≤
        c * (∑ t ∈ Finset.Icc 1 T, core t) +
          c * (∑ t ∈ Finset.Icc 1 T, core t) := by
            exact add_le_add hcurrent_sum hprevious_sum
    _ = (2 * c) * (∑ t ∈ Finset.Icc 1 T, core t) := by
      rw [two_mul, add_mul]
