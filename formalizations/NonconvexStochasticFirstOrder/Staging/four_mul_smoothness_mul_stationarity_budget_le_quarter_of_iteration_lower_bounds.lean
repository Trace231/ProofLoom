import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: smoothness-scaled stationarity budget quarter bound; orig was
--   `theorem62_partB_stationarity_term_le_quarter`, renamed away from theorem
--   numbering and the local setup wrapper.
-- generality used: real scalar smoothness, radius, combined noise coefficient,
--   noise scale, accuracy, and a natural horizon; no measure, independence,
--   integrability, convexity, oracle, normed-space, or finite-dimensional
--   assumptions are used.
-- portable call pattern: nonconvex stochastic first-order methods with a
--   budget `L * D^2 / N + C * sigma / sqrt N` call the same quarter-budget
--   inequality after selecting `N` from deterministic and stochastic lower
--   bound branches.
-- counterargument checked: this is not paper-local traceability because it
--   packages the reusable conversion from iteration lower bounds to a
--   smoothness-scaled accuracy allocation; existing budget-choice lemmas
--   cover different constants or different budget expressions.
-- coverage search: searched `four times smoothness stationarity budget at most
--   epsilon over four from deterministic and stochastic iteration lower
--   bounds`; closest hits were `budgetChoice_lower_bounds`,
--   `budget_bound_le_half_of_budget_choice`, and
--   `le_positive_ceil_threeway_max`, which do not state this two-branch
--   quarter-budget contract.
-- minimal hypotheses: positivity of L, C, sigma, and epsilon is sufficient;
--   D is unrestricted because it occurs only through D^2.

/-- Deterministic and stochastic iteration lower bounds make the scaled
stationarity budget at most one quarter of the accuracy.

For a budget of the form `L * D^2 / N + C * sigma / sqrt N`, the deterministic
lower bound controls the `L * D^2 / N` term and the squared stochastic lower
bound controls the `C * sigma / sqrt N` term. After scaling by `4 * L`, the
two equal `epsilon / (32 * L)` allocations sum to `epsilon / 4`.

Layer: Glue | Gap: Level 1 (closed-form stationarity-budget allocation)
Proof: clear the two positive denominators using ordered-field arithmetic; for
the stochastic branch, use `Real.le_sqrt_of_sq_le` before dividing by `sqrt N`.
Source: Mathlib real square-root monotonicity, natural-number coercions, and ordered-field division arithmetic
Used in: nonconvex stochastic first-order methods when a selected optimization horizon is chosen from deterministic and stochastic stationarity-budget lower bounds
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
theorem four_mul_smoothness_mul_stationarity_budget_le_quarter_of_iteration_lower_bounds
    (L D C sigma epsilon : Real)
    (hL_pos : 0 < L) (hC_pos : 0 < C) (hsigma_pos : 0 < sigma)
    (hepsilon_pos : 0 < epsilon) :
    let N : Nat :=
      Nat.ceil
        ((max (32 * L ^ 2 * D ^ 2 / epsilon)
          (32 * L * C * sigma / epsilon)) ^ 2)
    4 * L * (L * D ^ 2 / (N : Real) + C * sigma / Real.sqrt (N : Real)) <=
      epsilon / 4 := by
  dsimp only
  let N : Nat :=
    Nat.ceil
      ((max (32 * L ^ 2 * D ^ 2 / epsilon)
        (32 * L * C * sigma / epsilon)) ^ 2)
  have hceil_sq :
      (max
          (32 * L ^ 2 * D ^ 2 / epsilon)
          (32 * L * C * sigma / epsilon)) ^ 2 <=
        (N : Real) := by
    simpa [N] using
      Nat.le_ceil
        ((max
          (32 * L ^ 2 * D ^ 2 / epsilon)
          (32 * L * C * sigma / epsilon)) ^ 2)
  have hsto_choice_pos : 0 < 32 * L * C * sigma / epsilon := by
    exact div_pos
      (mul_pos (mul_pos (mul_pos (by norm_num : (0 : Real) < 32) hL_pos)
        hC_pos) hsigma_pos)
      hepsilon_pos
  have hmax_pos :
      0 <
        max (32 * L ^ 2 * D ^ 2 / epsilon)
          (32 * L * C * sigma / epsilon) :=
    lt_of_lt_of_le hsto_choice_pos (le_max_right _ _)
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (sq_pos_of_pos hmax_pos)
  have hN_nat : 1 <= N := Nat.succ_le_of_lt hN_pos_nat
  have hN_pos : 0 < (N : Real) := by
    exact_mod_cast hN_pos_nat
  have hsqrtN_pos : 0 < Real.sqrt (N : Real) :=
    Real.sqrt_pos.2 hN_pos
  have hmax_le_N :
      max (32 * L ^ 2 * D ^ 2 / epsilon)
          (32 * L * C * sigma / epsilon) <=
        (N : Real) := by
    by_cases hlarge :
        1 <=
          max (32 * L ^ 2 * D ^ 2 / epsilon)
            (32 * L * C * sigma / epsilon)
    · have hle_sq :
          max (32 * L ^ 2 * D ^ 2 / epsilon)
              (32 * L * C * sigma / epsilon) <=
            (max (32 * L ^ 2 * D ^ 2 / epsilon)
              (32 * L * C * sigma / epsilon)) ^ 2 := by
        nlinarith [hlarge]
      exact le_trans hle_sq hceil_sq
    · have hle_one :
          max (32 * L ^ 2 * D ^ 2 / epsilon)
              (32 * L * C * sigma / epsilon) <= 1 :=
        le_of_not_ge hlarge
      have hone_le_N : (1 : Real) <= (N : Real) := by
        exact_mod_cast hN_nat
      exact le_trans hle_one hone_le_N
  have hdet_lower :
      32 * L ^ 2 * D ^ 2 / epsilon <= (N : Real) := by
    exact le_trans (le_max_left _ _) hmax_le_N
  have hsto_lower :
      (32 * L * C * sigma / epsilon) ^ 2 <= (N : Real) := by
    have hsq_le :
        (32 * L * C * sigma / epsilon) ^ 2 <=
          (max (32 * L ^ 2 * D ^ 2 / epsilon)
            (32 * L * C * sigma / epsilon)) ^ 2 :=
      (sq_le_sq₀ (le_of_lt hsto_choice_pos) (le_of_lt hmax_pos)).2
        (le_max_right _ _)
    exact le_trans hsq_le hceil_sq
  have hdet :
      L * D ^ 2 / (N : Real) <= epsilon / (32 * L) := by
    have hmul :
        32 * L ^ 2 * D ^ 2 <= (N : Real) * epsilon := by
      rwa [div_le_iff₀ hepsilon_pos] at hdet_lower
    have hnum :
        L * D ^ 2 <= ((N : Real) * epsilon) / (32 * L) := by
      rw [le_div_iff₀ (mul_pos (by norm_num : (0 : Real) < 32) hL_pos)]
      nlinarith [hmul]
    calc
      L * D ^ 2 / (N : Real)
          <= (((N : Real) * epsilon) / (32 * L)) / (N : Real) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hN_pos)
      _ = epsilon / (32 * L) := by
            field_simp [ne_of_gt hN_pos, ne_of_gt hL_pos]
  have hsto :
      C * sigma / Real.sqrt (N : Real) <= epsilon / (32 * L) := by
    have hx_sqrt :
        32 * L * C * sigma / epsilon <= Real.sqrt (N : Real) :=
      Real.le_sqrt_of_sq_le hsto_lower
    rw [div_le_iff₀ hepsilon_pos] at hx_sqrt
    ring_nf at hx_sqrt
    have hnum :
        C * sigma <= (Real.sqrt (N : Real) * epsilon) / (32 * L) := by
      rw [le_div_iff₀ (mul_pos (by norm_num : (0 : Real) < 32) hL_pos)]
      nlinarith [hx_sqrt]
    calc
      C * sigma / Real.sqrt (N : Real)
          <= ((Real.sqrt (N : Real) * epsilon) / (32 * L)) /
              Real.sqrt (N : Real) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hsqrtN_pos)
      _ = epsilon / (32 * L) := by
            field_simp [ne_of_gt hsqrtN_pos, ne_of_gt hL_pos]
  calc
    4 * L * (L * D ^ 2 / (N : Real) + C * sigma / Real.sqrt (N : Real))
        <= 4 * L * (epsilon / (32 * L) + epsilon / (32 * L)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hdet hsto)
            (mul_nonneg (by norm_num : (0 : Real) <= 4) (le_of_lt hL_pos))
    _ = epsilon / 4 := by
          field_simp [ne_of_gt hL_pos]
          ring
