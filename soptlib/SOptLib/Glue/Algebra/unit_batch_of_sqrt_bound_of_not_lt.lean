import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import SOptLib.Glue.Algebra.real_sqrt_natCast_le_natCast_of_pos
-- Generalization plan (G0):
-- concept/name: collapse a positive natural square-root boundary to the unit batch; orig was `corollaryTwo_batch_boundary_split`
-- generality used: natural numbers `m` and `n`, real square-root comparison, positivity of `m`, and a natural strict-order negation; no measure, independence, integrability, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: any finite-batch stochastic method can dispatch a non-strict `n ≤ √m` boundary against a strict-branch requirement by supplying the positive batch cardinality and `¬ n < m`; the conclusion identifies both batch sizes as one
-- counterargument checked: this is a reusable arithmetic implication with a compound conclusion, not a paper traceability wrapper or caller-side expression; lower-level square-root lemmas do not package the cardinality collapse
-- coverage search: searched `positive naturals n ≤ sqrt m not n < m`, `sqrt bound boundary cardinality`, SOptLib Glue/Algebra, and Mathlib; only the lower-level `real_sqrt_natCast_le_natCast_of_pos` helper was found, so this theorem adds the missing combined step
-- minimal hypotheses: positivity of `m`, the real square-root bound on the natural cast of `n`, and `¬ n < m` are sufficient and all are used

/-- A positive natural square-root boundary with no strict inequality is the unit case.

Layer: Glue | Gap: Level 1 (square-root batch-boundary collapse)
Proof: derive `m ≤ n` from the negated strict inequality, cast it to the reals, and sandwich `n` between `m` and `√m`; the resulting square-root equality and `Real.sq_sqrt` force `m = 1`, after which `n = 1` follows by casting.
Source: Mathlib real square-root order characterization, natural-number casts, and nonlinear ordered-ring arithmetic
Used in: finite-batch algorithm boundary dispatch when a source condition `n ≤ √m` must be reconciled with an inherited strict branch `n < m`
Book citation: book/research/PAGE.json#/extension/additions/main_theorem/proof/6
Origin algorithm: Li, Bao, Zhang, and Richtárik - PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization (Corollary 2) -/
theorem unit_batch_of_sqrt_bound_of_not_lt
    (m n : ℕ)
    (hm : 0 < m)
    (h_sqrt : (n : ℝ) ≤ Real.sqrt (m : ℝ))
    (h_not_lt : ¬ n < m) :
    m = 1 ∧ n = 1 := by
  have hm_le_n : m ≤ n := Nat.le_of_not_lt h_not_lt
  have hm_le_n_real : (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hm_le_n
  have hsqrt_le_m : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
    exact real_sqrt_natCast_le_natCast_of_pos m hm
  have hm_eq_n_real : (m : ℝ) = (n : ℝ) := by
    exact le_antisymm hm_le_n_real (le_trans h_sqrt hsqrt_le_m)
  have hm_eq_n : m = n := by
    exact_mod_cast hm_eq_n_real
  have hsqrt_eq_m : Real.sqrt (m : ℝ) = (m : ℝ) := by
    exact le_antisymm hsqrt_le_m (le_trans hm_le_n_real h_sqrt)
  have hm_one_real : (m : ℝ) = 1 := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))
    rw [hsqrt_eq_m] at hsq
    have hm_ge_one_nat : 1 ≤ m := hm
    have hm_ge_one_real : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm_ge_one_nat
    nlinarith
  have hm_one : m = 1 := by
    exact_mod_cast hm_one_real
  exact ⟨hm_one, hm_eq_n.symm.trans hm_one⟩
