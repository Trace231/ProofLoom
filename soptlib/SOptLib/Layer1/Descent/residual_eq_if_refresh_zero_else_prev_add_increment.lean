import Mathlib.Algebra.Group.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: residual branch decomposition into an exact-refresh zero or a recursive previous-plus-increment form; orig was `line4_residual_branch_decomposition`.
-- generality used: arbitrary time-indexed residual maps into an additive monoid and a Boolean branch map; no norm, inner product, measure, probability, smoothness, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: refresh/recursive stochastic-estimator proofs provide the exact-refresh and non-refresh residual certificates at a time index, then reuse the same pointwise conditional decomposition while changing the process, branch schedule, and increment.
-- counterargument checked: this is not paper-local traceability or a caller-side expression; it packages the recurring two-branch case split and preserves a named residual invariant. Existing recursive-residual and second-moment APIs cover the non-refresh algebra or consume a decomposition, but no existing declaration assembles these two branch certificates.
-- coverage search: searched `branch decomposition residual zero previous increment` and `residual if branch zero else previous plus increment`; the closest hit was `estimator_residual_second_moment_step_of_refresh_or_centered_recursive_branch`, whose measure-level bound consumes a supplied decomposition and does not state this pointwise branch assembly.
-- minimal hypotheses: `[AddMonoid E]` supplies only zero and addition; the time index is retained because residual and branch processes vary with time.

/-- A residual process is zero on refresh steps and advances by a previous residual
plus an increment on recursive steps.

Layer: Layer1 | Gap: Level 0 (refresh-or-recursive residual branch assembly)
Proof: split on the Boolean branch at the selected time and apply the corresponding
pointwise branch certificate, simplifying the conditional expression.
Source: Mathlib Boolean case analysis, conditional simplification, and additive-monoid identities
Used in: refresh/recursive stochastic-gradient estimator recurrences before replacing the next residual by a branch-specific square or inner-product expression
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem residual_eq_if_refresh_zero_else_prev_add_increment
    {Ω E : Type*} [AddMonoid E]
    (δprev δnext inc : ℕ → Ω → E)
    (branch : ℕ → Ω → Bool) (t : ℕ)
    (h_refresh : ∀ ω, branch t ω = true → δnext t ω = 0)
    (h_recursive : ∀ ω, branch t ω = false →
      δnext t ω = δprev t ω + inc t ω) :
    ∀ ω, δnext t ω = if branch t ω then 0 else δprev t ω + inc t ω := by
  intro ω
  cases h : branch t ω with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact h_recursive ω h
  | true =>
      simp only [↓reduceIte]
      exact h_refresh ω h

end SOptLib
