import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: square-root bound by a positive natural cast; orig was `boundary_sqrt_le_card`
-- generality used: a natural number `m` with `0 < m`, cast to `ℝ`; no measure, independence, integrability, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: any stochastic-optimization proof comparing a non-strict batch/cardinality range with a strict branch can instantiate its positive natural cardinality and reuse the real square-root upper bound
-- counterargument checked: this is a reusable order theorem that composes the square-root characterization with natural-cast arithmetic; it is not paper traceability, a caller-side expression, or a duplicate of the lower-level Mathlib square-root lemmas
-- coverage search: searched `sqrt nat cast le nat cast positive`, `sqrt le nat cast positive`, SOptLib Glue/Algebra, and Mathlib; Mathlib's `real_sqrt_le_nat_sqrt_succ` has a different conclusion and no complete matching declaration was found
-- minimal hypotheses: positivity of the natural number is the only hypothesis required by the proof

/-- The real square root of a positive natural cast is at most that cast.

Layer: Glue | Gap: Level 1 (positive natural square-root order bound)
Proof: apply `Real.sqrt_le_iff`, use positivity for the target cast, and discharge the squared-cast inequality from the positive natural lower bound with ordered-ring arithmetic.
Source: Mathlib real square-root order characterization, natural-number casts, and nonlinear real arithmetic
Used in: batch-boundary proofs that turn a non-strict cardinality range into equality before dispatching the unit-boundary branch
Book citation: book/research/PAGE.json#/extension/additions/main_theorem/proof/6
Origin algorithm: Li, Bao, Zhang, and Richtárik - PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization (Corollary 2) -/
theorem real_sqrt_natCast_le_natCast_of_pos (m : ℕ) (hm : 0 < m) :
    Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · exact_mod_cast (Nat.zero_le m)
  · have hm_one : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hm)
    nlinarith
