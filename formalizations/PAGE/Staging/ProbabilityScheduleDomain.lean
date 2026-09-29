import Mathlib.Data.Real.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: time-indexed probability schedule domain; orig was RefreshProbabilityDomain.
-- generality used: an arbitrary natural-indexed real schedule; no measure, independence, integrability, optimization, or finite-dimensional assumptions are needed.
-- portable call pattern: any stochastic algorithm with time-varying refresh or activation probabilities can use this domain before constructing Bernoulli branches or product laws; the schedule changes while the pointwise bounds stay the same.
-- counterargument checked: this is a reusable mathematical contract rather than paper traceability or a caller-side expression; exact symbol searches found no existing SOptLib or Mathlib declaration with this statement, and the semantic Mathlib search service was unavailable.
-- coverage search: searched "probability schedule pointwise positive bounded one", "refresh activation probability domain", and the exact pointwise shape across SOptLib, Staging, and Mathlib; hits were PAGE-local schedule predicates or unrelated probability infrastructure, so coverage was none.
-- minimal hypotheses: the natural index and real codomain are the only required parameters; all setup, measure, and optimization assumptions were removed.

/-- A time-indexed real probability schedule stays strictly positive and at
most one at every natural-number time.

Layer: Model | Concept: time-indexed probability schedule domain
Proof: (definitional construction; pointwise positivity and upper-bound contract for a real-valued schedule)
Source: Mathlib ordered-real inequalities and function-space predicates
Used in: stochastic refresh, activation, and Bernoulli-branch constructions, where an algorithm supplies its schedule and reuses the same domain contract
Book citation: book/research/PAGE.json#/assumptions/3
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
def ProbabilityScheduleDomain (p : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < p t ∧ p t ≤ 1

/-- The probability-schedule domain unfolds to its pointwise inequalities.

Layer: Model | Gap: Level 0 (probability schedule domain unfolding)
Proof: by rfl after unfolding `ProbabilityScheduleDomain`.
Source: Mathlib propositional predicates and ordered-real inequalities
Used in: exposing positivity and unit upper bounds when a stochastic algorithm builds a time-indexed branch law
Book citation: book/research/PAGE.json#/assumptions/3
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
@[simp] theorem ProbabilityScheduleDomain_def (p : ℕ → ℝ) :
    ProbabilityScheduleDomain p ↔ ∀ t : ℕ, 0 < p t ∧ p t ≤ 1 := by
  rfl

/-- A schedule in the probability domain is positive at each time. -/
theorem ProbabilityScheduleDomain_pos (p : ℕ → ℝ)
    (h : ProbabilityScheduleDomain p) (t : ℕ) : 0 < p t :=
  (h t).1

/-- A schedule in the probability domain is at most one at each time. -/
theorem ProbabilityScheduleDomain_le_one (p : ℕ → ℝ)
    (h : ProbabilityScheduleDomain p) (t : ℕ) : p t ≤ 1 :=
  (h t).2

end SOptLib
