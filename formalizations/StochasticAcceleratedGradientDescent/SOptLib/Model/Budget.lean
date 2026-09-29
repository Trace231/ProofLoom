import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import SOptLib.Model.Iterates

/-- Objective-gap radius obtained by scaling an initial objective gap by a
positive smoothness parameter and taking the square root.

`objectiveGapRadius initialValue optimumValue L` names the paper quantity
`sqrt ((initialValue - optimumValue) / L)` without committing to a particular
objective, feasible carrier, or optimizer witness.

Layer: Model | Concept: Objective
Proof: (definitional construction; scalar objective-gap radius wrapper)
Source: Mathlib real square-root and ordered-field APIs for objective-gap
  scaling
Used in: nonconvex stochastic mirror descent initialization of the
  objective-gap radius `D_Psi`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def objectiveGapRadius
    (initialValue optimumValue L : ℝ) : ℝ :=
  Real.sqrt ((initialValue - optimumValue) / L)

/-- The objective-gap radius unfolds to the square root of the scaled objective gap.

For abstract real objective values, the staged radius wrapper is definitionally
the paper quantity `sqrt ((initialValue - optimumValue) / L)`, independent of
the concrete objective, feasible carrier, or optimizer witness.

Layer: Model | Gap: Level 0 (objective-gap radius formula)
Proof: by rfl after unfolding `objectiveGapRadius`.
Source: Mathlib real square-root and ordered-field APIs for objective-gap scaling
Used in: nonconvex stochastic mirror descent initialization of the objective-gap radius `D_Psi`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
theorem objectiveGapRadius_eq
    (initialValue optimumValue L : ℝ) :
    objectiveGapRadius initialValue optimumValue L =
      Real.sqrt ((initialValue - optimumValue) / L) := by
  rfl

/-- Closed-form one-run RSMD stationarity budget from the smoothness,
objective-gap radius, oracle variance scale, balancing radius, and SFO budget.

`rsmdBudgetBound L D sigma Dtilde Nbar` names the paper quantity
`𝓑_{\bar N}` appearing in the randomized stochastic mirror descent
one-run projected-gradient bound.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form real-valued budget combining
  deterministic descent and stochastic oracle variance terms)
Source: Mathlib real square-root, maximum, division, and ordered-field APIs for
  finite-budget stochastic approximation rates
Used in: randomized stochastic mirror descent one-run Markov stationarity bound
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def rsmdBudgetBound
    (L D sigma Dtilde : ℝ) (Nbar : ℕ) : ℝ :=
  16 * L * D ^ 2 / (Nbar : ℝ) +
    4 * Real.sqrt 6 * sigma / Real.sqrt (Nbar : ℝ) *
      (D ^ 2 / Dtilde +
        Dtilde *
          max 1 (Real.sqrt 6 * sigma /
            (4 * L * Dtilde * Real.sqrt (Nbar : ℝ))))

/-- Closed-form accelerated expected-gap budget from a positive-time Γ schedule.

The budget scales an initial Bregman/objective gap by `Γ_k / γ_1` and adds the
finite Γ-weighted oracle-noise accumulation with curvature denominator
`1 + μ γ_t - L α_t γ_t`.

Layer: Model | Concept: Objective
Proof: (definitional construction; Γ-weighted accelerated expected-gap budget)
Source: accelerated stochastic approximation convergence budgets with finite
  weighted sums over positive natural time
Used in: AC-SA expected suboptimality bound after reducing stochastic oracle
  terms to the displayed finite Γ-weighted scalar budget
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def acceleratedExpectedGapBudget
    (Gamma gamma alpha : {n : ℕ // 1 ≤ n} → ℝ)
    (initialGap oracleNormBound oracleStdDev mu L : ℝ)
    (k : {n : ℕ // 1 ≤ n}) : ℝ :=
  Gamma k / gamma SOptLib.positiveTimeOne * initialGap +
    Gamma k *
      Finset.sum (Finset.Icc 1 k.1).attach (fun t =>
        let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
        alpha τ * gamma τ * (oracleNormBound ^ 2 + oracleStdDev ^ 2) /
          (Gamma τ * (1 + mu * gamma τ - L * alpha τ * gamma τ)))

/-- The accelerated expected-gap budget unfolds to its Γ-weighted finite-sum formula.

Layer: Model | Gap: Level 0 (accelerated expected-gap budget unfolding)
Proof: by rfl after unfolding `acceleratedExpectedGapBudget`.
Source: Mathlib finite sums over natural intervals and real field arithmetic
Used in: AC-SA expected suboptimality bound after reducing stochastic oracle
  terms to the displayed finite Γ-weighted scalar budget
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedExpectedGapBudget_def
    (Gamma gamma alpha : {n : ℕ // 1 ≤ n} → ℝ)
    (initialGap oracleNormBound oracleStdDev mu L : ℝ)
    (k : {n : ℕ // 1 ≤ n}) :
    acceleratedExpectedGapBudget Gamma gamma alpha initialGap oracleNormBound
        oracleStdDev mu L k =
      Gamma k / gamma SOptLib.positiveTimeOne * initialGap +
        Gamma k *
          Finset.sum (Finset.Icc 1 k.1).attach (fun t =>
            let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
            alpha τ * gamma τ * (oracleNormBound ^ 2 + oracleStdDev ^ 2) /
              (Gamma τ * (1 + mu * gamma τ - L * alpha τ * gamma τ))) := by
  rfl

namespace SOptLib

/-- Denominator admissibility for a finite accelerated expected-error budget.

If the first stepsize is nonzero and, at every positive time in the finite
window, both the Γ weight and the curvature denominator are nonzero, then the
displayed finite sum over `{1, ..., k}` has all denominator witnesses needed
for checked real division.

Layer: Model | Gap: Level 1 (accelerated error-bound denominator admissibility)
Proof: reconstruct each natural index in `Finset.Icc 1 k` as a positive-time
  subtype, then combine the Γ and curvature nonzero facts with `mul_ne_zero`.
Source: Mathlib finite intervals over natural numbers and ordered-field
  denominator arithmetic for accelerated stochastic approximation rates
Used in: AC-SA expected suboptimality bound before exposing the Γ-weighted
  finite oracle-noise accumulation as a checked real sum
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_error_bound_denominators
    (gamma alpha : ℕ → ℝ)
    (Gamma : {n : ℕ // 1 ≤ n} → ℝ)
    (mu L : ℝ)
    (k : {n : ℕ // 1 ≤ n})
    (hgamma_one_ne : gamma 1 ≠ 0)
    (hGamma_ne : ∀ t (ht : t ∈ Finset.Icc 1 k.1),
      Gamma ⟨t, (Finset.mem_Icc.mp ht).1⟩ ≠ 0)
    (hcurvature_ne :
      ∀ t (ht : t ∈ Finset.Icc 1 k.1),
        1 + mu * gamma t - L * alpha t * gamma t ≠ 0) :
    gamma 1 ≠ 0 ∧
      (∀ t, (ht : t ∈ Finset.Icc 1 k.1) →
        Gamma ⟨t, (Finset.mem_Icc.mp ht).1⟩ *
          (1 + mu * gamma t - L * alpha t * gamma t) ≠ 0) := by
  refine ⟨hgamma_one_ne, ?_⟩
  intro t ht
  exact mul_ne_zero (hGamma_ne t ht) (hcurvature_ne t ht)

end SOptLib
