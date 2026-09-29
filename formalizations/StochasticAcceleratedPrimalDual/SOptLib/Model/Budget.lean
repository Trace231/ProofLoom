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

/-- Normalized finite-window stochastic gap envelope.

The envelope scales an initial potential by a finite output-window denominator
and adds the window sum of a linear zero-mean noise term and a quadratic
second-moment noise term.

Layer: Model | Concept: Objective
Proof: (definitional construction; normalized finite-window initial-potential
  plus stochastic linear and quadratic noise envelope)
Source: Stochastic mirror-descent finite-window expected-gap envelopes and
  Mathlib finite sums over real scalar budgets
Used in: stochastic block mirror descent expected output-gap envelope before
  martingale cancellation and quadratic oracle-budget bounding
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def finiteWindowStochasticGapEnvelope
    {Omega τ : Type*}
    (times : Finset τ) (η : τ → ℝ) (W initial : ℝ)
    (δ δbar : τ → Omega → ℝ) : Omega → ℝ :=
  fun omega =>
    W⁻¹ *
      (initial +
        Finset.sum times (fun k =>
          η k * δ k omega + (1 / 2 : ℝ) * η k ^ 2 * δbar k omega))

/-- The finite-window stochastic gap envelope unfolds to its normalized sum formula.

Layer: Model | Gap: Level 0 (finite-window stochastic envelope unfolding)
Proof: by rfl after unfolding `finiteWindowStochasticGapEnvelope`.
Source: Stochastic mirror-descent finite-window expected-gap envelopes and
  Mathlib finite sums over real scalar budgets
Used in: stochastic block mirror descent expected output-gap envelope before
  martingale cancellation and quadratic oracle-budget bounding
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem finiteWindowStochasticGapEnvelope_def
    {Omega τ : Type*}
    (times : Finset τ) (η : τ → ℝ) (W initial : ℝ)
    (δ δbar : τ → Omega → ℝ) :
    finiteWindowStochasticGapEnvelope times η W initial δ δbar =
      (fun omega =>
        W⁻¹ *
          (initial +
            Finset.sum times (fun k =>
              η k * δ k omega + (1 / 2 : ℝ) * η k ^ 2 * δbar k omega))) := by
  rfl

-- Promoted from SAPD Phase 3 staging (batch 1): primal-dual budget formulas.


-- Generalization plan (G0):
-- G0.1 naming: primalDualExpectedGapBudget (orig was:
--   sapdExpectedGapBudgetQ0 / Q0). The staged name drops the paper-local
--   `Q0` label and algorithm acronym while keeping the recognized convergence
--   budget concept.
-- G0.2 typeclass level used:
--   E: no carrier-space typeclass is required; the closed form depends only on
--     scalar schedules, Bregman-diameter bounds, and oracle variance scales.
--   measure: no measure abstraction is required; expectations have already
--     been reduced by callers to this deterministic real-valued budget.
--   convexity: no convexity hypothesis is required for the scalar budget
--     formula; convexity/Bregman assumptions are consumed before this object.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual expected saddle-gap bound after
--      martingale terms and square-noise terms are collected
--   2. stochastic mirror-prox or primal-dual mirror-descent two-block expected
--      gap bounds with separate primal and dual stepsize schedules
-- G0.4 search trace:
--   queries: ["expected gap budget",
--     "closed form stochastic primal dual finite sum budget"]
--   top hits: ["acceleratedExpectedGapBudget",
--     "acceleratedExpectedGapBudget_def",
--     "accelerated_expected_gap_bound_of_pathwise_telescope",
--     "expectedObjectiveGap",
--     "abs_inner_block_sum_le_sum_dual_bound_mul_radius",
--     "active_sum_objective_drop_add_scalar_budget"]
--   coverage: partial — `acceleratedExpectedGapBudget` covers the one-block
--     AC-SA Γ/α/curvature budget, while this definition names a distinct
--     two-block primal-dual η/τ finite-noise budget with p/q denominators.
-- G0.4 not-a-thin-wrapper rationale: this definition introduces the reusable
--   two-block expected-gap budget formula; it is not a renaming or
--   specialization of an existing Mathlib or SOptLib declaration.
-- G0.5 structural-content rationale: the definition keeps the deterministic
--   diameter contribution and the finite primal/dual variance accumulation as
--   one named convergence-rate object.
-- G0.5c thin-wrapper self-detect: clean — body is a multi-term stochastic
--   optimization budget formula with a finite schedule sum, not a direct alias
--   of a Mathlib primitive or existing SOptLib entry.
-- G0.5d minimal-hypothesis check: all already minimal; there are no hypotheses.

/-- Closed-form two-block expected saddle-gap budget for primal-dual methods.

The budget scales primal and dual Bregman-diameter bounds by the terminal
`beta * gamma` normalizer, then adds the finite primal and dual oracle-variance
accumulation with the usual `p` and `q` Young-inequality denominators.

Layer: Model | Concept: Objective
Proof: (definitional construction; two-block expected-gap convergence budget
  assembled from diameter terms and finite variance sums)
Source: stochastic primal-dual mirror and accelerated saddle-point convergence
  budgets with finite weighted oracle-noise accumulation
Used in: stochastic accelerated primal-dual expected saddle-gap bound after
  reducing pathwise telescope and martingale-noise estimates to scalar terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def primalDualExpectedGapBudget
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ) : ℝ :=
  (beta t * gamma t)⁻¹ *
      (4 * gamma t / eta t * D_X ^ 2 +
        4 * gamma t / tau t * D_Y ^ 2) +
    (1 / (2 * beta t * gamma t)) *
      Finset.sum (Finset.Icc 1 t) (fun i =>
        ((2 - q) * eta i * gamma i / (1 - q)) * sigmaX ^ 2 +
          ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2)

/-- The two-block primal-dual expected-gap budget unfolds to its finite-sum formula.

Layer: Model | Gap: Level 0 (two-block expected-gap budget unfolding)
Proof: by rfl after unfolding `primalDualExpectedGapBudget`.
Source: Mathlib finite sums over natural intervals and real field arithmetic
  for stochastic primal-dual convergence budgets
Used in: stochastic accelerated primal-dual expected saddle-gap rate-term
  algebra where the local `Q_0(t)` expression is exposed as a named budget
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem primalDualExpectedGapBudget_def
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ) :
    primalDualExpectedGapBudget beta gamma eta tau D_X D_Y sigmaX sigmaY p q t =
      (beta t * gamma t)⁻¹ *
          (4 * gamma t / eta t * D_X ^ 2 +
            4 * gamma t / tau t * D_Y ^ 2) +
        (1 / (2 * beta t * gamma t)) *
          Finset.sum (Finset.Icc 1 t) (fun i =>
            ((2 - q) * eta i * gamma i / (1 - q)) * sigmaX ^ 2 +
              ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2) := by
  rfl

-- Generalization plan (G0):
-- G0.1 naming: primalDualExpectedGapBudgetWithPrimalNoiseBudget (orig was:
--   sapdExpectedGapBudgetQ0WithPrimalBudget / Q0WithPrimalBudget). The staged
--   name removes the algorithm acronym and `Q0` paper label, and names the
--   mathematical object: a two-block expected-gap budget with an indexed
--   primal noise budget.
-- G0.2 typeclass level used:
--   E: no carrier-space typeclass is required; the formula is a deterministic
--     scalar convergence-rate budget after all Hilbert-space estimates have
--     been reduced to diameter and noise-budget scalars.
--   measure: no measure abstraction is required; expectations are already
--     discharged before callers instantiate this deterministic closed form.
--   convexity: no convexity hypothesis is required for the scalar budget;
--     convexity and Bregman geometry enter only through the supplied diameter
--     bounds `D_X` and `D_Y`.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual expected saddle-gap bounds with
--      generated or same-sample primal oracle residual budgets
--   2. stochastic mirror-prox or primal-dual mirror-descent analyses where
--      primal and dual square-noise terms have different per-index estimates
-- G0.4 search trace:
--   queries: ["expected gap budget", "primal noise budget finite sum",
--     "closed form stochastic primal dual finite sum budget"]
--   top hits: ["primalDualExpectedGapBudget",
--     "primalDualExpectedGapBudget_def",
--     "primalDualExpectedGapBudget_nonneg",
--     "acceleratedExpectedGapBudget",
--     "finite_window_zero_mean_plus_quadratic_noise_integral_bound"]
--   coverage: partial — `primalDualExpectedGapBudget` covers the constant
--     primal variance scale `sigmaX ^ 2`, while this definition exposes an
--     arbitrary indexed primal square-noise budget `primalNoiseBudget i`.
-- G0.4 not-a-thin-wrapper rationale: this definition adds a reusable indexed
--   primal-noise quantifier structure to the two-block expected-gap budget,
--   not a rename or specialization of the existing constant-variance budget.
-- G0.5 structural-content rationale: the definition keeps the deterministic
--   terminal diameter contribution and the finite indexed primal/constant dual
--   noise accumulation as one named convergence-rate object.
-- G0.5c thin-wrapper self-detect: clean — body is a multi-term stochastic
--   optimization budget formula with an indexed finite schedule sum, and the
--   companion theorems include compatibility and nonnegativity API.
-- G0.5d minimal-hypothesis check: all already minimal; the def has no
--   hypotheses and the nonnegativity theorem uses only pointwise scalar
--   nonnegativity on the finite window.

/-- Closed-form two-block expected saddle-gap budget with indexed primal noise.

The budget is the primal-dual expected-gap rate term where the primal
square-noise contribution may vary by index, while the dual contribution uses a
single variance scale. This covers generated or same-sample reconstructions
whose primal oracle residual cannot be collapsed to a constant variance.

Layer: Model | Concept: Objective
Proof: (definitional construction; two-block expected-gap convergence budget
  assembled from diameter terms, an indexed primal noise budget, and a finite
  dual variance sum)
Source: stochastic primal-dual mirror and accelerated saddle-point convergence
  budgets with finite weighted oracle-noise accumulation
Used in: stochastic accelerated primal-dual expected saddle-gap bound after
  replacing the primal oracle variance by per-index mixed-center residual
  budgets
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def primalDualExpectedGapBudgetWithPrimalNoiseBudget
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y : ℝ) (primalNoiseBudget : ℕ → ℝ)
    (sigmaY p q : ℝ) (t : ℕ) : ℝ :=
  (beta t * gamma t)⁻¹ *
      (4 * gamma t / eta t * D_X ^ 2 +
        4 * gamma t / tau t * D_Y ^ 2) +
    (1 / (2 * beta t * gamma t)) *
      Finset.sum (Finset.Icc 1 t) (fun i =>
        ((2 - q) * eta i * gamma i / (1 - q)) * primalNoiseBudget i +
          ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2)

/-- The indexed-primal two-block expected-gap budget unfolds to its finite-sum formula.

Layer: Model | Gap: Level 0 (indexed-primal expected-gap budget unfolding)
Proof: by rfl after unfolding `primalDualExpectedGapBudgetWithPrimalNoiseBudget`.
Source: Mathlib finite sums over natural intervals and real field arithmetic
  for stochastic primal-dual convergence budgets
Used in: stochastic accelerated primal-dual expected saddle-gap rate algebra
  where the local corrected `Q_0(t)` expression is exposed as a named budget
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem primalDualExpectedGapBudgetWithPrimalNoiseBudget_def
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y : ℝ) (primalNoiseBudget : ℕ → ℝ)
    (sigmaY p q : ℝ) (t : ℕ) :
    primalDualExpectedGapBudgetWithPrimalNoiseBudget beta gamma eta tau
        D_X D_Y primalNoiseBudget sigmaY p q t =
      (beta t * gamma t)⁻¹ *
          (4 * gamma t / eta t * D_X ^ 2 +
            4 * gamma t / tau t * D_Y ^ 2) +
        (1 / (2 * beta t * gamma t)) *
          Finset.sum (Finset.Icc 1 t) (fun i =>
            ((2 - q) * eta i * gamma i / (1 - q)) *
                primalNoiseBudget i +
              ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2) := by
  rfl

/-- A constant primal noise budget recovers the standard two-block budget.

Layer: Model | Gap: Level 0 (constant primal-noise budget compatibility)
Proof: by rfl after unfolding both expected-gap budget definitions.
Source: Mathlib finite sums over natural intervals and real field arithmetic
  for stochastic primal-dual convergence budgets
Used in: stochastic accelerated primal-dual proofs that switch between the
  source theorem's constant primal variance and a generated per-index primal
  residual budget
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem primalDualExpectedGapBudgetWithPrimalNoiseBudget_const
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ) :
    primalDualExpectedGapBudgetWithPrimalNoiseBudget beta gamma eta tau
        D_X D_Y (fun _ => sigmaX ^ 2) sigmaY p q t =
      primalDualExpectedGapBudget beta gamma eta tau D_X D_Y sigmaX sigmaY p q t := by
  rfl

/-- The indexed-primal two-block budget is nonnegative under pointwise scalar
nonnegativity of all deterministic and variance weights.

Layer: Model | Gap: Level 0 (indexed-primal expected-gap budget nonnegativity)
Proof: finite-sum nonnegativity combines the indexed primal budget bounds with
  nonnegativity of the dual variance square.
Source: scalar side conditions used after schedule and Young-denominator
  assumptions have been discharged in stochastic primal-dual rate proofs
Used in: stochastic accelerated primal-dual expected saddle-gap bounds where
  per-index primal residual estimates form a nonnegative error envelope
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem primalDualExpectedGapBudgetWithPrimalNoiseBudget_nonneg
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y : ℝ) (primalNoiseBudget : ℕ → ℝ)
    (sigmaY p q : ℝ) (t : ℕ)
    (hscale : 0 ≤ (beta t * gamma t)⁻¹)
    (hdiamX : 0 ≤ 4 * gamma t / eta t)
    (hdiamY : 0 ≤ 4 * gamma t / tau t)
    (hvarScale : 0 ≤ 1 / (2 * beta t * gamma t))
    (hvarX :
      ∀ i ∈ Finset.Icc 1 t,
        0 ≤ (2 - q) * eta i * gamma i / (1 - q))
    (hprimal :
      ∀ i ∈ Finset.Icc 1 t, 0 ≤ primalNoiseBudget i)
    (hvarY :
      ∀ i ∈ Finset.Icc 1 t,
        0 ≤ (2 - p) * tau i * gamma i / (1 - p)) :
    0 ≤ primalDualExpectedGapBudgetWithPrimalNoiseBudget beta gamma eta tau
      D_X D_Y primalNoiseBudget sigmaY p q t := by
  rw [primalDualExpectedGapBudgetWithPrimalNoiseBudget_def]
  apply add_nonneg
  · exact mul_nonneg hscale
      (add_nonneg (mul_nonneg hdiamX (sq_nonneg D_X))
        (mul_nonneg hdiamY (sq_nonneg D_Y)))
  · exact mul_nonneg hvarScale
      (Finset.sum_nonneg fun i hi =>
        add_nonneg (mul_nonneg (hvarX i hi) (hprimal i hi))
          (mul_nonneg (hvarY i hi) (sq_nonneg sigmaY)))

-- Generalization plan (G0):
-- G0.1 naming: primalDualTailDeviationBudget (orig was:
--   sapdHighProbabilityBudget / Q1). The staged name removes the algorithm
--   acronym and paper-local `Q1` label, and names the deterministic tail
--   deviation budget used in a two-block primal-dual high-probability bound.
-- G0.2 typeclass level used:
--   E: no carrier-space typeclass is required; the Hilbert-space estimates
--     have already been reduced to scalar diameter and oracle-scale bounds.
--   measure: no measure abstraction is required; martingale tail estimates
--     have already been reduced by callers to this deterministic budget.
--   convexity: no convexity hypothesis is required for the scalar closed
--     form; convexity and Bregman geometry enter only through `D_X` and `D_Y`.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual saddle-gap high-probability bounds
--      after martingale increments are collapsed to sub-Gaussian scales
--   2. stochastic mirror-prox or primal-dual mirror-descent tail bounds with
--      separate primal and dual stepsize schedules and Young-denominator terms
-- G0.4 search trace:
--   queries: ["high probability budget",
--     "closed form tail deviation finite sum budget"]
--   top hits: ["theorem_4_8_high_probability_fixedDomain_mixedCenter_corrected_obligation",
--     "sapd_high_probability_displayed_run_extension_claim",
--     "jointStrictTailProbability_eq_finiteSum",
--     "finiteStoppingStrictTailProbabilitySum",
--     "finiteResidualMomentBudget.exists_integrable_sum_and_integral_sum_le"]
--   coverage: partial — existing hits cover event/claim shapes, finite
--     stopping tail-probability expansions, or residual moment projections;
--     none names the closed-form two-block scalar deviation budget combining
--     diameter radii with finite primal/dual variance accumulation.
-- G0.4 not-a-thin-wrapper rationale: this definition introduces the reusable
--   two-block tail-deviation budget formula; it is not a rename or
--   specialization of a Mathlib or SOptLib tail-probability expansion.
-- G0.5 structural-content rationale: the definition keeps the radius-type
--   martingale scale and the finite Young-weighted variance accumulation as
--   one named convergence-rate object.
-- G0.5c thin-wrapper self-detect: clean — body is a multi-term stochastic
--   optimization budget formula with a square-root finite schedule sum and a
--   separate finite variance sum, not a direct alias of a primitive.
-- G0.5d minimal-hypothesis check: all already minimal; the def has no
--   hypotheses and the nonnegativity theorem uses only pointwise scalar
--   nonnegativity on the finite window.

/-- Closed-form two-block primal-dual tail-deviation budget.

The budget is the additive scale multiplying the deviation parameter in a
high-probability saddle-gap bound: a radius term from the martingale
sub-Gaussian scales plus a finite primal/dual variance accumulation with
Young-inequality denominators.

Layer: Model | Concept: Objective
Proof: (definitional construction; two-block tail-deviation convergence budget
  assembled from diameter radii, square-root schedule mass, and finite
  variance sums)
Source: stochastic primal-dual mirror and accelerated saddle-point
  high-probability convergence budgets with finite weighted oracle-noise
  accumulation
Used in: stochastic accelerated primal-dual high-probability saddle-gap bound
  after martingale increments and square-noise estimates are reduced to scalar
  terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def primalDualTailDeviationBudget
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ) : ℝ :=
  (beta t * gamma t)⁻¹ *
      (2 * sigmaX * D_X + Real.sqrt 2 * sigmaY * D_Y) *
        Real.sqrt (2 * Finset.sum (Finset.Icc 1 t) (fun i => gamma i ^ 2)) +
    (1 / (2 * beta t * gamma t)) *
      Finset.sum (Finset.Icc 1 t) (fun i =>
        ((2 - q) * eta i * gamma i / (1 - q)) * sigmaX ^ 2 +
          ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2)

/-- The two-block primal-dual tail-deviation budget unfolds to its finite-sum formula.

Layer: Model | Gap: Level 0 (two-block tail-deviation budget unfolding)
Proof: by rfl after unfolding `primalDualTailDeviationBudget`.
Source: Mathlib finite sums over natural intervals, real square roots, and real
  field arithmetic for stochastic primal-dual tail budgets
Used in: stochastic accelerated primal-dual high-probability saddle-gap
  rate-term algebra where the local `Q_1(t)` expression is exposed as a named
  budget
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem primalDualTailDeviationBudget_def
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ) :
    primalDualTailDeviationBudget beta gamma eta tau D_X D_Y sigmaX sigmaY p q t =
      (beta t * gamma t)⁻¹ *
          (2 * sigmaX * D_X + Real.sqrt 2 * sigmaY * D_Y) *
            Real.sqrt (2 * Finset.sum (Finset.Icc 1 t) (fun i => gamma i ^ 2)) +
        (1 / (2 * beta t * gamma t)) *
          Finset.sum (Finset.Icc 1 t) (fun i =>
            ((2 - q) * eta i * gamma i / (1 - q)) * sigmaX ^ 2 +
              ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2) := by
  rfl

/-- The two-block primal-dual tail-deviation budget is nonnegative when the
scalar scales, radii, and finite-window variance weights are nonnegative.

Layer: Model | Gap: Level 0 (two-block tail-deviation budget nonnegativity)
Proof: combine nonnegativity of real square roots, squares, and finite sums.
Source: scalar side conditions used after schedule and Young-denominator
  assumptions have been discharged in stochastic primal-dual tail proofs
Used in: stochastic accelerated primal-dual high-probability saddle-gap bounds
  where the closed-form deviation budget is used as a nonnegative error scale
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem primalDualTailDeviationBudget_nonneg
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ)
    (hscale : 0 ≤ (beta t * gamma t)⁻¹)
    (hsigmaX : 0 ≤ sigmaX) (hDX : 0 ≤ D_X)
    (hsigmaY : 0 ≤ sigmaY) (hDY : 0 ≤ D_Y)
    (hvarScale : 0 ≤ 1 / (2 * beta t * gamma t))
    (hvarX :
      ∀ i ∈ Finset.Icc 1 t,
        0 ≤ (2 - q) * eta i * gamma i / (1 - q))
    (hvarY :
      ∀ i ∈ Finset.Icc 1 t,
        0 ≤ (2 - p) * tau i * gamma i / (1 - p)) :
    0 ≤ primalDualTailDeviationBudget beta gamma eta tau D_X D_Y sigmaX sigmaY p q t := by
  rw [primalDualTailDeviationBudget_def]
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg hscale
        (add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsigmaX) hDX)
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hsigmaY) hDY)))
      (Real.sqrt_nonneg _)
  · exact mul_nonneg hvarScale
      (Finset.sum_nonneg fun i hi =>
        add_nonneg (mul_nonneg (hvarX i hi) (sq_nonneg sigmaX))
          (mul_nonneg (hvarY i hi) (sq_nonneg sigmaY)))
