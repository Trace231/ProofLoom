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


-- Generalization plan (G0):
-- concept/name: objective-Bregman budget nonnegativity; orig was
--   `smooth_theorem59D0_nonneg_of_optimal`, renamed away from the smooth
--   branch, theorem number, and setup-local `D0` name while retaining the
--   mathematical budget shape.
-- generality used: scalar objective gap, Bregman term, smoothness scale, and
--   two nonnegative coefficients over an ordered nonunital nonassociative
--   semiring with monotone nonnegative multiplication; no carrier, measure,
--   independence, integrability, topology, norm, inner product, convexity,
--   oracle, or finite-dimensional hypotheses are used.
-- portable call pattern: accelerated and mirror-descent convergence
--   initializations with budgets `a * gap + b * L * breg` call this after
--   proving the objective gap from optimality, Bregman nonnegativity from
--   convexity or distance-generation assumptions, and smoothness-scale
--   nonnegativity from model parameters.
-- counterargument checked: this is a short scalar wrapper, but it is not
--   paper-local traceability because the theorem removes all setup fields and
--   captures a recurring convergence-initialization proof step; Mathlib's
--   primitive `add_nonneg` and `mul_nonneg` are lower-level ingredients and do
--   not name the objective/Bregman budget boundary used by stochastic
--   optimization proofs.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and Mathlib
--   LeanSearch for objective gap budget, Bregman budget nonnegativity, and
--   nonnegative linear combination/product; top hits were `add_nonneg`,
--   `mul_nonneg`, existing Bregman nonnegativity lemmas, and unrelated budget
--   definitions, with no full statement covering `a * gap + b * L * breg`.
-- minimal hypotheses: the algorithm-specific optimality and Bregman proofs are
--   replaced by pointwise nonnegativity facts; the scalar class uses the local
--   shared-zero semiring bundle needed to combine `add_nonneg` and
--   `mul_nonneg` coherently.

/-- An objective-gap plus Bregman budget is nonnegative when all factors are
nonnegative.

The scalar budget `a * gap + b * L * breg` abstracts the initial Lyapunov
quantity used in convergence proofs: a nonnegative objective gap plus a
nonnegative smoothness-scaled Bregman contribution.

Layer: Model | Gap: Level 0 (objective-Bregman budget nonnegativity)
Proof: combine Mathlib ordered scalar primitives `mul_nonneg` and `add_nonneg`
  for the two nonnegative summands.
Source: Mathlib ordered arithmetic for nonnegative sums and products
Used in: variance-reduced accelerated gradient descent initialization of the
  objective-gap and Bregman Lyapunov budget
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem objective_bregman_budget_nonneg
    {R : Type*} [NonUnitalNonAssocSemiring R] [Preorder R] [AddLeftMono R]
    [PosMulMono R]
    (gap breg L a b : R)
    (hgap_nonneg : 0 ≤ gap)
    (hbreg_nonneg : 0 ≤ breg)
    (hL_nonneg : 0 ≤ L)
    (ha_nonneg : 0 ≤ a)
    (hb_nonneg : 0 ≤ b) :
    0 ≤ a * gap + b * L * breg := by
  exact
    add_nonneg
      (mul_nonneg ha_nonneg hgap_nonneg)
      (mul_nonneg (mul_nonneg hb_nonneg hL_nonneg) hbreg_nonneg)

end SOptLib

-- Merged from Staging/strongConvexInitialVarianceBudget.lean
-- Generalization plan (G0):
-- concept/name: strong-convexity initial variance budget; orig was
--   `Delta0Sigma0`, renamed away from paper-local delta notation and the
--   setup-local `sigma0` subscript while retaining the mathematical role of an
--   initial Lyapunov budget for strongly convex finite-sum methods.
-- generality used: scalar field parameters for the strong-convexity modulus,
--   component count, initial Bregman term, initial objective gap, and initial
--   variance scale; no carrier, measure, independence, integrability,
--   topology, norm, inner product, convexity, oracle, or finite-dimensional
--   hypotheses are used by the definitional construction.
-- portable call pattern: strongly convex finite-sum, variance-reduced, and
--   mirror/proximal gradient initialization steps can call the same closed
--   budget after changing `mu`, the component count `m`, the initial Bregman
--   contribution, the initial objective gap, and the initial variance scale.
-- counterargument checked: this is a single formula, but it is a named model
--   object rather than paper traceability: future convergence statements can
--   state rates in terms of this initial budget instead of repeatedly exposing
--   `mu * initialBregman + initialGap + sigma0 ^ 2 / (m * mu)`.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and Mathlib
--   LeanSearch for initial variance budget, strong convex budget, sigma
--   objective gap Bregman, and the exact `mu*bregman + gap + sigma^2/(m*mu)`
--   shape; hits were lower-level budget objects, `objective_bregman_budget_nonneg`,
--   and Mathlib strong-convexity/variance APIs, with no full definition
--   covering this closed-form initial variance budget.
-- minimal hypotheses: all algorithm-specific setup fields are replaced by
--   scalar arguments; no positivity hypotheses are needed to define the
--   totalized division formula.

/-- Closed-form initial variance budget for a strongly convex finite-sum method.

The budget combines a strong-convexity-scaled initial Bregman term, an initial
objective gap, and the initial variance scale divided by the component-count
and strong-convexity modulus product.

Layer: Model | Concept: Objective
Proof: (definitional construction; closed-form scalar initial variance budget)
Source: finite-sum strongly convex stochastic-optimization Lyapunov budgets and
  Mathlib field division notation
Used in: randomized gradient extrapolation initialization of the strongly
  convex expected-gap and stale-gradient variance budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
noncomputable def strongConvexInitialVarianceBudget
    {R : Type*} [Field R]
    (mu m initialBregman initialGap sigma0 : R) : R :=
  mu * initialBregman + initialGap + sigma0 ^ 2 / (m * mu)

/-- The strongly convex initial variance budget unfolds to its scalar formula.

Layer: Model | Gap: Level 0 (strongly convex initial variance budget unfolding)
Proof: by rfl after unfolding `strongConvexInitialVarianceBudget`.
Source: finite-sum strongly convex stochastic-optimization Lyapunov budgets and
  Mathlib field division notation
Used in: randomized gradient extrapolation initialization of the strongly
  convex expected-gap and stale-gradient variance budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem strongConvexInitialVarianceBudget_def
    {R : Type*} [Field R]
    (mu m initialBregman initialGap sigma0 : R) :
    strongConvexInitialVarianceBudget mu m initialBregman initialGap sigma0 =
      mu * initialBregman + initialGap + sigma0 ^ 2 / (m * mu) := by
  rfl

/-- Nonnegativity of the strongly convex initial variance budget.

Layer: Model | Gap: Level 0 (strongly convex initial variance budget
nonnegativity)
Proof: the scaled Bregman and objective-gap terms are nonnegative by
  multiplication and addition, and the variance term is nonnegative by
  square/division nonnegativity.
Source: finite-sum strongly convex stochastic-optimization Lyapunov budgets and
  Mathlib ordered-field nonnegativity lemmas
Used in: randomized gradient extrapolation initialization of the strongly
  convex expected-gap and stale-gradient variance budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem strongConvexInitialVarianceBudget_nonneg
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {mu m initialBregman initialGap sigma0 : R}
    (hmu : 0 ≤ mu) (hm : 0 ≤ m)
    (hBregman : 0 ≤ initialBregman) (hGap : 0 ≤ initialGap) :
    0 ≤ strongConvexInitialVarianceBudget mu m initialBregman initialGap sigma0 := by
  rw [strongConvexInitialVarianceBudget_def]
  exact add_nonneg (add_nonneg (mul_nonneg hmu hBregman) hGap)
    (div_nonneg (sq_nonneg sigma0) (mul_nonneg hm hmu))

-- Merged from Staging/staleGradientGeometricInitialBudget.lean
-- Generalization plan (G0):
-- concept/name: stale-gradient geometric initial budget; orig was
--   `DeltaTilde0Sigma0`, renamed away from paper-local delta notation while
--   retaining the mathematical role of a finite-window initial budget with a
--   geometrically decaying stale-gradient residual sum.
-- generality used: scalar field parameters for the output window, theta/tau/
--   eta/alpha schedules, component count, initial objective gap, initial
--   Bregman term, and initial stale-gradient scale; no carrier, measure,
--   independence, integrability, topology, norm, inner product, convexity,
--   oracle, or finite-dimensional hypotheses are used by the definitional
--   construction.
-- portable call pattern: randomized incremental, variance-reduced, and
--   block-coordinate stochastic methods can call the same closed initial
--   budget after changing the finite output window, schedule functions,
--   component count, initial gap/Bregman quantities, and stale-gradient scale.
-- counterargument checked: this is a single formula, but it is not merely
--   paper traceability because it gives future convergence statements a named
--   model object for the initial objective/Bregman terms plus the geometric
--   stale-residual accumulation, instead of exposing the full finite sum at
--   every theorem boundary.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and the target file
--   for stale/geometric/initial budget, theta/tau/eta/alpha, and sigma0; the
--   closest hit was `strongConvexInitialVarianceBudget`, which lacks the
--   finite-window stale-residual sum. Mathlib LeanSearch for finite geometric
--   stale-gradient budgets returned geometric-sum lemmas such as
--   `Nat.geomSum_eq`, `geom_sum_of_one_lt`, and `tsum_geometric_of_lt_one`,
--   with no definition covering this stochastic-optimization budget object.
-- minimal hypotheses: all setup fields are replaced by scalar schedules and a
--   finite-window map; positivity of eta denominators is not needed for the
--   totalized field-division definition.

/-- Closed-form initial budget with a geometric stale-gradient residual sum.

The budget combines an initial objective gap, an eta-scaled initial Bregman
term, and a finite output-window sum of stale-gradient residual weights with
geometric factor `((m - 1) / m) ^ (t - 1)`.

Layer: Model | Concept: Objective
Proof: (definitional construction; closed-form scalar initial budget with a
  finite geometric stale-residual accumulation)
Source: finite-sum stochastic-optimization Lyapunov budgets and Mathlib finite
  sums, powers, and field division notation
Used in: randomized gradient extrapolation initialization of the
  finite-window stale-gradient residual budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
noncomputable def staleGradientGeometricInitialBudget
    {K R : Type*} [Field R]
    (window : K → Finset ℕ)
    (theta tau eta alpha : ℕ → R)
    (m initialGap initialBregman sigma0 : R) (k : K) : R :=
  theta 1 * (m * (1 + tau 1) - 1) * initialGap +
    theta 1 * eta 1 * initialBregman +
    Finset.sum (window k) (fun t =>
      (((m - 1) / m) ^ (t - 1)) *
        (2 * theta t * alpha (t + 1) / (m * eta (t + 1))) * sigma0 ^ 2)

/-- The stale-gradient geometric initial budget unfolds to its finite-sum formula.

Layer: Model | Gap: Level 0 (stale-gradient geometric initial budget unfolding)
Proof: by rfl after unfolding `staleGradientGeometricInitialBudget`.
Source: finite-sum stochastic-optimization Lyapunov budgets and Mathlib finite
  sums, powers, and field division notation
Used in: randomized gradient extrapolation initialization of the
  finite-window stale-gradient residual budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem staleGradientGeometricInitialBudget_def
    {K R : Type*} [Field R]
    (window : K → Finset ℕ)
    (theta tau eta alpha : ℕ → R)
    (m initialGap initialBregman sigma0 : R) (k : K) :
    staleGradientGeometricInitialBudget window theta tau eta alpha
        m initialGap initialBregman sigma0 k =
      theta 1 * (m * (1 + tau 1) - 1) * initialGap +
        theta 1 * eta 1 * initialBregman +
        Finset.sum (window k) (fun t =>
          (((m - 1) / m) ^ (t - 1)) *
            (2 * theta t * alpha (t + 1) / (m * eta (t + 1))) * sigma0 ^ 2) := by
  rfl

/-- The stale-gradient geometric initial budget is nonnegative when each
initial contribution and each stale-gradient coefficient is nonnegative.

Layer: Model | Gap: Level 0 (stale-gradient geometric initial budget
nonnegativity)
Proof: finite sums of nonnegative terms are nonnegative.
Source: finite-sum stochastic-optimization Lyapunov budgets and Mathlib finite
  sum/order API
Used in: randomized gradient extrapolation initialization of the
  finite-window stale-gradient residual budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem staleGradientGeometricInitialBudget_nonneg
    {K R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (window : K → Finset ℕ)
    (theta tau eta alpha : ℕ → R)
    (m initialGap initialBregman sigma0 : R) (k : K)
    (hgap : 0 ≤ initialGap)
    (hBregman : 0 ≤ initialBregman)
    (hTheta_one : 0 ≤ theta 1)
    (hInitialCoeff : 0 ≤ m * (1 + tau 1) - 1)
    (hEta_one : 0 ≤ eta 1)
    (hGeom : 0 ≤ (m - 1) / m)
    (hTheta : ∀ t ∈ window k, 0 ≤ theta t)
    (hAlpha : ∀ t ∈ window k, 0 ≤ alpha (t + 1))
    (hDen : ∀ t ∈ window k, 0 < m * eta (t + 1)) :
    0 ≤ staleGradientGeometricInitialBudget window theta tau eta alpha
      m initialGap initialBregman sigma0 k := by
  have hInitialGap :
      0 ≤ theta 1 * (m * (1 + tau 1) - 1) * initialGap := by
    exact mul_nonneg (mul_nonneg hTheta_one hInitialCoeff) hgap
  have hInitialBregman : 0 ≤ theta 1 * eta 1 * initialBregman := by
    exact mul_nonneg (mul_nonneg hTheta_one hEta_one) hBregman
  have hStale :
      0 ≤ Finset.sum (window k) (fun t =>
        (((m - 1) / m) ^ (t - 1)) *
          (2 * theta t * alpha (t + 1) / (m * eta (t + 1))) * sigma0 ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro t ht
    have hPow : 0 ≤ (((m - 1) / m) ^ (t - 1)) := pow_nonneg hGeom _
    have hCoeff :
        0 ≤ 2 * theta t * alpha (t + 1) / (m * eta (t + 1)) := by
      have hNum : 0 ≤ 2 * theta t * alpha (t + 1) := by
        exact mul_nonneg (mul_nonneg (by norm_num) (hTheta t ht)) (hAlpha t ht)
      exact div_nonneg hNum (hDen t ht).le
    have hSigma : 0 ≤ sigma0 ^ 2 := sq_nonneg sigma0
    exact mul_nonneg (mul_nonneg hPow hCoeff) hSigma
  simpa [staleGradientGeometricInitialBudget] using
    add_nonneg (add_nonneg hInitialGap hInitialBregman) hStale
