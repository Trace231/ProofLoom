import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic
import SOptLib.Model.Selection

namespace SOptLib

/-- Displayed AC-SA parameter relations for the coupled `q`, `α`, `γ`, and
`Γ` schedules.

This model predicate records exactly the source-level algebraic relations from
the AC-SA parameter display: `α₁ = 1`, Eq. (4.2.9), Eq. (4.2.10), and the
weight monotonicity condition Eq. (4.2.22). Denominator side conditions for
checked quotients are intentionally separate run-contract facts.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; bundle the displayed AC-SA schedule
  relations as a reusable predicate)
Source: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, AC-SA parameter display
Used in: stochastic accelerated gradient descent setup parameter assumptions
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
def acceleratedParameterRelations
    (Gamma : ℕ → ℝ)
    (q alpha gamma : ℕ → ℝ) (mu L : ℝ) : Prop :=
  alpha 1 = 1 ∧
    (∀ t, 1 ≤ t →
      q t * (1 - alpha t) * (1 + mu * gamma t) =
        alpha t * (1 - q t)) ∧
    (∀ t, 1 ≤ t →
      L * alpha t * gamma t < 1 + mu * gamma t) ∧
    (∀ t, 1 ≤ t →
      alpha (t + 1) * (gamma t * Gamma t) ≤
        (alpha t * (1 + mu * gamma t)) *
          (gamma (t + 1) * Gamma (t + 1)))

/-- Paper-facing independent run-count ceiling for a binary confidence split.

For a target failure probability `Λ`, this is the Theorem 6.7 run selector
`ceil (log (2 / Λ) / log 2)`, i.e. the number of independent runs needed for
the geometric tail term at base two.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form natural-number selector obtained
  by applying natural ceiling to a base-two logarithmic confidence requirement)
Source: Mathlib real logarithm, natural ceiling, and stochastic mirror descent
  confidence-splitting parameter choices
Used in: two-phase randomized stochastic mirror descent independent run-count
  selection in the Theorem 6.7 confidence specialization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def runCountChoice (Λ : ℝ) : ℕ :=
  Nat.ceil (Real.log (2 / Λ) / Real.log 2)

/-- A natural ceiling of a positive logarithmic quotient is positive.

This is the arithmetic core behind confidence-splitting run counts: if the
logarithm numerator and denominator are both positive, then the quotient has a
positive natural ceiling.

Layer: Model | Gap: Level 0 (positive logarithmic ceiling parameter choice)
Proof: use positivity of the real logarithm above one, positivity of a quotient,
  and the `Nat.ceil_pos` characterization.
Source: Mathlib real logarithm, division order, and natural ceiling APIs
Used in: two-phase randomized stochastic mirror descent independent run-count
  selection from a base-two confidence split
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem ceil_log_div_log_pos_of_one_lt_div
    {a b Λ : ℝ} (hb : 1 < b) (hΛ : 1 < a / Λ) :
    0 < Nat.ceil (Real.log (a / Λ) / Real.log b) := by
  apply Nat.ceil_pos.mpr
  exact div_pos (Real.log_pos hΛ) (Real.log_pos hb)

/-- The base-two confidence run selector is positive when `Λ ∈ (0, 1)`.

For a failure probability strictly between zero and one, the paper selector
`ceil (log (2 / Λ) / log 2)` requests at least one independent run.

Layer: Model | Gap: Level 0 (positive base-two run-count selector)
Proof: reduce to positivity of a logarithmic ceiling; the interval assumption
  on `Λ` gives `1 < 2 / Λ` by ordered-field arithmetic.
Source: Mathlib real logarithm, ordered-field arithmetic, and natural ceiling APIs
Used in: two-phase randomized stochastic mirror descent construction of the
  specialized setup requiring a positive number of independent runs
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem runCountChoice_pos
    (Λ : ℝ) (hΛ_pos : 0 < Λ) (hΛ_lt : Λ < 1) :
    0 < runCountChoice Λ := by
  unfold runCountChoice
  apply ceil_log_div_log_pos_of_one_lt_div one_lt_two
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ_pos
  field_simp [hΛ_ne]
  nlinarith

/-- Paper-facing SFO budget ceiling for the Theorem 6.7 parameter regime.

This is the un-totalized budget formula printed in the theorem statement: it
takes the ceiling of the maximum of the deterministic, variance-balancing, and
validation-stability lower-bound requirements.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form natural-number selector obtained
  by taking the ceiling of the maximum of three real budget requirements)
Source: Mathlib real square-root, natural ceiling, lattice order, and division
  APIs for closed-form parameter choices
Used in: two-phase randomized stochastic mirror descent paper SFO budget
  selection before positive natural-number totalization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def paperBudgetChoice
    (L DPsi Dtilde σ ε : ℝ) : ℕ :=
  Nat.ceil
    (max
      (max (512 * L ^ 2 * DPsi ^ 2 / ε)
        (((Dtilde + DPsi ^ 2 / Dtilde) *
            (128 * Real.sqrt 6 * L * σ / ε)) ^ 2))
      (3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2)))

/-- Positive totalized SFO budget choice for the Theorem 6.7 parameter regime.

The selector is the paper ceiling of the maximum of the three lower-bound
requirements, wrapped in `max 1` so that it can be used as a positive natural
algorithm input without changing the paper lower bounds.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form natural-number selector obtained
  by taking the ceiling of the maximum of three real budget requirements and
  clipping below by one)
Source: Mathlib real square-root, natural ceiling, lattice order, and division
  APIs for closed-form parameter choices
Used in: two-phase randomized stochastic mirror descent per-run SFO budget
  selection in the Theorem 6.7 parameter specialization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def budgetChoice
    (L DPsi Dtilde σ ε : ℝ) : ℕ :=
  max 1
    (Nat.ceil
      (max
        (max (512 * L ^ 2 * DPsi ^ 2 / ε)
          (((Dtilde + DPsi ^ 2 / Dtilde) *
              (128 * Real.sqrt 6 * L * σ / ε)) ^ 2))
        (3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2))))

/-- The totalized budget selector is positive.

Layer: Model | Gap: Level 0 (positive natural totalization)
Proof: unfold the selector and use the left branch of `max 1`, which makes the
  natural-number output at least one independently of the real parameters.
Source: Mathlib natural-number order and lattice APIs
Used in: two-phase randomized stochastic mirror descent construction of the
  specialized setup requiring a nonzero per-run SFO budget
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem budgetChoice_pos
    (L DPsi Dtilde σ ε : ℝ) :
    0 < budgetChoice L DPsi Dtilde σ ε := by
  unfold budgetChoice
  exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_max_left 1 _)

/-- The totalized budget choice dominates all three paper lower-bound terms.

The three inequalities are exactly the ceiling guarantees needed after taking
the maximum of the deterministic, variance-balancing, and validation-stability
requirements in the Theorem 6.7 per-run budget.

Layer: Model | Gap: Level 0 (ceiling maximum lower bounds)
Proof: unfold the selector, use `Nat.le_ceil` for the real maximum, then pass
  through the `max 1` natural totalization with `Nat.le_max_right`.
Source: Mathlib natural ceiling and lattice-order APIs over real-valued maxima
Used in: two-phase randomized stochastic mirror descent proof that the chosen
  per-run SFO budget makes the one-run budget bound at most half of ε
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem budgetChoice_lower_bounds
    (L DPsi Dtilde σ ε : ℝ) :
    512 * L ^ 2 * DPsi ^ 2 / ε ≤
      (budgetChoice L DPsi Dtilde σ ε : ℝ) ∧
    ((Dtilde + DPsi ^ 2 / Dtilde) *
        (128 * Real.sqrt 6 * L * σ / ε)) ^ 2 ≤
      (budgetChoice L DPsi Dtilde σ ε : ℝ) ∧
    3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2) ≤
      (budgetChoice L DPsi Dtilde σ ε : ℝ) := by
  unfold budgetChoice
  let a : ℝ := 512 * L ^ 2 * DPsi ^ 2 / ε
  let b : ℝ :=
    ((Dtilde + DPsi ^ 2 / Dtilde) *
      (128 * Real.sqrt 6 * L * σ / ε)) ^ 2
  let c : ℝ := 3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2)
  have hceil : max (max a b) c ≤ (Nat.ceil (max (max a b) c) : ℝ) :=
    Nat.le_ceil _
  have hchoice :
      (Nat.ceil (max (max a b) c) : ℝ) ≤
        (max 1 (Nat.ceil (max (max a b) c)) : ℕ) := by
    exact_mod_cast (Nat.le_max_right 1 (Nat.ceil (max (max a b) c)))
  constructor
  · exact le_trans (le_trans (le_trans (le_max_left a b)
      (le_max_left (max a b) c)) hceil) hchoice
  constructor
  · exact le_trans (le_trans (le_trans (le_max_right a b)
      (le_max_left (max a b) c)) hceil) hchoice
  · exact le_trans (le_trans (le_max_right (max a b) c) hceil) hchoice

/-- The paper budget selector is bounded by its positive totalization.

The closed-form SFO budget printed in the paper is the right branch of the
algorithmic `max 1` totalization, so the totalized selector always dominates
the paper-facing selector for every real parameter tuple.

Layer: Model | Gap: Level 0 (positive natural budget totalization upper bound)
Proof: unfold both closed-form selectors and use the right branch inequality
  for the natural-number maximum.
Source: Mathlib natural-number lattice-order APIs
Used in: two-phase randomized stochastic mirror descent comparison between the
  paper SFO budget and the executable positive SFO budget
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem paperBudgetChoice_le_budgetChoice
    (L DPsi Dtilde σ ε : ℝ) :
    paperBudgetChoice L DPsi Dtilde σ ε ≤
      budgetChoice L DPsi Dtilde σ ε := by
  unfold paperBudgetChoice budgetChoice
  exact Nat.le_max_right 1
    (Nat.ceil
      (max
        (max (512 * L ^ 2 * DPsi ^ 2 / ε)
          (((Dtilde + DPsi ^ 2 / Dtilde) *
              (128 * Real.sqrt 6 * L * σ / ε)) ^ 2))
        (3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2))))

/-- Paper-facing validation sample-count ceiling for a multi-run confidence split.

Given an abstract natural-valued run-count selector, this is the closed-form
post-optimization validation sample count printed in the Theorem 6.7 parameter
choice: the ceiling of `24 * S * σ^2 / (Λ * ε)`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form natural-number selector obtained
  by applying natural ceiling to the validation variance requirement)
Source: Mathlib natural ceiling, real division, powers, and stochastic mirror
  descent validation-sampling parameter choices
Used in: two-phase randomized stochastic mirror descent validation sample
  selection after optimizing independent runs
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def paperValidationCountChoice
    (runCount : ℝ → ℕ) (σ ε Λ : ℝ) : ℕ :=
  Nat.ceil (24 * (runCount Λ : ℝ) * σ ^ 2 / (Λ * ε))

/-- Positive totalized validation sample-count choice for a two-phase run.

The selector is the paper validation ceiling wrapped in `max 1`, so it can be
used as a positive natural-number algorithm input without changing the paper
lower bound.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form natural-number selector obtained
  by clipping the paper validation sample count below by one)
Source: Mathlib natural-number lattice order, natural ceiling, real division,
  and stochastic mirror descent validation-sampling parameter choices
Used in: two-phase randomized stochastic mirror descent validation sample
  selection in the Theorem 6.7 parameter specialization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def validationCountChoice
    (runCount : ℝ → ℕ) (σ ε Λ : ℝ) : ℕ :=
  max 1 (paperValidationCountChoice runCount σ ε Λ)

/-- The totalized validation sample-count selector is positive.

Layer: Model | Gap: Level 0 (positive natural validation totalization)
Proof: unfold the selector and use the left branch of `max 1`, which makes the
  natural-number output at least one independently of the real parameters.
Source: Mathlib natural-number order and lattice APIs
Used in: two-phase randomized stochastic mirror descent construction of the
  specialized setup requiring a nonzero validation sample count
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem validationCountChoice_pos
    (runCount : ℝ → ℕ) (σ ε Λ : ℝ) :
    0 < validationCountChoice runCount σ ε Λ := by
  unfold validationCountChoice
  exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_max_left 1 _)

/-- The paper validation selector is bounded by its positive totalization.

The closed-form validation sample count printed in the paper is the right
branch of the algorithmic `max 1` totalization, so the totalized selector
always dominates the paper-facing selector.

Layer: Model | Gap: Level 0 (positive natural validation totalization upper bound)
Proof: unfold the totalized selector and use the right branch inequality for
  the natural-number maximum.
Source: Mathlib natural-number lattice-order APIs
Used in: two-phase randomized stochastic mirror descent comparison between the
  paper validation sample count and the executable positive sample count
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem paperValidationCountChoice_le_validationCountChoice
    (runCount : ℝ → ℕ) (σ ε Λ : ℝ) :
    paperValidationCountChoice runCount σ ε Λ ≤
      validationCountChoice runCount σ ε Λ := by
  unfold validationCountChoice
  exact Nat.le_max_right 1 (paperValidationCountChoice runCount σ ε Λ)

/-- A one-based natural-number product has a one-based left factor.

If a product `T * b` is at least one, then the left factor `T` must also
be at least one. This is the arithmetic parameter bridge used when an
algorithm records a total count as an exact natural-number product.

Layer: Glue | Gap: Level 0 (positive natural product parameter bridge)
Proof: convert one-based positivity of the product to strict positivity, then
  apply Mathlib's positive-factor theorem for multiplication by a nonnegative
  natural number.
Source: Mathlib natural-number order and ordered multiplication APIs
Used in: stochastic conditional-gradient epoch-length positivity from the
  exact recursive mini-batch product regime
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem one_le_left_factor_of_one_le_nat_mul
    {T b : ℕ} (hprod : 1 ≤ T * b) :
    1 ≤ T := by
  exact Nat.succ_le_iff.mpr
    (pos_of_mul_pos_left (Nat.succ_le_iff.mp hprod) (Nat.zero_le b))

/-- Variance-balanced square-root step size for a stochastic first-order method.

For iteration count `N`, mini-batch size `m`, smoothness scale `L`, diameter
scale `D`, and oracle standard-deviation parameter `sigma`, this is the
closed-form choice `sqrt (((1/N + sigma^2/(L*m))/(L*D^2)))`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; closed-form square-root step-size balancing
  deterministic `1/N` and mini-batch variance `sigma^2/(L*m)` terms against a
  smoothness-diameter scale)
Source: stochastic conditional-gradient parameter choices and Mathlib real
  square-root APIs
Used in: stochastic nonconvex conditional-gradient variance-floor absorption in
  the final weighted gap bound
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def varianceBalancedStepSize
    (N m : ℕ) (L D sigma : ℝ) : ℝ :=
  Real.sqrt (((1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ))) / (L * D ^ 2)))

/-- The variance-balanced step size unfolds to its square-root formula.

Layer: Model | Gap: Level 0 (variance-balanced step-size unfolding)
Proof: by rfl after unfolding `varianceBalancedStepSize`.
Source: stochastic conditional-gradient parameter choices and Mathlib real
  square-root APIs
Used in: stochastic nonconvex conditional-gradient rewriting of the displayed
  constant step size
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem varianceBalancedStepSize_def
    (N m : ℕ) (L D sigma : ℝ) :
    varianceBalancedStepSize N m L D sigma =
      Real.sqrt (((1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ))) / (L * D ^ 2))) := by
  rfl

/-- The variance-balanced step size absorbs a mini-batch variance floor.

If `N` and `m` are positive natural parameters and `L,D` are positive real
scales, then the variance term `sigma^2 / m` is bounded by
`(L * D * varianceBalancedStepSize N m L D sigma)^2`.

Layer: Model | Gap: Level 0 (variance-balanced square-root absorption)
Proof: square the square-root formula using denominator positivity, simplify
  the field expression to `L/N + sigma^2/m`, and drop the nonnegative `L/N`
  summand.
Source: Mathlib real square-root, ordered-field arithmetic, and stochastic
  conditional-gradient variance balancing
Used in: stochastic nonconvex conditional-gradient absorption of the Lemma 7.5
  mini-batch variance floor into the final smoothness-diameter step-size budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem varianceBalancedStepSize_variance_floor_le_sq_smoothness_diameter_mul
    (N m : ℕ) (L D sigma : ℝ)
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hL : 0 < L) (hD : 0 < D) :
    sigma ^ 2 / (m : ℝ) ≤
      (L * D * varianceBalancedStepSize N m L D sigma) ^ 2 := by
  have hN_pos_real : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hm_pos_real : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hLm_pos : 0 < L * (m : ℝ) :=
    mul_pos hL hm_pos_real
  have hden_pos : 0 < L * D ^ 2 :=
    mul_pos hL (sq_pos_of_pos hD)
  have hnum_nonneg :
      0 ≤ 1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ)) := by
    exact add_nonneg (le_of_lt (one_div_pos.mpr hN_pos_real))
      (div_nonneg (sq_nonneg sigma) (le_of_lt hLm_pos))
  have hrad_nonneg :
      0 ≤
        ((1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ))) /
          (L * D ^ 2)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos_real
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos_real
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hD_ne : D ≠ 0 := ne_of_gt hD
  have hformula :
      (L * D * varianceBalancedStepSize N m L D sigma) ^ 2 =
        L / (N : ℝ) + sigma ^ 2 / (m : ℝ) := by
    unfold varianceBalancedStepSize
    rw [show
      (L * D *
          Real.sqrt
            ((1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ))) /
              (L * D ^ 2))) ^ 2 =
        (L * D) ^ 2 *
          (Real.sqrt
            ((1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ))) /
              (L * D ^ 2))) ^ 2 by ring]
    rw [Real.sq_sqrt hrad_nonneg]
    field_simp [hN_ne, hm_ne, hL_ne, hD_ne]
  rw [hformula]
  have hL_div_N_nonneg : 0 ≤ L / (N : ℝ) :=
    div_nonneg (le_of_lt hL) (le_of_lt hN_pos_real)
  linarith

/-- The variance-balanced square-root step size is positive.

If the iteration count and mini-batch size are positive natural parameters and
the smoothness and diameter scales are positive, then the closed-form
variance-balanced choice
`sqrt (((1/N + sigma^2/(L*m))/(L*D^2)))` is strictly positive.

Layer: Model | Gap: Level 0 (variance-balanced square-root step-size positivity)
Proof: prove strict positivity of the radicand by combining positivity of
  `1/N`, nonnegativity of `sigma^2/(L*m)`, and positivity of `L*D^2`, then use
  Mathlib's real square-root positivity theorem.
Source: Mathlib real square-root, natural-cast positivity, and ordered-field
  division APIs for stochastic conditional-gradient parameter choices
Used in: stochastic nonconvex conditional-gradient displayed constant
  step-size positivity before weighted output normalization
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem varianceBalancedStepSize_pos
    (N m : ℕ) (L D sigma : ℝ)
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hL : 0 < L) (hD : 0 < D) :
    0 < varianceBalancedStepSize N m L D sigma := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hLm_pos : 0 < L * (m : ℝ) :=
    mul_pos hL hm_pos
  have hnum_pos :
      0 < 1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ)) := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr hN_pos)
      (div_nonneg (sq_nonneg sigma) (le_of_lt hLm_pos))
  have hden_pos : 0 < L * D ^ 2 :=
    mul_pos hL (sq_pos_of_pos hD)
  have hrad_pos :
      0 <
        ((1 / (N : ℝ) + sigma ^ 2 / (L * (m : ℝ))) /
          (L * D ^ 2)) :=
    div_pos hnum_pos hden_pos
  simpa [varianceBalancedStepSize] using Real.sqrt_pos.2 hrad_pos

/-- The totalized validation selector dominates the real-valued paper lower bound.

The paper lower bound is first dominated by the natural ceiling, and the
ceiling is then dominated by the `max 1` positive totalization.

Layer: Model | Gap: Level 0 (validation ceiling lower bound)
Proof: use `Nat.le_ceil` for the real validation requirement and then pass
  through the `max 1` natural totalization with `Nat.le_max_right`.
Source: Mathlib natural ceiling and lattice-order APIs over real-valued
  validation sample-count requirements
Used in: two-phase randomized stochastic mirror descent proof that the selected
  validation sample count makes the validation error contribution at most half
  of ε
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem validationCountChoice_lower_bound
    (runCount : ℝ → ℕ) (σ ε Λ : ℝ) :
    24 * (runCount Λ : ℝ) * σ ^ 2 / (Λ * ε) ≤
      (validationCountChoice runCount σ ε Λ : ℝ) := by
  unfold validationCountChoice paperValidationCountChoice
  let x : ℝ := 24 * (runCount Λ : ℝ) * σ ^ 2 / (Λ * ε)
  exact le_trans (Nat.le_ceil x)
    (by
      change (Nat.ceil x : ℝ) ≤ (max 1 (Nat.ceil x) : ℕ)
      exact_mod_cast (Nat.le_max_right 1 (Nat.ceil x)))

/-- Build a paper setup object from totalized positive natural parameter choices.

The real constants and budget bound record the Theorem 6.7 parameter context,
while the caller supplies the concrete setup constructor.  This separates the
library-level totalized-count wrapper from any algorithm-specific record fields.

Layer: Model | Concept: Iterates
Proof: (definitional construction; apply the supplied setup constructor to the
  totalized positive run, budget, and validation counts)
Source: Mathlib real-order and natural-number positivity APIs for stochastic
  mirror descent parameter-choice bookkeeping
Used in: two-phase randomized stochastic mirror descent Theorem 6.7 setup
  specialization with positive totalized natural run and sample counts
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def theorem67SetupTotalized
    {SetupData : Type*}
    (_L _DPsi _Dtilde _σ ε Λ : ℝ)
    (_budgetBound : ℕ → ℝ)
    (_hε : 0 < ε) (_hΛ_pos : 0 < Λ) (_hΛ_lt : Λ < 1)
    (mkSetup :
      (S Nbar T : ℕ) → 0 < S → 0 < Nbar → 0 < T → SetupData)
    (runCount budgetChoice validationCount : ℕ)
    (hRunCount_pos : 0 < runCount)
    (hBudgetChoice_pos : 0 < budgetChoice)
    (hValidationCount_pos : 0 < validationCount) :
    SetupData :=
  mkSetup runCount budgetChoice validationCount hRunCount_pos
    hBudgetChoice_pos hValidationCount_pos

/-- Compatibility selector for the source-correct Theorem 6.7 setup.

Once the totalized setup has been constructed from the paper choices for
`ε` and `Λ`, the older compatibility surface that also accepted `0 < σ`
selects the same setup without changing any algorithm parameter.

Layer: Model | Concept: Iterates
Proof: (definitional construction; identity selector carrying the legacy
  positive-variance hypothesis as an unused compatibility argument)
Source: Mathlib real-order API and stochastic mirror descent parameter-choice
  bookkeeping
Used in: two-phase randomized stochastic mirror descent Theorem 6.7 setup
  specialization after positive natural-count totalization
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def theorem67Setup
    {SetupData : Type*}
    (_L _DPsi _Dtilde σ ε Λ : ℝ)
    (_budgetBound : ℕ → ℝ)
    (totalizedSetup : SetupData)
    (_hε : 0 < ε) (_hΛ_pos : 0 < Λ) (_hΛ_lt : Λ < 1)
    (_hσ_pos : 0 < σ) : SetupData :=
  totalizedSetup

/-- Total recursive carrier for the accelerated `Gamma` weight schedule.

The zero branch is a harmless totalization for Lean recursion. The paper-facing
API is the positive-time wrapper `acceleratedGammaSchedule`, where the schedule
starts at time `1` and follows the displayed accelerated recurrence.

Layer: Model | Concept: Iterates
Proof: (definitional construction; total recursive real-valued schedule with a
  zero branch and the one-based accelerated Gamma recurrence)
Source: accelerated stochastic approximation parameter schedules and Mathlib
  natural-number recursion APIs
Used in: accelerated stochastic gradient descent recursive Gamma-weight
  schedule before extracting base and successor equations
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
def acceleratedGammaScheduleCore (alpha : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | t + 2 => (1 - alpha (t + 2)) * acceleratedGammaScheduleCore alpha (t + 1)

/-- Positive-time accelerated `Gamma` weight schedule.

For a scalar acceleration sequence `alpha`, this exposes the recursive
accelerated schedule only on positive natural times, matching the paper-time
indexing convention while keeping the underlying total recursion internal to
the construction.

Layer: Model | Concept: Iterates
Proof: (definitional construction; positive-time view of the recursive
  accelerated Gamma schedule)
Source: accelerated stochastic approximation parameter schedules and Mathlib
  subtype indexing APIs
Used in: accelerated stochastic gradient descent positive-time Gamma notation
  used by parameter relations and telescoping weights
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
def acceleratedGammaSchedule (alpha : ℕ → ℝ) (t : {n : ℕ // 1 ≤ n}) : ℝ :=
  acceleratedGammaScheduleCore alpha t.1

/-- The positive-time accelerated `Gamma` schedule starts from `1`.

Layer: Model | Gap: Level 0 (accelerated Gamma base equation)
Proof: unfold the positive-time wrapper and the recursive carrier at natural
  time `1`.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  natural-number recursion APIs
Used in: accelerated stochastic gradient descent initialization of the
  Gamma-weight recurrence
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedGammaSchedule_one (alpha : ℕ → ℝ) :
    acceleratedGammaSchedule alpha ⟨1, le_rfl⟩ = 1 := by
  rfl

/-- Successor recurrence for the positive-time accelerated `Gamma` schedule.

Layer: Model | Gap: Level 0 (accelerated Gamma successor recurrence)
Proof: split the natural time; the impossible zero-time predecessor is
  eliminated by positivity, and the successor case is the recursive equation.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  natural-number recursion APIs
Used in: accelerated stochastic gradient descent rewriting of Gamma weights in
  one-step recurrence and telescoping arguments
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedGammaSchedule_succ
    (alpha : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    acceleratedGammaSchedule alpha ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩ =
      (1 - alpha (t + 1)) * acceleratedGammaSchedule alpha ⟨t, ht⟩ := by
  cases t with
  | zero =>
      cases ht
  | succ t =>
      rfl

/-- Quotient form of an adjacent weighted-Gamma monotonicity condition.

If the cross-multiplied accelerated schedule inequality holds at time `t`, and
the two adjacent Gamma-weight denominators are positive, then the corresponding
normalized ratio inequality holds.

Layer: Model | Gap: Level 0 (weighted Gamma ratio monotonicity)
Proof: rewrite the quotient inequality by Mathlib's positive-denominator
  cross-multiplication theorem and apply the displayed schedule inequality.
Source: Mathlib ordered real field division and accelerated estimate-sequence
  schedule algebra
Used in: stochastic accelerated gradient descent conversion from displayed
  Gamma-weight monotonicity to checked quotient run-contract semantics
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem checkedQuotient_weight_mono_semantics
    (alpha gamma Gamma : ℕ → ℝ) (mu : ℝ) (t : ℕ)
    (hden_next_pos : 0 < gamma (t + 1) * Gamma (t + 1))
    (hden_cur_pos : 0 < gamma t * Gamma t)
    (hweighted :
      alpha (t + 1) * (gamma t * Gamma t) ≤
        (alpha t * (1 + mu * gamma t)) *
          (gamma (t + 1) * Gamma (t + 1))) :
    alpha (t + 1) / (gamma (t + 1) * Gamma (t + 1)) ≤
      (alpha t * (1 + mu * gamma t)) / (gamma t * Gamma t) := by
  rw [div_le_div_iff₀ hden_next_pos hden_cur_pos]
  exact hweighted

/-- The accelerated `alpha / Gamma` weights normalize to the reciprocal final
`Gamma` weight.

For the one-based accelerated schedule `Gamma_1 = 1` and
`Gamma_{t+1} = (1 - alpha_{t+1}) Gamma_t`, the identity
`alpha_{t+1} / Gamma_{t+1} = 1 / Gamma_{t+1} - 1 / Gamma_t` telescopes the
finite sum of `alpha_t / Gamma_t` over `1..k` to `1 / Gamma_k`, assuming
the displayed denominators are nonzero and `alpha_1 = 1`.

Layer: Model | Gap: Level 0 (accelerated Gamma reciprocal normalization)
Proof: rewrite each successor summand as a difference of reciprocal Gamma
  weights using the accelerated schedule recurrence, then induct over the
  closed interval sum.
Source: accelerated estimate-sequence parameter recurrences and Mathlib finite
  interval sum induction over ordered-field arithmetic
Used in: stochastic accelerated gradient descent lower-model weighted-sum
  normalization before replacing model values by the optimum value
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem sum_alpha_div_acceleratedGamma_eq_inv
    (alpha : ℕ → ℝ)
    (halpha_one : alpha 1 = 1)
    (hGamma_ne :
      ∀ t : {n : ℕ // 1 ≤ n}, acceleratedGammaSchedule alpha t ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    Finset.sum (Finset.Icc 1 k).attach (fun t =>
      let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
      alpha t.1 / acceleratedGammaSchedule alpha τ) =
      1 / acceleratedGammaSchedule alpha ⟨k, hk⟩ := by
  classical
  have hstep : ∀ (n : ℕ) (hn : 1 ≤ n),
      alpha (n + 1) /
          acceleratedGammaSchedule alpha
            ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ =
        1 /
            acceleratedGammaSchedule alpha
              ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ -
          1 / acceleratedGammaSchedule alpha ⟨n, hn⟩ := by
    intro n hn
    have hrec := acceleratedGammaSchedule_succ alpha n hn
    have hGn :
        acceleratedGammaSchedule alpha ⟨n, hn⟩ ≠ 0 :=
      hGamma_ne ⟨n, hn⟩
    have hGsn :
        acceleratedGammaSchedule alpha
          ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ ≠ 0 :=
      hGamma_ne ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
    field_simp [hGn, hGsn]
    nlinarith
  let invGamma : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then 1 / acceleratedGammaSchedule alpha ⟨n, hn⟩ else 0
  let term : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then alpha n / acceleratedGammaSchedule alpha ⟨n, hn⟩ else 0
  have hterm_one : term 1 = invGamma 1 := by
    simp [term, invGamma, halpha_one]
  have hplain : ∀ (k : ℕ) (hk : 1 ≤ k),
      Finset.sum (Finset.Icc 1 k) term = invGamma k := by
    intro k hk
    exact Nat.le_induction
      (by simp [hterm_one])
      (by
        intro n hn ih
        have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        rw [Finset.sum_Icc_succ_top hn1]
        rw [ih]
        have hterm_succ : term (n + 1) = invGamma (n + 1) - invGamma n := by
          dsimp [term, invGamma]
          simp only [hn, ↓reduceDIte]
          exact hstep n hn
        change invGamma n + term (n + 1) = invGamma (n + 1)
        rw [hterm_succ]
        ring)
      k hk
  have htarget_plain :
      Finset.sum (Finset.Icc 1 k).attach (fun t =>
        let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
        alpha t.1 / acceleratedGammaSchedule alpha τ) =
        Finset.sum (Finset.Icc 1 k) term := by
    calc
      Finset.sum (Finset.Icc 1 k).attach (fun t =>
        let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
        alpha t.1 / acceleratedGammaSchedule alpha τ) =
          Finset.sum (Finset.Icc 1 k).attach (fun t => term t.1) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            have htpos : 1 ≤ t.1 := (Finset.mem_Icc.mp t.2).1
            simp [term, htpos]
      _ = Finset.sum (Finset.Icc 1 k) term := by
            exact Finset.sum_attach (Finset.Icc 1 k) term
  rw [htarget_plain, hplain k hk]
  simp [invGamma, hk]

/-- Positivity of the accelerated Gamma schedule from strict post-initial
`alpha < 1` factors. -/
theorem acceleratedGamma_pos_of_alpha_lt_one
    (alpha : ℕ → ℝ)
    (halpha_lt_one : ∀ t : ℕ, 2 ≤ t → alpha t < 1) :
    ∀ t : {n : ℕ // 1 ≤ n}, 0 < acceleratedGammaSchedule alpha t := by
  intro t
  have hpos :
      ∀ (n : ℕ) (hn : 1 ≤ n),
        0 < acceleratedGammaSchedule alpha ⟨n, hn⟩ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        simpa using
          (show 0 < acceleratedGammaSchedule alpha ⟨1, le_rfl⟩ by
            rw [acceleratedGammaSchedule_one]
            norm_num)
    | succ m hm ih =>
        have htwo : 2 ≤ m + 1 := Nat.succ_le_succ hm
        have hfactor_pos : 0 < 1 - alpha (m + 1) := by
          have halpha_lt : alpha (m + 1) < 1 := halpha_lt_one (m + 1) htwo
          linarith
        rw [acceleratedGammaSchedule_succ alpha m hm]
        exact mul_pos hfactor_pos ih
  exact hpos t.1 t.2

/-- Positivity of a one-based Gamma schedule from interval-bounded recurrence
factors and nonzero denominators. -/
theorem acceleratedGamma_pos_of_mem_Icc_and_ne_zero
    (alpha : ℕ → ℝ) (Gamma : {n : ℕ // 1 ≤ n} → ℝ)
    (hGamma_one : Gamma ⟨1, le_rfl⟩ = 1)
    (hGamma_succ :
      ∀ (n : ℕ) (hn : 1 ≤ n),
        Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ =
          (1 - alpha (n + 1)) * Gamma ⟨n, hn⟩)
    (halpha_mem_Icc :
      ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (hGamma_ne : ∀ t : {n : ℕ // 1 ≤ n}, Gamma t ≠ 0) :
    ∀ t : {n : ℕ // 1 ≤ n}, 0 < Gamma t := by
  intro t
  have hnonneg :
      ∀ (n : ℕ) (hn : 1 ≤ n), 0 ≤ Gamma ⟨n, hn⟩ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hbase : 0 ≤ Gamma ⟨1, le_rfl⟩ := by
          rw [hGamma_one]
          norm_num
        simpa using hbase
    | succ m hm ih =>
        have halpha := halpha_mem_Icc
          ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩
        have hfactor : 0 ≤ 1 - alpha (m + 1) := by
          exact sub_nonneg.mpr (Set.mem_Icc.mp halpha).2
        rw [hGamma_succ m hm]
        exact mul_nonneg hfactor ih
  exact lt_of_le_of_ne (hnonneg t.1 t.2) (hGamma_ne t).symm

/-- Denominator side conditions for accelerated expected-error budgets. -/
theorem acceleratedErrorBound_denominators
    (gamma alpha : ℕ → ℝ)
    (Gamma : {n : ℕ // 1 ≤ n} → ℝ)
    (mu L : ℝ)
    (k : {n : ℕ // 1 ≤ n})
    (hgamma_one_ne : gamma 1 ≠ 0)
    (hGamma_ne : ∀ t : {n : ℕ // 1 ≤ n}, Gamma t ≠ 0)
    (hcurvature_ne :
      ∀ t : {n : ℕ // 1 ≤ n},
        1 + mu * gamma t.1 - L * alpha t.1 * gamma t.1 ≠ 0) :
    gamma 1 ≠ 0 ∧
      (∀ t, (ht : t ∈ Finset.Icc 1 k.1) →
        Gamma ⟨t, (Finset.mem_Icc.mp ht).1⟩ *
          (1 + mu * gamma t - L * alpha t * gamma t) ≠ 0) := by
  refine ⟨hgamma_one_ne, ?_⟩
  intro t ht
  let τ : {n : ℕ // 1 ≤ n} := ⟨t, (Finset.mem_Icc.mp ht).1⟩
  exact mul_ne_zero (hGamma_ne τ) (hcurvature_ne τ)

/-- Positive `alpha` from interval membership plus the non-initial left
denominator condition for the accelerated `q` relation. -/
theorem alpha_pos_of_mem_Icc_and_left_denominator_ne
    (alpha q : ℕ → ℝ)
    (t : {n : ℕ // 1 ≤ n})
    (halpha_mem : alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (halpha_one : alpha 1 = 1)
    (hleft_den_ne : ∀ n, 2 ≤ n → alpha n * (1 - q n) ≠ 0) :
    0 < alpha t.1 := by
  have halpha_nonneg : 0 ≤ alpha t.1 := (Set.mem_Icc.mp halpha_mem).1
  by_cases ht : t.1 = 1
  · rw [ht, halpha_one]
    norm_num
  · have htwo : 2 ≤ t.1 := by
      omega
    have hden_ne := hleft_den_ne t.1 htwo
    have halpha_ne : alpha t.1 ≠ 0 := by
      intro hzero
      exact hden_ne (by simp [hzero])
    exact lt_of_le_of_ne halpha_nonneg (Ne.symm halpha_ne)

/-- Quotient form of a cross-multiplied accelerated `q` coupling. -/
theorem q_ratio_eq_one_div_of_cross_mul
    {K : Type*} [Field K] (q alpha mu gamma : K)
    (hleft : alpha * (1 - q) ≠ 0)
    (hright : 1 + mu * gamma ≠ 0)
    (hrel : q * (1 - alpha) * (1 + mu * gamma) =
      alpha * (1 - q)) :
    (q * (1 - alpha)) / (alpha * (1 - q)) =
      1 / (1 + mu * gamma) := by
  field_simp [hleft, hright]
  rw [hrel]
  exact div_self hleft

/-- The square-root contraction schedule lies in `(0, 1)` and has negative log.

For `m ≥ 1` and positive `c`, the closed-form factor
`1 - 2 / (m * (sqrt (1 + 16 * c / m) + 1))` is a valid contraction
factor. This packages the sign facts needed by logarithmic ceiling schedules.

Layer: Model | Gap: Level 0 (square-root contraction schedule sign bounds)
Proof: prove the square-root term is greater than one, hence the denominator is
  greater than two, so the subtracted quotient lies in `(0, 1)`; negativity of
  the logarithm follows from `Real.log_neg_iff`.
Source: Mathlib real square-root, ordered-field arithmetic, and logarithm APIs
Used in: randomized accelerated proximal-point inner-loop contraction length
  selection from a closed-form square-root schedule
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sqrt_alpha_schedule_pos_lt_one_log_neg
    (m c alpha : ℝ) (hm_ge_one : 1 ≤ m) (hc_pos : 0 < c)
    (halpha :
      alpha = 1 - 2 / (m * (Real.sqrt (1 + 16 * c / m) + 1))) :
    0 < alpha ∧ alpha < 1 ∧ Real.log alpha < 0 := by
  let d : ℝ := m * (Real.sqrt (1 + 16 * c / m) + 1)
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_one
  have harg_gt_one : 1 < 1 + 16 * c / m := by
    have hfrac_pos : 0 < 16 * c / m := by positivity
    linarith
  have hsqrt_gt_one : 1 < Real.sqrt (1 + 16 * c / m) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hden_gt_two : 2 < d := by
    dsimp [d]
    have hsum_gt_two : 2 < Real.sqrt (1 + 16 * c / m) + 1 := by
      linarith
    nlinarith
  have hden_pos : 0 < d := by linarith
  have htwo_div_pos : 0 < 2 / d := by positivity
  have htwo_div_lt_one : 2 / d < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    simpa [d] using (sub_pos.mpr htwo_div_lt_one)
  have halpha_lt_one : alpha < 1 := by
    rw [halpha]
    have hpos : 0 < 2 / (m * (Real.sqrt (1 + 16 * c / m) + 1)) := by
      simpa [d] using htwo_div_pos
    linarith
  have hlog_neg : Real.log alpha < 0 := by
    exact (Real.log_neg_iff halpha_pos).mpr halpha_lt_one
  exact ⟨halpha_pos, halpha_lt_one, hlog_neg⟩

/-- A one-based accelerated Gamma recurrence is positive on a finite window
when its factors lie in `[0,1]` and the Gamma weights are nonzero on that
window.

This is the finite-horizon variant of global accelerated Gamma positivity: the
recurrence gives nonnegativity at every positive time, and finite-window
denominator admissibility upgrades the values in `Icc 1 k` to strict
positivity.

Layer: Model | Gap: Level 0 (finite-window accelerated Gamma positivity)
Proof: induct on positive natural times to propagate nonnegativity from
  `Gamma_1 = 1`; on the requested finite window, combine this with the
  supplied nonzero denominator fact.
Source: accelerated estimate-sequence parameter recurrences and Mathlib
  ordered real-field interval APIs
Used in: stochastic conditional-gradient sliding finite-window Gamma
  denominator positivity before ratio and telescope estimates
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem acceleratedGamma_pos_on_Icc_of_ne_zero_on_Icc
    (alpha : ℕ → ℝ) (Gamma : {n : ℕ // 1 ≤ n} → ℝ)
    (k : ℕ)
    (hGamma_one : Gamma ⟨1, le_rfl⟩ = 1)
    (hGamma_succ :
      ∀ (n : ℕ) (hn : 1 ≤ n),
        Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ =
          (1 - alpha (n + 1)) * Gamma ⟨n, hn⟩)
    (halpha_mem_Icc :
      ∀ t : {n : ℕ // 1 ≤ n}, alpha t.1 ∈ Set.Icc (0 : ℝ) 1)
    (hGamma_ne_window :
      ∀ t : {n : ℕ // n ∈ Finset.Icc 1 k},
        Gamma ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩ ≠ 0) :
    ∀ (n : ℕ) (hn : 1 ≤ n), n ≤ k → 0 < Gamma ⟨n, hn⟩ := by
  classical
  have hnonneg :
      ∀ (n : ℕ) (hn : 1 ≤ n), 0 ≤ Gamma ⟨n, hn⟩ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hbase : 0 ≤ Gamma ⟨1, le_rfl⟩ := by
          rw [hGamma_one]
          norm_num
        simpa using hbase
    | succ m hm ih =>
        have halpha := halpha_mem_Icc
          ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩
        have hfactor : 0 ≤ 1 - alpha (m + 1) := by
          exact sub_nonneg.mpr (Set.mem_Icc.mp halpha).2
        rw [hGamma_succ m hm]
        exact mul_nonneg hfactor ih
  intro n hn hnk
  have hmem : n ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hn, hnk⟩
  have hne : Gamma ⟨n, hn⟩ ≠ 0 := by
    simpa using hGamma_ne_window ⟨n, hmem⟩
  exact lt_of_le_of_ne (hnonneg n hn) hne.symm

-- Generalization plan (G0):
-- concept/name: accelerated variance-reduction scalar side-condition predicate;
--   orig was `lemma516CorrectedScalarSideConditions`, renamed away from the
--   paper-local lemma number and correction note to expose the reusable scalar
--   contract.
-- generality used: six real scalar parameters `mu`, `L`, `LQ`, `gamma`,
--   `alpha`, and `p`; no carrier, measure, independence, integrability,
--   topology, norm, inner product, convexity, smoothness function, oracle, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: accelerated finite-sum variance-reduced methods use
--   the same scalar contract before search-point convex-combination
--   admissibility, averaged-snapshot convexity, and absorption of the
--   estimator-noise quotient; schedules and smoothness constants vary while
--   the predicate shape is unchanged.
-- counterargument checked: this is a hypothesis bundle, but the grouped facts
--   recur as a stable parameter contract across Lemma 5.16, Lemma 5.17, and
--   Theorem 5.9 schedule specializations; it is not just paper traceability
--   because callers change only the six scalar values, not the conclusion.
-- coverage search: searched SOptLib/CATALOG/Staging for
--   `ScalarSideConditions`, `side conditions`, `1 - alpha - p`, curvature/noise
--   quotient shapes, `AcceleratedSnapshotAverageWeightsAdmissible`, and
--   existing parameter-choice contracts; Mathlib LeanSearch for real unit
--   interval and denominator side conditions returned `unitInterval.div_mem`
--   and `unitInterval` primitives, but no bundled accelerated VR scalar
--   parameter predicate. Existing `ConditionalGradientRealizationContract` and
--   `WeightedEpochOutputBoundary` are structurally different conditional-
--   gradient/window contracts.
-- minimal hypotheses: all already minimal; the statement is exactly a named
--   conjunction of scalar facts and does not require nonnegativity of `mu`,
--   positivity of `L`, or any global schedule assumption.

/-- Scalar parameter contract for an accelerated variance-reduction step.

The predicate packages the interval constraints on `alpha` and `p`, positivity
of `gamma`, the accelerated curvature denominator, the variance/noise
absorption inequality, and the residual convex-combination coefficient.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; bundled real scalar side conditions for
  accelerated variance-reduction parameter choices)
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib ordered real interval and division notation
Used in: variance-reduced accelerated gradient descent search-point
  admissibility, averaged snapshot admissibility, and estimator-noise
  absorption before the one-step recursion
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def AcceleratedVRScalarSideConditions
    (mu L LQ gamma alpha p : ℝ) : Prop :=
  alpha ∈ Set.Icc (0 : ℝ) 1 ∧
    p ∈ Set.Icc (0 : ℝ) 1 ∧
    0 < gamma ∧
    0 < 1 + mu * gamma - L * alpha * gamma ∧
    0 ≤ p - LQ * alpha * gamma / (1 + mu * gamma - L * alpha * gamma) ∧
    0 ≤ 1 - alpha - p

/-- The accelerated variance-reduction scalar side-condition predicate unfolds
to its six scalar inequalities.

Layer: Model | Gap: Level 0 (accelerated variance-reduction scalar contract unfolding)
Proof: by rfl after unfolding `AcceleratedVRScalarSideConditions`.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib ordered real interval and division notation
Used in: variance-reduced accelerated gradient descent schedule-specialization
  rewrites before applying search-point and averaged-snapshot admissibility
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem AcceleratedVRScalarSideConditions_def
    (mu L LQ gamma alpha p : ℝ) :
    AcceleratedVRScalarSideConditions mu L LQ gamma alpha p ↔
      alpha ∈ Set.Icc (0 : ℝ) 1 ∧
        p ∈ Set.Icc (0 : ℝ) 1 ∧
        0 < gamma ∧
        0 < 1 + mu * gamma - L * alpha * gamma ∧
        0 ≤ p - LQ * alpha * gamma / (1 + mu * gamma - L * alpha * gamma) ∧
        0 ≤ 1 - alpha - p := by
  rfl

namespace AcceleratedVRScalarSideConditions

/-- Build accelerated variance-reduction scalar side conditions from the six
component scalar facts.

Layer: Model | Gap: Level 0 (accelerated variance-reduction scalar contract constructor)
Proof: package the interval, positivity, denominator, noise, and residual
  coefficient facts into the definitional conjunction.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent schedule verification
  before search-point convexity and noise absorption
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem of_components
    {mu L LQ gamma alpha p : ℝ}
    (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : 0 < gamma)
    (hcurv : 0 < 1 + mu * gamma - L * alpha * gamma)
    (hnoise :
      0 ≤ p - LQ * alpha * gamma / (1 + mu * gamma - L * alpha * gamma))
    (hbar : 0 ≤ 1 - alpha - p) :
    AcceleratedVRScalarSideConditions mu L LQ gamma alpha p :=
  ⟨halpha, hp, hgamma, hcurv, hnoise, hbar⟩

/-- The `alpha` parameter in an accelerated variance-reduction scalar contract
lies in the unit interval.

Layer: Model | Gap: Level 0 (accelerated variance-reduction alpha interval projection)
Proof: unfold the scalar contract and take the first conjunct.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent search-point and
  averaged-snapshot convex-combination admissibility
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem alpha_mem
    {mu L LQ gamma alpha p : ℝ}
    (h : AcceleratedVRScalarSideConditions mu L LQ gamma alpha p) :
    alpha ∈ Set.Icc (0 : ℝ) 1 :=
  h.1

/-- The snapshot parameter `p` in an accelerated variance-reduction scalar
contract lies in the unit interval.

Layer: Model | Gap: Level 0 (accelerated variance-reduction snapshot interval projection)
Proof: unfold the scalar contract and take the second conjunct.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent search-point and
  averaged-snapshot convex-combination admissibility
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem p_mem
    {mu L LQ gamma alpha p : ℝ}
    (h : AcceleratedVRScalarSideConditions mu L LQ gamma alpha p) :
    p ∈ Set.Icc (0 : ℝ) 1 :=
  h.2.1

/-- The stepsize-like scalar `gamma` in an accelerated variance-reduction
scalar contract is positive.

Layer: Model | Gap: Level 0 (accelerated variance-reduction gamma positivity projection)
Proof: unfold the scalar contract and take the third conjunct.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent denominator positivity
  and one-step recursion scaling
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem gamma_pos
    {mu L LQ gamma alpha p : ℝ}
    (h : AcceleratedVRScalarSideConditions mu L LQ gamma alpha p) :
    0 < gamma :=
  h.2.2.1

/-- The accelerated curvature denominator in an accelerated
variance-reduction scalar contract is positive.

Layer: Model | Gap: Level 0 (accelerated variance-reduction curvature denominator projection)
Proof: unfold the scalar contract and take the fourth conjunct.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent Young-inequality
  denominator and estimator-noise quotient absorption
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem curvature_pos
    {mu L LQ gamma alpha p : ℝ}
    (h : AcceleratedVRScalarSideConditions mu L LQ gamma alpha p) :
    0 < 1 + mu * gamma - L * alpha * gamma :=
  h.2.2.2.1

/-- The variance/noise absorption coefficient in an accelerated
variance-reduction scalar contract is nonnegative.

Layer: Model | Gap: Level 0 (accelerated variance-reduction noise coefficient projection)
Proof: unfold the scalar contract and take the fifth conjunct.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent replacement of the
  linearized snapshot term by the snapshot objective value
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem noise_nonneg
    {mu L LQ gamma alpha p : ℝ}
    (h : AcceleratedVRScalarSideConditions mu L LQ gamma alpha p) :
    0 ≤ p - LQ * alpha * gamma / (1 + mu * gamma - L * alpha * gamma) :=
  h.2.2.2.2.1

/-- The residual bar coefficient in an accelerated variance-reduction scalar
contract is nonnegative.

Layer: Model | Gap: Level 0 (accelerated variance-reduction residual coefficient projection)
Proof: unfold the scalar contract and take the final conjunct.
Source: accelerated variance-reduced finite-sum parameter side conditions and
  Mathlib conjunction APIs
Used in: variance-reduced accelerated gradient descent search-point and
  averaged-snapshot convex-combination admissibility
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem bar_nonneg
    {mu L LQ gamma alpha p : ℝ}
    (h : AcceleratedVRScalarSideConditions mu L LQ gamma alpha p) :
    0 ≤ 1 - alpha - p :=
  h.2.2.2.2.2

end AcceleratedVRScalarSideConditions


open scoped BigOperators


-- Generalization plan (G0):
-- concept/name: terminal-adjusted smooth theta weights for normalized finite
--   epoch output; orig was `lemma517_smoothTheta_epochOutputWeightsAdmissible`,
--   renamed away from theorem numbering and local epoch-output predicate names.
-- generality used: real scalar parameters `gamma`, `alpha`, and `p` over a
--   positive natural window length `T`; no carrier, measure, independence,
--   integrability, topology, norm, inner product, convexity, smoothness, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: smooth accelerated epoch recursions instantiate a
--   positive epoch length, positive stepsize/acceleration parameters, and a
--   nonnegative snapshot weight to certify the terminal-adjusted theta output
--   weights before Jensen, finite-window selection, and output averaging.
-- counterargument checked: not merely paper-local traceability because the
--   same two-branch terminal-adjusted weight schedule is reused by smooth and
--   strongly-convex accelerated finite-sum epoch proofs; the generic
--   admissible-weight contract is already covered by
--   `FiniteWindowWeightsAdmissible`, so this staging theorem proves the
--   concrete schedule satisfies that existing contract instead of redefining it.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   legacy terminal-adjusted theta/output-weight names,
--   `FiniteWindowWeightsAdmissible`, and theta-weight phrases; the relevant partial
--   hit was `SOptLib.FiniteWindowWeightsAdmissible` with constructor
--   `of_nonneg_of_pos`. LeanSearch for "finite sum weights positive total mass
--   nonnegative weights admissible" returned `Finset.sum_nonneg`,
--   `finsum_cond_pos`, and `StdSimplex.mk`, but no formula-specific
--   terminal-adjusted theta schedule theorem.
-- minimal hypotheses: global algorithm assumptions reduce to `0 < T`,
--   `0 < gamma`, `0 < alpha`, and `0 <= p`; upper bounds on `alpha` and `p`,
--   curvature denominators, and noise inequalities are unused.

/-- Terminal-adjusted smooth epoch weights on a one-based finite epoch window.

The terminal atom has weight `gamma / alpha`; all earlier atoms have the
inflated smooth weight `gamma / alpha * (alpha + p)`.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; two-branch scalar schedule with a terminal
  adjustment for normalized epoch output)
Source: finite-sum accelerated-gradient epoch parameter choices and Mathlib
  ordered-field primitives
Used in: smooth accelerated epoch output weighting before Jensen and normalized
  finite-window averaging
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def terminal_adjusted_smooth_epoch_weight (T : ℕ) (gamma alpha p : ℝ) (t : ℕ) : ℝ :=
  if t = T then
    gamma / alpha
  else
    gamma / alpha * (alpha + p)

/-- The terminal-adjusted smooth epoch-weight definition unfolds to its two-branch
scalar formula.

Layer: Model | Gap: Level 0 (terminal-adjusted smooth epoch-weight unfolding)
Proof: by rfl after unfolding `terminal_adjusted_smooth_epoch_weight`.
Source: finite-sum accelerated-gradient epoch parameter choices and Mathlib
  ordered-field primitives
Used in: smooth accelerated epoch output weighting before Jensen and normalized
  finite-window averaging
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem terminal_adjusted_smooth_epoch_weight_def
    (T : ℕ) (gamma alpha p : ℝ) (t : ℕ) :
    terminal_adjusted_smooth_epoch_weight T gamma alpha p t =
      if t = T then
        gamma / alpha
      else
        gamma / alpha * (alpha + p) := by
  rfl

/-- Positive `gamma` and `alpha`, nonnegative `p`, and a nonempty epoch window
make the terminal-adjusted smooth epoch weights admissible.

The theorem targets the existing SOptLib finite-window weight contract:
nonnegativity holds at every one-based epoch time, and the positive window
length supplies a strictly positive atom, hence positive total mass.

Layer: Model | Gap: Level 0 (terminal-adjusted smooth epoch-weight admissible weights)
Proof: prove every atom is strictly positive by splitting on the terminal
  branch, then use `FiniteWindowWeightsAdmissible.of_nonneg_of_pos` with the
  first epoch index as the positive supported atom.
Source: Mathlib ordered-field positivity and finite-set real-sum APIs
Used in: smooth accelerated epoch output weighting before Jensen and normalized
  finite-window averaging
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem terminal_adjusted_smooth_epoch_weight_admissible
    {T : ℕ} {gamma alpha p : ℝ}
    (hT : 0 < T) (hgamma : 0 < gamma) (halpha : 0 < alpha)
    (hp : 0 ≤ p) :
    FiniteWindowWeightsAdmissible (Finset.univ : Finset (Fin T))
      (fun t : Fin T => terminal_adjusted_smooth_epoch_weight T gamma alpha p (t.1 + 1)) := by
  have hratio : 0 < gamma / alpha := div_pos hgamma halpha
  have hsum : 0 < alpha + p := add_pos_of_pos_of_nonneg halpha hp
  have htheta_pos :
      ∀ t : Fin T, 0 < terminal_adjusted_smooth_epoch_weight T gamma alpha p (t.1 + 1) := by
    intro t
    by_cases ht : t.1 + 1 = T
    · rw [terminal_adjusted_smooth_epoch_weight, if_pos ht]
      exact hratio
    · rw [terminal_adjusted_smooth_epoch_weight, if_neg ht]
      exact mul_pos hratio hsum
  have hnonneg :
      ∀ t : Fin T, t ∈ (Finset.univ : Finset (Fin T)) →
        0 ≤ terminal_adjusted_smooth_epoch_weight T gamma alpha p (t.1 + 1) := by
    intro t _ht
    exact le_of_lt (htheta_pos t)
  exact
    FiniteWindowWeightsAdmissible.of_nonneg_of_pos
      (times := (Finset.univ : Finset (Fin T)))
      (weight := fun t : Fin T => terminal_adjusted_smooth_epoch_weight T gamma alpha p (t.1 + 1))
      hnonneg
      (k := ⟨0, hT⟩)
      (by simp)
      (htheta_pos ⟨0, hT⟩)


-- Generalization plan (G0):
-- concept/name: epoch-indexed smooth theta schedule; orig was `smoothThetaOf`,
--   renamed away from a local helper suffix while keeping the standard
--   accelerated-epoch `theta` terminology.
-- generality used: natural epoch lengths and real-valued parameter schedules
--   `gamma`, `alpha`, and `p`; no carrier, measure, independence,
--   integrability, topology, norm, inner product, convexity, smoothness, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: smooth accelerated finite-sum epoch proofs vary the
--   epoch-length, stepsize, acceleration, and snapshot-weight schedules while
--   calling the same terminal/nonterminal theta schedule before output
--   weighting and epoch-recursion algebra.
-- counterargument checked: not merely paper-local traceability because the
--   same epoch-indexed Eq. (5.4.12)-style schedule is reused across smooth
--   accelerated and variance-reduced epoch proofs; the scalar formula is
--   already named by `terminal_adjusted_smooth_epoch_weight`, so this entry is
--   the schedule lift rather than a duplicate scalar definition.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `smoothTheta`, `theta`, `terminal_adjusted_smooth_epoch_weight`, and
--   epoch schedule terms; relevant partial hit was the staged scalar
--   `terminal_adjusted_smooth_epoch_weight` and its admissibility theorem.
--   LeanSearch for the two-branch gamma/alpha theta formula returned unrelated
--   theta/asymptotics/gamma entries, with no Mathlib schedule definition.
-- minimal hypotheses: all already minimal; this is a definitional parameter
--   schedule and needs no positivity or epoch-domain assumptions.

/-- Epoch-indexed terminal-adjusted smooth theta weights.

For epoch `s`, the terminal time `T s` has weight `gamma s / alpha s`; every
nonterminal time has weight `gamma s / alpha s * (alpha s + p s)`.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; lift the scalar terminal-adjusted smooth
  epoch weight to natural-indexed epoch parameter schedules)
Source: finite-sum accelerated-gradient epoch parameter choices and Mathlib
  ordered-field primitives
Used in: smooth accelerated epoch output weighting before Jensen and normalized
  finite-window averaging
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothEpochTheta (T : ℕ → ℕ) (gamma alpha p : ℕ → ℝ)
    (s t : ℕ) : ℝ :=
  terminal_adjusted_smooth_epoch_weight (T s) (gamma s) (alpha s) (p s) t

/-- The epoch-indexed smooth theta schedule unfolds to its terminal/nonterminal
formula.

Layer: Model | Gap: Level 0 (epoch-indexed smooth theta unfolding)
Proof: by rfl after unfolding `smoothEpochTheta` and
  `terminal_adjusted_smooth_epoch_weight`.
Source: finite-sum accelerated-gradient epoch parameter choices and Mathlib
  ordered-field primitives
Used in: smooth accelerated epoch output weighting before Jensen and normalized
  finite-window averaging
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem smoothEpochTheta_def (T : ℕ → ℕ) (gamma alpha p : ℕ → ℝ)
    (s t : ℕ) :
    smoothEpochTheta T gamma alpha p s t =
      if t = T s then
        gamma s / alpha s
      else
        gamma s / alpha s * (alpha s + p s) := by
  rfl



-- Generalization plan (G0):
-- concept/name: smooth-epoch left coefficient; orig was smoothEpochLOf
-- generality used: scalar epoch schedules only; no carrier, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: smooth variance-reduced accelerated epoch proofs instantiate the epoch length, step, averaging, and momentum schedules to name the total left-side theta-mass coefficient before telescoping or lower-bound arguments
-- counterargument checked: this is a formula-bodied definition, but it names the recurring `L_s` coefficient consumed by multiple staged lower-bound and coefficient-bridge lemmas; it is not paper-local after removing setup fields and theorem numbers
-- coverage search: searched smoothEpochLeftCoeff/smooth epoch left coefficient/L_s/gamma alpha p T in SOptLib, Staging, registry, and the project; hits were downstream lower-bound and right-to-left bridge theorems that unfold this formula, not a named generic coefficient definition
-- minimal hypotheses: all already minimal; the definition needs only the four scalar schedules and epoch index

/-- The smooth-epoch left coefficient from scalar epoch schedules.

For epoch length `T`, step schedule `gamma`, averaging schedule `alpha`, and
momentum schedule `p`, this is the coefficient
`gamma_s / alpha_s + (T_s - 1) * gamma_s * (alpha_s + p_s) / alpha_s`
that appears as the left-side mass in smooth accelerated epoch telescopes.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; closed-form scalar coefficient assembled
  from epoch length, step, averaging, and momentum schedules)
Source: Lan smooth variance-reduced accelerated gradient parameter recurrences
  and Mathlib real arithmetic over natural-number casts
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  and left-coefficient lower-bound steps
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothEpochLeftCoeff (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (s : Nat) : Real :=
  gamma s / alpha s +
    ((T s - 1 : Nat) : Real) * (gamma s * (alpha s + p s) / alpha s)

/-- The smooth-epoch left coefficient unfolds to its closed scalar formula.

Layer: Model | Gap: Level 0 (smooth-epoch left coefficient formula)
Proof: by rfl after unfolding `smoothEpochLeftCoeff`.
Source: Mathlib definitional equality and real arithmetic over natural-number
  casts
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  and left-coefficient lower-bound steps
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem smoothEpochLeftCoeff_def
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat) :
    smoothEpochLeftCoeff T gamma alpha p s =
      gamma s / alpha s +
        ((T s - 1 : Nat) : Real) *
          (gamma s * (alpha s + p s) / alpha s) := rfl

/-- The smooth-epoch left coefficient is nonnegative for nonnegative numerator
schedules and a positive averaging schedule.

Layer: Model | Gap: Level 0 (smooth-epoch left coefficient sign)
Proof: the closed formula is a sum of nonnegative terms.
Source: Mathlib ordered-field arithmetic and nonnegativity of natural casts
Used in: variance-reduced accelerated gradient descent coefficient lower-bound
  steps
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothEpochLeftCoeff_nonneg
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat)
    (hgamma : 0 <= gamma s) (halpha : 0 < alpha s) (hp : 0 <= p s) :
    0 <= smoothEpochLeftCoeff T gamma alpha p s := by
  rw [smoothEpochLeftCoeff_def]
  exact add_nonneg
    (div_nonneg hgamma (le_of_lt halpha))
    (mul_nonneg (by positivity)
      (div_nonneg
        (mul_nonneg hgamma (add_nonneg (le_of_lt halpha) hp))
        (le_of_lt halpha)))



-- Generalization plan (G0):
-- concept/name: smooth-epoch right coefficient; orig was smoothEpochROf
-- generality used: scalar epoch schedules only; no carrier, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: smooth variance-reduced accelerated epoch proofs instantiate the epoch length, step, averaging, and momentum schedules to name the lagged right-side coefficient before adjacent-coefficient telescope handoff arguments
-- counterargument checked: this is a formula-bodied definition, but it names the recurring `R_s` coefficient paired with `smoothEpochLeftCoeff` and consumed by coefficient-bridge/telescope lemmas; it is not paper-local after removing setup fields and theorem numbers
-- coverage search: searched smoothEpochRightCoeff/smooth epoch right coefficient/R_s/gamma alpha p T in SOptLib, Staging, registry, and the project; hits were bridge inequalities that inline this formula, not a named generic coefficient definition
-- minimal hypotheses: all already minimal; the definition needs only the four scalar schedules and epoch index

/-- The smooth-epoch right coefficient from scalar epoch schedules.

For epoch length `T`, step schedule `gamma`, averaging schedule `alpha`, and
momentum schedule `p`, this is the coefficient
`gamma_s / alpha_s * (1 - alpha_s) + (T_s - 1) * gamma_s * p_s / alpha_s`
that appears as the lagged right-side mass in smooth accelerated epoch
telescopes.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; closed-form scalar coefficient assembled
  from epoch length, step, averaging, and momentum schedules)
Source: Lan smooth variance-reduced accelerated gradient parameter recurrences
  and Mathlib real arithmetic over natural-number casts
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  and adjacent right-to-left coefficient handoff steps
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothEpochRightCoeff (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (s : Nat) : Real :=
  gamma s / alpha s * (1 - alpha s) +
    ((T s - 1 : Nat) : Real) * (gamma s * p s / alpha s)

/-- The smooth-epoch right coefficient unfolds to its closed scalar formula.

Layer: Model | Gap: Level 0 (smooth-epoch right coefficient formula)
Proof: by rfl after unfolding `smoothEpochRightCoeff`.
Source: Mathlib definitional equality and real arithmetic over natural-number
  casts
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  and adjacent right-to-left coefficient handoff steps
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem smoothEpochRightCoeff_def
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat) :
    smoothEpochRightCoeff T gamma alpha p s =
      gamma s / alpha s * (1 - alpha s) +
        ((T s - 1 : Nat) : Real) * (gamma s * p s / alpha s) := rfl

/-- The smooth-epoch right coefficient is nonnegative for nonnegative numerator
schedules, a positive averaging schedule, and `alpha_s ≤ 1`.

Layer: Model | Gap: Level 0 (smooth-epoch right coefficient sign)
Proof: the closed formula is a sum of nonnegative terms; the first term uses
  `1 - alpha_s ≥ 0`, and the second uses nonnegativity of natural casts.
Source: Mathlib ordered-field arithmetic and nonnegativity of natural casts
Used in: variance-reduced accelerated gradient descent coefficient handoff and
  telescope-weight nonnegativity checks
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothEpochRightCoeff_nonneg
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat)
    (hgamma : 0 <= gamma s) (halpha_pos : 0 < alpha s)
    (halpha_le_one : alpha s <= 1) (hp : 0 <= p s) :
    0 <= smoothEpochRightCoeff T gamma alpha p s := by
  rw [smoothEpochRightCoeff_def]
  exact add_nonneg
    (mul_nonneg
      (div_nonneg hgamma (le_of_lt halpha_pos))
      (sub_nonneg.mpr halpha_le_one))
    (mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg hgamma hp) (le_of_lt halpha_pos)))



-- Generalization plan (G0):
-- concept/name: smooth-epoch bridge weight; orig was smoothEpochWeightOf
-- generality used: scalar epoch schedules only; no carrier, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: smooth variance-reduced accelerated epoch proofs instantiate the epoch length, step, averaging, and momentum schedules to name the cross-epoch telescope weight before nonnegativity, weighted-average, and retained-gap arguments
-- counterargument checked: this is a formula-bodied definition, but it names the recurring bridge coefficient `L_s - R_{s+1}` between already staged left and right coefficients; it is not paper-local after removing setup fields and theorem numbers
-- coverage search: searched smoothEpochBridgeWeight/smooth epoch bridge weight/L_s - R_{s+1}/smoothEpochWeight in SOptLib, Staging, registry, and the project; hits were the staged left/right coefficient definitions and adjacent right-to-left inequality, not a named bridge-weight definition
-- minimal hypotheses: all already minimal; the definition needs only the four scalar schedules and epoch index

/-- The smooth-epoch bridge weight between adjacent scalar epoch coefficients.

For epoch length `T`, step schedule `gamma`, averaging schedule `alpha`, and
momentum schedule `p`, this is the cross-epoch telescope weight
`L_s - R_{s+1}` built from `smoothEpochLeftCoeff` and
`smoothEpochRightCoeff`.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; adjacent difference of the smooth-epoch
  left coefficient and the next smooth-epoch right coefficient)
Source: Lan smooth variance-reduced accelerated gradient parameter recurrences
  and Mathlib real arithmetic over scalar schedule coefficients
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  weights, weighted averages, and retained objective-gap terms
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothEpochBridgeWeight (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (s : Nat) : Real :=
  smoothEpochLeftCoeff T gamma alpha p s -
    smoothEpochRightCoeff T gamma alpha p (s + 1)

/-- The smooth-epoch bridge weight unfolds to the adjacent coefficient
difference `L_s - R_{s+1}`.

Layer: Model | Gap: Level 0 (smooth-epoch bridge weight formula)
Proof: by rfl after unfolding `smoothEpochBridgeWeight`.
Source: Mathlib definitional equality and real arithmetic over scalar schedule
  coefficients
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  weights and weighted-average normalization
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem smoothEpochBridgeWeight_def
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat) :
    smoothEpochBridgeWeight T gamma alpha p s =
      smoothEpochLeftCoeff T gamma alpha p s -
        smoothEpochRightCoeff T gamma alpha p (s + 1) := rfl

/-- The smooth-epoch bridge weight is nonnegative when the next right
coefficient is bounded by the current left coefficient.

Layer: Model | Gap: Level 0 (smooth-epoch bridge weight sign)
Proof: unfold the bridge weight and apply the ordered-ring characterization
  of nonnegative subtraction.
Source: Mathlib ordered-ring subtraction APIs over real scalar coefficients
Used in: variance-reduced accelerated gradient descent smooth-epoch telescope
  nonnegativity checks before forming weighted averages
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothEpochBridgeWeight_nonneg_of_right_succ_le_left
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat)
    (h :
      smoothEpochRightCoeff T gamma alpha p (s + 1) <=
        smoothEpochLeftCoeff T gamma alpha p s) :
    0 <= smoothEpochBridgeWeight T gamma alpha p s := by
  rw [smoothEpochBridgeWeight_def]
  exact sub_nonneg.mpr h


-- Generalization plan (G0):
-- concept/name: base-two floor-log cutoff parameter choice; orig was `theorem59Cutoff`
-- generality used: real scalar size parameter only; no carrier type, measure, convexity, smoothness, oracle, filtration, or finite-dimensional hypothesis is used
-- portable call pattern: finite-sum phased algorithms instantiate the component count, batch scale, or active coordinate count as `m` while reusing the same base-two doubling-phase cutoff
-- counterargument checked: this is a formula-bodied definition, but it names a recurring parameter selector consumed by generic doubling/frozen epoch schedules and logarithmic selector bounds; it is not just paper traceability after removing setup fields and theorem numbering
-- coverage search: searched SOptLib, Staging, registry, and CATALOG for `floorLogTwoCutoff`, `floor log two`, `Nat.floor (Real.log _ / Real.log 2)`, and logarithmic cutoff; existing `max_one_ceil_log_div_le_floor_log_of_div_le` is a theorem about this expression, while Mathlib hits `Nat.log`, `Nat.clog`, and `Real.floor_logb_natCast` do not provide this real-parameter cutoff selector
-- minimal hypotheses: all already minimal; the definition requires only the real parameter `m`



/-- The base-two floor-log cutoff associated to a positive scale parameter.

For a real scale `m`, this is the natural cutoff `floor (log m / log 2) + 1`
used to stop one-based doubling phases before switching to a frozen or tail
schedule.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; closed-form natural-number selector from a
  base-two real logarithm and natural floor)
Source: Mathlib real logarithm and natural floor APIs for scalar parameter
  choices in finite-sum doubling schedules
Used in: variance-reduced accelerated-gradient epoch construction where early
  finite-sum epochs double up to the component-count logarithmic cutoff
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def floorLogTwoCutoff (m : Real) : Nat :=
  Nat.floor (Real.log m / Real.log 2) + 1

/-- The base-two floor-log cutoff unfolds to `floor (log m / log 2) + 1`.

Layer: Model | Gap: Level 0 (base-two floor-log cutoff unfolding)
Proof: by rfl after unfolding `floorLogTwoCutoff`.
Source: Mathlib real logarithm and natural floor APIs for scalar parameter
  choices in finite-sum doubling schedules
Used in: variance-reduced accelerated-gradient epoch construction where early
  finite-sum epochs double up to the component-count logarithmic cutoff
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem floorLogTwoCutoff_def (m : Real) :
    floorLogTwoCutoff m =
      Nat.floor (Real.log m / Real.log 2) + 1 := rfl

/-- The base-two floor-log cutoff is always at least one.

Layer: Model | Gap: Level 0 (base-two floor-log cutoff lower bound)
Proof: the cutoff is a natural number plus one.
Source: Mathlib natural-number order API for scalar parameter choices
Used in: epoch schedules whose first phase requires a positive cutoff -/
theorem one_le_floorLogTwoCutoff (m : Real) :
    1 <= floorLogTwoCutoff m := by
  rw [floorLogTwoCutoff_def]
  exact Nat.succ_le_succ (Nat.zero_le _)


-- Generalization plan (G0):
-- concept/name: doubling-then-frozen epoch length schedule; orig was theorem59EpochLength, renamed away from theorem numbering and setup fields
-- generality used: natural-number cutoff and epoch index only; no carrier, measure, convexity, smoothness, oracle, topology, norm, inner product, or finite-dimensional hypotheses are used
-- portable call pattern: finite-sum variance-reduced and accelerated epoch proofs instantiate a cutoff and epoch index to reuse the same schedule when early epochs double and all later epochs use the cutoff length
-- counterargument checked: not paper-local traceability because the theorem-numbered setup argument was removed; not covered by Mathlib/SOptLib because existing accelerated schedules are Gamma/weight recurrences or epoch accounting, not this piecewise length schedule
-- coverage search: searched CATALOG.md, SOptLib, Staging, registry, and the algorithm file for epoch length/doubling/frozen/cutoff; LeanSearch for a natural-number schedule that doubles until a cutoff then remains frozen returned only generic doubling/eventual-constant facts
-- minimal hypotheses: all already minimal for the definition; branch and base lemmas use only the pointwise cutoff comparison required by the corresponding branch

/-- Epoch lengths that double until a cutoff and then stay frozen.

The one-based schedule is `2^(s-1)` through the cutoff epoch and remains
fixed at the cutoff value afterward.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; piecewise one-based natural-number epoch
  length schedule with a frozen post-cutoff branch)
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient epoch construction where early
  epoch lengths double and the strongly-convex tail reuses the cutoff length
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def doublingThenFrozenEpochLength (cutoff s : Nat) : Nat :=
  if s <= cutoff then
    2 ^ (s - 1)
  else
    2 ^ (cutoff - 1)

/-- The doubling-then-frozen epoch length unfolds to its two-branch formula.

Layer: Model | Gap: Level 0 (doubling-then-frozen epoch length unfolding)
Proof: by rfl after unfolding `doublingThenFrozenEpochLength`.
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient epoch construction where early
  epoch lengths double and the strongly-convex tail reuses the cutoff length
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem doublingThenFrozenEpochLength_def (cutoff s : Nat) :
    doublingThenFrozenEpochLength cutoff s =
      if s <= cutoff then
        2 ^ (s - 1)
      else
        2 ^ (cutoff - 1) := by
  rfl

/-- Before or at the cutoff, the doubling-then-frozen epoch length is
`2^(s-1)`.

Layer: Model | Gap: Level 0 (pre-cutoff epoch length branch)
Proof: unfold `doublingThenFrozenEpochLength` and select the true branch.
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient first-phase epoch arithmetic
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem doublingThenFrozenEpochLength_of_le {cutoff s : Nat}
    (h : s <= cutoff) :
    doublingThenFrozenEpochLength cutoff s = 2 ^ (s - 1) := by
  simp [doublingThenFrozenEpochLength, h]

/-- After the cutoff, the doubling-then-frozen epoch length is the cutoff
length.

Layer: Model | Gap: Level 0 (post-cutoff frozen epoch length branch)
Proof: unfold `doublingThenFrozenEpochLength` and select the false branch.
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient tail epoch arithmetic
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem doublingThenFrozenEpochLength_of_cutoff_lt {cutoff s : Nat}
    (h : cutoff < s) :
    doublingThenFrozenEpochLength cutoff s = 2 ^ (cutoff - 1) := by
  simp [doublingThenFrozenEpochLength, Nat.not_le.mpr h]

/-- Doubling-then-frozen epoch lengths are always positive.

Layer: Model | Gap: Level 0 (doubling-then-frozen epoch length positivity)
Proof: unfold the two schedule branches and use positivity of natural-number
  powers of two.
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient epoch windows indexed by
  `Fin (doublingThenFrozenEpochLength cutoff s)`
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem doublingThenFrozenEpochLength_pos (cutoff s : Nat) :
    0 < doublingThenFrozenEpochLength cutoff s := by
  unfold doublingThenFrozenEpochLength
  split_ifs <;> positivity

/-- The first epoch has length one whenever the cutoff includes epoch one.

Layer: Model | Gap: Level 0 (initial doubling-then-frozen epoch length)
Proof: use the pre-cutoff branch at epoch one and simplify the exponent.
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient initialization of one-based
  epoch windows
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem doublingThenFrozenEpochLength_one {cutoff : Nat}
    (hcutoff : 1 <= cutoff) :
    doublingThenFrozenEpochLength cutoff 1 = 1 := by
  simp [doublingThenFrozenEpochLength, hcutoff]

/-- First-phase epoch lengths double from one epoch to the next.

Layer: Model | Gap: Level 0 (first-phase epoch length doubling)
Proof: both adjacent epochs are in the pre-cutoff branch, then natural-number
  exponentiation reduces by `Nat.pow_succ`.
Source: finite-sum variance-reduction epoch schedules and Mathlib natural
  number exponentiation APIs
Used in: variance-reduced accelerated-gradient first-phase Lyapunov recurrence
  rewriting
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem doublingThenFrozenEpochLength_first_phase_doubling {cutoff s : Nat}
    (hs : 2 <= s) (hs0 : s <= cutoff) :
    doublingThenFrozenEpochLength cutoff s =
      2 * doublingThenFrozenEpochLength cutoff (s - 1) := by
  have hprev_strict : s - 2 < cutoff := by
    omega
  have hs_pred : s - 1 = (s - 2) + 1 := by
    omega
  simp [doublingThenFrozenEpochLength, hs0, hprev_strict, hs_pred,
    Nat.pow_succ]
  ring


-- Generalization plan (G0):
-- concept/name: capped doubling epoch length cutoff-bound propagation; orig was `smooth_epoch_length_le_component_count`, renamed away from smooth-case and theorem-numbered setup names
-- generality used: natural-number cutoff, named doubling-then-frozen epoch schedule, and a real scalar component-count bound; no carrier type, measure, convexity, smoothness, oracle, filtration, topology, norm, inner product, or finite-dimensional hypothesis is used
-- portable call pattern: finite-sum variance-reduced and accelerated-gradient proofs first prove the cutoff epoch is at most the refresh/component count, then reuse the same capped-doubling bound for every generated epoch while changing the component count, cutoff, or cutoff-bound proof
-- counterargument checked: not paper-local traceability because the statement is over the reusable `doublingThenFrozenEpochLength` schedule and an abstract scalar cap; not a pure wrapper around the floor-log lemma because it propagates any cutoff bound to all epochs of the capped schedule
-- coverage search: searched project/catalog tokens `epochLength`, `doublingThenFrozenEpochLength`, `componentCount`, `floorLogTwoCutoff`, and `two_pow_floor`; relevant hits were the schedule definition `doublingThenFrozenEpochLength`, the scalar cutoff theorem `two_pow_floor_log_div_log_two_le_self`, and the finite-sum call-count bound, but none states this all-epochs cap inheritance theorem
-- minimal hypotheses: the only proof input is the pointwise real bound on the cutoff epoch length; the floor-log construction and algorithm setup assumptions are deliberately left to callers

/-- A capped doubling epoch schedule is bounded everywhere by any bound on its
cutoff epoch.

For the named one-based schedule that doubles until `cutoff` and is frozen
afterward, the cutoff epoch is a maximum. Thus any real upper bound on the
cutoff length also bounds the length of every epoch.

Layer: Model | Gap: Level 0 (capped doubling epoch-length upper bound)
Proof: compare the natural epoch length to the cutoff length by case-splitting
  on whether the epoch is before the cutoff, then cast the natural inequality
  to `Real` and compose with the supplied cutoff bound.
Source: Mathlib natural-number exponentiation, subtraction monotonicity, and
  natural-to-real cast order APIs
Used in: variance-reduced accelerated-gradient component-gradient accounting
  after bounding the cutoff epoch by the finite-sum component count
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem doublingThenFrozenEpochLength_natCast_le_of_cutoff_natCast_le
    {m : Real} {cutoff : Nat}
    (hcutoff_le :
      (((doublingThenFrozenEpochLength cutoff cutoff : Nat) : Real)) <= m)
    (s : Nat) :
    (((doublingThenFrozenEpochLength cutoff s : Nat) : Real)) <= m := by
  have hlen_nat :
      doublingThenFrozenEpochLength cutoff s <=
        doublingThenFrozenEpochLength cutoff cutoff := by
    by_cases hs : s <= cutoff
    · have hpow_le :
          2 ^ (s - 1) <= 2 ^ (cutoff - 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2)
          (Nat.sub_le_sub_right hs 1)
      simpa [doublingThenFrozenEpochLength, hs] using hpow_le
    · simp [doublingThenFrozenEpochLength, hs]
  have hlen_real :
      (((doublingThenFrozenEpochLength cutoff s : Nat) : Real)) <=
        (((doublingThenFrozenEpochLength cutoff cutoff : Nat) : Real)) := by
    exact_mod_cast hlen_nat
  exact hlen_real.trans hcutoff_le



-- Generalization plan (G0):
-- concept/name: lower bound for an intermediate smooth-epoch left coefficient; orig was lemma520_smoothEpochL_lower_bound_intermediate
-- generality used: scalar real schedules only; no carrier, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: accelerated epoch schedule proofs with alpha_s = 2/(s-cutoff+4) and a lower bound m/2 <= T_s use the same square-coefficient lower bound while changing the epoch-length source
-- counterargument checked: not paper-local traceability because setup fields, theorem numbers, and component-count notation are removed; not a duplicate of the sharp staged theorem because this statement replaces the frozen cutoff length conclusion with an abstract real length lower bound m
-- coverage search: searched smoothEpoch/left coefficient/lower bound/intermediate schedule in SOptLib, Staging, registry, and Mathlib semantic search; the sharp staged theorem is related but retains T_cutoff, the right-to-left bridge has a different conclusion, and Mathlib hits were unrelated recurrence/asymptotic lower bounds
-- minimal hypotheses: pointwise schedule equations, positive smoothness scale, positive epoch length, strict intermediate cutoff, and the length lower bound m/2 <= T_s; global setup, frozen-length equality, tail cutoff, small-component, and finite-dimensional assumptions were dropped

/-- A square lower bound for the intermediate smooth-epoch left coefficient.

For the intermediate branch `alpha_s = 2 / (s - cutoff + 4)`, with `p_s = 1/2`
and the inverse smoothness rule for `gamma`, the left coefficient dominates
`(s-cutoff+4)^2 m/(48L)` whenever the epoch length is at least `m/2`.

Layer: Model | Gap: Level 1 (intermediate smooth-epoch left coefficient lower bound)
Proof: substitute the pointwise schedule equations, convert the natural
  predecessor cast using the localized epoch-length positivity, and
  reduce the remaining inequality to ordered-field arithmetic.
Source: Mathlib ordered-field arithmetic over real schedules and natural-number
  casts
Used in: variance-reduced accelerated gradient descent epoch telescope lower
  bound for the intermediate smooth branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smooth_epoch_left_coeff_lower_bound_of_intermediate_schedule
    (L : Real) (T : Nat -> Nat) (alpha gamma p : Nat -> Real)
    (cutoff : Nat) {s : Nat} (m : Real)
    (hL_pos : 0 < L)
    (hT_pos : 0 < T s)
    (hs_left : cutoff < s)
    (hp_s : p s = (1 / 2 : Real))
    (halpha_s : alpha s = 2 / (((s - cutoff + 4 : Nat) : Real)))
    (hgamma_s : gamma s = 1 / (3 * L * alpha s))
    (hT_lower : m / 2 <= ((T s : Nat) : Real)) :
    (((s : Real) - cutoff + 4) ^ 2 * m) / (48 * L) <=
      gamma s / alpha s +
        (((T s - 1 : Nat) : Real)) *
          (gamma s * (alpha s + p s) / alpha s) := by
  let d : Real := ((s - cutoff + 4 : Nat) : Real)
  have hd_pos : 0 < d := by
    dsimp [d]
    have hden_nat : 0 < s - cutoff + 4 := by
      omega
    exact_mod_cast hden_nat
  have hd_real :
      d = (s : Real) - cutoff + 4 := by
    dsimp [d]
    have hsub : cutoff <= s := le_of_lt hs_left
    norm_num [Nat.cast_sub hsub]
  have hTsub_cast :
      ((T s - 1 : Nat) : Real) = ((T s : Nat) : Real) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hT_pos)]
    norm_num
  have hmain :
      d ^ 2 * m / (48 * L) <=
        gamma s / alpha s +
          (((T s - 1 : Nat) : Real)) *
            (gamma s * (alpha s + p s) / alpha s) := by
    rw [hgamma_s, halpha_s, hp_s, hTsub_cast]
    have hden_alpha : 2 / d ≠ 0 := by
      exact ne_of_gt (div_pos (by norm_num) hd_pos)
    field_simp [hden_alpha, ne_of_gt hL_pos, ne_of_gt hd_pos]
    nlinarith [hT_lower, sq_nonneg d]
  simpa [hd_real] using hmain



-- Generalization plan (G0):
-- concept/name: adjacent smooth-epoch coefficient bridge; orig was lemma520_smoothEpochR_succ_le_smoothEpochL_intermediate
-- generality used: scalar real schedules only; no carrier, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: accelerated epoch telescopes with a frozen post-cutoff epoch length instantiate alpha/gamma/p branch formulas and close the handoff condition R_{j+1} <= L_j
-- counterargument checked: not paper-local traceability because the statement removes setup fields and theorem numbers; not a wrapper because Mathlib/SOptLib telescope lemmas consume this bridge rather than deriving it
-- coverage search: searched smoothEpoch/right/left/intermediate/frozen coefficient bridge in SOptLib, Staging, and Mathlib semantic search; hits were generic weighted telescope consumers, not this schedule-derived bridge
-- minimal hypotheses: pointwise schedule hypotheses only; the unused small-component assumption, cutoff window, and algorithm setup fields were dropped

/-- The next smooth-epoch right coefficient is bounded by the current left
coefficient in the intermediate schedule branch.

The hypotheses isolate the branch facts needed by accelerated epoch telescopes:
`p_j = p_{j+1} = 1/2`, the cutoff/intermediate formulas for `alpha_j` and
`alpha_{j+1}`, the standard inverse relation for `gamma`, and a frozen adjacent
epoch length.

Layer: Model | Gap: Level 1 (intermediate smooth-epoch coefficient bridge)
Proof: split on whether the epoch is exactly the cutoff. After substituting the
  schedule formulas, both branches reduce to scalar real inequalities discharged
  by ordered-field arithmetic.
Source: Mathlib ordered-field arithmetic over real schedules and natural-number
  casts
Used in: variance-reduced accelerated gradient descent epoch telescope handoff
  from the intermediate smooth branch to adjacent coefficient weights
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smooth_epoch_right_succ_le_left_of_intermediate_schedule
    (L : Real) (T : Nat -> Nat) (alpha gamma p : Nat -> Real)
    (cutoff : Nat) {j : Nat}
    (hL_pos : 0 < L)
    (hj_left : cutoff <= j)
    (hp_j : p j = (1 / 2 : Real))
    (hp_succ : p (j + 1) = (1 / 2 : Real))
    (halpha_j_cutoff : j = cutoff -> alpha j = (1 / 2 : Real))
    (halpha_j_intermediate :
      cutoff < j -> alpha j = 2 / (((j - cutoff + 4 : Nat) : Real)))
    (halpha_succ :
      alpha (j + 1) = 2 / (((j + 1 - cutoff + 4 : Nat) : Real)))
    (hgamma_j : gamma j = 1 / (3 * L * alpha j))
    (hgamma_succ : gamma (j + 1) = 1 / (3 * L * alpha (j + 1)))
    (hT_succ_eq : T (j + 1) = T j)
    (hT_pos : 0 < T j) :
    gamma (j + 1) / alpha (j + 1) * (1 - alpha (j + 1)) +
        (((T (j + 1) - 1 : Nat) : Real)) *
          (gamma (j + 1) * p (j + 1) / alpha (j + 1)) <=
      gamma j / alpha j +
        (((T j - 1 : Nat) : Real)) *
          (gamma j * (alpha j + p j) / alpha j) := by
  classical
  by_cases hj_eq : j = cutoff
  · subst j
    let T0 : Real := ((T cutoff : Nat) : Real)
    have hden_succ :
        (((cutoff + 1 - cutoff + 4 : Nat) : Real)) = (5 : Real) := by
      have hn : cutoff + 1 - cutoff + 4 = 5 := by omega
      exact_mod_cast hn
    have halpha_succ : alpha (cutoff + 1) = (2 / 5 : Real) := by
      rw [halpha_succ, hden_succ]
    have halpha_cutoff : alpha cutoff = (1 / 2 : Real) :=
      halpha_j_cutoff rfl
    have hgamma_cutoff : gamma cutoff = 2 / (3 * L) := by
      rw [hgamma_j, halpha_cutoff]
      field_simp [ne_of_gt hL_pos]
    have hgamma_succ : gamma (cutoff + 1) = 5 / (6 * L) := by
      rw [hgamma_succ, halpha_succ]
      field_simp [ne_of_gt hL_pos]
      ring
    have hT_ge : (1 : Real) <= T0 := by
      dsimp [T0]
      exact_mod_cast (Nat.succ_le_of_lt hT_pos)
    have hTsub_cutoff : (((T cutoff - 1 : Nat) : Real)) = T0 - 1 := by
      dsimp [T0]
      rw [Nat.cast_sub (Nat.succ_le_of_lt hT_pos)]
      norm_num
    have hleft :
        gamma cutoff / alpha cutoff +
            (((T cutoff - 1 : Nat) : Real)) *
              (gamma cutoff * (alpha cutoff + p cutoff) / alpha cutoff) =
          4 * T0 / (3 * L) := by
      rw [hgamma_cutoff, halpha_cutoff, hp_j, hTsub_cutoff]
      dsimp [T0]
      field_simp [ne_of_gt hL_pos]
      ring
    have hright :
        gamma (cutoff + 1) / alpha (cutoff + 1) *
              (1 - alpha (cutoff + 1)) +
            (((T (cutoff + 1) - 1 : Nat) : Real)) *
              (gamma (cutoff + 1) * p (cutoff + 1) / alpha (cutoff + 1)) =
          (25 * T0 + 5) / (24 * L) := by
      rw [hgamma_succ, halpha_succ, hp_succ, hT_succ_eq, hTsub_cutoff]
      dsimp [T0]
      field_simp [ne_of_gt hL_pos]
      ring
    have hscalar : (25 * T0 + 5) / (24 * L) <= 4 * T0 / (3 * L) := by
      have hden_left : 0 < 24 * L := by positivity
      have hden_right : 0 < 3 * L := by positivity
      rw [div_le_div_iff₀ hden_left hden_right]
      nlinarith
    calc
      gamma (cutoff + 1) / alpha (cutoff + 1) *
              (1 - alpha (cutoff + 1)) +
            (((T (cutoff + 1) - 1 : Nat) : Real)) *
              (gamma (cutoff + 1) * p (cutoff + 1) / alpha (cutoff + 1))
          = (25 * T0 + 5) / (24 * L) := hright
      _ <= 4 * T0 / (3 * L) := hscalar
      _ = gamma cutoff / alpha cutoff +
            (((T cutoff - 1 : Nat) : Real)) *
              (gamma cutoff * (alpha cutoff + p cutoff) / alpha cutoff) := by
        rw [hleft]
  · let T0 : Real := ((T j : Nat) : Real)
    let d : Real := ((j - cutoff + 4 : Nat) : Real)
    have hcut_j : cutoff < j := by omega
    have halpha_j : alpha j = 2 / d := by
      simpa [d] using halpha_j_intermediate hcut_j
    have hden_succ :
        (((j + 1 - cutoff + 4 : Nat) : Real)) = d + 1 := by
      dsimp [d]
      have hn : j + 1 - cutoff + 4 = j - cutoff + 4 + 1 := by omega
      calc
        (((j + 1 - cutoff + 4 : Nat) : Real)) =
            ((j - cutoff + 4 + 1 : Nat) : Real) := by exact_mod_cast hn
        _ = ((j - cutoff + 4 : Nat) : Real) + 1 := by norm_num
    have halpha_succ : alpha (j + 1) = 2 / (d + 1) := by
      rw [halpha_succ, hden_succ]
    have hd_pos : 0 < d := by
      dsimp [d]
      have hn : 0 < j - cutoff + 4 := by omega
      exact_mod_cast hn
    have hd_succ_pos : 0 < d + 1 := by linarith
    have hd_ge : (5 : Real) <= d := by
      dsimp [d]
      have hn : 5 <= j - cutoff + 4 := by omega
      exact_mod_cast hn
    have hgamma_j : gamma j = d / (6 * L) := by
      rw [hgamma_j, halpha_j]
      field_simp [ne_of_gt hL_pos, ne_of_gt hd_pos]
      ring
    have hgamma_succ : gamma (j + 1) = (d + 1) / (6 * L) := by
      rw [hgamma_succ, halpha_succ]
      field_simp [ne_of_gt hL_pos, ne_of_gt hd_succ_pos]
      ring
    have hT_ge : (1 : Real) <= T0 := by
      dsimp [T0]
      exact_mod_cast (Nat.succ_le_of_lt hT_pos)
    have hTsub_j : (((T j - 1 : Nat) : Real)) = ((T j : Nat) : Real) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hT_pos)]
      norm_num
    have hleft :
        gamma j / alpha j +
            (((T j - 1 : Nat) : Real)) *
              (gamma j * (alpha j + p j) / alpha j) =
          (d ^ 2 / 4 + (T0 - 1) * (d / 2 + d ^ 2 / 8)) / (3 * L) := by
      have hTj_cast : (((T j : Nat) : Real)) = T0 := by
        rfl
      rw [hgamma_j, halpha_j, hp_j, hTsub_j, hTj_cast]
      dsimp [T0]
      field_simp [ne_of_gt hL_pos, ne_of_gt hd_pos]
      ring
    have hright :
        gamma (j + 1) / alpha (j + 1) * (1 - alpha (j + 1)) +
            (((T (j + 1) - 1 : Nat) : Real)) *
              (gamma (j + 1) * p (j + 1) / alpha (j + 1)) =
          ((d ^ 2 - 1) / 4 + (T0 - 1) * (d + 1) ^ 2 / 8) / (3 * L) := by
      rw [hgamma_succ, halpha_succ, hp_succ, hT_succ_eq, hTsub_j]
      have hTj_cast : (((T j : Nat) : Real)) = T0 := by
        rfl
      rw [hTj_cast]
      dsimp [T0]
      field_simp [ne_of_gt hL_pos, ne_of_gt hd_succ_pos]
      ring
    have hscalar :
        ((d ^ 2 - 1) / 4 + (T0 - 1) * (d + 1) ^ 2 / 8) / (3 * L) <=
          (d ^ 2 / 4 + (T0 - 1) * (d / 2 + d ^ 2 / 8)) / (3 * L) := by
      have hden : 0 < 3 * L := by positivity
      have hinner :
          (d ^ 2 - 1) / 4 + (T0 - 1) * (d + 1) ^ 2 / 8 <=
            d ^ 2 / 4 + (T0 - 1) * (d / 2 + d ^ 2 / 8) := by
        have hdiff :
            d ^ 2 / 4 + (T0 - 1) * (d / 2 + d ^ 2 / 8) -
                ((d ^ 2 - 1) / 4 + (T0 - 1) * (d + 1) ^ 2 / 8) =
              1 / 4 + (T0 - 1) * (2 * d - 1) / 8 := by
          ring
        have hnonneg : 0 <= 1 / 4 + (T0 - 1) * (2 * d - 1) / 8 := by
          have hTminus : 0 <= T0 - 1 := by linarith
          have hdterm : 0 <= 2 * d - 1 := by nlinarith
          positivity
        linarith
      rw [div_le_div_iff₀ hden hden]
      exact mul_le_mul_of_nonneg_right hinner (le_of_lt hden)
    calc
      gamma (j + 1) / alpha (j + 1) * (1 - alpha (j + 1)) +
            (((T (j + 1) - 1 : Nat) : Real)) *
              (gamma (j + 1) * p (j + 1) / alpha (j + 1))
          = ((d ^ 2 - 1) / 4 + (T0 - 1) * (d + 1) ^ 2 / 8) / (3 * L) := hright
      _ <= (d ^ 2 / 4 + (T0 - 1) * (d / 2 + d ^ 2 / 8)) / (3 * L) := hscalar
      _ = gamma j / alpha j +
            (((T j - 1 : Nat) : Real)) *
              (gamma j * (alpha j + p j) / alpha j) := by
        rw [hleft]



private theorem parameterChoices_sum_range_if_succ_eq_last_else_const
    {M : Type*} [AddCommMonoid M]
    (N : Nat) (a b : M) :
    (Finset.range N).sum (fun k => if k + 1 = N then a else b) =
      if N = 0 then 0 else a + (N - 1) • b := by
  induction N with
  | zero =>
      simp
  | succ N _ih =>
      cases N with
      | zero =>
          simp
      | succ N =>
          have hprev_ne_top : forall k, k < N + 1 -> k + 1 ≠ N + 1 + 1 := by
            intro k hk
            omega
          calc
            (Finset.range (N + 1 + 1)).sum
                (fun k => if k + 1 = N + 1 + 1 then a else b) =
              (Finset.range (N + 1)).sum
                  (fun k => if k + 1 = N + 1 + 1 then a else b) + a := by
                rw [Finset.sum_range_succ]
                simp
            _ = (Finset.range (N + 1)).sum (fun _k => b) + a := by
                refine congrArg (fun z => z + a) ?_
                refine Finset.sum_congr rfl ?_
                intro k hk
                exact if_neg (hprev_ne_top k (Finset.mem_range.mp hk))
            _ = (N + 1) • b + a := by
                simp
            _ = a + ((N + 1 + 1) - 1) • b := by
                have hsub : (N + 1 + 1) - 1 = N + 1 := by omega
                rw [hsub]
                rw [add_comm]
            _ = (if N + 1 + 1 = 0 then 0
                  else a + ((N + 1 + 1) - 1) • b) := by
                simp

open scoped BigOperators


-- Generalization plan (G0):
-- concept/name: smooth-epoch theta mass equals the smooth-epoch left coefficient;
--   orig was `lemma520_smoothTheta_sum_eq_smoothEpochL`.
-- generality used: natural epoch-length schedules and real-valued `gamma`,
--   `alpha`, and `p` schedules; no carrier, measure, independence,
--   integrability, topology, norm, inner product, convexity, smoothness, oracle,
--   or finite-dimensional hypotheses are used.
-- portable call pattern: smooth accelerated finite-sum epoch recursions use the
--   same terminal/nonterminal theta profile to identify the total output weight
--   with the left coefficient before Jensen normalization; the concrete
--   `T`, `gamma`, `alpha`, and `p` schedules vary by algorithm branch.
-- counterargument checked: this is not a one-line paper traceability wrapper:
--   it composes the reusable `smoothEpochTheta` and `smoothEpochLeftCoeff`
--   objects with the terminal-exception finite-sum identity. It is not a
--   duplicate of `parameterChoices_sum_range_if_succ_eq_last_else_const`, which has no epoch
--   schedule or left-coefficient API, and not a duplicate of the admissibility
--   theorem, which proves positivity rather than the total mass formula.
-- coverage search: searched project/Staging/SOptLib/catalog for
--   `smoothEpochTheta`, `smoothEpochLeftCoeff`, `theta mass`, `sum_eq_leftCoeff`,
--   and `terminal_adjusted_smooth_epoch_weight`; hits were the schedule def,
--   coefficient def, admissibility theorem, and finite-sum terminal-exception
--   identity, but no theorem connecting the finite-window mass to the named
--   left coefficient.
-- minimal hypotheses: global setup and smoothness assumptions reduce to the
--   pointwise nonempty-window condition `0 < T s`; no positivity of `gamma`,
--   `alpha`, or `p` is needed for the equality.

/-- The finite-window mass of smooth-epoch theta weights is the smooth-epoch
left coefficient.

For any nonempty epoch, summing the one-based terminal-adjusted theta schedule
over `t = 1, ..., T_s` gives the closed coefficient `L_s`: one terminal atom
`gamma_s / alpha_s` plus `T_s - 1` interior atoms
`gamma_s / alpha_s * (alpha_s + p_s)`.

Layer: Model | Gap: Level 0 (smooth-epoch theta mass coefficient)
Proof: reindex the finite `Fin (T s)` sum as a natural range, apply the
  terminal-exception finite-sum identity, and unfold the named theta schedule
  and left coefficient.
Source: Mathlib finite sums over natural ranges and finite-sum accelerated
  gradient epoch parameter choices
Used in: variance-reduced accelerated gradient descent smooth-epoch output
  normalization before the Jensen bridge
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smooth_epoch_theta_sum_eq_left_coeff
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real) (s : Nat)
    (hT_pos : 0 < T s) :
    (Finset.univ.sum
        (fun t : Fin (T s) => smoothEpochTheta T gamma alpha p s (t.1 + 1))) =
      smoothEpochLeftCoeff T gamma alpha p s := by
  classical
  let a : Real := gamma s / alpha s
  let b : Real := gamma s / alpha s * (alpha s + p s)
  have hsum_range :
      (Finset.range (T s)).sum
          (fun k => smoothEpochTheta T gamma alpha p s (k + 1)) =
        smoothEpochLeftCoeff T gamma alpha p s := by
    have hshape :=
      parameterChoices_sum_range_if_succ_eq_last_else_const (M := Real) (T s) a b
    have hleft :
        (Finset.range (T s)).sum
            (fun k => smoothEpochTheta T gamma alpha p s (k + 1)) =
          (Finset.range (T s)).sum
            (fun k => if k + 1 = T s then a else b) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      simp [smoothEpochTheta, terminal_adjusted_smooth_epoch_weight, a, b]
    rw [hleft, hshape]
    have hT_ne : T s ≠ 0 := Nat.ne_of_gt hT_pos
    rw [if_neg hT_ne]
    dsimp [smoothEpochLeftCoeff, a, b]
    ring
  calc
    (Finset.univ.sum
        (fun t : Fin (T s) => smoothEpochTheta T gamma alpha p s (t.1 + 1))) =
      (Finset.range (T s)).sum
          (fun k => smoothEpochTheta T gamma alpha p s (k + 1)) := by
        rw [Finset.sum_fin_eq_sum_range]
        refine Finset.sum_congr rfl ?_
        intro k hk
        simp [Finset.mem_range.mp hk]
    _ = smoothEpochLeftCoeff T gamma alpha p s := hsum_range



private theorem parameterChoices_sum_range_terminal_geometric_sub_eq_tail_add_scaled_sum
    {R : Type*} [Ring R] (N : Nat) (base c : R) (hN : 0 < N) :
    (Finset.range N).sum
        (fun k => if k + 1 = N then base ^ k else base ^ k - c * base ^ (k + 1)) =
      c * base ^ N + (1 - c * base) *
        (Finset.range N).sum (fun k => base ^ k) := by
  cases N with
  | zero =>
      omega
  | succ N =>
      have hprev_ne_top :
          forall k, k < N -> Not (k + 1 = N + 1) := by
        intro k hk
        omega
      have hprev :
          (Finset.range N).sum
              (fun k =>
                if k + 1 = N + 1 then base ^ k else base ^ k - c * base ^ (k + 1)) =
            (Finset.range N).sum (fun k => base ^ k - c * base ^ (k + 1)) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [if_neg (hprev_ne_top k (Finset.mem_range.mp hk))]
      have hshift :
          (Finset.range N).sum (fun k => base ^ (k + 1)) =
            base * (Finset.range N).sum (fun k => base ^ k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _hk
        rw [pow_succ']
      have hshift_c :
          (Finset.range N).sum (fun k => c * base ^ (k + 1)) =
            c * (base * (Finset.range N).sum (fun k => base ^ k)) := by
        rw [hshift.symm]
        rw [Finset.mul_sum]
      rw [Finset.sum_range_succ]
      rw [if_pos rfl]
      rw [hprev]
      rw [Finset.sum_sub_distrib]
      rw [hshift_c]
      rw [Finset.sum_range_succ]
      rw [pow_succ']
      noncomm_ring

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: terminal-adjusted geometric theta-mass expansion; orig was
--   `lemma521_geometricTheta_sum_eq_tail_expansion`, renamed away from theorem
--   numbering and setup-local schedule names while preserving the standard
--   accelerated-epoch theta/Gamma terminology.
-- generality used: scalar schedules over a positive natural epoch length in a
--   commutative ring; no measure, independence, integrability, topology, norm,
--   inner product, convexity, smoothness, oracle, carrier, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: accelerated finite-sum and variance-reduced tail
--   proofs instantiate an epoch length, a geometric base, a terminal
--   coefficient, and theta/gamma schedules satisfying the same pointwise
--   one-based window equations; the conclusion rewrites total theta mass into
--   a terminal gamma correction plus a scaled gamma prefix sum.
-- counterargument checked: not a duplicate of the raw terminal-geometric range
--   identity because this theorem is the schedule API future proofs call after
--   naming `theta` and `gamma`; not paper-local traceability because setup
--   fields, theorem numbers, and Lan-specific notation are removed.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `terminalAdjustedGeometricTheta`, `geometric theta mass`, `theta sum`,
--   `geometricEpochTheta`, and terminal geometric expansions. Partial hits are
--   staged `geometricEpochTheta`/`geometricEpochGamma` definitions and
--   `parameterChoices_sum_range_terminal_geometric_sub_eq_tail_add_scaled_sum`, the raw scalar
--   identity this proof composes with. LeanSearch returned ordinary finite and
--   infinite geometric-series facts (`geom_sum_succ`, `tsum_geometric_*`) but
--   no terminal-adjusted theta/gamma schedule expansion.
-- minimal hypotheses: global algorithm assumptions reduce to `0 < T`, gamma's
--   geometric-power specification for indices `k ≤ T`, and theta's
--   terminal-adjusted difference specification for indices `k < T`.

/-- The sum of terminal-adjusted geometric theta weights expands into a terminal
gamma correction plus a scaled gamma-prefix mass.

On a positive one-based epoch window, suppose `gamma k = base^k` through the
terminal index and `theta (k+1)` is `gamma k` at the terminal atom, otherwise
`gamma k - c * gamma (k+1)`. Then the total theta mass is
`gamma T * c + (1 - c * base)` times the gamma mass over the prefix.

Layer: Model | Gap: Level 1 (terminal-adjusted geometric theta-mass expansion)
Proof: reindex the finite `Fin T` sums to `range T`, rewrite theta and gamma
  by their pointwise schedule specifications, apply the raw terminal-geometric
  range identity, and normalize the terminal gamma factor by commutative-ring
  arithmetic.
Source: Mathlib finite sums over natural ranges, natural powers, and
  finite-sum accelerated-gradient epoch parameter algebra in rings
Used in: variance-reduced accelerated-gradient tail-output theta-mass
  normalization before the small-epoch scalar coefficient comparison
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/15/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem terminal_adjusted_geometric_theta_sum_eq_tail_expansion
    {R : Type*} [CommRing R] (T : Nat) (base c : R)
    (theta gamma : Nat -> R) (hT : 0 < T)
    (hgamma : forall k, k <= T -> gamma k = base ^ k)
    (htheta : forall k, k < T ->
      theta (k + 1) = if k + 1 = T then gamma k else gamma k - c * gamma (k + 1)) :
    Finset.univ.sum (fun t : Fin T => theta (t.1 + 1)) =
      gamma T * c + (1 - c * base) *
        Finset.univ.sum (fun t : Fin T => gamma t.1) := by
  classical
  have htheta_range :
      Finset.univ.sum (fun t : Fin T => theta (t.1 + 1)) =
        (Finset.range T).sum
          (fun k => if k + 1 = T then base ^ k else base ^ k - c * base ^ (k + 1)) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkT : k < T := Finset.mem_range.mp hk
    have hgamma_k : gamma k = base ^ k := hgamma k (Nat.le_of_lt hkT)
    have hgamma_succ : gamma (k + 1) = base ^ (k + 1) :=
      hgamma (k + 1) (Nat.succ_le_of_lt hkT)
    simp [hkT, htheta k hkT, hgamma_k, hgamma_succ]
  have hgamma_range :
      Finset.univ.sum (fun t : Fin T => gamma t.1) =
        (Finset.range T).sum (fun k => base ^ k) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkT : k < T := Finset.mem_range.mp hk
    simpa [hkT] using hgamma k (Nat.le_of_lt hkT)
  have hgamma_top : gamma T = base ^ T := hgamma T le_rfl
  calc
    Finset.univ.sum (fun t : Fin T => theta (t.1 + 1)) =
        (Finset.range T).sum
          (fun k => if k + 1 = T then base ^ k else base ^ k - c * base ^ (k + 1)) :=
      htheta_range
    _ = c * base ^ T + (1 - c * base) *
          (Finset.range T).sum (fun k => base ^ k) :=
      parameterChoices_sum_range_terminal_geometric_sub_eq_tail_add_scaled_sum T base c hT
    _ = gamma T * c + (1 - c * base) *
          Finset.univ.sum (fun t : Fin T => gamma t.1) := by
      rw [hgamma_range, hgamma_top]
      ring



-- Generalization plan (G0):
-- concept/name: sharp lower bound for an intermediate smooth-epoch left coefficient; orig was lemma521_smoothEpochL_lower_bound_intermediate_epoch_length_sharp
-- generality used: scalar real schedules only; no carrier, measure, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: accelerated epoch tail anchors with frozen post-cutoff epoch length instantiate alpha/gamma/p branch formulas and reuse the same sharp left-coefficient lower bound
-- counterargument checked: not paper-local traceability because the theorem removes setup fields and theorem numbers; not a one-line wrapper because it packages the nontrivial field simplification and sharp coefficient inequality used by tail schedule proofs
-- coverage search: searched smoothEpoch/left coefficient/lower bound/intermediate schedule in SOptLib, Staging, registry, and Mathlib semantic search; the adjacent right-to-left bridge is related but has a different conclusion, and Mathlib hits were unrelated smoothing/asymptotics facts
-- minimal hypotheses: pointwise schedule equations, positive smoothness scale, strict intermediate cutoff, and positive frozen epoch length; global setup, tail cutoff, small-component, and finite-dimensional assumptions were dropped

/-- A sharp lower bound for the intermediate smooth-epoch left coefficient.

For the intermediate branch `alpha_s = 2 / (s - cutoff + 4)`, with `p_s = 1/2`,
the inverse smoothness rule for `gamma`, and frozen epoch length, the left
coefficient dominates the product
`(s-cutoff+4)(s-cutoff+8)T_cutoff/(24L)`.

Layer: Model | Gap: Level 1 (intermediate smooth-epoch left coefficient lower bound)
Proof: substitute the pointwise schedule equations, convert the natural
  predecessor cast for the positive epoch length, and reduce the result to
  ordered-field arithmetic.
Source: Mathlib ordered-field arithmetic over real schedules and natural-number
  casts
Used in: variance-reduced accelerated gradient descent tail anchor comparison
  for the intermediate smooth branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smooth_epoch_left_coeff_sharp_lower_bound_of_intermediate_schedule
    (L : Real) (T : Nat -> Nat) (alpha gamma p : Nat -> Real)
    (cutoff : Nat) {s : Nat}
    (hL_pos : 0 < L)
    (hs_left : cutoff < s)
    (hp_s : p s = (1 / 2 : Real))
    (halpha_s : alpha s = 2 / (((s - cutoff + 4 : Nat) : Real)))
    (hgamma_s : gamma s = 1 / (3 * L * alpha s))
    (hT_eq : T s = T cutoff)
    (hT_pos : 0 < T s) :
    (((s : Real) - cutoff + 4) *
        ((s : Real) - cutoff + 8) *
        ((T cutoff : Nat) : Real)) /
        (24 * L) <=
      gamma s / alpha s +
        (((T s - 1 : Nat) : Real)) *
          (gamma s * (alpha s + p s) / alpha s) := by
  let d : Real := ((s - cutoff + 4 : Nat) : Real)
  have hd_pos : 0 < d := by
    dsimp [d]
    have hden_nat : 0 < s - cutoff + 4 := by
      omega
    exact_mod_cast hden_nat
  have hd_ge_four : (4 : Real) <= d := by
    dsimp [d]
    have hden_nat : 4 <= s - cutoff + 4 := by
      omega
    exact_mod_cast hden_nat
  have hd_real :
      d = (s : Real) - cutoff + 4 := by
    dsimp [d]
    have hsub : cutoff <= s := le_of_lt hs_left
    norm_num [Nat.cast_sub hsub]
  have hT_cut_ge_one : (1 : Real) <= ((T cutoff : Nat) : Real) := by
    have hT_cut_pos : 0 < T cutoff := by
      simpa [hT_eq] using hT_pos
    exact_mod_cast Nat.succ_le_of_lt hT_cut_pos
  have hTsub_cast :
      ((T s - 1 : Nat) : Real) = ((T s : Nat) : Real) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hT_pos)]
    norm_num
  have hmain :
      d * (d + 4) * ((T cutoff : Nat) : Real) / (24 * L) <=
        gamma s / alpha s +
          (((T s - 1 : Nat) : Real)) *
            (gamma s * (alpha s + p s) / alpha s) := by
    rw [hgamma_s, halpha_s, hp_s, hTsub_cast, hT_eq]
    have hden_alpha : 2 / d ≠ 0 := by
      exact ne_of_gt (div_pos (by norm_num) hd_pos)
    field_simp [hden_alpha, ne_of_gt hL_pos, ne_of_gt hd_pos]
    nlinarith [hd_ge_four, hT_cut_ge_one, sq_nonneg d]
  convert hmain using 2
  · rw [hd_real]
    ring


-- Generalization plan (G0):
-- concept/name: base-two logarithmic ceiling selector bounded by a floor-log cutoff; orig was `smooth_first_log_selector_le_cutoff`
-- generality used: Glue-layer real scalar parameters only; no carrier type, measure, convexity, smoothness, oracle, or filtration assumptions
-- portable call pattern: finite-sum complexity proofs choose a logarithmic epoch before the component-count cutoff; `D0`, `epsilon`, and `m` vary while the conclusion shape is unchanged
-- counterargument checked: not paper-local traceability because the same scalar selector comparison is duplicated for later finite-sum accelerated proofs; not a pure wrapper because it composes log monotonicity with ceiling/floor rounding
-- coverage search: queried `ceil log floor selector`, `Nat.ceil_le_floor_add_one`, and LeanSearch for max-one ceil-log bounds; Mathlib has `Nat.ceil_le_floor_add_one` and SOptLib has casted ceiling helpers, but no full log-selector cutoff theorem
-- minimal hypotheses: positivity of `epsilon` and `D0` plus the pointwise ratio bound are exactly what the proof uses

/-- A base-two logarithmic ceiling selector is bounded by the floor-log cutoff
whenever its positive argument is bounded by the cutoff scale.

This packages the common finite-sum complexity step turning
`D0 / epsilon <= m` into a natural-number selector bound after applying a
base-two logarithm, natural ceiling, and the positive `max 1` totalization.

Layer: Glue | Gap: Level 0 (logarithmic selector cutoff rounding)
Proof: use monotonicity of `Real.log`, divide by the positive `log 2`, apply
  `Nat.ceil_mono`, and finish with `Nat.ceil_le_floor_add_one`.
Source: Mathlib real logarithm monotonicity and natural ceiling/floor APIs
Used in: variance-reduced accelerated finite-sum complexity proof selecting a
  pre-cutoff logarithmic epoch from an accuracy-to-component ratio
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem max_one_ceil_log_div_le_floor_log_of_div_le
    {m D0 epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon) (hD0_pos : 0 < D0)
    (hdiv_le : D0 / epsilon ≤ m) :
    max 1 (Nat.ceil (Real.log (D0 / epsilon) / Real.log 2)) ≤
      Nat.floor (Real.log m / Real.log 2) + 1 := by
  have hratio_pos : 0 < D0 / epsilon := div_pos hD0_pos hepsilon_pos
  have hlog_arg_le :
      Real.log (D0 / epsilon) / Real.log 2 ≤
        Real.log m / Real.log 2 := by
    have hlog_le :
        Real.log (D0 / epsilon) ≤ Real.log m :=
      Real.log_le_log hratio_pos hdiv_le
    exact div_le_div_of_nonneg_right hlog_le
      (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  have hceil_le :
      Nat.ceil (Real.log (D0 / epsilon) / Real.log 2) ≤
        Nat.floor (Real.log m / Real.log 2) + 1 :=
    (Nat.ceil_mono hlog_arg_le).trans
      (Nat.ceil_le_floor_add_one (Real.log m / Real.log 2))
  exact max_le (Nat.succ_le_succ (Nat.zero_le _)) hceil_le


-- Generalization plan (G0):
-- concept/name: square-root epoch stepsize absorption; orig was `tail_sqrt_schedule_mul_gamma_le_alpha_of_epoch_le_component_count`
-- generality used: scalar natural epoch length and positive real component-count, curvature, and smoothness scales only; no carrier type, measure, convexity, smoothness predicate, oracle, filtration, or finite-dimensional hypothesis is used
-- portable call pattern: finite-sum accelerated and variance-reduced tail proofs instantiate `T`, component count `m`, curvature `mu`, and smoothness scale `L` to show the constant tail stepsize makes `T * mu * gamma` no larger than the square-root acceleration parameter
-- counterargument checked: this is a short ordered-field/square-root wrapper, but it is not paper traceability because it captures a reusable parameter-choice side condition for square-root accelerated schedules; Mathlib has square-root algebra lemmas but not this compound schedule absorption statement
-- coverage search: searched CATALOG.md, SOptLib, Staging, the target algorithm file, and LeanSearch for `sqrt schedule`, `epoch gamma alpha component count`, `T * mu * gamma <= alpha`, and the displayed square-root formula; hits were generic sqrt/nat-order lemmas, existing Gamma schedule definitions, and paper-local uses, not this absorption inequality
-- minimal hypotheses: global setup fields were reduced to pointwise positivity of `m`, `mu`, and `L`, plus the single epoch-length bound `(T : Real) <= m`



/-- A square-root accelerated tail schedule absorbs one epoch length.

If the epoch length `T` is at most the component-count scale `m`, then with
`alpha = sqrt (m * mu / (3 * L))` and
`gamma = 1 / (3 * L * alpha)`, the product `T * mu * gamma` is bounded by
`alpha`.

Layer: Model | Gap: Level 0 (square-root accelerated schedule absorption)
Proof: multiply the epoch-length bound by the nonnegative scalar
  `mu / (3 * L * alpha)` and use `alpha^2 = m * mu / (3 * L)` to simplify the
  right-hand side.
Source: Mathlib real square-root and ordered-field arithmetic APIs for
  accelerated finite-sum parameter choices
Used in: variance-reduced accelerated-gradient strongly-convex tail proof that
  the frozen epoch length is compatible with the square-root alpha/gamma
  schedule
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sqrt_schedule_epoch_mul_gamma_le_alpha_of_le_component_count
    {T : Nat} {m mu L : Real}
    (hT_le_m : (T : Real) <= m) (hm : 0 < m) (hmu : 0 < mu) (hL : 0 < L) :
    (T : Real) *
        (mu * (1 / (3 * L * Real.sqrt (m * mu / (3 * L))))) <=
      Real.sqrt (m * mu / (3 * L)) := by
  let alpha : Real := Real.sqrt (m * mu / (3 * L))
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    exact Real.sqrt_pos.mpr (div_pos (mul_pos hm hmu) (by positivity))
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
  have halpha_sq : alpha ^ 2 = m * mu / (3 * L) := by
    dsimp [alpha]
    exact Real.sq_sqrt
      (div_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hmu)) (by positivity))
  have hcoef_nonneg :
      0 <= mu * (1 / (3 * L * alpha)) := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_right hT_le_m hcoef_nonneg
  have hright :
      m * (mu * (1 / (3 * L * alpha))) = alpha := by
    calc
      m * (mu * (1 / (3 * L * alpha))) =
          (m * mu / (3 * L)) / alpha := by
            field_simp [ne_of_gt hL, halpha_ne]
      _ = alpha := by
            rw [← halpha_sq]
            field_simp [halpha_ne]
  simpa [alpha] using hscaled.trans_eq hright

-- Generalization plan (G0):
-- concept/name: epoch-local geometric Gamma factor; orig was `theorem59GeometricGamma`
-- generality used: scalar schedules only; no carrier type, measure, convexity, smoothness, oracle, filtration, or finite-dimensional hypothesis is used
-- portable call pattern: strongly-convex accelerated tail proofs instantiate the curvature `mu`, epoch stepsize schedule `gamma`, epoch index, and inner time while reusing the same geometric reweighting factor for tail telescopes
-- counterargument checked: this is a formula-bodied definition, but it names the recurring fixed-epoch power schedule consumed by positivity, recurrence, Bernoulli lower-bound, and geometric theta-mass arguments; it is not paper-local after removing theorem numbers and setup fields
-- coverage search: searched SOptLib, Staging, CATALOG, and the target file for `geometric`, `epoch Gamma`, `Gamma_t = (1 + mu gamma_s)^t`, and `(1 + mu * gamma s)^t`; hits were the recursive `acceleratedGammaSchedule` and paper-local theorem59 wrappers, not this fixed-epoch geometric schedule
-- minimal hypotheses: all already minimal; the definition needs only the scalar curvature `mu`, stepsize schedule `gamma`, epoch `s`, and time `t`



/-- The fixed-epoch geometric Gamma factor generated by a curvature and stepsize schedule.

For a curvature scalar `mu`, epoch stepsize schedule `gamma`, epoch index `s`,
and inner time `t`, this is the geometric weight `(1 + mu * gamma s)^t` used
when a strongly-convex accelerated epoch is reweighted by a constant base.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; closed-form scalar geometric schedule from
  a fixed epoch base and natural-number power)
Source: Mathlib natural-number powers over real scalars and accelerated
  finite-sum tail reweighting parameter choices
Used in: variance-reduced accelerated-gradient strongly-convex tail telescope
  where each epoch uses a fixed geometric reweighting base
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def geometricEpochGamma (mu : Real) (gamma : Nat -> Real) (s t : Nat) : Real :=
  (1 + mu * gamma s) ^ t

/-- The fixed-epoch geometric Gamma factor unfolds to its scalar power formula.

Layer: Model | Gap: Level 0 (epoch-local geometric Gamma unfolding)
Proof: by rfl after unfolding `geometricEpochGamma`.
Source: Mathlib natural-number powers over real scalar schedules
Used in: variance-reduced accelerated-gradient strongly-convex tail telescope
  where the named Gamma factor must be converted to the printed power
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem geometricEpochGamma_def
    (mu : Real) (gamma : Nat -> Real) (s t : Nat) :
    geometricEpochGamma mu gamma s t = (1 + mu * gamma s) ^ t := rfl

/-- The fixed-epoch geometric Gamma factor is one at inner time zero.

Layer: Model | Gap: Level 0 (epoch-local geometric Gamma base case)
Proof: unfold the schedule and simplify the zeroth power.
Source: Mathlib natural-number powers over real scalar schedules
Used in: variance-reduced accelerated-gradient tail recurrences initialized at
  the start of an epoch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem geometricEpochGamma_zero
    (mu : Real) (gamma : Nat -> Real) (s : Nat) :
    geometricEpochGamma mu gamma s 0 = 1 := by
  simp [geometricEpochGamma]

/-- Successive fixed-epoch geometric Gamma factors differ by the epoch base.

Layer: Model | Gap: Level 0 (epoch-local geometric Gamma successor recurrence)
Proof: unfold the schedule and apply the natural-power successor identity.
Source: Mathlib natural-number powers over real scalar schedules
Used in: variance-reduced accelerated-gradient tail reweighting when moving
  from time `t` to `t + 1` inside a fixed epoch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp] theorem geometricEpochGamma_succ
    (mu : Real) (gamma : Nat -> Real) (s t : Nat) :
    geometricEpochGamma mu gamma s (t + 1) =
      geometricEpochGamma mu gamma s t * (1 + mu * gamma s) := by
  simp [geometricEpochGamma, pow_succ]

/-- A nonnegative fixed-epoch base gives nonnegative geometric Gamma factors.

Layer: Model | Gap: Level 0 (epoch-local geometric Gamma nonnegativity)
Proof: unfold the schedule and apply nonnegativity of natural powers.
Source: Mathlib ordered semiring powers over real scalar schedules
Used in: variance-reduced accelerated-gradient tail bounds that multiply
  inequalities by geometric epoch weights
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem geometricEpochGamma_nonneg
    (mu : Real) (gamma : Nat -> Real) (s t : Nat)
    (hbase : 0 <= 1 + mu * gamma s) :
    0 <= geometricEpochGamma mu gamma s t := by
  rw [geometricEpochGamma_def]
  exact pow_nonneg hbase t

/-- A positive fixed-epoch base gives positive geometric Gamma factors.

Layer: Model | Gap: Level 0 (epoch-local geometric Gamma positivity)
Proof: unfold the schedule and apply positivity of natural powers.
Source: Mathlib ordered semiring powers over real scalar schedules
Used in: variance-reduced accelerated-gradient geometric theta positivity in
  strongly-convex tail epochs
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem geometricEpochGamma_pos
    (mu : Real) (gamma : Nat -> Real) (s t : Nat)
    (hbase : 0 < 1 + mu * gamma s) :
    0 < geometricEpochGamma mu gamma s t := by
  rw [geometricEpochGamma_def]
  exact pow_pos hbase t

/-- Bernoulli lower bound for the fixed-epoch geometric Gamma factor.

If the epoch increment `mu * gamma s` is nonnegative, then the geometric
factor dominates its first-order linear approximation at every inner time.

Layer: Model | Gap: Level 0 (epoch-local geometric Gamma Bernoulli bound)
Proof: unfold the schedule and apply Mathlib's Bernoulli inequality for
  natural powers over ordered rings.
Source: Mathlib Bernoulli inequality for natural powers over real scalars
Used in: variance-reduced accelerated-gradient tail proof that the terminal
  geometric epoch weight is bounded below by a linear epoch-length expression
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/proof_plan/key_lemmas/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem one_add_nat_mul_le_geometricEpochGamma
    (mu : Real) (gamma : Nat -> Real) (s t : Nat)
    (hdelta : 0 <= mu * gamma s) :
    1 + (t : Real) * (mu * gamma s) <= geometricEpochGamma mu gamma s t := by
  rw [geometricEpochGamma_def]
  exact one_add_mul_le_pow (by nlinarith : -2 <= mu * gamma s) t


-- Generalization plan (G0):
-- concept/name: epoch-indexed geometric theta schedule; orig was
--   `theorem59GeometricTheta`, renamed away from theorem-number traceability
--   while keeping the standard accelerated-epoch `theta` terminology.
-- generality used: natural epoch lengths and real-valued schedules `Gamma`,
--   `alpha`, and `p`; no carrier, measure, independence, integrability,
--   topology, norm, inner product, convexity, smoothness, oracle, filtration,
--   or finite-dimensional hypothesis is used.
-- portable call pattern: strongly-convex variance-reduced accelerated tail
--   proofs vary the epoch length, geometric factor, acceleration schedule, and
--   snapshot-weight schedule while using the same terminal/nonterminal theta
--   weights for normalized epoch output and tail telescope algebra.
-- counterargument checked: this is a formula-bodied definition, but it names a
--   recurring geometric-branch theta schedule rather than paper source
--   traceability; the existing `geometricEpochGamma` names only the power
--   factor and `smoothEpochTheta` covers the different smooth-branch formula.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `geometricEpochTheta`, `geometric theta`, `EpochTheta`, `theta schedule`,
--   and terminal/nonterminal Gamma formulas; relevant partial hits were staged
--   `geometricEpochGamma` and `smoothEpochTheta`. LeanSearch for real scalar
--   geometric theta weights returned Gamma-function/modular-form results, not
--   an epoch schedule definition.
-- minimal hypotheses: all already minimal; this is a definitional scalar
--   parameter schedule and needs no positivity or epoch-domain assumptions.



/-- Epoch-indexed geometric theta weights from a supplied Gamma schedule.

For epoch `s`, the terminal time `T s` has weight `Gamma s (T s - 1)`;
every nonterminal time has weight
`Gamma s (t - 1) - (1 - alpha s - p s) * Gamma s t`.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; lift the geometric terminal/nonterminal
  theta formula to natural-indexed epoch parameter schedules)
Source: finite-sum accelerated-gradient epoch parameter choices and Mathlib
  ordered-ring primitives over real scalar schedules
Used in: variance-reduced accelerated-gradient strongly-convex tail output
  weighting before geometric telescope and theta-mass arguments
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def geometricEpochTheta (T : ℕ → ℕ) (Gamma : ℕ → ℕ → ℝ)
    (alpha p : ℕ → ℝ) (s t : ℕ) : ℝ :=
  if t = T s then
    Gamma s (t - 1)
  else
    Gamma s (t - 1) - (1 - alpha s - p s) * Gamma s t

/-- The epoch-indexed geometric theta schedule unfolds to its
terminal/nonterminal formula.

Layer: Model | Gap: Level 0 (epoch-indexed geometric theta unfolding)
Proof: by rfl after unfolding `geometricEpochTheta`.
Source: finite-sum accelerated-gradient epoch parameter choices and Mathlib
  ordered-ring primitives over real scalar schedules
Used in: variance-reduced accelerated-gradient strongly-convex tail output
  weighting before geometric telescope and theta-mass arguments
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem geometricEpochTheta_def (T : ℕ → ℕ) (Gamma : ℕ → ℕ → ℝ)
    (alpha p : ℕ → ℝ) (s t : ℕ) :
    geometricEpochTheta T Gamma alpha p s t =
      if t = T s then
        Gamma s (t - 1)
      else
        Gamma s (t - 1) - (1 - alpha s - p s) * Gamma s t := by
  rfl

/-- Geometric theta weights are positive for a positive fixed-epoch base under
the usual coefficient budget.

This specializes `geometricEpochTheta` to the power schedule
`Gamma s t = base s ^ t`. Terminal weights are positive powers of the base;
nonterminal weights factor as
`base s ^ (t - 1) * (1 - (1 - alpha s - p s) * base s)`.

Layer: Model | Gap: Level 0 (geometric theta positivity)
Proof: split on the terminal time; the nonterminal branch is the elementary
  factorization above plus positivity of both factors.
Source: Mathlib ordered-ring arithmetic for real powers and accelerated
  finite-sum geometric output weights
Used in: variance-reduced accelerated-gradient strongly-convex tail output
  weighting before geometric telescope and theta-mass arguments
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem geometricEpochTheta_pos_of_base_pos_of_coeff_base_lt_one
    (T : ℕ → ℕ) (base alpha p : ℕ → ℝ) {s t : ℕ}
    (htpos : 1 ≤ t)
    (hbase_pos : 0 < base s)
    (hcoeff : (1 - alpha s - p s) * base s < 1) :
    0 < geometricEpochTheta T (fun s t => base s ^ t) alpha p s t := by
  unfold geometricEpochTheta
  by_cases ht : t = T s
  · rw [if_pos ht]
    exact pow_pos hbase_pos (t - 1)
  · rw [if_neg ht]
    dsimp
    have ht_eq : t = (t - 1) + 1 := by
      omega
    have hpow :
        base s ^ t = base s ^ (t - 1) * base s := by
      rw [ht_eq]
      exact pow_succ (base s) (t - 1)
    rw [hpow]
    have hpow_pos : 0 < base s ^ (t - 1) :=
      pow_pos hbase_pos (t - 1)
    have hfactor_pos : 0 < 1 - (1 - alpha s - p s) * base s := by
      exact sub_pos.mpr hcoeff
    nlinarith [mul_pos hpow_pos hfactor_pos]


-- Generalization plan (G0):
-- concept/name: terminal_adjusted_geometric_weight_pos_of_coeff_mul_base_lt_one
--   exposes positivity of a terminal-adjusted geometric output weight; orig was
--   `geometric_theta_positive_of_coeff_base_lt_one`, renamed away from theorem
--   number and `theta` schedule traceability.
-- generality used: ordered-commutative-ring scalar `base` and `coeff` plus
--   natural terminal time `T` and one-based time `t`; no carrier, measure,
--   independence,
--   integrability, topology, norm, inner product, convexity, smoothness,
--   oracle, filtration, or finite-dimensional hypothesis is used.
-- portable call pattern: accelerated or variance-reduced epoch proofs choose
--   different bases and coefficients while reusing the same terminal branch
--   `base^(t-1)` and nonterminal correction `base^(t-1) - coeff * base^t`
--   to prove pointwise positivity of normalized output weights.
-- counterargument checked: this is short scalar algebra, but not a pure rename
--   or caller-side traceability wrapper; it packages the recurring positivity
--   step needed after a coefficient budget `coeff * base < 1`.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `terminalAdjustedGeometricWeight`, `geometric theta positive`,
--   `coeff base`, and `base^(t-1) - coeff * base^t`; the closest hit was
--   staged `SOptLib.geometricEpochTheta_pos_of_base_pos_of_coeff_base_lt_one`,
--   which is schedule-specific and factors `coeff` as `1 - alpha s - p s`.
--   LeanSearch for the precise positivity shape returned unrelated ordinal,
--   polynomial, and geometric-sum lemmas, so no Mathlib/SOptLib theorem covers
--   this scalar statement directly.
-- minimal hypotheses: all already minimal except paper schedules are replaced
--   by pointwise scalar `base`, `coeff`, `T`, and `t` hypotheses.


/-- A terminal-adjusted geometric weight is positive when the base is positive
and the nonterminal coefficient budget is below one.

The terminal branch is a positive power of `base`. In the nonterminal branch,
the one-based condition on `t` rewrites `base^t` as `base^(t-1) * base`, leaving
the product of `base^(t-1)` and `1 - coeff * base`.

Layer: Glue | Gap: Level 0 (terminal-adjusted geometric weight positivity)
Proof: split on the terminal branch; the nonterminal branch factors the
  geometric powers and uses positivity of both factors.
Source: Mathlib ordered-ring arithmetic for real powers and finite geometric
  output weights
Used in: variance-reduced accelerated-gradient strongly-convex tail output
  weight admissibility
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem terminal_adjusted_geometric_weight_pos_of_coeff_mul_base_lt_one
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (base coeff : R) (T t : ℕ)
    (htpos : 1 ≤ t)
    (hbase_pos : 0 < base)
    (hcoeff : coeff * base < 1) :
    0 < (if t = T then
        base ^ (t - 1)
      else
        base ^ (t - 1) - coeff * base ^ t) := by
  by_cases ht : t = T
  · rw [if_pos ht]
    exact pow_pos hbase_pos (t - 1)
  · rw [if_neg ht]
    have ht_eq : t = (t - 1) + 1 := by
      omega
    have hpow :
        base ^ t = base ^ (t - 1) * base := by
      rw [ht_eq]
      exact pow_succ base (t - 1)
    rw [hpow]
    have hpow_pos : 0 < base ^ (t - 1) :=
      pow_pos hbase_pos (t - 1)
    have hfactor_pos : 0 < 1 - coeff * base := by
      exact sub_pos.mpr hcoeff
    have hfactor :
        base ^ (t - 1) - coeff * (base ^ (t - 1) * base) =
          base ^ (t - 1) * (1 - coeff * base) := by
      ring
    rw [hfactor]
    exact mul_pos hpow_pos hfactor_pos

-- Generalization plan (G0):
-- concept/name: terminal-adjusted geometric epoch weights admissible for
--   normalized finite-window output; orig was
--   `theorem59GeometricTheta_epochOutputWeightsAdmissible_of_coeff_aux`,
--   renamed away from theorem numbering, local theta names, and setup fields.
-- generality used: real scalar `base` and `coeff` plus a positive natural
--   epoch length `T`; no carrier, measure, independence, integrability,
--   topology, norm, inner product, convexity, smoothness, oracle, filtration,
--   or finite-dimensional hypotheses are used.
-- portable call pattern: strongly-convex accelerated and variance-reduced
--   epoch methods instantiate a positive epoch length, a positive geometric
--   base, and a coefficient budget `coeff * base < 1` to certify normalized
--   selected-output weights before Jensen, finite-window PMF construction, or
--   averaged-output feasibility.
-- counterargument checked: the generic admissible-weight contract is already
--   `FiniteWindowWeightsAdmissible`, so this theorem does not redefine it; the
--   reusable content is the formula-specific bridge from terminal-adjusted
--   geometric weights and a scalar coefficient budget to that existing
--   finite-window contract. It is not a pure wrapper because future callers
--   avoid reproving pointwise positivity plus positive total mass.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `FiniteWindowWeightsAdmissible`, `terminal adjusted geometric weights`,
--   `geometricEpochTheta`, and coefficient-budget admissibility; the full
--   coverage hit was only the abstract finite-window predicate and
--   constructor, while the partial hits were staged pointwise positivity
--   `terminal_adjusted_geometric_weight_pos_of_coeff_mul_base_lt_one` and
--   the `geometricEpochTheta` schedule definition. LeanSearch for finite-sum
--   positivity returned `Finset.sum_pos` and `Finset.sum_pos'`, not this
--   terminal-adjusted geometric schedule theorem.
-- minimal hypotheses: all already minimal for this admissibility result:
--   `0 < T` supplies a supported atom, `0 < base` and `coeff * base < 1`
--   supply pointwise strict positivity; no upper bounds or algorithm schedule
--   assumptions are used.

/-- Terminal-adjusted geometric epoch weights are admissible on a nonempty
one-based finite epoch window.

The terminal atom has weight `base^(T - 1)`. Every nonterminal atom has the
corrected geometric weight `base^(t - 1) - coeff * base^t`; the coefficient
budget `coeff * base < 1` makes those corrected weights strictly positive.

Layer: Model | Gap: Level 0 (terminal-adjusted geometric finite-window weights)
Proof: prove strict positivity of every atom using the scalar terminal-adjusted
  geometric positivity lemma, then use
  `FiniteWindowWeightsAdmissible.of_nonneg_of_pos` with the first epoch index
  as the positive supported atom.
Source: Mathlib ordered-ring powers and finite-set real-sum positivity APIs
Used in: variance-reduced accelerated-gradient strongly-convex tail epoch
  output weighting before normalized finite-window averaging
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem terminal_adjusted_geometric_weights_admissible
    {T : ℕ} {base coeff : ℝ}
    (hT : 0 < T) (hbase_pos : 0 < base)
    (hcoeff : coeff * base < 1) :
    FiniteWindowWeightsAdmissible (Finset.univ : Finset (Fin T))
      (fun t : Fin T =>
        if t.1 + 1 = T then
          base ^ ((t.1 + 1) - 1)
        else
          base ^ ((t.1 + 1) - 1) - coeff * base ^ (t.1 + 1)) := by
  let weight : Fin T → ℝ := fun t =>
    if t.1 + 1 = T then
      base ^ ((t.1 + 1) - 1)
    else
      base ^ ((t.1 + 1) - 1) - coeff * base ^ (t.1 + 1)
  have hweight_pos : ∀ t : Fin T, 0 < weight t := by
    intro t
    have htpos : 1 ≤ t.1 + 1 := by omega
    exact
      terminal_adjusted_geometric_weight_pos_of_coeff_mul_base_lt_one
        base coeff T (t.1 + 1) htpos hbase_pos hcoeff
  have hnonneg :
      ∀ t : Fin T, t ∈ (Finset.univ : Finset (Fin T)) → 0 ≤ weight t := by
    intro t _ht
    exact le_of_lt (hweight_pos t)
  exact
    FiniteWindowWeightsAdmissible.of_nonneg_of_pos
      (times := (Finset.univ : Finset (Fin T)))
      (weight := weight)
      hnonneg
      (k := ⟨0, hT⟩)
      (by simp)
      (hweight_pos ⟨0, hT⟩)

/-- The inverse-power scalar weight generated by a base and natural time.

For a scalar base `alpha` and time `t`, this is the output weight
`1 / alpha^t` used in finite-window geometric reweighting and telescoping
arguments.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; closed-form reciprocal natural-power
  scalar schedule)
Source: Mathlib natural-number powers and real division APIs for finite-window
  output reweighting
Used in: random primal-dual gradient finite-window output weighting before the
  geometric telescope and normalizer positivity arguments
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def inverse_power_weight {𝕜 : Type*} [Field 𝕜] (alpha : 𝕜) (t : ℕ) : 𝕜 :=
  1 / (alpha ^ t)

/-- The inverse-power scalar weight unfolds to the reciprocal power formula.

Layer: Model | Gap: Level 0 (inverse-power weight unfolding)
Proof: by rfl after unfolding `inverse_power_weight`.
Source: Mathlib natural-number powers and real division APIs
Used in: random primal-dual gradient output-weight formula normalization
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp] theorem inverse_power_weight_def {𝕜 : Type*} [Field 𝕜] (alpha : 𝕜) (t : ℕ) :
    inverse_power_weight alpha t = 1 / (alpha ^ t) := by
  rfl

/-- Inverse-power weights are positive for a positive base.

Layer: Model | Gap: Level 0 (inverse-power weight positivity)
Proof: unfold the schedule and combine positivity of natural powers with
  positivity of reciprocal division.
Source: Mathlib ordered-field division and natural-power positivity APIs
Used in: finite-window output distribution weights for random primal-dual
  gradient convergence
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inverse_power_weight_pos
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (alpha : 𝕜) (halpha : 0 < alpha) (t : ℕ) :
    0 < inverse_power_weight alpha t := by
  simpa [inverse_power_weight] using one_div_pos.mpr (pow_pos halpha t)

/-- Inverse-power weights are nonnegative for a positive base.

Layer: Model | Gap: Level 0 (inverse-power weight nonnegativity)
Proof: derive nonnegativity from the strict positivity theorem.
Source: Mathlib ordered-field division and natural-power positivity APIs
Used in: finite-window output weighted averages whose weights must be
  nonnegative
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inverse_power_weight_nonneg
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (alpha : 𝕜) (halpha : 0 < alpha) (t : ℕ) :
    0 ≤ inverse_power_weight alpha t :=
  (inverse_power_weight_pos alpha halpha t).le

/-- A nonempty one-based finite window has positive inverse-power weight mass.

Layer: Model | Gap: Level 0 (inverse-power finite-window mass positivity)
Proof: use strict positivity of every inverse-power weight and the fact that
  `1` belongs to `Icc 1 k` when `1 ≤ k`.
Source: Mathlib finite sums over ordered additive monoids and real
  inverse-power positivity
Used in: random primal-dual gradient output normalizer positivity for the
  weighted average over times `1, ..., k`
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inverse_power_weight_sum_pos_Icc
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (alpha : 𝕜) (halpha : 0 < alpha) {k : ℕ} (hk : 1 ≤ k) :
    0 < ∑ t ∈ Finset.Icc 1 k, inverse_power_weight alpha t := by
  classical
  have hnonneg :
      ∀ t ∈ Finset.Icc 1 k, 0 ≤ inverse_power_weight alpha t := by
    intro t _ht
    exact inverse_power_weight_nonneg alpha halpha t
  have hmem : 1 ∈ Finset.Icc 1 k := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  exact Finset.sum_pos' hnonneg
    ⟨1, hmem, inverse_power_weight_pos alpha halpha 1⟩

/-- Multiplying the next inverse-power weight by the base gives the previous one.

Layer: Model | Gap: Level 0 (inverse-power successor shift)
Proof: unfold the reciprocal-power schedule, rewrite the successor power, and
  clear the nonzero base and power denominators by field simplification.
Source: Mathlib real field simplification and natural-power successor APIs
Used in: weighted telescope steps where `alpha * theta_{t+1}` must rewrite to
  `theta_t`
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem mul_inverse_power_weight_succ
    {𝕜 : Type*} [Field 𝕜]
    (alpha : 𝕜) (halpha : alpha ≠ 0) (t : ℕ) :
    alpha * inverse_power_weight alpha (t + 1) = inverse_power_weight alpha t := by
  unfold inverse_power_weight
  rw [pow_succ]
  field_simp [halpha, pow_ne_zero t halpha]

/-- Multiplying a positive-time inverse-power weight by the base shifts to the
preceding time.

Layer: Model | Gap: Level 0 (inverse-power predecessor shift)
Proof: rewrite the positive time as `(t - 1) + 1` and apply the successor
  shift identity.
Source: Mathlib natural-number predecessor arithmetic and real inverse-power
  shift algebra
Used in: random primal-dual gradient weighted telescope step
  `alpha_t * theta_t = theta_{t-1}` under a constant `alpha_t`
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem mul_inverse_power_weight_eq_pred_of_one_le
    {𝕜 : Type*} [Field 𝕜]
    (alpha : 𝕜) (halpha : alpha ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    alpha * inverse_power_weight alpha t = inverse_power_weight alpha (t - 1) := by
  have ht_eq : t = (t - 1) + 1 := by omega
  conv_lhs =>
    rw [ht_eq]
  exact mul_inverse_power_weight_succ alpha halpha (t - 1)

end SOptLib

-- Generalization plan (G0):
-- concept/name: inverse geometric-mixing step size selector; orig was Theorem2ChosenStepsize.
-- generality used: natural network size plus real denominator coefficient, Lipschitz scale, and geometric-mixing prefactor; no measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are needed.
-- portable call pattern: decentralized consensus, push-pull, and pull-with-memory convergence proofs choose a constant stepsize by inverting a scalar multiple of network size, squared mixing constant, and Lipschitz scale while changing the coefficient and constants.
-- counterargument checked: the original declaration is a paper-facing Prop wrapper, but the reusable core is the named closed-form scalar selector; Mathlib has real division and powers but no domain-specific geometric-mixing stepsize choice, and SOptLib has other parameter-choice selectors but none with this denominator shape.
-- coverage search: lean_search_symbols "inverse geometric mixing stepsize equals one over coefficient network size mixing constant squared Lipschitz" found finite-network geometric-mixing contracts and unrelated parameter-choice schedules; "closed form stepsize one over n C squared L" found local PullWithMemoryDGD coefficient lemmas and half-Lipschitz schedules, not this selector.
-- minimal hypotheses: all algorithm setup fields were removed; only the parameters that occur in the scalar formula remain, with positivity hypotheses appearing only on the positivity theorem.

/-- Constant inverse stepsize selected from a finite-network geometric mixing
denominator.

The value is `1 / (denomCoeff * n * C^2 * L)`, where `n` is the network size,
`C` is a geometric-mixing prefactor, and `L` is the Lipschitz scale.

Layer: Model | Concept: inverse geometric-mixing stepsize selector
Proof: (definitional construction; reciprocal of a scalar multiple of network size, squared mixing prefactor, and Lipschitz scale)
Source: Mathlib real field operations and decentralized-optimization geometric-mixing stepsize notation
Used in: choosing the constant stepsize for geometric-mixing decentralized convergence theorems before substituting it into stationarity and coefficient bounds
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
noncomputable def inverse_geometric_mixing_step_size (n : Nat) (denomCoeff L C : Real) : Real :=
  1 / (denomCoeff * (n : Real) * C ^ (2 : Nat) * L)

/-- The inverse geometric-mixing stepsize unfolds to its reciprocal scalar
formula.

Layer: Model | Gap: Level 0 (inverse geometric-mixing stepsize unfolding)
Proof: by rfl after unfolding `inverse_geometric_mixing_step_size`.
Source: Mathlib real field operations and decentralized-optimization geometric-mixing stepsize notation
Used in: rewriting a chosen constant stepsize to the scalar denominator used by geometric-mixing stationarity estimates
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem inverse_geometric_mixing_step_size_def
    (n : Nat) (denomCoeff L C : Real) :
    inverse_geometric_mixing_step_size n denomCoeff L C =
      1 / (denomCoeff * (n : Real) * C ^ (2 : Nat) * L) := by
  rfl

/-- The inverse geometric-mixing stepsize is positive when every denominator
factor is positive.

Layer: Model | Gap: Level 0 (inverse geometric-mixing stepsize positivity)
Proof: combine positivity of the scalar coefficient, natural network size cast, squared mixing prefactor, and Lipschitz scale, then apply positivity of a reciprocal.
Source: Mathlib ordered real field arithmetic, natural-number casts, and power positivity APIs
Used in: discharging positive constant-stepsize side conditions after selecting a geometric-mixing stepsize
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem inverse_geometric_mixing_step_size_pos
    (n : Nat) (denomCoeff L C : Real)
    (hcoeff : 0 < denomCoeff) (hn : 0 < n) (hL : 0 < L)
    (hC_sq : 0 < C ^ (2 : Nat)) :
    0 < inverse_geometric_mixing_step_size n denomCoeff L C := by
  unfold inverse_geometric_mixing_step_size
  apply one_div_pos.mpr
  exact mul_pos (mul_pos (mul_pos hcoeff (by exact_mod_cast hn)) hC_sq) hL

-- Generalization plan (G0):
-- concept/name: geometric-logarithmic inner-round natural ceiling selector; orig was theorem2ChosenCorrectedInnerRounds.
-- generality used: real constants C and beta plus a zero-based natural index; no measure, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are needed.
-- portable call pattern: decentralized consensus and push-pull algorithms with zero-based communication horizons call the same selector while changing the mixing constants and outer index.
-- counterargument checked: not merely paper-local because corrected zero-based logarithmic communication schedules recur when a positive-index formula is used over a natural horizon; not a duplicate of Mathlib because Mathlib gives only the generic Nat.le_ceil fact, not this named selector.
-- coverage search: lean_search_symbols "natural ceiling of corrected geometric logarithmic inner round lower bound dominates lower bound all natural indices" found only the local PullWithMemoryDGD declarations; "Nat.ceil logarithmic schedule lower bound max log C log k beta" found unrelated SOptLib log-ceiling cutoff bounds; lean_leansearch "natural ceiling of a real number is at least the real number" identified Mathlib Nat.le_ceil as the proof ingredient, not a duplicate selector.
-- minimal hypotheses: all algorithm setup fields were removed; the formula depends only on C, beta, and k.

/-- Corrected zero-based geometric-logarithmic inner-round selector.

For positive `k` this is the natural ceiling of
`max (log C / (1 - beta)) (log k / (1 - beta))`; at `k = 0` it keeps the
well-formed `log C` branch.

Layer: Model | Concept: geometric-logarithmic inner-round ceiling selector
Proof: (definitional construction; natural ceiling of the corrected all-index real logarithmic communication lower bound)
Source: Mathlib real logarithm, lattice maximum, and natural ceiling APIs for geometric communication schedules
Used in: selecting natural communication rounds from a zero-based geometric mixing schedule before proving the corrected schedule lower bound
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
noncomputable def geometricLogInnerRoundCeil (C beta : Real) (k : Nat) : Nat :=
  Nat.ceil
    (if _hk : 0 < k then
      max (Real.log C / (1 - beta)) (Real.log (k : Real) / (1 - beta))
    else
      Real.log C / (1 - beta))

/-- The corrected geometric-logarithmic inner-round selector unfolds to the
natural ceiling of its corrected all-index real lower bound.

Layer: Model | Gap: Level 0 (geometric-logarithmic ceiling selector unfolding)
Proof: by rfl after unfolding `geometricLogInnerRoundCeil`.
Source: Mathlib real logarithm, lattice maximum, and natural ceiling APIs for geometric communication schedules
Used in: rewriting a chosen natural communication count to the scalar ceiling schedule used by zero and positive index branches
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem geometricLogInnerRoundCeil_def (C beta : Real) (k : Nat) :
    geometricLogInnerRoundCeil C beta k =
      Nat.ceil
        (if _hk : 0 < k then
          max (Real.log C / (1 - beta)) (Real.log (k : Real) / (1 - beta))
        else
          Real.log C / (1 - beta)) := by
  rfl

/-- The corrected geometric-logarithmic inner-round selector dominates its
real lower bound after coercion to `Real`.

Layer: Model | Gap: Level 0 (geometric-logarithmic ceiling lower bound)
Proof: unfold the selector and apply Mathlib's generic `Nat.le_ceil`.
Source: Mathlib natural ceiling API over ordered floor semirings, specialized to real logarithmic schedules
Used in: proving that chosen natural communication rounds satisfy the corrected all-index geometric mixing lower-bound requirement
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem geometricLogInnerRoundCeil_lower_bound (C beta : Real) (k : Nat) :
    (if _hk : 0 < k then
      max (Real.log C / (1 - beta)) (Real.log (k : Real) / (1 - beta))
    else
      Real.log C / (1 - beta)) <= (geometricLogInnerRoundCeil C beta k : Real) := by
  unfold geometricLogInnerRoundCeil
  exact Nat.le_ceil _

-- Generalization plan (G0):
-- concept/name: positive-index geometric-logarithmic inner-round lower-bound selector.
-- generality used: real prefactor C and contraction beta, a natural outer index k with 0 < k; no measure, filtration, independence, integrability, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are used.
-- portable call pattern: decentralized consensus, push-pull, and inner-loop contraction proofs call the same real lower-bound selector when choosing communication rounds so that both a C-weighted geometric residual and a k-dependent residual are small; C, beta, and k vary while the max-of-two-log-branches conclusion stays unchanged.
-- counterargument checked: this is not merely paper traceability because positive-index geometric communication schedules recur independently of PULM-DGD; it is not a pure wrapper over Mathlib because Mathlib supplies logarithm and max primitives but no named stochastic-optimization schedule object, and it differs from the staged ceiling selector by exposing the real lower bound before natural-number rounding.
-- coverage search: lean_search_symbols queries "positive index logarithmic lower bound max log C over one minus beta log k over one minus beta", "geometric logarithmic inner round lower bound max two log branches", and "positive geometric logarithmic inner round lower bound real max log C log k" found only the zero-based Nat-ceiling selector geometricLogInnerRoundCeil; LeanSearch for the real logarithmic lower-bound maximum returned generic Real.log/logb lemmas, not this schedule object.
-- minimal hypotheses: all algorithm setup fields were removed; the positive-index domain is structural to rule out the zero-index logarithm convention.

/-- Positive-index geometric-logarithmic inner-round lower-bound selector.

For positive `k`, this is the real lower bound
`max (log C / (1 - beta)) (log k / (1 - beta))` used before taking a natural
ceiling for communication or contraction rounds.

Layer: Model | Concept: positive geometric-logarithmic inner-round lower-bound selector
Proof: (definitional construction; maximum of the prefactor and positive-index logarithmic residual branches divided by the contraction gap)
Source: Mathlib real logarithm, division in ordered fields, and lattice maximum APIs for geometric communication schedules
Used in: selecting enough inner communication rounds from a positive-index geometric mixing schedule before natural-number ceiling totalization -/
noncomputable def positive_geometric_log_inner_round_lower_bound
    (C beta : Real) (k : {n : Nat // 0 < n}) : Real :=
  max (Real.log C / (1 - beta))
    (Real.log (k.1 : Real) / (1 - beta))

/-- The positive-index geometric-logarithmic inner-round lower-bound selector
unfolds to the maximum of its two logarithmic branches.

Layer: Model | Gap: Level 0 (positive geometric-logarithmic lower-bound unfolding)
Proof: by rfl after unfolding `positive_geometric_log_inner_round_lower_bound`.
Source: Mathlib real logarithm, division in ordered fields, and lattice maximum APIs for geometric communication schedules
Used in: rewriting a positive-index communication lower-bound selector to the source-level scalar display -/
@[simp] theorem positive_geometric_log_inner_round_lower_bound_def
    (C beta : Real) (k : {n : Nat // 0 < n}) :
    positive_geometric_log_inner_round_lower_bound C beta k =
      max (Real.log C / (1 - beta))
        (Real.log (k.1 : Real) / (1 - beta)) := by
  rfl

/-- The constant logarithmic branch is bounded by the positive-index selector.

Layer: Model | Gap: Level 0 (positive geometric-logarithmic left branch lower bound)
Proof: unfold the selector and use the left branch of `max`.
Source: Mathlib lattice maximum APIs over real logarithmic schedules
Used in: proving that a selected positive communication count controls the constant geometric residual branch -/
theorem log_const_div_one_sub_le_positive_geometric_log_inner_round_lower_bound
    (C beta : Real) (k : {n : Nat // 0 < n}) :
    Real.log C / (1 - beta) <=
      positive_geometric_log_inner_round_lower_bound C beta k := by
  rw [positive_geometric_log_inner_round_lower_bound_def]
  exact le_max_left _ _

/-- The positive-index logarithmic branch is bounded by the positive-index selector.

Layer: Model | Gap: Level 0 (positive geometric-logarithmic right branch lower bound)
Proof: unfold the selector and use the right branch of `max`.
Source: Mathlib lattice maximum APIs over real logarithmic schedules
Used in: proving that a selected positive communication count controls the index-dependent geometric residual branch -/
theorem log_index_div_one_sub_le_positive_geometric_log_inner_round_lower_bound
    (C beta : Real) (k : {n : Nat // 0 < n}) :
    Real.log (k.1 : Real) / (1 - beta) <=
      positive_geometric_log_inner_round_lower_bound C beta k := by
  rw [positive_geometric_log_inner_round_lower_bound_def]
  exact le_max_right _ _

/-- The positive-index real lower-bound selector is dominated by the existing
natural ceiling selector after coercion to `Real`.

Layer: Model | Gap: Level 0 (positive geometric-logarithmic ceiling lower bound)
Proof: specialize `geometricLogInnerRoundCeil_lower_bound` to the positive branch.
Source: Mathlib `Nat.le_ceil` through the geometric-logarithmic ceiling selector API
Used in: choosing natural communication rounds from the positive-index real lower-bound selector -/
theorem positive_geometric_log_inner_round_lower_bound_le_geometric_log_inner_round_ceil
    (C beta : Real) (k : {n : Nat // 0 < n}) :
    positive_geometric_log_inner_round_lower_bound C beta k <=
      (geometricLogInnerRoundCeil C beta k.1 : Real) := by
  simpa [positive_geometric_log_inner_round_lower_bound_def, k.2]
    using geometricLogInnerRoundCeil_lower_bound C beta k.1

-- Generalization plan (G0):
-- concept/name: zero-index geometric-logarithmic inner-round lower-bound selector; orig was theorem2ZeroRoundLowerBound.
-- generality used: real prefactor C and contraction beta; no measure, filtration, independence, integrability, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are used.
-- portable call pattern: decentralized consensus, push-pull, and inner-loop contraction proofs call the same zero-index branch when totalizing a positive-index logarithmic communication schedule over a natural horizon; C and beta vary while the well-formed log C branch stays unchanged.
-- counterargument checked: this is a one-line real formula, but it is not only paper traceability because it is the reusable zero-index branch paired with the already staged positive branch and ceiling selector; Mathlib has the logarithm and division primitives but no named geometric communication schedule branch.
-- coverage search: lean_search_symbols queries "zero index geometric logarithmic inner round lower bound log C over one minus beta" and "zero geometric logarithmic lower bound real log C divided by one minus beta definition" found the local paper declaration plus existing positive-branch and ceiling-selector APIs, but no zero-branch selector; lean_leansearch "real logarithm divided by one minus beta geometric schedule zero index branch" returned generic Real.log/logb facts, not this schedule object.
-- minimal hypotheses: all algorithm setup fields were removed; the formula depends only on C and beta.

/-- Zero-index geometric-logarithmic inner-round lower-bound selector.

This is the well-formed `k = 0` branch `log C / (1 - beta)` used when a
positive-index logarithmic communication schedule is totalized over a
zero-based natural horizon.

Layer: Model | Concept: zero-index geometric-logarithmic inner-round lower-bound selector
Proof: (definitional construction; constant logarithmic branch divided by the contraction gap)
Source: Mathlib real logarithm and division APIs for geometric communication schedules
Used in: selecting enough inner communication rounds at the zero index of a corrected zero-based geometric mixing schedule
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
noncomputable def zeroGeometricLogInnerRoundLowerBound (C beta : Real) : Real :=
  Real.log C / (1 - beta)

/-- The zero-index geometric-logarithmic inner-round lower-bound selector
unfolds to the constant logarithmic branch.

Layer: Model | Gap: Level 0 (zero-index geometric-logarithmic lower-bound unfolding)
Proof: by rfl after unfolding `zeroGeometricLogInnerRoundLowerBound`.
Source: Mathlib real logarithm and division APIs for geometric communication schedules
Used in: rewriting the zero-index communication lower-bound selector to the source-level scalar display
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem zeroGeometricLogInnerRoundLowerBound_def (C beta : Real) :
    zeroGeometricLogInnerRoundLowerBound C beta =
      Real.log C / (1 - beta) := by
  rfl

/-- The zero-index real lower-bound selector is dominated by the zero-based
natural ceiling selector after coercion to `Real`.

Layer: Model | Gap: Level 0 (zero-index geometric-logarithmic ceiling lower bound)
Proof: specialize `geometricLogInnerRoundCeil_lower_bound` at index zero and unfold the zero branch.
Source: Mathlib natural ceiling API through the geometric-logarithmic ceiling selector
Used in: choosing natural communication rounds from the zero-index real lower-bound selector
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem zeroGeometricLogInnerRoundLowerBound_le_geometricLogInnerRoundCeil
    (C beta : Real) :
    zeroGeometricLogInnerRoundLowerBound C beta <=
      (geometricLogInnerRoundCeil C beta 0 : Real) := by
  simpa [zeroGeometricLogInnerRoundLowerBound]
    using geometricLogInnerRoundCeil_lower_bound C beta 0

-- Generalization plan (G0):
-- concept/name: zero-based geometric-logarithmic inner-round real lower-bound selector; orig was theorem2CorrectedScheduleLowerBound.
-- generality used: real prefactor C and contraction beta plus a zero-based natural outer index k; no measure, filtration, independence, integrability, convexity, smoothness, oracle, topology, normed-space, or finite-dimensional hypotheses are used.
-- portable call pattern: decentralized consensus, push-pull, and pull-with-memory algorithms can call this all-index real lower-bound selector when a positive-index logarithmic communication schedule must be totalized over a natural outer-loop horizon; C, beta, and k vary while the positive and zero branch contract remains unchanged.
-- counterargument checked: this is a one-line branch wrapper, but it is not paper-local traceability because it composes the reusable positive and zero geometric-logarithmic branch selectors into the real lower bound consumed before ceiling or schedule domination; Mathlib has only logarithm, max, and if primitives, and the existing staged ceiling selector changes the codomain to Nat.
-- coverage search: lean_search_symbols queries "zero based geometric logarithmic inner round real lower bound positive branch zero branch" and "all index logarithmic lower bound selector log C log k one minus beta zero index" found the staged positive branch, zero branch, and Nat ceiling selector but no all-index Real-valued selector; lean_leansearch "zero based logarithmic maximum lower bound positive natural index log C divided by one minus beta" returned generic Nat logarithm declarations, not this real communication schedule object.
-- minimal hypotheses: all algorithm setup fields were removed; the only structural hypothesis is the branch-local proof 0 < k carried internally by the dependent positive-index selector.

/-- Zero-based geometric-logarithmic inner-round real lower-bound selector.

For positive `k`, this uses the maximum of the constant and index-dependent
logarithmic branches; at `k = 0`, it keeps only the well-formed constant
branch before any natural-number ceiling is taken.

Layer: Model | Concept: zero-based geometric-logarithmic inner-round real lower-bound selector
Proof: (definitional construction; totalized branch between the positive-index logarithmic lower-bound selector and the zero-index constant lower-bound selector)
Source: Mathlib real logarithm, division, subtype, and conditional APIs for geometric communication schedules
Used in: expressing the real lower-bound requirement for inner communication rounds over a zero-based geometric mixing schedule before natural ceiling or schedule domination
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
noncomputable def geometric_log_inner_round_lower_bound
    (C beta : Real) (k : Nat) : Real :=
  if hk : 0 < k then
    positive_geometric_log_inner_round_lower_bound C beta ⟨k, hk⟩
  else
    zeroGeometricLogInnerRoundLowerBound C beta

/-- The zero-based geometric-logarithmic inner-round lower-bound selector
unfolds to its positive-index and zero-index branch selectors.

Layer: Model | Gap: Level 0 (zero-based geometric-logarithmic lower-bound unfolding)
Proof: by rfl after unfolding `geometric_log_inner_round_lower_bound`.
Source: Mathlib conditional simplification together with the positive and zero geometric-logarithmic selector APIs
Used in: rewriting the corrected all-index communication lower-bound selector to the branch form required by schedule assumptions
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem geometric_log_inner_round_lower_bound_def
    (C beta : Real) (k : Nat) :
    geometric_log_inner_round_lower_bound C beta k =
      if hk : 0 < k then
        positive_geometric_log_inner_round_lower_bound C beta ⟨k, hk⟩
      else
        zeroGeometricLogInnerRoundLowerBound C beta := by
  rfl

/-- At a positive index, the zero-based lower-bound selector is the
positive-index geometric-logarithmic selector.

Layer: Model | Gap: Level 0 (positive branch of zero-based geometric-logarithmic lower bound)
Proof: unfold `geometric_log_inner_round_lower_bound` and simplify the conditional with the supplied positivity proof.
Source: Mathlib conditional simplification and subtype APIs specialized to positive-index logarithmic communication schedules
Used in: recovering the displayed maximum selector from the corrected all-index communication lower-bound requirement at positive outer-loop indices
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem geometric_log_inner_round_lower_bound_of_pos
    (C beta : Real) {k : Nat} (hk : 0 < k) :
    geometric_log_inner_round_lower_bound C beta k =
      positive_geometric_log_inner_round_lower_bound C beta ⟨k, hk⟩ := by
  simp [geometric_log_inner_round_lower_bound, hk]

/-- At index zero, the zero-based lower-bound selector is the zero-index
constant logarithmic branch.

Layer: Model | Gap: Level 0 (zero branch of zero-based geometric-logarithmic lower bound)
Proof: unfold `geometric_log_inner_round_lower_bound` and simplify the conditional at zero.
Source: Mathlib natural-number order and conditional simplification APIs specialized to zero-index communication schedules
Used in: recovering the corrected zero-index communication lower-bound branch without inventing a convention for `log 0`
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem geometric_log_inner_round_lower_bound_zero
    (C beta : Real) :
    geometric_log_inner_round_lower_bound C beta 0 =
      zeroGeometricLogInnerRoundLowerBound C beta := by
  simp [geometric_log_inner_round_lower_bound]

/-- The zero-based real lower-bound selector is dominated by the natural
ceiling selector after coercion to `Real`.

Layer: Model | Gap: Level 0 (zero-based geometric-logarithmic ceiling lower bound)
Proof: split on the positivity of the index and reuse the already staged positive and zero branch ceiling lower bounds.
Source: Mathlib conditional case splits and natural ceiling lower-bound APIs through the geometric-logarithmic selector family
Used in: proving that selected natural inner communication rounds satisfy the corrected all-index real lower-bound schedule requirement
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/main_theorem/statement_math
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem geometric_log_inner_round_lower_bound_le_geometricLogInnerRoundCeil
    (C beta : Real) (k : Nat) :
    geometric_log_inner_round_lower_bound C beta k <=
      (geometricLogInnerRoundCeil C beta k : Real) := by
  by_cases hk : 0 < k
  · simpa [geometric_log_inner_round_lower_bound, hk]
      using
        positive_geometric_log_inner_round_lower_bound_le_geometric_log_inner_round_ceil
          C beta ⟨k, hk⟩
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst hk0
    simpa [geometric_log_inner_round_lower_bound]
      using zeroGeometricLogInnerRoundLowerBound_le_geometricLogInnerRoundCeil C beta

-- Merged from Staging/sqrtDenominatorContractionAlpha.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: square-root denominator contraction factor; orig was
--   `theoremAlpha`, renamed away from theorem numbering and RGEM-local setup
--   fields while retaining the mathematical role of a closed-form contraction
--   parameter.
-- generality used: real scalar component-count surrogate `m`, smoothness scale
--   `L`, and curvature `mu`; no carrier, measure, independence, integrability,
--   convexity, oracle, topology, norm, inner product, or finite-dimensional
--   hypotheses are used by the definitional construction.
-- portable call pattern: strongly-convex finite-sum, variance-reduced, and
--   accelerated stochastic proofs call this at parameter-selection and
--   geometric-rate setup steps while changing `m`, `L`, and `mu`.
-- counterargument checked: this is a single expression, but it is a named
--   closed-form contraction parameter with reusable sign API, not merely
--   paper traceability; later side-condition proofs use the same denominator
--   formula without depending on the original algorithm setup record.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and the target file
--   for `sqrt alpha contraction denominator`, `sqrt alpha schedule`, and
--   `one minus inverse sqrt denominator`; the closest SOptLib hit was
--   `sqrt_alpha_schedule_pos_lt_one_log_neg`, whose formula is the different
--   normalized schedule `1 - 2 / (m * (sqrt (1 + 16*c/m) + 1))`. LeanSearch
--   returned only generic real square-root and golden-ratio facts.
-- minimal hypotheses: the definition is total over real scalars; the interval
--   theorem uses exactly `1 ≤ m`, `0 ≤ L`, and `0 < mu`.

/-- Closed-form contraction factor with a square-root denominator.

For scalar component-count surrogate `m`, smoothness scale `L`, and curvature
`mu`, this names the factor `1 - (m + sqrt (m^2 + 16*m*L/mu))⁻¹`.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; closed-form real contraction factor built
  from a positive count surrogate, smoothness scale, and curvature)
Source: real square-root parameter choices for strongly-convex finite-sum
  stochastic optimization
Used in: randomized gradient extrapolation geometric-rate parameter selection
  and finite-sum strongly-convex contraction side conditions
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
noncomputable def sqrtDenominatorContractionAlpha (m L mu : ℝ) : ℝ :=
  1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹

/-- The square-root denominator contraction factor unfolds to its closed form.

Layer: Model | Gap: Level 0 (square-root denominator contraction formula)
Proof: by rfl after unfolding `sqrtDenominatorContractionAlpha`.
Source: real square-root parameter choices for strongly-convex finite-sum
  stochastic optimization
Used in: randomized gradient extrapolation geometric-rate parameter selection
  and finite-sum strongly-convex contraction side conditions
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem sqrtDenominatorContractionAlpha_def (m L mu : ℝ) :
    sqrtDenominatorContractionAlpha m L mu =
      1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹ := by
  rfl

/-- The square-root denominator contraction factor lies in `(0, 1)`.

If the component-count surrogate is at least one, the smoothness scale is
nonnegative, and the curvature is positive, then the square-root denominator is
larger than one, so subtracting its reciprocal from one gives a valid
contraction factor.

Layer: Model | Gap: Level 0 (square-root denominator contraction sign bounds)
Proof: prove the radicand is positive and the denominator is greater than one;
  positivity and the upper bound then follow from reciprocal order facts.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: randomized gradient extrapolation geometric-rate parameter selection
  and finite-sum strongly-convex contraction side conditions
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem sqrtDenominatorContractionAlpha_pos_lt_one
    (m L mu : ℝ) (hm_ge_one : 1 ≤ m) (hL_nonneg : 0 ≤ L) (hmu_pos : 0 < mu) :
    0 < sqrtDenominatorContractionAlpha m L mu ∧
      sqrtDenominatorContractionAlpha m L mu < 1 := by
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_one
  have hterm_nonneg : 0 ≤ 16 * m * L / mu := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hm_pos.le) hL_nonneg)
      hmu_pos.le
  have hrad_pos : 0 < m ^ 2 + 16 * m * L / mu := by
    have hm_sq_pos : 0 < m ^ 2 := pow_pos hm_pos 2
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (m ^ 2 + 16 * m * L / mu) :=
    Real.sqrt_pos.2 hrad_pos
  have hden_gt_one : 1 < m + Real.sqrt (m ^ 2 + 16 * m * L / mu) := by
    linarith
  have hden_pos : 0 < m + Real.sqrt (m ^ 2 + 16 * m * L / mu) :=
    lt_trans zero_lt_one hden_gt_one
  have hinv_pos : 0 < (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹ :=
    inv_pos.mpr hden_pos
  have hinv_lt_one : (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hden_gt_one
  constructor
  · simpa [sqrtDenominatorContractionAlpha] using sub_pos.mpr hinv_lt_one
  · simpa [sqrtDenominatorContractionAlpha] using sub_lt_self (1 : ℝ) hinv_pos

-- Generalization plan (G0):
-- concept/name: checked quotient specification; orig was sourceQuotientSpec
-- generality used: arbitrary group-with-zero carrier; no measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: parameter selectors and adaptive stepsize definitions construct a displayed
--   scalar ratio; the numerator, denominator, and quotient witness vary while the checked relation stays fixed
-- counterargument checked: although the predicate is a short conjunction, repeated ratio contracts need
--   its bundled nonzero-denominator fact and the accompanying constructor/eliminator API
-- coverage search: searched "checked quotient relation nonzero denominator cross multiplied quotient
--   equation" and "division equality iff multiplication denominator nonzero"; Mathlib `eq_div_iff`
--   supplies only the algebraic bridge, while SOptLib hits are specialized schedule and budget relations
-- minimal hypotheses: `GroupWithZero K` supplies exactly the division and nonzero-cancellation API used below

/-- A quotient witness together with the side condition that makes division valid.

`checked_quotient_spec numerator denominator value` records both that the
denominator is nonzero and that `value` satisfies the cross-multiplied quotient
equation.

Layer: Glue | Concept: checked quotient specification
Proof: (definitional construction; pair a nonzero denominator with the cross-multiplied quotient equation)
Source: Mathlib group-with-zero division and nonzero-denominator cancellation APIs
Used in: displayed stochastic-optimization parameter ratios and adaptive stepsize formulas whose denominator side conditions must remain explicit
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
def checked_quotient_spec {K : Type*} [GroupWithZero K]
    (numerator denominator value : K) : Prop :=
  denominator ≠ 0 ∧ value * denominator = numerator

/-- The checked quotient specification unfolds to its denominator condition and
cross-multiplied equation.

Layer: Glue | Gap: Level 0 (checked quotient definitional specification)
Proof: by rfl after unfolding `checked_quotient_spec`.
Source: Mathlib group-with-zero multiplication and zero APIs
Used in: exposing denominator validity and cross-multiplied equations for stochastic-optimization parameter and stepsize ratios
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem checked_quotient_spec_def {K : Type*} [GroupWithZero K]
    (numerator denominator value : K) :
    checked_quotient_spec numerator denominator value ↔
      denominator ≠ 0 ∧ value * denominator = numerator := by
  rfl

/-- Division by a nonzero denominator satisfies the checked quotient
specification.

Layer: Glue | Gap: Level 0 (checked quotient construction)
Proof: retain the nonzero-denominator hypothesis and cancel the denominator from the quotient product using `div_mul_cancel₀`.
Source: Mathlib group-with-zero division and `div_mul_cancel₀`
Used in: constructing checked parameter and adaptive-stepsize ratios once their denominator side conditions have been proved
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
theorem checked_quotient_spec_div_of_den_ne {K : Type*} [GroupWithZero K]
    (numerator : K) {denominator : K} (hden : denominator ≠ 0) :
    checked_quotient_spec numerator denominator (numerator / denominator) := by
  exact ⟨hden, div_mul_cancel₀ numerator hden⟩

/-- A checked quotient witness equals ordinary division.

Layer: Glue | Gap: Level 0 (checked quotient elimination)
Proof: apply Mathlib's `eq_div_iff` using the stored nonzero denominator and cross-multiplied equation.
Source: Mathlib group-with-zero division theorem `eq_div_iff`
Used in: replacing checked stochastic-optimization parameter and stepsize witnesses by ordinary quotient expressions during algebraic proofs
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
theorem eq_div_of_checked_quotient_spec {K : Type*} [GroupWithZero K]
    {numerator denominator value : K}
    (h : checked_quotient_spec numerator denominator value) :
    value = numerator / denominator := by
  exact (eq_div_iff h.1).2 h.2

-- Generalization plan (G0):
-- concept/name: Option-valued checked quotient; orig was sourceQuotientValue
-- generality used: arbitrary carrier with zero, division, and decidable equality; the
--   value-specification bridge alone requires a group with zero
-- portable call pattern: parameter selectors, adaptive stepsizes, and normalized potential terms
--   evaluate displayed ratios; their numerators and denominators vary while zero remains an undefined denominator
-- counterargument checked: the construction is a short conditional, but it is not paper-local or a
--   cosmetic wrapper because it preserves undefinedness absent from total division and has a paired specification API
-- coverage search: searched "Option-valued division returns none if denominator is zero otherwise
--   returns quotient" and "partial division Option zero denominator"; Mathlib `Part.instDiv` only
--   propagates existing partiality and SOptLib provides the complementary `checked_quotient_spec`, not this selector
-- minimal hypotheses: `[Zero K] [Div K]` supply the operations used by the selector;
--   `[DecidableEq K]` is used only to compute the zero-denominator branch

/-- The partial quotient that is undefined exactly when its denominator is zero.

Unlike the total division operation on a group with zero, this selector retains
the side condition needed for a displayed quotient as `Option.none`.

Layer: Glue | Concept: Option-valued checked quotient
Proof: (definitional construction; branch on whether the denominator is zero and otherwise return ordinary division)
Source: Mathlib zero and division operations, decidable equality, and `Option`
Used in: stochastic-optimization parameter selectors, adaptive stepsizes, and normalized potential terms whose displayed denominators require explicit validation
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
def checked_quotient {K : Type*} [Zero K] [Div K] [DecidableEq K]
    (numerator denominator : K) : Option K :=
  if denominator = 0 then none else some (numerator / denominator)

/-- The checked quotient is definitionally the zero-denominator conditional.

Layer: Glue | Gap: Level 0 (checked quotient definitional equation)
Proof: by rfl after unfolding `checked_quotient`.
Source: Mathlib zero and division operations, decidable conditionals, and `Option`
Used in: simplifying checked stochastic-optimization ratios after a denominator side condition has been established
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem checked_quotient_def {K : Type*} [Zero K] [Div K] [DecidableEq K]
    (numerator denominator : K) :
    checked_quotient numerator denominator =
      if denominator = 0 then none else some (numerator / denominator) := by
  rfl

/-- Deprecated compatibility name for algorithm proofs staged before the
snake_case Glue API was introduced. -/
@[deprecated checked_quotient_def (since := "2026-08-06")]
theorem checkedQuotientValue_def {K : Type*} [Zero K] [Div K] [DecidableEq K]
    (numerator denominator : K) :
    checked_quotient numerator denominator =
      if denominator = 0 then none else some (numerator / denominator) :=
  checked_quotient_def numerator denominator

/-- A checked quotient is undefined if and only if its denominator is zero.

Layer: Glue | Gap: Level 0 (checked quotient undefinedness characterization)
Proof: unfold the selector and simplify the two zero-denominator branches.
Source: Mathlib decidable conditionals and `Option` constructor disjointness
Used in: proving that stochastic-optimization parameter and adaptive-stepsize ratios are available exactly under their denominator run contracts
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem checked_quotient_eq_none_iff {K : Type*} [Zero K] [Div K] [DecidableEq K]
    (numerator denominator : K) :
    checked_quotient numerator denominator = none ↔ denominator = 0 := by
  simp [checked_quotient]

/-- A value is returned by the checked quotient exactly when it satisfies the
checked quotient specification.

Layer: Glue | Gap: Level 0 (checked quotient value-specification equivalence)
Proof: split on a zero denominator; in the nonzero branch use the checked quotient constructor and its division uniqueness theorem.
Source: Mathlib group-with-zero division together with `checked_quotient_spec_div_of_den_ne` and `eq_div_of_checked_quotient_spec`
Used in: moving between Option-valued stochastic-optimization ratios and explicit nonzero-denominator quotient witnesses
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STORM -/
@[simp]
theorem checked_quotient_eq_some_iff {K : Type*} [GroupWithZero K]
    [DecidableEq K]
    {numerator denominator value : K} :
    checked_quotient numerator denominator = some value ↔
      checked_quotient_spec numerator denominator value := by
  by_cases hden : denominator = 0
  · simp [checked_quotient, checked_quotient_spec, hden]
  · rw [checked_quotient_def]
    simp only [hden, ↓reduceIte, Option.some.injEq]
    constructor
    · intro hvalue
      rw [← hvalue]
      exact checked_quotient_spec_div_of_den_ne numerator hden
    · intro hspec
      exact (eq_div_of_checked_quotient_spec hspec).symm

-- Generalization plan (G0):
-- concept/name: inverse real-power adaptive step-size schedule; orig was
--   `adaptiveStepsize`, renamed to `inverse_rpow_step_size`
-- generality used: four real scalars for the numerator, offset, accumulated
--   statistic, and exponent; no carrier, measure, convexity, smoothness,
--   oracle, filtration, integrability, or finite-dimensional assumptions
-- portable call pattern: AdaGrad-style, recursive-momentum, and adaptive
--   stochastic-gradient updates vary the numerator, stabilizing offset,
--   accumulated statistic, and exponent while retaining the quotient by a
--   real power of offset plus accumulator
-- counterargument checked: although the construction is a single formula, it
--   is a named adaptive schedule used by update, positivity, and measurability
--   arguments; the companion API preserves that boundary, whereas the
--   separately proposed base and denominator fragments were caller-side
--   expressions and were declined
-- coverage search: `lean_search_symbols` queries for "stepsize equal numerator
--   divided by real power of offset plus accumulator", "inverse real power
--   adaptive stepsize schedule", and "numerator division Real.rpow offset
--   accumulator exponent" found only paper-local STORM equations and unrelated
--   real-power bounds; the closest SOptLib definition is the constant
--   `halfLipschitzStepSizeSchedule`, and Mathlib semantic search exposes
--   `Real.rpow` primitives but no adaptive schedule definition
-- minimal hypotheses: the definition and unfolding theorem use only real
--   operations; positivity needs positive numerator and base, while
--   measurability needs no restriction on the exponent

/-- The inverse real-power step size with an additive stabilizing offset.

For numerator `numerator`, offset `offset`, accumulated statistic
`accumulator`, and exponent `exponent`, this is
`numerator / (offset + accumulator) ^ exponent` using `Real.rpow`.

Layer: Model | Concept: inverse real-power adaptive step-size schedule
Proof: (definitional construction; divide the numerator by the real power of the offset plus accumulated statistic)
Source: Mathlib real-power and real-field operations for adaptive optimization parameter schedules
Used in: recursive-momentum, AdaGrad-style, and adaptive stochastic-gradient updates whose step size decays with an accumulated gradient statistic
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
noncomputable def inverse_rpow_step_size
    (numerator offset accumulator exponent : ℝ) : ℝ :=
  numerator / Real.rpow (offset + accumulator) exponent

/-- The inverse real-power step size unfolds to its defining quotient.

Layer: Model | Gap: Level 0 (inverse real-power step-size unfolding)
Proof: by rfl after unfolding `inverse_rpow_step_size`.
Source: Mathlib real-power and real-field definitional reduction APIs
Used in: adaptive stochastic-gradient scalar algebra that substitutes the explicit accumulated-statistic denominator for the named step size
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
@[simp] theorem inverse_rpow_step_size_def
    (numerator offset accumulator exponent : ℝ) :
    inverse_rpow_step_size numerator offset accumulator exponent =
      numerator / Real.rpow (offset + accumulator) exponent := by
  rfl

/-- An inverse real-power step size is positive when its numerator and base are positive.

Layer: Model | Gap: Level 0 (inverse real-power step-size positivity)
Proof: unfold the schedule, use positivity of `Real.rpow` on a positive base, and apply positivity of division.
Source: Mathlib `Real.rpow_pos_of_pos` and ordered-field division positivity APIs
Used in: adaptive recursive-momentum and stochastic-gradient proofs establishing positive update scales from positive offsets and accumulated statistics
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_pos_of_numerator_pos_of_base_pos
    (numerator offset accumulator exponent : ℝ)
    (hnumerator : 0 < numerator)
    (hbase : 0 < offset + accumulator) :
    0 < inverse_rpow_step_size numerator offset accumulator exponent := by
  rw [inverse_rpow_step_size_def]
  exact div_pos hnumerator (Real.rpow_pos_of_pos hbase exponent)

/-- The inverse real-power step size is measurable in its accumulated statistic.

Layer: Model | Gap: Level 0 (inverse real-power step-size measurability)
Proof: take the measurable constant real power of the offset accumulator, then use measurability of constant division.
Source: Mathlib `Measurable.pow_const`, `Measurable.const_div`, and measurable real-field operation APIs
Used in: adaptive stochastic-gradient process proofs transporting measurability of accumulated gradient statistics to generated step sizes
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_measurable
    (numerator offset exponent : ℝ) :
    Measurable
      (fun accumulator : ℝ =>
        inverse_rpow_step_size numerator offset accumulator exponent) := by
  rw [show (fun accumulator : ℝ =>
      inverse_rpow_step_size numerator offset accumulator exponent) =
      fun accumulator : ℝ =>
        numerator / Real.rpow (offset + accumulator) exponent by
    funext accumulator
    rw [inverse_rpow_step_size_def]]
  have hbase : Measurable (fun accumulator : ℝ => offset + accumulator) :=
    measurable_const.add measurable_id
  exact (hbase.pow_const exponent).const_div numerator

-- Generalization plan (G0):
-- concept/name: quadratic momentum weight; orig was momentumWeight
-- generality used: an arbitrary monoid for the definition and unfolding theorem;
--   an ordered semiring with the minimal square-nonnegativity order interfaces for the
--   nonnegativity theorem
-- portable call pattern: recursive-momentum and variance-reduced stochastic-gradient
--   updates choose a new coefficient and step while retaining the weight coefficient * step^2
-- counterargument checked: although the formula is short, it is a named update parameter used
--   by transition, measurability, continuity, and sign arguments; its unfolding and sign API
--   preserve that mathematical boundary rather than merely renaming a caller-side expression
-- coverage search: queries "quadratic momentum weight coefficient times squared step size" and
--   "parameter weight coefficient multiplied by square of step size equality" found only the
--   finite aggregate outputSquaredStepSum and the different weight gamma - L * gamma^2;
--   Mathlib semantic search found QuadraticMap.weightedSumSquares, which is an indexed quadratic
--   map rather than this scalar algorithm parameter, so coverage is partial and non-duplicative
-- minimal hypotheses: Monoid supplies multiplication and natural powers; Semiring, LinearOrder,
--   ExistsAddOfLE, PosMulMono, AddLeftMono, and coefficient nonnegativity are used only by the
--   sign theorem

/-- The quadratic momentum weight obtained by scaling the square of a step size.

Layer: Model | Concept: quadratic momentum parameter choice
Proof: (definitional construction; multiply a scalar coefficient by the square of the step)
Source: recursive-momentum parameter schedules and Mathlib semiring natural-power operations
Used in: recursive-momentum and variance-reduced stochastic-gradient transitions that damp the
  previous direction by one minus a coefficient-scaled squared step size
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/3
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD,
  STOchastic Recursive Momentum -/
def quadraticMomentumWeight {R : Type*} [Monoid R]
    (coefficient step : R) : R :=
  coefficient * step ^ 2

/-- A quadratic momentum weight unfolds to the coefficient times the squared step size.

Layer: Model | Gap: Level 0 (quadratic momentum weight unfolding)
Proof: by rfl after unfolding `quadraticMomentumWeight`.
Source: Mathlib semiring multiplication and natural-power APIs
Used in: recursive-momentum transition equations and scalar algebra that substitute the displayed
  coefficient-scaled squared-step formula for the named momentum weight
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/3
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD,
  STOchastic Recursive Momentum -/
@[simp] theorem quadraticMomentumWeight_def
    {R : Type*} [Monoid R] (coefficient step : R) :
    quadraticMomentumWeight coefficient step = coefficient * step ^ 2 := by
  rfl

/-- A quadratic momentum weight is nonnegative when its coefficient is nonnegative.

Layer: Model | Gap: Level 0 (quadratic momentum weight nonnegativity)
Proof: unfold the weight, then combine coefficient nonnegativity with nonnegativity of a square.
Source: Mathlib ordered ring multiplication and square-nonnegativity APIs
Used in: recursive-momentum stability arguments that bound one minus the momentum weight after
  proving the algorithmic coefficient is nonnegative
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/3
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD,
  STOchastic Recursive Momentum -/
theorem quadraticMomentumWeight_nonneg
    {R : Type*} [Semiring R] [LinearOrder R] [ExistsAddOfLE R]
    [PosMulMono R] [AddLeftMono R]
    (coefficient step : R)
    (hcoefficient : 0 ≤ coefficient) :
    0 ≤ quadraticMomentumWeight coefficient step := by
  exact mul_nonneg hcoefficient (sq_nonneg step)

-- Generalization plan (G0):
-- concept/name: checked inverse real-power step-size schedule; orig was
--   `adaptiveStepsizeSourceValue`, renamed to `checked_inverse_rpow_step_size`
-- generality used: four real scalars for the numerator, offset, accumulated
--   statistic, and exponent; no measure, convexity, smoothness, oracle,
--   filtration, integrability, carrier, or finite-dimensional assumptions
-- portable call pattern: recursive-momentum, AdaGrad-style, and adaptive
--   stochastic-gradient algorithms validate positivity of an offset plus an
--   accumulated statistic before selecting the corresponding inverse-power step
-- counterargument checked: this is a short composition, but it is not a pure
--   rename or caller-side expression: it is the partial counterpart of the
--   named inverse-power schedule and its positive-base theorem bridges checked
--   source semantics to the total schedule used in arithmetic and updates
-- coverage search: searched "checked inverse real power step size some total
--   inverse power positive base" and "Option valued real rpow positive base
--   checked quotient numerator denominator"; Mathlib provides `Real.rpow`,
--   while SOptLib provides `checked_quotient` and `inverse_rpow_step_size`, but
--   neither Mathlib nor SOptLib contains their positive-base checked composition
-- minimal hypotheses: all definition parameters are real scalars; only the
--   bridge theorem assumes positivity of the denominator base

/-- The inverse real-power step size, defined only when its denominator base is
positive.

When `offset + accumulator` is positive, this checks the resulting real-power
denominator before returning the quotient. Otherwise it returns `none`.

Layer: Model | Concept: checked inverse real-power adaptive step-size schedule
Proof: (definitional construction; validate the real-power base and apply the Option-valued checked quotient to the resulting denominator)
Source: Mathlib `Real.rpow`, ordered real arithmetic, and SOptLib checked quotient and inverse real-power schedule APIs
Used in: recursive-momentum, AdaGrad-style, and adaptive stochastic-gradient updates that retain a positive denominator-base run contract before selecting a step size
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
noncomputable def checked_inverse_rpow_step_size
    (numerator offset accumulator exponent : ℝ) : Option ℝ :=
  if 0 < offset + accumulator then
    checked_quotient numerator (Real.rpow (offset + accumulator) exponent)
  else
    none

/-- The checked inverse real-power step size unfolds to its positive-base
conditional and checked denominator quotient.

Layer: Model | Gap: Level 0 (checked inverse real-power step-size unfolding)
Proof: by rfl after unfolding `checked_inverse_rpow_step_size`.
Source: Mathlib decidable conditionals and real powers together with SOptLib `checked_quotient`
Used in: simplifying a validated adaptive step-size selector to its checked real-power quotient branch
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
@[simp] theorem checked_inverse_rpow_step_size_def
    (numerator offset accumulator exponent : ℝ) :
    checked_inverse_rpow_step_size numerator offset accumulator exponent =
      if 0 < offset + accumulator then
        checked_quotient numerator (Real.rpow (offset + accumulator) exponent)
      else
        none := by
  rfl

/-- A positive denominator base makes the checked inverse real-power step size
equal to the total inverse real-power schedule.

Layer: Model | Gap: Level 0 (checked-to-total inverse real-power step-size bridge)
Proof: select the positive-base branch, use positivity of `Real.rpow` to discharge the checked quotient denominator condition, and unfold the total schedule
Source: Mathlib `Real.rpow_pos_of_pos` and SOptLib checked quotient and inverse real-power step-size definitions
Used in: recursive-momentum and adaptive stochastic-gradient proofs that replace a source-validated step-size value by the total scalar used in update algebra
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
@[simp] theorem checked_inverse_rpow_step_size_eq_some_of_base_pos
    (numerator offset accumulator exponent : ℝ)
    (hbase : 0 < offset + accumulator) :
    checked_inverse_rpow_step_size numerator offset accumulator exponent =
      some (inverse_rpow_step_size numerator offset accumulator exponent) := by
  have hden : (offset + accumulator) ^ exponent ≠ 0 := by
    positivity
  simp [checked_inverse_rpow_step_size, checked_quotient, inverse_rpow_step_size,
    hbase, hden]

-- Generalization plan (G0):
-- concept/name: positive-base checked specification for an inverse real-power
--   step-size schedule; orig was `adaptiveStepsize_source_spec_of_base_pos`,
--   renamed to `inverseRpowStepSizeSpec_of_base_pos`
-- generality used: four real scalars for the numerator, offset, accumulated
--   statistic, and exponent; no carrier, measure, convexity, smoothness,
--   oracle, filtration, integrability, or finite-dimensional assumptions
-- portable call pattern: recursive-momentum, AdaGrad-style, and adaptive
--   stochastic-gradient proofs vary the schedule parameters and accumulated
--   statistic while deriving the same positive-base checked quotient contract
-- counterargument checked: the proof composes short existing APIs, but is not
--   a pure rename: it packages the positive source-domain condition together
--   with the checked specification of the named total inverse-power schedule
-- coverage search: queries for "inverse rpow step size checked quotient
--   specification positive base" and "positive real rpow nonzero quotient
--   multiplication specification" found the partial SOptLib results
--   `checked_quotient_spec_div_of_den_ne` and
--   `checked_inverse_rpow_step_size_eq_some_of_base_pos`; Mathlib semantic
--   search found `Real.rpow_pos_of_pos`, but no theorem with this conjunction
-- minimal hypotheses: all parameters are real scalars and the only hypothesis
--   is pointwise positivity of the shifted denominator base

/-- A positive shifted base gives the checked quotient specification for an
inverse real-power step size.

Layer: Model | Gap: Level 0 (positive-base checked inverse-power schedule specification)
Proof: use `Real.rpow_pos_of_pos` to make the denominator nonzero, then apply the checked quotient constructor after unfolding the named schedule.
Source: Mathlib `Real.rpow_pos_of_pos` and SOptLib checked quotient construction for nonzero denominators
Used in: recursive-momentum, AdaGrad-style, and adaptive stochastic-gradient proofs validating displayed inverse-power step sizes before using their totalized values
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverseRpowStepSizeSpec_of_base_pos
    (numerator offset accumulator exponent : ℝ)
    (hbase : 0 < offset + accumulator) :
    0 < offset + accumulator ∧
      checked_quotient_spec numerator
        (Real.rpow (offset + accumulator) exponent)
        (inverse_rpow_step_size numerator offset accumulator exponent) := by
  refine ⟨hbase, ?_⟩
  rw [inverse_rpow_step_size_def]
  exact checked_quotient_spec_div_of_den_ne numerator
    (ne_of_gt (Real.rpow_pos_of_pos hbase exponent))

-- Generalization plan (G0):
-- concept/name: reciprocal continuity of an inverse real-power adaptive
--   step-size schedule; orig was
--   `lemma2_reciprocal_stepsize_of_sumSq_continuousOn_Icc`, renamed to
--   `inverse_rpow_step_size_reciprocal_continuousOn_Icc`
-- generality used: real numerator, offset, exponent, accumulator, and interval
--   endpoint; no carrier, measure, convexity, smoothness, oracle, filtration,
--   integrability, or finite-dimensional assumptions
-- portable call pattern: recursive-momentum, AdaGrad-style, and adaptive
--   stochastic-gradient proofs vary the numerator, stabilizing offset,
--   exponent, accumulated statistic, and compact range while retaining
--   continuity of the reciprocal schedule used for compact-range bounds
-- counterargument checked: this is not merely a paper traceability wrapper;
--   it packages the nontrivial reciprocal-of-a-quotient rewrite with real-power
--   continuity for the named schedule, and no existing API theorem supplies
--   that compound conclusion
-- coverage search: symbol queries for "reciprocal inverse rpow step size
--   continuous on interval nonnegative exponent" and
--   "inverse rpow step size reciprocal continuous" found the staged
--   `inverse_rpow_step_size` definition and its measurability theorem but no
--   continuity result; Mathlib semantic search found only the partial building
--   blocks `Real.continuous_rpow_const` and `ContinuousWithinAt.rpow_const`
-- minimal hypotheses: `0 ≤ exponent` is exactly what gives global continuity
--   of real power even where the shifted accumulator vanishes; totalized
--   division makes a nonzero-numerator assumption unnecessary

/-- The reciprocal of an inverse real-power step size is continuous on a
compact accumulator interval when the exponent is nonnegative.

Layer: Model | Gap: Level 0 (reciprocal inverse-real-power schedule continuity)
Proof: rewrite the reciprocal quotient as the shifted real power divided by the numerator, then compose affine, real-power, and constant-multiplication continuity.
Source: Mathlib `Real.continuous_rpow_const`, continuous affine operations, and real-field quotient identities
Used in: recursive-momentum and AdaGrad-style integrability proofs bounding reciprocal adaptive step sizes over a compact range of accumulated squared gradients
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_reciprocal_continuousOn_Icc
    (numerator offset exponent R : ℝ)
    (hexponent : 0 ≤ exponent) :
    ContinuousOn
      (fun accumulator : ℝ =>
        1 / inverse_rpow_step_size numerator offset accumulator exponent)
      (Set.Icc 0 R) := by
  have hrpow_cont :
      ContinuousOn
        (fun accumulator : ℝ => Real.rpow (offset + accumulator) exponent)
        (Set.Icc 0 R) := by
    exact
      ((Real.continuous_rpow_const hexponent).comp
        (continuous_const.add continuous_id)).continuousOn
  have hrewrite :
      (fun accumulator : ℝ =>
          1 / inverse_rpow_step_size numerator offset accumulator exponent) =
        fun accumulator : ℝ =>
          Real.rpow (offset + accumulator) exponent / numerator := by
    funext accumulator
    rw [inverse_rpow_step_size_def]
    exact one_div_div _ _
  rw [hrewrite]
  simpa [div_eq_mul_inv] using hrpow_cont.mul continuousOn_const

-- Generalization plan (G0):
-- concept/name: continuity of the complementary quadratic momentum weight for
--   an inverse real-power step-size schedule; orig was
--   `lemma3_one_sub_momentum_of_sumSq_continuousOn_Icc`
-- generality used: real numerator, positive offset, arbitrary real exponent,
--   quadratic-weight coefficient, and interval endpoint; no carrier, measure,
--   convexity, smoothness, oracle, filtration, integrability, or
--   finite-dimensional assumptions
-- portable call pattern: recursive-momentum and variance-reduced stochastic-
--   gradient proofs vary the schedule numerator, stabilizing offset, decay
--   exponent, momentum coefficient, and accumulator range while retaining
--   continuity of one minus the generated momentum weight
-- counterargument checked: the result is not a paper-local rename or a pure
--   wrapper; it composes two named parameter choices and packages the positive-
--   base side condition needed to prove continuity for arbitrary real exponents
-- coverage search: symbol queries for "one minus quadratic momentum weight
--   inverse real power step size continuous on interval positive offset",
--   "inverse rpow step size continuous on Icc positive base", and "Real rpow
--   composition division continuousOn positive base" found no matching project
--   declaration; Mathlib semantic search found the component theorem
--   `ContinuousOn.rpow_const`, while the staged reciprocal-continuity theorem
--   has a different conclusion and assumes a nonnegative exponent
-- minimal hypotheses: positivity of the offset is sufficient on `Icc 0 R` to
--   keep the real-power denominator nonzero; the exponent, numerator,
--   coefficient, and endpoint are otherwise unrestricted

/-- One minus the quadratic momentum weight of an inverse real-power step size
is continuous on a nonnegative compact accumulator interval when the schedule
offset is positive.

Layer: Model | Gap: Level 0 (complementary quadratic momentum schedule continuity)
Proof: prove the shifted base is positive on the interval, use `ContinuousOn.rpow_const` for the denominator, and preserve continuity through division, squaring, scalar multiplication, and subtraction.
Source: Mathlib `ContinuousOn.rpow_const`, continuous real-field operations, and the SOptLib inverse-real-power step-size and quadratic-momentum parameter definitions
Used in: recursive-momentum compact-range bounds where one minus the next momentum coefficient is composed with an accumulated squared-gradient step-size schedule
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem one_sub_quadraticMomentumWeight_inverseRpowStepSize_continuousOn_Icc
    (numerator offset exponent coefficient R : ℝ)
    (hoffset : 0 < offset) :
    ContinuousOn
      (fun accumulator : ℝ =>
        1 - quadraticMomentumWeight coefficient
          (inverse_rpow_step_size numerator offset accumulator exponent))
      (Set.Icc 0 R) := by
  have hbase_pos :
      ∀ accumulator ∈ Set.Icc (0 : ℝ) R, 0 < offset + accumulator := by
    intro accumulator haccumulator
    exact add_pos_of_pos_of_nonneg hoffset haccumulator.1
  have hbase_ne :
      ∀ accumulator ∈ Set.Icc (0 : ℝ) R, offset + accumulator ≠ 0 := by
    intro accumulator haccumulator
    exact ne_of_gt (hbase_pos accumulator haccumulator)
  have hrpow_cont :
      ContinuousOn
        (fun accumulator : ℝ => Real.rpow (offset + accumulator) exponent)
        (Set.Icc 0 R) := by
    exact
      (continuousOn_const.add continuousOn_id).rpow_const
        (fun accumulator haccumulator =>
          Or.inl (hbase_ne accumulator haccumulator))
  have hrpow_ne :
      ∀ accumulator ∈ Set.Icc (0 : ℝ) R,
        Real.rpow (offset + accumulator) exponent ≠ 0 := by
    intro accumulator haccumulator
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos accumulator haccumulator) exponent)
  have hstepsize_cont :
      ContinuousOn
        (fun accumulator : ℝ =>
          inverse_rpow_step_size numerator offset accumulator exponent)
        (Set.Icc 0 R) := by
    simpa only [inverse_rpow_step_size_def] using
      continuousOn_const.div hrpow_cont hrpow_ne
  have hstepsize_sq_cont :
      ContinuousOn
        (fun accumulator : ℝ =>
          inverse_rpow_step_size numerator offset accumulator exponent ^ 2)
        (Set.Icc 0 R) :=
    hstepsize_cont.pow 2
  simpa only [quadraticMomentumWeight_def] using
    continuousOn_const.sub (continuousOn_const.mul hstepsize_sq_cont)

-- Generalization plan (G0):
-- concept/name: continuity of the reciprocal inverse-rpow step size times the
--   squared complementary quadratic momentum weight; orig was
--   `lemma3_scalar_multiplier_of_sumSq_continuousOn_Icc`, renamed to
--   `inverse_rpow_step_size_complementary_quadratic_momentum_multiplier_continuousOn_Icc`
-- generality used: real numerator, positive offset, arbitrary real exponent,
--   quadratic momentum coefficient, and interval endpoint; no carrier,
--   measure, convexity, smoothness, oracle, filtration, integrability, or
--   finite-dimensional assumptions
-- portable call pattern: recursive-momentum and adaptive variance-reduction
--   proofs vary the inverse-power schedule and quadratic momentum parameters
--   while bounding the multiplier eta^{-1} * (1 - a(eta))^2 over a compact
--   range of accumulated squared gradients
-- counterargument checked: although continuity closure combines two component
--   factors, the exact multiplier is the reusable coefficient in error-energy
--   and compact-range bounds; unlike the existing reciprocal theorem, this
--   statement also permits arbitrary real exponents under a positive offset
-- coverage search: symbol queries for "inverse real power step size reciprocal
--   times squared complementary quadratic momentum weight continuous" and
--   "eta inverse one minus momentum squared continuousOn Icc" found only the
--   component theorems
--   `inverse_rpow_step_size_reciprocal_continuousOn_Icc` and
--   `one_sub_quadraticMomentumWeight_inverseRpowStepSize_continuousOn_Icc`;
--   Mathlib semantic search found only generic `ContinuousOn.inv₀`,
--   `ContinuousOn.div₀`, and continuity closure results, so coverage is partial
-- minimal hypotheses: positivity of the offset keeps every shifted base on
--   `Icc 0 R` positive; the source nonzero-numerator hypothesis is unnecessary,
--   and no sign restriction on the exponent is needed on a positive base

/-- The reciprocal inverse-real-power step size times the square of its
complementary quadratic momentum weight is continuous on a nonnegative compact
accumulator interval when the schedule offset is positive.

Layer: Model | Gap: Level 0 (adaptive reciprocal complementary-momentum multiplier continuity)
Proof: use positive-base real-power continuity to control the reciprocal schedule, reuse complementary quadratic-momentum continuity, and close under squaring and multiplication.
Source: Mathlib `ContinuousOn.rpow_const` and continuous real-field operations, composed with SOptLib inverse-real-power step-size and quadratic-momentum parameter APIs
Used in: recursive-momentum and adaptive variance-reduction proofs obtaining compact-range bounds for the error-energy multiplier eta^{-1} times the squared complementary momentum coefficient
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_complementary_quadratic_momentum_multiplier_continuousOn_Icc
    (numerator offset exponent coefficient R : ℝ)
    (hoffset : 0 < offset) :
    ContinuousOn
      (fun accumulator : ℝ =>
        (1 / inverse_rpow_step_size numerator offset accumulator exponent) *
          (1 - quadraticMomentumWeight coefficient
            (inverse_rpow_step_size numerator offset accumulator exponent)) ^ 2)
      (Set.Icc 0 R) := by
  have hbase_pos :
      ∀ accumulator ∈ Set.Icc (0 : ℝ) R, 0 < offset + accumulator := by
    intro accumulator haccumulator
    exact add_pos_of_pos_of_nonneg hoffset haccumulator.1
  have hbase_ne :
      ∀ accumulator ∈ Set.Icc (0 : ℝ) R, offset + accumulator ≠ 0 := by
    intro accumulator haccumulator
    exact ne_of_gt (hbase_pos accumulator haccumulator)
  have hrpow_cont :
      ContinuousOn
        (fun accumulator : ℝ => Real.rpow (offset + accumulator) exponent)
        (Set.Icc 0 R) := by
    exact
      (continuousOn_const.add continuousOn_id).rpow_const
        (fun accumulator haccumulator =>
          Or.inl (hbase_ne accumulator haccumulator))
  have hreciprocal :
      ContinuousOn
        (fun accumulator : ℝ =>
          1 / inverse_rpow_step_size numerator offset accumulator exponent)
        (Set.Icc 0 R) := by
    rw [show (fun accumulator : ℝ =>
          1 / inverse_rpow_step_size numerator offset accumulator exponent) =
        fun accumulator : ℝ =>
          Real.rpow (offset + accumulator) exponent / numerator by
      funext accumulator
      rw [inverse_rpow_step_size_def]
      exact one_div_div _ _]
    simpa only [div_eq_mul_inv] using hrpow_cont.mul continuousOn_const
  have hcomplement :=
    one_sub_quadraticMomentumWeight_inverseRpowStepSize_continuousOn_Icc
      numerator offset exponent coefficient R hoffset
  exact hreciprocal.mul (hcomplement.pow 2)

-- Generalization plan (G0):
-- concept/name: antitonicity of an inverse real-power step-size schedule;
--   orig was `theorem1_generated_stepsize_antitone`, renamed to
--   `inverse_rpow_step_size_antitone_of_monotone`
-- generality used: an arbitrary preordered index type, three real schedule
--   parameters, and a real-valued accumulator; no measure, convexity,
--   smoothness, oracle, filtration, integrability, or carrier assumptions
-- portable call pattern: recursive-momentum, AdaGrad-style, and adaptive
--   stochastic-gradient proofs vary the index type, numerator, stabilizing
--   offset, exponent, and monotone nonnegative statistic while retaining an
--   antitone step-size schedule
-- counterargument checked: Mathlib supplies the component real-power and
--   division order lemmas, but not the coherent contract for the named
--   inverse-power adaptive schedule; this theorem adds the schedule-level API
--   used directly by terminal-step-size and weighted-sum arguments
-- coverage search: `lean_search_symbols` queries for "inverse real power step
--   size antitone monotone accumulator positive offset numerator nonnegative
--   exponent" and "Real rpow antitone positive base nonnegative numerator
--   exponent monotone function division" found the existing schedule API but
--   no antitonicity theorem; Mathlib semantic search found
--   `Real.antitoneOn_rpow_Ioi_of_exponent_nonpos`, `Monotone.inv`, and
--   `one_div_pow_anti`, which do not package this parameterized schedule
-- minimal hypotheses: monotonicity is pointwise through `Monotone accumulator`;
--   base positivity is required only at schedule indices, and the numerator
--   and exponent are merely nonnegative

/-- An inverse real-power step-size schedule is antitone along a monotone
accumulator with positive shifted values.

Layer: Model | Gap: Level 0 (inverse real-power adaptive schedule antitonicity)
Proof: compare shifted accumulators, apply `Real.rpow_le_rpow` at a nonnegative exponent, then reverse the positive denominator inequality using nonnegative-numerator division.
Source: Mathlib `Real.rpow_le_rpow`, `Real.rpow_pos_of_pos`, and linear ordered-field division APIs
Used in: recursive-momentum and AdaGrad-style convergence proofs comparing a terminal adaptive step size with every earlier step size before bounding a weighted gradient sum
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_antitone_of_monotone
    {ι : Type*} [Preorder ι]
    (numerator offset exponent : ℝ) (accumulator : ι → ℝ)
    (haccumulator : Monotone accumulator)
    (hbase : ∀ i, 0 < offset + accumulator i)
    (hnumerator : 0 ≤ numerator) (hexponent : 0 ≤ exponent) :
    Antitone
      (fun i =>
        inverse_rpow_step_size numerator offset (accumulator i) exponent) := by
  intro i j hij
  have hbase_i : 0 < offset + accumulator i := hbase i
  have hpow_le :
      Real.rpow (offset + accumulator i) exponent ≤
        Real.rpow (offset + accumulator j) exponent :=
    Real.rpow_le_rpow (le_of_lt hbase_i)
      (by linarith [haccumulator hij]) hexponent
  change
    inverse_rpow_step_size numerator offset (accumulator j) exponent ≤
      inverse_rpow_step_size numerator offset (accumulator i) exponent
  rw [inverse_rpow_step_size_def, inverse_rpow_step_size_def]
  exact div_le_div_of_nonneg_left hnumerator
    (Real.rpow_pos_of_pos hbase_i exponent) hpow_le

-- Generalization plan (G0):
-- concept/name: upper bound for a one-third inverse real-power step-size
--   schedule; orig was `theorem1_generated_stepsize_le_one_over_fourL`,
--   renamed to `inverse_rpow_step_size_one_third_le_one_div_four_mul`
-- generality used: four real scalars for the numerator, offset, accumulated
--   statistic, and positive scale; no carrier, measure, convexity, smoothness,
--   oracle, filtration, integrability, or finite-dimensional assumptions
-- portable call pattern: recursive-momentum, AdaGrad-style, and adaptive
--   stochastic-gradient analyses vary the numerator, stabilizing offset,
--   nonnegative accumulated statistic, and positive smoothness scale while
--   using the same inverse-cube-root schedule and cubic offset-floor bound
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes cube-root monotonicity, denominator positivity, and
--   ordered division into a schedule-level bound absent from the existing API
-- coverage search: `lean_search_symbols` query "inverse real power step size
--   one third upper bound one divided four times positive scale cube lower
--   bound" found the existing schedule and antitonicity API but no upper-bound
--   theorem; Mathlib semantic search found `Real.le_rpow_inv_iff_of_pos`, which
--   supplies only the root comparison and not the quotient conclusion
-- minimal hypotheses: nonnegativity of the numerator and positivity of the
--   scale suffice; when the numerator is positive, the cubic lower bound
--   implies positivity of the shifted statistic, while the zero case is
--   immediate from the schedule definition

/-- A one-third inverse real-power step size is at most `1 / (4 * L)` when
the shifted statistic dominates the cube of `4 * L * numerator`.

Layer: Model | Gap: Level 0 (inverse-cube-root adaptive step-size upper bound)
Proof: convert the cubic floor to a cube-root lower bound with `Real.le_rpow_inv_iff_of_pos`, then compare and cancel the positive real-power denominator.
Source: Mathlib `Real.le_rpow_inv_iff_of_pos`, positive real powers, and linear ordered-field division APIs
Used in: recursive-momentum, AdaGrad-style, and adaptive stochastic-gradient proofs discharging a smoothness-scale cap on an inverse-cube-root step size from its offset floor
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_one_third_le_one_div_four_mul
    (numerator offset statistic L : ℝ)
    (hnumerator : 0 ≤ numerator) (hL : 0 < L)
    (hcube : (4 * L * numerator) ^ 3 ≤ offset + statistic) :
    inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3) ≤
      (1 : ℝ) / (4 * L) := by
  rcases hnumerator.eq_or_lt with rfl | hnumerator_pos
  · simp only [inverse_rpow_step_size_def, zero_div]
    exact one_div_nonneg.mpr (mul_nonneg (by norm_num) hL.le)
  · have hfourL_pos : 0 < 4 * L := by positivity
    have hscaled_pos : 0 < 4 * L * numerator := by positivity
    have hbase_pos : 0 < offset + statistic :=
      lt_of_lt_of_le (pow_pos hscaled_pos 3) hcube
    have hroot_inv :
        4 * L * numerator ≤
          Real.rpow (offset + statistic) ((3 : ℝ)⁻¹) := by
      exact
        (Real.le_rpow_inv_iff_of_pos
          (le_of_lt hscaled_pos) (le_of_lt hbase_pos)
          (by norm_num : (0 : ℝ) < 3)).2
          (by simpa [one_div] using hcube)
    have hroot :
        4 * L * numerator ≤
          Real.rpow (offset + statistic) ((1 : ℝ) / 3) := by
      simpa [one_div] using hroot_inv
    have hnumerator_le :
        numerator ≤
          Real.rpow (offset + statistic) ((1 : ℝ) / 3) / (4 * L) := by
      exact (le_div_iff₀ hfourL_pos).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hroot)
    have hden_pos :
        0 < Real.rpow (offset + statistic) ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hbase_pos ((1 : ℝ) / 3)
    rw [inverse_rpow_step_size_def]
    calc
      numerator / Real.rpow (offset + statistic) ((1 : ℝ) / 3) ≤
          (Real.rpow (offset + statistic) ((1 : ℝ) / 3) / (4 * L)) /
            Real.rpow (offset + statistic) ((1 : ℝ) / 3) := by
        exact div_le_div_of_nonneg_right hnumerator_le (le_of_lt hden_pos)
      _ = (1 : ℝ) / (4 * L) := by
        field_simp [ne_of_gt hden_pos, ne_of_gt hfourL_pos]

-- Generalization plan (G0):
-- concept/name: unit upper bound for a quadratic momentum weight driven by an
--   inverse-cube-root step-size schedule; orig was
--   `theorem1_generated_nextMomentumWeight_le_one`, renamed to
--   `quadraticMomentumWeight_inverseRpowStepSize_le_one`
-- generality used: five real scalars for the coefficient, numerator, offset,
--   accumulated statistic, and positive scale; no carrier, measure,
--   convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: recursive-momentum and variance-reduced stochastic
--   gradient methods vary the coefficient, schedule numerator, stabilizing
--   offset, accumulated statistic, and scale while retaining the same
--   quadratic weight, inverse-cube-root schedule, and two cubic offset floors
-- counterargument checked: this is not a paper-local wrapper; the existing
--   schedule theorem uses only the first cubic floor, while this result also
--   converts the coefficient-dependent floor into the product bound needed to
--   control the quadratic momentum weight
-- coverage search: queries "quadratic momentum weight inverse cube root step
--   size upper bound from cubic offset lower bounds" and "coefficient times
--   inverse power step squared less than or equal one offset cube" found
--   `inverse_rpow_step_size_one_third_le_one_div_four_mul` as partial coverage
--   and no theorem with the compound conclusion; Mathlib semantic search found
--   unrelated mean inequalities and no adaptive-schedule result
-- minimal hypotheses: positivity of the coefficient, numerator, and scale and
--   nonnegativity of the accumulated statistic are the pointwise scalar facts
--   used; both cubic bounds are stated directly on the offset

/-- A quadratic momentum weight from a one-third inverse real-power step size
is at most one when its offset dominates the two controlling cubes.

Layer: Model | Gap: Level 0 (inverse-cube-root quadratic momentum stability bound)
Proof: use the first cubic offset floor to bound the step size by `1 / (4 * L)`, use the coefficient-dependent floor to bound `c * step` by `4 * L`, and multiply the two inequalities.
Source: Mathlib `Real.le_rpow_inv_iff_of_pos` and ordered-field multiplication and division APIs, composed with SOptLib inverse real-power step-size and quadratic momentum definitions
Used in: recursive-momentum and variance-reduced stochastic-gradient stability proofs showing that one minus the generated momentum weight is nonnegative
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/parameters/2/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem quadraticMomentumWeight_inverseRpowStepSize_le_one
    (c numerator offset statistic L : ℝ)
    (hc : 0 < c) (hnumerator : 0 < numerator) (hL : 0 < L)
    (hstatistic : 0 ≤ statistic)
    (hoffset_four : (4 * L * numerator) ^ 3 ≤ offset)
    (hoffset_coefficient : (c * numerator / (4 * L)) ^ 3 ≤ offset) :
    quadraticMomentumWeight c
        (inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3)) ≤ 1 := by
  have hfourL_pos : 0 < 4 * L := by positivity
  have hfourLNumerator_pos : 0 < 4 * L * numerator := by positivity
  have hoffset_pos : 0 < offset :=
    lt_of_lt_of_le (pow_pos hfourLNumerator_pos 3) hoffset_four
  have hbase_pos : 0 < offset + statistic :=
    add_pos_of_pos_of_nonneg hoffset_pos hstatistic
  have hstep_pos :
      0 < inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3) :=
    inverse_rpow_step_size_pos_of_numerator_pos_of_base_pos
      numerator offset statistic ((1 : ℝ) / 3) hnumerator hbase_pos
  have hstep_le :
      inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3) ≤
        (1 : ℝ) / (4 * L) :=
    inverse_rpow_step_size_one_third_le_one_div_four_mul
      numerator offset statistic L hnumerator.le hL (by linarith)
  have hscaled_pos : 0 < c * numerator / (4 * L) := by positivity
  have hroot_inv :
      c * numerator / (4 * L) ≤
        Real.rpow (offset + statistic) ((3 : ℝ)⁻¹) := by
    exact
      (Real.le_rpow_inv_iff_of_pos
        hscaled_pos.le hbase_pos.le (by norm_num : (0 : ℝ) < 3)).2
        (by
          simpa [one_div] using
            (show (c * numerator / (4 * L)) ^ 3 ≤ offset + statistic by
              linarith))
  have hroot :
      c * numerator / (4 * L) ≤
        Real.rpow (offset + statistic) ((1 : ℝ) / 3) := by
    simpa [one_div] using hroot_inv
  have hcoefficientNumerator_le :
      c * numerator ≤
        Real.rpow (offset + statistic) ((1 : ℝ) / 3) * (4 * L) :=
    (div_le_iff₀ hfourL_pos).1 hroot
  have hdenominator_pos :
      0 < Real.rpow (offset + statistic) ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hbase_pos ((1 : ℝ) / 3)
  have hcoefficientStep_le :
      c * inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3) ≤
        4 * L := by
    rw [inverse_rpow_step_size_def]
    field_simp [ne_of_gt hdenominator_pos]
    nlinarith [hcoefficientNumerator_le]
  calc
    quadraticMomentumWeight c
        (inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3)) =
        (c * inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3)) *
          inverse_rpow_step_size numerator offset statistic ((1 : ℝ) / 3) := by
      rw [quadraticMomentumWeight_def]
      ring
    _ ≤ (4 * L) * ((1 : ℝ) / (4 * L)) := by
      exact mul_le_mul hcoefficientStep_le hstep_le hstep_pos.le hfourL_pos.le
    _ = 1 := by
      field_simp [ne_of_gt hfourL_pos]

-- Generalization plan (G0):
-- concept/name: cube identity for an inverse-cube-root adaptive step-size
--   schedule; orig was `theorem1_stepsize_cube_eq`, renamed to
--   `inverse_rpow_step_size_cube`
-- generality used: three real scalars for the numerator, offset, and
--   accumulated statistic; no carrier, measure, convexity, smoothness,
--   oracle, filtration, integrability, or finite-dimensional assumptions
-- portable call pattern: recursive-momentum, AdaGrad-style, and adaptive
--   stochastic-gradient analyses vary the numerator, stabilizing offset, and
--   accumulated statistic while cubing the same inverse-cube-root schedule
-- counterargument checked: this is not merely paper traceability; although
--   Mathlib supplies the root identity, the theorem composes it with the named
--   adaptive schedule and quotient powers into the invariant used downstream
-- coverage search: `lean_search_symbols` queries for "inverse real power step
--   size cube equals numerator cubed divided by base nonnegative", "real rpow
--   inverse natural cast power nonnegative", and "division power quotient
--   denominator power" found no SOptLib schedule theorem; Mathlib's
--   `Real.rpow_inv_natCast_pow` covers only the denominator root identity
-- minimal hypotheses: nonnegativity of the shifted base is sufficient; the
--   source algorithm's strict positivity assumption is not needed

/-- Cubing a one-third inverse real-power step size gives the numerator cube
divided by its shifted base.

Layer: Model | Gap: Level 0 (inverse-cube-root adaptive step-size cube identity)
Proof: unfold the named schedule, distribute the cube over division, and evaluate the denominator with `Real.rpow_inv_natCast_pow` under shifted-base nonnegativity.
Source: Mathlib `Real.rpow_inv_natCast_pow` and real-field quotient power APIs
Used in: recursive-momentum, AdaGrad-style, and adaptive stochastic-gradient scalar estimates that replace a cubed inverse-cube-root step size by its accumulated-statistic denominator
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem inverse_rpow_step_size_cube
    (numerator offset accumulator : ℝ)
    (hbase : 0 ≤ offset + accumulator) :
    inverse_rpow_step_size numerator offset accumulator ((1 : ℝ) / 3) ^ 3 =
      numerator ^ 3 / (offset + accumulator) := by
  rw [inverse_rpow_step_size_def, div_pow]
  congr 1
  simpa [one_div] using
    (Real.rpow_inv_natCast_pow hbase (by norm_num : (3 : ℕ) ≠ 0))

end SOptLib

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: accelerated finite-window scalar step-condition predicate,
--   renamed away from the paper section label while retaining the genuine
--   accelerated-method role of the finite-window scalar contract.
-- generality used: real scalar schedules `alpha`, `beta`, `lam`, a positive-time
--   `Gamma` weight schedule, a scalar smoothness scale `L`, and a finite
--   natural horizon `N`; no carrier, measure, independence, integrability,
--   topology, norm, inner product, convexity, smoothness function, oracle, or
--   finite-dimensional hypotheses are used by the predicate itself.
-- portable call pattern: accelerated convex and nonconvex stochastic-gradient
--   finite-window accelerated analyses instantiate the four schedules and horizon, then reuse the
--   same monotone distance-telescope coefficient, noise absorption, and
--   gradient-weight lower-bound consequences.
-- counterargument checked: this is a hypothesis bundle, but not merely paper
--   traceability because the grouped facts are consumed as one stable scalar
--   contract by prefix restriction, distance telescoping, stopping-weight
--   positivity, noise absorption, and gradient coefficient estimates; Mathlib
--   has no accelerated-method schedule predicate with this shape.
-- coverage search: searched `accelerated step condition monotone coefficient
--   beta lambda gamma noise gradient weight lower bound`, `parameter choices
--   alpha beta lambda Gamma monotonicity stochastic accelerated`, and `finite
--   positive window prefix restriction bundled step size condition`; relevant
--   hits were `acceleratedParameterRelations`,
--   `AcceleratedVRScalarSideConditions`, positive-time step-size/window APIs,
--   and local private finite-window helpers, none of which packages this finite-window
--   ratio monotonicity plus beta/lambda absorption contract. LeanSearch for
--   real scalar monotone step-size coefficient bounds returned unrelated
--   order/convexity facts.
-- minimal hypotheses: all already minimal for the predicate; positivity of
--   `beta` is intentionally required only by the gradient-coefficient theorem,
--   not bundled into the finite-window scalar step condition.

/-- Finite-window scalar step-condition contract for accelerated finite-window scalar bounds.

The predicate packages monotonicity of the accelerated ratio
`alpha k / (lam k * Gamma k)`, the noise-absorption inequality
`alpha k * lam k <= L * beta k^2`, and the strict upper bound
`beta k < 1 / L` over the positive window `1, ..., N`.

Layer: Model | Concept: accelerated finite-window scalar step-condition
Proof: (definitional construction; bundled finite-window real scalar schedule
  conditions for accelerated finite-window scalar telescope and coefficient estimates)
Source: accelerated stochastic approximation parameter schedules and Mathlib
  ordered real-field quotient notation over subtype-indexed finite windows
Used in: randomized stochastic accelerated-gradient finite-window accelerated case
  telescope, stopping-weight positivity, noise absorption, and gradient
  coefficient lower-bound steps
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def AcceleratedFiniteWindowScalarStepCondition
    (alpha beta lam : ℕ → ℝ) (Gamma : {k : ℕ // 1 ≤ k} → ℝ)
    (L : ℝ) (N : ℕ) : Prop :=
  (∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, ∀ j : {t : ℕ // 1 ≤ t ∧ t ≤ N},
    k.1 + 1 = j.1 →
      alpha k.1 / (lam k.1 * Gamma ⟨k.1, k.2.1⟩) ≥
        alpha j.1 / (lam j.1 * Gamma ⟨j.1, j.2.1⟩)) ∧
  (∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N},
    alpha k.1 * lam k.1 ≤ L * beta k.1 ^ 2) ∧
  (∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, beta k.1 < 1 / L)

/-- The accelerated finite-window scalar step-condition predicate unfolds to its three
finite-window scalar schedule conditions.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar step-condition unfolding)
Proof: by rfl after unfolding `AcceleratedFiniteWindowScalarStepCondition`.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  ordered real-field quotient notation over subtype-indexed finite windows
Used in: exposing the randomized stochastic accelerated-gradient finite-window
  assumptions as monotone-ratio, noise-absorption, and beta-upper-bound facts
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
@[simp]
theorem AcceleratedFiniteWindowScalarStepCondition_def
    (alpha beta lam : ℕ → ℝ) (Gamma : {k : ℕ // 1 ≤ k} → ℝ)
    (L : ℝ) (N : ℕ) :
    AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N ↔
      (∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, ∀ j : {t : ℕ // 1 ≤ t ∧ t ≤ N},
        k.1 + 1 = j.1 →
          alpha k.1 / (lam k.1 * Gamma ⟨k.1, k.2.1⟩) ≥
            alpha j.1 / (lam j.1 * Gamma ⟨j.1, j.2.1⟩)) ∧
      (∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N},
        alpha k.1 * lam k.1 ≤ L * beta k.1 ^ 2) ∧
      (∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, beta k.1 < 1 / L) := by
  rfl

namespace AcceleratedFiniteWindowScalarStepCondition

/-- Build accelerated finite-window scalar step conditions from the monotone ratio,
noise-absorption, and beta upper-bound components.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar step-condition constructor)
Proof: package the three finite-window scalar schedule facts into the
  definitional conjunction.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  conjunction APIs
Used in: schedule-specialization proofs before randomized stochastic
  accelerated-gradient finite-window telescope and coefficient estimates
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem of_components
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N : ℕ}
    (hratio :
      ∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, ∀ j : {t : ℕ // 1 ≤ t ∧ t ≤ N},
        k.1 + 1 = j.1 →
          alpha k.1 / (lam k.1 * Gamma ⟨k.1, k.2.1⟩) ≥
            alpha j.1 / (lam j.1 * Gamma ⟨j.1, j.2.1⟩))
    (hnoise :
      ∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N},
        alpha k.1 * lam k.1 ≤ L * beta k.1 ^ 2)
    (hbeta :
      ∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, beta k.1 < 1 / L) :
    AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N :=
  ⟨hratio, hnoise, hbeta⟩

/-- The ratio monotonicity component of accelerated finite-window scalar step conditions.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar ratio projection)
Proof: unfold the scalar contract and take the first conjunct.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  conjunction APIs
Used in: randomized stochastic accelerated-gradient finite-window squared-distance
  telescope where adjacent coefficient monotonicity is required
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem ratio_mono
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N : ℕ}
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N) :
    ∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, ∀ j : {t : ℕ // 1 ≤ t ∧ t ≤ N},
      k.1 + 1 = j.1 →
        alpha k.1 / (lam k.1 * Gamma ⟨k.1, k.2.1⟩) ≥
          alpha j.1 / (lam j.1 * Gamma ⟨j.1, j.2.1⟩) :=
  h.1

/-- The noise-absorption component of accelerated finite-window scalar step conditions.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar noise projection)
Proof: unfold the scalar contract and take the second conjunct.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  conjunction APIs
Used in: randomized stochastic accelerated-gradient finite-window replacement of the
  one-step noise coefficient by `L * beta_k^2`
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem noise_absorption
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N : ℕ}
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N) :
    ∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N},
      alpha k.1 * lam k.1 ≤ L * beta k.1 ^ 2 :=
  h.2.1

/-- The beta upper-bound component of accelerated finite-window scalar step conditions.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar beta upper-bound projection)
Proof: unfold the scalar contract and take the final conjunct.
Source: accelerated stochastic approximation parameter schedules and Mathlib
  conjunction APIs
Used in: randomized stochastic accelerated-gradient finite-window stopping-weight
  positivity through the factor `1 - L * beta_k`
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem beta_lt_inv
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N : ℕ}
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N) :
    ∀ k : {t : ℕ // 1 ≤ t ∧ t ≤ N}, beta k.1 < 1 / L :=
  h.2.2

/-- Accelerated finite-window scalar step conditions restrict to any shorter positive prefix.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar prefix restriction)
Proof: coerce each shorter-window index into the longer window using the
  horizon inequality, then apply the three component facts.
Source: Mathlib subtype indexing and natural-number order transitivity APIs
Used in: randomized stochastic accelerated-gradient finite-window prefix arguments
  where a stopping index inherits the horizon-wide step conditions
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem restrict
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {K N : ℕ} (hKN : K ≤ N)
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N) :
    AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L K := by
  refine ⟨?_, ?_, ?_⟩
  · intro k j hsucc
    exact h.1
      ⟨k.1, k.2.1, le_trans k.2.2 hKN⟩
      ⟨j.1, j.2.1, le_trans j.2.2 hKN⟩
      hsucc
  · intro k
    exact h.2.1 ⟨k.1, k.2.1, le_trans k.2.2 hKN⟩
  · intro k
    exact h.2.2 ⟨k.1, k.2.1, le_trans k.2.2 hKN⟩

/-- The monotone ratio condition gives monotonicity of the half-scaled distance
telescope coefficient on adjacent positive times.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar half-ratio coefficient monotonicity)
Proof: instantiate the ratio monotonicity at adjacent window indices, multiply
  by the nonnegative scalar `1 / 2`, and rewrite the quotient shape.
Source: Mathlib ordered real-field arithmetic and subtype-indexed finite-window
  schedule ratios
Used in: randomized stochastic accelerated-gradient finite-window squared-distance
  telescope after introducing the coefficient `alpha_k / (2 * lam_k * Gamma_k)`
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem half_ratio_succ_le
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N n : ℕ}
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N)
    (hn : 1 ≤ n) (hnN : n < N) :
    alpha (n + 1) /
        (2 * lam (n + 1) *
          Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩) ≤
      alpha n / (2 * lam n * Gamma ⟨n, hn⟩) := by
  have hnN_le : n ≤ N := Nat.le_of_lt hnN
  have hn1_le_N : n + 1 ≤ N := hnN
  let k : {t : ℕ // 1 ≤ t ∧ t ≤ N} := ⟨n, hn, hnN_le⟩
  let j : {t : ℕ // 1 ≤ t ∧ t ≤ N} :=
    ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hn1_le_N⟩
  have hratio := h.1 k j (by rfl)
  have hscaled :
      (1 / 2) *
          (alpha (n + 1) /
            (lam (n + 1) *
              Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)) ≤
        (1 / 2) * (alpha n / (lam n * Gamma ⟨n, hn⟩)) :=
    mul_le_mul_of_nonneg_left hratio (by norm_num)
  calc
    alpha (n + 1) /
        (2 * lam (n + 1) *
          Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)
        =
      (1 / 2) *
        (alpha (n + 1) /
          (lam (n + 1) *
            Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)) := by
          ring
    _ ≤ (1 / 2) * (alpha n / (lam n * Gamma ⟨n, hn⟩)) := hscaled
    _ = alpha n / (2 * lam n * Gamma ⟨n, hn⟩) := by
          ring

/-- Accelerated finite-window scalar step conditions bound the averaged one-step noise
coefficient by `L * beta_k^2`.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar noise coefficient absorption)
Proof: use the bundled inequality `alpha_k * lam_k <= L * beta_k^2` and
  discharge the scalar average bound by ordered-ring arithmetic.
Source: Mathlib ordered real-ring arithmetic for scalar coefficient absorption
Used in: randomized stochastic accelerated-gradient finite-window one-step recurrence
  after combining stochastic-noise terms
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem noise_coeff_half_le_Lbeta_sq
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N : ℕ}
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N)
    (k : {t : ℕ // 1 ≤ t ∧ t ≤ N}) :
    (L * beta k.1 ^ 2 + alpha k.1 * lam k.1) / 2 ≤
      L * beta k.1 ^ 2 := by
  have hstep := h.2.1 k
  nlinarith

/-- Accelerated finite-window scalar step conditions lower-bound the one-step gradient
coefficient by the stopping-weight factor `beta_k * (1 - L * beta_k)`.

Layer: Model | Gap: Level 0 (accelerated finite-window scalar gradient coefficient lower bound)
Proof: use positivity of `beta_k` to clear the local quotient and combine the
  result with `alpha_k * lam_k <= L * beta_k^2` by ordered-field arithmetic.
Source: Mathlib ordered real-field arithmetic and denominator clearing APIs
Used in: randomized stochastic accelerated-gradient finite-window finite-sum
  replacement of raw gradient coefficients by stopping weights
Book citation: book/book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem gradient_coeff_weight_ge
    {alpha beta lam : ℕ → ℝ} {Gamma : {k : ℕ // 1 ≤ k} → ℝ}
    {L : ℝ} {N : ℕ}
    (h : AcceleratedFiniteWindowScalarStepCondition alpha beta lam Gamma L N)
    (k : {t : ℕ // 1 ≤ t ∧ t ≤ N}) (hbeta_pos : 0 < beta k.1) :
    beta k.1 *
        (1 - L * beta k.1 / 2 -
          alpha k.1 * lam k.1 / (2 * beta k.1)) ≥
      beta k.1 * (1 - L * beta k.1) := by
  have hstep := h.2.1 k
  have hbeta_ne : beta k.1 ≠ 0 := ne_of_gt hbeta_pos
  field_simp [hbeta_ne]
  nlinarith

end AcceleratedFiniteWindowScalarStepCondition

end SOptLib
