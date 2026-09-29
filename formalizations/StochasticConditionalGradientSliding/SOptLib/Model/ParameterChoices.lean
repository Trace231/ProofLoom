import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

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

end SOptLib
