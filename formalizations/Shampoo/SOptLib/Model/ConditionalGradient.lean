import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import SOptLib.Model.Iterates
import SOptLib.Model.Objective

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open scoped BigOperators

namespace SOptLib

/-- A measurable linear-minimization oracle over a feasible set.

For each linear model vector `g`, the oracle selects a feasible point whose
inner product with `g` is minimal over the feasible set.  The bundled
measurability field is the extra data needed when the selected minimizer is
used inside stochastic-process and adaptedness arguments.

Layer: Model | Concept: Oracle
Proof: (definitional construction; bundled selector with feasibility, linear
  argmin certificate, and measurability)
Source: Conditional-gradient and Frank-Wolfe oracle model over real Hilbert spaces
Used in: stochastic conditional-gradient linear-oracle update and Wolfe-gap
  realization through a measurable nonunique selector
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
structure LinearMinimizationOracle
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    (X : Set E) where
  /-- Selected linear-oracle point as a function of the model vector. -/
  toFun : E → E
  /-- The selected linear-oracle point is feasible. -/
  mem : ∀ g : E, toFun g ∈ X
  /-- The selected point minimizes the linear model over the feasible set. -/
  is_argmin : ∀ g x : E, x ∈ X → ⟪g, toFun g⟫_ℝ ≤ ⟪g, x⟫_ℝ
  /-- The selected linear-oracle map is measurable. -/
  measurable : Measurable toFun

/-- Coerce a bundled linear-minimization oracle to its selector map.

Layer: Model | Gap: Level 0 (linear-minimization oracle coercion)
Proof: (definitional construction; expose the selector field as a function)
Source: Mathlib coercion API for bundled function-like structures
Used in: stochastic conditional-gradient update formulas that apply the linear
  oracle directly to a gradient estimator
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
instance linearMinimizationOracleCoeFun
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {X : Set E} : CoeFun (LinearMinimizationOracle E X) (fun _ => E → E) where
  coe := LinearMinimizationOracle.toFun

/-- State carried by a conditional-gradient recursion with a gradient estimator
and an epoch counter.

The field `x` stores the current iterate, `G` stores the current gradient or
gradient-estimator value, and `s` stores the current outer-loop or epoch counter.

Layer: Model | Concept: Iterates
Proof: (definitional construction; bundled conditional-gradient iterate,
  estimator, and epoch-counter state)
Source: conditional-gradient and variance-reduction algorithm-state notation
Used in: stochastic nonconvex conditional gradient epoch-refresh estimator recursion
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
structure ConditionalGradientState (P : Type*) (D : Type*) where
  x : P
  G : D
  s : ℕ

namespace ConditionalGradientState

variable {P D : Type*}

@[simp] theorem x_mk (x : P) (G : D) (s : ℕ) :
    (ConditionalGradientState.mk x G s).x = x := rfl

@[simp] theorem estimator_mk (x : P) (G : D) (s : ℕ) :
    (ConditionalGradientState.mk x G s).G = G := rfl

@[simp] theorem epoch_mk (x : P) (G : D) (s : ℕ) :
    (ConditionalGradientState.mk x G s).s = s := rfl

@[simp] theorem mk_eta (state : ConditionalGradientState P D) :
    ConditionalGradientState.mk state.x state.G state.s = state := by
  cases state
  rfl

end ConditionalGradientState

/-- Finite-sum conditional-gradient model data with component objectives,
smoothness-weighted component sampling, a measurable linear minimization oracle,
and stepsize/batch assumptions.

The structure packages the reusable assumptions needed before building a
finite-sum variance-reduced conditional-gradient estimator and its randomized
Wolfe-gap output.

Layer: Model | Concept: Oracle
Proof: (definitional construction; bundled finite-sum conditional-gradient
  model contract with component gradients, smoothness-proportional sampling,
  feasible-set geometry, an LMO, and schedule arithmetic)
Source: Frank-Wolfe conditional-gradient finite-sum models and importance
  sampling by component smoothness constants
Used in: finite-sum stochastic nonconvex conditional-gradient component
  sampling law before recursive estimator and output-law construction
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/key_lemmas/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
structure FiniteSumConditionalGradientSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E]
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- Compact feasible set. -/
  X : Set E
  /-- Initial feasible iterate. -/
  x₁ : E
  /-- Number of finite-sum components. -/
  componentCount : ℕ
  /-- Component objectives in `f(x) = n⁻¹ ∑ᵢ Fᵢ(x)`. -/
  Fcomp : Fin componentCount → E → ℝ
  /-- Component gradients `∇Fᵢ(x)`. -/
  gradFcomp : Fin componentCount → E → E
  /-- Component smoothness constants used to define the sampling law. -/
  componentL : Fin componentCount → ℝ
  /-- Smoothness constant equal to the average component smoothness. -/
  L : ℝ
  /-- Total number of iterations. -/
  N : ℕ
  /-- Epoch length. -/
  T : ℕ
  /-- Recursive mini-batch size. -/
  b : ℕ
  /-- Stepsize schedule. -/
  α : ℕ → ℝ
  /-- Component-index sample stream. -/
  sample : ℕ → Ω → Fin componentCount
  /-- Measurable linear minimization oracle over the feasible set. -/
  lmo : LinearMinimizationOracle E X
  /-- Coordinate measurability of the component-index sample stream. -/
  hsample_meas : ∀ k : ℕ, Measurable (sample k)
  /-- Probability measure for algorithmic sampling. -/
  P : Measure Ω
  /-- The sample-space measure is a probability measure. -/
  hP : IsProbabilityMeasure P
  /-- The feasible set is closed. -/
  hX_closed : IsClosed X
  /-- The feasible set is compact. -/
  hX_compact : IsCompact X
  /-- The feasible set is convex. -/
  hX_convex : Convex ℝ X
  /-- The initial point is feasible. -/
  hx₁_mem : x₁ ∈ X
  /-- There is at least one finite-sum component. -/
  hcomponentCount_pos : 1 ≤ componentCount
  /-- The average smoothness constant is positive. -/
  hL_pos : 0 < L
  /-- Component smoothness constants are positive. -/
  hcomponentL_pos : ∀ i : Fin componentCount, 0 < componentL i
  /-- The component smoothness constants sum to `componentCount * L`. -/
  hcomponentL_sum_eq : Finset.sum Finset.univ componentL = (componentCount : ℝ) * L
  /-- The output window is nonempty. -/
  hN_pos : 1 ≤ N
  /-- The recursive mini-batch is nonempty. -/
  hb_pos : 1 ≤ b
  /-- The epoch length is nonempty. -/
  hT_pos : 1 ≤ T
  /-- Each component gradient is the gradient of its component objective. -/
  hFcomp_hasGradientAt :
    ∀ i : Fin componentCount, ∀ x : E, x ∈ X →
      HasGradientAt (Fcomp i) (gradFcomp i x) x
  /-- Each finite-sum component has a Lipschitz gradient on feasible pairs. -/
  hFcomp_smooth :
    ∀ i : Fin componentCount, ∀ x y : E, x ∈ X → y ∈ X →
      ‖gradFcomp i x - gradFcomp i y‖ ≤ componentL i * ‖x - y‖
  /-- Component-index samples are independent across calls. -/
  hsample_iIndep : iIndepFun (β := fun _ => Fin componentCount) sample P
  /-- Each component-index sample has the smoothness-proportional law
  `q_i = L_i/(m L)`. -/
  hsample_componentQ :
    ∀ k, Measure.map (sample k) P =
      (PMF.ofFintypeOfReal
        (fun i : Fin componentCount => componentL i / ((componentCount : ℝ) * L))
        (by
          intro i
          exact div_nonneg (le_of_lt (hcomponentL_pos i))
            (mul_nonneg (Nat.cast_nonneg componentCount) (le_of_lt hL_pos)))
        (by
          have hden_ne : (componentCount : ℝ) * L ≠ 0 := by
            have hn_pos_nat : 0 < componentCount :=
              Nat.lt_of_lt_of_le Nat.zero_lt_one hcomponentCount_pos
            have hn_pos : 0 < (componentCount : ℝ) := by exact_mod_cast hn_pos_nat
            exact mul_ne_zero (ne_of_gt hn_pos) (ne_of_gt hL_pos)
          calc
            (∑ i : Fin componentCount, componentL i / ((componentCount : ℝ) * L))
                = (∑ i : Fin componentCount, componentL i) / ((componentCount : ℝ) * L) := by
                  rw [← Finset.sum_div]
            _ = 1 := by
                  rw [hcomponentL_sum_eq, div_self hden_ne])).toMeasure
  /-- Stepsizes are nonnegative throughout the schedule. -/
  hα_nonneg : ∀ k, 0 ≤ α k

/-- A nonempty compact feasible set admits a maximizer of every shifted
inner-product linear model.

For any base point `x` and model vector `G`, the affine objective
`y ↦ ⟪G, x - y⟫` attains its maximum on a compact nonempty feasible set `X`,
with the witness returned as an element of the feasible-set subtype.

Layer: Model | Gap: Level 1 (compact conditional-gradient linear-model maximizer)
Proof: build continuity of the shifted inner-product objective from Mathlib's
  continuous inner-product API, apply `IsCompact.exists_isMaxOn`, and rebuild
  the maximizing point as a feasible-set subtype.
Source: Mathlib compact extreme-value theorem and real inner-product continuity
  APIs
Used in: stochastic and finite-sum conditional-gradient Wolfe-surrogate
  maximizer existence before selecting a nonunique gap maximizer
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem exists_linearModelMaximizer_on_compact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (x G : E) :
    ∃ y : {y : E // y ∈ X},
      ∀ z : {z : E // z ∈ X},
        ⟪G, x - (z : E)⟫_ℝ ≤ ⟪G, x - (y : E)⟫_ℝ := by
  classical
  let φ : E → ℝ := fun y => ⟪G, x - y⟫_ℝ
  have hcont : ContinuousOn φ X := by
    exact (continuous_const.inner (continuous_const.sub continuous_id)).continuousOn
  obtain ⟨y, hyX, hymax⟩ := hX_compact.exists_isMaxOn hX_nonempty hcont
  refine ⟨⟨y, hyX⟩, ?_⟩
  intro z
  exact hymax z.property

/-- Snake-case compatibility spelling for compact shifted linear-model maximizers. -/
theorem exists_linear_model_maximizer_on_compact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (x G : E) :
    ∃ y : {y : E // y ∈ X},
    ∀ z : {z : E // z ∈ X},
      ⟪G, x - (z : E)⟫_ℝ ≤ ⟪G, x - (y : E)⟫_ℝ :=
  exists_linearModelMaximizer_on_compact hX_compact hX_nonempty x G

/-- Select a feasible maximizer of the shifted linear model on a nonempty compact
set.

For a compact nonempty feasible set `X`, base point `x`, and model vector `G`,
`compactLinearModelMaximizer hX_compact hX_nonempty x G` is a point of `X`
maximizing `y ↦ ⟪G, x - y⟫`.

Layer: Model | Concept: Conditional-gradient linear-model selector
Proof: (definitional construction; choose the feasible-set subtype witness
  supplied by compact shifted-linear-model attainment)
Source: Mathlib compact extreme-value theorem and real inner-product continuity
  APIs, via `SOptLib.exists_linearModelMaximizer_on_compact`
Used in: stochastic conditional-gradient sliding CndG subproblem point selection
  before proving Wolfe-surrogate gap and line-search identities
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
noncomputable def compactLinearModelMaximizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (x G : E) : E :=
  (Classical.choose (exists_linearModelMaximizer_on_compact hX_compact hX_nonempty x G)).1

/-- The compact linear-model maximizer selector unfolds to the chosen compact
attainment witness. -/
@[simp] theorem compactLinearModelMaximizer_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (x G : E) :
    compactLinearModelMaximizer hX_compact hX_nonempty x G =
      (Classical.choose
        (exists_linearModelMaximizer_on_compact hX_compact hX_nonempty x G)).1 := rfl

/-- The compact linear-model maximizer selector is feasible.

Layer: Model | Gap: Level 0 (compact linear-model selector feasibility)
Proof: project the subtype membership component from the witness chosen by
  `compactLinearModelMaximizer`.
Source: Mathlib compact extreme-value theorem and real inner-product continuity
  APIs, via `SOptLib.exists_linearModelMaximizer_on_compact`
Used in: stochastic conditional-gradient sliding CndG subproblem point selection
  before proving Wolfe-surrogate gap and line-search identities
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem compactLinearModelMaximizer_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (x G : E) :
    compactLinearModelMaximizer hX_compact hX_nonempty x G ∈ X := by
  classical
  exact (Classical.choose
    (exists_linearModelMaximizer_on_compact hX_compact hX_nonempty x G)).2

/-- The compact linear-model maximizer selector realizes the shifted linear
model maximum.

Layer: Model | Gap: Level 0 (compact linear-model selector maximality)
Proof: specialize the maximality certificate from the subtype witness chosen by
  `compactLinearModelMaximizer` to the queried feasible point.
Source: Mathlib compact extreme-value theorem and real inner-product continuity
  APIs, via `SOptLib.exists_linearModelMaximizer_on_compact`
Used in: stochastic conditional-gradient sliding CndG subproblem point selection
  before proving Wolfe-surrogate gap and line-search identities
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem compactLinearModelMaximizer_isMax
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (x G z : E) (hz : z ∈ X) :
    ⟪G, x - z⟫_ℝ ≤
      ⟪G, x - compactLinearModelMaximizer hX_compact hX_nonempty x G⟫_ℝ := by
  classical
  simpa [compactLinearModelMaximizer] using
    (Classical.choose_spec
      (exists_linearModelMaximizer_on_compact hX_compact hX_nonempty x G)) ⟨z, hz⟩

/-- The scalar quotient relation used for a conditional-gradient inner-loop
ceiling budget.

The witness `q` represents the partial quotient
`6 * beta * diameter ^ 2 / eta` by storing both the nonzero denominator
condition and the cross-multiplied value.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; partial real quotient relation for the
  Frank-Wolfe inner-loop ceiling numerator)
Source: conditional-gradient inner-loop complexity bounds and Mathlib ordered
  real-field scalar algebra
Used in: stochastic conditional-gradient sliding CndG inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def conditionalGradientInnerIterationBudgetScalar (beta eta diameter q : ℝ) : Prop :=
  eta ≠ 0 ∧ q * eta = 6 * beta * diameter ^ 2

/-- The conditional-gradient inner-loop budget scalar unfolds to its nonzero
denominator and cross-multiplied quotient value.

Layer: Model | Gap: Level 0 (conditional-gradient budget scalar definition)
Proof: by rfl after unfolding `conditionalGradientInnerIterationBudgetScalar`.
Source: conditional-gradient inner-loop complexity bounds and Mathlib ordered
  real-field scalar algebra
Used in: stochastic conditional-gradient sliding inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem conditionalGradientInnerIterationBudgetScalar_def (beta eta diameter q : ℝ) :
    conditionalGradientInnerIterationBudgetScalar beta eta diameter q ↔
      eta ≠ 0 ∧ q * eta = 6 * beta * diameter ^ 2 := by
  rfl

/-- The displayed quotient is a valid conditional-gradient inner-loop budget
scalar whenever the tolerance denominator is nonzero.

Layer: Model | Gap: Level 0 (conditional-gradient budget scalar construction)
Proof: cancel the nonzero denominator in the real quotient.
Source: conditional-gradient inner-loop complexity bounds and Mathlib ordered
  real-field scalar algebra
Used in: stochastic conditional-gradient sliding inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem conditionalGradientInnerIterationBudgetScalar_of_eta_ne_zero
    (beta diameter : ℝ) {eta : ℝ} (hη : eta ≠ 0) :
    conditionalGradientInnerIterationBudgetScalar beta eta diameter
      ((6 * beta * diameter ^ 2) / eta) := by
  refine ⟨hη, ?_⟩
  exact div_mul_cancel₀ (6 * beta * diameter ^ 2) hη

/-- Any witness for the conditional-gradient inner-loop budget scalar is the
corresponding displayed quotient.

Layer: Model | Gap: Level 0 (conditional-gradient budget scalar quotient value)
Proof: divide the cross-multiplied equality by the nonzero denominator.
Source: conditional-gradient inner-loop complexity bounds and Mathlib ordered
  real-field scalar algebra
Used in: stochastic conditional-gradient sliding inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem eq_div_of_conditionalGradientInnerIterationBudgetScalar
    {beta eta diameter q : ℝ}
    (h : conditionalGradientInnerIterationBudgetScalar beta eta diameter q) :
    q = (6 * beta * diameter ^ 2) / eta := by
  have hdiv := congrArg (fun x : ℝ => x / eta) h.2
  simpa [mul_div_cancel_right₀, h.1] using hdiv

/-- Conditional-gradient inner-loop natural budget obtained by ceiling the
partial scalar quotient.

The relation keeps the partial quotient witness explicit, so callers can use
the nonzero-denominator information carried by
`conditionalGradientInnerIterationBudgetScalar` while naming the natural
iteration budget used by the inner solver.

Layer: Model | Concept: ParameterChoices
Proof: (definitional construction; existential scalar quotient witness followed
  by a natural ceiling)
Source: conditional-gradient inner-loop complexity bounds and Mathlib natural
  ceiling API for real scalars
Used in: stochastic conditional-gradient sliding CndG inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def conditionalGradientInnerIterationBudget (beta eta diameter : ℝ) (T : ℕ) : Prop :=
  ∃ q : ℝ, conditionalGradientInnerIterationBudgetScalar beta eta diameter q ∧
    T = Nat.ceil q

/-- The conditional-gradient inner-loop budget unfolds to a scalar quotient
witness and a natural ceiling equality.

Layer: Model | Gap: Level 0 (conditional-gradient budget definition)
Proof: by rfl after unfolding `conditionalGradientInnerIterationBudget`.
Source: conditional-gradient inner-loop complexity bounds and Mathlib natural
  ceiling API for real scalars
Used in: stochastic conditional-gradient sliding CndG inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem conditionalGradientInnerIterationBudget_def (beta eta diameter : ℝ) (T : ℕ) :
    conditionalGradientInnerIterationBudget beta eta diameter T ↔
      ∃ q : ℝ, conditionalGradientInnerIterationBudgetScalar beta eta diameter q ∧
        T = Nat.ceil q := by
  rfl

/-- The displayed quotient supplies a conditional-gradient inner-loop budget
whenever the tolerance denominator is nonzero.

Layer: Model | Gap: Level 0 (conditional-gradient budget construction)
Proof: use the scalar quotient construction and record the requested ceiling
  equality.
Source: conditional-gradient inner-loop complexity bounds and Mathlib natural
  ceiling API for real scalars
Used in: stochastic conditional-gradient sliding CndG inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem conditionalGradientInnerIterationBudget_of_eta_ne_zero
    (beta diameter : ℝ) {eta : ℝ} {T : ℕ} (hη : eta ≠ 0)
    (hT : T = Nat.ceil ((6 * beta * diameter ^ 2) / eta)) :
    conditionalGradientInnerIterationBudget beta eta diameter T := by
  refine ⟨(6 * beta * diameter ^ 2) / eta, ?_, hT⟩
  exact conditionalGradientInnerIterationBudgetScalar_of_eta_ne_zero beta diameter hη

/-- Any conditional-gradient inner-loop budget is the ceiling of the displayed
quotient.

Layer: Model | Gap: Level 0 (conditional-gradient budget quotient value)
Proof: eliminate the scalar witness, identify it with the displayed quotient,
  and rewrite the recorded ceiling equality.
Source: conditional-gradient inner-loop complexity bounds and Mathlib natural
  ceiling API for real scalars
Used in: stochastic conditional-gradient sliding CndG inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem eq_ceil_div_of_conditionalGradientInnerIterationBudget
    {beta eta diameter : ℝ} {T : ℕ}
    (h : conditionalGradientInnerIterationBudget beta eta diameter T) :
    T = Nat.ceil ((6 * beta * diameter ^ 2) / eta) := by
  rcases h with ⟨q, hq, hT⟩
  calc
    T = Nat.ceil q := hT
    _ = Nat.ceil ((6 * beta * diameter ^ 2) / eta) := by
      rw [eq_div_of_conditionalGradientInnerIterationBudgetScalar hq]

/-- The conditional-gradient inner-loop budget relation is equivalent to the
nonzero tolerance denominator and the displayed quotient ceiling.

Layer: Model | Gap: Level 0 (conditional-gradient budget quotient iff)
Proof: one direction eliminates the scalar witness and rewrites by the quotient
  value theorem; the reverse direction constructs the scalar witness by division.
Source: conditional-gradient inner-loop complexity bounds, ordered real-field
  division, and Mathlib natural ceiling API
Used in: stochastic conditional-gradient sliding CndG inner-loop ceiling budget
  before proving the performed-update count bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem conditionalGradientInnerIterationBudget_iff
    {beta eta diameter : ℝ} {T : ℕ} :
    conditionalGradientInnerIterationBudget beta eta diameter T ↔
      eta ≠ 0 ∧ T = Nat.ceil ((6 * beta * diameter ^ 2) / eta) := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hT⟩
    refine ⟨hq.1, ?_⟩
    calc
      T = Nat.ceil q := hT
      _ = Nat.ceil ((6 * beta * diameter ^ 2) / eta) := by
        rw [eq_div_of_conditionalGradientInnerIterationBudgetScalar hq]
  · rintro ⟨hη, hT⟩
    exact conditionalGradientInnerIterationBudget_of_eta_ne_zero beta diameter hη hT

/-- First-stopping output relation for a gap-controlled iterate sequence.

`firstGapStoppingOutputRel gap iterate eta uplus` says that `uplus` is the
iterate at the first one-based time whose gap certificate is at most `eta`.

Layer: Model | Concept: Iterates
Proof: (definitional construction; existential first one-based stopping index
  tied to the selected iterate)
Source: conditional-gradient and approximate-projection while-loop output
  contracts over natural-number iterate sequences
Used in: stochastic conditional-gradient sliding CndG inner-loop output relation
  after the Wolfe-gap stopping test succeeds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def firstGapStoppingOutputRel {E : Type*} (gap : E -> ℝ) (iterate : ℕ -> E)
    (eta : ℝ) (uplus : E) : Prop :=
  ∃ t : ℕ,
    (1 ≤ t ∧ gap (iterate t) ≤ eta) ∧
      (∀ s : ℕ, 1 ≤ s -> s < t -> ¬ (1 ≤ s ∧ gap (iterate s) ≤ eta)) ∧
        uplus = iterate t

/-- The first-stopping output relation unfolds to a one-based first stopping
index, the gap test at that index, and equality with the returned iterate.

Layer: Model | Gap: Level 0 (first stopping output relation definition)
Proof: by rfl after unfolding `firstGapStoppingOutputRel`.
Source: conditional-gradient and approximate-projection while-loop output
  contracts over natural-number iterate sequences
Used in: stochastic conditional-gradient sliding CndG inner-loop output relation
  after the Wolfe-gap stopping test succeeds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem firstGapStoppingOutputRel_def {E : Type*} (gap : E -> ℝ) (iterate : ℕ -> E)
    (eta : ℝ) (uplus : E) :
    firstGapStoppingOutputRel gap iterate eta uplus ↔
      ∃ t : ℕ,
        (1 ≤ t ∧ gap (iterate t) ≤ eta) ∧
          (∀ s : ℕ, 1 ≤ s -> s < t -> ¬ (1 ≤ s ∧ gap (iterate s) ≤ eta)) ∧
            uplus = iterate t := by
  rfl

/-- A first-stopping output has a gap certificate bounded by the tolerance. -/
theorem firstGapStoppingOutputRel_gap_le {E : Type*} {gap : E -> ℝ}
    {iterate : ℕ -> E} {eta : ℝ} {uplus : E}
    (h : firstGapStoppingOutputRel gap iterate eta uplus) :
    gap uplus ≤ eta := by
  rcases h with ⟨t, ⟨_, ht_gap⟩, _, rfl⟩
  exact ht_gap

/-- Extract the witnessing first stopping index and its minimality certificate. -/
theorem firstGapStoppingOutputRel_exists_index {E : Type*} {gap : E -> ℝ}
    {iterate : ℕ -> E} {eta : ℝ} {uplus : E}
    (h : firstGapStoppingOutputRel gap iterate eta uplus) :
    ∃ t : ℕ,
      (1 ≤ t ∧ gap (iterate t) ≤ eta) ∧
        (∀ s : ℕ, 1 ≤ s -> s < t -> ¬ (1 ≤ s ∧ gap (iterate s) ≤ eta)) ∧
          uplus = iterate t := by
  exact h

/-- A nonempty compact feasible set admits a minimizer of every real inner-product
linear objective.

For any model vector `g`, the continuous objective `y ↦ ⟪g, y⟫` attains its
minimum on a compact nonempty feasible set `X`.

Layer: Model | Gap: Level 1 (compact linear-oracle minimizer existence)
Proof: build continuity of the inner-product linear objective from Mathlib's
  continuous inner-product API, then apply `IsCompact.exists_isMinOn`.
Source: Mathlib compact extreme-value theorem and real inner-product continuity
  APIs
Used in: stochastic conditional-gradient linear-minimization oracle existence
  before selecting a measurable nonunique oracle
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem linearMinimizer_exists_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty) (g : E) :
    ∃ y : E, y ∈ X ∧ ∀ x : E, x ∈ X → ⟪g, y⟫_ℝ ≤ ⟪g, x⟫_ℝ := by
  classical
  have hcont : ContinuousOn (fun y : E => ⟪g, y⟫_ℝ) X := by
    exact (continuous_const.inner continuous_id).continuousOn
  obtain ⟨y, hyX, hymin⟩ := hX_compact.exists_isMinOn hX_nonempty hcont
  exact ⟨y, hyX, fun x hx => hymin hx⟩

/-- Deterministic iterates that stop once a real-valued gap is below a tolerance.

Starting from `u0`, the successor state is the current state itself when
`gap u ≤ eta`; otherwise it is `move u`. This models the totalized recursion
behind early-stopped inner optimization solvers.

Layer: Model | Concept: Iterates
Proof: (definitional construction; primitive recursion with a gap-controlled
  terminal self-loop)
Source: conditional-gradient and approximate-projection while-loop iterate
  contracts over natural-number recursions
Used in: stochastic conditional-gradient sliding CndG inner-loop stopped
  recursion before the raw-descent transfer and first-gap output relation
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
noncomputable def gap_stopped_iterate {E : Type*} (gap : E → ℝ) (move : E → E)
    (eta : ℝ) (u0 : E) : ℕ → E :=
  Nat.rec u0 fun _ ut => if gap ut ≤ eta then ut else move ut

/-- The gap-stopped iterate is the primitive recursion with a terminal self-loop.

Layer: Model | Gap: Level 0 (gap-stopped iterate definition)
Proof: by rfl after unfolding `gap_stopped_iterate`.
Source: Mathlib natural-number primitive recursion and ordered-real gap tests
Used in: stochastic conditional-gradient sliding CndG inner-loop stopped
  recursion before the raw-descent transfer and first-gap output relation
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem gap_stopped_iterate_def {E : Type*} (gap : E → ℝ) (move : E → E)
    (eta : ℝ) (u0 : E) :
    gap_stopped_iterate gap move eta u0 =
      Nat.rec u0 (fun _ ut => if gap ut ≤ eta then ut else move ut) := by
  rfl

/-- The gap-stopped iterate starts from the supplied initial state.

Layer: Model | Gap: Level 0 (gap-stopped iterate initial value)
Proof: by rfl after unfolding `gap_stopped_iterate`.
Source: Mathlib natural-number primitive recursion and ordered-real gap tests
Used in: stochastic conditional-gradient sliding CndG inner-loop stopped
  recursion before the raw-descent transfer and first-gap output relation
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem gap_stopped_iterate_zero {E : Type*} (gap : E → ℝ) (move : E → E)
    (eta : ℝ) (u0 : E) :
    gap_stopped_iterate gap move eta u0 0 = u0 := by
  rfl

/-- A gap-stopped iterate either self-loops after a successful gap test or
applies the move map.

Layer: Model | Gap: Level 0 (gap-stopped iterate successor unfolding)
Proof: by rfl after unfolding `gap_stopped_iterate`.
Source: Mathlib natural-number primitive recursion and ordered-real gap tests
Used in: stochastic conditional-gradient sliding CndG inner-loop stopped
  recursion before the raw-descent transfer and first-gap output relation
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem gap_stopped_iterate_succ {E : Type*} (gap : E → ℝ) (move : E → E)
    (eta : ℝ) (u0 : E) (n : ℕ) :
    gap_stopped_iterate gap move eta u0 (n + 1) =
      let ut := gap_stopped_iterate gap move eta u0 n
      if gap ut ≤ eta then ut else move ut := by
  rfl

/-- If the gap test succeeds at an index, the next gap-stopped iterate self-loops.

Layer: Model | Gap: Level 1 (gap-stopped iterate stop branch)
Proof: unfold the successor equation and simplify with the successful gap test.
Source: Mathlib simplifier for conditional expressions over decidable propositions
Used in: early-stopped inner solvers when carrying the terminal state forward
  after a certificate has been found
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem gap_stopped_iterate_succ_of_gap_le {E : Type*} (gap : E → ℝ)
    (move : E → E) (eta : ℝ) (u0 : E) {n : ℕ}
    (hgap : gap (gap_stopped_iterate gap move eta u0 n) ≤ eta) :
    gap_stopped_iterate gap move eta u0 (n + 1) =
      gap_stopped_iterate gap move eta u0 n := by
  rw [gap_stopped_iterate_succ]
  exact if_pos hgap

/-- If the gap test fails at an index, the next gap-stopped iterate applies `move`.

Layer: Model | Gap: Level 1 (gap-stopped iterate move branch)
Proof: unfold the successor equation and simplify with the failed gap test.
Source: Mathlib simplifier for conditional expressions over decidable propositions
Used in: early-stopped inner solvers when matching the active update branch
  before a certificate has been found
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem gap_stopped_iterate_succ_of_not_gap_le {E : Type*} (gap : E → ℝ)
    (move : E → E) (eta : ℝ) (u0 : E) {n : ℕ}
    (hgap : ¬ gap (gap_stopped_iterate gap move eta u0 n) ≤ eta) :
    gap_stopped_iterate gap move eta u0 (n + 1) =
      move (gap_stopped_iterate gap move eta u0 n) := by
  rw [gap_stopped_iterate_succ]
  exact if_neg hgap

/-- Once the gap test succeeds, all later gap-stopped iterates stay at that state.

Layer: Model | Gap: Level 1 (gap-stopped iterate terminal self-loop)
Proof: induction on the number of additional successor steps, using the stop
  branch at each step.
Source: Mathlib natural-number induction and simplification of conditional
  recursions
Used in: downstream stopped-recursion proofs that need to replace later inner
  iterates by the first certified one
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem gap_stopped_iterate_eq_of_gap_le {E : Type*} (gap : E → ℝ)
    (move : E → E) (eta : ℝ) (u0 : E) {n : ℕ}
    (hgap : gap (gap_stopped_iterate gap move eta u0 n) ≤ eta) :
    ∀ k : ℕ,
      gap_stopped_iterate gap move eta u0 (n + k) =
        gap_stopped_iterate gap move eta u0 n
  | 0 => by simp
  | k + 1 => by
      rw [Nat.add_succ, gap_stopped_iterate_succ]
      have hcurrent :
          gap (gap_stopped_iterate gap move eta u0 (n + k)) ≤ eta := by
        simpa [gap_stopped_iterate_eq_of_gap_le gap move eta u0 hgap k] using hgap
      exact (if_pos hcurrent).trans
        (gap_stopped_iterate_eq_of_gap_le gap move eta u0 hgap k)

/-- An approximate conditional-gradient update certificate.

The returned point is feasible, and its prox-linear residual has inner product
at most `eta` against every feasible comparison direction.

Layer: Model | Concept: Conditional-gradient update certificate
Proof: (definitional construction; feasible returned point bundled with the
  approximate prox-linear variational inequality)
Source: Frank-Wolfe and conditional-gradient approximate oracle optimality
  conditions over real inner-product spaces
Used in: stochastic conditional-gradient sliding inner-loop output before
  projected-gradient comparison and descent estimates
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
def IsApproxConditionalGradientUpdate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (G x : E) (gamma eta : ℝ) (y : E) : Prop :=
  y ∈ X ∧ ∀ z : E, z ∈ X →
    ⟪G + gamma⁻¹ • (y - x), y - z⟫_ℝ ≤ eta

/-- The approximate conditional-gradient update certificate unfolds to
feasibility and its variational inequality.

Layer: Model | Gap: Level 0 (approximate conditional-gradient update unfolding)
Proof: by rfl after unfolding `IsApproxConditionalGradientUpdate`.
Source: Frank-Wolfe and conditional-gradient approximate oracle optimality
  conditions over real inner-product spaces
Used in: stochastic conditional-gradient sliding inner-loop output before
  projected-gradient comparison and descent estimates
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem IsApproxConditionalGradientUpdate_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (G x : E) (gamma eta : ℝ) (y : E) :
    IsApproxConditionalGradientUpdate X G x gamma eta y ↔
      y ∈ X ∧ ∀ z : E, z ∈ X →
        ⟪G + gamma⁻¹ • (y - x), y - z⟫_ℝ ≤ eta := by
  rfl

/-- Any positive-time gap witness yields a first positive-time gap witness.

For a natural-time sequence of ordered gap certificates, existence of some
one-based index with `gap t ≤ eta` is enough to choose the first such index and
record that no earlier one-based index satisfies the same stopping test.

Layer: Model | Gap: Level 0 (one-based first gap stopping index)
Proof: define the one-based stopping predicate and apply Mathlib's `Nat.find`
  least-witness API; `Nat.find_spec` gives the hit and `Nat.find_min'` gives
  exclusion of earlier hits.
Source: Mathlib natural-number least witness API for decidable predicates
Used in: stochastic conditional-gradient sliding CndG inner-loop termination
  after deriving an arbitrary Wolfe-gap stopping witness
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem exists_first_gap_stop_of_exists_gap_stop
    {R : Type*} [LE R] (gap : ℕ → R) (eta : R)
    (hstop : ∃ t : ℕ, 1 ≤ t ∧ gap t ≤ eta) :
    ∃ t : ℕ, (1 ≤ t ∧ gap t ≤ eta) ∧
      ∀ s : ℕ, 1 ≤ s → s < t → ¬ (1 ≤ s ∧ gap s ≤ eta) := by
  classical
  let P : ℕ → Prop := fun t => 1 ≤ t ∧ gap t ≤ eta
  let t0 : ℕ := Nat.find hstop
  have ht0 : P t0 := by
    simpa [P, t0] using Nat.find_spec hstop
  refine ⟨t0, ht0, ?_⟩
  intro s _hs hslt hsP
  exact (not_le.mpr hslt) (Nat.find_min' hstop hsP)

namespace ConditionalGradient

/-- The attained Wolfe gap for a chosen feasible maximizer selector.

Given a feasible-set subtype selector `maximizer`, this is the
conditional-gradient Wolfe stationarity certificate `⟪grad x, x - y⟫`
evaluated at `y = maximizer x`.

Layer: Model | Concept: Objective
Proof: (definitional construction; shifted gradient inner-product value at a
  selected feasible maximizer)
Source: Conditional-gradient and Frank-Wolfe Wolfe-gap stationarity
  certificates over real Hilbert spaces
Used in: stochastic and finite-sum conditional-gradient expected Wolfe-gap
  certificates after selecting a compact feasible-set maximizer
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def wolfeGap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (grad : E → E) (maximizer : E → {y : E // y ∈ X})
    (x : E) : ℝ :=
  ⟪grad x, x - (maximizer x : E)⟫_ℝ

/-- The selected-maximizer Wolfe gap unfolds to its shifted gradient
inner-product formula.

Layer: Model | Gap: Level 0 (selected Wolfe-gap value expansion)
Proof: by rfl after unfolding `wolfeGap`.
Source: Conditional-gradient Wolfe-gap notation and Mathlib real inner-product
  syntax
Used in: stochastic conditional-gradient Wolfe-gap algebra after naming the
  selected feasible maximizer value
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp] theorem wolfeGap_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (grad : E → E) (maximizer : E → {y : E // y ∈ X})
    (x : E) :
    wolfeGap grad maximizer x = ⟪grad x, x - (maximizer x : E)⟫_ℝ := by
  rfl

/-- The attained shifted linear model value for a chosen feasible maximizer selector.

Given a selector `maximizer x G` over the feasible-set subtype, this is the
linearized conditional-gradient model `⟪G, x - y⟫` evaluated at the selected
feasible point.

Layer: Model | Concept: Conditional-gradient max-linear model
Proof: definition by the selected shifted inner-product value.
Source: Frank-Wolfe conditional-gradient linear model over a feasible set
Used in: stochastic nonconvex conditional-gradient descent comparisons
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def maxLinearModel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (maximizer : E → E → {y : E // y ∈ X}) (x G : E) : ℝ :=
  ⟪G, x - (maximizer x G : E)⟫_ℝ

/-- The selected shifted linear model unfolds to its inner-product value.

Layer: Model | Concept: Conditional-gradient max-linear model
Proof: by rfl after unfolding `maxLinearModel`.
Source: Frank-Wolfe conditional-gradient linear model over a feasible set
Used in: stochastic nonconvex conditional-gradient descent comparisons
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp] theorem maxLinearModel_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (maximizer : E → E → {y : E // y ∈ X}) (x G : E) :
    maxLinearModel maximizer x G = ⟪G, x - (maximizer x G : E)⟫_ℝ := by
  rfl

/-- A selected Wolfe-gap maximizer has the same value as the linear
minimization oracle.

If `maximizer x` realizes the maximum of `y ↦ ⟪grad x, x - y⟫` over the
feasible set, and `lmo` minimizes `y ↦ ⟪grad x, y⟫` over the same set, then
both selectors realize the same Wolfe-gap value at `x`.

Layer: Model | Gap: Level 1 (Wolfe gap realization by linear minimization oracle)
Proof: compare the selected maximizer with the LMO point in both directions:
  the LMO argmin certificate gives the upper bound after expanding
  `inner_sub_right`, while the Wolfe-maximizer certificate gives the lower
  bound; antisymmetry closes the equality.
Source: Frank-Wolfe conditional-gradient linear-oracle calculus and Mathlib
  real inner-product subtraction algebra
Used in: stochastic conditional-gradient Wolfe-gap measurability and
  integrability through the measurable LMO selector
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem wolfeGap_eq_linearMinimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {X : Set E} (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (linearMinimizer : E → E)
    (linearMinimizer_mem : ∀ g : E, linearMinimizer g ∈ X)
    (linearMinimizer_is_argmin :
      ∀ g z : E, z ∈ X → ⟪g, linearMinimizer g⟫_ℝ ≤ ⟪g, z⟫_ℝ)
    (hmax : ∀ x : E, ∀ z : {z : E // z ∈ X},
      ⟪grad x, x - (z : E)⟫_ℝ ≤ ⟪grad x, x - (maximizer x : E)⟫_ℝ)
    (x : E) :
    wolfeGap grad maximizer x = ⟪grad x, x - linearMinimizer (grad x)⟫_ℝ := by
  classical
  let y : {y : E // y ∈ X} := ⟨linearMinimizer (grad x), linearMinimizer_mem (grad x)⟩
  let z : {z : E // z ∈ X} := maximizer x
  have hle_lmo :
      ⟪grad x, linearMinimizer (grad x)⟫_ℝ ≤ ⟪grad x, (z : E)⟫_ℝ :=
    linearMinimizer_is_argmin (grad x) (z : E) z.property
  have hgap_le :
      wolfeGap grad maximizer x ≤ ⟪grad x, x - linearMinimizer (grad x)⟫_ℝ := by
    have hvalue : wolfeGap grad maximizer x = ⟪grad x, x - (z : E)⟫_ℝ := by
      simp [wolfeGap, z]
    rw [hvalue]
    rw [inner_sub_right, inner_sub_right]
    linarith
  have hlmo_le :
      ⟪grad x, x - linearMinimizer (grad x)⟫_ℝ ≤ wolfeGap grad maximizer x := by
    simpa [wolfeGap, y] using hmax x y
  exact le_antisymm hgap_le hlmo_le

/-- LMO-bundled form of `wolfeGap_eq_linearMinimizer`. -/
theorem wolfeGap_eq_linearMinimizationOracle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {X : Set E} (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (lmo : LinearMinimizationOracle E X)
    (hmax : ∀ x : E, ∀ z : {z : E // z ∈ X},
      ⟪grad x, x - (z : E)⟫_ℝ ≤ ⟪grad x, x - (maximizer x : E)⟫_ℝ)
    (x : E) :
    wolfeGap grad maximizer x = ⟪grad x, x - lmo (grad x)⟫_ℝ :=
  wolfeGap_eq_linearMinimizer grad maximizer (fun g => lmo g) lmo.mem lmo.is_argmin hmax x

/-- Every feasible linearized gap is bounded by the selected Wolfe gap.

Given an existence certificate for a maximizer of
`z ↦ ⟪grad x, x - z⟫` on the feasible set, the `wolfeGap` value formed from
the classically selected maximizer dominates every feasible linearized gap.

Layer: Model | Gap: Level 0 (selected Wolfe-gap upper-bound spec)
Proof: apply `Classical.choose_spec` to the attained-maximizer certificate and
  fold the selected inner-product value back into `wolfeGap`.
Source: Frank-Wolfe conditional-gradient Wolfe-gap stationarity certificates
  and Mathlib subtype-valued classical choice
Used in: stochastic and finite-sum conditional-gradient proofs after selecting
  a compact feasible-set maximizer for the Wolfe stationarity gap
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem le_wolfeGap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (grad : E → E)
    (hmax_exists : ∀ x : E, ∃ y : {y : E // y ∈ X},
      ∀ z : {z : E // z ∈ X},
        ⟪grad x, x - (z : E)⟫_ℝ ≤ ⟪grad x, x - (y : E)⟫_ℝ)
    (x : E) (z : {z : E // z ∈ X}) :
    ⟪grad x, x - (z : E)⟫_ℝ ≤
      wolfeGap grad (fun x => Classical.choose (hmax_exists x)) x := by
  classical
  simpa [wolfeGap] using (Classical.choose_spec (hmax_exists x) z)

/-- A conditional-gradient segment line-search objective attains a minimum on
`[0,1]`.

For any selected point `v`, the scalar objective obtained by restricting the
linear-plus-quadratic model to `(1 - α) • ut + α • v` has a minimizer on the
closed interval of admissible segment stepsizes.

Layer: Model | Gap: Level 1 (conditional-gradient segment line-search argmin)
Proof: prove continuity of the affine segment, the linear inner-product term,
  and the squared-distance quadratic term, then apply `IsCompact.exists_isMinOn`
  on `Set.Icc (0 : ℝ) 1`.
Source: Mathlib compact extreme-value theorem and real inner-product continuity
  APIs
Used in: stochastic conditional-gradient sliding inner line search before
  comparing the selected update against trial segment points
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem segment_linear_quadratic_stepsize_exists
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) (β : ℝ) (ut v : E) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1,
      ∀ a ∈ Set.Icc (0 : ℝ) 1,
        SOptLib.quadraticRegularizedObjectiveOn (X := (Set.univ : Set E))
            (fun y : {z : E // z ∈ (Set.univ : Set E)} => ⟪g, y.1⟫_ℝ)
            (β / 2) u ⟨(1 - α) • ut + α • v, by simp⟩ ≤
          SOptLib.quadraticRegularizedObjectiveOn (X := (Set.univ : Set E))
            (fun y : {z : E // z ∈ (Set.univ : Set E)} => ⟪g, y.1⟫_ℝ)
            (β / 2) u ⟨(1 - a) • ut + a • v, by simp⟩ := by
  classical
  let F : ℝ → ℝ := fun a =>
    SOptLib.quadraticRegularizedObjectiveOn (X := (Set.univ : Set E))
      (fun y : {z : E // z ∈ (Set.univ : Set E)} => ⟪g, y.1⟫_ℝ)
      (β / 2) u ⟨(1 - a) • ut + a • v, by simp⟩
  have hseg : Continuous (fun a : ℝ => (1 - a) • ut + a • v) := by
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hinner :
      Continuous (fun a : ℝ => ⟪g, (1 - a) • ut + a • v⟫_ℝ) := by
    exact continuous_const.inner hseg
  have hquad :
      Continuous (fun a : ℝ =>
        β / 2 * ‖(1 - a) • ut + a • v - u‖ ^ 2) := by
    exact continuous_const.mul (((hseg.sub continuous_const).norm).pow 2)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    have hcont_global : Continuous F := by
      dsimp [F]
      simpa [SOptLib.quadraticRegularizedObjectiveOn_def] using hinner.add hquad
    exact hcont_global.continuousOn
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨α, hα, hmin⟩ := (isCompact_Icc).exists_isMinOn hne hcont
  refine ⟨α, hα, ?_⟩
  intro a ha
  simpa [F] using hmin ha

/-- The canonical conditional-gradient line-search stepsize selected from a
compact interval argmin.

`segment_linear_quadratic_stepsize g u β ut v` chooses one minimizer of the
linear-plus-quadratic objective along the segment from the current point `ut`
to the selected point `v`, constrained to `0 ≤ α ≤ 1`.

Layer: Model | Concept: Objective line-search stepsize selector
Proof: (definitional construction; classical choice from compact interval
  existence of the segment line-search minimizer)
Source: Conditional-gradient and Frank-Wolfe line-search models over real
  inner-product spaces
Used in: stochastic conditional-gradient sliding inner update selection before
  line-search comparison and quotient-form derivations
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
noncomputable def segment_linear_quadratic_stepsize
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) (β : ℝ) (ut v : E) : ℝ :=
  Classical.choose (segment_linear_quadratic_stepsize_exists g u β ut v)

@[simp] theorem segment_linear_quadratic_stepsize_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) (β : ℝ) (ut v : E) :
    segment_linear_quadratic_stepsize g u β ut v =
      Classical.choose (segment_linear_quadratic_stepsize_exists g u β ut v) :=
  rfl

/-- The selected conditional-gradient line-search stepsize lies in `[0,1]`.

Layer: Model | Gap: Level 0 (conditional-gradient line-search stepsize
interval membership)
Proof: unwrap the classical-choice certificate from
  `segment_linear_quadratic_stepsize_exists`.
Source: Mathlib classical choice API for existential minimizers
Used in: stochastic conditional-gradient sliding segment feasibility of the
  selected inner update
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem segment_linear_quadratic_stepsize_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) (β : ℝ) (ut v : E) :
    segment_linear_quadratic_stepsize g u β ut v ∈ Set.Icc (0 : ℝ) 1 :=
  (Classical.choose_spec (segment_linear_quadratic_stepsize_exists g u β ut v)).1

/-- The selected conditional-gradient line-search stepsize minimizes the
linear-plus-quadratic segment objective over `[0,1]`.

Layer: Model | Gap: Level 0 (conditional-gradient line-search minimizer
certificate)
Proof: unwrap the minimizer component of the classical-choice certificate from
  `segment_linear_quadratic_stepsize_exists`.
Source: Mathlib classical choice API for compact interval minimizers
Used in: stochastic conditional-gradient sliding descent proof when comparing
  the selected update with arbitrary admissible trial steps
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem segment_linear_quadratic_stepsize_minimizes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) (β : ℝ) (ut v : E) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    SOptLib.quadraticRegularizedObjectiveOn (X := (Set.univ : Set E))
        (fun y : {z : E // z ∈ (Set.univ : Set E)} => ⟪g, y.1⟫_ℝ)
        (β / 2) u
        ⟨(1 - segment_linear_quadratic_stepsize g u β ut v) • ut +
          segment_linear_quadratic_stepsize g u β ut v • v, by simp⟩ ≤
      SOptLib.quadraticRegularizedObjectiveOn (X := (Set.univ : Set E))
        (fun y : {z : E // z ∈ (Set.univ : Set E)} => ⟪g, y.1⟫_ℝ)
        (β / 2) u ⟨(1 - a) • ut + a • v, by simp⟩ :=
  (Classical.choose_spec (segment_linear_quadratic_stepsize_exists g u β ut v)).2 a ha

/-- The closed-form clamped quotient stepsize for a segment quadratic line search.

For a linear model vector `G`, quadratic center `u`, curvature `beta`, current
point `ut`, and selected segment endpoint `vt`, this is the displayed scalar
`min 1 (numerator / denominator)` used before proving interval membership or
argmin certificates.

Layer: Model | Concept: Objective line-search stepsize selector
Proof: (definitional construction; clamped real quotient for a Hilbert-space
  segment quadratic model)
Source: Conditional-gradient and Frank-Wolfe closed-form line-search formulas
  over real inner-product spaces
Used in: stochastic conditional-gradient sliding inner update selection when
  the selected oracle endpoint is combined with the displayed quotient stepsize
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
noncomputable def closed_form_segment_quadratic_line_search
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G u : E) (beta : ℝ) (ut vt : E) : ℝ :=
  min 1 (⟪beta • (u - ut) - G, vt - ut⟫_ℝ / (beta * ‖vt - ut‖ ^ 2))

/-- The closed-form segment quadratic line search unfolds to its clamped quotient.

Layer: Model | Gap: Level 0 (closed-form segment line-search unfolding)
Proof: by rfl after unfolding `closed_form_segment_quadratic_line_search`.
Source: Conditional-gradient and Frank-Wolfe closed-form line-search formulas
  over real inner-product spaces
Used in: stochastic conditional-gradient sliding inner update selection when
  the displayed quotient is expanded for scalar quadratic comparison
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp] theorem closed_form_segment_quadratic_line_search_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G u : E) (beta : ℝ) (ut vt : E) :
    closed_form_segment_quadratic_line_search G u beta ut vt =
      min 1 (⟪beta • (u - ut) - G, vt - ut⟫_ℝ / (beta * ‖vt - ut‖ ^ 2)) :=
  rfl

/-- The closed-form clamped quotient line search lies in `[0,1]` whenever its
unclamped quotient is nonnegative.

Layer: Model | Gap: Level 0 (closed-form segment line-search interval
membership)
Proof: combine `0 ≤ min 1 q` from `0 ≤ q` with the upper clamp bound
`min 1 q ≤ 1`.
Source: Conditional-gradient and Frank-Wolfe closed-form line-search formulas
  over real inner-product spaces
Used in: stochastic conditional-gradient sliding segment feasibility when the
  displayed quotient is known to be nonnegative
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem closed_form_segment_quadratic_line_search_mem_Icc_of_quotient_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G u : E) (beta : ℝ) (ut vt : E)
    (hquot_nonneg :
      0 ≤ ⟪beta • (u - ut) - G, vt - ut⟫_ℝ / (beta * ‖vt - ut‖ ^ 2)) :
    closed_form_segment_quadratic_line_search G u beta ut vt ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simpa [closed_form_segment_quadratic_line_search] using
      le_min zero_le_one hquot_nonneg
  · change min (1 : ℝ)
        (⟪beta • (u - ut) - G, vt - ut⟫_ℝ / (beta * ‖vt - ut‖ ^ 2)) ≤ 1
    exact min_le_left (1 : ℝ)
      (⟪beta • (u - ut) - G, vt - ut⟫_ℝ / (beta * ‖vt - ut‖ ^ 2))

end ConditionalGradient

end SOptLib
