import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import SOptLib.Model.Iterates

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

end ConditionalGradient

end SOptLib
