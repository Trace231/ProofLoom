-- SOptLib/Layer1/Descent.lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Model.Bregman
import SOptLib.Model.Budget
import SOptLib.Model.Filtration
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Iterates
import SOptLib.Model.StochasticOracle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Independence.Basic
import SOptLib.Model.Objective
import SOptLib.Model.SaddleGap
import SOptLib.Layer1.Proximal


open scoped BigOperators InnerProductSpace

/-- An accelerated upper-model step closes after the prox model and tail bound.

If an averaged iterate is bounded by a base term plus an alpha-scaled local
model and smoothness tail, the alpha-scaled local model is bounded by the
prox-model right hand side, and the remaining smoothness/Bregman/noise tail is
bounded by a stochastic error term, then the standard accelerated one-step
recurrence follows.

Layer: Layer1 | Gap: Level 1 (accelerated prox-model tail recurrence assembly)
Proof: substitute the prox-model inequality into the upper model, regroup the
  Bregman and noise terms, and insert the completed stochastic-error tail bound.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra and
  Mathlib ordered-ring arithmetic for real inequalities
Used in: stochastic accelerated gradient descent one-step recurrence after the
  prox Bregman estimate and stochastic-error completion square
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_delta_tail_bound_of_prox_and_bregman
    (value base alpha model smooth lowerModel vpart breg noise stochasticError : ℝ)
    (hUpper : value ≤ base + alpha * model + smooth)
    (hProxModel :
      alpha * model ≤ alpha * (lowerModel + vpart - breg + noise))
    (hTail : smooth - alpha * breg + alpha * noise ≤ stochasticError) :
    value ≤ base + alpha * lowerModel + alpha * vpart + stochasticError := by
  calc
    value ≤ base + alpha * model + smooth := hUpper
    _ ≤ base + alpha * (lowerModel + vpart - breg + noise) + smooth := by
      linarith
    _ = base + alpha * lowerModel + alpha * vpart +
          (smooth - alpha * breg + alpha * noise) := by
      ring
    _ ≤ base + alpha * lowerModel + alpha * vpart + stochasticError := by
      linarith

/-- Coordinate components of a recursive process transport to one-based positive time.

If the successor slice of a recursive process is given by a sample-kernel step,
and the step exposes named current-coordinate and averaged-coordinate
projections, then at any positive natural time `t` those projections agree with
the process at time `t`.  A derived query indexed by `natSuccPositiveTime (t-1)`
is transported at the same time.

Layer: Layer1 | Gap: Level 1 (recursive-process coordinate transport)
Proof: normalize `t - 1 + 1` to `t`, rewrite the successor state by the
  sample-kernel update, project both coordinates through the step equations, and
  unfold the positive-time predecessor used by the derived query.
Source: Mathlib natural-number subtraction, subtype indexing, and Pi-function
  extensionality APIs
Used in: stochastic accelerated gradient descent generated-process component
  transport before Bregman recurrence rewriting
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem recursive_process_components_at_nat_succ_positive_time
    {Ω State Sample X XBar Query : Type*}
    (process : ℕ → Ω → State)
    (sample : ℕ → Ω → Sample)
    (step : ℕ → State → Sample → State)
    (stateX : State → X) (stateXBar : State → XBar)
    (nextX : {n : ℕ // 1 ≤ n} → State → Sample → X)
    (nextXBar : {n : ℕ // 1 ≤ n} → State → X → XBar)
    (searchPoint : {n : ℕ // 1 ≤ n} → State → Query)
    (xUnder : {n : ℕ // 1 ≤ n} → Ω → Query)
    (h_succ :
      ∀ k : ℕ, process (k + 1) =
        fun ω => step k (process k ω) (sample (k + 1) ω))
    (h_step_x :
      ∀ k prev ξ,
        stateX (step k prev ξ) =
          nextX (SOptLib.natSuccPositiveTime k) prev ξ)
    (h_step_xBar :
      ∀ k prev ξ,
        stateXBar (step k prev ξ) =
          nextXBar (SOptLib.natSuccPositiveTime k) prev
            (nextX (SOptLib.natSuccPositiveTime k) prev ξ))
    (h_xUnder :
      ∀ τ ω, xUnder τ ω = searchPoint τ (process (τ.1 - 1) ω))
    (ω : Ω) (t : ℕ) (ht : 1 ≤ t) :
    let k : ℕ := t - 1
    let τ : {m : ℕ // 1 ≤ m} := SOptLib.natSuccPositiveTime k
    let prev : State := process k ω
    let ξ : Sample := sample τ.1 ω
    stateX (process t ω) = nextX τ prev ξ ∧
      stateXBar (process t ω) = nextXBar τ prev (nextX τ prev ξ) ∧
      searchPoint τ prev = xUnder τ ω := by
  classical
  let k : ℕ := t - 1
  let τ : {m : ℕ // 1 ≤ m} := SOptLib.natSuccPositiveTime k
  let prev : State := process k ω
  let ξ : Sample := sample τ.1 ω
  have hkadd : k + 1 = t := by
    dsimp [k]
    simpa using Nat.sub_add_cancel ht
  have hτval : τ.1 = k + 1 := by
    simp [τ, SOptLib.natSuccPositiveTime]
  have hsucc :
      process (k + 1) ω = step k (process k ω) (sample (k + 1) ω) := by
    simpa using congrFun (h_succ k) ω
  have hx_cur : stateX (process t ω) = nextX τ prev ξ := by
    rw [← hkadd]
    calc
      stateX (process (k + 1) ω) =
          stateX (step k (process k ω) (sample (k + 1) ω)) := by
        rw [hsucc]
      _ = nextX τ prev ξ := by
        simpa [prev, ξ, τ, hτval] using
          h_step_x k (process k ω) (sample (k + 1) ω)
  have hxbar_cur :
      stateXBar (process t ω) = nextXBar τ prev (nextX τ prev ξ) := by
    rw [← hkadd]
    calc
      stateXBar (process (k + 1) ω) =
          stateXBar (step k (process k ω) (sample (k + 1) ω)) := by
        rw [hsucc]
      _ = nextXBar τ prev (nextX τ prev ξ) := by
        simpa [prev, ξ, τ, hτval] using
          h_step_xBar k (process k ω) (sample (k + 1) ω)
  have hxunder_eq : searchPoint τ prev = xUnder τ ω := by
    have hidx : τ.1 - 1 = k := by
      simp [τ, SOptLib.natSuccPositiveTime]
    simpa [prev, hidx] using (h_xUnder τ ω).symm
  exact ⟨hx_cur, hxbar_cur, hxunder_eq⟩

/-- A positive-time raw Bregman recurrence transports to natural generated-process time.

If a raw one-step Bregman recurrence is available for the positive time
`natSuccPositiveTime (t - 1)`, and the current generated state, residual, and
auxiliary point agree with the raw step data, then the same recurrence holds in
natural-time process coordinates at `t`.

Layer: Layer1 | Gap: Level 1 (generated-process Bregman recurrence transport)
Proof: normalize the positive-time subtype value using `natSuccPositiveTime`,
  rewrite the current state, residual, and auxiliary-point coordinates, and
  close by the supplied raw recurrence.
Source: Mathlib natural-number subtraction, subtype indexing, and real
  inner-product ordered-ring APIs
Used in: stochastic accelerated gradient descent generated-process recurrence
  before finite-window Bregman telescoping
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem positive_time_bregman_recurrence_transport
    {E State Ω Sample : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (process : ℕ → Ω → State) (stateX stateXBar : State → E)
    (sample : ℕ → Ω → Sample)
    (rawXNext rawXBar rawXPlus rawDelta :
      {n : ℕ // 1 ≤ n} → State → Sample → E)
    (xPlus delta : {n : ℕ // 1 ≤ n} → Ω → E)
    (Psi : E → ℝ) (V : E → E → ℝ)
    (alpha gamma : ℕ → ℝ) (mu L M : ℝ) (xRef : E)
    (ω : Ω) (t : ℕ) (ht : 1 ≤ t)
    (hcurrX :
      rawXNext (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample ((t - 1) + 1) ω) =
        stateX (process t ω))
    (hcurrBar :
      rawXBar (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample ((t - 1) + 1) ω) =
        stateXBar (process t ω))
    (hxPlus :
      rawXPlus (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample ((t - 1) + 1) ω) =
        xPlus (SOptLib.natSuccPositiveTime (t - 1)) ω)
    (hdelta :
      rawDelta (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample ((t - 1) + 1) ω) =
        delta (SOptLib.natSuccPositiveTime (t - 1)) ω)
    (hraw :
      let τ : {n : ℕ // 1 ≤ n} := SOptLib.natSuccPositiveTime (t - 1)
      let prev : State := process (t - 1) ω
      let ξ : Sample := sample τ.1 ω
      Psi (rawXBar τ prev ξ) - Psi xRef ≤
        (1 - alpha τ.1) * (Psi (stateXBar prev) - Psi xRef) +
          alpha τ.1 / gamma τ.1 *
            (V (stateX prev) xRef -
              (1 + mu * gamma τ.1) * V (rawXNext τ prev ξ) xRef) +
          alpha τ.1 * gamma τ.1 * (M + ‖rawDelta τ prev ξ‖) ^ 2 /
            (2 * (1 + mu * gamma τ.1 - L * alpha τ.1 * gamma τ.1)) +
          alpha τ.1 * ⟪rawDelta τ prev ξ, xRef - rawXPlus τ prev ξ⟫_ℝ) :
    Psi (stateXBar (process t ω)) - Psi xRef ≤
      (1 - alpha t) * (Psi (stateXBar (process (t - 1) ω)) - Psi xRef) +
        alpha t / gamma t *
          (V (stateX (process (t - 1) ω)) xRef -
            (1 + mu * gamma t) * V (stateX (process t ω)) xRef) +
        alpha ((t - 1) + 1) * gamma ((t - 1) + 1) *
          (M + ‖delta (SOptLib.natSuccPositiveTime (t - 1)) ω‖) ^ 2 /
            (2 * (1 + mu * gamma ((t - 1) + 1) -
              L * alpha ((t - 1) + 1) * gamma ((t - 1) + 1))) +
        alpha ((t - 1) + 1) *
          ⟪delta (SOptLib.natSuccPositiveTime (t - 1)) ω,
            xRef - xPlus (SOptLib.natSuccPositiveTime (t - 1)) ω⟫_ℝ := by
  classical
  let k : ℕ := t - 1
  let τ : {n : ℕ // 1 ≤ n} := SOptLib.natSuccPositiveTime k
  have hkadd : k + 1 = t := by
    dsimp [k]
    simpa using Nat.sub_add_cancel ht
  have ht_sub_add : (t - 1) + 1 = t :=
    Nat.sub_add_cancel ht
  have hτval : τ.1 = t := by
    simp [τ, hkadd]
  have hcurrX_t :
      rawXNext (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample t ω) =
        stateX (process t ω) := by
    simpa [ht_sub_add] using hcurrX
  have hcurrBar_t :
      rawXBar (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample t ω) =
        stateXBar (process t ω) := by
    simpa [ht_sub_add] using hcurrBar
  have hxPlus_t :
      rawXPlus (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample t ω) =
        xPlus (SOptLib.natSuccPositiveTime (t - 1)) ω := by
    simpa [ht_sub_add] using hxPlus
  have hdelta_t :
      rawDelta (SOptLib.natSuccPositiveTime (t - 1)) (process (t - 1) ω)
          (sample t ω) =
        delta (SOptLib.natSuccPositiveTime (t - 1)) ω := by
    simpa [ht_sub_add] using hdelta
  simpa [k, τ, hτval, hkadd, hcurrX_t, hcurrBar_t, hxPlus_t, hdelta_t] using hraw

/-- One-step mirror descent pathwise descent from a subgradient inequality, a
three-point mirror inequality, a residual Bregman lower bound, and a norm bound on
the deterministic oracle component.
Layer: Layer1 | Gap: Level 1 (pathwise mirror descent algebra)
Proof: split the oracle term into deterministic and residual components, use the
  three-point inequality, and control the residual step with Young's inequality and
  the oracle magnitude bound.
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  proof of Theorem 4.1
Used in: stochastic mirror descent one-step pathwise bounds
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem mirrorDescent_oneStep_pathwise_of_residual_lower_bound
    {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : X → ℝ) (V : X → X → ℝ) (point : X → E)
    (x xNext xRef : X) (G g δ : E) (γ M : ℝ)
    (hγpos : 0 < γ)
    (hsub : f xRef ≥ f x + ⟪g, point xRef - point x⟫_ℝ)
    (hthree :
      γ * ⟪G, point xNext - point xRef⟫_ℝ + V x xNext ≤
        V x xRef - V xNext xRef)
    (hVlower :
      (1 / 2 : ℝ) * ‖point x - point xNext‖ ^ 2 ≤ V x xNext)
    (hdecomp : G = g + δ)
    (hgbound : ‖g‖ ≤ M) :
    γ * (f x - f xRef) ≤
      V x xRef - V xNext xRef + γ ^ 2 * (M ^ 2 + ‖δ‖ ^ 2) -
        γ * ⟪δ, point x - point xRef⟫_ℝ := by
  have hconv_step :
      γ * (f x - f xRef) ≤ γ * ⟪g, point x - point xRef⟫_ℝ := by
    have hbase : f x - f xRef ≤ ⟪g, point x - point xRef⟫_ℝ := by
      have hneg :
          -⟪g, point xRef - point x⟫_ℝ =
            ⟪g, point x - point xRef⟫_ℝ := by
        have hvec : point x - point xRef = -(point xRef - point x) := by
          abel
        rw [hvec, inner_neg_right]
      linarith
    exact mul_le_mul_of_nonneg_left hbase (le_of_lt hγpos)
  have hgt_decomp :
      ⟪g, point x - point xRef⟫_ℝ =
        ⟪G, point x - point xRef⟫_ℝ -
          ⟪δ, point x - point xRef⟫_ℝ := by
    have hg : g = G - δ := by
      rw [hdecomp]
      abel
    rw [hg, inner_sub_left]
  have hsplit :
      ⟪G, point x - point xRef⟫_ℝ =
        ⟪G, point x - point xNext⟫_ℝ +
          ⟪G, point xNext - point xRef⟫_ℝ := by
    have hvec :
        point x - point xRef =
          (point x - point xNext) + (point xNext - point xRef) := by
      abel
    rw [hvec, inner_add_right]
  have hresidual :
      γ * ⟪G, point x - point xNext⟫_ℝ - V x xNext ≤
        γ ^ 2 * (M ^ 2 + ‖δ‖ ^ 2) := by
    have hinner_norm :
        ⟪G, point x - point xNext⟫_ℝ ≤ ‖G‖ * ‖point x - point xNext‖ :=
      real_inner_le_norm G (point x - point xNext)
    have hγinner :
        γ * ⟪G, point x - point xNext⟫_ℝ ≤
          γ * (‖G‖ * ‖point x - point xNext‖) :=
      mul_le_mul_of_nonneg_left hinner_norm (le_of_lt hγpos)
    have hyoung :
        γ * (‖G‖ * ‖point x - point xNext‖) -
            (1 / 2 : ℝ) * ‖point x - point xNext‖ ^ 2 ≤
          (1 / 2 : ℝ) * γ ^ 2 * ‖G‖ ^ 2 := by
      nlinarith [sq_nonneg (γ * ‖G‖ - ‖point x - point xNext‖)]
    have hVreplace :
        γ * ⟪G, point x - point xNext⟫_ℝ - V x xNext ≤
          γ * (‖G‖ * ‖point x - point xNext‖) -
            (1 / 2 : ℝ) * ‖point x - point xNext‖ ^ 2 := by
      nlinarith [hγinner, hVlower]
    have hGbound :
        ‖G‖ ^ 2 ≤ 2 * (M ^ 2 + ‖δ‖ ^ 2) :=
      norm_sq_le_two_mul_sq_add_sq_of_eq_add_of_norm_le G g δ M hdecomp hgbound
    have hhalf :
        (1 / 2 : ℝ) * γ ^ 2 * ‖G‖ ^ 2 ≤
          γ ^ 2 * (M ^ 2 + ‖δ‖ ^ 2) := by
      have hγsq : 0 ≤ γ ^ 2 := sq_nonneg γ
      nlinarith
    nlinarith
  calc
    γ * (f x - f xRef)
        ≤ γ * ⟪g, point x - point xRef⟫_ℝ := hconv_step
    _ = γ * ⟪G, point x - point xRef⟫_ℝ -
          γ * ⟪δ, point x - point xRef⟫_ℝ := by
        rw [hgt_decomp]
        ring
    _ = (γ * ⟪G, point x - point xNext⟫_ℝ - V x xNext) +
          (γ * ⟪G, point xNext - point xRef⟫_ℝ + V x xNext) -
          γ * ⟪δ, point x - point xRef⟫_ℝ := by
        rw [hsplit]
        ring
    _ ≤ γ ^ 2 * (M ^ 2 + ‖δ‖ ^ 2) +
          (V x xRef - V xNext xRef) -
          γ * ⟪δ, point x - point xRef⟫_ℝ := by
        nlinarith
    _ = V x xRef - V xNext xRef +
          γ ^ 2 * (M ^ 2 + ‖δ‖ ^ 2) -
          γ * ⟪δ, point x - point xRef⟫_ℝ := by
        ring

/-- One-step mirror descent pathwise descent from a carrier-wide Bregman lower bound.

If the mirror descent three-point inequality holds, `G` decomposes as `g + δ`,
the subgradient inequality is available at `xRef`, and the Bregman residual
dominates the squared point distance on the whole carrier, then the standard
one-step pathwise SMD descent inequality follows.

Layer: Layer1 | Gap: Level 1 (all-carrier Bregman lower-bound discharge)
Proof: specialize the global Bregman lower bound to `(x, xNext)` and invoke the
  residual-lower-bound one-step pathwise descent theorem.
Source: Lan Chapter 4 mirror descent one-step analysis
Used in: stochastic mirror descent one-step bound with boundary-safe Bregman facts
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem mirrorDescent_oneStep_pathwise_of_all_carrier_lower_bound
    {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : X → ℝ) (V : X → X → ℝ) (point : X → E)
    (x xNext xRef : X) (G g δ : E) (γ M : ℝ)
    (hγpos : 0 < γ)
    (hsub : f xRef ≥ f x + ⟪g, point xRef - point x⟫_ℝ)
    (hthree :
      γ * ⟪G, point xNext - point xRef⟫_ℝ + V x xNext ≤
        V x xRef - V xNext xRef)
    (hVlower_all :
      ∀ y z : X, (1 / 2 : ℝ) * ‖point y - point z‖ ^ 2 ≤ V y z)
    (hdecomp : G = g + δ)
    (hgbound : ‖g‖ ≤ M) :
    γ * (f x - f xRef) ≤
      V x xRef - V xNext xRef + γ ^ 2 * (M ^ 2 + ‖δ‖ ^ 2) -
        γ * ⟪δ, point x - point xRef⟫_ℝ := by
  exact mirrorDescent_oneStep_pathwise_of_residual_lower_bound
    (f := f) (V := V) (point := point)
    (x := x) (xNext := xNext) (xRef := xRef)
    (G := G) (g := g) (δ := δ) (γ := γ) (M := M)
    hγpos hsub hthree (hVlower_all x xNext) hdecomp hgbound


/-- Convergence from abstract Bregman boundary facts.
Layer: Layer1 | Gap: Level 1 (boundary-to-summation bridge)
Proof: compose the finite-window pathwise summation theorem from the two boundary
  facts with the expectation-level bound consuming that pathwise inequality.
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  proof of Theorem 4.1
Used in: stochastic mirror descent convergence from boundary-safe Bregman facts
Book citation: book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math
Origin algorithm: Lan stochastic mirror descent -/
theorem stochasticMirrorDescent_convergence_of_V_boundary_bridge
    {E Point Ω Time Window : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (point : Point → E) (V : Point → Point → ℝ)
    (x : Time → Ω → Point) (xStar : Point) (nextTime : Time → Time)
    (pathwiseBound : Window → Prop) (convergenceBound : MeasureTheory.Measure Ω → Window → Prop)
    (h_expectation_of_pathwise :
      ∀ w : Window, pathwiseBound w → convergenceBound μ w)
    (h_summed_oneStep_of_V_boundary :
      (∀ t : Time, ∀ ω : Ω,
        (1 / 2 : ℝ) * ‖point (x t ω) - point (x (nextTime t) ω)‖ ^ 2 ≤
          V (x t ω) (x (nextTime t) ω)) →
      (∀ t : Time, ∀ ω : Ω, 0 ≤ V (x t ω) xStar) →
      ∀ w : Window, pathwiseBound w)
    (hVlower :
      ∀ t : Time, ∀ ω : Ω,
        (1 / 2 : ℝ) * ‖point (x t ω) - point (x (nextTime t) ω)‖ ^ 2 ≤
          V (x t ω) (x (nextTime t) ω))
    (hVtail_nonneg :
      ∀ t : Time, ∀ ω : Ω, 0 ≤ V (x t ω) xStar)
    (w : Window) :
    convergenceBound μ w := by
  exact h_expectation_of_pathwise w
    (h_summed_oneStep_of_V_boundary hVlower hVtail_nonneg w)

/-- Stochastic mirror descent convergence follows from intrinsic-closure Bregman boundary facts.

If intrinsic-closure continuity of the Bregman model supplies both the one-step
quadratic lower bound and the nonnegative tail term, then the standard
pathwise-to-expectation bridge yields the convergence bound for the window.

Layer: Layer1 | Gap: Level 1 (intrinsic-closure Bregman boundary convergence)
Proof: delegates to the V-boundary convergence bridge, instantiating the
  required lower-bound and tail-nonnegativity hypotheses from the
  intrinsic-closure continuity facts at the iterates.
Source: Mathlib topology ContinuousOn APIs and inner-product norm inequalities
Used in: SMD convergence bound from intrinsic-closure Bregman lower bound and nonnegativity
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem mirror_descent_convergence_of_intrinsicClosure
    {E X Ω Time Window : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace X] [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (point : X → E) (V : X → X → ℝ)
    (x : Time → Ω → X) (xStar : X) (nextTime : Time → Time)
    (pathwiseBound : Window → Prop)
    (convergenceBound : MeasureTheory.Measure Ω → Window → Prop)
    (h_expectation_of_pathwise :
      ∀ w : Window, pathwiseBound w → convergenceBound μ w)
    (h_summed_oneStep_of_V_boundary :
      (∀ t : Time, ∀ ω : Ω,
        (1 / 2 : ℝ) * ‖point (x t ω) - point (x (nextTime t) ω)‖ ^ 2 ≤
          V (x t ω) (x (nextTime t) ω)) →
      (∀ t : Time, ∀ ω : Ω, 0 ≤ V (x t ω) xStar) →
      ∀ w : Window, pathwiseBound w)
    (hcont : ContinuousOn (fun p : X × X => V p.1 p.2) Set.univ)
    (hVlower_of_intrinsicClosure :
      ContinuousOn (fun p : X × X => V p.1 p.2) Set.univ →
        ∀ y z : X, (1 / 2 : ℝ) * ‖point y - point z‖ ^ 2 ≤ V y z)
    (hVtail_nonneg_of_intrinsicClosure :
      ContinuousOn (fun p : X × X => V p.1 p.2) Set.univ →
        ∀ y z : X, 0 ≤ V y z)
    (w : Window) :
    convergenceBound μ w := by
  exact stochasticMirrorDescent_convergence_of_V_boundary_bridge
    (μ := μ)
    (point := point)
    (V := V)
    (x := x)
    (xStar := xStar)
    (nextTime := nextTime)
    (pathwiseBound := pathwiseBound)
    (convergenceBound := convergenceBound)
    (h_expectation_of_pathwise := h_expectation_of_pathwise)
    (h_summed_oneStep_of_V_boundary := h_summed_oneStep_of_V_boundary)
    (hVlower := fun t ω =>
      hVlower_of_intrinsicClosure hcont (x t ω) (x (nextTime t) ω))
    (hVtail_nonneg := fun t ω =>
      hVtail_nonneg_of_intrinsicClosure hcont (x t ω) xStar)
    (w := w)

/-- A pointwise mirror-step update preserves the selector's argmin inequality.

If `xNext` is defined pointwise by `mirrorStep` and the mirror-step selector
minimizes the mirror objective for every current iterate, oracle value, stepsize,
and candidate, then each updated iterate `xNext ω` satisfies the same
minimization inequality.

Layer: Layer1 | Gap: Level 0 (mirror-step update argmin transfer)
Proof: rewrite the updated iterate with the pointwise update rule and apply the
  assumed mirror-step minimization property at the sampled iterate, oracle value,
  and stepsize.
Source: Mathlib equality rewriting and order relation APIs
Used in: stochastic mirror descent update rule showing the next iterate minimizes
  the paper mirror objective
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem mirrorStep_minimizes_of_update
    {Ω P G : Type*}
    (objective : P → G → ℝ → P → ℝ)
    (mirrorStep : P → G → ℝ → P)
    (x xNext : Ω → P) (oracle : Ω → G) (stepSize : Ω → ℝ)
    (h_update : ∀ ω, xNext ω = mirrorStep (x ω) (oracle ω) (stepSize ω))
    (h_mirrorStep_minimizes :
      ∀ x g γ y, objective x g γ (mirrorStep x g γ) ≤ objective x g γ y)
    (ω : Ω) :
    ∀ y : P,
      objective (x ω) (oracle ω) (stepSize ω) (xNext ω) ≤
        objective (x ω) (oracle ω) (stepSize ω) y := by
  intro y
  rw [h_update ω]
  exact h_mirrorStep_minimizes (x ω) (oracle ω) (stepSize ω) y

/-- A recursive mirror update has literal argmin semantics at an interior current iterate.

If the pathwise next iterate is defined by `mirrorStep`, and `mirrorStep` is known
to satisfy the literal mirror-step predicate when started from an interior-domain
wrapper, then identifying the current iterate with that wrapper transports the
literal argmin statement to `xNext ω`.

Layer: Layer1 | Gap: Level 1 (interior mirror-step argmin transport)
Proof: rewrite the update equation and the interior identification, then apply
  the pointwise literal mirror-step specification.
Source: Mathlib equality rewriting and specialization APIs
Used in: stochastic mirror descent proof that an interior current iterate gives
  literal mirror-step argmin semantics
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem literalMirrorStep_of_update_of_interior
    {Ω P IP D : Type*}
    (toP : IP → P)
    (mirrorStep : P → D → ℝ → P)
    (IsLiteralMirrorStep : IP → D → ℝ → P → Prop)
    (x xNext : Ω → P) (d : Ω → D) (stepSize : Ω → ℝ)
    (h_update : ∀ ω, xNext ω = mirrorStep (x ω) (d ω) (stepSize ω))
    (h_mirrorStep_literal :
      ∀ x g γ, IsLiteralMirrorStep x g γ (mirrorStep (toP x) g γ))
    {ω : Ω} (xInterior : IP) (hxInterior : toP xInterior = x ω) :
    IsLiteralMirrorStep xInterior (d ω) (stepSize ω) (xNext ω) := by
  rw [h_update ω, ← hxInterior]
  exact h_mirrorStep_literal xInterior (d ω) (stepSize ω)

/-- Pathwise mirror-descent three-point inequality transported across an abstract update rule.

If a stochastic iterate `xNext` is pointwise equal to the mirror-descent step
computed from `x`, `g`, and `γ`, then the deterministic three-point Bregman
inequality for that step applies pathwise at every sample `ω`.

Layer: Layer1 | Gap: Level 1 (pathwise transport of mirror-descent three-point inequality)
Proof: rewrite the pathwise update equality and apply the deterministic
  three-point step inequality.
Source: Mathlib equality rewriting and ordered real inner-product algebra APIs
Used in: stochastic mirror descent descent step using the update rule and Bregman
  three-point inequality
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem mirrorDescent_three_point_of_update
    {Ω P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → P → ℝ) (eval : P → E) (step : P → E → ℝ → P)
    (x xNext : Ω → P) (g : Ω → E) (γ : ℝ) (y : P)
    (h_update : ∀ ω, xNext ω = step (x ω) (g ω) γ)
    (h_step_three_point :
      ∀ x g γ y,
        γ * ⟪g, eval (step x g γ) - eval y⟫_ℝ +
          V x (step x g γ) ≤
            V x y - V (step x g γ) y)
    (ω : Ω) :
    γ * ⟪g ω, eval (xNext ω) - eval y⟫_ℝ +
      V (x ω) (xNext ω) ≤
        V (x ω) y - V (xNext ω) y := by
  rw [h_update ω]
  exact h_step_three_point (x ω) (g ω) γ y

open MeasureTheory ProbabilityTheory

/-- Recursive stochastic iterates are adapted when each measurable update uses only past state,
current sample information, a measurable oracle value, and a deterministic step parameter.

Layer: Layer1 | Gap: Level 1 (recursive adaptedness of stochastic iterates)
Proof: strong induction on the time index; measurability is propagated by filtration
  monotonicity, product measurability, measurable composition through the oracle and
  update maps, and the constant-step measurability API.
Source: Mathlib measure theory measurability composition and filtration monotonicity APIs
Used in: stochastic mirror descent adapted-iterate construction for recursive oracle updates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem adapted_iterate_of_recursive_adapted_update
    {Ω P S D : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace S]
    [MeasurableSpace D]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (x : {t : ℕ // 1 ≤ t} → Ω → P) (ξ : {t : ℕ // 1 ≤ t} → Ω → S)
    (oracle : P → S → D) (update : P → D → ℝ → P)
    (γ : {t : ℕ // 1 ≤ t} → ℝ) (x₁ : P)
    (horacle : Measurable (fun p : P × S => oracle p.1 p.2))
    (hupdate : Measurable (fun p : P × D × ℝ => update p.1 p.2.1 p.2.2))
    (hξ_adapted : ∀ t : {t : ℕ // 1 ≤ t}, Measurable[filt.seq t.1] (ξ t))
    (hx_init : x ⟨1, le_rfl⟩ = fun _ => x₁)
    (hx_update :
      ∀ t : {t : ℕ // 1 ≤ t},
        x ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩ = fun ω =>
          update (x t ω) (oracle (x t ω) (ξ t ω)) (γ t))
    (t : {t : ℕ // 1 ≤ t}) :
    Measurable[filt.seq (t.1 - 1)] (x t) := by
  classical
  rcases t with ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              have hinit : x ⟨1, hn⟩ = fun _ => x₁ := by
                simpa using hx_init
              rw [hinit]
              exact measurable_const
          | succ k =>
              let s : {t : ℕ // 1 ≤ t} := ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
              have hs_lt : s.1 < Nat.succ (Nat.succ k) := by
                dsimp [s]
                omega
              have hx_past : Measurable[filt.seq (s.1 - 1)] (x s) :=
                ih s.1 hs_lt s.2
              have hx_curr : Measurable[filt.seq s.1] (x s) :=
                hx_past.mono (filt.mono (Nat.sub_le s.1 1)) le_rfl
              have hξ_curr : Measurable[filt.seq s.1] (ξ s) :=
                hξ_adapted s
              have hG_curr : Measurable[filt.seq s.1] (fun ω => oracle (x s ω) (ξ s ω)) :=
                horacle.comp (hx_curr.prodMk hξ_curr)
              have hstep :
                  x ⟨Nat.succ (Nat.succ k), hn⟩ = fun ω =>
                    update (x s ω) (oracle (x s ω) (ξ s ω)) (γ s) := by
                have h := hx_update s
                simpa [s] using h
              rw [hstep]
              have hγ : Measurable[filt.seq s.1] (fun _ : Ω => γ s) :=
                measurable_const
              simpa [s] using
                hupdate.comp (hx_curr.prodMk (hG_curr.prodMk hγ))

/-- Recursive sample-driven stochastic iterates are adapted to the past sample filtration.

If the initial iterate is deterministic, each sample is measurable, the oracle and update maps are
measurable, and the recursion updates `x (t+1)` from `x t`, the current sample, and a deterministic
stepsize, then `x t` is measurable with respect to the natural filtration generated by samples before
time `t`.

Layer: Layer1 | Gap: Level 1 (recursive iterate measurability for sample filtrations)
Proof: reduce to the abstract adapted-recursive-update lemma, then show each indexed sample is
  measurable with respect to its natural past filtration by a `comap`-to-`iSup` inclusion and
  subtype index arithmetic.
Source: Mathlib measure theory measurable-space comap, filtration, and order-theoretic iSup APIs
Used in: stochastic mirror descent proof that recursive iterates are adapted to the past sample filtration
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem adapted_iterate_of_recursive_sample_update
    {Ω P S D : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace S]
    [MeasurableSpace D]
    (x : {t : ℕ // 1 ≤ t} → Ω → P) (ξ : {t : ℕ // 1 ≤ t} → Ω → S)
    (oracle : P → S → D) (update : P → D → ℝ → P)
    (γ : {t : ℕ // 1 ≤ t} → ℝ) (x₁ : P)
    (horacle : Measurable (fun p : P × S => oracle p.1 p.2))
    (hupdate : Measurable (fun p : P × D × ℝ => update p.1 p.2.1 p.2.2))
    (hξ_measurable : ∀ t : {t : ℕ // 1 ≤ t}, Measurable (ξ t))
    (hx_init : x ⟨1, le_rfl⟩ = fun _ => x₁)
    (hx_update :
      ∀ t : {t : ℕ // 1 ≤ t},
        x ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩ = fun ω =>
          update (x t ω) (oracle (x t ω) (ξ t ω)) (γ t))
    (t : {t : ℕ // 1 ≤ t}) :
    Measurable[
      (SOptLib.filtration
        (fun j : ℕ => ξ ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
        (fun j : ℕ => hξ_measurable ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)).seq
          (t.1 - 1)] (x t) := by
  refine adapted_iterate_of_recursive_adapted_update
    (filt := SOptLib.filtration
      (fun j : ℕ => ξ ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
      (fun j : ℕ => hξ_measurable ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩))
    (x := x) (ξ := ξ) (oracle := oracle) (update := update) (γ := γ) (x₁ := x₁)
    horacle hupdate ?_ hx_init hx_update t
  intro s
  have htime :
      (⟨s.1 - 1 + 1, Nat.succ_le_succ (Nat.zero_le (s.1 - 1))⟩ :
        {t : ℕ // 1 ≤ t}) = s := by
    ext
    exact Nat.sub_add_cancel s.2
  refine Measurable.of_comap_le ?_
  have hle :
      MeasurableSpace.comap (ξ s) (by infer_instance : MeasurableSpace S) ≤
        ⨆ j < s.1,
          MeasurableSpace.comap
            (ξ ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
            (by infer_instance : MeasurableSpace S) := by
    calc
      MeasurableSpace.comap (ξ s) (by infer_instance : MeasurableSpace S) =
          MeasurableSpace.comap
            (ξ ⟨s.1 - 1 + 1, Nat.succ_le_succ (Nat.zero_le (s.1 - 1))⟩)
            (by infer_instance : MeasurableSpace S) := by
        rw [htime]
      _ ≤ ⨆ j < s.1,
          MeasurableSpace.comap
            (ξ ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
            (by infer_instance : MeasurableSpace S) :=
        le_iSup_of_le (s.1 - 1)
          (le_iSup_of_le (by omega : s.1 - 1 < s.1) le_rfl)
  simpa [SOptLib.filtration_seq] using hle

/-- Absorb a residual/exact-gradient cross term in a one-step descent inequality.

If the raw descent controls a weighted stochastic projected-gradient square by an
objective drop, a residual square, and a residual/exact projected-gradient inner
product, and the exact and stochastic projected gradients are Lipschitz-close by
the residual, then the cross term is absorbed into one half of the stochastic
square and two more residual squares.

Layer: Layer1 | Gap: Level 1 (residual cross-term absorption in pathwise descent)
Proof: use the norm triangle inequality and Cauchy-Schwarz to bound the inner
  product by `‖δ‖ * (‖spg‖ + ‖δ‖)`, apply scalar Young absorption with
  `γ - L * γ ^ 2 = γ / 2`, and finish by ordered-ring arithmetic.
Source: Mathlib inner-product norm inequalities and real Young inequality algebra
Used in: nonconvex stochastic mirror descent one-step residual descent after projected-gradient Lipschitz comparison
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem one_step_descent_absorb_residual_cross_term
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ L D : ℝ) (spg epg δ : E)
    (hγ : 0 ≤ γ)
    (hstep :
      (γ - L * γ ^ 2) * ‖spg‖ ^ 2 ≤
        D + γ * ‖δ‖ ^ 2 + γ * ⟪δ, epg⟫_ℝ)
    (hlip : ‖epg - spg‖ ≤ ‖δ‖)
    (hweight : γ - L * γ ^ 2 = γ / 2) :
    ((γ - L * γ ^ 2) / 2) * ‖spg‖ ^ 2 ≤
      D + 3 * γ * ‖δ‖ ^ 2 := by
  let w : ℝ := γ - L * γ ^ 2
  have he_norm : ‖epg‖ ≤ ‖spg‖ + ‖δ‖ := by
    have htri : ‖epg‖ ≤ ‖spg‖ + ‖epg - spg‖ := by
      calc
        ‖epg‖ = ‖spg + (epg - spg)‖ := by
          congr 1
          abel
        _ ≤ ‖spg‖ + ‖epg - spg‖ := norm_add_le _ _
    linarith
  have hinner : ⟪δ, epg⟫_ℝ ≤ ‖δ‖ * (‖spg‖ + ‖δ‖) := by
    calc
      ⟪δ, epg⟫_ℝ ≤ |⟪δ, epg⟫_ℝ| := le_abs_self _
      _ ≤ ‖δ‖ * ‖epg‖ := abs_real_inner_le_norm δ epg
      _ ≤ ‖δ‖ * (‖spg‖ + ‖δ‖) :=
        mul_le_mul_of_nonneg_left he_norm (norm_nonneg δ)
  have hcross :
      γ * ⟪δ, epg⟫_ℝ ≤ (w / 2) * ‖spg‖ ^ 2 + 2 * γ * ‖δ‖ ^ 2 :=
    mul_le_half_sq_add_two_mul_sq_of_le_mul_add hγ (by simpa [w] using hweight) hinner
  have hstep' :
      w * ‖spg‖ ^ 2 ≤ D + γ * ‖δ‖ ^ 2 + γ * ⟪δ, epg⟫_ℝ := by
    simpa [w] using hstep
  have hfinal : (w / 2) * ‖spg‖ ^ 2 ≤ D + 3 * γ * ‖δ‖ ^ 2 := by
    nlinarith [hstep', hcross]
  simpa [w] using hfinal

/-- A recursive process is measurable when its oracle and update are measurable.

For a process with measurable initial state, if every pointwise oracle call is
measurable along measurable random queries and each time-indexed update is
measurable on the state-oracle product, then all process slices are measurable.

Layer: Layer1 | Gap: Level 1 (recursive oracle-update process measurability)
Proof: induction on the natural-number time index; the successor step composes the measurable product of the previous process slice and oracle slice with the measurable update map.
Source: Mathlib measure-theory APIs for measurable products and composition
Used in: randomized stochastic mirror descent mini-batch prox iterate measurability
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
theorem recursive_process_measurable_of_measurable_update_oracle
    {Ω P D : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace D]
    (x : ℕ → Ω → P)
    (oracle : ℕ → P → Ω → D)
    (update : ℕ → P → D → P)
    (h_initial : Measurable (x 0))
    (h_oracle :
      ∀ n (y : Ω → P), Measurable y → Measurable (fun ω => oracle n (y ω) ω))
    (h_update : ∀ n, Measurable (fun p : P × D => update n p.1 p.2))
    (h_succ : ∀ n, x (n + 1) = fun ω => update n (x n ω) (oracle n (x n ω) ω)) :
    ∀ n : ℕ, Measurable (x n) := by
  intro n
  induction n with
  | zero =>
      exact h_initial
  | succ n ih =>
      have horacle_slice : Measurable (fun ω => oracle n (x n ω) ω) :=
        h_oracle n (x n) ih
      have hupdate_slice : Measurable (fun p : P × D => update n p.1 p.2) :=
        h_update n
      simpa [h_succ n] using hupdate_slice.comp (ih.prodMk horacle_slice)

/-- A one-block bound lifts to an inverse-weighted aggregate block potential bound.

If the selected block potential changes by at most `delta`, all non-selected
block potential terms are unchanged, and the selected inverse sampling weight
is nonnegative, then the weighted product-space potential changes by at most
the selected inverse weight times `delta`.

Layer: Layer1 | Gap: Level 1 (single-block aggregate potential lift)
Proof: multiply the selected block inequality by the nonnegative selected
  inverse weight, compare the finite sums termwise, and collapse the singleton
  correction with `Finset.sum_eq_single` via `simp`.
Source: finite block-coordinate Lyapunov algebra for randomized coordinate
  mirror descent
Used in: stochastic block mirror descent one-block prox-step aggregate
  Bregman potential recursion
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem weighted_block_bregman_potential_single_block_bound
    {ι State : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Type*) (p : ι → ℝ) (coord : ∀ i, State → B i)
    (V : ∀ i, B i → B i → ℝ)
    (i : ι) (z y x : State) (delta : ℝ)
    (hweight : 0 ≤ (p i)⁻¹)
    (hblock :
      V i (coord i y) (coord i x) ≤ V i (coord i z) (coord i x) + delta)
    (hother :
      ∀ j, j ≠ i →
        V j (coord j y) (coord j x) = V j (coord j z) (coord j x)) :
    weightedBlockBregmanPotential B p coord V y x ≤
      weightedBlockBregmanPotential B p coord V z x + (p i)⁻¹ * delta := by
  classical
  unfold weightedBlockBregmanPotential
  have hblock_weighted :
      (p i)⁻¹ * V i (coord i y) (coord i x) ≤
        (p i)⁻¹ * V i (coord i z) (coord i x) + (p i)⁻¹ * delta := by
    nlinarith [mul_le_mul_of_nonneg_left hblock hweight]
  have hsum :
      Finset.sum Finset.univ
          (fun j => (p j)⁻¹ * V j (coord j y) (coord j x)) ≤
        Finset.sum Finset.univ
          (fun j =>
            (p j)⁻¹ * V j (coord j z) (coord j x) +
              if j = i then (p i)⁻¹ * delta else 0) := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hji : j = i
    · subst j
      simpa using hblock_weighted
    · simp [hji, hother j hji]
  calc
    Finset.sum Finset.univ (fun j => (p j)⁻¹ * V j (coord j y) (coord j x))
        ≤ Finset.sum Finset.univ
            (fun j =>
              (p j)⁻¹ * V j (coord j z) (coord j x) +
                if j = i then (p i)⁻¹ * delta else 0) := hsum
    _ = Finset.sum Finset.univ (fun j => (p j)⁻¹ * V j (coord j z) (coord j x)) +
          (p i)⁻¹ * delta := by
        rw [Finset.sum_add_distrib]
        simp

/-- A fixed coordinate prox update is measurable from measurable components.

If the state query, sample query, deterministic center map, stochastic oracle,
gradient-coordinate map, prox selector, stepsize, and replacement splice are
measurable in their natural product presentations, then the composed
samplewise fixed-coordinate prox update is measurable.

Layer: Layer1 | Gap: Level 1 (sampled-coordinate prox update measurability)
Proof: compose the state and sample observables through the oracle, postcompose
  with the coordinate map, apply `Measurable.proxStep_comp`, then compose the
  resulting selector with the state-replacement splice.
Source: Mathlib measure theory measurability composition and product APIs
Used in: stochastic block mirror descent fixed-block prox splice before finite block dispatch
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem fixed_coordinate_prox_update_measurable_of_components
    {Ω State Center Sample Raw Grad : Type*}
    [MeasurableSpace Ω] [MeasurableSpace State] [MeasurableSpace Center]
    [MeasurableSpace Sample] [MeasurableSpace Raw] [MeasurableSpace Grad]
    (center : State → Center) (oracle : State → Sample → Raw) (coord : Raw → Grad)
    (prox : Center → Grad → ℝ → Center) (replace : State → Center → State)
    (query : Ω → State) (sample : Ω → Sample) (step : Ω → ℝ)
    (hcenter : Measurable center)
    (horacle : Measurable (fun p : State × Sample => oracle p.1 p.2))
    (hcoord : Measurable coord)
    (hprox : Measurable (fun p : Center × Grad × ℝ => prox p.1 p.2.1 p.2.2))
    (hreplace : Measurable (fun p : State × Center => replace p.1 p.2))
    (hquery : Measurable query) (hsample : Measurable sample) (hstep : Measurable step) :
    Measurable
      (fun ω =>
        replace (query ω)
          (prox (center (query ω)) (coord (oracle (query ω) (sample ω))) (step ω))) := by
  have hcenter_comp : Measurable (fun ω => center (query ω)) :=
    hcenter.comp hquery
  have horacle_comp : Measurable (fun ω => oracle (query ω) (sample ω)) :=
    horacle.comp (hquery.prodMk hsample)
  have hgrad_comp : Measurable (fun ω => coord (oracle (query ω) (sample ω))) :=
    hcoord.comp horacle_comp
  have hsel :
      Measurable
        (fun ω => prox (center (query ω)) (coord (oracle (query ω) (sample ω))) (step ω)) :=
    Measurable.proxStep_comp (prox := prox) hprox hcenter_comp hgrad_comp hstep
  exact hreplace.comp (hquery.prodMk hsel)

/-- A selected-block aggregate potential step rewrites as drift plus oracle noise.

If a one-step aggregate potential bound is stated using the sampled block
inner product and selected quadratic penalty, and the selected lift pairs with
ambient displacements, then the same step can be written as deterministic
mean-gradient drift plus the scalar oracle-noise and quadratic `deltaBar`
terms.

Layer: Layer1 | Gap: Level 1 (selected-block one-step recursion algebra)
Proof: rewrite the selected block pairing through the ambient lift, expand the
  scalar oracle-noise inner product, substitute the quadratic selected term,
  and close the ordered-ring inequality.
Source: block-coordinate mirror descent Lyapunov recursion and Mathlib
  real inner-product algebra
Used in: stochastic block mirror descent one-step aggregate potential recursion
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem block_mirror_descent_one_step_aggregate_recursion
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (point : P → E) (V : P → P → ℝ)
    (x xNext xRef : P) (sampledLift meanGrad : E)
    (sampledPair eta delta deltaBar quad : ℝ)
    (hstep :
      V xNext xRef ≤ V x xRef +
        eta * sampledPair + (1 / 2 : ℝ) * eta ^ 2 * quad)
    (hpair :
      sampledPair = ⟪sampledLift, point xRef - point x⟫_ℝ)
    (hdelta :
      delta = ⟪sampledLift - meanGrad, point xRef - point x⟫_ℝ)
    (hdeltaBar : deltaBar = quad) :
    V xNext xRef ≤ V x xRef +
      eta * ⟪meanGrad, point xRef - point x⟫_ℝ +
      eta * delta +
      (1 / 2 : ℝ) * eta ^ 2 * deltaBar := by
  have hnoise :
      eta * ⟪meanGrad, point xRef - point x⟫_ℝ + eta * delta =
        eta * sampledPair := by
    rw [hdelta, hpair]
    simp [inner_sub_left]
    ring
  have hquad :
      (1 / 2 : ℝ) * eta ^ 2 * deltaBar =
        (1 / 2 : ℝ) * eta ^ 2 * quad := by
    rw [hdeltaBar]
  nlinarith



open scoped InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: conditional_gradient_wolfe_gap_one_step_descent_of_smooth
--   (orig was: conditionalGradient_wolfeGap_oneStep_descent_of_smooth; renamed
--   to snake_case while keeping the recognized conditional-gradient Wolfe-gap
--   descent concept).
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses
--      subtraction, real inner products, norms, and ordered real algebra, with
--      no finite-dimensionality, completeness, topology, or measurability.
--   measure: none; this is a deterministic pointwise one-step algebra lemma.
--   convexity: none; smoothness and LMO geometry enter only through the two
--      pointwise hypotheses actually consumed by the proof.
-- G0.3 reusability — could instantiate:
--   1. finite-sum stochastic nonconvex conditional gradient, after the smooth
--      affine-LMO descent premise and before summing active Wolfe gaps.
--   2. stochastic conditional gradient and variance-reduced Frank-Wolfe,
--      when a true Wolfe gap is bounded by an estimator surrogate plus a
--      diameter-weighted residual term.
-- G0.4 search trace:
--   queries: ["Wolfe gap descent smooth",
--     "inner linear minimizer smooth descent estimator error diameter",
--     "Young inequality alpha d D over L plus L alpha squared D squared"]
--   top hits: ["Convex.carrier_smooth_quadratic_upper_bound",
--     "summed_one_step_gap_bound_of_telescope",
--     "conditional_gradient_smooth_descent_premise_of_estimator",
--     "SOptLib.ConditionalGradient.wolfeGap_le_maxLinearModel_add_estimatorError_mul_diameter",
--     "mul_mul_le_inv_two_mul_add_half_mul_sq",
--     "Real.young_inequality",
--     "two_mul_le_add_mul_sq"]
--   coverage: partial — the hits provide the smooth quadratic premise, Wolfe
--     surrogate bound, scaled Young inequality, or later telescoping, but none
--     packages the intermediate one-step Wolfe-gap descent rearrangement.
-- G0.4 not-a-thin-wrapper rationale: combines a pointwise Wolfe-gap surrogate
--   inequality, the estimator-LMO descent premise, sign reversal of the LMO
--   displacement, and scaled Young absorption into one reusable descent bound.
-- G0.5 structural-content rationale: theorem only; it introduces no wrapper
--   structure or formula-bodied definition and exposes the exact descent
--   invariant consumed by conditional-gradient summation proofs.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step inner-product
--   sign algebra, descent rearrangement, Young absorption, and coefficient
--   collection beyond a single existing theorem call.
-- G0.5d minimal-hypothesis check: all already minimal; smoothness, diameter,
--   and LMO optimality have been reduced to pointwise surrogate and descent
--   inequalities at the current iterate.

/-- A Wolfe-gap surrogate plus a smooth conditional-gradient descent premise
gives the absorbed one-step gap descent inequality.

If a stationarity gap at `x` is bounded by the estimator linear model
`⟪G, x - lmo G⟫` plus a diameter-weighted residual norm, and a smooth descent
premise controls `f xnext` using the opposite LMO displacement, then multiplying
the gap by the stepsize is bounded by the objective drop, a residual square, and
the usual `3/2` smoothness-diameter term.

Layer: Layer1 | Gap: Level 1 (conditional-gradient Wolfe-gap one-step descent)
Proof: multiply the surrogate bound by the nonnegative stepsize, rewrite
  `⟪G, x - y⟫` as `-⟪G, y - x⟫`, rearrange the descent premise, absorb the
  residual-diameter product with scaled Young's inequality, and collect terms.
Source: Frank-Wolfe conditional-gradient one-step descent algebra, real
  Hilbert-space inner-product identities, and ordered-field Young inequality
Used in: finite-sum and stochastic nonconvex conditional-gradient active-step
  Wolfe-gap descent before summation and expectation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem conditional_gradient_wolfe_gap_one_step_descent_of_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gap f : E → ℝ) (targetGrad lmo : E → E)
    (x G xnext : E) (alpha L D : ℝ)
    (hL_pos : 0 < L)
    (halpha_nonneg : 0 ≤ alpha)
    (hgap :
      gap x ≤ ⟪G, x - lmo G⟫_ℝ + ‖G - targetGrad x‖ * D)
    (hdescent :
      f xnext ≤
        f x + alpha * ⟪G, lmo G - x⟫_ℝ +
          (1 / (2 * L)) * ‖G - targetGrad x‖ ^ 2 +
          L * alpha ^ 2 * D ^ 2) :
    alpha * gap x ≤
      f x - f xnext +
        (1 / L) * ‖G - targetGrad x‖ ^ 2 +
        (3 / 2) * L * alpha ^ 2 * D ^ 2 := by
  let y : E := lmo G
  let d : ℝ := ‖G - targetGrad x‖
  have hgap_mul :
      alpha * gap x ≤ alpha * (⟪G, x - y⟫_ℝ + d * D) := by
    exact mul_le_mul_of_nonneg_left (by simpa [y, d] using hgap) halpha_nonneg
  have hinner_neg : ⟪G, x - y⟫_ℝ = -⟪G, y - x⟫_ℝ := by
    have hxy : x - y = -(y - x) := by
      abel
    rw [hxy, inner_neg_right]
  have hdesc_rearr :
      -alpha * ⟪G, y - x⟫_ℝ ≤
        f x - f xnext +
          (1 / (2 * L)) * d ^ 2 +
          L * alpha ^ 2 * D ^ 2 := by
    dsimp [y, d] at hdescent ⊢
    linarith
  have hyoung :
      alpha * (d * D) ≤
        (1 / (2 * L)) * d ^ 2 +
          (L / 2) * alpha ^ 2 * D ^ 2 := by
    exact mul_mul_le_inv_two_mul_add_half_mul_sq alpha d D L hL_pos
  calc
    alpha * gap x
        ≤ alpha * (⟪G, x - y⟫_ℝ + d * D) := hgap_mul
    _ = -alpha * ⟪G, y - x⟫_ℝ + alpha * (d * D) := by
        rw [hinner_neg]
        ring
    _ ≤
        (f x - f xnext +
          (1 / (2 * L)) * d ^ 2 +
          L * alpha ^ 2 * D ^ 2) +
          ((1 / (2 * L)) * d ^ 2 +
            (L / 2) * alpha ^ 2 * D ^ 2) := by
        exact add_le_add hdesc_rearr hyoung
    _ =
      f x - f xnext +
        (1 / L) * ‖G - targetGrad x‖ ^ 2 +
        (3 / 2) * L * alpha ^ 2 * D ^ 2 := by
        dsimp [d]
        field_simp [ne_of_gt hL_pos]
        ring



-- Generalization plan (G0):
-- G0.1 naming: recursive_estimator_residual_global_index_eq_prev_add_centered_batch_diff
--   (orig was: deltaProcessOfWellDefined_globalIndex_recursive); the staged name
--   describes a recursive estimator residual transported through global epoch
--   indices and centered into a mini-batch difference, with no paper-internal
--   theorem number or algorithm acronym.
-- G0.2 typeclass level used:
--   E: [AddCommGroup E] [Module ℝ E]; the proof uses only subtraction, addition,
--      finite sums, and real scalar multiplication by the batch-cardinality
--      inverse. No norm, topology, inner product, completeness, or finite
--      dimensionality is used.
--   measure: none; the identity is pathwise before probability, filtration,
--      independence, integrability, or conditional expectation enters.
--   convexity: none; no feasible-set or objective geometry is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional-gradient recursive estimator residuals
--      before applying centered mini-batch variance bounds.
--   2. variance-reduced stochastic gradient and mirror-descent estimator-drift
--      recursions with epoch-local mini-batch increments.
-- G0.4 search trace:
--   queries: ["recursive estimator residual",
--     "global index centered mini batch residual recursion"]
--   top hits: ["estimatorResidualProcess_succ_eq_of_estimator_update",
--     "process_recursive_average_sub_target_eq_average_residual",
--     "deltaProcess_globalIndex_recursive_residual",
--     "miniBatchAverage_sub_target_eq_average_residual",
--     "pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero"]
--   coverage: partial — existing hits cover one-step residual updates,
--     global-index transport, or average centering separately; none returns the
--     paired raw and centered global-index recursion from a successor-time
--     estimator residual recurrence.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable invariant
--   that successor-time estimator residual recurrences have both their raw and
--   centered mini-batch forms after transport to one-based global epoch indices.
-- G0.5 structural-content rationale: the paired conclusion lets algorithm files
--   preserve existing raw-recursion statements while exposing the centered
--   residual-average form consumed by variance-reduction proofs.
-- G0.5c thin-wrapper self-detect: clean — body composes epoch-index transport
--   with finite-average centering and records both resulting recursion forms,
--   rather than renaming a single existing declaration.
-- G0.5d minimal-hypothesis check: all already minimal; the proof uses only the
--   pointwise successor recursion, batch-cardinality equality, positive
--   denominator, and pointwise bounds `2 ≤ j` and `j ≤ T`.

namespace SOptLib

/-- A successor-time estimator residual recursion has raw and centered global-index forms.

If an estimator residual process satisfies a within-epoch successor recursion
whose increment is a finite mini-batch average minus a target difference, then
at every one-based global epoch coordinate `2 ≤ j ≤ T` it yields both the raw
`average - target` recursion and the centered residual-average recursion.

Layer: Layer1 | Gap: Level 1 (global-index estimator residual centering)
Proof: first transport the successor-time recurrence to global epoch indices
  with the fixed-length global-index recursion theorem, then center the finite
  average by the mini-batch residual identity.
Source: Mathlib natural-number modulo arithmetic, finite sums, and real module algebra
Used in: stochastic nonconvex conditional-gradient recursive estimator residual
  decomposition before mini-batch second-moment control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem recursive_estimator_residual_global_index_eq_prev_add_centered_batch_diff
    {Ω ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : ℕ) (I : Finset ι) (m : ℕ) (hmcard : I.card = m) (hmpos : 0 < m)
    (δ : ℕ → Ω → E) (batch_diff : ℕ → ℕ → ι → Ω → E)
    (target_diff : ℕ → ℕ → Ω → E)
    (hrec : ∀ k, (k + 1) % T ≠ 0 → ∀ ω,
      δ (k + 2) ω =
        δ (k + 1) ω +
          ((m : ℝ)⁻¹) • Finset.sum I (fun i => batch_diff (k + 1) (k + 2) i ω) -
        target_diff (k + 1) (k + 2) ω)
    (s j : ℕ) (hj2 : 2 ≤ j) (hjT : j ≤ T) :
    (∀ ω,
      δ (global_index T s j) ω =
        δ (global_index T s (j - 1)) ω +
          ((m : ℝ)⁻¹) •
            Finset.sum I
              (fun i => batch_diff (global_index T s (j - 1)) (global_index T s j) i ω) -
        target_diff (global_index T s (j - 1)) (global_index T s j) ω) ∧
    (∀ ω,
      δ (global_index T s j) ω =
        δ (global_index T s (j - 1)) ω +
          ((m : ℝ)⁻¹) •
            Finset.sum I
              (fun i =>
                batch_diff (global_index T s (j - 1)) (global_index T s j) i ω -
                  target_diff (global_index T s (j - 1)) (global_index T s j) ω)) := by
  have hraw :
      ∀ ω,
        δ (global_index T s j) ω =
          δ (global_index T s (j - 1)) ω +
            ((m : ℝ)⁻¹) •
              Finset.sum I
                (fun i => batch_diff (global_index T s (j - 1)) (global_index T s j) i ω) -
          target_diff (global_index T s (j - 1)) (global_index T s j) ω := by
    exact
      global_index_recursive_of_succ
        (T := T)
        (process := δ)
        (increment := fun k k' ω =>
          ((m : ℝ)⁻¹) • Finset.sum I (fun i => batch_diff k k' i ω))
        (correction := fun k k' ω => target_diff k k' ω)
        (hrec := hrec)
        (s := s) (j := j) hj2 hjT
  have hcenter :
      ∀ ω,
        δ (global_index T s j) ω =
          δ (global_index T s (j - 1)) ω +
            ((m : ℝ)⁻¹) •
              Finset.sum I
                (fun i =>
                  batch_diff (global_index T s (j - 1)) (global_index T s j) i ω -
                    target_diff (global_index T s (j - 1)) (global_index T s j) ω) :=
    process_recursive_average_sub_target_eq_average_residual
      (I := I) (m := m) (hmcard := hmcard) (hmpos := hmpos)
      (process := δ)
      (prev := global_index T s (j - 1)) (curr := global_index T s j)
      (a := fun i ω => batch_diff (global_index T s (j - 1)) (global_index T s j) i ω)
      (target := fun ω => target_diff (global_index T s (j - 1)) (global_index T s j) ω)
      hraw
  exact ⟨hraw, hcenter⟩

end SOptLib

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: terminal finite-window bound from a guarded sum inequality
--   and an unguarded sum identity.
-- generality used: arbitrary summands over the one-based natural window
--   `Finset.Icc 1 t`, plus a terminal value; no measure, independence,
--   integrability, Hilbert-space, convexity, smoothness, or oracle assumptions
--   are used by this finite-sum assembly step.
-- portable call pattern: proofs can call this after summing guarded pointwise
--   recurrences and proving that the corresponding unguarded left side equals
--   a terminal boundary; schedules, state formulas, residual summands, and
--   comparison points vary while the conclusion shape remains.
-- counterargument checked: the theorem is close to ordered algebra, but it is
--   not a pure rename of a Mathlib lemma because it packages the recurring
--   bridge between a guarded finite-window sum bound and an unguarded
--   finite-window sum identity.
-- coverage search: searched catalog/SOptLib/Staging for terminal/telescope,
--   weighted one-step, guarded telescope, and summed one-step gap; closest
--   hits were `summed_one_step_gap_bound_of_telescope`,
--   `sum_Icc_shifted_sub_telescope_from_one`, and
--   `finite_window_weighted_recurrence_telescope_with_tail_sums`, all partial
--   because they either perform the telescope itself, drop tails, or assume a
--   different descent decomposition rather than replacing a terminal boundary
--   after the one-step sum and telescope have already been established.
-- minimal hypotheses: all algorithm setup fields were reduced to two
--   hypotheses, the guarded sum bound and the unguarded sum identity; the
--   interval membership proof supplies the guard on every summand.

/-- A terminal value is bounded by a finite-window sum from a guarded sum bound and an
unguarded sum identity.

If the guarded left summands are bounded by the right summands over `[1, t]`,
and the unguarded left summands sum exactly to the terminal value, then the
terminal value is bounded by the right sum.

Layer: Glue | Gap: finite-sum bridge from guarded to unguarded left side
Proof: remove the redundant `1 ≤ i` guard on the closed interval, rewrite by
  the sum identity, and compose with the guarded sum inequality.
Source: Mathlib finite sums over natural intervals and ordered arithmetic -/
theorem terminal_le_sum_of_guarded_sum_le_and_sum_eq
    {α : Type*} [AddCommMonoid α] [Preorder α]
    (left raw : ℕ → α) (terminal : α) (t : ℕ)
    (hone_step :
      Finset.sum (Finset.Icc 1 t) (fun i =>
          if _hi : 1 ≤ i then left i else 0) ≤
        Finset.sum (Finset.Icc 1 t) raw)
    (htelescope :
      Finset.sum (Finset.Icc 1 t) left = terminal) :
    terminal ≤ Finset.sum (Finset.Icc 1 t) raw := by
  classical
  have hleft_guard :
      Finset.sum (Finset.Icc 1 t) (fun i =>
          if _hi : 1 ≤ i then left i else 0) =
        Finset.sum (Finset.Icc 1 t) left := by
    refine Finset.sum_congr rfl ?_
    intro i hiIcc
    simp [(Finset.mem_Icc.mp hiIcc).1]
  have hterminal :
      Finset.sum (Finset.Icc 1 t) (fun i =>
          if _hi : 1 ≤ i then left i else 0) = terminal := by
    exact hleft_guard.trans htelescope
  exact le_of_eq_of_le hterminal.symm hone_step

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: guarded_bregman_boundary_sum_eq_shifted_twoBlockWeightedBregmanBoundary; orig was
--   generated_bregman_raw_sum_eq_generatedBTerm. The concept is a finite-window
--   two-block Bregman boundary sum evaluated on a zero-based generated process
--   and rewritten as the named one-based boundary term.
-- generality used: arbitrary outcome type and arbitrary block-state types;
--   scalar schedules and block Bregman kernels are explicit functions. No
--   measure, measurability, independence, integrability, convexity, topology,
--   vector-space structure, or finite-dimensional hypotheses are used.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   block mirror-descent proofs can call this when a raw generated-process
--   Bregman summation over natural process times must be identified with a
--   one-based named boundary observable; the process and kernels vary while
--   the shifted-boundary equality remains unchanged.
-- counterargument checked: this is short definitional algebra, but it is not
--   only paper traceability because the zero-based process versus one-based
--   paper window shift recurs across generated stochastic-optimization proofs.
--   It is not a duplicate of `twoBlockWeightedBregmanBoundary_def`, which
--   unfolds an already one-based sequence, nor of
--   `twoBlockWeightedBregmanBoundary_eq_of_eq_on_Icc_succ`, which transports
--   between two one-based streams rather than building the shifted stream.
-- coverage search: searched project/catalog tokens
--   `twoBlockWeightedBregmanBoundary`, `generated bregman raw sum`, `BTerm`,
--   `one based shifted process`, and `Icc succ`; relevant hits were
--   `twoBlockWeightedBregmanBoundary`,
--   `twoBlockWeightedBregmanBoundary_def`, and
--   `twoBlockWeightedBregmanBoundary_eq_of_eq_on_Icc_succ`. Coverage is
--   partial: existing entries name the boundary formula and stream transport,
--   but none package the guarded raw generated-process sum as the shifted
--   two-block boundary term.
-- minimal hypotheses: all already minimal; the proof uses only membership in
--   `Finset.Icc 1 t` to discharge the guard and natural-number simplification
--   for `(i + 1) - 1`.

/-- A guarded raw generated-process Bregman sum is the shifted two-block
weighted Bregman boundary term.

The raw summand uses a zero-based generated process at times `i - 1` and `i`.
On the positive window `Icc 1 t`, this is exactly the named boundary functional
applied to the one-based sequence `i ↦ process (i - 1)`.

Layer: Layer1 | Gap: Level 0 (generated-process Bregman boundary shift)
Proof: apply `Finset.sum_congr`; interval membership discharges the positive
  time guard, and simplification rewrites the successor of the shifted sequence.
Source: Mathlib finite interval membership, finite-sum congruence, and natural
  number subtraction simplification
Used in: stochastic accelerated primal-dual generated-process Bregman boundary
  identification before weighted saddle-gap assembly
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem guarded_bregman_boundary_sum_eq_shifted_twoBlockWeightedBregmanBoundary
    {Ω X Y : Type*}
    (gamma eta tau : ℕ → ℝ)
    (VX : X → X → ℝ) (VY : Y → Y → ℝ)
    (process : ℕ → Ω → X × Y)
    (t : ℕ) (z : X × Y) (ω : Ω) :
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if _hi : 1 ≤ i then
          let stPrev := process (i - 1) ω
          let stNext := process i ω
          gamma i / eta i *
              (VX z.1 stPrev.1 - VX z.1 stNext.1) +
            gamma i / tau i *
              (VY z.2 stPrev.2 - VY z.2 stNext.2)
        else 0) =
      twoBlockWeightedBregmanBoundary gamma eta tau VX VY
        (fun i ω => process (i - 1) ω) t z ω := by
  classical
  rw [twoBlockWeightedBregmanBoundary]
  refine Finset.sum_congr rfl ?_
  intro i hiIcc
  have hi : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
  simp [hi]

end SOptLib

-- Generalization plan (G0):
-- concept/name: finite-window raw-sum decomposition with two telescoped
--   boundary components; orig was generated_eq_4461_sum_raw_telescope.
-- generality used: arbitrary finite index set and real-valued scalar
--   summands. No measure, measurability, independence, integrability,
--   convexity, smoothness, oracle, topology, Hilbert-space, or finite-dimensional
--   hypotheses are used by this assembly step.
-- portable call pattern: accelerated primal-dual, mirror-prox, and block
--   mirror-descent proofs can call this after summing one-step inequalities and
--   proving that the raw summand splits into a Bregman boundary component, a
--   coupling telescope component, and remaining square/noise penalties; the
--   schedules, iterates, residual formulas, and telescoped boundary identities
--   vary while the conclusion shape stays unchanged.
-- counterargument checked: this is ordered scalar algebra, but it is not merely
--   paper-local traceability because it packages a recurring post-telescope
--   finite-window assembly boundary. It is not a duplicate of
--   `summed_one_step_gap_bound_of_telescope`, which assumes a single descent
--   telescope and drops a nonnegative terminal tail, nor of the existing
--   Bregman-boundary identity, which rewrites only one component.
-- coverage search: searched catalog/SOptLib/Staging for `raw sum split`,
--   `boundary coupling telescope`, `summed one step telescope`, and
--   `Bregman raw sum`; relevant hits were `summed_one_step_gap_bound_of_telescope`,
--   `terminal_le_sum_of_guarded_sum_le_and_sum_eq`,
--   `guarded_bregman_boundary_sum_eq_shifted_twoBlockWeightedBregmanBoundary`,
--   and Mathlib `Finset.sum_add_distrib`/`Finset.sum_sub_distrib`. Coverage is
--   partial: existing entries cover the terminal bridge, individual telescopes,
--   or raw sum distribution, but not the combined two-identity decomposition
--   boundary used after raw one-step summation.
-- minimal hypotheses: all algorithm setup fields were reduced to four scalar
--   hypotheses: a terminal raw-sum bound, two finite-sum identities, and a
--   pointwise raw-summand split on the active index set.

/-- A terminal raw-sum bound closes after splitting the raw summand and
rewriting two telescoped boundary components.

If a terminal quantity is bounded by a finite raw sum, the raw summand splits
pointwise into Bregman, coupling, and four remainder components, and the first
two component sums have already been identified with named boundary terms, then
the terminal quantity is bounded by those boundaries minus the remainder sums.

Layer: Layer1 | Gap: Level 1 (finite-window raw-sum decomposition assembly)
Proof: rewrite the raw finite sum by `Finset.sum_congr`, distribute finite sums
  over addition and subtraction, then substitute the two supplied telescope
  identities and compose with the terminal raw-sum bound.
Source: Mathlib finite sums over ordered rings and real linear arithmetic
Used in: stochastic accelerated primal-dual post-telescope saddle-gap assembly
  after Bregman-boundary and coupling-telescope identities
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem terminal_le_boundary_add_tail_sub_sums_of_raw_split
    {ι : Type*} (s : Finset ι)
    (terminal boundary couplingTail : ℝ)
    (raw breg couplingDiff lagCross xSq ySq noise : ι → ℝ)
    (hterminal : terminal ≤ Finset.sum s raw)
    (hbreg : Finset.sum s breg = boundary)
    (hcoupling : Finset.sum s couplingDiff = couplingTail)
    (hsplit : ∀ i ∈ s,
      raw i = breg i + couplingDiff i - lagCross i - xSq i - ySq i - noise i) :
    terminal ≤
      boundary + couplingTail -
        Finset.sum s lagCross -
        Finset.sum s xSq -
        Finset.sum s ySq -
        Finset.sum s noise := by
  classical
  have hraw_split :
      Finset.sum s raw =
        Finset.sum s (fun i =>
          breg i + couplingDiff i - lagCross i - xSq i - ySq i - noise i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hsplit i hi
  have hsum_split :
      Finset.sum s raw =
        Finset.sum s breg + Finset.sum s couplingDiff -
          Finset.sum s lagCross -
          Finset.sum s xSq -
          Finset.sum s ySq -
          Finset.sum s noise := by
    calc
      Finset.sum s raw =
          Finset.sum s (fun i =>
            breg i + couplingDiff i - lagCross i - xSq i - ySq i - noise i) :=
        hraw_split
      _ =
          Finset.sum s breg + Finset.sum s couplingDiff -
            Finset.sum s lagCross -
            Finset.sum s xSq -
            Finset.sum s ySq -
            Finset.sum s noise := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc
    terminal ≤ Finset.sum s raw := hterminal
    _ =
        Finset.sum s breg + Finset.sum s couplingDiff -
          Finset.sum s lagCross -
          Finset.sum s xSq -
          Finset.sum s ySq -
          Finset.sum s noise := hsum_split
    _ =
        boundary + couplingTail -
          Finset.sum s lagCross -
          Finset.sum s xSq -
          Finset.sum s ySq -
          Finset.sum s noise := by
        rw [hbreg, hcoupling]

-- Generalization plan (G0):
-- concept/name: generated accelerated primal-dual spine one-step gap bound
--   from a raw recurrence and absorbed finite-window remainder; orig was
--   lemma_4_9_generated_spine_extension_obligation.
-- generality used: real-valued scalar quantities only. The proof uses no
--   measure, filtration, independence, integrability, convexity, smoothness,
--   oracle, topology, Hilbert-space, or finite-dimensional assumptions; those
--   belong to the component lemmas that produce the raw recurrence and
--   remainder absorption hypotheses.
-- portable call pattern: accelerated primal-dual, mirror-prox, extragradient,
--   and proximal acceleration proofs call this after a summed raw gap
--   recurrence has exposed a finite-window lag/square/noise remainder and
--   separate Young/parameter-coupling lemmas have absorbed that remainder.
--   The process, schedules, residual formulas, and boundary terms vary while
--   the final scalar handoff shape stays unchanged.
-- counterargument checked: this is close to arithmetic, but it is not a pure
--   wrapper or paper-local traceability because it packages the recurring
--   proof-composition boundary between a raw one-step gap recurrence and a
--   separately proved finite-window absorption theorem. It does not introduce
--   abstract formula-equality parameters; all named mathematical objects are
--   caller-supplied scalar terms.
-- coverage search: searched SOptLib/Staging/catalog/source for
--   `terminal_le_boundary_add_tail_sub_sums_of_raw_split`,
--   `finite_window_four_term_absorption_bridge`, `one step gap bound`,
--   `raw telescope`, and `absorption bridge`. Existing entries cover the raw
--   split and the four-term absorption separately, but not their terminal
--   composition into the final one-step gap bound.
-- minimal hypotheses: exactly the raw finite-window gap recurrence and the
--   absorbed remainder bound are assumed; no global algorithm hypotheses remain.

/-- A raw generated-spine recurrence closes once its finite-window remainder is
absorbed.

If a one-step gap quantity is bounded by a boundary term, a coupling tail, and
four unabsorbed finite-window remainder sums, and those remainder sums are
bounded by a retained terminal term plus collected residuals, then the final
one-step gap bound follows.

Layer: Layer1 | Gap: Level 1 (raw recurrence and absorption composition)
Proof: compose the raw scalar inequality with the absorbed remainder bound and
  reassociate the real terms by linear arithmetic.
Source: Mathlib ordered real linear arithmetic for finite-window descent
  estimate assembly
Used in: stochastic accelerated primal-dual generated-process one-step
  saddle-gap recursion after raw telescoping and Young/parameter absorption
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem one_step_gap_bound_of_raw_recurrence_and_remainder_bound
    (gap boundary couplingTail lagSum xSqSum ySqSum noiseSum terminal residual : ℝ)
    (hraw :
      gap ≤
        boundary + couplingTail - lagSum - xSqSum - ySqSum - noiseSum)
    (hremainder :
      -lagSum - xSqSum - ySqSum - noiseSum ≤ terminal + residual) :
    gap ≤ boundary + couplingTail + terminal + residual := by
  linarith

-- Generalization plan (G0):
-- concept/name: positive_time_recursive_process_eq_of_zero_one_eq_of_same_step.
--   The exposed concept is pathwise uniqueness for two warm-started
--   positive-time recursive state processes driven by the same call stream and
--   update rule.
-- generality used: arbitrary outcome, state, and call types; no measure,
--   filtration, independence, integrability, convexity, topology, norm, inner
--   product, smoothness, or oracle hypotheses are used.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   stochastic-gradient proofs can call this when two process presentations
--   share initialization and the same one-step update; only the state type,
--   call stream, and transition function change.
-- counterargument checked: this is more than paper-local traceability because
--   it states reusable uniqueness of a positive-time recursive process, not a
--   Lan-specific source expression. It is close to the already staged
--   shifted displayed/generated lemma, but that theorem compares indices
--   `k` and `k - 1`; this one compares two same-index processes.
-- coverage search: searched project tokens `source boundary state displayed`,
--   `warmStartedQueryDrivenStateProcess`, `positiveTimeGeneratedProcessSemantics`,
--   and `recursive process state equality step init`; LeanSearch query
--   `two recursive sequences same initial value same recurrence are equal`
--   found only generic recursion congruence and linear-recurrence facts.
--   SOptLib/Staging coverage is partial: process constructors and semantics
--   projections exist, and `displayedState_eq_generatedProcess_shift` covers
--   a shifted transport, but no existing entry states same-index uniqueness
--   for two processes with the same positive-time update.
-- minimal hypotheses: all already minimal; the proof needs exactly equality
--   at slices `0` and `1`, plus both positive-time successor equations.

namespace SOptLib

/-- Two warm-started positive-time recursive state processes with the same driver are equal.

If two processes agree at slices `0` and `1`, and every positive successor
slice is generated by the same call stream and transition from the previous
state, then they agree at every natural index and sample point.

Layer: Layer1 | Gap: Level 1 (warm-start recursive-process uniqueness)
Proof: split the two warm-start base indices, then induct on the remaining
  successor index and rewrite both processes through the shared update rule.
Source: Mathlib natural-number induction and equality rewriting APIs for
  recursive stochastic-optimization processes
Used in: stochastic accelerated primal-dual comparison of two generated-call
  process presentations before pathwise recurrence rewriting
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem positive_time_recursive_process_eq_of_zero_one_eq_of_same_step
    {Ω State Call : Type*}
    (process₁ process₂ : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (t : ℕ) → 1 ≤ t → Call → State → Ω → State)
    (hzero : ∀ ω, process₁ 0 ω = process₂ 0 ω)
    (hone : ∀ ω, process₁ 1 ω = process₂ 1 ω)
    (hleft_succ :
      ∀ (t : ℕ) (ht : 1 ≤ t) (ω : Ω),
        process₁ (t + 1) ω =
          step t ht (call t ω) (process₁ t ω) ω)
    (hright_succ :
      ∀ (t : ℕ) (ht : 1 ≤ t) (ω : Ω),
        process₂ (t + 1) ω =
          step t ht (call t ω) (process₂ t ω) ω)
    (k : ℕ) (ω : Ω) :
    process₁ k ω = process₂ k ω := by
  cases k with
  | zero =>
      exact hzero ω
  | succ k =>
      induction k with
      | zero =>
          exact hone ω
      | succ k ih =>
          calc
            process₁ (Nat.succ (Nat.succ k)) ω =
                step (k + 1) (Nat.succ_pos k) (call (k + 1) ω)
                  (process₁ (k + 1) ω) ω := by
                  simpa [Nat.succ_eq_add_one] using
                    hleft_succ (k + 1) (Nat.succ_pos k) ω
            _ =
                step (k + 1) (Nat.succ_pos k) (call (k + 1) ω)
                  (process₂ (k + 1) ω) ω := by
                  rw [ih]
            _ = process₂ (Nat.succ (Nat.succ k)) ω := by
                  simpa [Nat.succ_eq_add_one] using
                    (hright_succ (k + 1) (Nat.succ_pos k) ω).symm

end SOptLib



-- Generalization plan (G0):
-- G0.1 naming: refresh_index_not_mem_epoch_start_footprint_of_global_index_le
--   (orig was: epoch_refresh_index_not_mem_epoch_start_footprint); the staged
--   declaration keeps the requested public name
--   `refresh_index_not_mem_epoch_start_footprint_of_global_index_le` for
--   backfill compatibility, while the concept is finite sample-footprint
--   freshness for epoch refresh coordinates.
-- G0.2 typeclass level used:
--   E: no carrier space; this is natural-number sample-coordinate arithmetic.
--   measure: none; the proof is the arithmetic premise consumed before
--     finite sample-block independence.
--   convexity: none; no feasible-set or objective geometry is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, epoch-refresh sample
--      freshness before applying finite sample-block independence.
--   2. variance-reduced mirror descent or SARAH/SPIDER, proving that a fresh
--      epoch refresh mini-batch is outside the recursive-sample history block.
-- G0.4 search trace:
--   queries: ["Finset Ico range not mem",
--     "not_mem_Ico not_mem_range natural arithmetic"]
--   top hits: ["iIndepFun.indep_sampleBlock_singleton_of_not_mem",
--     "epoch_refresh_index_not_mem_epoch_start_footprint",
--     "sampleBlock_indep_singleton_of_not_mem",
--     "recursive_index_mem_epoch_start_footprint_of_lt",
--     "Finset.mem_range", "Finset.notMem_range_self"]
--   coverage: partial — SOptLib has the independence theorem once
--     out-of-block freshness is known, and Mathlib has raw range/Ico
--     membership facts, but no compound epoch-refresh footprint exclusion.
-- G0.4 not-a-thin-wrapper rationale: this packages the reusable invariant
--   that a current epoch refresh coordinate is simultaneously outside the
--   strict refresh prefix and below the recursive-sample footprint start when
--   the encoded first step of the epoch is inside the run horizon.
-- G0.5 structural-content rationale: the theorem connects the named
--   fixed-length epoch encoder, the refresh prefix, and the recursive
--   half-open footprint into one reusable sample-freshness arithmetic fact.
-- G0.5c thin-wrapper self-detect: clean — the body splits union membership
--   and derives two independent arithmetic contradictions rather than
--   re-exporting a single Mathlib or SOptLib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; `1 ≤ T` is used only
--   to derive `s + 1 ≤ global_index T s 1`, `hi` is pointwise membership in
--   the refresh mini-batch, and `hsN` is the horizon bound at this epoch.

open scoped BigOperators

/-- A current epoch refresh coordinate is outside the epoch-start sample footprint.

For a fixed epoch length `T`, a refresh mini-batch coordinate `i < m` at epoch
`s` is not in the finite footprint made from earlier refresh coordinates and
recursive sample coordinates, provided the epoch's first encoded global step is
within the run horizon.

Layer: Layer1 | Gap: Level 1 (epoch refresh sample-footprint freshness)
Proof: split membership in the union. The range branch contradicts
  `s*m ≤ s*m+i`, while the `Ico` branch contradicts `s*m+i < N*m`, obtained
  from `i < m`, `1 ≤ T`, and `global_index T s 1 ≤ N`.
Source: Mathlib finite-set interval membership and natural-number arithmetic APIs
Used in: stochastic variance-reduced conditional-gradient epoch-refresh sample
  freshness before finite sample-block independence
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem refresh_index_not_mem_epoch_start_footprint_of_global_index_le
    {T N m b s i : ℕ}
    (hT_pos : 1 ≤ T)
    (hi : i ∈ Finset.range m)
    (hsN : SOptLib.global_index T s 1 ≤ N) :
    s * m + i ∉
      (Finset.range (s * m) ∪
        Finset.Ico (N * m) (N * m + SOptLib.global_index T s 1 * b)) := by
  intro hmem
  rw [Finset.mem_union] at hmem
  rcases hmem with hprev | hrec
  · have hidx_ge : s * m ≤ s * m + i := Nat.le_add_right _ _
    have hidx_lt : s * m + i < s * m := Finset.mem_range.mp hprev
    omega
  · have hi_lt : i < m := Finset.mem_range.mp hi
    have hs_succ_le_global : s + 1 ≤ SOptLib.global_index T s 1 := by
      rw [SOptLib.global_index]
      have hs_le_sT : s ≤ s * T := by
        simpa using Nat.mul_le_mul_left s hT_pos
      omega
    have hs_le_N : s + 1 ≤ N := le_trans hs_succ_le_global hsN
    have hleft_lt_Nm : s * m + i < N * m := by
      have hlt_succ : s * m + i < (s + 1) * m := by
        nlinarith
      have hsucc_le : (s + 1) * m ≤ N * m :=
        Nat.mul_le_mul_right m hs_le_N
      exact lt_of_lt_of_le hlt_succ hsucc_le
    have hright_ge_Nm : N * m ≤ s * m + i :=
      (Finset.mem_Ico.mp hrec).1
    omega



-- Generalization plan (G0):
-- G0.1 naming: epoch_start_sample_footprint_subset_succ (orig was:
--   epoch_start_footprint_subset_next); the name keeps the mathematical object
--   `epochStartSampleFootprint` visible while the suffix states the subset
--   property across successor epochs.
-- G0.2 typeclass level used:
--   E: no carrier space; this is natural-number finite-sample index arithmetic.
--   measure: none; this is the deterministic footprint inclusion consumed
--     before finite sample-block independence.
--   convexity: none; no feasible-set or objective geometry is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, carrying epoch-start
--      measurable sample footprints from one epoch boundary to the next.
--   2. variance-reduced mirror descent or SARAH/SPIDER, extending the
--      accumulated refresh-plus-recursive sample history at epoch boundaries.
-- G0.4 search trace:
--   queries: ["epoch start footprint subset",
--     "Finset range Ico union subset monotone"]
--   top hits: ["dense_subtype_of_subset_closure",
--     "validationStrictErrorEvent_subset_validationErrorEvent",
--     "iIndepFun.indepFun_finset_subtype_blocks",
--     "Finset.mem_range", "Finset.mem_Ico"]
--   coverage: partial — SOptLib has finite-block independence and Mathlib has
--     raw `range`/`Ico` membership facts, but no theorem packages successor
--     monotonicity for a refresh-prefix plus recursive-sample footprint.
-- G0.4 not-a-thin-wrapper rationale: this packages the reusable invariant that
--   both the refresh prefix and the recursive half-open sample block are
--   monotone when the epoch-start recursive cutoff is monotone.
-- G0.5 structural-content rationale: the theorem connects two finite-set
--   constructors into a single footprint inclusion used by sample-history
--   measurability and independence arguments.
-- G0.5c thin-wrapper self-detect: clean — the body splits union membership,
--   transfers the `range` branch through refresh-prefix monotonicity, and
--   transfers the `Ico` branch through cutoff monotonicity.
-- G0.5d minimal-hypothesis check: all already minimal; the only nontrivial
--   hypothesis is pointwise monotonicity of the recursive-sample cutoff from
--   `s` to `s + 1`.

open scoped BigOperators

/-- The epoch-start finite sample footprint is monotone across successor epochs.

If the recursive-sample cutoff encoded by `globalIndex · 1` is monotone from
epoch `s` to epoch `s+1`, then the finite footprint made of the refresh prefix
and recursive half-open sample block at epoch `s` is contained in the
corresponding footprint at epoch `s+1`.

Layer: Layer1 | Gap: Level 1 (successor monotonicity of epoch sample footprints)
Proof: split membership in the union. The refresh-prefix branch uses
  monotonicity of multiplication by `m`, while the recursive half-open branch
  uses monotonicity of the encoded cutoff after multiplication by `b`.
Source: Mathlib finite-set interval membership and natural-number order APIs
Used in: stochastic variance-reduced conditional-gradient epoch-boundary
  measurability of accumulated refresh and recursive sample histories
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epoch_start_sample_footprint_subset_succ
    {N m b : ℕ} {globalIndex : ℕ → ℕ → ℕ} (s : ℕ)
    (hglobal : globalIndex s 1 ≤ globalIndex (s + 1) 1) :
    (Finset.range (s * m) ∪
        Finset.Ico (N * m) (N * m + globalIndex s 1 * b)) ⊆
      (Finset.range ((s + 1) * m) ∪
        Finset.Ico (N * m) (N * m + globalIndex (s + 1) 1 * b)) := by
  intro q hq
  rw [Finset.mem_union] at hq ⊢
  rcases hq with hprev | hrec
  · left
    have hlt : q < s * m := Finset.mem_range.mp hprev
    have hle : s * m ≤ (s + 1) * m :=
      Nat.mul_le_mul_right m (Nat.le_succ s)
    exact Finset.mem_range.mpr (lt_of_lt_of_le hlt hle)
  · right
    have hrec' := Finset.mem_Ico.mp hrec
    exact Finset.mem_Ico.mpr ⟨hrec'.1, by
      have hmul :
          globalIndex s 1 * b ≤ globalIndex (s + 1) 1 * b :=
        Nat.mul_le_mul_right b hglobal
      omega⟩



open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: estimator_at_epoch_start_eq_refresh_minibatch (orig was:
--   estimatorProcessOfWellDefined_globalIndex_one_eq_refresh_average); the new
--   name states the variance-reduced estimator invariant without the paper-local
--   well-definedness wrapper or `globalIndex` notation.
-- G0.2 typeclass level used:
--   E: [AddCommMonoid E] [Sub E] [SMul ℝ E]; the proof only uses finite sums,
--      subtraction in the process's recursive branch, and real scalar mini-batch
--      weights. No norm, topology, inner product, completeness, or finite dimension is used.
--   measure: none; this is a pathwise process identity before probability,
--      filtration, measurability, independence, or integrability assumptions enter.
--   convexity: none; the refresh estimator identity does not mention a feasible set.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient epoch-refresh estimator identities
--   2. SARAH/SVRG-style stochastic gradient or mirror-descent refresh steps with
--      sampled mini-batch resets and recursive within-epoch estimator updates
-- G0.4 search trace:
--   queries: ["epoch start estimator refresh minibatch",
--     "globalIndex one refresh average estimator",
--     "variance reduced process epoch refresh estimator"]
--   top hits: ["estimatorProcess_epochStart_eq_target",
--     "estimatorProcessOfWellDefined_globalIndex_one_eq_refresh_average",
--     "varianceReducedConditionalGradientProcess_one_estimator",
--     "varianceReducedConditionalGradientProcess",
--     "varianceReducedConditionalGradientProcess_succ_succ"]
--   coverage: partial — the exact-refresh theorem targets deterministic finite-sum
--     resets, and the process unfoldings cover only single indices; this theorem adds
--     the all-epoch sampled mini-batch refresh identity `s*T+1 ↦ s*m+i`.
-- G0.4 not-a-thin-wrapper rationale: the proof combines the named variance-reduced
--   process, its derived epoch-counter invariant, epoch-index arithmetic, modulo
--   branch identification, and state projection transport to expose the reusable
--   sampled-refresh invariant.
-- G0.5 structural-content rationale: this theorem upgrades local process unfolding
--   rules into an all-epoch estimator identity indexed by the outer-loop counter
--   and proves the needed stored-counter arithmetic along the way.
-- G0.5c thin-wrapper self-detect: clean — body has case analysis, natural-number
--   arithmetic, refresh-branch selection, and projection rewriting.
-- G0.5d minimal-hypothesis check: all already minimal; `hT_pos` is only the
--   pointwise positivity needed for the epoch-boundary modulo calculation.

namespace SOptLib

/-- A sampled-refresh variance-reduced estimator equals its epoch mini-batch at every epoch start.

For the variance-reduced conditional-gradient state process, the estimator
component at index `s*T+1` is the refresh mini-batch average evaluated at the
iterate component at the same index, using sample coordinates `s*m+i`.

Layer: Layer1 | Gap: Level 1 (sampled-refresh estimator epoch-start identity)
Proof: split the initial epoch from positive epochs. Positive epochs rewrite
  `s*T+1` as a successor-after-successor index, identify the modulo refresh
  branch with `Nat.mul_mod_right`, and simplify the state constructor accessors.
Source: Mathlib natural-number arithmetic and variance-reduced finite-sum recursions
Used in: stochastic nonconvex conditional-gradient refresh residual centering
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem estimator_at_epoch_start_eq_refresh_minibatch
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (hstateX_mk : ∀ x G s, stateX (mkState x G s) = x)
    (hstateEstimator_mk : ∀ x G s, stateEstimator (mkState x G s) = G)
    (hstateEpoch_mk : ∀ x G s, stateEpoch (mkState x G s) = s)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E)
    (hT_pos : 1 ≤ T)
    (s : ℕ) :
    (fun ω =>
        stateEstimator
          (varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
            x0 m b T N sample gradF update (s * T + 1) ω)) =
      fun ω =>
        (m : ℝ)⁻¹ •
          Finset.sum (Finset.range m)
            (fun i =>
              gradF
                (stateX
                  (varianceReducedConditionalGradientProcess
                    mkState stateX stateEstimator stateEpoch
                    x0 m b T N sample gradF update (s * T + 1) ω))
                (sample (s * m + i) ω)) := by
  have h_succ_epoch :
      ∀ k : ℕ, ∀ ω : Ω,
        stateEpoch
            (varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
              x0 m b T N sample gradF update (k + 1) ω) =
          k / T := by
    intro k ω
    induction k with
    | zero =>
        rw [varianceReducedConditionalGradientProcess_one]
        simp [hstateEpoch_mk]
    | succ k ih =>
        by_cases hdiv : T ∣ k + 1
        · have hmod : ((((k + 1) % T == 0)) = true) := by
            simp [Nat.mod_eq_zero_of_dvd hdiv]
          rw [varianceReducedConditionalGradientProcess_succ_succ]
          simp [-varianceReducedConditionalGradientProcess_def, hmod, hstateEpoch_mk,
            ih, Nat.succ_div_of_dvd hdiv]
        · have hmod_ne : (k + 1) % T ≠ 0 := by
            intro hmod_zero
            exact hdiv (Nat.dvd_of_mod_eq_zero hmod_zero)
          have hmod : ((((k + 1) % T == 0)) = false) := by
            simp [hmod_ne]
          rw [varianceReducedConditionalGradientProcess_succ_succ]
          simp [-varianceReducedConditionalGradientProcess_def, hmod, hstateEpoch_mk,
            ih, Nat.succ_div_of_not_dvd hdiv]
  funext ω
  cases s with
  | zero =>
      simp only [Nat.zero_mul, zero_add]
      rw [varianceReducedConditionalGradientProcess_one]
      simp [hstateX_mk, hstateEstimator_mk]
  | succ r =>
      have hprod_pos : 0 < (r + 1) * T := by
        exact Nat.mul_pos (Nat.succ_pos r) (Nat.lt_of_lt_of_le Nat.zero_lt_one hT_pos)
      have hpred_add : ((r + 1) * T - 1) + 1 = (r + 1) * T := by
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hprod_pos)
      have hidx : (r + 1) * T + 1 = ((r + 1) * T - 1) + 2 := by
        omega
      have hmod : (((((r + 1) * T - 1) + 1) % T == 0) = true) := by
        have hzero : ((r + 1) * T) % T = 0 := by
          rw [Nat.mul_comm]
          exact Nat.mul_mod_right T (r + 1)
        simp [hpred_add, hzero]
      have hdiv_prev : (((r + 1) * T - 1) / T = r) := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · have hlt_mul : r * T < (r + 1) * T :=
            Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self r)
              (Nat.lt_of_lt_of_le Nat.zero_lt_one hT_pos)
          exact Nat.le_pred_of_lt hlt_mul
        · exact Nat.pred_lt (Nat.ne_of_gt hprod_pos)
      have hs_prev :
          stateEpoch
              (varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
                x0 m b T N sample gradF update (((r + 1) * T - 1) + 1) ω) +
            1 =
          r + 1 := by
        have hs := h_succ_epoch (((r + 1) * T - 1)) ω
        rw [hdiv_prev] at hs
        simpa only [Nat.succ_eq_add_one] using congrArg Nat.succ hs
      rw [hidx]
      rw [varianceReducedConditionalGradientProcess_succ_succ]
      simp [-varianceReducedConditionalGradientProcess_def, hmod, hstateX_mk,
        hstateEstimator_mk, hs_prev]

end SOptLib



-- Generalization plan (G0):
-- G0.1 naming: recursive_estimator_residual_eq_prev_add_centered_batch_diff_of_not_epoch_start
--   (orig was: estimatorResidual_recursive_of_not_epochStart); the name describes
--   the variance-reduced estimator residual recursion away from epoch refreshes,
--   not a paper-local delta-process theorem.
-- G0.2 typeclass level used:
--   E: [AddCommGroup E] [Module ℝ E]; the proof uses subtraction, addition,
--      finite sums, and real scalar multiplication by a batch-cardinality
--      inverse. It does not use norm, topology, inner product, completeness, or
--      finite-dimensionality.
--   measure: none; the identity is pathwise before probability, filtration,
--      independence, integrability, or conditional expectation is used.
--   convexity: none; no feasible-set, objective-geometry, or smoothness
--      hypothesis is involved in this algebraic residual recursion.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional-gradient recursive estimator residuals
--      before the centered mini-batch variance bound in Lemma 7.5.
--   2. SARAH/SPIDER-style stochastic gradient and mirror-descent estimator
--      drift recursions inside non-refresh epoch steps.
-- G0.4 search trace:
--   queries: ["estimator residual recursive centered",
--     "recursive estimator update mini batch target difference"]
--   top hits: ["recursive_estimator_residual_global_index_eq_prev_add_centered_batch_diff",
--     "estimatorResidualProcess_succ_eq_of_estimator_update",
--     "process_recursive_average_sub_target_eq_average_residual",
--     "miniBatchAverage_sub_target_eq_average_residual",
--     "recursiveGradientDifferenceAverage"]
--   coverage: partial — existing hits cover global-index transport, a one-step
--     residual update, or finite-average centering separately; none states the
--     successor-time non-refresh theorem that derives both raw and centered
--     residual recursions from an abstract recursive mini-batch estimator update.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   linking a non-refresh estimator update, the named residual process, and the
--   centered mini-batch residual-average form in one successor-time statement.
-- G0.5 structural-content rationale: the paired conclusion lets algorithm
--   proofs keep their displayed raw recursion while exposing the centered
--   residual-average increment consumed by second-moment and cancellation APIs.
-- G0.5c thin-wrapper self-detect: clean — body composes the estimator-residual
--   update theorem with recursive mini-batch centering and instantiates both
--   with the same non-refresh mini-batch update.
-- G0.5d minimal-hypothesis check: the update hypothesis and batch-cardinality
--   hypothesis are pointwise at the active non-refresh successor time; positivity
--   of the shared batch size is the only global numeric side condition.

namespace SOptLib

/-- A non-refresh recursive estimator update gives raw and centered residual recursions.

If an estimator advances away from epoch starts by adding a finite mini-batch
average of paired oracle differences, then its residual relative to a target
field advances both as `average - target difference` and as the average of
centered paired differences.

Layer: Layer1 | Gap: Level 1 (non-refresh recursive estimator residual centering)
Proof: apply the one-step estimator-residual update to the recursive mini-batch
  estimator update, then rewrite the resulting `average - target difference`
  increment by the finite mini-batch residual-centering lemma.
Source: Mathlib finite sums, real module algebra, and additive-group cancellation
Used in: stochastic nonconvex conditional-gradient recursive estimator residual
  decomposition before centered mini-batch second-moment control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem recursive_estimator_residual_eq_prev_add_centered_batch_diff_of_not_epoch_start
    {Ω ι X S E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (batch : ℕ → Finset ι)
    (k : ℕ) (hbatch_card : (batch (k + 1)).card = m) (hmpos : 0 < m)
    (estimator : ℕ → Ω → E) (iterate : ℕ → Ω → X)
    (oracle : X → S → E) (target : X → E) (sample : ℕ → ι → Ω → S)
    (hupdate : ∀ ω,
      estimator (k + 2) ω =
        estimator (k + 1) ω +
          ((m : ℝ)⁻¹) •
            Finset.sum (batch (k + 1))
              (fun i =>
                oracle (iterate (k + 2) ω) (sample (k + 1) i ω) -
                  oracle (iterate (k + 1) ω) (sample (k + 1) i ω)))
    :
    (∀ ω,
      estimatorResidualProcess estimator iterate target (k + 2) ω =
        estimatorResidualProcess estimator iterate target (k + 1) ω +
          ((m : ℝ)⁻¹) •
            Finset.sum (batch (k + 1))
              (fun i =>
                oracle (iterate (k + 2) ω) (sample (k + 1) i ω) -
                  oracle (iterate (k + 1) ω) (sample (k + 1) i ω)) -
          (target (iterate (k + 2) ω) - target (iterate (k + 1) ω))) ∧
    (∀ ω,
      estimatorResidualProcess estimator iterate target (k + 2) ω =
        estimatorResidualProcess estimator iterate target (k + 1) ω +
          ((m : ℝ)⁻¹) •
            Finset.sum (batch (k + 1))
              (fun i =>
                (oracle (iterate (k + 2) ω) (sample (k + 1) i ω) -
                    oracle (iterate (k + 1) ω) (sample (k + 1) i ω)) -
                  (target (iterate (k + 2) ω) - target (iterate (k + 1) ω)))) := by
  have hraw :
      ∀ ω,
        estimatorResidualProcess estimator iterate target (k + 2) ω =
          estimatorResidualProcess estimator iterate target (k + 1) ω +
            ((m : ℝ)⁻¹) •
              Finset.sum (batch (k + 1))
                (fun i =>
                  oracle (iterate (k + 2) ω) (sample (k + 1) i ω) -
                    oracle (iterate (k + 1) ω) (sample (k + 1) i ω)) -
            (target (iterate (k + 2) ω) - target (iterate (k + 1) ω)) := by
    intro ω
    simp [estimatorResidualProcess, hupdate ω]
    abel
  have hcenter :
      ∀ ω,
        estimatorResidualProcess estimator iterate target (k + 2) ω =
          estimatorResidualProcess estimator iterate target (k + 1) ω +
            ((m : ℝ)⁻¹) •
              Finset.sum (batch (k + 1))
                (fun i =>
                  (oracle (iterate (k + 2) ω) (sample (k + 1) i ω) -
                      oracle (iterate (k + 1) ω) (sample (k + 1) i ω)) -
                    (target (iterate (k + 2) ω) - target (iterate (k + 1) ω))) :=
    process_recursive_average_sub_target_eq_average_residual
      (I := batch (k + 1)) (m := m) (hmcard := hbatch_card)
      (hmpos := hmpos)
      (process := estimatorResidualProcess estimator iterate target)
      (prev := k + 1) (curr := k + 2)
      (a := fun i ω =>
        oracle (iterate (k + 2) ω) (sample (k + 1) i ω) -
          oracle (iterate (k + 1) ω) (sample (k + 1) i ω))
      (target := fun ω => target (iterate (k + 2) ω) - target (iterate (k + 1) ω))
      hraw
  exact ⟨hraw, hcenter⟩

end SOptLib



-- Generalization plan (G0):
-- G0.1 naming: one_step_gap_bound_with_epoch_budget_of_delta_second_moment
--   (orig was: oneStepGap_bound_with_epochBudget_of_deltaSecondMoment)
-- G0.2 typeclass level used:
--   E: none; the estimator residual norm square and Wolfe-gap expectation have
--     already been reduced to scalar real quantities.
--   measure: none; integration is consumed by the input scalar one-step and
--     second-moment hypotheses.
--   convexity: none; smoothness, feasibility, and conditional-gradient geometry
--     enter only through the scalar base gap bound.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, replacing a residual
--      second-moment term by an epoch-difference budget in the one-step
--      expected Wolfe-gap bound.
--   2. variance-reduced Frank-Wolfe or proximal-gradient inner-loop analyses,
--      where an estimator-error second moment is first bounded by an epoch
--      drift budget and then substituted into a one-step descent inequality.
-- G0.4 search trace:
--   queries: ["one step gap epoch budget", "delta second moment epoch budget bound"]
--   top hits: ["summed_one_step_gap_bound_of_telescope",
--     "window_pathwise_bound_of_jensen_and_summed_one_step",
--     "block_mirror_descent_one_step_aggregate_recursion",
--     "dualNorm_mean_sq_le_second_moment_bound",
--     "selected_block_second_moment_integral_le_sum_bounds",
--     "miniBatchAverage_secondMoment_le_variance_div_card"]
--   coverage: partial — hits cover finite-window telescoping and oracle
--     second-moment estimates, but none subsumes the scalar substitution of a
--     delta second-moment term inside a one-step gap inequality by an
--     epoch-budget term with the `1 / L` to `L / b` coefficient change.
-- G0.4 not-a-thin-wrapper rationale: packages the reusable invariant that a
--   one-step gap bound remains valid after a residual second-moment estimate is
--   scaled by the descent coefficient and rewritten as an epoch budget.
-- G0.5 structural-content rationale: the theorem combines order-preserving
--   scaling by a positive smoothness reciprocal, field normalization of the
--   smoothness/batch coefficient, and transitive substitution into the base
--   one-step gap inequality.
-- G0.5b name-body alignment: the name promises an epoch-budget replacement for
--   a delta second-moment term in a one-step gap bound, and the theorem proves
--   exactly that scalar replacement.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step algebraic content
--   and is not a direct alias of any searched Mathlib or SOptLib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; `0 < L` is used for
--   monotone scaling and `b ≠ 0` is used only for the coefficient field
--   normalization.

/-- Replace the delta second-moment term in a one-step gap bound by an epoch budget.

If a base one-step expected gap bound contains `(1 / L) * deltaSq`, and the
delta second moment is bounded by `(L ^ 2 / b) * epochBudget`, then the same
one-step bound holds with the epoch-budget term `(L / b) * epochBudget`.

Layer: Layer1 | Gap: Level 1 (one-step residual second-moment budget substitution)
Proof: scale the second-moment estimate by the nonnegative reciprocal
  smoothness coefficient, normalize the resulting field coefficient, and
  substitute the scaled estimate into the base one-step gap inequality.
Source: Mathlib ordered-field arithmetic and monotone multiplication APIs over `ℝ`
Used in: stochastic nonconvex conditional-gradient one-step expected Wolfe-gap
  bound after replacing estimator residual variance by an epoch-difference budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem one_step_gap_bound_with_epoch_budget_of_delta_second_moment
    (lhs drop deltaSq epochBudget alphaSqTerm L b : ℝ)
    (hbase : lhs ≤ drop + (1 / L) * deltaSq + alphaSqTerm)
    (hdelta : deltaSq ≤ (L ^ 2 / b) * epochBudget)
    (hL_pos : 0 < L)
    (hb_ne : b ≠ 0) :
    lhs ≤ drop + (L / b) * epochBudget + alphaSqTerm := by
  have hcoef_nonneg : 0 ≤ (1 / L : ℝ) := by
    simpa [one_div] using inv_nonneg.mpr (le_of_lt hL_pos)
  have hdelta_scaled :
      (1 / L) * deltaSq ≤ (L / b) * epochBudget := by
    have hmul := mul_le_mul_of_nonneg_left hdelta hcoef_nonneg
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    calc
      (1 / L) * deltaSq
          ≤ (1 / L) * ((L ^ 2 / b) * epochBudget) := hmul
      _ = (L / b) * epochBudget := by
        field_simp [hL_ne, hb_ne]
  linarith



-- Generalization plan (G0):
-- G0.1 naming: conditional_gradient_update_diff_sq_le_alpha_sq_diameter_sq
-- G0.2 typeclass level used:
--   E: [SeminormedAddCommGroup E] [NormedSpace ℝ E]; the proof only uses
--      vector subtraction, real scalar multiplication, and `norm_smul`.
--   measure: none; this is a deterministic pathwise update estimate.
--   convexity: none; feasibility has already been compressed into a pointwise
--      diameter bound between the two points used in the update.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, bounding generated
--      within-epoch iterate differences by the feasible-set diameter.
--   2. finite-sum variance-reduced conditional gradient, converting a
--      Frank-Wolfe update identity into the epoch-difference square budget.
-- G0.4 search trace:
--   queries: ["update difference diameter", "norm smul sub squared le diameter"]
--   top hits: ["finite_epochDifference_form_scalar_budget_theorem716",
--     "integrable_sq_norm_sub_of_measurable_mem_diameter_bound",
--     "norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq",
--     "norm_le_ref_norm_add_lipschitz_mul_diam"]
--   coverage: partial — hits cover epoch aggregation, L2 integrability, finite
--      averages, or Lipschitz-diameter norm bounds, but none packages a
--      conditional-gradient affine update identity into a squared displacement
--      bound.
-- G0.4 not-a-thin-wrapper rationale: the statement packages the reusable
--   invariant "Frank-Wolfe affine update displacement equals `α • (y - x)`,
--   hence its squared norm is bounded by `α^2` times the feasible diameter
--   squared" from the update identity, scalar norm rule, diameter domination,
--   and square monotonicity.
-- G0.5 structural-content rationale: this theorem exposes the algorithm-level
--   update frame without paper setup fields or epoch indices.
-- G0.5c thin-wrapper self-detect: clean — body combines norm-scalar algebra,
--   a pointwise diameter hypothesis, nonnegativity, and real square arithmetic.
-- G0.5d minimal-hypothesis check: all already minimal; the update and diameter
--   hypotheses are pointwise at the single step used.

open scoped BigOperators

/-- A conditional-gradient affine update has squared displacement at most
`α^2` times a diameter bound.

If a step satisfies `xnext - x = α • (y - x)`, the step size is nonnegative,
and the selected feasible displacement is bounded by `D`, then the squared
norm of the realized displacement is bounded by `α^2 * D^2`.

Layer: Layer1 | Gap: Level 0 (conditional-gradient affine update diameter step bound)
Proof: rewrite the displacement with the update identity, use `norm_smul` and
  the pointwise diameter bound, then square the resulting nonnegative scalar
  inequality.
Source: Frank-Wolfe conditional-gradient affine update algebra and Mathlib normed-space scalar norm APIs
Used in: stochastic and finite-sum nonconvex conditional-gradient epoch-difference square budgets
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic nonconvex conditional gradient -/
theorem conditional_gradient_update_diff_sq_le_alpha_sq_diameter_sq
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x xnext y : E) (α D : ℝ)
    (hα_nonneg : 0 ≤ α)
    (hupdate : xnext - x = α • (y - x))
    (hdiam : ‖y - x‖ ≤ D) :
    ‖xnext - x‖ ^ 2 ≤ α ^ 2 * D ^ 2 := by
  have hnorm_le :
      ‖xnext - x‖ ≤ α * D := by
    rw [hupdate, norm_smul, Real.norm_of_nonneg hα_nonneg]
    exact mul_le_mul_of_nonneg_left hdiam hα_nonneg
  have hleft_nonneg : 0 ≤ ‖xnext - x‖ := norm_nonneg _
  have hD_nonneg : 0 ≤ D := le_trans (norm_nonneg _) hdiam
  have hright_nonneg : 0 ≤ α * D := mul_nonneg hα_nonneg hD_nonneg
  calc
    ‖xnext - x‖ ^ 2 ≤ (α * D) ^ 2 := by
      nlinarith
    _ = α ^ 2 * D ^ 2 := by
      ring



-- Generalization plan (G0):
-- G0.1 naming: epoch_delta_sq_integrable_of_recursive_step
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E]; only the norm on residuals is mentioned.
--      No scalar multiplication, inner product, completeness, or finite dimension is used.
--   measure: arbitrary Measure μ on a measurable space; no finiteness or probability property is used.
--   convexity: none.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, epochwise estimator residual L2 invariant
--   2. variance-reduced mirror descent, recursive residual square-integrability within epochs
-- G0.4 search trace:
--   queries: ["epoch delta square integrable recursive",
--     "Integrable norm square Nat induction recursive step"]
--   top hits: ["integrable_inner_of_integrable_sq_norm",
--     "integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one",
--     "integrable_of_integrable_norm_sq", "integrable_sq_norm_centeredMiniBatchAverage",
--     "integrable_sq_oracleResidual_of_indep_fixed_variance_bound",
--     "adapted_iterate_of_recursive_adapted_update",
--     "second_moment_add_recurrence_le_of_cross_zero"]
--   coverage: partial — hits supply L2 closure or one-step recurrence ingredients,
--     but none packages induction over an epoch-local Nat index under prefix-closed validity.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable invariant
--   that a base L2 residual and one-step L2 propagation imply all valid epoch
--   residuals are L2, including the prefix-validity bookkeeping needed by generated runs.
-- G0.5 structural-content rationale: no structure or def is introduced; the
--   theorem exposes a load-bearing induction principle for recursive stochastic estimators.
-- G0.5c thin-wrapper self-detect: clean — body performs Nat induction with base,
--   prefix-validity transport, and recursive-step specialization.
-- G0.5d minimal-hypothesis check: all already minimal; validity is pointwise at
--   the terminal epoch coordinate and transported only to predecessors.

open MeasureTheory

/-- Square-integrability propagates through every valid step of an epoch recurrence.

If epoch coordinates have a prefix-closed validity predicate, the first residual
is square-integrable, and each valid step `j ≥ 2` propagates square-integrability
from `j - 1` to `j`, then every valid coordinate in the epoch is square-integrable.

Layer: Layer1 | Gap: Level 1 (epoch residual L2 induction)
Proof: induction on the epoch-local index. The base case uses the supplied
  first-coordinate square-integrability, and the successor case transports
  prefix validity to the predecessor before applying the recursive step.
Source: Mathlib natural-number induction and measure-theory integrability APIs
Used in: stochastic conditional-gradient recursive estimator residual L2 invariant
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epoch_delta_sq_integrable_of_recursive_step
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (delta : ℕ → Ω → E) (index : ℕ → ℕ → ℕ)
    (Valid : ℕ → ℕ → Prop) (T : ℕ)
    (hvalid_prefix :
      ∀ {s i j : ℕ}, i ≤ j → Valid s j → Valid s i)
    (hbase :
      ∀ s : ℕ, Valid s 1 →
        Integrable (fun ω => ‖delta (index s 1) ω‖ ^ 2) μ)
    (hstep :
      ∀ s j : ℕ, 2 ≤ j → j ≤ T → Valid s j →
        Integrable (fun ω => ‖delta (index s (j - 1)) ω‖ ^ 2) μ →
        Integrable (fun ω => ‖delta (index s j) ω‖ ^ 2) μ)
    (s t : ℕ) (ht : 1 ≤ t) (ht_le : t ≤ T) (hvalid : Valid s t) :
    Integrable (fun ω => ‖delta (index s t) ω‖ ^ 2) μ := by
  induction t with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hbase s hvalid
      · have hn_pos : 1 ≤ n := by omega
        have hj2 : 2 ≤ n + 1 := by omega
        have hn_le_t : n ≤ n + 1 := by omega
        have hn_le_T : n ≤ T := by omega
        have hprev_valid : Valid s n :=
          hvalid_prefix hn_le_t hvalid
        have hprev_sq :
            Integrable (fun ω => ‖delta (index s n) ω‖ ^ 2) μ :=
          ih hn_pos hn_le_T hprev_valid
        simpa using
          hstep s (n + 1) hj2 ht_le hvalid hprev_sq



open MeasureTheory

-- Generalization plan (G0):
-- G0.1 naming: within_epoch_iterate_measurable_before_recursive_mini_batch
--   (orig was: finite_iterProcess_globalIndex_measurable_recursive_cutoff);
--   the name describes the within-epoch predictable-iterate measurability
--   property before the recursive mini-batch sample block.
-- G0.2 typeclass level used:
--   E: arbitrary measurable state and estimator spaces X/G; no norm, topology,
--      inner product, convexity, or finite-dimensionality is used.
--   measure: none; the proof is filtration measurability only and does not
--      use a probability measure or independence.
--   convexity: none; the update measurability hypothesis abstracts the
--      deterministic optimization update without feasible-set geometry.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient recursive estimator
--      measurability before a fresh inner mini-batch.
--   2. SARAH/SPIDER or variance-reduced mirror descent inner-loop iterate
--      measurability before sampling the next recursive gradient-difference batch.
-- G0.4 search trace:
--   queries: ["within epoch measurable iterate", "measurable fst pair filtration",
--     "measurable first projection of measurable pair",
--     "measurable adapted recursive process before next sample block filtration"]
--   top hits: ["iterate_measurable_of_process_measurable_strictPast",
--     "recursive_process_pair_measurable_at_sample_cutoff_of_refresh_or_minibatch",
--     "adapted_iterate_of_recursive_adapted_update",
--     "adapted_iterate_of_recursive_sample_update",
--     "measurable_fst", "Measurable.fst", "MeasureTheory.Adapted.measurable_le"]
--   coverage: partial — projection and generic adaptedness hits do not subsume
--     the fixed-length within-epoch index arithmetic that rewrites
--     `globalIndex T s j` to the non-refresh update after `globalIndex T s (j-1)`.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the recurring
--   variance-reduced invariant combining pair measurability at sample cutoffs,
--   update measurability, non-refresh update unfolding, and fixed-epoch index
--   arithmetic.
-- G0.5 structural-content rationale: the statement exposes a reusable
--   predictable-iterate-before-fresh-mini-batch invariant over arbitrary
--   measurable state and estimator spaces.
-- G0.5c thin-wrapper self-detect: clean — body performs index arithmetic,
--   cutoff/pair projection, update measurability, and recursive update rewriting.
-- G0.5d minimal-hypothesis check: all already minimal; pair measurability,
--   update measurability, and update equality are pointwise at the exact
--   cutoff/time used.

/-- A within-epoch recursive iterate is measurable before the fresh mini-batch.

For a fixed-length epoch schedule, if each iterate-estimator pair is measurable
at its sample cutoff and non-refresh steps update the iterate from the previous
measurable pair, then an inner-loop iterate `globalIndex T s j` with `2 ≤ j ≤ T`
is measurable at the previous inner step's sample cutoff.

Layer: Layer1 | Gap: Level 1 (within-epoch predictable iterate measurability)
Proof: identify `globalIndex T s j` as the non-refresh successor of
  `globalIndex T s (j - 1)`, project the previous iterate and estimator from
  pair measurability, apply the measurable update hypothesis, and rewrite the
  recursive update equation.
Source: Mathlib filtration measurability, product projection, and natural-number
  epoch-index arithmetic APIs
Used in: variance-reduced conditional-gradient recursive mini-batch
  measurability before fresh sample blocks
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem within_epoch_iterate_measurable_before_recursive_mini_batch
    {Ω X G : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace G]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (T b N : ℕ)
    (iter : ℕ → Ω → X)
    (estimator : ℕ → Ω → G)
    (update : X → G → ℕ → X)
    (h_pair :
      ∀ k, k ≤ N →
        Measurable[filt.seq (k * b)] (fun ω => (iter k ω, estimator k ω)))
    (h_update_meas :
      ∀ {cutoff n},
        Measurable[filt.seq cutoff] (iter n) →
        Measurable[filt.seq cutoff] (estimator n) →
        Measurable[filt.seq cutoff]
          (fun ω => update (iter n ω) (estimator n ω) n))
    (h_iter_update :
      ∀ n, (n + 1) % T ≠ 0 →
        iter (n + 2) =
          fun ω => update (iter (n + 1) ω) (estimator (n + 1) ω) (n + 1))
    (s j : ℕ) (hj2 : 2 ≤ j) (hjT : j ≤ T)
    (hjN : SOptLib.global_index T s j ≤ N) :
    Measurable[filt.seq (SOptLib.global_index T s (j - 1) * b)]
      (iter (SOptLib.global_index T s j)) := by
  let k := SOptLib.global_index T s (j - 1) - 1
  have hk1 : k + 1 = SOptLib.global_index T s (j - 1) := by
    dsimp [k]
    simp [SOptLib.global_index]
    omega
  have hk2 : k + 2 = SOptLib.global_index T s j := by
    dsimp [k]
    simp [SOptLib.global_index]
    omega
  have hmod : (k + 1) % T ≠ 0 := by
    have hj1_lt : j - 1 < T := by omega
    have hmod_eq : SOptLib.global_index T s (j - 1) % T = j - 1 := by
      simp [SOptLib.global_index, Nat.mul_comm, Nat.mod_eq_of_lt hj1_lt]
    rw [hk1, hmod_eq]
    omega
  have hprevN : SOptLib.global_index T s (j - 1) ≤ N :=
    SOptLib.global_index_le_of_step_le (T := T) (N := N) (s := s)
      (i := j - 1) (t := j) (by omega) hjN
  have hpair_prev :
      Measurable[filt.seq (SOptLib.global_index T s (j - 1) * b)]
        (fun ω =>
          (iter (SOptLib.global_index T s (j - 1)) ω,
            estimator (SOptLib.global_index T s (j - 1)) ω)) :=
    h_pair (SOptLib.global_index T s (j - 1)) hprevN
  have hx_prev :
      Measurable[filt.seq (SOptLib.global_index T s (j - 1) * b)]
        (iter (SOptLib.global_index T s (j - 1))) :=
    measurable_fst.comp hpair_prev
  have hG_prev :
      Measurable[filt.seq (SOptLib.global_index T s (j - 1) * b)]
        (estimator (SOptLib.global_index T s (j - 1))) :=
    measurable_snd.comp hpair_prev
  have hx_update :
      Measurable[filt.seq (SOptLib.global_index T s (j - 1) * b)]
        (fun ω =>
          update (iter (SOptLib.global_index T s (j - 1)) ω)
            (estimator (SOptLib.global_index T s (j - 1)) ω)
            (SOptLib.global_index T s (j - 1))) :=
    h_update_meas hx_prev hG_prev
  convert hx_update using 1
  funext ω
  rw [← hk2, ← hk1]
  exact congrFun (h_iter_update k hmod) ω



open scoped InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: conditional_gradient_smooth_descent_premise_of_estimator
--   (orig was: conditionalGradient_smoothDescent_premise_of_estimator)
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; inner products are used
--      for the gradient/estimator pairing and Cauchy-Schwarz, with no finite
--      dimensionality or completeness needed once the smooth quadratic bound is
--      passed as a hypothesis.
--   measure: none; this is a deterministic pointwise one-step descent lemma.
--   convexity: none in the theorem; convexity/smoothness enter only through the
--      supplied quadratic upper-bound premise.
-- G0.3 reusability — could instantiate:
--   1. finite-sum stochastic nonconvex conditional gradient, affine LMO update
--      descent before active-window summation.
--   2. stochastic conditional gradient / variance-reduced Frank-Wolfe,
--      estimator-error Young absorption after a smooth objective upper bound.
-- G0.4 search trace:
--   queries: ["conditional gradient smooth descent estimator",
--     "inner estimator error Young smoothness inequality"]
--   top hits: ["finite_one_step_smooth_descent_premise",
--     "stochastic_one_step_smooth_descent_premise",
--     "wolfeGap_le_maxLinearModel_add_estimatorError_mul_diameter",
--     "mul_mul_le_inv_two_mul_add_half_mul_sq",
--     "Convex.carrier_smooth_quadratic_upper_bound",
--     "smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex"]
--   coverage: partial — existing hits cover either the paper-local finite and
--     stochastic private lemmas, Wolfe-gap surrogate algebra, scalar Young
--     absorption, or the smooth quadratic bound, but none packages affine LMO
--     descent with estimator-error absorption from an abstract quadratic premise.
-- G0.4 not-a-thin-wrapper rationale: combines the smooth quadratic premise,
--   affine update rewrite, diameter control, estimator/gradient inner-product
--   decomposition, Cauchy-Schwarz, and scaled Young absorption.
-- G0.5 structural-content rationale: theorem only; it exposes the reusable
--   conditional-gradient one-step descent invariant without introducing a
--   formula-bodied def or paper setup wrapper.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step descent algebra
--   beyond one Mathlib/SOptLib call.
-- G0.5d minimal-hypothesis check: all already minimal; smoothness and convexity
--   were reduced to the pointwise quadratic upper-bound premise used here.

/-- A smooth quadratic bound plus an affine conditional-gradient step gives
descent with estimator-error absorption.

If `xnext - x = alpha • (lmo G - x)`, the smooth quadratic upper bound is
available at `xnext`, and the LMO displacement has norm at most `D`, then the
true-gradient term can be rewritten through the estimator `G` and the residual
cross term absorbed by Young's inequality.

Layer: Layer1 | Gap: Level 1 (conditional-gradient estimator-error descent)
Proof: rewrite the smooth descent bound along the affine LMO step, split the
  true-gradient inner product into estimator plus residual, control the residual
  by Cauchy-Schwarz and the diameter bound, then apply scaled Young absorption.
Source: Frank-Wolfe smooth descent algebra, real Hilbert-space Cauchy-Schwarz,
  and ordered-field Young inequality
Used in: finite-sum and stochastic nonconvex conditional-gradient one-step
  descent before estimator second-moment aggregation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem conditional_gradient_smooth_descent_premise_of_estimator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad lmo : E → E) (x G xnext : E) (alpha L D : ℝ)
    (hL_pos : 0 < L)
    (halpha_nonneg : 0 ≤ alpha)
    (hstep : xnext - x = alpha • (lmo G - x))
    (hquad :
      f xnext ≤ f x + ⟪grad x, xnext - x⟫_ℝ + (L / 2) * ‖xnext - x‖ ^ 2)
    (hdiam : ‖lmo G - x‖ ≤ D) :
    f xnext ≤
      f x + alpha * ⟪G, lmo G - x⟫_ℝ +
        (1 / (2 * L)) * ‖G - grad x‖ ^ 2 +
        L * alpha ^ 2 * D ^ 2 := by
  let y : E := lmo G
  let e : ℝ := ‖grad x - G‖
  have hD_nonneg : 0 ≤ D := le_trans (norm_nonneg (y - x)) (by simpa [y] using hdiam)
  have hinner_update :
      ⟪grad x, xnext - x⟫_ℝ = alpha * ⟪grad x, y - x⟫_ℝ := by
    simpa [y, inner_smul_right] using
      congrArg (fun z : E => ⟪grad x, z⟫_ℝ) hstep
  have hquad' :
      f xnext ≤ f x + alpha * ⟪grad x, y - x⟫_ℝ +
        (L / 2) * ‖xnext - x‖ ^ 2 := by
    simpa [hinner_update] using hquad
  have hnorm_update : ‖xnext - x‖ ≤ alpha * D := by
    calc
      ‖xnext - x‖ = ‖alpha • (y - x)‖ := by
        simpa [y] using congrArg (fun z : E => ‖z‖) hstep
      _ = alpha * ‖y - x‖ := by
        rw [norm_smul, Real.norm_of_nonneg halpha_nonneg]
      _ ≤ alpha * D := by
        exact mul_le_mul_of_nonneg_left (by simpa [y] using hdiam) halpha_nonneg
  have hnorm_sq : ‖xnext - x‖ ^ 2 ≤ alpha ^ 2 * D ^ 2 := by
    have hright_nonneg : 0 ≤ alpha * D := mul_nonneg halpha_nonneg hD_nonneg
    have hleft_nonneg : 0 ≤ ‖xnext - x‖ := norm_nonneg _
    nlinarith
  have hqbound :
      (L / 2) * ‖xnext - x‖ ^ 2 ≤
        (L / 2) * (alpha ^ 2 * D ^ 2) := by
    have hLhalf_nonneg : 0 ≤ L / 2 := by
      linarith
    exact mul_le_mul_of_nonneg_left hnorm_sq hLhalf_nonneg
  have hinner_decomp :
      alpha * ⟪grad x, y - x⟫_ℝ =
        alpha * ⟪G, y - x⟫_ℝ + alpha * ⟪grad x - G, y - x⟫_ℝ := by
    have hbase :
        ⟪grad x, y - x⟫_ℝ =
          ⟪G, y - x⟫_ℝ + ⟪grad x - G, y - x⟫_ℝ := by
      rw [inner_sub_left]
      ring
    rw [hbase]
    ring
  have hinner_err :
      ⟪grad x - G, y - x⟫_ℝ ≤ e * D := by
    calc
      ⟪grad x - G, y - x⟫_ℝ
          ≤ |⟪grad x - G, y - x⟫_ℝ| := le_abs_self _
      _ ≤ ‖grad x - G‖ * ‖y - x‖ :=
          abs_real_inner_le_norm (grad x - G) (y - x)
      _ ≤ e * D := by
          dsimp [e]
          exact mul_le_mul_of_nonneg_left (by simpa [y] using hdiam) (norm_nonneg _)
  have hcross_linear :
      alpha * ⟪grad x - G, y - x⟫_ℝ ≤ alpha * (e * D) :=
    mul_le_mul_of_nonneg_left hinner_err halpha_nonneg
  have hyoung :
      alpha * (e * D) ≤
        (1 / (2 * L)) * e ^ 2 + (L / 2) * alpha ^ 2 * D ^ 2 := by
    exact mul_mul_le_inv_two_mul_add_half_mul_sq alpha e D L hL_pos
  have hcross :
      alpha * ⟪grad x - G, y - x⟫_ℝ ≤
        (1 / (2 * L)) * e ^ 2 + (L / 2) * alpha ^ 2 * D ^ 2 :=
    le_trans hcross_linear hyoung
  have hcombined :
      f xnext ≤
        f x + alpha * ⟪G, y - x⟫_ℝ +
          (1 / (2 * L)) * e ^ 2 + L * alpha ^ 2 * D ^ 2 := by
    have hquad_bound :
        f xnext ≤ f x + alpha * ⟪grad x, y - x⟫_ℝ +
          (L / 2) * (alpha ^ 2 * D ^ 2) := by
      linarith
    have hhalf :
        (L / 2) * (alpha ^ 2 * D ^ 2) +
          (L / 2) * alpha ^ 2 * D ^ 2 =
            L * alpha ^ 2 * D ^ 2 := by
      ring
    linarith
  dsimp [y, e] at hcombined ⊢
  simpa [norm_sub_rev] using hcombined

-- From Staging/recursiveProcess_pair_measurable_at_sampleCutoff_of_refresh_or_minibatch.lean

open MeasureTheory

-- Generalization plan (G0):
-- G0.1 naming: recursive_process_pair_measurable_at_sample_cutoff_of_refresh_or_minibatch
--   (orig was: recursiveProcess_pair_measurable_at_sampleCutoff_of_refresh_or_minibatch)
-- G0.2 typeclass level used:
--   E: none; the proof only needs measurable spaces on an abstract state and estimator type
--   measure: none; no integration or probability property is used
--   convexity: none; the argument is filtration measurability only
-- G0.3 reusability — could instantiate:
--   1. finite-sum conditional gradient recursive estimator adaptedness before fresh mini-batches
--   2. variance-reduced stochastic gradient or SARAH/SPIDER estimator adaptedness with refresh steps
-- G0.4 search trace:
--   queries: ["recursive process measurable cutoff", "measurable pair filtration recursive update"]
--   top hits: ["finite_process_pair_measurable_recursive_cutoff_of_le",
--     "processOfWellDefined_pair_measurable_recursive_cutoff",
--     "SOptLib.recursive_process_measurable_of_measurable_update",
--     "SOptLib.recursive_process_measurable_of_measurable_update_oracle",
--     "SOptLib.recursiveProcess_measurable_wrt_strictPast",
--     "MeasureTheory.Adapted",
--     "MeasureTheory.isPredictable_of_measurable_add_one"]
--   coverage: partial — existing recursive-process lemmas cover a single update/oracle driver,
--     but not a state-estimator pair with refresh/minibatch estimator branches at enlarged cutoffs
-- G0.4 not-a-thin-wrapper rationale: the declaration adds the two-branch estimator
--   transition and cutoff-monotonicity induction structure not present in the single-driver APIs.
-- G0.5 structural-content rationale: the proof packages the recurring adapted state-pair
--   invariant used before fresh stochastic mini-batches.
-- G0.5c thin-wrapper self-detect: clean — body has a multi-branch induction with cutoff lifting.
-- G0.5d minimal-hypothesis check: all hypotheses are pointwise in the time index and cutoff used.

/-- A recursive state-estimator pair is measurable at sample cutoffs through
refresh and mini-batch estimator branches.

The theorem abstracts the common variance-reduced adaptedness pattern: the
previous state pair is lifted to the next sample cutoff, the next state is
measurable there, and the estimator is measurable either by an exact-refresh
branch or by a recursive mini-batch branch.

Layer: Layer1 | Gap: Level 1 (recursive state-estimator adaptedness at sample cutoffs)
Proof: induction on the natural-number time index; the successor-successor
  step lifts the previous pair along filtration monotonicity, proves the next
  state measurable, and splits into refresh or recursive estimator branches.
Source: Mathlib process filtration and measurable product composition APIs
Used in: finite-sum and variance-reduced conditional-gradient prefix/fresh
  mini-batch measurability
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem recursive_process_pair_measurable_at_sample_cutoff_of_refresh_or_minibatch
    {Ω X G : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace G]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (sampleCutoff : ℕ → ℕ)
    (state : ℕ → Ω → X × G)
    (nextState : ℕ → Ω → X)
    (refreshEstimator recursiveEstimator : ℕ → Ω → G)
    (isRefresh : ℕ → Prop)
    (N k : ℕ)
    (h_sampleCutoff_mono :
      ∀ n, n + 1 ≤ N → sampleCutoff n ≤ sampleCutoff (n + 1))
    (h_zero : Measurable[filt.seq (sampleCutoff 0)] (state 0))
    (h_one : 1 ≤ N → Measurable[filt.seq (sampleCutoff 1)] (state 1))
    (h_next :
      ∀ n, n + 2 ≤ N →
        Measurable[filt.seq (sampleCutoff (n + 2))] (state (n + 1)) →
        Measurable[filt.seq (sampleCutoff (n + 2))] (nextState n))
    (h_refresh :
      ∀ n, n + 2 ≤ N → isRefresh (n + 1) →
        Measurable[filt.seq (sampleCutoff (n + 2))] (nextState n) →
        Measurable[filt.seq (sampleCutoff (n + 2))] (refreshEstimator n))
    (h_recursive :
      ∀ n, n + 2 ≤ N → ¬ isRefresh (n + 1) →
        Measurable[filt.seq (sampleCutoff (n + 2))] (state (n + 1)) →
        Measurable[filt.seq (sampleCutoff (n + 2))] (nextState n) →
        Measurable[filt.seq (sampleCutoff (n + 2))] (recursiveEstimator n))
    (h_state_refresh :
      ∀ n, n + 2 ≤ N → isRefresh (n + 1) →
        state (n + 2) = fun ω => (nextState n ω, refreshEstimator n ω))
    (h_state_recursive :
      ∀ n, n + 2 ≤ N → ¬ isRefresh (n + 1) →
        state (n + 2) = fun ω => (nextState n ω, recursiveEstimator n ω))
    (hkN : k ≤ N) :
    Measurable[filt.seq (sampleCutoff k)] (state k) := by
  induction k with
  | zero =>
      exact h_zero
  | succ k ih =>
      cases k with
      | zero =>
          exact h_one (by omega)
      | succ n =>
          have hprevN : n + 1 ≤ N := by omega
          have hpair_prev_base :
              Measurable[filt.seq (sampleCutoff (n + 1))] (state (n + 1)) :=
            ih hprevN
          have hcutoff : sampleCutoff (n + 1) ≤ sampleCutoff (n + 2) :=
            h_sampleCutoff_mono (n + 1) (by omega)
          have hpair_prev :
              Measurable[filt.seq (sampleCutoff (n + 2))] (state (n + 1)) :=
            hpair_prev_base.mono (filt.mono hcutoff) le_rfl
          have hx_next :
              Measurable[filt.seq (sampleCutoff (n + 2))] (nextState n) :=
            h_next n (by omega) hpair_prev
          by_cases hstart : isRefresh (n + 1)
          · have hG :
                Measurable[filt.seq (sampleCutoff (n + 2))] (refreshEstimator n) :=
              h_refresh n (by omega) hstart hx_next
            simpa [h_state_refresh n (by omega) hstart] using hx_next.prodMk hG
          · have hG :
                Measurable[filt.seq (sampleCutoff (n + 2))] (recursiveEstimator n) :=
              h_recursive n (by omega) hstart hpair_prev hx_next
            simpa [h_state_recursive n (by omega) hstart] using hx_next.prodMk hG


-- From Staging/weighted_gap_sum_bound_of_active_one_step_and_budget.lean

open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: weighted_gap_sum_bound_of_active_one_step_and_budget
--   (kept planner name; the concept is a weighted active one-step gap
--   aggregation from a final scalar budget, with no paper theorem markers).
-- G0.2 typeclass level used:
--   E: none; Wolfe gaps, objectives, norms, and expectations have already been
--     reduced to scalar finite-sum terms before this Layer1 aggregation step.
--   measure: none; measure-theoretic content is contained in scalar functions
--     such as `gapWeight` and `stepRhs` supplied by earlier lemmas.
--   convexity: none; convexity and smoothness are consumed by the one-step
--     hypothesis before this finite-sum budget handoff.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient, summing active expected
--      Wolfe-gap one-step inequalities and applying the Theorem 7.16 scalar
--      budget after objective telescoping.
--   2. variance-reduced Frank-Wolfe or stochastic proximal-gradient inner
--      loops, reindexing active step windows and consuming any already proved
--      final descent-plus-noise budget.
-- G0.4 search trace:
--   queries: ["weighted gap sum budget",
--     "reindexed finite sum pointwise bound final budget"]
--   top hits: ["weighted_gap_sum_bound_of_active_one_step_with_l1_floor",
--     "weighted_gap_sum_bound_of_active_one_step_with_variance_floor",
--     "weighted_gap_sum_bound_of_active_one_step_young_variance",
--     "summed_one_step_gap_bound_of_telescope",
--     "active_sum_objective_drop_add_scalar_budget",
--     "integral_sum_telescope_bound_of_pointwise_lower_bound"]
--   coverage: partial — hits either decompose the one-step RHS into specific
--     stochastic-optimization component budgets or telescope objective drops,
--     while this theorem is the more general active reindexing plus pointwise
--     one-step plus arbitrary final-budget handoff.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   invariant that a global weighted numerator can be reindexed onto active
--   windows, bounded pointwise there, and discharged by an independently
--   proved nested active-window budget.
-- G0.5 structural-content rationale: the statement exposes exactly the common
--   active-window partition, local one-step inequality, and final scalar
--   budget structure while removing paper-local epoch and estimator notation.
-- G0.5b name-body alignment: the name promises a weighted gap sum bound from
--   active one-step bounds and a budget, and the theorem proves precisely that.
-- G0.5c thin-wrapper self-detect: clean — body combines reindexing, nested
--   finite-sum monotonicity, and a separate final budget rather than aliasing
--   one existing Mathlib or SOptLib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; each hypothesis is used
--   directly for the partition rewrite, pointwise active bound, or final
--   budget comparison.

/-- Bound a reindexed weighted gap sum from active one-step bounds and a final
budget.

If the global weighted gap numerator reindexes onto active epoch windows, every
active term is bounded by a scalar one-step right-hand side, and the nested sum
of those right-hand sides is already bounded by `finalBound`, then the global
weighted numerator is bounded by `finalBound`.

Layer: Layer1 | Gap: Level 1 (active weighted-gap final-budget handoff)
Proof: rewrite the global finite sum by the active-window partition, sum the
  pointwise one-step inequalities over the nested active windows, and compose
  with the supplied final scalar budget.
Source: Mathlib finite big-operator inequalities over ordered additive monoids
Used in: finite-sum nonconvex conditional-gradient weighted Wolfe-gap numerator
  after active one-step descent and scalar Theorem 7.16 budget assembly
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/key_lemmas/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem weighted_gap_sum_bound_of_active_one_step_and_budget
    {K A B R : Type*} [AddCommMonoid R] [Preorder R] [IsOrderedAddMonoid R]
    (window : Finset K) (epochs : Finset A) (active : A → Finset B)
    (idx : A → B → K) (gapWeight : K → R) (stepRhs : A → B → R)
    (finalBound : R)
    (hpartition :
      Finset.sum window gapWeight =
        Finset.sum epochs
          (fun a => Finset.sum (active a) (fun b => gapWeight (idx a b))))
    (hstep :
      ∀ a ∈ epochs, ∀ b ∈ active a, gapWeight (idx a b) ≤ stepRhs a b)
    (hbudget :
      Finset.sum epochs (fun a => Finset.sum (active a) (fun b => stepRhs a b)) ≤
        finalBound) :
    Finset.sum window gapWeight ≤ finalBound := by
  classical
  calc
    Finset.sum window gapWeight
        =
      Finset.sum epochs
        (fun a => Finset.sum (active a) (fun b => gapWeight (idx a b))) :=
        hpartition
    _ ≤
      Finset.sum epochs
        (fun a => Finset.sum (active a) (fun b => stepRhs a b)) := by
        exact Finset.sum_le_sum (fun a ha =>
          Finset.sum_le_sum (fun b hb => hstep a ha b hb))
    _ ≤ finalBound := hbudget


-- From Staging/current_iterate_measurable_before_recursive_batch.lean

open MeasureTheory

-- Generalization plan (G0):
-- G0.1 naming: current_iterate_measurable_before_recursive_batch
--   (orig was: iterProcessOfWellDefined_globalIndex_measurable_recursive_cutoff);
--   the name describes the predictable current-iterate measurability property
--   before a recursive mini-batch, without paper-local process names.
-- G0.2 typeclass level used:
--   E: arbitrary measurable state and estimator spaces X/G; no norm, topology,
--      inner product, convexity, or finite-dimensionality is used.
--   measure: none; the proof is filtration measurability only and does not use
--      a probability measure, integration, or independence.
--   convexity: none; the update rule is an abstract measurable map hypothesis.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient recursive mini-batch
--      measurability before a fresh estimator-difference batch.
--   2. SARAH/SPIDER or variance-reduced mirror descent inner-loop predictable
--      iterate measurability before the next gradient-difference sample block.
-- G0.4 search trace:
--   queries: ["current iterate measurable recursive batch",
--     "measurable composition recursive process cutoff",
--     "measurable first projection of measurable pair"]
--   top hits: ["within_epoch_iterate_measurable_before_recursive_mini_batch",
--     "recursive_process_pair_measurable_at_sample_cutoff_of_refresh_or_minibatch",
--     "recursiveProcess_measurable_wrt_strictPast", "measurable_fst",
--     "Measurable.fst", "measurable_fun_prod"]
--   coverage: strengthens within_epoch_iterate_measurable_before_recursive_mini_batch
--     by dropping the finite-horizon `global_index T s j ≤ N` premise and by
--     carrying an abstract sample-cutoff offset.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages fixed-epoch index
--   arithmetic, strict-past pair projection, update measurability, and
--   non-refresh recursion rewriting into one reusable predictable-iterate
--   invariant.
-- G0.5 structural-content rationale: the statement exposes the horizon-free
--   current-iterate-before-fresh-batch measurability invariant over arbitrary
--   measurable state and estimator spaces.
-- G0.5c thin-wrapper self-detect: clean — body performs index arithmetic,
--   pair projection, update measurability, and recursive update rewriting.
-- G0.5d minimal-hypothesis check: all already minimal; pair measurability,
--   update measurability, and update equality are pointwise at the exact
--   cutoff/time used.

/-- A current within-epoch recursive iterate is measurable before the fresh batch.

For a fixed-length epoch schedule, if each iterate-estimator pair is measurable
at its recursive sample cutoff and non-refresh steps update the iterate from the
previous measurable pair, then an inner-loop iterate at step `j`, `2 ≤ j ≤ T`,
is measurable at the previous step's sample cutoff.

Layer: Layer1 | Gap: Level 1 (horizon-free predictable iterate measurability)
Proof: identify `global_index T s j` as the non-refresh successor of
  `global_index T s (j - 1)`, project the previous iterate and estimator from
  pair measurability, apply the measurable update hypothesis, and rewrite the
  recursive update equation.
Source: Mathlib filtration measurability, product projection, and natural-number
  epoch-index arithmetic APIs
Used in: variance-reduced conditional-gradient recursive mini-batch
  measurability before fresh estimator-difference sample blocks
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem current_iterate_measurable_before_recursive_batch
    {Ω X G : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace G]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (T b offset : ℕ)
    (iter : ℕ → Ω → X)
    (estimator : ℕ → Ω → G)
    (update : X → G → ℕ → X)
    (h_pair :
      ∀ k,
        Measurable[filt.seq (offset + k * b)]
          (fun ω => (iter k ω, estimator k ω)))
    (h_update_meas :
      ∀ {cutoff n},
        Measurable[filt.seq cutoff] (iter n) →
        Measurable[filt.seq cutoff] (estimator n) →
        Measurable[filt.seq cutoff]
          (fun ω => update (iter n ω) (estimator n ω) n))
    (h_iter_update :
      ∀ n, (n + 1) % T ≠ 0 →
        iter (n + 2) =
          fun ω => update (iter (n + 1) ω) (estimator (n + 1) ω) (n + 1))
    (s j : ℕ) (hj2 : 2 ≤ j) (hjT : j ≤ T) :
    Measurable[filt.seq (offset + SOptLib.global_index T s (j - 1) * b)]
      (iter (SOptLib.global_index T s j)) := by
  let k := SOptLib.global_index T s (j - 1) - 1
  have hk1 : k + 1 = SOptLib.global_index T s (j - 1) := by
    dsimp [k]
    simp [SOptLib.global_index]
    omega
  have hk2 : k + 2 = SOptLib.global_index T s j := by
    dsimp [k]
    simp [SOptLib.global_index]
    omega
  have hmod : (k + 1) % T ≠ 0 := by
    have hj1_lt : j - 1 < T := by
      omega
    have hmod_eq : SOptLib.global_index T s (j - 1) % T = j - 1 := by
      simp [SOptLib.global_index, Nat.mul_comm, Nat.mod_eq_of_lt hj1_lt]
    rw [hk1, hmod_eq]
    omega
  have hpair_prev :
      Measurable[filt.seq (offset + SOptLib.global_index T s (j - 1) * b)]
        (fun ω =>
          (iter (SOptLib.global_index T s (j - 1)) ω,
            estimator (SOptLib.global_index T s (j - 1)) ω)) :=
    h_pair (SOptLib.global_index T s (j - 1))
  have hx_prev :
      Measurable[filt.seq (offset + SOptLib.global_index T s (j - 1) * b)]
        (iter (SOptLib.global_index T s (j - 1))) :=
    measurable_fst.comp hpair_prev
  have hG_prev :
      Measurable[filt.seq (offset + SOptLib.global_index T s (j - 1) * b)]
        (estimator (SOptLib.global_index T s (j - 1))) :=
    measurable_snd.comp hpair_prev
  have hx_update :
      Measurable[filt.seq (offset + SOptLib.global_index T s (j - 1) * b)]
        (fun ω =>
          update (iter (SOptLib.global_index T s (j - 1)) ω)
            (estimator (SOptLib.global_index T s (j - 1)) ω)
            (SOptLib.global_index T s (j - 1))) :=
    h_update_meas hx_prev hG_prev
  convert hx_update using 1
  funext ω
  rw [← hk2, ← hk1]
  exact congrFun (h_iter_update k hmod) ω


-- From Staging/epochStartIterate_measurable_strictSampleFootprint.lean

open scoped MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- G0.1 naming: epoch_start_iterate_measurable_strict_sample_footprint
--   (orig was: iterProcess_epoch_start_measurable_sampleBlock); the name keeps
--   the stochastic-optimization concept of an epoch-start iterate measurable
--   from its strict finite sample footprint, without paper-local setup names.
-- G0.2 typeclass level used:
--   Ω: no ambient measurable space; all source measurability is taken with
--      respect to the explicit `sampleBlockMeasurableSpace`.
--   Ξ, E: [MeasurableSpace Ξ] and [MeasurableSpace E] only; the proof uses
--      generated sample-block measurability plus measurability of iterate,
--      estimator, and update outputs, with no algebra, norm, inner product,
--      topology, completeness, or finite-dimensional structure.
--   measure: none; the statement is sigma-algebra measurability, not an
--      independence or integration result.
--   convexity: none; the proof is an adaptedness/footprint bridge.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional-gradient epoch-start adaptedness before
--      a fresh refresh mini-batch.
--   2. SARAH/SPIDER and variance-reduced stochastic-gradient methods whose
--      epoch-boundary iterate is an update of a strict-predecessor state.
-- G0.4 search trace:
--   queries: ["epoch start measurable",
--     "sample block measurable prefix process",
--     "Measurable sampleBlockMeasurableSpace induction update"]
--   top hits: ["SOptLib.process_prefix_measurable_wrt_sampleBlock",
--     "SOptLib.sampleBlockMeasurableSpace",
--     "SOptLib.sampleBlock_coordinate_measurable",
--     "SOptLib.recursive_process_measurable_of_measurable_update_oracle",
--     "SOptLib.randomizedOutput_measurable_wrt_sampleBlock"]
--   coverage: partial — process-prefix lemmas prove fixed-prefix recursion
--     measurability, but do not package epoch-boundary selection from a
--     strict-predecessor state plus a boundary update identity.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable
--   boundary/predecessor quantifier structure that turns strict-footprint
--   state-pair adaptedness and update measurability into epoch-start iterate
--   adaptedness.
-- G0.5 structural-content rationale: the statement exposes the invariant that
--   epoch-start iterates may be read through the previous epoch's terminal
--   update while keeping the current refresh batch out of the source
--   sigma-algebra.
-- G0.5c thin-wrapper self-detect: clean — body performs a successor-boundary
--   case split, extracts measurable components from a predecessor pair, applies
--   the update measurability bridge, and rewrites by the boundary identity.
-- G0.5d minimal-hypothesis check: all hypotheses are pointwise at the base
--   boundary or the successor boundary being proved.

/-- An epoch-start iterate is measurable from its strict finite sample footprint.

If the initial boundary slice is measurable, every positive epoch boundary has a
measurable strict-predecessor iterate/estimator pair, and the update from that
pair is measurable and equal to the boundary iterate, then all epoch-start
iterates are measurable for their finite sample-block sigma-algebras.

Layer: Layer1 | Gap: Level 1 (epoch-start strict-footprint adaptedness)
Proof: split on the epoch index. The successor case projects the predecessor
  pair measurability, applies the abstract update measurability hypothesis, and
  rewrites the result by the boundary update identity.
Source: Mathlib MeasureTheory product measurability and finite generated
  sample-block sigma-algebras
Used in: stochastic nonconvex conditional-gradient epoch-start adaptedness before
  a fresh refresh mini-batch
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epoch_start_iterate_measurable_strict_sample_footprint
    {Ω Ξ E : Type*} [MeasurableSpace Ξ] [MeasurableSpace E]
    (ξ : ℕ → Ω → Ξ)
    (x G : ℕ → Ω → E)
    (update : E → E → ℕ → E)
    (footprint : ℕ → Finset ℕ)
    (boundary prevBoundary : ℕ → ℕ)
    (hbase :
      Measurable[sampleBlockMeasurableSpace ξ (footprint 0)]
        (x (boundary 0)))
    (hprev_pair :
      ∀ r : ℕ,
        Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
          (fun ω => (x (prevBoundary (r + 1)) ω,
            G (prevBoundary (r + 1)) ω)))
    (hupdate :
      ∀ r : ℕ,
        Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
          (x (prevBoundary (r + 1))) →
        Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
          (G (prevBoundary (r + 1))) →
        Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
          (fun ω =>
            update (x (prevBoundary (r + 1)) ω)
              (G (prevBoundary (r + 1)) ω) (prevBoundary (r + 1))))
    (hboundary_update :
      ∀ (r : ℕ) (ω : Ω),
        x (boundary (r + 1)) ω =
          update (x (prevBoundary (r + 1)) ω)
            (G (prevBoundary (r + 1)) ω) (prevBoundary (r + 1)))
    (s : ℕ) :
    Measurable[sampleBlockMeasurableSpace ξ (footprint s)] (x (boundary s)) := by
  cases s with
  | zero =>
      simpa using hbase
  | succ r =>
      have hpair :
          Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
            (fun ω => (x (prevBoundary (r + 1)) ω,
              G (prevBoundary (r + 1)) ω)) :=
        hprev_pair r
      have hx_prev :
          Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
            (x (prevBoundary (r + 1))) :=
        measurable_fst.comp hpair
      have hG_prev :
          Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
            (G (prevBoundary (r + 1))) :=
        measurable_snd.comp hpair
      have hnext :
          Measurable[sampleBlockMeasurableSpace ξ (footprint (r + 1))]
            (fun ω =>
              update (x (prevBoundary (r + 1)) ω)
                (G (prevBoundary (r + 1)) ω) (prevBoundary (r + 1))) :=
        hupdate r hx_prev hG_prev
      convert hnext using 1
      funext ω
      exact hboundary_update r ω

end SOptLib


-- From Staging/conditionalGradientUpdate_measurable_of_lmo.lean

-- Generalization plan (G0):
-- G0.1 naming: conditionalGradientUpdate_measurable_of_lmo (orig was:
--   iterUpdateOfWellDefined_measurable_sampleBlock); the name describes the
--   standard conditional-gradient affine update and its LMO measurability
--   hypothesis, not Algorithm 7.13 paper-local notation.
-- G0.2 typeclass level used:
--   E: [MeasurableSpace E] [Add E] [SMul ℝ E] [MeasurableAdd₂ E]
--      [MeasurableConstSMul ℝ E]; the proof only uses measurable addition
--      and constant real scalar multiplication. No norm, inner product,
--      completeness, Borel-space, or finite-dimensional structure is used.
--   measure: none; the statement is over an arbitrary source sigma-algebra
--      `mΩ`, so it applies to filtrations, generated sample-block
--      sigma-algebras, and ambient measurable spaces without a measure.
--   convexity: none; feasibility of the same named update is handled by
--      `conditionalGradientIterUpdate_mem`, while this theorem only concerns
--      measurability.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient sample-block adapted update
--   2. finite-sum variance-reduced conditional gradient prefix-measurable update
-- G0.4 search trace:
--   queries: ["conditional gradient update measurable",
--     "measurable affine combination scalar smul add",
--     "conditionalGradientIterUpdate measurable", "Measurable const_smul add"]
--   top hits: ["SOptLib.conditionalGradientIterUpdate",
--     "SOptLib.conditionalGradientIterUpdate_def",
--     "SOptLib.conditionalGradientIterUpdate_mem",
--     "StochasticNonconvexConditionalGradientSetup.iterUpdateOfWellDefined_measurable_sampleBlock",
--     "StochasticNonconvexConditionalGradientSetup.iterUpdateOfWellDefined_measurable",
--     "finite_iterUpdate_measurable", "SOptLib.Model.Iterates.weightedAverageOutput_measurable",
--     "SOptLib.Layer0.Oracle.miniBatchOracle_measurable_of_coordinate_measurable"]
--   coverage: partial — the existing Model def names the update and local
--     algorithm lemmas prove this shape for paper setups, but no SOptLib or
--     Mathlib hit gives the named conditional-gradient update measurability
--     theorem over an arbitrary source sigma-algebra.
-- G0.4 not-a-thin-wrapper rationale: the declaration adds the reusable
--   quantifier structure tying measurable iterate, measurable estimator, and
--   measurable LMO selector to the named conditional-gradient update; it is
--   not a renaming of a single existing theorem because no existing hit states
--   this named update measurability principle.
-- G0.5 structural-content rationale: this theorem is API for the existing
--   conditional-gradient update object, exposing the adaptedness/measurability
--   invariant needed by stochastic optimization recursions.
-- G0.5c thin-wrapper self-detect: clean — body composes LMO measurability
--   with two measurable scalar multiples and measurable addition for a named
--   optimization update.
-- G0.5d minimal-hypothesis check: all already minimal; there are no global
--   analytic, measure-theoretic, convexity, or pointwise differentiability
--   hypotheses to weaken.

namespace SOptLib

/-- A conditional-gradient affine LMO update is measurable from measurable inputs.

For any source sigma-algebra, if the current iterate `x` and estimator or
gradient-like input `G` are measurable and the linear-minimization selector is
measurable, then the Frank-Wolfe update
`conditionalGradientIterUpdate alpha linearMinimizer (x ω) (G ω) k` is
measurable.

Layer: Layer1 | Gap: Level 0 (conditional-gradient affine update measurability)
Proof: compose the measurable LMO selector with the estimator, then close the
  affine update under constant scalar multiplication and measurable addition.
Source: Mathlib MeasureTheory measurable algebra APIs for addition and scalar
  multiplication
Used in: stochastic nonconvex conditional gradient adapted LMO iterate update
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
theorem conditionalGradientUpdate_measurable_of_lmo
    {Ω E : Type*} [MeasurableSpace E]
    [Add E] [SMul ℝ E] [MeasurableAdd₂ E] [MeasurableConstSMul ℝ E]
    (mΩ : MeasurableSpace Ω) (alpha : ℕ → ℝ) (linearMinimizer : E → E)
    (hlmo : Measurable linearMinimizer) {x G : Ω → E} {k : ℕ}
    (hx : @Measurable Ω E mΩ _ x) (hG : @Measurable Ω E mΩ _ G) :
    @Measurable Ω E mΩ _
      (fun ω => conditionalGradientIterUpdate alpha linearMinimizer (x ω) (G ω) k) := by
  have hy : @Measurable Ω E mΩ _ (fun ω => linearMinimizer (G ω)) :=
    hlmo.comp hG
  simpa [conditionalGradientIterUpdate] using
    ((hx.const_smul (1 - alpha k)).add (hy.const_smul (alpha k)))

end SOptLib


-- From Staging/epoch_recursiveEstimator_secondMoment_le_diffSum.lean

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: epoch_recursive_estimator_second_moment_le_difference_sum
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E]; the induction only mentions squared norms of
--      residuals and iterate differences. Inner products, completeness, scalar
--      multiplication, and finite dimensionality are not used.
--   measure: arbitrary Measure μ on a measurable space; no probability or
--      finite-measure normalization is used.
--   convexity: none; the geometric and oracle assumptions enter only through
--      the one-step second-moment recurrence hypothesis.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, recursive estimator-error
--      accumulation inside an epoch
--   2. variance-reduced mirror descent, recursive gradient-estimator residual
--      accumulation from one-step variance recurrences
-- G0.4 search trace:
--   queries: ["recursive estimator second moment",
--     "integral norm square recursive bound"]
--   top hits: ["finite_recursive_minibatch_increment_second_moment_le",
--     "recursive_minibatch_increment_second_moment_le",
--     "second_moment_add_recurrence_le_of_cross_zero",
--     "epochwise_delta_one_step_second_moment_le",
--     "finite_delta_one_step_second_moment_le",
--     "integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero",
--     "integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero"]
--   coverage: partial — hits provide one-step residual recurrences,
--     mini-batch moment bounds, and Hilbert moment algebra, but none packages
--     the epoch-local induction that bounds the recursive estimator second
--     moment by the accumulated squared iterate differences.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that a base residual bound and a one-step recursive second-moment estimate
--   telescope through a prefix-valid epoch coordinate system against the named
--   epoch squared-difference accumulation.
-- G0.5 structural-content rationale: no structure or def is introduced; the
--   theorem exposes the load-bearing epoch induction principle over the
--   existing `SOptLib.epochSquaredDifferenceSum` object.
-- G0.5b name-body alignment: the name promises a theorem bounding an epoch
--   recursive estimator second moment by a difference sum, and the body proves
--   exactly that property.
-- G0.5c thin-wrapper self-detect: clean — body performs Nat induction,
--   prefix-validity transport, finite-sum integral splitting, recurrence
--   application, and scalar algebra rather than a direct lemma alias.
-- G0.5d minimal-hypothesis check: all already minimal; validity is pointwise
--   and prefix-closed, integrability is requested only for residuals and
--   difference terms at the indices used by the finite interval split, and the
--   one-step recurrence is pointwise in the epoch coordinate.

/-- An epoch recursive estimator has second moment bounded by accumulated
squared iterate differences.

If the first estimator residual in each valid epoch is bounded by the empty
epoch squared-difference sum and every later valid coordinate satisfies the
one-step recurrence
`secondMoment_j <= secondMoment_{j-1} + c * difference_j`, then induction gives
the standard bound by `c` times the integral of the named accumulated epoch
squared-difference sum.

Layer: Layer1 | Gap: Level 1 (epoch recursive-estimator second-moment induction)
Proof: induct on the epoch-local coordinate. The successor case transports
validity to predecessors, splits the finite-interval integral defining
`epochSquaredDifferenceSum`, applies the one-step recurrence and the induction
hypothesis, then closes by ordered-ring arithmetic.
Source: Mathlib natural-number induction, finite interval sums, and Bochner
  integral linearity
Used in: stochastic nonconvex conditional-gradient recursive estimator-error
  accumulation before expected Wolfe-gap summation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epoch_recursive_estimator_second_moment_le_difference_sum
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (delta x : ℕ → Ω → E) (index : ℕ → ℕ → ℕ)
    (Valid : ℕ → ℕ → Prop) (T : ℕ) (c : ℝ)
    (hvalid_prefix :
      ∀ {s i j : ℕ}, i ≤ j → Valid s j → Valid s i)
    (hbase :
      ∀ s : ℕ, Valid s 1 →
        ∫ ω, ‖delta (index s 1) ω‖ ^ 2 ∂μ ≤
          c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s 1 ω ∂μ)
    (hdelta_sq_int :
      ∀ s j : ℕ, 1 ≤ j → j ≤ T → Valid s j →
        Integrable (fun ω => ‖delta (index s j) ω‖ ^ 2) μ)
    (hdiff_sq_int :
      ∀ s i : ℕ, 2 ≤ i → i ≤ T → Valid s i →
        Integrable
          (fun ω => ‖x (index s i) ω - x (index s (i - 1)) ω‖ ^ 2) μ)
    (hstep :
      ∀ s j : ℕ, 2 ≤ j → j ≤ T → Valid s j →
        Integrable (fun ω => ‖delta (index s (j - 1)) ω‖ ^ 2) μ →
        ∫ ω, ‖delta (index s j) ω‖ ^ 2 ∂μ ≤
          ∫ ω, ‖delta (index s (j - 1)) ω‖ ^ 2 ∂μ +
            c * ∫ ω, ‖x (index s j) ω - x (index s (j - 1)) ω‖ ^ 2 ∂μ)
    (s t : ℕ) (ht : 1 ≤ t) (ht_le : t ≤ T) (hvalid : Valid s t) :
    ∫ ω, ‖delta (index s t) ω‖ ^ 2 ∂μ ≤
      c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s t ω ∂μ := by
  induction t with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hbase s hvalid
      · have hn_pos : 1 ≤ n := by omega
        have hj2 : 2 ≤ n + 1 := by omega
        have hn_le_t : n ≤ n + 1 := by omega
        have hn_le_T : n ≤ T := by omega
        have hprev_valid : Valid s n :=
          hvalid_prefix hn_le_t hvalid
        have hprev_bound :
            ∫ ω, ‖delta (index s n) ω‖ ^ 2 ∂μ ≤
              c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ :=
          ih hn_pos hn_le_T hprev_valid
        have hprev_sq :
            Integrable (fun ω => ‖delta (index s n) ω‖ ^ 2) μ :=
          hdelta_sq_int s n hn_pos hn_le_T hprev_valid
        have hsum_n_int :
            Integrable (SOptLib.epochSquaredDifferenceSum x index s n) μ := by
          unfold SOptLib.epochSquaredDifferenceSum
          exact MeasureTheory.integrable_finset_sum
            (s := Finset.Icc 2 n)
            (fun i hi =>
              hdiff_sq_int s i
                (by
                  exact (Finset.mem_Icc.mp hi).1)
                (by
                  have hi_le : i ≤ n := (Finset.mem_Icc.mp hi).2
                  omega)
                (hvalid_prefix
                  (by
                    have hi_le : i ≤ n := (Finset.mem_Icc.mp hi).2
                    omega)
                  hvalid))
        have hdiff_int :
            Integrable
              (fun ω =>
                ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2) μ := by
          simpa using hdiff_sq_int s (n + 1) hj2 ht_le hvalid
        have hsum_succ :
            ∫ ω, SOptLib.epochSquaredDifferenceSum x index s (n + 1) ω ∂μ =
              ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ +
                ∫ ω,
                  ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ := by
          let f : ℕ → Ω → ℝ := fun i ω =>
            ‖x (index s i) ω - x (index s (i - 1)) ω‖ ^ 2
          calc
            ∫ ω, SOptLib.epochSquaredDifferenceSum x index s (n + 1) ω ∂μ =
                ∫ ω, Finset.sum (Finset.Icc 2 (n + 1)) (fun i => f i ω) ∂μ := by
                  rfl
            _ = ∫ ω, (Finset.sum (Finset.Icc 2 n) (fun i => f i ω) + f (n + 1) ω)
                  ∂μ := by
                  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro ω
                  simpa using
                    (Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)
                      (fun i => f i ω))
            _ = ∫ ω, Finset.sum (Finset.Icc 2 n) (fun i => f i ω) ∂μ +
                  ∫ ω, f (n + 1) ω ∂μ := by
                  exact integral_add hsum_n_int hdiff_int
            _ = ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ +
                  ∫ ω,
                    ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ := by
                  rfl
        calc
          ∫ ω, ‖delta (index s (n + 1)) ω‖ ^ 2 ∂μ ≤
              ∫ ω, ‖delta (index s n) ω‖ ^ 2 ∂μ +
                c * ∫ ω,
                  ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ :=
            hstep s (n + 1) hj2 ht_le hvalid hprev_sq
          _ ≤
              c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ +
                c * ∫ ω,
                  ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ := by
              linarith [hprev_bound]
          _ =
              c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s (n + 1) ω ∂μ := by
              rw [hsum_succ]
              ring


-- From Staging/recursiveRefreshProcess_pair_measurable_before_epochStart.lean

open scoped BigOperators
open scoped MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- G0.1 naming: recursive_refresh_process_pair_measurable_before_epoch_start
--   (orig was: processOfWellDefined_pair_measurable_before_epoch_start)
-- G0.2 typeclass level used:
--   E: [MeasurableSpace E] [AddCommMonoid E] [Sub E] [SMul ℝ E]
--      [MeasurableAdd₂ E] [MeasurableSub₂ E] [MeasurableConstSMul ℝ E]; the proof
--      uses finite sums, scalar multiplication by constants, subtraction, and
--      measurable addition, but no norm, inner product, completeness, or
--      finite-dimensionality.
--   measure: none; the result is sigma-algebra measurability only.
--   convexity: none; no feasible-set or convexity argument appears.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional-gradient epoch-start adaptedness
--      before refresh mini-batches
--   2. SARAH/SPIDER and variance-reduced stochastic-gradient estimators with
--      full-refresh and recursive mini-batch branches before a stopping boundary
-- G0.4 search trace:
--   queries: ["recursive process measurable",
--     "Measurable pair recursive update finite sum"]
--   top hits: ["SOptLib.recursive_process_measurable_of_measurable_update",
--     "SOptLib.recursive_process_measurable_of_measurable_update_oracle",
--     "recursive_process_pair_measurable_at_sample_cutoff_of_refresh_or_minibatch",
--     "SOptLib.recursiveProcess_measurable_wrt_strictPast",
--     "processOfWellDefined_pair_measurable_before_epoch_start"]
--   coverage: partial — existing recursive-process hits handle all-time
--     measurability or sample-cutoff adaptedness; none packages finite footprint
--     coordinate membership for all times strictly before an epoch-start boundary.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the fixed-boundary
--   footprint induction and proves the refresh and recursive finite-sum branches
--   from coordinate-membership hypotheses, not merely from pre-proved branch
--   measurability.
-- G0.5 structural-content rationale: the statement exposes the reusable
--   invariant that a two-branch variance-reduced state-estimator pair is
--   measurable for the sample footprint of a future refresh boundary.
-- G0.5c thin-wrapper self-detect: clean — body has a multi-branch strong
--   induction with finite-kernel sum measurability and coordinate generators.
-- G0.5d minimal-hypothesis check: all schedule, update, projection, and
--   coordinate-footprint assumptions are pointwise at the boundary/time used.

/-- A variance-reduced state-estimator pair is measurable before an epoch-start
boundary's finite sample footprint.

The theorem abstracts the adaptedness pattern for epoch-refresh recursive
estimators: every refresh or recursive sample coordinate used before the
boundary belongs to the boundary footprint, so the iterate/estimator pair is
measurable with respect to that finite generated sigma-algebra.

Layer: Layer1 | Gap: Level 1 (epoch-boundary footprint adaptedness)
Proof: strong induction on the process time; the successor-successor case
  proves the update measurable, then splits between refresh and recursive
  estimator finite sums using coordinate measurability from the footprint.
Source: Mathlib measurable finite sums and generated finite-block sigma-algebras
Used in: stochastic nonconvex conditional-gradient epoch-start adaptedness before
  a fresh refresh mini-batch
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem recursive_refresh_process_pair_measurable_before_epoch_start
    {Ω E Ξ State : Type*} [MeasurableSpace E] [MeasurableSpace Ξ]
    [AddCommMonoid E] [Sub E] [SMul ℝ E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E] [MeasurableConstSMul ℝ E]
    (mkState : E → E → ℕ → State)
    (xOf estimatorOf : State → E) (epochOf : State → ℕ)
    (x0 : E) (m b T N : ℕ)
    (ξ : ℕ → Ω → Ξ) (gradF : E → Ξ → E)
    (update : E → E → ℕ → E)
    (boundary : ℕ → ℕ) (footprint : ℕ → Finset ℕ)
    (hgradF : Measurable (fun p : E × Ξ => gradF p.1 p.2))
    (hupdate :
      ∀ (s n : ℕ) {x G : Ω → E},
        Measurable[sampleBlockMeasurableSpace ξ (footprint s)] x →
        Measurable[sampleBlockMeasurableSpace ξ (footprint s)] G →
        Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
          (fun ω => update (x ω) (G ω) n))
    (hx_mk : ∀ x G r, xOf (mkState x G r) = x)
    (hG_mk : ∀ x G r, estimatorOf (mkState x G r) = G)
    (hepoch_refresh :
      ∀ (s n : ℕ) (ω : Ω), n + 2 < boundary s → (n + 1) % T = 0 →
        epochOf
            (varianceReducedConditionalGradientProcess mkState xOf estimatorOf epochOf
              x0 m b T N ξ gradF update (n + 1) ω) + 1 =
          (n + 1) / T)
    (h_initial_refresh_mem :
      ∀ s i, 1 < boundary s → i < m → i ∈ footprint s)
    (h_epoch_refresh_mem :
      ∀ s n i, n + 2 < boundary s → (n + 1) % T = 0 → i < m →
        ((n + 1) / T) * m + i ∈ footprint s)
    (h_recursive_mem :
      ∀ s n i, n + 1 < boundary s → i < b →
        N * m + (n + 1) * b + i ∈ footprint s)
    (s k : ℕ) (hk : k < boundary s) :
    Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
      (fun ω =>
        (xOf
            (varianceReducedConditionalGradientProcess mkState xOf estimatorOf epochOf
              x0 m b T N ξ gradF update k ω),
          estimatorOf
            (varianceReducedConditionalGradientProcess mkState xOf estimatorOf epochOf
              x0 m b T N ξ gradF update k ω))) := by
  classical
  let process :=
    varianceReducedConditionalGradientProcess mkState xOf estimatorOf epochOf
      x0 m b T N ξ gradF update
  change Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
    (fun ω => (xOf (process k ω), estimatorOf (process k ω)))
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
      cases k with
      | zero =>
          simpa [-varianceReducedConditionalGradientProcess_def,
            process, varianceReducedConditionalGradientProcess, hx_mk, hG_mk] using
            (measurable_const :
              Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                (fun _ : Ω => (x0, (0 : E))))
      | succ k =>
          cases k with
          | zero =>
              have hx : Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                  (fun _ : Ω => x0) :=
                measurable_const
              have hGsum :
                  Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                    (fun ω =>
                      Finset.sum (Finset.range m)
                        (fun i => gradF x0 (ξ i ω))) :=
                measurable_finset_sum_kernel_comp_of_coordinate_measurable
                  (mΩ := sampleBlockMeasurableSpace ξ (footprint s))
                  (I := Finset.range m)
                  (K := fun p : E × Ξ => gradF p.1 p.2) hgradF hx ξ
                  (fun i => i)
                  (by
                    intro i hi
                    exact sampleBlock_coordinate_measurable ξ (fun q : ℕ => q)
                      (footprint s)
                      (h_initial_refresh_mem s i hk (Finset.mem_range.mp hi)))
              have hG : Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                  (fun ω =>
                    (m : ℝ)⁻¹ •
                      Finset.sum (Finset.range m)
                        (fun i => gradF x0 (ξ i ω))) :=
                hGsum.const_smul ((m : ℝ)⁻¹)
              simpa [-varianceReducedConditionalGradientProcess_def,
                process, varianceReducedConditionalGradientProcess, hx_mk, hG_mk] using
                hx.prodMk hG
          | succ n =>
              have hprev_lt : n + 1 < boundary s := by omega
              have hpair_prev :
                  Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                    (fun ω => (xOf (process (n + 1) ω),
                      estimatorOf (process (n + 1) ω))) :=
                ih (n + 1) (by omega) s hprev_lt
              have hx_prev :
                  Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                    (fun ω => xOf (process (n + 1) ω)) :=
                measurable_fst.comp hpair_prev
              have hG_prev :
                  Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                    (fun ω => estimatorOf (process (n + 1) ω)) :=
                measurable_snd.comp hpair_prev
              have hx_next :
                  Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                    (fun ω =>
                      update (xOf (process (n + 1) ω))
                        (estimatorOf (process (n + 1) ω)) (n + 1)) :=
                hupdate s (n + 1) hx_prev hG_prev
              by_cases hstart : (n + 1) % T = 0
              · have hGsum :
                    Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                      (fun ω =>
                        Finset.sum (Finset.range m)
                          (fun i =>
                            gradF
                              (update (xOf (process (n + 1) ω))
                                (estimatorOf (process (n + 1) ω)) (n + 1))
                              (ξ (((n + 1) / T) * m + i) ω))) :=
                  measurable_finset_sum_kernel_comp_of_coordinate_measurable
                    (mΩ := sampleBlockMeasurableSpace ξ (footprint s))
                    (I := Finset.range m)
                    (K := fun p : E × Ξ => gradF p.1 p.2) hgradF hx_next ξ
                    (fun i => ((n + 1) / T) * m + i)
                    (by
                      intro i hi
                      exact sampleBlock_coordinate_measurable ξ (fun q : ℕ => q)
                        (footprint s)
                        (h_epoch_refresh_mem s n i hk hstart (Finset.mem_range.mp hi)))
                have hG :
                    Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                      (fun ω =>
                        (m : ℝ)⁻¹ •
                          Finset.sum (Finset.range m)
                            (fun i =>
                              gradF
                                (update (xOf (process (n + 1) ω))
                                  (estimatorOf (process (n + 1) ω)) (n + 1))
                                (ξ (((n + 1) / T) * m + i) ω))) :=
                  hGsum.const_smul ((m : ℝ)⁻¹)
                have hepoch :
                    ∀ ω : Ω, epochOf (process (n + 1) ω) + 1 = (n + 1) / T :=
                  fun ω => hepoch_refresh s n ω hk hstart
                simpa [-varianceReducedConditionalGradientProcess_def,
                  process, varianceReducedConditionalGradientProcess, hstart,
                  hx_mk, hG_mk, hepoch] using hx_next.prodMk hG
              · have hGdiff :
                    Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                      (fun ω =>
                        Finset.sum (Finset.range b)
                          (fun i =>
                            gradF
                                (update (xOf (process (n + 1) ω))
                                  (estimatorOf (process (n + 1) ω)) (n + 1))
                                (ξ (N * m + (n + 1) * b + i) ω) -
                              gradF (xOf (process (n + 1) ω))
                                (ξ (N * m + (n + 1) * b + i) ω))) :=
                  measurable_finset_sum_kernel_diff_comp_of_coordinate_measurable
                    (mΩ := sampleBlockMeasurableSpace ξ (footprint s))
                    (I := Finset.range b)
                    (K := fun p : E × Ξ => gradF p.1 p.2)
                    hgradF hx_next hx_prev ξ
                    (fun i => N * m + (n + 1) * b + i)
                    (by
                      intro i hi
                      exact sampleBlock_coordinate_measurable ξ (fun q : ℕ => q)
                        (footprint s)
                        (h_recursive_mem s n i hprev_lt (Finset.mem_range.mp hi)))
                have hG :
                    Measurable[sampleBlockMeasurableSpace ξ (footprint s)]
                      (fun ω =>
                        (b : ℝ)⁻¹ •
                            Finset.sum (Finset.range b)
                              (fun i =>
                                gradF
                                    (update (xOf (process (n + 1) ω))
                                      (estimatorOf (process (n + 1) ω)) (n + 1))
                                    (ξ (N * m + (n + 1) * b + i) ω) -
                                  gradF (xOf (process (n + 1) ω))
                                    (ξ (N * m + (n + 1) * b + i) ω)) +
                          estimatorOf (process (n + 1) ω)) :=
                  (hGdiff.const_smul ((b : ℝ)⁻¹)).add hG_prev
                simpa [-varianceReducedConditionalGradientProcess_def,
                  process, varianceReducedConditionalGradientProcess, hstart,
                  hx_mk, hG_mk] using hx_next.prodMk hG

end SOptLib


-- From Staging/recursiveDelta_globalIndex_succ_eq.lean

-- Generalization plan (G0):
-- G0.1 naming: recursive_delta_global_index_succ_eq
--   (orig was: rawDeltaProcess_globalIndex_recursive; suggested name was
--   recursiveDelta_globalIndex_succ_eq). The staged name is snake_case and
--   describes the recursive estimator-residual identity at a global epoch
--   successor coordinate, without paper theorem numbers or local setup names.
-- G0.2 typeclass level used:
--   E: [AddCommMonoid E] [Sub E] [SMul ℝ E]; the proof uses only finite sums,
--      addition, subtraction, and real scalar multiplication by the mini-batch
--      denominator inverse. No norm, topology, inner product, completeness, or
--      finite-dimensional structure is used.
--   measure: none; the identity is pathwise before probability, filtration,
--      independence, integrability, or conditional expectation enters.
--   convexity: none; no feasible-set or objective geometry is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional-gradient raw recursive estimator
--      identities before transferring to well-defined iterates.
--   2. variance-reduced stochastic gradient and mirror-descent estimator-drift
--      recursions with mini-batch oracle differences inside fixed epochs.
-- G0.4 search trace:
--   queries: ["global index recursive", "successor recursion global index"]
--   top hits: ["deltaProcessOfWellDefined_globalIndex_recursive",
--     "deltaProcess_globalIndex_recursive", "deltaProcess_globalIndex_recursive_residual",
--     "global_index_recursive_of_succ",
--     "recursive_estimator_residual_global_index_eq_prev_add_centered_batch_diff",
--     "rawDeltaProcess_globalIndex_recursive"]
--   coverage: partial — `global_index_recursive_of_succ` covers the schedule
--     transport arithmetic, while the centered residual theorem has extra
--     finite-cardinality hypotheses and a paired centered conclusion; this
--     statement exposes the raw recursive-delta mini-batch oracle-difference
--     formula without those centering-specific assumptions.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   recursive-delta invariant linking previous/current iterates, fresh
--   mini-batch samples, oracle differences, and mean differences at global
--   epoch successor coordinates.
-- G0.5 structural-content rationale: the statement isolates the estimator
--   recursion formula consumed by variance-reduction proofs, while delegating
--   only the already-factored epoch-index arithmetic to the lower-level
--   transport lemma.
-- G0.5c thin-wrapper self-detect: clean — the body specializes the generic
--   index-transport theorem to the structured recursive-delta mini-batch
--   formula, rather than renaming the transport theorem under the same
--   hypotheses.
-- G0.5d minimal-hypothesis check: all already minimal; the proof uses only the
--   pointwise successor recursion and the pointwise epoch-coordinate bounds
--   `2 ≤ j` and `j ≤ T`.

namespace SOptLib

/-- A recursive delta process has the raw mini-batch global-index successor form.

If a delta process updates within an epoch by adding a mini-batch average of
oracle differences and subtracting the corresponding mean difference, then the
same identity holds at every one-based global epoch coordinate `2 ≤ j ≤ T`.

Layer: Layer1 | Gap: Level 1 (recursive delta mini-batch global-index identity)
Proof: specialize the fixed-length global-index successor-recursion transport
  theorem to the mini-batch oracle-difference increment and mean-difference
  correction.
Source: Mathlib finite sums, scalar actions, and natural-number epoch-index arithmetic
Used in: stochastic nonconvex conditional-gradient recursive estimator residual
  expansion before mini-batch variance control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem recursive_delta_global_index_succ_eq
    {Ω X S E : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (T batchSize sampleOffset : ℕ)
    (delta : ℕ → Ω → E) (x : ℕ → Ω → X) (sample : ℕ → Ω → S)
    (oracleDiff : X → X → S → E) (meanDiff : X → X → E)
    (hrec : ∀ k, (k + 1) % T ≠ 0 → ∀ ω,
      delta (k + 2) ω =
        delta (k + 1) ω +
          ((batchSize : ℝ)⁻¹) •
            Finset.sum (Finset.range batchSize)
              (fun i =>
                oracleDiff (x (k + 2) ω) (x (k + 1) ω)
                  (sample (sampleOffset + (k + 1) * batchSize + i) ω)) -
          meanDiff (x (k + 2) ω) (x (k + 1) ω))
    (s j : ℕ) (hj2 : 2 ≤ j) (hjT : j ≤ T) :
    ∀ ω,
      delta (global_index T s j) ω =
        delta (global_index T s (j - 1)) ω +
          ((batchSize : ℝ)⁻¹) •
            Finset.sum (Finset.range batchSize)
              (fun i =>
                oracleDiff (x (global_index T s j) ω)
                  (x (global_index T s (j - 1)) ω)
                  (sample
                    (sampleOffset + global_index T s (j - 1) * batchSize + i) ω)) -
          meanDiff (x (global_index T s j) ω)
            (x (global_index T s (j - 1)) ω) := by
  exact
    global_index_recursive_of_succ
      (T := T)
      (process := delta)
      (increment := fun k k' ω =>
        ((batchSize : ℝ)⁻¹) •
          Finset.sum (Finset.range batchSize)
            (fun i =>
              oracleDiff (x k' ω) (x k ω)
                (sample (sampleOffset + k * batchSize + i) ω)))
      (correction := fun k k' ω => meanDiff (x k' ω) (x k ω))
      (hrec := hrec)
      (s := s) (j := j) hj2 hjT

end SOptLib


-- From Staging/recursive_index_mem_epochStartFootprint_of_lt_cutoff.lean

-- Generalization plan (G0):
-- G0.1 naming: recursive_index_mem_epoch_start_sample_footprint_of_lt_cutoff
--   (orig was: recursive_index_mem_epochStartFootprint_of_lt_cutoff); renamed
--   to snake_case and to expose the mathematical object as a finite sample
--   footprint rather than paper-local camelCase notation.
-- G0.2 typeclass level used:
--   E: no carrier space; this is natural-number finite-sample index arithmetic.
--   measure: none; the theorem is the deterministic membership premise used
--     before finite sample-block measurability and independence arguments.
--   convexity: none; no objective geometry or feasible-set structure is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, proving recursive
--      mini-batch coordinates are inside the epoch-start sample history.
--   2. variance-reduced mirror descent or SARAH/SPIDER, recording that all
--      recursive samples before a cutoff are available in the sample footprint.
-- G0.4 search trace:
--   queries: ["Ico membership cutoff",
--     "natural number interval left right membership addition multiplication",
--     "epoch start footprint recursive index"]
--   top hits: ["recursive_index_mem_epoch_start_footprint_of_lt",
--     "recursive_index_mem_next_epoch_start_footprint",
--     "epoch_start_sample_footprint_subset_succ",
--     "refresh_index_not_mem_epoch_start_footprint_of_global_index_le",
--     "Finset.mem_Ico", "Finset.mem_range"]
--   coverage: partial — Mathlib has raw `Ico` membership facts and SOptLib has
--     successor footprint monotonicity, but no theorem packages membership of
--     a flattened recursive mini-batch coordinate in the cutoff footprint.
-- G0.4 not-a-thin-wrapper rationale: this packages the reusable invariant that
--   every coordinate `N*m+k*b+i` with `k < cutoff` and `i < b` lands in the
--   recursive half-open block of the epoch-start sample footprint.
-- G0.5 structural-content rationale: the statement connects the refresh prefix
--   plus recursive `Ico` footprint with flattened mini-batch indexing, the
--   exact arithmetic bridge repeatedly needed before sample-block reasoning;
--   the unused refresh-prefix cutoff is independent because membership is
--   proved through the recursive half-open branch.
-- G0.5c thin-wrapper self-detect: clean — the body derives positivity of the
--   batch size, lifts `k < cutoff` through multiplication by `b`, and proves
--   both endpoints of `Ico` membership.
-- G0.5d minimal-hypothesis check: all already minimal; only the pointwise
--   inequalities `k < cutoff` and `i < b` are used.

open scoped BigOperators

/-- A recursive mini-batch coordinate before a cutoff is in the recursive
half-open sample block.

For a flattened recursive sample coordinate `N*m+k*b+i`, if the mini-batch
number `k` is strictly before the recursive cutoff and `i` is inside the
mini-batch, then the coordinate belongs to the recursive half-open block
starting at the epoch-start sample offset.

Layer: Layer1 | Gap: Level 1 (recursive mini-batch sample-footprint membership)
Proof: prove the lower `Ico` endpoint by monotonicity, and prove the upper
  endpoint by bounding
  `k*b+i` by `(k+1)*b ≤ cutoff*b`.
Source: Mathlib finite-set interval membership and natural-number arithmetic APIs
Used in: stochastic variance-reduced conditional-gradient epoch-start
  measurability of accumulated recursive mini-batch sample histories
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem recursive_index_mem_Ico_of_lt_cutoff
    {N m b cutoff k i : ℕ}
    (hk : k < cutoff) (hi : i < b) :
    N * m + k * b + i ∈ Finset.Ico (N * m) (N * m + cutoff * b) := by
  refine Finset.mem_Ico.mpr ⟨by omega, ?_⟩
  have hbpos : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hkb : k * b + i < (k + 1) * b := by
    nlinarith
  have hkle : k + 1 ≤ cutoff := Nat.succ_le_of_lt hk
  have hmul : (k + 1) * b ≤ cutoff * b :=
    Nat.mul_le_mul_right b hkle
  omega


-- From Staging/refresh_index_mem_later_epochStartFootprint_of_epoch_lt.lean

-- Generalization plan (G0):
-- G0.1 naming: refresh_index_mem_later_epoch_start_sample_footprint_of_epoch_lt
--   (orig was: refresh_index_mem_later_epochStartFootprint_of_epoch_lt); renamed
--   to Mathlib-style snake_case while preserving the refresh-prefix
--   sample-footprint membership statement.
-- G0.2 typeclass level used:
--   E: no carrier space; this is natural-number finite-sample index arithmetic.
--   measure: none; this deterministic footprint fact is consumed before
--     finite sample-block measurability and independence arguments.
--   convexity: none; no objective geometry or feasible-set structure is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, proving earlier
--      epoch-refresh samples are in a later epoch-start sample history.
--   2. variance-reduced mirror descent or SARAH/SPIDER, recording that all
--      completed refresh mini-batches are available in later epoch histories.
-- G0.4 search trace:
--   queries: ["Finset Ico union membership",
--     "natural number multiplication less range Ico"]
--   top hits: ["recursive_index_mem_Ico_of_lt_cutoff",
--     "refresh_index_mem_next_epoch_start_footprint",
--     "refresh_index_not_mem_epoch_start_footprint_of_global_index_le",
--     "epoch_start_sample_footprint_subset_succ",
--     "Finset.mem_range", "Finset.mem_Ico"]
--   coverage: partial — Mathlib has raw range/union membership facts and
--     SOptLib has recursive-coordinate and successor-footprint lemmas, but no
--     theorem packages earlier refresh-coordinate membership in a later
--     refresh-prefix footprint with an arbitrary recursive tail.
-- G0.4 not-a-thin-wrapper rationale: this packages the reusable invariant that
--   every coordinate `r*m+i` of a completed refresh mini-batch, with `r < s`,
--   lies in the refresh-prefix branch of any later epoch-start sample footprint.
-- G0.5 structural-content rationale: the statement connects flattened
--   epoch-refresh indexing with finite footprint membership while abstracting
--   away the unused recursive tail as an arbitrary finset.
-- G0.5c thin-wrapper self-detect: clean — the body proves the refresh-prefix
--   range bound from strict epoch order and within-mini-batch membership.
-- G0.5d minimal-hypothesis check: all already minimal; only `r < s` and the
--   pointwise within-refresh bound `i < m` are used.

open scoped BigOperators

/-- An earlier epoch refresh coordinate is in any later refresh-prefix footprint.

For a fixed refresh mini-batch size `m`, if epoch `r` is strictly before epoch
`s` and `i` is inside the refresh mini-batch, then the flattened coordinate
`r*m+i` belongs to the refresh-prefix branch `range (s*m)`. Consequently it
belongs to any epoch-start sample footprint whose first branch is that prefix.

Layer: Layer1 | Gap: Level 1 (later epoch refresh-prefix membership)
Proof: split membership in the union and prove the range branch by bounding
  `r*m+i < (r+1)*m ≤ s*m`.
Source: Mathlib finite-set range membership and natural-number order arithmetic APIs
Used in: stochastic variance-reduced conditional-gradient epoch-start
  measurability of accumulated refresh mini-batch sample histories
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem refresh_index_mem_later_epoch_start_sample_footprint_of_epoch_lt
    {m s r i : ℕ} (tail : Finset ℕ)
    (hr : r < s) (hi : i < m) :
    r * m + i ∈ Finset.range (s * m) ∪ tail := by
  rw [Finset.mem_union]
  left
  exact Finset.mem_range.mpr (by
    have hri : r * m + i < (r + 1) * m := by
      have htmp : r * m + i < r * m + m := by omega
      simpa [Nat.succ_mul] using htmp
    have hle : (r + 1) * m ≤ s * m := by
      exact Nat.mul_le_mul_right m (Nat.succ_le_of_lt hr)
    exact lt_of_lt_of_le hri hle)


-- From Staging/integral_nonneg_le_add_of_integral_sq_le_add_sq.lean

-- Generalization plan (G0):
-- G0.1 naming: integral_nonneg_le_add_of_integral_sq_le_add_sq
-- G0.2 typeclass level used:
--   E: none; the theorem is scalar-valued and only uses real ordered-ring
--      arithmetic on probability integrals.
--   measure: arbitrary probability measure `(mu : Measure Omega)` via
--      `[IsProbabilityMeasure mu]`, because the proof uses the probability-space
--      L2 contraction of expectation.
--   convexity: none; this is a measure-theoretic L2-to-L1 bridge.
-- G0.3 reusability -- could instantiate:
--   1. stochastic nonconvex conditional gradient estimator-error L1 absorption
--      from an epochwise second-moment budget plus a mini-batch variance floor.
--   2. stochastic mirror descent or stochastic proximal-gradient oracle-noise
--      L1 control when deterministic and variance second-moment contributions
--      are tracked separately.
-- G0.4 search trace:
--   queries: ["integral nonnegative square",
--     "expectation bounded by square root second moment"]
--   top hits: ["integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one",
--     "integral_nonneg_le_of_integral_sq_le_sq", "sq_integral_le_integral_sq",
--     "blockOracleSecondMomentExpectation",
--     "dualNorm_mean_sq_le_second_moment_bound"]
--   coverage: partial -- `sq_integral_le_integral_sq` gives the squared-mean
--     contraction and `integral_nonneg_le_of_integral_sq_le_sq` covers a
--     single square bound, while this theorem preserves two nonnegative square
--     contributions and returns the split `A + C` bound.
-- G0.4 not-a-thin-wrapper rationale: the declaration combines measurability
--   recovery, probability L2 contraction, an external two-source square budget,
--   and the ordered-real comparison `A^2 + C^2 <= (A + C)^2`.
-- G0.5 structural-content rationale: the theorem exposes the standard
--   nonnegative L2-to-L1 implication for stochastic estimators with separate
--   deterministic and variance-floor budgets.
-- G0.5c thin-wrapper self-detect: clean -- body has multiple substantive
--   steps beyond a direct alias of one Mathlib or SOptLib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; nonnegativity is a.e.,
--   square-integrability is exactly needed for measurability and L2
--   contraction, and `0 <= A`, `0 <= C` are used only in the final square
--   comparison.


open MeasureTheory ProbabilityTheory

/-- A nonnegative scalar random variable has expectation at most `A + C` when
its second moment is bounded by `A^2 + C^2`.

On a probability space this is the common `L2` to `L1` passage for stochastic
estimator majorants with two separately tracked square contributions.

Layer: Glue | Gap: Level 1 (split nonnegative scalar L2-to-L1 moment bound)
Proof: recover a.e. strong measurability from square-integrability and a.e.
  nonnegativity, use the scalar probability second-moment contraction, then
  compare `A^2 + C^2` with `(A + C)^2` by ordered real arithmetic.
Source: Mathlib probability variance API and real ordered-ring square comparison
Used in: stochastic nonconvex conditional-gradient estimator-error L1 absorption
  with epoch-difference penalty and mini-batch variance floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_nonneg_le_add_of_integral_sq_le_add_sq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {Z : Omega -> ℝ} {A C : ℝ}
    (hZ_sq_int : Integrable (fun omega => Z omega ^ 2) mu)
    (hZ_nonneg : ∀ᵐ omega ∂mu, 0 <= Z omega)
    (hA_nonneg : 0 <= A)
    (hC_nonneg : 0 <= C)
    (hZ_sq_le : ∫ omega, Z omega ^ 2 ∂mu <= A ^ 2 + C ^ 2) :
    ∫ omega, Z omega ∂mu <= A + C := by
  have hZ_meas : AEStronglyMeasurable Z mu :=
    AEStronglyMeasurable.of_integrable_sq_of_nonneg hZ_sq_int hZ_nonneg
  have hsq_l1 :
      (∫ omega, Z omega ∂mu) ^ 2 <= ∫ omega, Z omega ^ 2 ∂mu :=
    sq_integral_le_integral_sq hZ_meas hZ_sq_int
  have hsq_bound : (∫ omega, Z omega ∂mu) ^ 2 <= A ^ 2 + C ^ 2 :=
    le_trans hsq_l1 hZ_sq_le
  have hleft_nonneg : 0 <= ∫ omega, Z omega ∂mu :=
    integral_nonneg_of_ae hZ_nonneg
  have hsum_sq : A ^ 2 + C ^ 2 <= (A + C) ^ 2 := by
    nlinarith [hA_nonneg, hC_nonneg]
  nlinarith


-- From Staging/integral_one_step_gap_bound_of_pointwise.lean

open MeasureTheory

-- Generalization plan (G0):
-- G0.1 naming: integral_one_step_gap_bound_of_pointwise (orig was: integral_one_step_gap_bound_of_pointwise)
-- G0.2 typeclass level used:
--   E: none; the theorem is scalar after the algorithm has converted the descent step to real-valued gap, drop, and second-moment terms.
--   measure: arbitrary `Measure Ω` with `[IsProbabilityMeasure P]`, needed exactly to rewrite the integral of the deterministic constant as that constant.
--   convexity: none; smoothness and conditional-gradient facts enter only through the pointwise scalar hypothesis.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional-gradient one-step Wolfe-gap expectation bridge
--   2. stochastic mirror-descent or proximal-gradient one-step descent after estimator-error second moments are exposed
-- G0.4 search trace:
--   queries: ["integral one step gap", "integral pointwise bound measurable integrable"]
--   top hits: ["integral_one_step_gap_source_form_of_pointwise", "SOptLib.Glue.Probability.integral_le_integral_affine_combination", "SOptLib.Layer1.Telescope.integral_sum_telescope_bound_of_pointwise_lower_bound", "MeasureTheory.integral_mono", "MeasureTheory.integral_mono_ae"]
--   coverage: partial — overlaps in integral monotonicity and linearity, but no hit subsumes the three-term printed one-step split with one square term and one probability-space constant.
-- G0.4 not-a-thin-wrapper rationale: packages the reusable invariant that a pointwise scaled-gap bound with a single second-moment term and deterministic budget survives expectation with the same algebraic coefficients.
-- G0.5 structural-content rationale: the theorem combines integrability assembly, integral monotonicity, scalar pull-out, additive splitting, and probability-space constant evaluation.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step content and does not call the existing source-form theorem as a specialization.
-- G0.5d minimal-hypothesis check: all already minimal; only integrability of the three scalar functions and a pointwise inequality are required.

/-- Integrate a pointwise one-step scaled-gap bound and split the printed terms.

If a scaled gap is pointwise bounded by an objective drop, a scaled second
moment, and a deterministic budget, then the same three-term inequality holds
after taking expectation under a probability measure.

Layer: Layer1 | Gap: Level 1 (one-step expected scaled-gap bound)
Proof: assemble integrability of the three-term upper bound, apply Bochner
  integral monotonicity, and split the upper integral using additivity,
  constant-scalar pull-out, and probability-space constant integration.
Source: Mathlib Bochner integral monotonicity and linearity APIs
Used in: stochastic conditional-gradient one-step Wolfe-gap expectation bridge
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_one_step_gap_bound_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (gap drop deltaSq : Ω → ℝ)
    (a cDelta c : ℝ)
    (hgap_int : Integrable gap P)
    (hdrop_int : Integrable drop P)
    (hdeltaSq_int : Integrable deltaSq P)
    (hpoint : ∀ ω, a * gap ω ≤ drop ω + cDelta * deltaSq ω + c) :
    a * ∫ ω, gap ω ∂P ≤
      ∫ ω, drop ω ∂P + cDelta * ∫ ω, deltaSq ω ∂P + c := by
  let upper : Ω → ℝ := fun ω => drop ω + cDelta * deltaSq ω + c
  have hleft_int : Integrable (fun ω => a * gap ω) P :=
    hgap_int.const_mul a
  have hdrop_delta_int : Integrable (fun ω => drop ω + cDelta * deltaSq ω) P :=
    hdrop_int.add (hdeltaSq_int.const_mul cDelta)
  have hupper_int : Integrable upper P :=
    hdrop_delta_int.add (integrable_const (c := c))
  have hmono :
      ∫ ω, a * gap ω ∂P ≤ ∫ ω, upper ω ∂P := by
    exact integral_mono hleft_int hupper_int hpoint
  have hupper_eq :
      ∫ ω, upper ω ∂P =
        ∫ ω, drop ω ∂P + cDelta * ∫ ω, deltaSq ω ∂P + c := by
    calc
      ∫ ω, upper ω ∂P
          =
          ∫ ω, drop ω + cDelta * deltaSq ω ∂P + ∫ _ω, c ∂P := by
            exact integral_add hdrop_delta_int (integrable_const (c := c))
      _ =
          (∫ ω, drop ω ∂P + ∫ ω, cDelta * deltaSq ω ∂P) + c := by
            rw [integral_add hdrop_int (hdeltaSq_int.const_mul cDelta)]
            simp [integral_const, probReal_univ]
      _ =
          ∫ ω, drop ω ∂P + cDelta * ∫ ω, deltaSq ω ∂P + c := by
            rw [integral_const_mul]
  calc
    a * ∫ ω, gap ω ∂P
        = ∫ ω, a * gap ω ∂P := by
          rw [integral_const_mul]
    _ ≤ ∫ ω, upper ω ∂P := hmono
    _ =
      ∫ ω, drop ω ∂P + cDelta * ∫ ω, deltaSq ω ∂P + c := hupper_eq


-- From Staging/iterProcess_succ_eq_update_of_process_recursion.lean

-- Generalization plan (G0):
-- G0.1 naming: iterProcess_succ_eq_update_of_process_recursion. The requested
--   name is retained for backfill compatibility; it has no paper theorem,
--   section, author, or local-constant markers.
-- G0.2 typeclass level used:
--   E: [AddCommMonoid E] [Sub E] [SMul ℝ E], exactly the algebra needed by the
--      variance-reduced conditional-gradient process definition for minibatch
--      sums, differences, scalar averages, and the zero initial estimator.
--      No norm, topology, inner product, completeness, or finite-dimensionality
--      is used.
--   measure: none; this is a pathwise process-unfolding identity before
--      probability, filtration, measurability, independence, or integrability
--      hypotheses enter.
--   convexity: none; feasible-set and LMO geometry are downstream of the
--      generated-process update equation.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient smooth one-step descent, after
--      unfolding the variance-reduced iterate/estimator state process
--   2. variance-reduced mirror descent or stochastic proximal-gradient processes
--      that store an iterate, recursive estimator, and epoch counter in state
-- G0.4 search trace:
--   queries: ["iter process update recursion",
--     "successor recursive sequence equals update",
--     "variance reduced conditional gradient process successor update"]
--   top hits: ["iterProcess_succ_eq_iterUpdate",
--     "stochastic_iterProcessOfWellDefined_succ_eq_iterUpdate",
--     "finite_sum_conditional_gradient_process_state_x_succ_eq_update",
--     "SOptLib.recursiveIterateProcess_succ",
--     "SOptLib.iterateProcess_bridge_of_recursiveProcess",
--     "SOptLib.varianceReducedConditionalGradientProcess_succ_eq_step",
--     "SOptLib.varianceReducedConditionalGradientProcess_succ_succ",
--     "SOptLib.ConditionalGradientState.varianceReducedConditionalGradientStep_succ_x"]
--   coverage: partial — the recursive-process bridges unfold a raw successor
--     step, the finite-sum theorem targets a different generated process, and
--     the canonical-state theorem fixes the state record; this theorem adds the
--     reusable positive-time iterate-projection invariant for an abstract state
--     constructor of the variance-reduced process.
-- G0.4 not-a-thin-wrapper rationale: the statement packages the common
--   variance-reduced state-process invariant that, after the initialized first
--   state, the iterate projection advances by the supplied update applied to
--   the previous iterate and estimator projections.
-- G0.5 structural-content rationale: this is a theorem over an existing process
--   definition, not a new wrapper def; it combines positive-index case analysis,
--   epoch-refresh process unfolding, and abstract state-constructor projection.
-- G0.5c thin-wrapper self-detect: clean — the proof is not a direct single-call
--   alias of a Mathlib or SOptLib lemma; it specializes the successor-after-
--   successor recursion through an abstract state accessor law and discharges
--   the impossible initialized-time branch.
-- G0.5d minimal-hypothesis check: all already minimal; the only
--   non-definitional hypothesis is the pointwise constructor projection law
--   `h_mkState_x`.

namespace SOptLib

/-- The iterate projection of a variance-reduced process advances by the
supplied update after the initialized first state.

For a variance-reduced conditional-gradient state process whose state
constructor stores the iterate in an accessor `stateX`, every positive time `k`
satisfies the expected pathwise update equation for the iterate projection.

Layer: Model | Gap: Level 1 (variance-reduced process iterate-update projection)
Proof: split the natural time index; the impossible zero case is arithmetic,
  and the successor case unfolds the variance-reduced recursion and rewrites
  the iterate projection of the constructed next state.
Source: Mathlib natural-number recursion, finite-sum, and state-projection
  rewriting APIs
Used in: stochastic nonconvex conditional gradient smooth one-step descent
  after generated-process unfolding
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem iterProcess_succ_eq_update_of_process_recursion
    {Ω State E S : Type*} [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (x0 : E)
    (m b T N : ℕ)
    (sample : ℕ → Ω → S)
    (gradF : E → S → E)
    (update : E → E → ℕ → E)
    (h_mkState_x : ∀ x G s, stateX (mkState x G s) = x)
    {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    stateX
        (varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
          x0 m b T N sample gradF update (k + 1) ω) =
      update
        (stateX
          (varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
            x0 m b T N sample gradF update k ω))
        (stateEstimator
          (varianceReducedConditionalGradientProcess mkState stateX stateEstimator stateEpoch
            x0 m b T N sample gradF update k ω))
        k := by
  cases k with
  | zero =>
      omega
  | succ n =>
      rw [varianceReducedConditionalGradientProcess_succ_succ]
      simp [-varianceReducedConditionalGradientProcess_def, h_mkState_x]

end SOptLib


-- From Staging/wolfe_gap_descent_printed_of_true_gradient_descent.lean

open scoped InnerProductSpace

namespace SOptLib.ConditionalGradient

-- Generalization plan (G0):
-- G0.1 naming: wolfeGap_descent_of_trueGradient_linearMinimizer_descent
--   (orig was: wolfe_gap_descent_printed_of_true_gradient_descent; renamed to
--   remove the paper-local "printed" marker and name the conditional-gradient
--   Wolfe-gap descent concept).
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses
--      subtraction, norms, real inner products, Cauchy-Schwarz, Young
--      absorption, and ordered-field algebra. No finite-dimensionality,
--      completeness, compactness, or topology is used.
--   measure: none; this is deterministic one-step conditional-gradient algebra.
--   convexity: none; after an LMO comparison and a pointwise feasible-pair
--      diameter bound are supplied, no global convexity hypothesis is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, combining true-gradient
--      smooth descent with Wolfe-gap LMO comparison before estimator-error
--      Young absorption.
--   2. finite-sum nonconvex conditional gradient, the same one-step stationarity
--      descent step when a finite-sum gradient estimator drives the LMO.
-- G0.4 search trace:
--   queries: ["wolfe gap descent", "true gradient descent smooth inner"]
--   top hits: ["finite_one_step_gap_descent_pointwise",
--     "stochastic_one_step_gap_descent_pointwise_printed",
--     "SOptLib.ConditionalGradient.wolfeGap_le_linearMinimizer_model_plus_gradient_error_mul_diameter",
--     "conditional_gradient_smooth_descent_premise_of_estimator",
--     "smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex"]
--   coverage: partial — existing Wolfe-gap surrogate hits bound the gap before
--      descent, and the smooth-descent premise hit proves the preceding update
--      inequality; none package the sharper combined true-gradient/L1-linear
--      cancellation that leaves a single `1/(2L) * ‖G - grad x‖^2` term.
-- G0.4 not-a-thin-wrapper rationale: the theorem combines selected Wolfe-gap
--   expansion, LMO comparison in the estimator direction, true-gradient descent
--   rearrangement, Cauchy-Schwarz diameter control, and scaled Young absorption.
-- G0.5 structural-content rationale: the statement uses the concrete
--   `wolfeGap` model object and a direct LMO argmin certificate rather than an
--   abstract gap function with a formula hypothesis.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step inner-product
--   algebra and Young absorption, not a direct single Mathlib or SOptLib alias.
-- G0.5d minimal-hypothesis check: all already minimal; LMO comparison is needed
--   only at the selected maximizer, represented by the pointwise LMO
--   comparison, and the diameter bound is pointwise for the pair actually used.

/-- One-step Wolfe-gap descent from a true-gradient LMO descent inequality.

If the objective decrease is already available with the true gradient paired
against the estimator-driven linear-minimizer step, then the selected Wolfe gap
can be bounded by combining the LMO comparison in the estimator direction with
that descent inequality before applying one Young inequality to
`G - grad x`.

Layer: Layer1 | Gap: Level 1 (conditional-gradient combined Wolfe/descent algebra)
Proof: expand the selected Wolfe gap, use the LMO comparison to replace the
  selected maximizer by the estimator LMO, rearrange the true-gradient descent
  premise, and control the remaining estimator-error inner product by
  Cauchy-Schwarz plus scaled Young absorption.
Source: Frank-Wolfe conditional-gradient one-step descent calculus, real
  Hilbert-space Cauchy-Schwarz, and ordered-field Young inequality
Used in: stochastic and finite-sum nonconvex conditional-gradient one-step
  stationarity descent before summing estimator second moments
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem wolfeGap_descent_of_trueGradient_linearMinimizer_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (f : E → ℝ) (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (linearMinimizer : E → E)
    (x G xnext : E) (a L D : ℝ)
    (hL_pos : 0 < L) (ha_nonneg : 0 ≤ a)
    (h_lmo :
      ⟪G, linearMinimizer G⟫_ℝ ≤ ⟪G, (maximizer x : E)⟫_ℝ)
    (hdiam :
      ‖(maximizer x : E) - linearMinimizer G‖ ≤ D)
    (hdescent :
      f xnext ≤
        f x + a * ⟪grad x, linearMinimizer G - x⟫_ℝ +
          (L / 2) * a ^ 2 * D ^ 2) :
    a * wolfeGap grad maximizer x ≤
      f x - f xnext +
        (1 / (2 * L)) * ‖G - grad x‖ ^ 2 +
        L * a ^ 2 * D ^ 2 := by
  classical
  let y : E := linearMinimizer G
  let z : {z : E // z ∈ X} := maximizer x
  let d : E := G - grad x
  have hG_decomp : G = grad x + d := by
    dsimp [d]
    abel
  have hgap_eq :
      wolfeGap grad maximizer x = ⟪grad x, x - (z : E)⟫_ℝ := by
    simp [wolfeGap, z]
  have hG_lmo : ⟪G, y⟫_ℝ ≤ ⟪G, (z : E)⟫_ℝ := by
    dsimp [y]
    exact h_lmo
  have hG_xz_le_xy : ⟪G, x - (z : E)⟫_ℝ ≤ ⟪G, x - y⟫_ℝ := by
    have hdiff : ⟪G, x - (z : E)⟫_ℝ - ⟪G, x - y⟫_ℝ =
        ⟪G, y⟫_ℝ - ⟪G, (z : E)⟫_ℝ := by
      rw [inner_sub_right, inner_sub_right]
      ring
    linarith
  have hgap_linear :
      wolfeGap grad maximizer x ≤
        ⟪grad x, x - y⟫_ℝ + ⟪d, (z : E) - y⟫_ℝ := by
    rw [hgap_eq]
    have hdecomp_z :
        ⟪grad x, x - (z : E)⟫_ℝ =
          ⟪G, x - (z : E)⟫_ℝ - ⟪d, x - (z : E)⟫_ℝ := by
      rw [hG_decomp, inner_add_left]
      ring
    have hdecomp_y :
        ⟪G, x - y⟫_ℝ - ⟪d, x - (z : E)⟫_ℝ =
          ⟪grad x, x - y⟫_ℝ + ⟪d, (z : E) - y⟫_ℝ := by
      rw [hG_decomp, inner_add_left]
      have hinner : ⟪d, x - y⟫_ℝ - ⟪d, x - (z : E)⟫_ℝ =
          ⟪d, (z : E) - y⟫_ℝ := by
        rw [inner_sub_right, inner_sub_right, inner_sub_right]
        ring
      linarith
    calc
      ⟪grad x, x - (z : E)⟫_ℝ =
          ⟪G, x - (z : E)⟫_ℝ - ⟪d, x - (z : E)⟫_ℝ := hdecomp_z
      _ ≤ ⟪G, x - y⟫_ℝ - ⟪d, x - (z : E)⟫_ℝ := by
        linarith
      _ = ⟪grad x, x - y⟫_ℝ + ⟪d, (z : E) - y⟫_ℝ := hdecomp_y
  have hgap_mul :
      a * wolfeGap grad maximizer x ≤
        a * ⟪grad x, x - y⟫_ℝ + a * ⟪d, (z : E) - y⟫_ℝ := by
    have hmul := mul_le_mul_of_nonneg_left hgap_linear ha_nonneg
    nlinarith
  have hdesc_rearr :
      a * ⟪grad x, x - y⟫_ℝ ≤
        f x - f xnext + (L / 2) * a ^ 2 * D ^ 2 := by
    dsimp [y] at hdescent ⊢
    have hneg : ⟪grad x, y - x⟫_ℝ = -⟪grad x, x - y⟫_ℝ := by
      have hyx : y - x = -(x - y) := by
        abel
      rw [hyx, inner_neg_right]
    rw [hneg] at hdescent
    nlinarith
  have hcross_linear :
      a * ⟪d, (z : E) - y⟫_ℝ ≤ a * (‖d‖ * D) := by
    have hinner :
        ⟪d, (z : E) - y⟫_ℝ ≤ ‖d‖ * ‖(z : E) - y‖ := by
      calc
        ⟪d, (z : E) - y⟫_ℝ ≤ |⟪d, (z : E) - y⟫_ℝ| := le_abs_self _
        _ ≤ ‖d‖ * ‖(z : E) - y‖ := abs_real_inner_le_norm d ((z : E) - y)
    have hinnerD : ⟪d, (z : E) - y⟫_ℝ ≤ ‖d‖ * D := by
      exact le_trans hinner (mul_le_mul_of_nonneg_left (by simpa [z, y] using hdiam) (norm_nonneg d))
    exact mul_le_mul_of_nonneg_left hinnerD ha_nonneg
  have hyoung :
      a * (‖d‖ * D) ≤
        (1 / (2 * L)) * ‖d‖ ^ 2 +
          (L / 2) * a ^ 2 * D ^ 2 := by
    have hsq : 0 ≤ (‖d‖ - L * a * D) ^ 2 := sq_nonneg _
    have hmain :
        2 * L * (a * (‖d‖ * D)) ≤
          ‖d‖ ^ 2 + L ^ 2 * a ^ 2 * D ^ 2 := by
      nlinarith [hsq]
    have hden_pos : 0 < 2 * L := mul_pos two_pos hL_pos
    calc
      a * (‖d‖ * D) = (2 * L * (a * (‖d‖ * D))) / (2 * L) := by
        have hden_ne : 2 * L ≠ 0 := ne_of_gt hden_pos
        calc
          a * (‖d‖ * D) = (a * (‖d‖ * D)) * ((2 * L) / (2 * L)) := by
            rw [div_self hden_ne]
            ring
          _ = (2 * L * (a * (‖d‖ * D))) / (2 * L) := by
            field_simp [hden_ne]
      _ ≤ (‖d‖ ^ 2 + L ^ 2 * a ^ 2 * D ^ 2) / (2 * L) := by
        exact div_le_div_of_nonneg_right hmain (le_of_lt hden_pos)
      _ = (1 / (2 * L)) * ‖d‖ ^ 2 +
          (L / 2) * a ^ 2 * D ^ 2 := by
        field_simp [ne_of_gt hL_pos, ne_of_gt hden_pos]
  calc
    a * wolfeGap grad maximizer x
        ≤ a * ⟪grad x, x - y⟫_ℝ + a * ⟪d, (z : E) - y⟫_ℝ := hgap_mul
    _ ≤
        (f x - f xnext + (L / 2) * a ^ 2 * D ^ 2) +
          ((1 / (2 * L)) * ‖d‖ ^ 2 +
            (L / 2) * a ^ 2 * D ^ 2) := by
      exact add_le_add hdesc_rearr (le_trans hcross_linear hyoung)
    _ =
      f x - f xnext +
        (1 / (2 * L)) * ‖G - grad x‖ ^ 2 +
        L * a ^ 2 * D ^ 2 := by
      dsimp [d]
      ring

end SOptLib.ConditionalGradient


-- From Staging/wolfe_gap_descent_source_form_of_smooth_descent.lean

open scoped InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: wolfe_gap_descent_source_form_of_smooth_descent
--   (orig was: wolfe_gap_descent_source_form_of_smooth_descent; the name
--   describes conditional-gradient Wolfe-gap descent before Young absorption
--   and has no paper-internal marker).
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses
--      subtraction, real inner products, norms, and ordered real algebra, with
--      no finite-dimensionality, completeness, compactness, or measurability.
--   measure: none; this is deterministic pointwise one-step algebra.
--   convexity: none; smoothness, LMO geometry, and the Wolfe-gap surrogate are
--      reduced to the two pointwise hypotheses actually consumed.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, before integrating the
--      source-form one-step Wolfe-gap bound and applying scalar epoch budgets.
--   2. finite-sum nonconvex conditional gradient and variance-reduced
--      Frank-Wolfe, when the residual norm term must be preserved for a later
--      expectation or variance estimate instead of immediately Young-absorbed.
-- G0.4 search trace:
--   queries: ["Wolfe gap descent", "smooth descent gap source form",
--     "inner linear minimizer descent residual diameter"]
--   top hits: ["conditional_gradient_wolfe_gap_one_step_descent_of_smooth",
--     "wolfeGap_descent_of_trueGradient_linearMinimizer_descent",
--     "finite_one_step_gap_descent_pointwise_source_form",
--     "stochastic_one_step_gap_descent_pointwise_source_form",
--     "wolfeGap_le_linearMinimizer_model_plus_gradient_error_mul_diameter",
--     "integral_one_step_gap_source_form_of_pointwise"]
--   coverage: partial — existing public hits either prove the Wolfe-gap
--     surrogate before descent, integrate a supplied pointwise source-form
--     bound, or Young-absorb the residual product; target-file private hits
--     have paper setup parameters and are not reusable declarations.
-- G0.4 not-a-thin-wrapper rationale: combines a pointwise Wolfe-gap surrogate,
--   multiplication by a nonnegative stepsize, inner-product sign reversal, and
--   rearrangement of a smooth descent premise while preserving the source
--   residual norm product for downstream expectation estimates.
-- G0.5 structural-content rationale: theorem only; it introduces no wrapper
--   structure or formula-bodied definition and exposes a reusable one-step
--   source-form descent invariant.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step inner-product
--   sign algebra, descent rearrangement, and coefficient collection, and is
--   not a direct call to an existing theorem.
-- G0.5d minimal-hypothesis check: all already minimal; all global smoothness,
--   feasible-set, and LMO assumptions have been reduced to the two pointwise
--   inequalities at the current iterate.

/-- A Wolfe-gap surrogate plus a smooth conditional-gradient descent premise
gives the source-form one-step gap descent inequality.

The residual-diameter product is deliberately left unabsorbed. This is the
form used when a later expectation, Cauchy-Schwarz, or variance estimate should
control `alpha * D * ‖delta‖` instead of spending a Young inequality locally.

Layer: Layer1 | Gap: Level 1 (conditional-gradient Wolfe-gap source-form descent)
Proof: multiply the surrogate bound by the nonnegative stepsize, rewrite
  `⟪G, x - y⟫` as `-⟪G, y - x⟫`, rearrange the descent premise, and collect
  the unabsorbed residual-diameter term.
Source: Frank-Wolfe conditional-gradient one-step descent algebra and real
  Hilbert-space inner-product identities
Used in: stochastic and finite-sum nonconvex conditional-gradient one-step
  Wolfe-gap bounds before expectation and variance-budget aggregation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem wolfe_gap_descent_source_form_of_smooth_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gap f : E → ℝ) (lmo : E → E) (delta : E → E → E)
    (x G xnext : E) (alpha L D : ℝ)
    (halpha_nonneg : 0 ≤ alpha)
    (hgap :
      gap x ≤ ⟪G, x - lmo G⟫_ℝ + ‖delta G x‖ * D)
    (hdescent :
      f xnext ≤
        f x + alpha * ⟪G, lmo G - x⟫_ℝ +
          (1 / (2 * L)) * ‖delta G x‖ ^ 2 +
          L * alpha ^ 2 * D ^ 2) :
    alpha * gap x ≤
      f x - f xnext +
        (1 / (2 * L)) * ‖delta G x‖ ^ 2 +
        L * alpha ^ 2 * D ^ 2 +
        alpha * D * ‖delta G x‖ := by
  let y : E := lmo G
  let d : ℝ := ‖delta G x‖
  have hgap_mul :
      alpha * gap x ≤ alpha * (⟪G, x - y⟫_ℝ + d * D) := by
    exact mul_le_mul_of_nonneg_left (by simpa [y, d] using hgap) halpha_nonneg
  have hinner_neg : ⟪G, x - y⟫_ℝ = -⟪G, y - x⟫_ℝ := by
    have hxy : x - y = -(y - x) := by
      abel
    rw [hxy, inner_neg_right]
  have hdesc_rearr :
      -alpha * ⟪G, y - x⟫_ℝ ≤
        f x - f xnext +
          (1 / (2 * L)) * d ^ 2 +
          L * alpha ^ 2 * D ^ 2 := by
    dsimp [y, d] at hdescent ⊢
    linarith
  calc
    alpha * gap x
        ≤ alpha * (⟪G, x - y⟫_ℝ + d * D) := hgap_mul
    _ = -alpha * ⟪G, y - x⟫_ℝ + alpha * (d * D) := by
        rw [hinner_neg]
        ring
    _ ≤
        (f x - f xnext +
          (1 / (2 * L)) * d ^ 2 +
          L * alpha ^ 2 * D ^ 2) + alpha * (d * D) := by
        linarith
    _ =
      f x - f xnext +
        (1 / (2 * L)) * ‖delta G x‖ ^ 2 +
        L * alpha ^ 2 * D ^ 2 +
        alpha * D * ‖delta G x‖ := by
        dsimp [d]
        ring


-- From Staging/affine_lmo_smooth_descent_true_gradient.lean

open scoped InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: affine_lmo_smooth_descent_true_gradient
--   (orig was: affine_lmo_smooth_descent_true_gradient; "LMO" is the standard
--   linear-minimization-oracle abbreviation in conditional-gradient analysis).
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses real
--      inner products, the norm of an affine update displacement, scalar
--      multiplication, and ordered real algebra, with no finite-dimensionality,
--      completeness, compactness, or measurability.
--   measure: none; this is deterministic pointwise one-step descent algebra.
--   convexity: none; convex feasibility and smoothness are reduced to the
--      pointwise affine update, diameter, and quadratic upper-bound hypotheses.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, preserving the true-gradient
--      smooth descent term before Wolfe-gap perturbation cancellation.
--   2. finite-sum and variance-reduced Frank-Wolfe, deriving one-step descent
--      from a smooth quadratic upper bound without prematurely absorbing the
--      estimator residual.
-- G0.4 search trace:
--   queries: ["smooth descent lmo", "inner affine update norm square"]
--   top hits: ["conditional_gradient_smooth_descent_premise_of_estimator",
--     "conditional_gradient_wolfe_gap_one_step_descent_of_smooth",
--     "wolfe_gap_descent_source_form_of_smooth_descent",
--     "stochastic_one_step_smooth_descent_gradf_premise",
--     "conditional_gradient_update_diff_sq_le_alpha_sq_diameter_sq",
--     "Convex.carrier_smooth_quadratic_upper_bound"]
--   coverage: partial — existing public hits either Young-absorb estimator
--     error, start after a descent premise is already supplied, or only bound
--     the affine update displacement; the target-file hit is paper-local and
--     private.
-- G0.4 not-a-thin-wrapper rationale: combines a pointwise smooth quadratic
--   upper bound, the affine LMO step identity, inner-product scalar rewriting,
--   and the affine-update diameter square bound into the reusable true-gradient
--   conditional-gradient descent premise.
-- G0.5 structural-content rationale: theorem only; it introduces no wrapper
--   def or structure and exposes a named one-step descent invariant.
-- G0.5c thin-wrapper self-detect: clean — body has smoothness substitution,
--   inner-product update algebra, use of the reusable displacement-square
--   estimate, and coefficient monotonicity, not a direct single-lemma alias.
-- G0.5d minimal-hypothesis check: all already minimal; global smoothness,
--   convexity, LMO feasibility, and set-diameter assumptions are pointwise
--   hypotheses at the single step used.

/-- A smooth quadratic bound plus an affine LMO update gives true-gradient
conditional-gradient descent.

If `xnext - x = a • (lmo G - x)`, the objective has the usual smooth quadratic
upper bound from `x` to `xnext`, and the selected LMO displacement is bounded
by `D`, then the smoothness term can be written using the true gradient at `x`
and the quadratic term is controlled by `(L / 2) * a^2 * D^2`.

Layer: Layer1 | Gap: Level 1 (conditional-gradient true-gradient smooth descent)
Proof: rewrite the linear smoothness term with the affine update identity, use
  the conditional-gradient displacement-square diameter estimate, and multiply
  it by the nonnegative smoothness coefficient.
Source: Frank-Wolfe conditional-gradient smooth descent algebra, real
  Hilbert-space inner-product scalar identities, and Mathlib normed-space
  scalar norm APIs
Used in: stochastic and finite-sum nonconvex conditional-gradient true-gradient
  one-step descent before Wolfe-gap residual cancellation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem affine_lmo_smooth_descent_true_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad lmo : E → E) (x G xnext : E) (a L D : ℝ)
    (ha_nonneg : 0 ≤ a)
    (hL_nonneg : 0 ≤ L)
    (hstep : xnext - x = a • (lmo G - x))
    (hquad :
      f xnext ≤ f x + ⟪grad x, xnext - x⟫_ℝ + (L / 2) * ‖xnext - x‖ ^ 2)
    (hdiam : ‖lmo G - x‖ ≤ D) :
    f xnext ≤
      f x + a * ⟪grad x, lmo G - x⟫_ℝ + (L / 2) * a ^ 2 * D ^ 2 := by
  let y : E := lmo G
  have hinner_update :
      ⟪grad x, xnext - x⟫_ℝ = a * ⟪grad x, y - x⟫_ℝ := by
    simpa [y, inner_smul_right] using
      congrArg (fun z : E => ⟪grad x, z⟫_ℝ) hstep
  have hnorm_sq :
      ‖xnext - x‖ ^ 2 ≤ a ^ 2 * D ^ 2 := by
    exact conditional_gradient_update_diff_sq_le_alpha_sq_diameter_sq
      x xnext y a D ha_nonneg (by simpa [y] using hstep) (by simpa [y] using hdiam)
  have hqbound :
      (L / 2) * ‖xnext - x‖ ^ 2 ≤ (L / 2) * (a ^ 2 * D ^ 2) := by
    have hLhalf_nonneg : 0 ≤ L / 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hnorm_sq hLhalf_nonneg
  calc
    f xnext
        ≤ f x + ⟪grad x, xnext - x⟫_ℝ + (L / 2) * ‖xnext - x‖ ^ 2 := hquad
    _ = f x + a * ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖xnext - x‖ ^ 2 := by
        rw [hinner_update]
    _ ≤ f x + a * ⟪grad x, y - x⟫_ℝ + (L / 2) * (a ^ 2 * D ^ 2) := by
        linarith
    _ = f x + a * ⟪grad x, lmo G - x⟫_ℝ + (L / 2) * a ^ 2 * D ^ 2 := by
        dsimp [y]
        ring

/-- Centered square-integrability is preserved by a two-stage affine combination.

If `x` and `xBar` have integrable squared distance from a fixed center `c`,
then the point obtained by first forming `(1 - q) • xBar + q • x` and then
forming the affine blend `a • · + b • x` also has integrable squared distance
from `c`.

Layer: Glue | Gap: Level 1 (centered L2 transport through nested affine updates)
Proof: convert centered squared-norm integrability to `MemLp` at exponent two,
  rewrite each centered affine blend as the corresponding affine blend of
  centered displacements, close `MemLp` under addition and scalar
  multiplication, and convert back by `memLp_two_iff_integrable_sq_norm`.
Source: Mathlib Lp-space closure, Bochner measurability, and norm-square
  integrability APIs
Used in: stochastic accelerated gradient descent auxiliary-point multiplier
  square-integrability; stochastic mirror descent momentum-point L2 transport
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_sq_norm_const_sub_two_stage_affine
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω}
    (c : E) (x xBar : Ω → E) (q a b : ℝ)
    (hx_meas : AEStronglyMeasurable x μ)
    (hxBar_meas : AEStronglyMeasurable xBar μ)
    (hx_sq : Integrable (fun ω => ‖c - x ω‖ ^ 2) μ)
    (hxBar_sq : Integrable (fun ω => ‖c - xBar ω‖ ^ 2) μ)
    (hab : a + b = 1) :
    Integrable
      (fun ω => ‖c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω)‖ ^ 2)
      μ := by
  have hx_disp_meas : AEStronglyMeasurable (fun ω => c - x ω) μ :=
    (aestronglyMeasurable_const.sub hx_meas)
  have hxBar_disp_meas : AEStronglyMeasurable (fun ω => c - xBar ω) μ :=
    (aestronglyMeasurable_const.sub hxBar_meas)
  have hx_disp_l2 : MemLp (fun ω => c - x ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hx_disp_meas).2 hx_sq
  have hxBar_disp_l2 : MemLp (fun ω => c - xBar ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hxBar_disp_meas).2 hxBar_sq
  have hfirst_raw :
      MemLp (fun ω => (1 - q) • (c - xBar ω) + q • (c - x ω)) 2 μ :=
    (hxBar_disp_l2.const_smul (1 - q)).add (hx_disp_l2.const_smul q)
  have hfirst_l2 :
      MemLp (fun ω => c - ((1 - q) • xBar ω + q • x ω)) 2 μ := by
    refine MemLp.ae_eq ?_ hfirst_raw
    refine Filter.Eventually.of_forall ?_
    intro ω
    change (1 - q) • (c - xBar ω) + q • (c - x ω) =
      c - ((1 - q) • xBar ω + q • x ω)
    module
  have hsecond_raw :
      MemLp
        (fun ω =>
          a • (c - ((1 - q) • xBar ω + q • x ω)) + b • (c - x ω))
        2 μ :=
    (hfirst_l2.const_smul a).add (hx_disp_l2.const_smul b)
  have htarget_l2 :
      MemLp
        (fun ω => c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω))
        2 μ := by
    refine MemLp.ae_eq ?_ hsecond_raw
    refine Filter.Eventually.of_forall ?_
    intro ω
    change a • (c - ((1 - q) • xBar ω + q • x ω)) + b • (c - x ω) =
      c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω)
    have hb : b = 1 - a := by linarith
    rw [hb]
    module
  exact
    (memLp_two_iff_integrable_sq_norm htarget_l2.aestronglyMeasurable).1
      htarget_l2

/-- Centered square-integrability is preserved by a named affine update.

If two random vectors have integrable squared distance from a fixed center and
`xUpdate` agrees a.e. with `(1 - alpha) • xPrev + alpha • xNext`, then
`xUpdate` also has integrable squared distance from the center.

Layer: Glue | Gap: Level 1 (centered L2 transport through affine updates)
Proof: convert centered squared-norm integrability to `MemLp` at exponent two,
  close `MemLp` under deterministic scalar multiplication and addition,
  transport along the a.e. affine-update identity, and convert back by
  `memLp_two_iff_integrable_sq_norm`.
Source: Mathlib Lp-space closure, Bochner measurability, and norm-square
  integrability APIs
Used in: stochastic accelerated gradient descent accelerated-average
  square-integrability; stochastic mirror descent momentum iterate L2 transport
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_sq_norm_const_sub_affine_update
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω}
    (c : E) (xPrev xNext xUpdate : Ω → E) (alpha : ℝ)
    (hxPrev_meas : AEStronglyMeasurable xPrev μ)
    (hxNext_meas : AEStronglyMeasurable xNext μ)
    (hxPrev_sq : Integrable (fun ω => ‖c - xPrev ω‖ ^ 2) μ)
    (hxNext_sq : Integrable (fun ω => ‖c - xNext ω‖ ^ 2) μ)
    (h_update :
      xUpdate =ᵐ[μ] fun ω => (1 - alpha) • xPrev ω + alpha • xNext ω) :
    Integrable (fun ω => ‖c - xUpdate ω‖ ^ 2) μ := by
  have hxPrev_disp_meas : AEStronglyMeasurable (fun ω => c - xPrev ω) μ :=
    (aestronglyMeasurable_const.sub hxPrev_meas)
  have hxNext_disp_meas : AEStronglyMeasurable (fun ω => c - xNext ω) μ :=
    (aestronglyMeasurable_const.sub hxNext_meas)
  have hxPrev_l2 : MemLp (fun ω => c - xPrev ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hxPrev_disp_meas).2 hxPrev_sq
  have hxNext_l2 : MemLp (fun ω => c - xNext ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hxNext_disp_meas).2 hxNext_sq
  have hcombo_l2 :
      MemLp
        (fun ω => (1 - alpha) • (c - xPrev ω) + alpha • (c - xNext ω))
        2 μ :=
    (hxPrev_l2.const_smul (1 - alpha)).add (hxNext_l2.const_smul alpha)
  have htarget_l2 : MemLp (fun ω => c - xUpdate ω) 2 μ := by
    refine MemLp.ae_eq ?_ hcombo_l2
    filter_upwards [h_update] with ω hω
    rw [hω]
    module
  exact
    (memLp_two_iff_integrable_sq_norm htarget_l2.aestronglyMeasurable).1
      htarget_l2

/-- Raw search-point formula for an accelerated auxiliary point at successor paper time.

If an auxiliary point is represented by `SOptLib.acceleratedAuxiliaryPoint`
and the generated query at positive time `τ` is the search point of the
predecessor process state, then the displayed raw quotient using the search
point and predecessor coordinate is equal to that auxiliary point.

Layer: Layer1 | Gap: Level 1 (accelerated auxiliary-point raw formula transport)
Proof: normalize the `natSuccPositiveTime` predecessor index, rewrite the raw
  search point to the named query, and unfold `acceleratedAuxiliaryPoint`.
Source: accelerated stochastic approximation iterate notation plus Mathlib
  subtype-index and natural-number predecessor APIs
Used in: stochastic accelerated gradient descent generated auxiliary plus-point
  rewriting before Bregman recurrence transport
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_auxiliary_point_raw_at_nat_succ_positive_time
    {Ω State E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (process : ℕ → Ω → State)
    (stateX : State → E)
    (searchPoint : {n : ℕ // 1 ≤ n} → State → E)
    (xUnder xPlus : {n : ℕ // 1 ≤ n} → Ω → E)
    (mu : ℝ) (gamma : ℕ → ℝ)
    (h_xUnder :
      ∀ τ ω, searchPoint τ (process (τ.1 - 1) ω) = xUnder τ ω)
    (h_xPlus :
      ∀ τ ω, xPlus τ ω =
        SOptLib.acceleratedAuxiliaryPoint mu gamma xUnder
          (fun n ω => stateX (process n ω)) τ ω)
    (ω : Ω) (t : ℕ) :
    let k : ℕ := t - 1
    let τ : {m : ℕ // 1 ≤ m} := SOptLib.natSuccPositiveTime k
    let prev : State := process k ω
    (mu * gamma τ.1 / (1 + mu * gamma τ.1)) • searchPoint τ prev +
      (1 / (1 + mu * gamma τ.1)) • stateX prev =
        xPlus τ ω := by
  classical
  let k : ℕ := t - 1
  let τ : {m : ℕ // 1 ≤ m} := SOptLib.natSuccPositiveTime k
  let prev : State := process k ω
  have hτpred : τ.1 - 1 = k := by
    simp [τ, SOptLib.natSuccPositiveTime]
  have hτval : τ.1 = k + 1 := by
    simp [τ, SOptLib.natSuccPositiveTime]
  have hxunder : searchPoint τ prev = xUnder τ ω := by
    simpa [prev, hτpred] using h_xUnder τ ω
  dsimp only
  rw [hxunder, h_xPlus τ ω]
  simp [SOptLib.acceleratedAuxiliaryPoint_def, hτval, k]

/-- Centered square-integrability transfers through two named affine updates.

If `x` and `xBar` have integrable squared distance from a fixed center, `xUnder`
agrees a.e. with the affine search blend `(1 - q) • xBar + q • x`, and `xPlus`
agrees a.e. with `a • xUnder + b • x`, then `xPlus` has integrable squared
distance from the same center.

Layer: Glue | Gap: Level 1 (named two-stage centered L2 affine transport)
Proof: apply the raw two-stage affine L2 theorem to the unfolded formula, then
  compose the two a.e. update laws and transport integrability to the named
  output.
Source: Mathlib Lp-space closure, Bochner integrability congruence, and
  norm-square integrability APIs
Used in: stochastic accelerated gradient descent auxiliary-point multiplier
  square-integrability; stochastic mirror descent momentum-point L2 transport
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_sq_norm_const_sub_two_stage_affine_of_previous_l2
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω}
    (c : E) (x xBar xUnder xPlus : Ω → E) (q a b : ℝ)
    (hx_meas : AEStronglyMeasurable x μ)
    (hxBar_meas : AEStronglyMeasurable xBar μ)
    (hx_sq : Integrable (fun ω => ‖c - x ω‖ ^ 2) μ)
    (hxBar_sq : Integrable (fun ω => ‖c - xBar ω‖ ^ 2) μ)
    (hab : a + b = 1)
    (h_under : xUnder =ᵐ[μ] fun ω => (1 - q) • xBar ω + q • x ω)
    (h_plus : xPlus =ᵐ[μ] fun ω => a • xUnder ω + b • x ω) :
    Integrable (fun ω => ‖c - xPlus ω‖ ^ 2) μ := by
  have hraw :
      Integrable
        (fun ω =>
          ‖c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω)‖ ^ 2)
        μ :=
    integrable_sq_norm_const_sub_two_stage_affine (μ := μ)
      c x xBar q a b hx_meas hxBar_meas hx_sq hxBar_sq hab
  have htarget_eq :
      (fun ω => ‖c - xPlus ω‖ ^ 2) =ᵐ[μ]
        (fun ω =>
          ‖c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω)‖ ^ 2) := by
    filter_upwards [h_plus, h_under] with ω hplus hunder
    rw [hplus, hunder]
  exact hraw.congr htarget_eq.symm

/-- A pathwise accelerated composite one-step recursion from local model facts.

If the averaged objective satisfies an upper-model inequality, the local model
is controlled by a lower model plus Bregman and residual terms, the weighted
Bregman budget absorbs the prox displacement, and the residual term admits the
standard completion-square bound, then the accelerated one-step recursion
follows with the named stochastic-error term.

Layer: Layer1 | Gap: Level 1 (accelerated composite one-step recursion)
Proof: normalize the smoothness displacement, split the residual inner product
  through the auxiliary point, absorb the Bregman tail by the completed square,
  and invoke the scalar prox/Bregman recurrence assembly.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra and
  Mathlib real Hilbert-space ordered-field arithmetic APIs
Used in: stochastic accelerated gradient descent pathwise one-step recursion
  before finite-window Bregman telescoping
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_composite_one_step_recursion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Psi lowerModel : E → ℝ) (V : E → E → ℝ)
    (alpha gamma mu L M : ℝ)
    (localModel : ℝ)
    (xBarPrev xPrev xUnder xNext xBar xPlus xRef delta : E)
    (halpha_nonneg : 0 ≤ alpha)
    (hgamma_pos : 0 < gamma)
    (hUpper :
      Psi xBar ≤
        (1 - alpha) * Psi xBarPrev +
          alpha * localModel +
          L / 2 * ‖alpha • (xNext - xPlus)‖ ^ 2 +
          M * ‖alpha • (xNext - xPlus)‖)
    (hProxModel :
      localModel ≤
        lowerModel xRef +
          (1 / gamma) *
            (V xPrev xRef - (1 + mu * gamma) * V xNext xRef) -
          ((1 / gamma) * V xPrev xNext + mu * V xUnder xNext) +
          ⟪delta, xRef - xNext⟫_ℝ)
    (hBregLower :
      ((1 + mu * gamma) / (2 * gamma)) * ‖xNext - xPlus‖ ^ 2 ≤
        (1 / gamma) * V xPrev xNext + mu * V xUnder xNext)
    (hCompletionSquare :
      alpha * (M * ‖xNext - xPlus‖ - ⟪delta, xNext - xPlus⟫_ℝ -
        (1 + mu * gamma - L * alpha * gamma) / (2 * gamma) *
          ‖xNext - xPlus‖ ^ 2) ≤
        alpha * gamma * (M + ‖delta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma))) :
    Psi xBar ≤
      (1 - alpha) * Psi xBarPrev +
        alpha * lowerModel xRef +
        (alpha / gamma) *
          (V xPrev xRef - (1 + mu * gamma) * V xNext xRef) +
        SOptLib.acceleratedStochasticError
          (fun _ : Unit => ()) (fun _ : Unit => alpha) (fun _ : Unit => gamma)
          M mu L (fun z : E => ‖z‖)
          (fun _ : Unit => fun _ : Unit => delta)
          (fun _ : Unit => fun _ : Unit => xPlus) () () xRef := by
  let d : E := xNext - xPlus
  let breg : ℝ := (1 / gamma) * V xPrev xNext + mu * V xUnder xNext
  let vpart : ℝ :=
    (1 / gamma) * (V xPrev xRef - (1 + mu * gamma) * V xNext xRef)
  let noise : ℝ := ⟪delta, xRef - xNext⟫_ℝ
  let stochasticError : ℝ :=
    SOptLib.acceleratedStochasticError
      (fun _ : Unit => ()) (fun _ : Unit => alpha) (fun _ : Unit => gamma)
      M mu L (fun z : E => ‖z‖)
      (fun _ : Unit => fun _ : Unit => delta)
      (fun _ : Unit => fun _ : Unit => xPlus) () () xRef
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hnorm_smul : ‖alpha • d‖ = alpha * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg halpha_nonneg]
  have hBregScaled :
      alpha * (((1 + mu * gamma) / (2 * gamma)) * ‖d‖ ^ 2) ≤
        alpha * breg := by
    exact mul_le_mul_of_nonneg_left (by simpa [breg, d] using hBregLower) halpha_nonneg
  have hBregScaled' :
      alpha *
          ((((1 + mu * gamma - L * alpha * gamma) + L * alpha * gamma) /
              (2 * gamma)) * ‖d‖ ^ 2) ≤
        alpha * breg := by
    convert hBregScaled using 1
    · field_simp [hgamma_ne]
      ring
  have htail_core :
      L / 2 * (alpha * ‖d‖) ^ 2 + M * (alpha * ‖d‖) - alpha * breg +
          (alpha * ⟪delta, xRef - xPlus⟫_ℝ - alpha * ⟪delta, d⟫_ℝ) ≤
        alpha * gamma * (M + ‖delta‖) ^ 2 /
            (2 * (1 + mu * gamma - L * alpha * gamma)) +
          alpha * ⟪delta, xRef - xPlus⟫_ℝ := by
    exact
      smooth_quadratic_tail_absorption_of_bregman_and_completion_square
        (E := E) (a := alpha) (L := L) (M := M) (gamma := gamma)
        (D := 1 + mu * gamma - L * alpha * gamma)
        (breg := breg) (tailNoise := ⟪delta, xRef - xPlus⟫_ℝ)
        (δ := delta) (d := d) hgamma_pos hBregScaled'
        (by simpa [d] using hCompletionSquare)
  have hnoise_split :
      alpha * noise =
        alpha * ⟪delta, xRef - xPlus⟫_ℝ - alpha * ⟪delta, d⟫_ℝ := by
    have hxsplit : xRef - xNext = (xRef - xPlus) - d := by
      simp [d]
    dsimp [noise]
    rw [hxsplit, inner_sub_right]
    ring
  have hTail :
      L / 2 * ‖alpha • d‖ ^ 2 + M * ‖alpha • d‖ -
          alpha * breg + alpha * noise ≤
        stochasticError := by
    unfold stochasticError SOptLib.acceleratedStochasticError
    rw [hnorm_smul, hnoise_split]
    simpa [d] using htail_core
  have hUpperAbbrev :
      Psi xBar ≤
        (1 - alpha) * Psi xBarPrev + alpha * localModel +
          (L / 2 * ‖alpha • d‖ ^ 2 + M * ‖alpha • d‖) := by
    simpa [d, add_assoc] using hUpper
  have hModelScaled :
      alpha * localModel ≤ alpha * (lowerModel xRef + vpart - breg + noise) := by
    exact mul_le_mul_of_nonneg_left (by simpa [vpart, breg, noise] using hProxModel)
      halpha_nonneg
  have hCombined :
      Psi xBar ≤
        (1 - alpha) * Psi xBarPrev + alpha * lowerModel xRef +
          alpha * vpart + stochasticError :=
    accelerated_delta_tail_bound_of_prox_and_bregman
      (value := Psi xBar)
      (base := (1 - alpha) * Psi xBarPrev)
      (alpha := alpha)
      (model := localModel)
      (smooth := L / 2 * ‖alpha • d‖ ^ 2 + M * ‖alpha • d‖)
      (lowerModel := lowerModel xRef)
      (vpart := vpart)
      (breg := breg)
      (noise := noise)
      (stochasticError := stochasticError)
      hUpperAbbrev hModelScaled hTail
  calc
    Psi xBar ≤
        (1 - alpha) * Psi xBarPrev + alpha * lowerModel xRef +
          alpha * vpart + stochasticError := hCombined
    _ = (1 - alpha) * Psi xBarPrev +
        alpha * lowerModel xRef +
        (alpha / gamma) *
          (V xPrev xRef - (1 + mu * gamma) * V xNext xRef) +
        SOptLib.acceleratedStochasticError
          (fun _ : Unit => ()) (fun _ : Unit => alpha) (fun _ : Unit => gamma)
          M mu L (fun z : E => ‖z‖)
          (fun _ : Unit => fun _ : Unit => delta)
          (fun _ : Unit => fun _ : Unit => xPlus) () () xRef := by
        simp [vpart, stochasticError]
        ring

/-- A generated execution inherits an expected bound from an internal run contract.

If a conditional theorem proves well-definedness and a scalar expected-gap bound
for a run contract, the contract well-definedness fact transfers to the
generated public gap, and the contract value/budget presentations agree with the
generated public presentations at the requested output time, then the generated
execution has the same well-definedness and bound.

Layer: Layer1 | Gap: Level 1 (generated-to-contract expected-bound bridge)
Proof: split the contract theorem's paired conclusion, transfer the contract
  gap well-definedness fact, and rewrite the scalar expected gap and budget to
  their generated presentations.
Source: Mathlib equality rewriting for ordered real propositions and SOptLib
  expectation well-definedness predicates
Used in: stochastic accelerated gradient descent generated execution theorem
  after generated data constructs the internal run contract
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem generated_execution_bound_of_run_contract_bridge
    {Ω RunContract PositiveTime : Type*}
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (run : RunContract)
    (conditionalGap : RunContract → ℕ → Ω → ℝ)
    (generatedGap : ℕ → Ω → ℝ)
    (conditionalExpectedGap : RunContract → ℕ → ℝ)
    (generatedExpectedGap : ℕ → ℝ)
    (conditionalBudget : RunContract → PositiveTime → ℝ)
    (generatedBudget : PositiveTime → ℝ)
    (k : ℕ) (t : PositiveTime)
    (hcontract :
      SOptLib.expectationWellDefined μ (conditionalGap run k) ∧
        conditionalExpectedGap run k ≤ conditionalBudget run t)
    (hgap_wellDefined :
      SOptLib.expectationWellDefined μ (conditionalGap run k) →
        SOptLib.expectationWellDefined μ (generatedGap k))
    (hexpected_eq :
      conditionalExpectedGap run k = generatedExpectedGap k)
    (hbudget_eq :
      conditionalBudget run t = generatedBudget t) :
    SOptLib.expectationWellDefined μ (generatedGap k) ∧
      generatedExpectedGap k ≤ generatedBudget t := by
  refine ⟨?_, ?_⟩
  · exact hgap_wellDefined hcontract.1
  · simpa [hexpected_eq, hbudget_eq] using hcontract.2

/-- A generated expected objective-gap bound follows from carrier-objective
measurability and auxiliary-point L2 regularity.

If the carrier objective is measurable, every generated output carrier is
measurable, and the positive-time auxiliary points have the required squared
distance integrability, then any theorem closed under those two regularity
inputs yields the generated expected objective-gap bound.

Layer: Layer1 | Gap: Level 1 (carrier-measurable generated-bound regularity adapter)
Proof: compose carrier-objective measurability with each output-carrier map,
  convert the resulting objective-value measurability to objective-gap
  measurability, and invoke the supplied regularity-closed expected-bound
  theorem with the L2 side condition.
Source: Mathlib measure theory strongly measurable composition APIs and
  stochastic-optimization objective-gap expectation bounds
Used in: stochastic accelerated gradient descent generated execution theorem
  from carrier-restricted objective measurability and auxiliary-point L2 control
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem generated_bound_of_carrier_objective_measurable
    {Ω E X PositiveTime : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure Ω)
    (carrierObjective : X → ℝ) (optimumValue : ℝ)
    (outputCarrier : ℕ → Ω → X)
    (xPlus : PositiveTime → Ω → E) (xRef : E)
    (expectedGap : ℕ → ℝ) (budget : PositiveTime → ℝ)
    (k : ℕ) (t : PositiveTime)
    (hcarrier_meas : Measurable carrierObjective)
    (houtput_meas : ∀ n : ℕ, Measurable (outputCarrier n))
    (hxPlus_l2 :
      ∀ t : PositiveTime,
        Integrable (fun ω => ‖xRef - xPlus t ω‖ ^ 2) μ)
    (hbound_of_regularity :
      (∀ n : ℕ,
        AEStronglyMeasurable
          (SOptLib.objectiveGapIntegrand carrierObjective optimumValue
            outputCarrier n) μ) →
      (∀ t : PositiveTime,
        Integrable (fun ω => ‖xRef - xPlus t ω‖ ^ 2) μ) →
      SOptLib.expectationWellDefined μ
          (SOptLib.objectiveGapIntegrand carrierObjective optimumValue
            outputCarrier k) ∧
        expectedGap k ≤ budget t) :
    SOptLib.expectationWellDefined μ
        (SOptLib.objectiveGapIntegrand carrierObjective optimumValue
          outputCarrier k) ∧
      expectedGap k ≤ budget t := by
  refine hbound_of_regularity ?_ hxPlus_l2
  intro n
  exact SOptLib.objectiveGap_aestronglyMeasurable μ carrierObjective
    optimumValue outputCarrier n
    ((hcarrier_meas.comp (houtput_meas n)).aestronglyMeasurable)

-- Generalization plan (G0):
-- G0.1 naming: weighted_center_mem_and_sq_distance_bound
-- G0.2 typeclass level used:
--   E: [SeminormedAddCommGroup E] [NormedSpace ℝ E]; the proof uses only real
--      vector-space convex combinations, norm homogeneity, and squared-norm
--      order algebra. No inner product or finite-dimensional structure is used.
--   measure: none; this is deterministic feasible-set geometry.
--   convexity: explicit Convex ℝ X hypothesis; no function convexity is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated gradient descent weighted auxiliary-center state control
--   2. randomized accelerated proximal-point two-center estimate-sequence updates
-- G0.4 search trace:
--   queries: ["weighted center convex squared distance",
--     "convex combination norm square bound"]
--   top hits: ["two_center_bregman_absorbs_weighted_center_sq",
--     "weighted_sq_norm_sub_center_le", "Convex.normalized_weighted_sum_mem",
--     "blockBregmanDivergence_lower_bound_of_strongConvexOnWithNorm"]
--   coverage: partial — weighted_sq_norm_sub_center_le gives the norm-square
--     half of the argument, and Convex.normalized_weighted_sum_mem gives a
--     finite-sum membership pattern, but no hit packages the two-point weighted
--     center feasibility together with the uniform state squared-distance bound.
-- G0.4 not-a-thin-wrapper rationale: the theorem combines a convex-set
--   feasibility invariant with the two-endpoint state radius envelope consumed
--   by accelerated proximal state proofs.
-- G0.5 structural-content rationale: this is a theorem with no new structure
--   or def wrapper; its content is the combined membership-and-distance
--   invariant for a normalized two-point weighted center.
-- G0.5c thin-wrapper self-detect: clean — body uses convexity, the staged
--   weighted square estimate, denominator positivity, and order algebra rather
--   than a direct alias of one lemma.
-- G0.5d minimal-hypothesis check: all hypotheses are pointwise; global
--   convexity of X is exactly what supplies weighted-center membership.

/-- A normalized two-point weighted center stays feasible and has bounded
squared distance to any reference point.

If `xPrev` and `xUnder` lie in a convex feasible set and `xPlus` is their
normalized center with weights `1` and `mu * gamma`, then `xPlus` is feasible
and its squared distance to `xStar` is controlled by twice the sum of the two
endpoint squared distances.

Layer: Layer1 | Gap: Level 1 (two-point weighted-center feasible state bound)
Proof: prove feasibility by the two-point convexity rule, then apply the
  weighted center squared-norm inequality and relax the weighted average to the
  two-endpoint state envelope by ordered-field arithmetic.
Source: Mathlib convex-set APIs and normed real vector-space squared-distance
  algebra
Used in: stochastic accelerated gradient descent weighted auxiliary-center
  feasibility and state-radius control before prox residual removal
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem weighted_center_mem_and_sq_distance_bound
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} {xStar xPrev xUnder xPlus : E} {mu gamma : ℝ}
    (hX : Convex ℝ X)
    (hmu_nonneg : 0 ≤ mu)
    (hgamma_pos : 0 < gamma)
    (hxPrev : xPrev ∈ X)
    (hxUnder : xUnder ∈ X)
    (hxplus :
      xPlus =
        (mu * gamma / (1 + mu * gamma)) • xUnder +
          (1 / (1 + mu * gamma)) • xPrev) :
    xPlus ∈ X ∧
      ‖xStar - xPlus‖ ^ 2 ≤
        2 * (‖xStar - xPrev‖ ^ 2 + ‖xStar - xUnder‖ ^ 2) := by
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have hr_nonneg : 0 ≤ mu * gamma := mul_nonneg hmu_nonneg hgamma_nonneg
  have hden_pos : 0 < 1 + mu * gamma := by linarith
  have hden_ne : 1 + mu * gamma ≠ 0 := ne_of_gt hden_pos
  let a : ℝ := mu * gamma / (1 + mu * gamma)
  let b : ℝ := 1 / (1 + mu * gamma)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hab_sum : a + b = 1 := by
    dsimp [a, b]
    field_simp [hden_ne]
    ring
  have hxPlus_mem : xPlus ∈ X := by
    rw [hxplus]
    simpa [a, b] using hX hxUnder hxPrev ha_nonneg hb_nonneg hab_sum
  have hweighted :
      ((1 + mu * gamma) / 2) *
          ‖xStar - ((mu * gamma / (1 + mu * gamma)) • xUnder +
            (1 / (1 + mu * gamma)) • xPrev)‖ ^ 2 ≤
        (1 / 2) * ‖xPrev - xStar‖ ^ 2 +
          (mu * gamma / 2) * ‖xUnder - xStar‖ ^ 2 :=
    weighted_sq_norm_sub_center_le (E := E) (u := xUnder) (v := xPrev)
      (y := xStar) (r := mu * gamma) hr_nonneg
  have hsquare :
      ‖xStar - xPlus‖ ^ 2 ≤
        2 * (‖xStar - xPrev‖ ^ 2 + ‖xStar - xUnder‖ ^ 2) := by
    rw [hxplus]
    have hweighted' :
        ((1 + mu * gamma) / 2) *
            ‖xStar - ((mu * gamma / (1 + mu * gamma)) • xUnder +
              (1 / (1 + mu * gamma)) • xPrev)‖ ^ 2 ≤
          (1 / 2) * ‖xStar - xPrev‖ ^ 2 +
            (mu * gamma / 2) * ‖xStar - xUnder‖ ^ 2 := by
      simpa [norm_sub_rev] using hweighted
    have hprev_nonneg : 0 ≤ ‖xPrev - xStar‖ ^ 2 := sq_nonneg _
    have hunder_nonneg : 0 ≤ ‖xUnder - xStar‖ ^ 2 := sq_nonneg _
    have hdist_nonneg :
        0 ≤ ‖xStar - ((mu * gamma / (1 + mu * gamma)) • xUnder +
          (1 / (1 + mu * gamma)) • xPrev)‖ ^ 2 := sq_nonneg _
    nlinarith [hweighted', hprev_nonneg, hunder_nonneg, hdist_nonneg, hr_nonneg]
  exact ⟨hxPlus_mem, by simpa [norm_sub_rev] using hsquare⟩

-- Generalization plan (G0):
-- G0.1 naming: sq_norm_endpoint_le_of_two_center_prox_step
--   (orig was: generated_acsa_prop42_context_of_kernel_step); the new name
--   removes generated/AC-SA/Proposition-number markers and describes the
--   mathematical endpoint squared-norm bound supplied by a two-center prox step.
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses norm,
--      subtraction, scalar multiplication, real inner products, convex segment
--      calculus through `ConvexOn`, and ordered real arithmetic, with no
--      completeness, measurability, probability, or finite-dimensional facts.
--   measure: none; this is a deterministic pathwise one-step prox assembly.
--   convexity: Mathlib `ConvexOn ℝ X p` for the nonsmooth prox term; smoothness,
--      model, and optimality facts are pointwise one-step hypotheses.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated gradient descent, generated-kernel prox step
--      before the endpoint boundary and finite-window Bregman telescope.
--   2. variance-reduced accelerated proximal-gradient descent, two-center prox
--      step after isolating a stochastic residual from the gradient estimate.
-- G0.4 search trace:
--   queries: ["two center prox context",
--     "prox step convex upper model bregman",
--     "source budget bregman live weighted absorb delta completion"]
--   top hits: ["sq_norm_endpoint_le_of_two_center_prox_context",
--     "two_bregman_argmin_descent",
--     "prox_three_point_of_isMinOn_linear_bregman",
--     "prox_gamma_step_bound_of_three_point_and_dual_support",
--     "alpha_scaled_bregman_tail_absorption_of_weighted_bound"]
--   coverage: partial — existing hits cover the already-normalized endpoint
--     context, the abstract two-Bregman argmin descent, or the tail absorption
--     substep, but none packages the raw prox-step upper model and argmin
--     context into the endpoint bound.
-- G0.4 not-a-thin-wrapper rationale: this theorem adds the reusable invariant
--   that raw upper-model data and a convex two-center prox argmin certificate
--   assemble into the normalized endpoint context consumed by accelerated
--   stochastic/proximal recurrences.
-- G0.5 structural-content rationale: theorem, not a def or structure; the
--   statement exposes a complete one-step algorithm-frame handoff while keeping
--   all setup-record, time-index, and kernel implementation details abstract.
-- G0.5b name-body alignment: the name promises a squared-norm endpoint
--   inequality from a two-center prox step, and the theorem proves exactly that
--   by deriving the prox-step context and applying the endpoint boundary.
-- G0.5c thin-wrapper self-detect: clean — body derives the normalized upper
--   model, invokes the two-Bregman argmin theorem, transports the prox objective
--   formula, and only then applies the endpoint context theorem.
-- G0.5d minimal-hypothesis check: all hypotheses are pointwise one-step facts;
--   no global smoothness, measurability, probability, or minimizer structure is
--   retained beyond the `ConvexOn` property needed on the prox segment.

/-- A two-center prox step gives the accelerated squared-norm endpoint bound.

This is the deterministic assembly layer above the normalized endpoint theorem:
the raw upper model is rewritten through the accelerated average identity, the
convex two-center prox minimizer gives the Bregman descent inequality, and the
existing endpoint context theorem supplies the final squared-distance boundary.

Layer: Layer1 | Gap: Level 1 (two-center prox-step endpoint assembly)
Proof: normalize the upper model with `xBar - xUnder = alpha • (z - xPlus)`,
  derive the two-center Bregman descent inequality from the abstract argmin
  theorem, rewrite the prox term formula, and invoke the endpoint boundary.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra,
  Mathlib convex segment calculus, and real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent generated-kernel prox step
  before the endpoint boundary and finite-window Bregman telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem sq_norm_endpoint_le_of_two_center_prox_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (Psi f h : E → ℝ) (V : E → E → ℝ) (objGrad bregGrad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xRef xPlus xBar g eta : E)
    (p : E → ℝ)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_pos : 0 < alpha)
    (hgamma_pos : 0 < gamma)
    (hmu_nonneg : 0 ≤ mu)
    (hp_convex : ConvexOn ℝ X p)
    (hz_mem : z ∈ X)
    (hxRef_mem : xRef ∈ X)
    (hp_def : ∀ u, p u = gamma * (⟪g, u⟫_ℝ + h u))
    (hnoise_decomp : g = objGrad xUnder + eta)
    (hV_segment_deriv :
      ∀ (a z u : E), z ∈ X →
        let d : E := u - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z u t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪bregGrad z - bregGrad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0)
    (hV_three :
      ∀ a b c : E,
        V a c = V a b + ⟪bregGrad b - bregGrad a, c - b⟫_ℝ + V b c)
    (h_opt :
      ∀ u, u ∈ X →
        p z + (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
          p u + (gamma * mu) * V xUnder u + (1 : ℝ) * V prevCenter u)
    (havg_under : xBar - xUnder = alpha • (z - xPlus))
    (hUpper_raw :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪objGrad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * ‖xBar - xUnder‖ ^ 2 +
          M * ‖xBar - xUnder‖)
    (hweighted_absorb :
      ((1 + mu * gamma) / (2 * gamma)) * ‖z - xPlus‖ ^ 2 ≤
        (1 / gamma) * V prevCenter z + mu * V xUnder z)
    (hDeltaSquare :
      alpha *
          (M * ‖z - xPlus‖ - ⟪eta, z - xPlus⟫_ℝ -
            (1 + mu * gamma - L * alpha * gamma) /
              (2 * gamma) * ‖z - xPlus‖ ^ 2) ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)))
    (hPsi_ref_le_xBar : Psi xRef ≤ Psi xBar)
    (hmodel_le :
      f xUnder + ⟪objGrad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef ≤
        Psi xRef)
    (hVz_lower :
      (1 / 2 : ℝ) * ‖z - xRef‖ ^ 2 ≤ V z xRef) :
    alpha / (2 * gamma) * ‖z - xRef‖ ^ 2 ≤
      (1 - alpha) * (Psi prevBar - Psi xRef) +
        alpha / gamma * V prevCenter xRef +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  have hnorm_avg_under :
      ‖xBar - xUnder‖ = alpha * ‖z - xPlus‖ := by
    rw [havg_under, norm_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg halpha_nonneg]
  have hUpper :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪objGrad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) := by
    simpa [hnorm_avg_under] using hUpper_raw
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have htwo_bregman_raw :=
    two_bregman_argmin_descent
      X p V bregGrad hp_convex
      (uHat := z) (xTilde := xUnder) (yTilde := prevCenter)
      (mu1 := gamma * mu) (mu2 := (1 : ℝ))
      hz_mem (mul_nonneg hgamma_nonneg hmu_nonneg) (by norm_num)
      hV_segment_deriv hV_three h_opt xRef hxRef_mem
  have htwo_bregman :
      gamma * (⟪g, z⟫_ℝ + h z) +
          (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
        gamma * (⟪g, xRef⟫_ℝ + h xRef) +
          (gamma * mu) * V xUnder xRef +
          (1 : ℝ) * V prevCenter xRef -
            ((gamma * mu) + (1 : ℝ)) * V z xRef := by
    simpa [hp_def z, hp_def xRef] using htwo_bregman_raw
  exact
    sq_norm_endpoint_le_of_two_center_prox_context
      Psi f h V objGrad alpha gamma mu L M
      prevBar prevCenter xUnder z xRef xPlus xBar g eta
      halpha_nonneg halpha_pos hgamma_pos hmu_nonneg hnoise_decomp
      hUpper htwo_bregman hweighted_absorb hDeltaSquare
      hPsi_ref_le_xBar hmodel_le hVz_lower

-- Generalization plan (G0):
-- G0.1 naming: accelerated_composite_endpoint_recurrence_of_convex_two_center_prox_step
--   (orig was: generated_prop42_endpoint_recurrence_of_kernel_step); the new
--   name removes generated/Proposition-number markers and describes the
--   mathematical endpoint recurrence supplied by a convex two-center prox step.
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses norm,
--      subtraction, scalar multiplication, real inner products, convex segment
--      calculus through `ConvexOn`, and ordered real arithmetic, with no
--      completeness, measurability, probability, or finite-dimensional facts.
--   measure: none; this is a deterministic pathwise one-step prox recurrence.
--   convexity: Mathlib `Convex ℝ X` and `ConvexOn ℝ X h`; the theorem derives
--      convexity of the linear-plus-simple prox objective pointwise.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated gradient descent, generated-kernel prox step
--      before the endpoint boundary used by the finite-window regularity route.
--   2. variance-reduced accelerated proximal-gradient descent, two-center prox
--      step after splitting the variance-reduced residual from the full gradient.
-- G0.4 search trace:
--   queries: ["endpoint recurrence kernel step",
--     "convex composite two center prox endpoint"]
--   top hits: ["accelerated_composite_gap_recurrence_of_two_center_prox_step",
--     "sq_norm_endpoint_le_of_accelerated_bregman_recurrence",
--     "sq_norm_endpoint_le_of_two_center_prox_step",
--     "sq_norm_endpoint_le_of_two_center_prox_context",
--     "two_center_bregman_absorbs_weighted_center_sq"]
--   coverage: partial — existing hits cover the normalized endpoint context or
--     the prox-step endpoint assembly when convexity of the auxiliary prox
--     objective is already supplied; this theorem derives that convexity from
--     the convex simple composite term and exposes the endpoint recurrence with
--     no paper setup, time-index, or generated-kernel record.
-- G0.4 not-a-thin-wrapper rationale: this theorem adds the reusable invariant
--   that a convex simple term makes the linearized composite prox objective
--   convex, then packages that derived objective into the two-center endpoint
--   recurrence consumed by accelerated stochastic/proximal methods.
-- G0.5 structural-content rationale: theorem, not a def or structure; the
--   statement exposes a one-step algorithm-frame handoff without depending on
--   setup records, generated processes, or sample-kernel implementation fields.
-- G0.5b name-body alignment: the name promises an accelerated composite
--   endpoint recurrence from a convex two-center prox step, and the theorem
--   proves exactly that recurrence.
-- G0.5c thin-wrapper self-detect: clean — body derives prox-objective
--   convexity from `ConvexOn h`, transports the formula into the abstract
--   two-center prox-step endpoint theorem, and is not a direct alias.
-- G0.5d minimal-hypothesis check: all hypotheses are pointwise one-step facts
--   except the carrier/simple-term convexity needed to prove the prox
--   objective convex on arbitrary carrier segments.

/-- A convex two-center prox step gives the accelerated endpoint recurrence.

The linear oracle term plus a convex simple term is convex on the carrier, so a
two-center composite prox optimality certificate can be fed directly into the
standard endpoint squared-distance recurrence for accelerated methods.

Layer: Layer1 | Gap: Level 1 (convex two-center prox-step endpoint recurrence)
Proof: derive convexity of `u ↦ γ * (⟪g, u⟫ + h u)` from linearity of the
  inner product and `ConvexOn h`, transport the prox optimality inequality
  through that definition, and invoke the two-center endpoint assembly theorem.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra,
  Mathlib convex function APIs, and real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent generated-kernel prox step
  before the endpoint boundary and finite-window regularity closure
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_composite_endpoint_recurrence_of_convex_two_center_prox_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (Psi f h : E → ℝ) (V : E → E → ℝ) (objGrad bregGrad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xRef xPlus xBar g eta : E)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_pos : 0 < alpha)
    (hgamma_pos : 0 < gamma)
    (hmu_nonneg : 0 ≤ mu)
    (hX_convex : Convex ℝ X)
    (hh_convex : ConvexOn ℝ X h)
    (hz_mem : z ∈ X)
    (hxRef_mem : xRef ∈ X)
    (hnoise_decomp : g = objGrad xUnder + eta)
    (hV_segment_deriv :
      ∀ (a z u : E), z ∈ X →
        let d : E := u - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z u t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪bregGrad z - bregGrad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0)
    (hV_three :
      ∀ a b c : E,
        V a c = V a b + ⟪bregGrad b - bregGrad a, c - b⟫_ℝ + V b c)
    (h_opt :
      ∀ u, u ∈ X →
        gamma * (⟪g, z⟫_ℝ + h z) +
            (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
          gamma * (⟪g, u⟫_ℝ + h u) +
            (gamma * mu) * V xUnder u + (1 : ℝ) * V prevCenter u)
    (havg_under : xBar - xUnder = alpha • (z - xPlus))
    (hUpper_raw :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪objGrad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * ‖xBar - xUnder‖ ^ 2 +
          M * ‖xBar - xUnder‖)
    (hweighted_absorb :
      ((1 + mu * gamma) / (2 * gamma)) * ‖z - xPlus‖ ^ 2 ≤
        (1 / gamma) * V prevCenter z + mu * V xUnder z)
    (hDeltaSquare :
      alpha *
          (M * ‖z - xPlus‖ - ⟪eta, z - xPlus⟫_ℝ -
            (1 + mu * gamma - L * alpha * gamma) /
              (2 * gamma) * ‖z - xPlus‖ ^ 2) ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)))
    (hPsi_ref_le_xBar : Psi xRef ≤ Psi xBar)
    (hmodel_le :
      f xUnder + ⟪objGrad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef ≤
        Psi xRef)
    (hVz_lower :
      (1 / 2 : ℝ) * ‖z - xRef‖ ^ 2 ≤ V z xRef) :
    alpha / (2 * gamma) * ‖z - xRef‖ ^ 2 ≤
      (1 - alpha) * (Psi prevBar - Psi xRef) +
        alpha / gamma * V prevCenter xRef +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  let p : E → ℝ := fun u => gamma * (⟪g, u⟫_ℝ + h u)
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have hp_convex : ConvexOn ℝ X p := by
    refine ⟨hX_convex, ?_⟩
    intro y hy w hw a b ha hb hab
    have hh := hh_convex.2 hy hw ha hb hab
    have hinner :
        ⟪g, a • y + b • w⟫_ℝ =
          a * ⟪g, y⟫_ℝ + b * ⟪g, w⟫_ℝ := by
      simp [inner_add_right, inner_smul_right]
    simp [p, hinner, smul_eq_mul]
    have hhconv : h (a • y + b • w) ≤ a * h y + b * h w := by
      simpa [smul_eq_mul] using hh
    nlinarith [mul_le_mul_of_nonneg_left hhconv hgamma_nonneg]
  exact
    sq_norm_endpoint_le_of_two_center_prox_step
      X Psi f h V objGrad bregGrad alpha gamma mu L M
      prevBar prevCenter xUnder z xRef xPlus xBar g eta p
      halpha_nonneg halpha_pos hgamma_pos hmu_nonneg hp_convex
      hz_mem hxRef_mem
      (by intro u; rfl)
      hnoise_decomp hV_segment_deriv hV_three
      (by
        intro u hu
        simpa [p] using h_opt u hu)
      havg_under hUpper_raw hweighted_absorb hDeltaSquare
      hPsi_ref_le_xBar hmodel_le hVz_lower

-- Promoted from Staging/Layer1/block_mirror_descent_aggregate_potential_recursion.lean
-- Generalization plan (G0):
-- concept/name: weighted selected-step aggregate potential recursion; orig was expectedSuboptimalityGap_aggregate_potential_recursion, renamed to expose the block mirror descent aggregate-potential recursion rather than the paper's expected-gap proof wrapper.
-- generality used: arbitrary sample path type, state type, reference type, real-valued potential, pointwise successor equality, selected inverse weight, sampled drift, mean drift, scalar noise, and quadratic noise; no measure, filtration, integrability, convexity, smoothness, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: randomized block mirror descent, randomized coordinate mirror-prox, and stochastic coordinate proximal-gradient one-step Lyapunov recursions after a selected-coordinate step bound has been proved; the state, reference point, potential, selected oracle pairing, mean drift, scalar noise, and quadratic bound change while the recursion conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the theorem removes Setup, iterateAt, oneStepUpdate, scalarDelta, and deltaBar; not a duplicate of block_mirror_descent_one_step_aggregate_recursion because this statement additionally transports the generated successor and keeps the selected inverse weight outside the sampled drift/quadratic terms.
-- coverage search: searched SOptLib catalog/source for aggregate potential recursion, selected-block one-step recursion, weighted block potential, and Bregman descent; block_mirror_descent_one_step_aggregate_recursion covers the normalized drift/noise algebra, and weighted_block_bregman_potential_single_block_bound covers the single-block lift, but neither covers the selected inverse-weight plus successor-transport assembly used here.
-- minimal hypotheses: all hypotheses are pointwise scalar inequalities/equalities; global probability, measurability, feasibility, subgradient, and prox construction assumptions are deliberately pushed to callers.

/-- A selected weighted potential step gives the aggregate drift/noise recursion.

If the generated next state agrees with a raw selected update, the raw update
satisfies a weighted sampled-drift/quadratic potential bound, and the selected
weighted drift and quadratic terms decompose into mean drift, scalar noise, and
quadratic noise, then the generated next state satisfies the aggregate
potential recursion.

Layer: Layer1 | Gap: Level 1 (selected weighted aggregate potential recursion)
Proof: rewrite the generated successor to the raw update, substitute the drift
  and quadratic decompositions, and close by ordered real arithmetic.
Source: randomized block-coordinate mirror descent Lyapunov recursion and
  Mathlib ordered-ring arithmetic for real inequalities
Used in: stochastic block mirror descent one-step aggregate Bregman potential
  recursion after the sampled-block prox estimate
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem block_mirror_descent_aggregate_potential_recursion
    {Ω State Ref : Type*}
    (V : State → Ref → ℝ)
    (x rawNext xNext : Ω → State) (xRef : Ref)
    (weight eta sampledDrift meanDrift scalarNoise sampledQuad quadraticNoise : Ω → ℝ)
    (ω : Ω)
    (hsucc : xNext ω = rawNext ω)
    (hstep :
      V (rawNext ω) xRef ≤
        V (x ω) xRef +
          weight ω * (eta ω * sampledDrift ω +
            (1 / 2 : ℝ) * eta ω ^ 2 * sampledQuad ω))
    (hdrift : weight ω * sampledDrift ω = meanDrift ω + scalarNoise ω)
    (hquad : weight ω * sampledQuad ω = quadraticNoise ω) :
    V (xNext ω) xRef ≤
      V (x ω) xRef +
        eta ω * meanDrift ω +
        (eta ω * scalarNoise ω +
          (1 / 2 : ℝ) * eta ω ^ 2 * quadraticNoise ω) := by
  have hrhs :
      V (x ω) xRef +
          weight ω * (eta ω * sampledDrift ω +
            (1 / 2 : ℝ) * eta ω ^ 2 * sampledQuad ω) =
        V (x ω) xRef +
          eta ω * meanDrift ω +
          (eta ω * scalarNoise ω +
            (1 / 2 : ℝ) * eta ω ^ 2 * quadraticNoise ω) := by
    calc
      V (x ω) xRef +
          weight ω * (eta ω * sampledDrift ω +
            (1 / 2 : ℝ) * eta ω ^ 2 * sampledQuad ω)
          = V (x ω) xRef +
              eta ω * (weight ω * sampledDrift ω) +
              (1 / 2 : ℝ) * eta ω ^ 2 * (weight ω * sampledQuad ω) := by
              ring
      _ = V (x ω) xRef +
            eta ω * (meanDrift ω + scalarNoise ω) +
            (1 / 2 : ℝ) * eta ω ^ 2 * quadraticNoise ω := by
              rw [hdrift, hquad]
      _ = V (x ω) xRef +
            eta ω * meanDrift ω +
            (eta ω * scalarNoise ω +
              (1 / 2 : ℝ) * eta ω ^ 2 * quadraticNoise ω) := by
              ring
  rw [hsucc]
  rwa [hrhs] at hstep


-- Promoted from Staging/Layer1/weighted_gap_le_potential_drop_add_noise_of_recursion.lean
-- Generalization plan (G0):
-- concept/name: weighted one-step gap bound from a potential recursion; orig was expectedSuboptimalityGap_one_step_weighted_gap_bound, renamed to expose the support-plus-recursion algebra rather than expected-suboptimality paper notation.
-- generality used: scalar real ordered-ring algebra only; no carrier topology, measure, convexity, smoothness, oracle, or finite-dimensional assumptions are used after the caller supplies the support inequality and one-step recursion.
-- portable call pattern: stochastic mirror descent, randomized block-coordinate mirror descent, proximal-gradient, and variance-reduced methods can call this after a convexity/subgradient support bound and a Lyapunov one-step recursion have been proved; objective values, weight schedules, potential values, and noise terms change while the conclusion stays fixed.
-- counterargument checked: not paper-local traceability because Setup, iterateAt, aggregateBregman, scalarDelta, and deltaBar are removed; not a duplicate of weighted_output_gap_le_initial_potential_add_noise, which consumes this pointwise premise at the finite-window telescope layer.
-- coverage search: searched SOptLib catalog/source for weighted gap, potential drop, one-step recursion, and telescope; top relevant hit was weighted_output_gap_le_initial_potential_add_noise, which is a later summation/Jensen theorem, and LeanSearch returned unrelated weighted-sum facts rather than this support-recursion bridge.
-- minimal hypotheses: all already minimal; the theorem needs exactly weight equality, nonnegative recursion weight, support inequality, and the potential recursion.

/-- A support inequality and one-step potential recursion give a weighted gap bound.

If a reference value supports the current objective value by a linearized
`meanPair` term, and the next potential is bounded by the current potential
plus the same weighted term and noise, then the weighted objective gap is
bounded by the potential drop plus noise.

Layer: Layer1 | Gap: Level 1 (weighted one-step gap from potential recursion)
Proof: turn the support inequality into `currentValue - refValue ≤ -meanPair`,
  multiply by the nonnegative recursion weight, substitute the displayed
  weight, and combine with the one-step potential recursion by ordered-ring
  arithmetic.
Source: convex subgradient support inequalities and Lyapunov descent recursion
  algebra for stochastic first-order methods
Used in: stochastic block mirror descent one-step weighted gap before the
  finite-window output telescope
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem weighted_gap_le_potential_drop_add_noise_of_recursion
    (theta gamma currentValue refValue meanPair potential nextPotential noise : ℝ)
    (htheta : theta = gamma)
    (hsupport : refValue ≥ currentValue + meanPair)
    (hgamma_nonneg : 0 ≤ gamma)
    (hrec : nextPotential ≤ potential + gamma * meanPair + noise) :
    theta * (currentValue - refValue) ≤ potential - nextPotential + noise := by
  rw [htheta]
  have hgap_le : currentValue - refValue ≤ -meanPair := by
    linarith
  have hscaled : gamma * (currentValue - refValue) ≤ gamma * (-meanPair) :=
    mul_le_mul_of_nonneg_left hgap_le hgamma_nonneg
  nlinarith


-- Promoted from Staging/Layer1/integrable_radius_of_pointwise_succ_bound.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: finite-time integrability of a nonnegative radius process from
--   pointwise successor domination; orig was
--   iterateAt_block_displacement_integrable.
-- generality used: arbitrary measurable sample space, arbitrary measure,
--   real-valued nonnegative radius process, real-valued noise/envelope process,
--   and deterministic scalar coefficients. No block setup, oracle structure,
--   independence, convexity, smoothness, Hilbert structure, or finite
--   dimensionality is used by this induction step.
-- portable call pattern: stochastic block mirror descent, randomized
--   coordinate SGD, block proximal-gradient, and variance-reduced methods can
--   call this after proving a one-step radius recursion and integrability of
--   the stochastic increment; the radius, increment, coefficient, and update
--   proof change while finite-time radius integrability stays the conclusion.
-- counterargument checked: Mathlib supplies `Integrable.mono'`, and existing
--   SOptLib/Staging entries cover envelope domination and selected-oracle
--   integrability, but none packages the finite-time successor induction with
--   a two-point totalized-process base case. This is not paper traceability
--   because all SBMD setup fields are replaced by abstract processes and
--   pointwise hypotheses.
-- coverage search: direct rg over SOptLib/Staging/catalog for
--   "integrable radius", "pointwise successor", "block displacement
--   integrable", "Integrable norm Nat induction recursive step", and
--   "successor bound" found only domination primitives, oracle-integrability
--   transfer lemmas, and the separate selected-update successor bound.
--   LeanSearch for "integrable by induction pointwise bounded successor norm
--   constant bound" returned Mathlib integrability primitives such as
--   `MeasureTheory.Integrable.norm`, finite-measure constant lemmas, and
--   interval-integrability results, with no full recurrence theorem.
-- minimal hypotheses: global algorithm assumptions were replaced by
--   a.e. strong measurability, a.e. nonnegativity, integrable base radii at
--   times 0 and 1, integrable increments, and an a.e. successor domination for
--   every positive predecessor time.

/-- A nonnegative radius process is integrable at every finite time from a
positive-time successor domination.

If the totalized process has integrable radii at times `0` and `1`, every
positive successor radius is a.e. bounded by the previous radius plus an
integrable stochastic increment times a deterministic coefficient, and all
radii are a.e. nonnegative and measurable, then each finite-time radius is
integrable.

Layer: Layer1 | Gap: Level 1 (finite-time radius integrability from successor recursion)
Proof: induct on the time index. The positive successor case forms an
  integrable majorant from the induction hypothesis and the increment
  integrability, then applies `Integrable.mono'` using nonnegativity to remove
  real norms.
Source: Mathlib Bochner integrability by a.e. domination and natural-number
  induction APIs
Used in: stochastic block mirror descent adapted block-radius integrability
  after selected-block displacement recursion and oracle dual-norm integrability
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem integrable_radius_of_pointwise_succ_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (radius noise : ℕ → Ω → ℝ) (coeff : ℕ → ℝ) (k : ℕ)
    (hradius_aestronglyMeasurable :
      ∀ n, AEStronglyMeasurable (radius n) μ)
    (hradius_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ radius n ω)
    (hzero : Integrable (radius 0) μ)
    (hone : Integrable (radius 1) μ)
    (hnoise_int : ∀ n, Integrable (noise n) μ)
    (hsucc : ∀ n, 1 ≤ n → ∃ A : ℝ,
      ∀ᵐ ω ∂μ, radius (n + 1) ω ≤
        radius n ω + A * coeff n * noise n ω) :
    Integrable (radius k) μ := by
  induction k with
  | zero =>
      simpa using hzero
  | succ n ih =>
      by_cases hn : 1 ≤ n
      · rcases hsucc n hn with ⟨A, hstep⟩
        have hmajorant :
            Integrable
              (fun ω => radius n ω + A * coeff n * noise n ω) μ := by
          simpa [mul_assoc] using ih.add ((hnoise_int n).const_mul (A * coeff n))
        refine Integrable.mono' hmajorant
          (hradius_aestronglyMeasurable (n + 1)) ?_
        filter_upwards [hradius_nonneg (n + 1), hstep] with ω htarget_nonneg hle
        have hmajorant_nonneg :
            0 ≤ radius n ω + A * coeff n * noise n ω :=
          le_trans htarget_nonneg hle
        simpa [Real.norm_of_nonneg htarget_nonneg,
          Real.norm_of_nonneg hmajorant_nonneg] using hle
      · have hn0 : n = 0 := by omega
        subst n
        simpa using hone


-- Promoted from Staging/Layer1/blockDisplacement_measurable_of_iterate_measurable.lean
-- Generalization plan (G0):
-- concept/name: measurable block-coordinate seminorm displacement from a
--   measurable iterate; orig was iterateAt_block_displacement_measurable.
-- generality used: arbitrary sample space, dependent finite-dimensional real
--   normed block fibers, an abstract measurable iterate into the block product,
--   a fixed reference point, and arbitrary block seminorms. No probability
--   measure, filtration, independence, integrability, convexity, smoothness, or
--   oracle assumptions are used.
-- portable call pattern: stochastic block mirror descent, randomized coordinate
--   descent, and block proximal-gradient proofs call this during radius
--   integrability/adaptedness inductions; the generated iterate process,
--   reference point, block fibers, and seminorms change while the single-block
--   displacement measurability conclusion stays the same.
-- counterargument checked: this is not just paper-local traceability because it
--   removes the Lan setup and packages the repeated coordinate-projection plus
--   finite-dimensional seminorm-continuity bridge. It is not covered by the
--   existing finite-sum radius measurability theorem, which handles subtype
--   deterministic budgets rather than a random process slice at one block.
-- coverage search: searched catalog/source for "block displacement
--   measurable", "seminorm radius measurable", "measurable const sub
--   seminorm", and "iterate measurable rawProcess"; Mathlib hits
--   `Measurable.const_sub` and `Measurable.norm` are partial because they do
--   not cover arbitrary seminorms, and SOptLib hits
--   `measurable_finset_sum_const_mul_seminorm_subtype_radius` and
--   `positive_time_iterate_value_measurable_of_raw_process` cover adjacent
--   budget/process steps rather than this single-block displacement map.
-- minimal hypotheses: finite dimensionality is used only to derive continuity
--   of an arbitrary seminorm; all paper setup fields and stochastic assumptions
--   are removed.

/-- A measurable iterate has measurable single-block seminorm displacement.

For dependent finite-dimensional real normed block spaces, projecting a
measurable block-valued process to one coordinate, subtracting it from a fixed
reference coordinate, and applying an arbitrary block seminorm gives a
measurable real-valued map.

Layer: Glue | Gap: Level 1 (single-block seminorm displacement measurability)
Proof: compose the measurable product iterate with the coordinate projection,
  use measurable subtraction by a constant reference coordinate, derive
  continuity of the finite-dimensional seminorm from norm domination, and
  compose.
Source: Mathlib dependent-product measurable-space APIs, measurable
  subtraction, and SOptLib finite-dimensional seminorm norm control
Used in: stochastic block mirror descent finite-time block-radius
  integrability induction after generated iterate measurability
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockDisplacement_measurable_of_iterate_measurable
    {Ω ι : Type*} [MeasurableSpace Ω]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (blockSeminorm : ∀ i, Seminorm ℝ (E i))
    (xRef : ∀ i, E i) (iterate : Ω → ∀ i, E i)
    (i : ι)
    (hiterate : Measurable iterate) :
    Measurable (fun ω : Ω => blockSeminorm i (xRef i - iterate ω i)) := by
  classical
  have hcoord : Measurable (fun ω : Ω => iterate ω i) :=
    (measurable_pi_apply i).comp hiterate
  have hdiff : Measurable (fun ω : Ω => xRef i - iterate ω i) :=
    measurable_const.sub hcoord
  have hseminorm_cont : Continuous (fun x : E i => blockSeminorm i x) := by
    rcases Seminorm.exists_bound_by_norm_of_finiteDimensional (blockSeminorm i) with
      ⟨K, hKnonneg, hK⟩
    let q : Seminorm ℝ (E i) := (Real.toNNReal K) • normSeminorm ℝ (E i)
    have hqcont : Continuous q := by
      change Continuous (fun x : E i => ((Real.toNNReal K : ℝ) * ‖x‖))
      exact continuous_const.mul continuous_norm
    refine Seminorm.continuous_of_le hqcont ?_
    intro x
    change blockSeminorm i x ≤ ((Real.toNNReal K : ℝ) * ‖x‖)
    simpa [Real.toNNReal_of_nonneg hKnonneg] using hK x
  exact hseminorm_cont.measurable.comp hdiff


-- Promoted from Staging/Layer1/iterate_blockRadius_succ_le_of_selected_update.lean
-- Generalization plan (G0):
-- concept/name: successor radius recursion for an iterate updated only in a
--   selected block; orig was iterateAt_block_displacement_succ_bound.
-- generality used: deterministic selected-coordinate process algebra over an
--   arbitrary state type, block-indexed oracle value type, radius functional,
--   dual gauge, update map, and scalar stepsize. No measure, filtration,
--   convexity, smoothness, or Hilbert structure is used by this proof.
-- portable call pattern: stochastic block mirror descent, randomized
--   coordinate mirror descent, and block proximal-gradient integrability
--   inductions that lift a fixed-stepsize selected-block update bound through
--   a sampled recursive process; the state, block oracle, update map, radius,
--   and dual gauge change while the successor inequality has the same shape.
-- counterargument checked: this is not merely paper-local traceability because
--   it abstracts away the SBMD setup and packages the recurring case split
--   between the sampled selected block and unchanged nonselected coordinates.
--   It is not covered by the one-step displacement staging lemmas, which
--   provide the selected-update hypothesis consumed here.
-- coverage search: rg over SOptLib/Staging/docs for "recursive displacement",
--   "successor displacement", "selected block displacement", and "other
--   coordinate" found only Model coordinate-preservation lemmas and the
--   staged one-step selected displacement bounds; no full successor process
--   transport theorem was present. The precise source-shape Lean symbol search
--   could not attach to the stale LSP session, so direct file/catalog search
--   was used for the coverage decision.
-- minimal hypotheses: the selected-update estimate, nonselected-radius
--   preservation, nonnegative stepsize, and nonnegative dual gauge are exactly
--   the pointwise facts used; paper setup fields and positivity proofs are
--   specialized only at the call site.

/-- A selected-block update radius bound transports through one successor step.

If a recursive process advances by applying the sampled block update, the
selected block has a fixed-stepsize radius growth estimate, and all other block
updates preserve the measured radius, then the successor iterate satisfies the
same radius recursion with the sampled block gauge.

Layer: Layer1 | Gap: Level 1 (selected-block successor radius recursion)
Proof: choose the coefficient from the selected-block update estimate, split on
  whether the sampled block is the measured block, and use nonnegativity of the
  added gauge term in the nonselected case.
Source: Mathlib dependent function application, equality case analysis, and
  ordered-ring monotonicity for real inequalities
Used in: stochastic block mirror descent finite-time block-radius
  integrability induction after the sampled recursive update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem iterate_blockRadius_succ_le_of_selected_update
    {Ω ι State : Type*} {Grad : ι → Type*}
    (blockRadius : ι → State → ℝ)
    (dualGauge : (j : ι) → Grad j → ℝ)
    (iterate : ℕ → Ω → State)
    (selectedBlock : ℕ → Ω → ι)
    (selectedOracle : (n : ℕ) → (ω : Ω) → Grad (selectedBlock n ω))
    (update : (j : ι) → State → Grad j → State)
    (stepsize : ℝ) (t : ℕ) (i : ι)
    (hstepsize_nonneg : 0 ≤ stepsize)
    (hdual_nonneg : ∀ (j : ι) (g : Grad j), 0 ≤ dualGauge j g)
    (hiterate_succ :
      ∀ ω : Ω,
        iterate (t + 1) ω =
          update (selectedBlock t ω) (iterate t ω) (selectedOracle t ω))
    (hselected :
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (x : State) (g : Grad i),
          blockRadius i (update i x g) ≤
            blockRadius i x + A * stepsize * dualGauge i g)
    (hother :
      ∀ {j : ι}, j ≠ i → ∀ (x : State) (g : Grad j),
        blockRadius i (update j x g) = blockRadius i x) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ ω : Ω,
        blockRadius i (iterate (t + 1) ω) ≤
          blockRadius i (iterate t ω) +
            A * stepsize * dualGauge (selectedBlock t ω) (selectedOracle t ω) := by
  classical
  rcases hselected with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro ω
  let j : ι := selectedBlock t ω
  let g : Grad j := selectedOracle t ω
  have hsucc := hiterate_succ ω
  by_cases hji : j = i
  · subst hji
    have hsel := hA (iterate t ω) g
    simpa [j, g, hsucc, mul_assoc] using hsel
  · have hsame :
        blockRadius i (update j (iterate t ω) g) =
          blockRadius i (iterate t ω) := by
      exact hother hji (iterate t ω) g
    have hinc_nonneg :
        0 ≤ A * stepsize * dualGauge j g := by
      exact mul_nonneg (mul_nonneg hA_nonneg hstepsize_nonneg) (hdual_nonneg j g)
    calc
      blockRadius i (iterate (t + 1) ω) =
          blockRadius i (update j (iterate t ω) g) := by
        rw [hsucc]
      _ = blockRadius i (iterate t ω) := hsame
      _ ≤ blockRadius i (iterate t ω) + A * stepsize * dualGauge j g :=
        le_add_of_nonneg_right hinc_nonneg


-- Promoted from Staging/Layer1/iterateAt_strictPrefix_measurable.lean
open MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: totalized positive-time iterate strict-prefix measurability; orig was iterateAt_prefix_measurable
-- generality used: arbitrary sample space and state with only MeasurableSpace State; no measure, topology, convexity, oracle, or update assumptions
-- portable call pattern: one-based SGD/SMD/proximal generated iterate freshness before a same-time sample; the raw process, past filtration, and state type change while the conclusion stays the same
-- counterargument checked: not paper-local traceability because it packages a recurring one-based/raw-process index bridge; not a duplicate of iterate_measurable_of_process_measurable_strictPast, which has no nonpositive totalization branch or predecessor-index normalization
-- coverage search: queries "process prefix measurable sampleBlock strict prefix" and "positive time iterate strict past measurable raw process"; top hits process_prefix_measurable_wrt_sampleBlock, recursiveProcess_measurable_wrt_strictPast, iterate_measurable_of_process_measurable_strictPast; partial coverage only
-- minimal hypotheses: hraw is required only in the positive-time branch; h_iterateAt_pos and h_iterateAt_nonpos are the exact view equations needed for rewriting

/-- A totalized one-based iterate inherits strict-prefix measurability from its raw predecessor.

For positive paper time `k`, the public iterate is the raw zero-based slice
`k - 1`, whose strict-past sigma-algebra is indexed by `(k - 1) + 1`.
At nonpositive time, the totalized iterate is constant.

Layer: Model | Gap: Level 1 (totalized positive-time strict-prefix measurability)
Proof: split on `1 ≤ k`; the positive branch normalizes `(k - 1) + 1` to
  `k` and rewrites to the raw-process measurability hypothesis, while the
  remaining branch is constant.
Source: Mathlib measure-theory APIs for measurable rewriting and constant maps
Used in: stochastic block mirror descent iterate freshness before the same-time
  sampled block-oracle pair
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem iterateAt_strictPrefix_measurable
    {Ω State : Type*} [MeasurableSpace State]
    (past : ℕ → MeasurableSpace Ω)
    (rawProcess : ℕ → Ω → State)
    (iterateAt : ℕ → Ω → State)
    (x0 : State)
    (k : ℕ)
    (hraw : 1 ≤ k → Measurable[past (k - 1 + 1)] (rawProcess (k - 1)))
    (h_iterateAt_pos : 1 ≤ k → iterateAt k = rawProcess (k - 1))
    (h_iterateAt_nonpos : ¬ 1 ≤ k → iterateAt k = fun _ => x0) :
    Measurable[past k] (iterateAt k) := by
  by_cases hk : 1 ≤ k
  · have hidx : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hraw' := hraw hk
    rw [hidx] at hraw'
    simpa [h_iterateAt_pos hk] using hraw'
  · rw [h_iterateAt_nonpos hk]
    exact measurable_const

end SOptLib


-- Promoted from Staging/Layer1/blockMirrorUpdate_aggregateBregman_single_block_bound.lean
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: selected block mirror update aggregate Bregman lift; orig was oneStepUpdate_aggregateBregman_sampled_bound, renamed to expose the block-update Lyapunov step rather than a paper setup method.
-- generality used: finite block index, abstract state, arbitrary Bregman-coordinate types with dependent Hilbert ambient evaluation spaces, arbitrary inverse weights, arbitrary block Bregman-like kernels, arbitrary dual norm, and pointwise selected/unchanged coordinate hypotheses; no measure, filtration, convexity, or oracle assumptions are used.
-- portable call pattern: randomized block mirror descent or coordinate mirror-prox one-step recursion; the update selector, block kernel, dual norm, stepsize, and pointwise block descent estimate change while the aggregate weighted-potential conclusion stays fixed.
-- counterargument checked: not paper-local traceability because it removes the concrete Setup/oneStepUpdate/blockProx objects; not a duplicate of weighted_block_bregman_potential_single_block_bound because it additionally rewrites selected-coordinate update data and packages the explicit mirror-step residual delta.
-- coverage search: searched weighted block potential/single block bound in SOptLib and finite weighted coordinate update in Mathlib; weighted_block_bregman_potential_single_block_bound is the underlying core lift, Mathlib has only generic finite-sum update lemmas, and this bridge strengthens the SOptLib theorem for block mirror update call sites.
-- minimal hypotheses: all hypotheses are pointwise; global feasibility, probability, independence, measurability, convexity, and prox construction assumptions are pushed to callers.

/-- A selected block mirror-step estimate lifts to an aggregate weighted Bregman bound.

If an update changes only one coordinate, the selected coordinate satisfies the
usual mirror-step Bregman estimate with a linear residual and dual-norm
quadratic term, and the selected inverse weight is nonnegative, then the
inverse-weighted aggregate block potential satisfies the corresponding one-step
recursion.

Layer: Layer1 | Gap: Level 1 (selected block mirror-step aggregate lift)
Proof: rewrite the selected block estimate through the coordinate equalities
  and invoke the existing weighted single-block potential lift.
Source: finite block-coordinate Bregman Lyapunov algebra for randomized mirror
  descent and Mathlib real inner-product arithmetic
Used in: stochastic block mirror descent sampled-block prox update aggregate
  Bregman potential recursion
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockMirrorUpdate_aggregateBregman_single_block_bound
    {ι State : Type*} {B E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (p : ι → ℝ) (coord : ∀ i, State → B i) (eval : ∀ i, B i → E i)
    (V : ∀ i, B i → B i → ℝ) (dualNorm : ∀ i, E i → ℝ)
    (i : ι) (z y x : State) (zBlock yBlock xBlock : B i) (g : E i) (γ : ℝ)
    (hweight : 0 ≤ (p i)⁻¹)
    (hz : coord i z = zBlock)
    (hy : coord i y = yBlock)
    (hx : coord i x = xBlock)
    (hblock :
      V i yBlock xBlock ≤
        V i zBlock xBlock +
          (γ * ⟪g, eval i xBlock - eval i zBlock⟫_ℝ +
            (1 / 2 : ℝ) * γ ^ 2 * dualNorm i g ^ 2))
    (hother : ∀ j, j ≠ i → coord j y = coord j z) :
    weightedBlockBregmanPotential B p coord V y x ≤
      weightedBlockBregmanPotential B p coord V z x +
        (p i)⁻¹ *
          (γ * ⟪g, eval i xBlock - eval i zBlock⟫_ℝ +
            (1 / 2 : ℝ) * γ ^ 2 * dualNorm i g ^ 2) := by
  classical
  let delta : ℝ :=
    γ * ⟪g, eval i xBlock - eval i zBlock⟫_ℝ +
      (1 / 2 : ℝ) * γ ^ 2 * dualNorm i g ^ 2
  have hblock' :
      V i (coord i y) (coord i x) ≤
        V i (coord i z) (coord i x) + delta := by
    simpa [delta, hz, hy, hx] using hblock
  simpa [delta] using
    weighted_block_bregman_potential_single_block_bound
      (B := B) (p := p) (coord := coord) (V := V)
      (i := i) (z := z) (y := y) (x := x) (delta := delta)
      hweight hblock' (fun j hji => by simp [hother j hji])


-- Promoted from Staging/Layer1/blockMirrorUpdate_selected_displacement_le.lean
-- Generalization plan (G0):
-- concept/name: selected coordinate displacement growth for a block mirror
--   update; orig was oneStepUpdate_selected_block_displacement_bound.
-- generality used: deterministic seminormed real vector geometry with an
--   abstract metric prox carrier, coordinate evaluation, selected-coordinate
--   equality, zero-oracle fixed point, a same-stepsize prox stability
--   hypothesis, and a seminorm-to-ambient-norm comparison. No measure,
--   filtration, convexity, smoothness, or stochastic assumptions are used.
-- portable call pattern: stochastic block mirror descent and randomized
--   coordinate proximal-gradient displacement recursions after a selected
--   block update; the carrier, prox map, dual gauge, and stability constant
--   change while the reference-distance recursion stays the same.
-- counterargument checked: this is not merely paper traceability; it packages
--   the reusable triangle/seminorm conversion and zero-oracle specialization
--   needed by block-update integrability proofs. It is also not covered by
--   SOptLib.blockMirrorUpdate_selected, which only identifies the selected
--   coordinate, or by the paired-variational lemma, which proves the prox
--   stability estimate consumed here.
-- coverage search: direct rg over SOptLib/Staging/catalog for
--   "blockMirrorUpdate selected displacement", "selected coordinate
--   displacement", and "blockProx state oracle gradient bound" found only
--   coordinate-recovery APIs and lower-level prox-stability lemmas; LeanSearch
--   for "coordinate update selected block displacement norm equals prox
--   displacement bound" returned generic norm/triangle facts but no block
--   update assembly theorem. Coverage is partial, not full.
-- minimal hypotheses: finite-dimensionality was reduced to the explicit
--   seminorm bound hypothesis; paper setup fields were reduced to pointwise
--   selected-coordinate, zero-prox, prox-stability, and evaluation-distance
--   assumptions.

open scoped InnerProductSpace

/-- A selected block update grows reference displacement by the prox movement.

If the selected coordinate of an update is the evaluated prox point, the
zero-oracle prox point is the current block, the prox selector is stable against
the zero-oracle comparison, and the block seminorm is bounded by the ambient
norm, then the selected-coordinate reference displacement satisfies the standard
one-step affine growth bound.

Layer: Layer1 | Gap: Level 1 (selected block update displacement recursion)
Proof: specialize the prox stability estimate against the zero oracle, convert
  the resulting metric displacement through the coordinate evaluation and the
  seminorm-to-norm comparison, then use the seminorm triangle inequality.
Source: Mathlib seminorm triangle inequality, normed-space metric identities,
  and coordinate-update prox stability algebra
Used in: stochastic block mirror descent finite-time selected-block
  displacement integrability after the sampled prox update
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockMirrorUpdate_selected_displacement_le
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace P]
    (p : Seminorm ℝ E) (dualGauge : E → ℝ)
    (eval : P → E) (prox : P → E → P) (baseGap : P → P → E)
    (xRef current updated : E) (z : P) (g : E) (gamma : ℝ)
    (hselected : updated = eval (prox z g))
    (hcurrent : current = eval z)
    (hzero : prox z 0 = z)
    (hdual_zero : dualGauge 0 = 0)
    (hbase_self : baseGap z z = 0)
    (hdist_eval : ∀ a b : P, dist (eval a) (eval b) ≤ dist a b)
    (hseminorm_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ d : E, p d ≤ K * ‖d‖)
    (hprox_bound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (z₁ z₂ : P) (g₁ g₂ : E),
          dist (prox z₁ g₁) (prox z₂ g₂) ≤
            C * (gamma * dualGauge (g₁ - g₂) + dualGauge (baseGap z₁ z₂))) :
    ∃ A : ℝ, 0 ≤ A ∧
      p (xRef - updated) ≤ p (xRef - current) + A * gamma * dualGauge g := by
  rcases hseminorm_bound with ⟨K, hK_nonneg, hK_bound⟩
  rcases hprox_bound with ⟨C, hC_nonneg, hprox⟩
  refine ⟨K * C, mul_nonneg hK_nonneg hC_nonneg, ?_⟩
  let y : P := prox z g
  have hdist :
      dist y z ≤ C * (gamma * dualGauge g) := by
    have hraw := hprox z z g 0
    have hraw' :
        dist (prox z g) z ≤
          C * (gamma * dualGauge (g - 0) + dualGauge (baseGap z z)) := by
      simpa [hzero] using hraw
    simpa [y, sub_zero, hbase_self, hdual_zero] using hraw'
  have hnorm :
      ‖eval y - eval z‖ ≤ C * (gamma * dualGauge g) := by
    have hmetric : dist (eval y) (eval z) ≤ C * (gamma * dualGauge g) :=
      (hdist_eval y z).trans hdist
    simpa [dist_eq_norm] using hmetric
  have hstep :
      p (current - eval y) ≤ K * (C * (gamma * dualGauge g)) := by
    have hseminorm :
        p (current - eval y) = p (eval y - eval z) := by
      have hsub : current - eval y = -(eval y - eval z) := by
        rw [hcurrent]
        abel
      rw [hsub]
      simpa using map_neg_eq_map p (eval y - eval z)
    rw [hseminorm]
    exact (hK_bound (eval y - eval z)).trans
      (mul_le_mul_of_nonneg_left hnorm hK_nonneg)
  have htri :
      p (xRef - eval y) ≤ p (xRef - current) + p (current - eval y) := by
    have hsum : xRef - eval y = (xRef - current) + (current - eval y) := by
      abel
    rw [hsum]
    exact map_add_le_add p (xRef - current) (current - eval y)
  calc
    p (xRef - updated) = p (xRef - eval y) := by rw [hselected]
    _ ≤ p (xRef - current) + p (current - eval y) := htri
    _ ≤ p (xRef - current) + K * (C * (gamma * dualGauge g)) := by
      exact add_le_add (le_refl _) hstep
    _ = p (xRef - current) + (K * C) * gamma * dualGauge g := by
      ring


-- Promoted from Staging/Layer1/exists_uniform_blockMirrorUpdate_selected_displacement_le.lean
-- Generalization plan (G0):
-- concept/name: uniform selected-coordinate displacement growth for a fixed
--   stepsize block mirror update; orig was
--   oneStepUpdate_selected_block_displacement_bound_fixedStepsize.
-- generality used: deterministic seminormed real vector geometry with an
--   abstract metric prox carrier, coordinate evaluation, zero-oracle fixed
--   point, same-stepsize prox stability, and seminorm-to-ambient-norm
--   comparison. No measure, filtration, convexity, smoothness, or oracle
--   unbiasedness assumptions are used.
-- portable call pattern: stochastic block mirror descent, randomized
--   coordinate mirror descent, and block proximal-gradient finite-window
--   displacement recursions where the same coefficient must be chosen before
--   the random state and sampled block-gradient value.
-- counterargument checked: this is not paper-local traceability because the
--   statement removes the dependent SBMD setup and exposes the reusable
--   fixed-stepsize uniform-coefficient step. It is not covered by
--   blockMirrorUpdate_selected_displacement_le, whose existential coefficient
--   is pointwise after the selected state and oracle value.
-- coverage search: searched rg/catalog for "selected block displacement",
--   "uniform displacement", and "blockMirrorUpdate selected displacement";
--   the only full neighbor was the staged pointwise theorem
--   blockMirrorUpdate_selected_displacement_le. LeanSearch for "seminorm
--   reference displacement update bounded by current displacement plus
--   movement" returned Mathlib triangle/norm insert lemmas, which are proof
--   components rather than the uniform block-update assembly.
-- minimal hypotheses: finite-dimensionality is not assumed; it is represented
--   by the explicit seminorm bound hypothesis. Paper setup fields are reduced
--   to pointwise zero-prox, base self-gap, evaluation nonexpansiveness, and
--   prox-stability assumptions.

/-- A fixed-stepsize selected block update admits a uniform displacement
coefficient.

If every zero-oracle prox point is the current block, the prox selector is
stable at a fixed stepsize, and the selected-coordinate seminorm is bounded by
the ambient norm, then one coefficient controls the reference displacement for
all current block states and oracle values.

Layer: Layer1 | Gap: Level 1 (uniform selected block update displacement recursion)
Proof: choose the product of the seminorm comparison constant and the prox
  stability constant, specialize stability against the zero oracle at the same
  current state, convert metric displacement through the evaluation map, and
  close with the seminorm triangle inequality.
Source: Mathlib seminorm triangle inequality, normed-space metric identities,
  and deterministic mirror-prox stability algebra
Used in: stochastic block mirror descent finite-window displacement
  integrability with a fixed stepsize coefficient chosen before sampling
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem exists_uniform_blockMirrorUpdate_selected_displacement_le
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace P]
    (p : Seminorm ℝ E) (dualGauge : E → ℝ)
    (eval : P → E) (prox : P → E → P) (baseGap : P → P → E)
    (xRef : E) (gamma : ℝ)
    (hzero : ∀ z : P, prox z 0 = z)
    (hdual_zero : dualGauge 0 = 0)
    (hbase_self : ∀ z : P, baseGap z z = 0)
    (hdist_eval : ∀ a b : P, dist (eval a) (eval b) ≤ dist a b)
    (hseminorm_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ d : E, p d ≤ K * ‖d‖)
    (hprox_bound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (z₁ z₂ : P) (g₁ g₂ : E),
          dist (prox z₁ g₁) (prox z₂ g₂) ≤
            C * (gamma * dualGauge (g₁ - g₂) + dualGauge (baseGap z₁ z₂))) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (z : P) (g : E),
        p (xRef - eval (prox z g)) ≤
          p (xRef - eval z) + A * gamma * dualGauge g := by
  rcases hseminorm_bound with ⟨K, hK_nonneg, hK_bound⟩
  rcases hprox_bound with ⟨C, hC_nonneg, hprox⟩
  refine ⟨K * C, mul_nonneg hK_nonneg hC_nonneg, ?_⟩
  intro z g
  let y : P := prox z g
  have hdist :
      dist y z ≤ C * (gamma * dualGauge g) := by
    have hraw := hprox z z g 0
    have hraw' :
        dist (prox z g) z ≤
          C * (gamma * dualGauge (g - 0) + dualGauge (baseGap z z)) := by
      simpa [hzero z] using hraw
    simpa [y, sub_zero, hbase_self z, hdual_zero] using hraw'
  have hnorm :
      ‖eval y - eval z‖ ≤ C * (gamma * dualGauge g) := by
    have hmetric : dist (eval y) (eval z) ≤ C * (gamma * dualGauge g) :=
      (hdist_eval y z).trans hdist
    simpa [dist_eq_norm] using hmetric
  have hstep :
      p (eval z - eval y) ≤ K * (C * (gamma * dualGauge g)) := by
    have hseminorm :
        p (eval z - eval y) = p (eval y - eval z) := by
      have hsub : eval z - eval y = -(eval y - eval z) := by
        abel
      rw [hsub]
      simpa using map_neg_eq_map p (eval y - eval z)
    rw [hseminorm]
    exact (hK_bound (eval y - eval z)).trans
      (mul_le_mul_of_nonneg_left hnorm hK_nonneg)
  have htri :
      p (xRef - eval y) ≤ p (xRef - eval z) + p (eval z - eval y) := by
    have hsum : xRef - eval y = (xRef - eval z) + (eval z - eval y) := by
      abel
    rw [hsum]
    exact map_add_le_add p (xRef - eval z) (eval z - eval y)
  calc
    p (xRef - eval (prox z g)) = p (xRef - eval y) := by rfl
    _ ≤ p (xRef - eval z) + p (eval z - eval y) := htri
    _ ≤ p (xRef - eval z) + K * (C * (gamma * dualGauge g)) := by
      exact add_le_add (le_refl _) hstep
    _ = p (xRef - eval z) + (K * C) * gamma * dualGauge g := by
      ring



namespace SOptLib

/-- Positive-time one-step regularity interface for a recursive stochastic
process and its displayed current-call stream. -/
def RecursiveProcessOneStepMeasurableUpTo
    {Ω State Call : Type*}
    (StateMeasurable : (Ω → State) → Prop)
    (CallMeasurable : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (T : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ T →
    StateMeasurable (state i) →
    CallMeasurable (call i) →
      StateMeasurable (state (i + 1))

@[simp]
theorem RecursiveProcessOneStepMeasurableUpTo_iff
    {Ω State Call : Type*}
    (StateMeasurable : (Ω → State) → Prop)
    (CallMeasurable : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (T : ℕ) :
    RecursiveProcessOneStepMeasurableUpTo StateMeasurable CallMeasurable state call T ↔
      ∀ i, 1 ≤ i → i ≤ T →
        StateMeasurable (state i) →
        CallMeasurable (call i) →
          StateMeasurable (state (i + 1)) := by
  rfl

theorem RecursiveProcessOneStepMeasurableUpTo.step
    {Ω State Call : Type*}
    {StateMeasurable : (Ω → State) → Prop}
    {CallMeasurable : (Ω → Call) → Prop}
    {state : ℕ → Ω → State}
    {call : ℕ → Ω → Call}
    {T i : ℕ}
    (h :
      RecursiveProcessOneStepMeasurableUpTo
        StateMeasurable CallMeasurable state call T)
    (hi_pos : 1 ≤ i) (hi_le : i ≤ T)
    (hstate : StateMeasurable (state i))
    (hcall : CallMeasurable (call i)) :
    StateMeasurable (state (i + 1)) :=
  h i hi_pos hi_le hstate hcall

theorem RecursiveProcessOneStepMeasurableUpTo_mono
    {Ω State Call : Type*}
    {StateMeasurable : (Ω → State) → Prop}
    {CallMeasurable : (Ω → Call) → Prop}
    {state : ℕ → Ω → State}
    {call : ℕ → Ω → Call}
    {T U : ℕ}
    (h :
      RecursiveProcessOneStepMeasurableUpTo
        StateMeasurable CallMeasurable state call U)
    (hTU : T ≤ U) :
    RecursiveProcessOneStepMeasurableUpTo
      StateMeasurable CallMeasurable state call T := by
  intro i hi_pos hi_le hstate hcall
  exact h i hi_pos (le_trans hi_le hTU) hstate hcall

/-- Selected recursive steps supply a positive-time one-step regularity interface. -/
theorem oneStepMeasurableUpTo_of_selectedStep_measurable
    {Ω State Call : Type*}
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (T : ℕ)
    (hstep :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω) :
    RecursiveProcessOneStepMeasurableUpTo
      stateRegular callRegular state call T := by
  intro i hi hiT hstate hcall
  have hselected : stateRegular
      (fun ω => step i hi (call i ω) (state i ω) ω) :=
    hstep i hi hiT hstate hcall
  simpa [hstate_step i hi] using hselected

/-- Finite-horizon selected prox-selector regularity supplies one-step regularity. -/
theorem oneStepMeasurableUpTo_of_selectedProxSelectorsMeasurableAt
    {Ω State Call : Type*}
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (SelectedProxSelectorsMeasurableAt : (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hstep :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω)
    (hselectors :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi) :
    RecursiveProcessOneStepMeasurableUpTo
      stateRegular callRegular state call T := by
  exact
    oneStepMeasurableUpTo_of_selectedStep_measurable
      stateRegular
      callRegular
      state
      call
      step
      T
      (fun i hi hiT hstate hcall =>
        hstep i hi hiT (hselectors i hi hiT) hstate hcall)
      hstate_step

/-- A one-sided selector measurability supplier gives one-step regularity. -/
theorem oneStepMeasurableUpTo_of_dualSelectorMeasurable
    {Ω State Call : Type*}
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (DualSelectorMeasurableAt PrimalSelectorMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hselected :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω)
    (hdual :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i,
        PrimalSelectorMeasurableAt i hi) :
    RecursiveProcessOneStepMeasurableUpTo
      stateRegular callRegular state call T := by
  exact
    oneStepMeasurableUpTo_of_selectedStep_measurable
      stateRegular
      callRegular
      state
      call
      step
      T
      (fun i hi hiT hstate hcall =>
        hselected i hi hiT (hdual i hi hiT) (hprimal i hi) hstate hcall)
      hstate_step

/-- Continuity of the remaining selector supplies one-step regularity. -/
theorem oneStepMeasurableUpTo_of_dualSelectorContinuous
    {Ω State Call : Type*}
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (DualSelectorContinuousAt DualSelectorMeasurableAt PrimalSelectorMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hselected :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω)
    (hdual_of_cont :
      ∀ i, ∀ hi : 1 ≤ i,
        DualSelectorContinuousAt i hi → DualSelectorMeasurableAt i hi)
    (hcont :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorContinuousAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i,
        PrimalSelectorMeasurableAt i hi) :
    RecursiveProcessOneStepMeasurableUpTo
      stateRegular callRegular state call T := by
  exact
    oneStepMeasurableUpTo_of_dualSelectorMeasurable
      stateRegular
      callRegular
      state
      call
      step
      DualSelectorMeasurableAt
      PrimalSelectorMeasurableAt
      T
      hselected
      hstate_step
      (fun i hi hiT => hdual_of_cont i hi (hcont i hi hiT))
      hprimal

/-- A recursive process is state-regular up to `T + 1` when current calls are
realized from current regular states. -/
theorem recursive_process_state_regular_of_realized_call
    {Ω State Call : Type*}
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (T : ℕ)
    (hinit : stateRegular (state 1))
    (hcall :
      ∀ i, i ∈ Finset.Icc 1 T →
        stateRegular (state i) →
          callRegular (call i))
    (hstep :
      RecursiveProcessOneStepMeasurableUpTo
        stateRegular callRegular state call T) :
    ∀ i, 1 ≤ i → i ≤ T + 1 → stateRegular (state i) := by
  intro i hi hT
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => cases hi
      | succ k =>
          cases k with
          | zero =>
              simpa using hinit
          | succ k =>
              have hprev : stateRegular (state (k + 1)) := by
                exact ih (k + 1) (by omega) (by omega) (by omega)
              have hkpos : 1 ≤ k + 1 := by omega
              have hkT : k + 1 ≤ T := by omega
              have hcall_i : callRegular (call (k + 1)) :=
                hcall (k + 1) (Finset.mem_Icc.mpr ⟨hkpos, hkT⟩) hprev
              exact hstep (k + 1) hkpos hkT hprev hcall_i

/-- A positive-time recursive process is state-regular from call-stream and
one-step regularity. -/
theorem recursive_process_state_regular_of_call_stream_and_one_step
    {Ω State Call : Type*}
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (T : ℕ)
    (hinit : stateRegular (state 1))
    (hcall : ∀ i, 1 ≤ i → i ≤ T → callRegular (call i))
    (hstep :
      RecursiveProcessOneStepMeasurableUpTo
        stateRegular callRegular state call T) :
    ∀ i, 1 ≤ i → i ≤ T + 1 → stateRegular (state i) := by
  intro i hi hT
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => cases hi
      | succ k =>
          cases k with
          | zero =>
              simpa using hinit
          | succ k =>
              have hprev : stateRegular (state (k + 1)) := by
                exact ih (k + 1) (by omega) (by omega) (by omega)
              have hkpos : 1 ≤ k + 1 := by omega
              have hkT : k + 1 ≤ T := by omega
              have hcall_i : callRegular (call (k + 1)) :=
                hcall (k + 1) hkpos hkT
              exact hstep (k + 1) hkpos hkT hprev hcall_i

/-- A positive-time recursive process has a measurable reported output under a
finite-horizon realized-call regularity boundary. -/
theorem recursive_process_output_measurable_of_realized_call
    {Ω State Call Output : Type*} [MeasurableSpace Ω] [MeasurableSpace Output]
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (output : (t : ℕ) → 1 ≤ t → Ω → Output)
    (T : ℕ) (hT : 1 ≤ T)
    (hinit : stateRegular (state 1))
    (hcall :
      ∀ i, i ∈ Finset.Icc 1 T →
        stateRegular (state i) →
          callRegular (call i))
    (hstep :
      RecursiveProcessOneStepMeasurableUpTo
        stateRegular callRegular state call T)
    (houtput :
      stateRegular (state (T + 1)) →
        Measurable (output T hT)) :
    Measurable (output T hT) := by
  exact houtput
    (recursive_process_state_regular_of_realized_call
      stateRegular
      callRegular
      state
      call
      T
      hinit
      hcall
      hstep
      (T + 1)
      (by omega)
      (by omega))

/-- A positive-time recursive process has a measurable reported output when
realized calls and regular selected update selectors drive its recursion. -/
theorem recursive_process_output_measurable_of_realized_call_and_regular_selectors
    {Ω State Call Output : Type*} [MeasurableSpace Ω] [MeasurableSpace Output]
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (SelectedProxSelectorsMeasurableAt : (i : ℕ) → 1 ≤ i → Prop)
    (output : (t : ℕ) → 1 ≤ t → Ω → Output)
    (T : ℕ) (hT : 1 ≤ T)
    (hinit : stateRegular (state 1))
    (hcall :
      ∀ i, i ∈ Finset.Icc 1 T →
        stateRegular (state i) →
          callRegular (call i))
    (hstep :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω)
    (hselectors :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi)
    (houtput :
      stateRegular (state (T + 1)) →
        Measurable (output T hT)) :
    Measurable (output T hT) := by
  exact
    recursive_process_output_measurable_of_realized_call
      stateRegular
      callRegular
      state
      call
      output
      T
      hT
      hinit
      hcall
      (oneStepMeasurableUpTo_of_selectedProxSelectorsMeasurableAt
        stateRegular
        callRegular
        state
        call
        step
        SelectedProxSelectorsMeasurableAt
        T
        hstep
        hstate_step
        hselectors)
      houtput

/-- A positive-time recursive process has a measurable reported output under a
direct finite call-stream regularity boundary. -/
theorem recursive_process_output_measurable_of_call_stream_and_one_step
    {Ω State Call Output : Type*} [MeasurableSpace Ω] [MeasurableSpace Output]
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (output : (t : ℕ) → 1 ≤ t → Ω → Output)
    (T : ℕ) (hT : 1 ≤ T)
    (hinit : stateRegular (state 1))
    (hcall : ∀ i, 1 ≤ i → i ≤ T → callRegular (call i))
    (hstep :
      RecursiveProcessOneStepMeasurableUpTo
        stateRegular callRegular state call T)
    (houtput :
      stateRegular (state (T + 1)) →
        Measurable (output T hT)) :
    Measurable (output T hT) := by
  exact houtput
    (recursive_process_state_regular_of_call_stream_and_one_step
      stateRegular
      callRegular
      state
      call
      T
      hinit
      hcall
      hstep
      (T + 1)
      (by omega)
      (by omega))

/-- A positive-time recursive process has a measurable reported output when
current-call regularity is supplied by current-state regularity. -/
theorem recursiveProcess_outputMeasurable_of_totalizedCallBoundary
    {Ω State Call Output : Type*} [MeasurableSpace Ω] [MeasurableSpace Output]
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (output : (t : ℕ) → 1 ≤ t → Ω → Output)
    (T : ℕ) (hT : 1 ≤ T)
    (hinit : stateRegular (state 1))
    (hcall_of_state :
      ∀ i, stateRegular (state i) → callRegular (call i))
    (hstep :
      RecursiveProcessOneStepMeasurableUpTo
        stateRegular callRegular state call T)
    (houtput :
      stateRegular (state (T + 1)) →
        Measurable (output T hT)) :
    Measurable (output T hT) := by
  exact houtput
    (recursive_process_state_regular_of_realized_call
      stateRegular
      callRegular
      state
      call
      T
      hinit
      (fun i _hi hstate => hcall_of_state i hstate)
      hstep
      (T + 1)
      (by omega)
      (by omega))

/-- Terminal output measurability follows from totalized calls and a one-sided
selector regularity supplier. -/
theorem recursiveProcess_outputMeasurable_of_totalizedCall_and_dualSelector
    {Ω State Call Output : Type*} [MeasurableSpace Ω] [MeasurableSpace Output]
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (DualSelectorMeasurableAt PrimalSelectorMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (output : (t : ℕ) → 1 ≤ t → Ω → Output)
    (T : ℕ) (hT : 1 ≤ T)
    (hinit : stateRegular (state 1))
    (hcall_of_state :
      ∀ i, stateRegular (state i) → callRegular (call i))
    (hselected :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω)
    (hdual :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i,
        PrimalSelectorMeasurableAt i hi)
    (houtput :
      stateRegular (state (T + 1)) →
        Measurable (output T hT)) :
    Measurable (output T hT) := by
  exact
    recursiveProcess_outputMeasurable_of_totalizedCallBoundary
      stateRegular
      callRegular
      state
      call
      output
      T
      hT
      hinit
      hcall_of_state
      (oneStepMeasurableUpTo_of_dualSelectorMeasurable
        stateRegular
        callRegular
        state
        call
        step
        DualSelectorMeasurableAt
        PrimalSelectorMeasurableAt
        T
        hselected
        hstate_step
        hdual
        hprimal)
      houtput

/-- Terminal output measurability follows from totalized calls and
continuity-supplied selector measurability. -/
theorem recursiveProcess_outputMeasurable_of_dualSelectorContinuous
    {Ω State Call Output : Type*} [MeasurableSpace Ω] [MeasurableSpace Output]
    (stateRegular : (Ω → State) → Prop)
    (callRegular : (Ω → Call) → Prop)
    (state : ℕ → Ω → State)
    (call : ℕ → Ω → Call)
    (step : (i : ℕ) → 1 ≤ i → Call → State → Ω → State)
    (DualSelectorContinuousAt DualSelectorMeasurableAt PrimalSelectorMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (output : (t : ℕ) → 1 ≤ t → Ω → Output)
    (T : ℕ) (hT : 1 ≤ T)
    (hinit : stateRegular (state 1))
    (hcall_of_state :
      ∀ i, stateRegular (state i) → callRegular (call i))
    (hselected :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
        stateRegular (state i) →
        callRegular (call i) →
          stateRegular
            (fun ω => step i hi (call i ω) (state i ω) ω))
    (hstate_step :
      ∀ i, ∀ hi : 1 ≤ i,
        state (i + 1) =
          fun ω => step i hi (call i ω) (state i ω) ω)
    (hdual_of_cont :
      ∀ i, ∀ hi : 1 ≤ i,
        DualSelectorContinuousAt i hi → DualSelectorMeasurableAt i hi)
    (hcont :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorContinuousAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i,
        PrimalSelectorMeasurableAt i hi)
    (houtput :
      stateRegular (state (T + 1)) →
        Measurable (output T hT)) :
    Measurable (output T hT) := by
  exact
    recursiveProcess_outputMeasurable_of_totalizedCallBoundary
      stateRegular
      callRegular
      state
      call
      output
      T
      hT
      hinit
      hcall_of_state
      (oneStepMeasurableUpTo_of_dualSelectorContinuous
        stateRegular
        callRegular
        state
        call
        step
        DualSelectorContinuousAt
        DualSelectorMeasurableAt
        PrimalSelectorMeasurableAt
        T
        hselected
        hstate_step
        hdual_of_cont
        hcont
        hprimal)
      houtput

-- Generalization plan (G0):
-- concept/name: generated-driver selected prox-selector one-step regularity
--   bridge; orig was GeneratedAxExtensionOneStepMeasurableUpTo_of_selected_prox_regular.
-- generality used: arbitrary sample, state, and generated-driver types with
--   abstract state and driver regularity predicates; the selected prox-selector
--   obligation is a pointwise positive-time predicate. No measure, topology,
--   algebra, convexity, smoothness, oracle, independence, or integrability
--   assumptions are used.
-- portable call pattern: stochastic mirror descent, stochastic proximal
--   gradient, and accelerated primal-dual generated-driver processes where a
--   finite-horizon selected-prox regularity proof discharges the recursive
--   one-step state-regularity contract.
-- counterargument checked: close to
--   `recursiveProcessOneStepMeasurableUpTo_of_selectedStep_measurable` and
--   `oneStepMeasurableUpTo_of_selectedProxSelectorsMeasurableAt`; the former
--   asks callers to build selected-step regularity directly, and the latter is
--   for positive-time displayed calls rather than generated drivers indexed by
--   `i + 1`. This statement combines the generated-driver shape with the
--   recurring selected-prox predicate supplier.
-- coverage search: searched project hits for
--   `OneStepMeasurableUpTo`, `selectedProxSelectorsMeasurableAt`, and
--   `recursiveProcessOneStepMeasurableUpTo`; relevant hits were the generated
--   selected-step bridge and the positive-time selected-prox bridge, with
--   partial but not full statement coverage.
-- minimal hypotheses: all already minimal; the proof uses only the
--   finite-horizon selected-selector supplier, the selected-selector-to-step
--   regularity transformer, and the recursive successor-state equation.


/-- Finite-horizon selected prox-selector regularity supplies generated-driver one-step regularity.

If a generated-driver update is regular whenever the named selected-prox
selector obligation holds at the current positive time, then a finite-horizon
supplier for that selector obligation proves the zero-based recursive
one-step regularity contract.

Layer: Layer1 | Gap: Level 1 (generated-driver selected prox-selector one-step regularity bridge)
Proof: specialize the selected-prox step-regularity hypothesis at the successor
  positive index, supply the selector obligation from the finite-horizon
  hypothesis, and rewrite by the recursive successor equation.
Source: stochastic approximation recursive process APIs and Mathlib
  natural-number successor order rewriting
Used in: stochastic accelerated primal-dual generated-driver selected-prox
  state measurability propagation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem recursiveProcessOneStepMeasurableUpTo_of_selectedProxSelectorsMeasurableAt
    {Ω State Driver : Type*}
    (stateRegular : (Ω → State) → Prop)
    (driverRegular : (Ω → Driver) → Prop)
    (process : ℕ → Ω → State)
    (driver : ℕ → Ω → Driver)
    (step : (i : ℕ) → 1 ≤ i → Driver → State → Ω → State)
    (SelectedProxSelectorsMeasurableAt : (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hstep :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi →
        stateRegular (process (i - 1)) →
        driverRegular (driver i) →
          stateRegular
            (fun ω => step i hi (driver i ω) (process (i - 1) ω) ω))
    (hprocess_step :
      ∀ i,
        process (i + 1) =
          fun ω => step (i + 1) (Nat.succ_pos i) (driver (i + 1) ω)
            (process i ω) ω)
    (hselectors :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi) :
    recursiveProcessOneStepMeasurableUpTo
      stateRegular driverRegular process driver T := by
  intro i hiT hstate hdriver
  have hi_pos : 1 ≤ i + 1 := Nat.succ_pos i
  have hi_le : i + 1 ≤ T := Nat.succ_le_of_lt hiT
  have hselected :
      stateRegular
        (fun ω => step (i + 1) hi_pos (driver (i + 1) ω) (process i ω) ω) := by
    simpa using
      hstep (i + 1) hi_pos hi_le (hselectors (i + 1) hi_pos hi_le)
        hstate hdriver
  simpa [hprocess_step i] using hselected


-- Generalization plan (G0):
-- concept/name: generated-driver one-sided selector measurability bridge; orig
--   was GeneratedAxExtensionOneStepMeasurableUpTo_of_dual_lsc_selector.
-- generality used: arbitrary sample, state, and driver types with abstract
--   state and driver regularity predicates; selector regularity is represented
--   by two positive-time pointwise predicates; no measure, topology, algebra,
--   convexity, smoothness, oracle, integrability, or finite-dimensional
--   assumptions are used by the proof.
-- portable call pattern: stochastic mirror descent, stochastic proximal
--   gradient, and accelerated primal-dual generated-driver processes where one
--   selected update/prox selector is available pointwise and the other is the
--   remaining finite-horizon measurability hypothesis needed to propagate
--   recursive state regularity.
-- counterargument checked: this is close to
--   `recursiveProcessOneStepMeasurableUpTo_of_selectedStep_measurable`, but
--   that theorem still requires both selector-regularity witnesses to be
--   assembled at every generated-driver call site; this lemma packages the
--   recurring one-sided selector-discharge boundary. It is also close to
--   `oneStepMeasurableUpTo_of_dualSelectorMeasurable`, but that theorem covers
--   positive-time state/call indexing rather than generated streams using
--   `driver (i + 1)`.
-- coverage search: searched `oneStepMeasurableUpTo dual selector measurable
--   primal selector`, `recursiveProcessOneStepMeasurableUpTo selectedStep
--   measurable`, and current staging files; hits were the positive-time
--   one-sided selector bridge and the generated-driver both-selector bridge,
--   giving partial but not alpha-equivalent coverage.
-- minimal hypotheses: all already minimal; the proof uses only finite-horizon
--   dual selector regularity, the pointwise primal selector supplier, the
--   selected generated-step regularity transformer, and the recursive
--   successor-state equation.


/-- A generated-driver process is one-step regular from a one-sided selector supplier.

If a generated-driver selected update is regular whenever both selector
regularity obligations are available, and one selector obligation is supplied
pointwise for all positive times, then the remaining finite-horizon selector
hypothesis proves the generated-driver one-step regularity contract.

Layer: Layer1 | Gap: Level 1 (generated-driver one-sided selector measurability bridge)
Proof: apply the generated-driver selected-step bridge, supplying the finite
  horizon dual selector hypothesis and the pointwise primal selector supplier
  at the successor positive time.
Source: stochastic approximation recursive process APIs and Mathlib
  natural-number successor indexing
Used in: stochastic accelerated primal-dual generated-driver selected-prox
  state measurability after compact unique-argmin primal selector regularity
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem recursiveProcessOneStepMeasurableUpTo_of_dualSelector_measurable
    {Ω State Driver : Type*}
    (stateRegular : (Ω → State) → Prop)
    (driverRegular : (Ω → Driver) → Prop)
    (process : ℕ → Ω → State)
    (driver : ℕ → Ω → Driver)
    (step : (i : ℕ) → 1 ≤ i → Driver → State → Ω → State)
    (DualSelectorMeasurableAt PrimalSelectorMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hselected :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
        stateRegular (process (i - 1)) →
        driverRegular (driver i) →
          stateRegular
            (fun ω => step i hi (driver i ω) (process (i - 1) ω) ω))
    (hprocess_step :
      ∀ i,
        process (i + 1) =
          fun ω => step (i + 1) (Nat.succ_pos i) (driver (i + 1) ω)
            (process i ω) ω)
    (hdual :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i,
        PrimalSelectorMeasurableAt i hi) :
    recursiveProcessOneStepMeasurableUpTo
      stateRegular driverRegular process driver T := by
  intro i hiT hstate hdriver
  have hi_pos : 1 ≤ i + 1 := Nat.succ_pos i
  have hi_le : i + 1 ≤ T := Nat.succ_le_of_lt hiT
  have hselected_step :
      stateRegular
        (fun ω => step (i + 1) hi_pos (driver (i + 1) ω) (process i ω) ω) := by
    simpa using
      hselected (i + 1) hi_pos hi_le (hdual (i + 1) hi_pos hi_le)
        (hprimal (i + 1) hi_pos) hstate hdriver
  simpa [hprocess_step i] using hselected_step


-- Generalization plan (G0):
-- concept/name: generated-driver continuity-supplied selector measurability
--   bridge; orig was
--   GeneratedAxExtensionOneStepMeasurableUpTo_of_dual_selector_continuity.
-- generality used: arbitrary sample, state, and driver types with abstract
--   state and driver regularity predicates; selector continuity and selector
--   measurability are pointwise positive-time predicates; no measure,
--   topology, algebra, convexity, smoothness, oracle, integrability, or
--   finite-dimensional assumptions are used by the proof.
-- portable call pattern: stochastic mirror descent, stochastic proximal
--   gradient, and accelerated primal-dual generated-driver processes where
--   continuity of one selected prox/update selector is the standard route to
--   discharge the finite-horizon selector measurability premise needed for
--   recursive state-regularity propagation.
-- counterargument checked: close to
--   `recursiveProcessOneStepMeasurableUpTo_of_dualSelector_measurable`, but
--   that theorem still requires the finite-horizon selector measurability
--   hypothesis directly; this theorem packages the recurring
--   continuity-to-measurability handoff. It is also close to
--   `oneStepMeasurableUpTo_of_dualSelectorContinuous`, but that covers
--   positive-time call/state recurrences rather than generated streams using
--   `driver (i + 1)` and predecessor states `process (i - 1)`.
-- coverage search: searched `recursiveProcessOneStepMeasurableUpTo`,
--   `dualSelectorContinuous`, and staged generated-driver selector bridges;
--   top hits were the generated-driver measurable bridge and the source-time
--   continuity bridge, giving partial but not alpha-equivalent coverage.
-- minimal hypotheses: all already minimal; the proof uses only the pointwise
--   continuity-implies-measurability transformer, finite-horizon continuity,
--   the pointwise primal selector supplier, the selected-step regularity
--   transformer, and the recursive successor-state equation.


/-- Continuity of a generated-driver selector supplies one-step regularity.

If generated-driver recursive one-step regularity follows from dual-selector
measurability and a pointwise primal selector supplier, and continuity of the
dual selector implies that measurability predicate at each positive time, then
finite-horizon dual selector continuity is enough to prove the generated-driver
one-step regularity contract.

Layer: Layer1 | Gap: Level 1 (generated-driver continuity-supplied selector measurability bridge)
Proof: convert the finite-horizon continuity hypothesis to dual selector
  measurability pointwise, then apply the generated-driver one-sided selector
  measurability bridge.
Source: stochastic approximation recursive process APIs and Mathlib universal
  quantifier specialization
Used in: stochastic accelerated primal-dual generated-driver selected-prox
  state measurability when compact prox-selector continuity supplies selector
  measurability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem recursiveProcessOneStepMeasurableUpTo_of_dualSelectorContinuous
    {Ω State Driver : Type*}
    (stateRegular : (Ω → State) → Prop)
    (driverRegular : (Ω → Driver) → Prop)
    (process : ℕ → Ω → State)
    (driver : ℕ → Ω → Driver)
    (step : (i : ℕ) → 1 ≤ i → Driver → State → Ω → State)
    (DualSelectorContinuousAt DualSelectorMeasurableAt PrimalSelectorMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hselected :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
        stateRegular (process (i - 1)) →
        driverRegular (driver i) →
          stateRegular
            (fun ω => step i hi (driver i ω) (process (i - 1) ω) ω))
    (hprocess_step :
      ∀ i,
        process (i + 1) =
          fun ω => step (i + 1) (Nat.succ_pos i) (driver (i + 1) ω)
            (process i ω) ω)
    (hdual_of_cont :
      ∀ i, ∀ hi : 1 ≤ i,
        DualSelectorContinuousAt i hi → DualSelectorMeasurableAt i hi)
    (hcont :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        DualSelectorContinuousAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i,
        PrimalSelectorMeasurableAt i hi) :
    recursiveProcessOneStepMeasurableUpTo
      stateRegular driverRegular process driver T := by
  exact
    recursiveProcessOneStepMeasurableUpTo_of_dualSelector_measurable
      stateRegular
      driverRegular
      process
      driver
      step
      DualSelectorMeasurableAt
      PrimalSelectorMeasurableAt
      T
      hselected
      hprocess_step
      (fun i hi hiT => hdual_of_cont i hi (hcont i hi hiT))
      hprimal


-- Generalization plan (G0):
-- concept/name: recursive-process one-step regularity from
--   variational-stability selected prox suppliers; orig was
--   GeneratedAxExtensionOneStepMeasurableUpTo_of_dual_variational_stability.
-- generality used: arbitrary state, driver, and sample space types with
--   abstract state and driver regularity predicates; selector regularity is
--   represented by positive-time pointwise propositions. No measure,
--   topology, algebra, convexity, smoothness, oracle, independence,
--   integrability, or finite-dimensional assumptions are used.
-- portable call pattern: stochastic mirror descent, stochastic proximal
--   gradient, and accelerated primal-dual generated-driver processes where a
--   dual prox/update selector regularity theorem obtained from variational
--   stability and a primal selector supplier assemble the selected-prox
--   package needed for one-step state regularity propagation.
-- counterargument checked: close to
--   `recursiveProcessOneStepMeasurableUpTo_of_selectedProxSelectorsMeasurableAt`
--   and the inlined selected-prox component assembly; neither alone exposes
--   the recurring generated-driver handoff from variational-stability
--   component suppliers to the one-step recursive regularity interface. This
--   theorem is a reusable composition boundary, not only the paper-local
--   generated `A_x` traceability name.
-- coverage search: searched project/staging for
--   `recursiveProcessOneStepMeasurableUpTo`, `selectedProxSelectorsMeasurableAt`,
--   and `variational_stability`; inspected the generated-driver selected-prox
--   bridge, the positive-time selected-prox bridge, and the totalized-output
--   variational-stability bridge. Coverage is partial: existing entries cover
--   selected-prox one-step propagation or component assembly separately, while
--   this statement combines them before terminal output measurability.
-- minimal hypotheses: all already minimal; the proof uses the selected-step
--   transformer, successor-process equation, dual variational-stability
--   supplier, primal selector supplier, and selected-prox component assembler.


/-- Variational-stability selected prox suppliers give generated-driver one-step regularity.

If a generated-driver selected update is regular whenever the selected-prox
selector package holds, and that package is assembled from a dual selector
regularity supplier obtained by variational stability plus a primal selector
supplier, then the recursive generated-driver one-step regularity contract
holds on the finite horizon.

Layer: Layer1 | Gap: Level 1 (generated-driver variational-stability selected-prox regularity)
Proof: assemble the selected-prox package at each positive time from the dual
  variational-stability and primal selector suppliers, then apply the
  generated-driver selected-prox one-step regularity bridge.
Source: stochastic approximation recursive-process APIs and Mathlib indexed
  universal-specialization principles
Used in: stochastic accelerated primal-dual generated-driver state
  measurability when dual selector regularity is supplied by variational
  stability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem recursive_process_one_step_measurable_up_to_of_variational_stability_selected_prox
    {Ω State Driver : Type*}
    (stateRegular : (Ω → State) → Prop)
    (driverRegular : (Ω → Driver) → Prop)
    (process : ℕ → Ω → State)
    (driver : ℕ → Ω → Driver)
    (step : (i : ℕ) → 1 ≤ i → Driver → State → Ω → State)
    (DualSelectorMeasurableAt PrimalSelectorMeasurableAt SelectedProxSelectorsMeasurableAt :
      (i : ℕ) → 1 ≤ i → Prop)
    (T : ℕ)
    (hstep :
      ∀ i, ∀ hi : 1 ≤ i, i ≤ T →
        SelectedProxSelectorsMeasurableAt i hi →
        stateRegular (process (i - 1)) →
        driverRegular (driver i) →
          stateRegular
            (fun ω => step i hi (driver i ω) (process (i - 1) ω) ω))
    (hprocess_step :
      ∀ i,
        process (i + 1) =
          fun ω => step (i + 1) (Nat.succ_pos i) (driver (i + 1) ω)
            (process i ω) ω)
    (hdual_of_variational_stability :
      ∀ i, ∀ hi : 1 ≤ i, DualSelectorMeasurableAt i hi)
    (hprimal :
      ∀ i, ∀ hi : 1 ≤ i, PrimalSelectorMeasurableAt i hi)
    (hselected_of_components :
      ∀ i, ∀ hi : 1 ≤ i,
        DualSelectorMeasurableAt i hi →
        PrimalSelectorMeasurableAt i hi →
          SelectedProxSelectorsMeasurableAt i hi) :
    recursiveProcessOneStepMeasurableUpTo
      stateRegular driverRegular process driver T := by
  exact
    recursiveProcessOneStepMeasurableUpTo_of_selectedProxSelectorsMeasurableAt
      stateRegular
      driverRegular
      process
      driver
      step
      SelectedProxSelectorsMeasurableAt
      T
      hstep
      hprocess_step
      (fun i hi _hiT =>
        hselected_of_components i hi
          (hdual_of_variational_stability i hi)
          (hprimal i hi))



-- Batch 12 promoted descent-envelope and SAPD boundary bridges.

-- Generalization plan (G0):
-- concept/name: selected gap-maximizer pathwise Lambda bound; orig was
--   GeneratedEq4469GapMaxLambdaBound, renamed away from equation numbers and
--   SAPD setup-field names while retaining the domain terms "gap",
--   "maximizer", and "Lambda" for the selected finite residual sum.
-- generality used: arbitrary measurable sample space, arbitrary measure,
--   abstract output and selected-comparison types, a real-valued gap, an output
--   process, a selector, a finite natural-index window, a real-valued Lambda
--   summand, deterministic scale/base constants, and a raw boundary term; no
--   probability, independence, integrability, Hilbert, convexity, smoothness,
--   or oracle assumptions are used.
-- portable call pattern: stochastic primal-dual, mirror-prox, and stochastic
--   mirror-descent gap proofs after a one-step/telescope lemma has produced a
--   selected-gap inequality with a boundary term and finite residual sum, and a
--   diameter or terminal estimate replaces the boundary by deterministic base
--   terms; the gap, selector, window, Lambda formula, and boundary estimate
--   change while the conclusion shape stays fixed.
-- counterargument checked: the theorem is not merely paper-local traceability
--   because it composes two reusable Layer1 proof obligations under an a.e.
--   selected maximizer.  It is not covered by the later residual-envelope
--   predicates because it preserves the selected finite Lambda sum before the
--   auxiliary/canonical-residual conversion.
-- coverage search: searched catalog/SOptLib/Staging for pathwise gap lambda
--   sum, gap maximizer, Bregman diameter, and residual envelope.  Closest hits
--   were `pathwiseGapBoundWithResidual`, `gapDescentEnvelopeWithPrimalBudget`,
--   and `lambda_sum_le_auxiliary_boundary_add_canonical_residual`; all are
--   partial because they either occur after Lambda has become a residual or
--   bound Lambda itself rather than assembling the selected gap bound.
-- minimal hypotheses: global setup fields were reduced to two a.e. scalar
--   inequalities; the measure is arbitrary and all unused stochastic,
--   topological, and vector-space assumptions were dropped.

/-- A selected gap-maximizer bound keeps the finite Lambda sum after replacing a raw boundary.

If a scaled gap at the selected comparison point is almost everywhere bounded
by a raw boundary plus a finite Lambda sum, and that same raw boundary is almost
everywhere bounded by deterministic base terms, then the selected pathwise gap
is bounded by those base terms plus the Lambda sum.

Layer: Layer1 | Gap: Level 1 (selected gap Lambda boundary replacement)
Proof: filter the two a.e. inequalities to one sample, compose them by
  transitivity, and regroup the real terms by ordered-ring arithmetic.
Source: Mathlib finite big-operator notation, almost-everywhere filters, and
  ordered real arithmetic
Used in: stochastic accelerated primal-dual selected saddle-gap bound before
  the Lambda residual sum is converted to an auxiliary Bregman residual
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem pathwiseGapMaxLambdaBound
    {Ω Out Z : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ℕ)
    (gap : Out → ℝ) (out : Ω → Out) (select : Out → Z)
    (lambda : ℕ → Z → Ω → ℝ)
    (scale primalBase dualBase : ℝ) (rawBoundary : Z → Ω → ℝ)
    (hraw :
      ∀ᵐ ω ∂P,
        scale * gap (out ω) ≤
          rawBoundary (select (out ω)) ω +
            Finset.sum s (fun i => lambda i (select (out ω)) ω))
    (hboundary :
      ∀ᵐ ω ∂P,
        rawBoundary (select (out ω)) ω ≤ primalBase + dualBase) :
    ∀ᵐ ω ∂P,
      scale * gap (out ω) ≤
        primalBase + dualBase +
          Finset.sum s (fun i => lambda i (select (out ω)) ω) := by
  filter_upwards [hraw, hboundary] with ω hrawω hboundaryω
  linarith


-- Generalization plan (G0):
-- concept/name: integrable absolute gap envelope; orig was
--   GeneratedGapDescentEnvelope, renamed away from generated-process and SAPD
--   setup-field language while preserving the stochastic-optimization domain
--   phrase "gap descent envelope".
-- generality used: arbitrary measurable sample space, arbitrary measure, and
--   an arbitrary normed-valued gap random variable dominated a.e. by a
--   real-valued integrable envelope; no probability, independence, Hilbert,
--   convexity, smoothness, oracle, or algorithm-update hypotheses are used.
-- portable call pattern: stochastic mirror descent, stochastic primal-dual,
--   accelerated stochastic-gradient, and mirror-prox proofs after deriving a
--   pathwise descent bound for a real or normed gap and before invoking
--   `Integrable.mono`; the process, gap functional, measure, and envelope
--   witness change while the domination-to-integrability boundary stays fixed.
-- counterargument checked: Mathlib already has `MeasureTheory.Integrable.mono`
--   for the final integrability proof, so this file does not restage that
--   theorem alone; the reusable SOptLib object is the named existential
--   envelope predicate used as a proof boundary across algorithm files.
-- coverage search: searched SOptLib/Staging/catalog for gap envelope,
--   integrable envelope, dominated integrability, and residual mean envelope;
--   closest hits were `gapDescentEnvelopeWithPrimalBudget`,
--   `pathwise_gap_envelope_with_mean_residual`, and Mathlib
--   `MeasureTheory.Integrable.mono`, all partial but none name this absolute
--   integrable-envelope predicate.
-- minimal hypotheses: the SAPD output map and setup gap were reduced to one
--   normed-valued random variable; the measure is arbitrary and
--   `AEStronglyMeasurable` is required only by the integrability theorem.

/-- An absolute gap process has an integrable descent envelope.

The predicate records the common stochastic-optimization boundary where a gap
random variable is a.e. dominated in norm by an integrable real envelope.  It is
intended to be consumed by `GapDescentEnvelope.integrable`, which applies
Mathlib's domination theorem.

Layer: Layer1 | Concept: Gap
Proof: (definitional construction; existential real-valued integrable envelope
  dominating a normed gap random variable)
Source: Mathlib Bochner integrability and almost-everywhere domination APIs
Used in: accelerated stochastic primal-dual saddle-gap integrability after the
  pathwise descent envelope is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def GapDescentEnvelope
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (gap : Ω → E) : Prop :=
  ∃ B : Ω → ℝ, Integrable B μ ∧
    (∀ᵐ ω ∂μ, ‖gap ω‖ ≤ ‖B ω‖)

/-- The absolute gap descent envelope unfolds to its existential domination form.

Layer: Layer1 | Gap: Level 0 (absolute gap descent envelope unfolding)
Proof: by rfl after unfolding `GapDescentEnvelope`.
Source: Mathlib Bochner integrability and almost-everywhere domination APIs
Used in: accelerated stochastic primal-dual saddle-gap integrability after the
  pathwise descent envelope is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem GapDescentEnvelope_def
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (gap : Ω → E) :
    GapDescentEnvelope μ gap =
      (∃ B : Ω → ℝ, Integrable B μ ∧
        (∀ᵐ ω ∂μ, ‖gap ω‖ ≤ ‖B ω‖)) := by
  rfl

/-- An integrable dominating process introduces an absolute gap descent envelope.

Layer: Layer1 | Gap: Level 1 (absolute gap descent envelope construction)
Proof: use the supplied dominating process as the existential envelope witness.
Source: Mathlib Bochner integrability and almost-everywhere domination APIs
Used in: accelerated stochastic primal-dual saddle-gap integrability after the
  pathwise descent envelope is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem GapDescentEnvelope.intro
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {gap : Ω → E} {B : Ω → ℝ}
    (hB_int : Integrable B μ)
    (hdom : ∀ᵐ ω ∂μ, ‖gap ω‖ ≤ ‖B ω‖) :
    GapDescentEnvelope μ gap := by
  exact ⟨B, hB_int, hdom⟩

/-- A gap with an absolute descent envelope is integrable.

Layer: Layer1 | Gap: Level 1 (absolute envelope domination to gap integrability)
Proof: unpack the envelope witness and apply Mathlib's `Integrable.mono` to the
  a.e. norm domination.
Source: Mathlib Bochner integrability and almost-everywhere domination APIs
Used in: accelerated stochastic primal-dual expected-gap integration after the
  generated descent envelope is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem GapDescentEnvelope.integrable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {gap : Ω → E}
    (hgap_aesm : AEStronglyMeasurable gap μ)
    (henv : GapDescentEnvelope μ gap) :
    Integrable gap μ := by
  rcases henv with ⟨B, hB_int, hdom⟩
  exact hB_int.mono hgap_aesm hdom

/-- A measurable real gap with an absolute descent envelope is integrable.

Layer: Layer1 | Gap: Level 1 (measurable absolute envelope to gap integrability)
Proof: convert measurability to a.e. strong measurability and use
  `GapDescentEnvelope.integrable`.
Source: Mathlib measurable functions, Bochner integrability, and
  almost-everywhere domination APIs
Used in: accelerated stochastic primal-dual expected-gap integration after the
  measurable output gap and generated descent envelope are established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem GapDescentEnvelope.integrable_of_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {gap : Ω → ℝ}
    (hgap_meas : Measurable gap)
    (henv : GapDescentEnvelope μ gap) :
    Integrable gap μ := by
  exact GapDescentEnvelope.integrable hgap_meas.aestronglyMeasurable henv


-- Generalization plan (G0):
-- concept/name: nonnegative one-sided upper bound to absolute gap descent
--   envelope; orig was `GeneratedGapDescentEnvelope.of_nonnegative_upper_bound`,
--   renamed away from generated-process and SAPD setup-field language.
-- generality used: arbitrary measurable sample space, arbitrary measure, and
--   real-valued gap/envelope processes; no probability, independence,
--   integrability beyond the envelope, Hilbert, convexity, smoothness, oracle,
--   or algorithm-update hypotheses are used.
-- portable call pattern: stochastic mirror descent, accelerated stochastic
--   gradient, stochastic primal-dual, and mirror-prox proofs after deriving a
--   pathwise nonnegative gap bound and before consuming the named absolute
--   `GapDescentEnvelope`; the gap process, measure, and upper envelope vary
--   while the conversion from one-sided to absolute domination is unchanged.
-- counterargument checked: this is not merely `Integrable.mono`; it builds the
--   named SOptLib envelope predicate and performs the nonnegativity conversion
--   from `gap ≤ B` to `‖gap‖ ≤ ‖B‖`. It is not paper traceability because the
--   statement contains no algorithm state, generated stream, or SAPD setup.
-- coverage search: searched SOptLib/Staging/catalog for `GapDescentEnvelope`,
--   `nonnegative upper bound`, and `absolute envelope`; closest existing hits
--   are `GapDescentEnvelope.intro`, `GapDescentEnvelope.integrable`, and
--   Mathlib `MeasureTheory.HasFiniteIntegral.mono'`, all partial but none
--   combine nonnegative one-sided real domination with the named envelope.
-- minimal hypotheses: SAPD output and `gap_nonneg` setup fields were reduced
--   to an a.e. nonnegativity hypothesis; the upper bound is a.e.; the measure
--   is arbitrary and no finite-dimensional assumptions are used.

/-- A nonnegative real gap with an integrable one-sided upper bound has an
absolute gap descent envelope.

For nonnegative gaps, an a.e. inequality `gap ≤ B` also makes `B`
nonnegative a.e., so the same `B` witnesses the absolute domination required by
`GapDescentEnvelope`.

Layer: Layer1 | Gap: Level 1 (nonnegative gap upper bound to absolute envelope)
Proof: use the upper bound as the existential envelope witness; on the common
  full-measure set, convert both real norms to absolute values and remove the
  absolute values using nonnegativity.
Source: Mathlib real absolute-value order and almost-everywhere filter APIs
Used in: stochastic accelerated primal-dual saddle-gap integrability after a
  pathwise nonnegative descent bound is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem GapDescentEnvelope.of_nonnegative_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {gap B : Ω → ℝ}
    (hB_int : Integrable B μ)
    (hgap_nonneg : ∀ᵐ ω ∂μ, 0 ≤ gap ω)
    (hupper : ∀ᵐ ω ∂μ, gap ω ≤ B ω) :
    GapDescentEnvelope μ gap := by
  refine ⟨B, hB_int, ?_⟩
  filter_upwards [hgap_nonneg, hupper] with ω hgap_nonnegω hle
  have hB_nonneg : 0 ≤ B ω := le_trans hgap_nonnegω hle
  simpa [Real.norm_eq_abs, abs_of_nonneg hgap_nonnegω, abs_of_nonneg hB_nonneg] using hle


-- Generalization plan (G0):
-- concept/name: scaled pathwise upper bound to gap descent envelope; orig was
--   `GeneratedGapDescentEnvelope.of_eq4472_envelope_scaling_pattern`,
--   renamed away from generated-process, equation-number, and SAPD setup-field
--   language while preserving the reusable gap-envelope construction.
-- generality used: arbitrary measurable sample space, finite measure, and
--   real-valued gap and residual processes; no independence, Hilbert-space,
--   convexity, smoothness, oracle, or algorithm-update hypotheses are used.
-- portable call pattern: stochastic mirror descent, accelerated stochastic
--   gradient, stochastic primal-dual, and mirror-prox proofs after deriving a
--   scaled pathwise descent inequality `c * gap <= B0 + U` and before
--   consuming the absolute `GapDescentEnvelope`; the process, scale, base
--   constant, residual, and pathwise inequality change while the unscaling
--   constructor stays fixed.
-- counterargument checked: this is not paper-local traceability because the
--   statement contains no generated stream, equation number, SAPD state, or
--   source theorem. It is not just the existing
--   `GapDescentEnvelope.of_nonnegative_upper_bound`: this theorem also builds
--   the integrable affine envelope from a finite-measure constant plus an
--   integrable residual and unscales by a positive coefficient.
-- coverage search: searched SOptLib/Staging/catalog for `GapDescentEnvelope`,
--   `scaled pathwise`, `c * gap`, and residual envelopes; closest hits were
--   `GapDescentEnvelope.of_nonnegative_upper_bound`,
--   `pathwise_gap_envelope_with_mean_residual`, and
--   `integral_le_inv_mul_budget_of_ae_mul_le_add`, all partial and none build
--   the named absolute envelope from a scaled a.e. pathwise upper bound.
--   LeanSearch returned generic integrability domination and layer-cake
--   results, not this stochastic-optimization envelope constructor.
-- minimal hypotheses: probability was weakened to finite measure; the SAPD
--   base formula was reduced to one scalar `B0`; the gap nonnegativity and
--   scaled upper bound are only assumed a.e.

/-- A positive scaled pathwise upper bound builds an absolute gap descent envelope.

If a nonnegative real gap satisfies `c * gap <= B0 + U` almost everywhere for a
positive deterministic scale `c`, with integrable residual `U` and finite
underlying measure, then `c⁻¹ * (B0 + U)` is an integrable one-sided upper
bound and hence witnesses the standard absolute `GapDescentEnvelope`.

Layer: Layer1 | Gap: Level 1 (scaled pathwise upper bound to gap envelope)
Proof: form the integrable affine envelope from the finite-measure constant and
  residual, unscale the a.e. pathwise inequality by positivity of `c`, then
  invoke `GapDescentEnvelope.of_nonnegative_upper_bound`.
Source: Mathlib finite-measure Bochner integrability, real ordered-field
  arithmetic, and almost-everywhere filter APIs
Used in: stochastic accelerated primal-dual saddle-gap envelope after the
  scaled pathwise residual inequality is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem GapDescentEnvelope.of_scaled_pathwise_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {gap U : Ω → ℝ} {c B0 : ℝ}
    (hU_int : Integrable U μ)
    (hc_pos : 0 < c)
    (hgap_nonneg : ∀ᵐ ω ∂μ, 0 ≤ gap ω)
    (hscaled : ∀ᵐ ω ∂μ, c * gap ω ≤ B0 + U ω) :
    GapDescentEnvelope μ gap := by
  have hB_int : Integrable (fun ω : Ω => c⁻¹ * (B0 + U ω)) μ := by
    have hconst : Integrable (fun _ : Ω => B0) μ := integrable_const B0
    exact (hconst.add hU_int).const_mul c⁻¹
  refine
    GapDescentEnvelope.of_nonnegative_upper_bound hB_int hgap_nonneg ?_
  filter_upwards [hscaled] with ω hle
  have hscaled' : c⁻¹ * (c * gap ω) ≤ c⁻¹ * (B0 + U ω) := by
    exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (le_of_lt hc_pos))
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  calc
    gap ω = c⁻¹ * (c * gap ω) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
    _ ≤ c⁻¹ * (B0 + U ω) := hscaled'


-- Generalization plan (G0):
-- concept/name: two-block Lambda residual Young split; orig was
--   LambdaTerm_le_auxiliary_step_plus_canonicalU_summand, renamed to expose the
--   auxiliary-step plus canonical-residual summand bound.
-- generality used: two arbitrary real Hilbert blocks with
--   `[NormedAddCommGroup] [InnerProductSpace ℝ]`; no measure, measurability,
--   independence, integrability, convexity, or finite-dimensional assumptions.
-- portable call pattern: accelerated primal-dual, mirror-prox, and two-block
--   stochastic mirror-descent proofs split a one-step residual at an auxiliary
--   point while schedules, residuals, and comparison points vary.
-- counterargument checked: not paper-local traceability because the theorem is
--   stated for the named `twoBlockStochasticLambdaTerm` model formula and only
--   assumes pointwise positivity; not a pure wrapper because it combines two
--   Hilbert Young absorptions with the auxiliary/martingale rearrangement.
-- coverage search: searched `lambdaTerm auxiliary canonical residual summand`,
--   `twoBlockStochasticLambdaTerm square noise martingale correction`, catalog
--   Young hits, and LeanSearch for Hilbert inner-product Young inequalities;
--   Mathlib supplies Cauchy-Schwarz, SOptLib supplies scalar Young absorption,
--   and existing staged Lambda definitions name the formula, but no hit states
--   this two-block auxiliary residual bound.
-- minimal hypotheses: global setup fields were replaced by pointwise schedule
--   positivity at the active index and pointwise denominator positivity.

/-- A two-block Lambda residual is bounded by an auxiliary-point split plus
Young square-noise budgets.

For a named two-block stochastic Lambda residual, moving the residual pairing
from the next point to an auxiliary point leaves a canonical correction against
the previous point.  The two negative squared displacements absorb the remaining
cross terms by Young's inequality, with separate primal and dual stepsizes.

Layer: Layer1 | Gap: Level 1 (two-block Lambda auxiliary residual split)
Proof: unfold the named Lambda residual, rearrange the two Hilbert inner
  products around the auxiliary point, and apply the scaled scalar Young
  inequality separately in each block.
Source: real Hilbert-space Cauchy-Schwarz and ordered-field Young inequality
  algebra
Used in: stochastic accelerated primal-dual Lambda residual algebra before the
  auxiliary prox term and martingale correction are summed
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem lambdaTerm_le_auxiliaryStep_add_canonicalResidualSummand
    {EX EY : Type*}
    [NormedAddCommGroup EX] [InnerProductSpace ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY]
    (gamma eta tau : ℕ → ℝ) (p q : ℝ)
    (zSeq : ℕ → EX × EY) (delta : ℕ → EX × EY)
    (i : ℕ) (z zAux : EX × EY)
    (hgamma : 0 < gamma i) (heta : 0 < eta i) (htau : 0 < tau i)
    (hq : 0 < 1 - q) (hp : 0 < 1 - p) :
    twoBlockStochasticLambdaTerm gamma eta tau p q zSeq delta i z ≤
      gamma i *
        (⟪-(delta i).1, zAux.1 - z.1⟫_ℝ +
          ⟪-(delta i).2, zAux.2 - z.2⟫_ℝ) +
      eta i * gamma i / (2 * (1 - q)) * ‖(delta i).1‖ ^ 2 +
      tau i * gamma i / (2 * (1 - p)) * ‖(delta i).2‖ ^ 2 +
      gamma i *
        (⟪(delta i).1, zAux.1 - (zSeq i).1⟫_ℝ +
          ⟪(delta i).2, zAux.2 - (zSeq i).2⟫_ℝ) := by
  classical
  let xPrev : EX := (zSeq i).1
  let xNext : EX := (zSeq (i + 1)).1
  let yPrev : EY := (zSeq i).2
  let yNext : EY := (zSeq (i + 1)).2
  let xAux : EX := zAux.1
  let yAux : EY := zAux.2
  let dx : EX := (delta i).1
  let dy : EY := (delta i).2
  have hx :
      gamma i * ⟪dx, -(xNext - xPrev)⟫_ℝ -
          (1 - q) * gamma i / (2 * eta i) * ‖xNext - xPrev‖ ^ 2 ≤
        eta i * gamma i / (2 * (1 - q)) * ‖dx‖ ^ 2 := by
    have hinner :
        ⟪dx, -(xNext - xPrev)⟫_ℝ ≤ ‖dx‖ * ‖xNext - xPrev‖ := by
      simpa [norm_neg, norm_sub_rev] using real_inner_le_norm dx (-(xNext - xPrev))
    have hscaled :
        gamma i * ⟪dx, -(xNext - xPrev)⟫_ℝ ≤
          gamma i * (‖dx‖ * ‖xNext - xPrev‖) :=
      mul_le_mul_of_nonneg_left hinner (le_of_lt hgamma)
    let L : ℝ := (1 - q) / (gamma i * eta i)
    have hL : 0 < L := by
      exact div_pos hq (mul_pos hgamma heta)
    have hyoung :=
      mul_mul_le_inv_two_mul_add_half_mul_sq
        (R := ℝ) (gamma i) ‖dx‖ ‖xNext - xPrev‖ L hL
    have hcoeff_left :
        1 / (2 * ((1 - q) / (gamma i * eta i))) =
          eta i * gamma i / (2 * (1 - q)) := by
      field_simp [ne_of_gt hgamma, ne_of_gt heta, ne_of_gt hq]
    have hcoeff_right :
        (1 - q) / (gamma i * eta i) / 2 * (gamma i) ^ 2 =
          (1 - q) * gamma i / (2 * eta i) := by
      field_simp [ne_of_gt hgamma, ne_of_gt heta, ne_of_gt hq]
    have hyoung_norm :
        gamma i * (‖dx‖ * ‖xNext - xPrev‖) ≤
          eta i * gamma i / (2 * (1 - q)) * ‖dx‖ ^ 2 +
            (1 - q) * gamma i / (2 * eta i) * ‖xNext - xPrev‖ ^ 2 := by
      have h := hyoung
      dsimp [L] at h
      rw [hcoeff_left, hcoeff_right] at h
      nlinarith [h]
    nlinarith [hscaled, hyoung_norm]
  have hy :
      gamma i * ⟪dy, -(yNext - yPrev)⟫_ℝ -
          (1 - p) * gamma i / (2 * tau i) * ‖yNext - yPrev‖ ^ 2 ≤
        tau i * gamma i / (2 * (1 - p)) * ‖dy‖ ^ 2 := by
    have hinner :
        ⟪dy, -(yNext - yPrev)⟫_ℝ ≤ ‖dy‖ * ‖yNext - yPrev‖ := by
      simpa [norm_neg, norm_sub_rev] using real_inner_le_norm dy (-(yNext - yPrev))
    have hscaled :
        gamma i * ⟪dy, -(yNext - yPrev)⟫_ℝ ≤
          gamma i * (‖dy‖ * ‖yNext - yPrev‖) :=
      mul_le_mul_of_nonneg_left hinner (le_of_lt hgamma)
    let L : ℝ := (1 - p) / (gamma i * tau i)
    have hL : 0 < L := by
      exact div_pos hp (mul_pos hgamma htau)
    have hyoung :=
      mul_mul_le_inv_two_mul_add_half_mul_sq
        (R := ℝ) (gamma i) ‖dy‖ ‖yNext - yPrev‖ L hL
    have hcoeff_left :
        1 / (2 * ((1 - p) / (gamma i * tau i))) =
          tau i * gamma i / (2 * (1 - p)) := by
      field_simp [ne_of_gt hgamma, ne_of_gt htau, ne_of_gt hp]
    have hcoeff_right :
        (1 - p) / (gamma i * tau i) / 2 * (gamma i) ^ 2 =
          (1 - p) * gamma i / (2 * tau i) := by
      field_simp [ne_of_gt hgamma, ne_of_gt htau, ne_of_gt hp]
    have hyoung_norm :
        gamma i * (‖dy‖ * ‖yNext - yPrev‖) ≤
          tau i * gamma i / (2 * (1 - p)) * ‖dy‖ ^ 2 +
            (1 - p) * gamma i / (2 * tau i) * ‖yNext - yPrev‖ ^ 2 := by
      have h := hyoung
      dsimp [L] at h
      rw [hcoeff_left, hcoeff_right] at h
      nlinarith [h]
    nlinarith [hscaled, hyoung_norm]
  have hx' :
      -((1 - q) * gamma i / (2 * eta i)) * ‖xNext - xPrev‖ ^ 2 -
          gamma i * ⟪dx, xNext - z.1⟫_ℝ ≤
        gamma i * ⟪-dx, xAux - z.1⟫_ℝ +
          eta i * gamma i / (2 * (1 - q)) * ‖dx‖ ^ 2 +
          gamma i * ⟪dx, xAux - xPrev⟫_ℝ := by
    have hrewrite :
        gamma i * ⟪dx, -(xNext - xPrev)⟫_ℝ -
            (1 - q) * gamma i / (2 * eta i) * ‖xNext - xPrev‖ ^ 2 =
          -((1 - q) * gamma i / (2 * eta i)) * ‖xNext - xPrev‖ ^ 2 -
            gamma i * ⟪dx, xNext - z.1⟫_ℝ -
            gamma i * ⟪-dx, xAux - z.1⟫_ℝ -
            gamma i * ⟪dx, xAux - xPrev⟫_ℝ := by
      simp only [inner_neg_left, neg_sub, inner_sub_right]
      ring
    nlinarith [hx]
  have hy' :
      -((1 - p) * gamma i / (2 * tau i)) * ‖yNext - yPrev‖ ^ 2 -
          gamma i * ⟪dy, yNext - z.2⟫_ℝ ≤
        gamma i * ⟪-dy, yAux - z.2⟫_ℝ +
          tau i * gamma i / (2 * (1 - p)) * ‖dy‖ ^ 2 +
          gamma i * ⟪dy, yAux - yPrev⟫_ℝ := by
    have hrewrite :
        gamma i * ⟪dy, -(yNext - yPrev)⟫_ℝ -
            (1 - p) * gamma i / (2 * tau i) * ‖yNext - yPrev‖ ^ 2 =
          -((1 - p) * gamma i / (2 * tau i)) * ‖yNext - yPrev‖ ^ 2 -
            gamma i * ⟪dy, yNext - z.2⟫_ℝ -
            gamma i * ⟪-dy, yAux - z.2⟫_ℝ -
            gamma i * ⟪dy, yAux - yPrev⟫_ℝ := by
      simp only [inner_neg_left, neg_sub, inner_sub_right]
      ring
    nlinarith [hy]
  have hsum := add_le_add hx' hy'
  dsimp [twoBlockStochasticLambdaTerm, xPrev, xNext, yPrev, yNext, xAux, yAux, dx, dy] at hsum ⊢
  nlinarith


-- Generalization plan (G0):
-- concept/name: finite Lambda-sum assembly into an auxiliary Bregman boundary
--   plus a canonical residual; orig was GeneratedEq4471LambdaAuxiliaryBound,
--   renamed away from Eq. numbering and SAPD setup fields.
-- generality used: arbitrary measurable sample space, abstract measure, finite
--   natural-index window, selected comparison point, and real-valued summand,
--   auxiliary, penalty, residual, and boundary terms; no convexity, smoothness,
--   independence, integrability, or Hilbert-space structure is used here.
-- portable call pattern: accelerated primal-dual, mirror-prox, and stochastic
--   mirror-descent proofs can call this after a pointwise Lambda summand split
--   and an auxiliary-process telescope; schedules, iterates, residual formulas,
--   and selected comparison points vary while the finite-sum conclusion remains.
-- counterargument checked: this is not just paper traceability because it
--   factors the recurring Layer1 assembly step between local residual bounds
--   and a pathwise/a.e. descent envelope; it is not a pure wrapper around a
--   single Mathlib lemma because it combines `sum_le_sum`, auxiliary telescope
--   insertion, and residual regrouping under an a.e. selector.
-- coverage search: searched SOptLib/catalog/staging for Lambda auxiliary
--   canonical residual and used LeanSearch for finite-sum inequality coverage;
--   Mathlib supplies `Finset.sum_le_sum` and sum distributivity, and the staged
--   per-summand Lambda split is related but strictly pointwise rather than this
--   finite-window auxiliary-bound assembly.
-- minimal hypotheses: global algorithm setup fields were replaced by pointwise
--   a.e. hypotheses; the measure is arbitrary rather than a probability measure,
--   and all topological/vector-space assumptions were dropped.

/-- A finite Lambda sum is bounded by an auxiliary boundary plus a canonical
residual after a pointwise split and an auxiliary telescope.

The theorem packages the common Layer1 assembly step: each Lambda summand is
split into an auxiliary term and a residual term, the auxiliary terms are
controlled by a boundary plus penalties, and penalties plus residual terms are
recognized as the canonical residual.

Layer: Layer1 | Gap: Level 1 (finite Lambda auxiliary residual assembly)
Proof: filter the a.e. hypotheses to one sample, apply `Finset.sum_le_sum` to
  the pointwise split, insert the auxiliary finite-sum bound, and regroup the
  penalty and residual sums into the named canonical residual.
Source: Mathlib finite big-operator order algebra and measure-theoretic
  almost-everywhere filters
Used in: stochastic accelerated primal-dual pathwise Lambda residual summation
  before the auxiliary Bregman boundary and martingale-noise residual are used
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem lambdaSum_le_auxiliaryBTerm_add_canonicalResidual
    {Ω Z : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (s : Finset ℕ)
    (lambda auxiliary penalty residual : ℕ → Z → Ω → ℝ)
    (auxiliaryBTerm : Z → Ω → ℝ) (canonicalResidual : Ω → ℝ)
    (zSel : Ω → Z)
    (hpoint :
      ∀ᵐ ω ∂P, ∀ i ∈ s,
        lambda i (zSel ω) ω ≤
          auxiliary i (zSel ω) ω + residual i (zSel ω) ω)
    (haux :
      ∀ᵐ ω ∂P,
        Finset.sum s (fun i => auxiliary i (zSel ω) ω) ≤
          auxiliaryBTerm (zSel ω) ω +
            Finset.sum s (fun i => penalty i (zSel ω) ω))
    (hresidual :
      ∀ᵐ ω ∂P,
        Finset.sum s (fun i => penalty i (zSel ω) ω) +
          Finset.sum s (fun i => residual i (zSel ω) ω) =
            canonicalResidual ω) :
    ∀ᵐ ω ∂P,
      Finset.sum s (fun i => lambda i (zSel ω) ω) ≤
        auxiliaryBTerm (zSel ω) ω + canonicalResidual ω := by
  filter_upwards [hpoint, haux, hresidual] with ω hpointω hauxω hresidualω
  have hsum_point :
      Finset.sum s (fun i => lambda i (zSel ω) ω) ≤
        Finset.sum s (fun i =>
          auxiliary i (zSel ω) ω + residual i (zSel ω) ω) := by
    exact Finset.sum_le_sum hpointω
  calc
    Finset.sum s (fun i => lambda i (zSel ω) ω)
        ≤ Finset.sum s (fun i =>
            auxiliary i (zSel ω) ω + residual i (zSel ω) ω) := hsum_point
    _ = Finset.sum s (fun i => auxiliary i (zSel ω) ω) +
          Finset.sum s (fun i => residual i (zSel ω) ω) := by
        rw [Finset.sum_add_distrib]
    _ ≤ (auxiliaryBTerm (zSel ω) ω +
          Finset.sum s (fun i => penalty i (zSel ω) ω)) +
          Finset.sum s (fun i => residual i (zSel ω) ω) := by
        linarith
    _ = auxiliaryBTerm (zSel ω) ω +
          (Finset.sum s (fun i => penalty i (zSel ω) ω) +
            Finset.sum s (fun i => residual i (zSel ω) ω)) := by ring
    _ = auxiliaryBTerm (zSel ω) ω + canonicalResidual ω := by
        rw [hresidualω]


-- Generalization plan (G0):
-- concept/name: residual mean bound from a square-moment component and a
--   nonpositive martingale component; orig was GeneratedEq4473CanonicalUMeanBound,
--   renamed in the concept analysis away from equation numbers and canonical
--   paper notation, while retaining the requested staging declaration name for
--   pipeline backfill.
-- generality used: arbitrary measurable sample space, arbitrary Measure Ω,
--   real-valued residual components, arbitrary finite index set, and a real
--   deterministic budget family; no probability, independence, Hilbert,
--   convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: stochastic mirror descent, accelerated gradient,
--   primal-dual, and variance-reduced proofs split an error residual into a
--   square-moment budgeted term and a conditionally mean-zero or nonpositive
--   martingale term; component functions, finite window, and budget family vary
--   while the residual expectation conclusion stays the same.
-- counterargument checked: not a paper-local traceability wrapper because it
--   composes two reusable proof products, square-noise expectation control and
--   martingale nonpositive mean, into the final residual mean contract; not
--   covered by the two-stream square-noise aggregator, which lacks the
--   residual decomposition and martingale component.
-- coverage search: LeanSearch for "integral sum bound by sum bounds integrable
--   finite sum" found Mathlib `integrable_finset_sum` and
--   `integral_finset_sum`; SOptLib/catalog search found
--   `integrable_finset_sum_and_integral_le_sum_of_per_index`,
--   `weighted_two_noise_finset_sq_integrable_and_bound`, and martingale
--   cancellation lemmas, all partial but none stating this residual assembly.
-- minimal hypotheses: global SAPD schedule and oracle assumptions were reduced
--   to the exact component equality, square-component integrability and budget
--   bound, martingale integrability, and nonpositive martingale mean.

/-- A residual mean bound follows from a square-noise budget and nonpositive martingale mean.

If a real residual decomposes into a budgeted square-noise component plus a
martingale component whose mean is nonpositive, then the residual is integrable
and has the same finite-window deterministic mean budget as the square-noise
component.

Layer: Layer1 | Gap: Level 0 (residual expectation assembly)
Proof: rewrite the residual by the supplied component decomposition, use
  integrability closure under addition, commute the integral through addition,
  and add the square-noise budget to the nonpositive martingale mean.
Source: Mathlib Bochner integral additivity, integrability closure under
  addition, and ordered real arithmetic
Used in: stochastic accelerated primal-dual residual expectation assembly after
  finite-window square-noise aggregation and martingale cancellation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sapdCanonicalResidualMeanBound
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι)
    (U squareNoise martingale : Ω → ℝ) (budget : ι → ℝ)
    (hU : U = fun ω => squareNoise ω + martingale ω)
    (hsquare_int : Integrable squareNoise μ)
    (hsquare_bound :
      ∫ ω, squareNoise ω ∂μ ≤ (1 / 2 : ℝ) * Finset.sum s budget)
    (hmartingale_int : Integrable martingale μ)
    (hmartingale_bound : ∫ ω, martingale ω ∂μ ≤ 0) :
    Integrable U μ ∧
      ∫ ω, U ω ∂μ ≤ (1 / 2 : ℝ) * Finset.sum s budget := by
  constructor
  · rw [hU]
    exact hsquare_int.add hmartingale_int
  · rw [hU]
    rw [integral_add hsquare_int hmartingale_int]
    linarith


-- Generalization plan (G0):
-- concept/name: scaled gap descent envelope with deterministic residual mean
--   budget; orig was GeneratedGapEq4472EnvelopeWithPrimalBudget, renamed away
--   from equation numbers and SAPD setup-field names while keeping the domain
--   phrase "gap descent envelope".
-- generality used: arbitrary measurable sample space, arbitrary output type,
--   arbitrary Measure Ω, a real-valued gap on outputs, an output process, real
--   scale/base/budget constants, and an existential real residual; no
--   probability, independence, Hilbert, convexity, smoothness, or oracle
--   assumptions are used.
-- portable call pattern: stochastic mirror descent, stochastic primal-dual,
--   accelerated stochastic-gradient, and mirror-prox expected-gap proofs after
--   a pathwise scaled gap inequality and a residual expectation estimate; the
--   output map, gap functional, scale, base terms, and residual budget change
--   while the envelope predicate stays the same.
-- counterargument checked: the old staged
--   `pathwise_gap_envelope_with_mean_residual` constructor is theorem-shaped
--   and was rejected as a constructor wrapper; this file instead names the
--   reusable envelope predicate and gives the minimal constructor API.  It is
--   not paper-local traceability because future algorithms can state their
--   expected-gap boundary in this predicate before integrating it.
-- coverage search: searched SOptLib/Staging/catalog for envelope, mean
--   residual, pathwise mean, Integrable with a.e. bounds, and existential U;
--   closest hits were `integral_le_inv_mul_budget_of_ae_mul_le_add`,
--   `residual_mean_bound_of_square_noise_and_martingale_nonpos`, and the
--   rejected constructor `pathwise_gap_envelope_with_mean_residual`, all
--   partial but none provide the named predicate.
-- minimal hypotheses: the SAPD finite-window primal-noise formula was reduced
--   to a deterministic scalar budget; the two deterministic base terms remain
--   explicit because callers commonly track separate primal and dual radius
--   contributions.

/-- A scaled gap descent envelope with a residual whose mean has a deterministic budget.

The predicate records the common stochastic-optimization boundary: an output
gap, after multiplication by a deterministic scale, is almost everywhere bounded
by deterministic base terms plus an integrable residual whose expectation is
bounded by a scalar budget.

Layer: Layer1 | Concept: Gap
Proof: (definitional construction; existential residual envelope with two
  deterministic base terms and a scalar residual mean budget)
Source: stochastic descent-envelope algebra and Mathlib Bochner integrability
  predicates
Used in: accelerated stochastic primal-dual saddle-gap envelope after the
  pathwise descent inequality and residual expectation estimate
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def gapDescentEnvelopeWithPrimalBudget
    {Ω Out : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (gap : Out → ℝ) (out : Ω → Out)
    (scale primalBase dualBase residualBudget : ℝ) : Prop :=
  ∃ U : Ω → ℝ, Integrable U P ∧
    (∫ ω, U ω ∂P ≤ residualBudget) ∧
    (∀ᵐ ω ∂P, scale * gap (out ω) ≤ primalBase + dualBase + U ω)

/-- The scaled gap descent envelope unfolds to its existential residual formula.

Layer: Layer1 | Gap: Level 0 (gap descent envelope unfolding)
Proof: by rfl after unfolding `gapDescentEnvelopeWithPrimalBudget`.
Source: stochastic descent-envelope algebra and Mathlib Bochner integrability
  predicates
Used in: accelerated stochastic primal-dual saddle-gap envelope after the
  pathwise descent inequality and residual expectation estimate
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem gapDescentEnvelopeWithPrimalBudget_def
    {Ω Out : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (gap : Out → ℝ) (out : Ω → Out)
    (scale primalBase dualBase residualBudget : ℝ) :
    gapDescentEnvelopeWithPrimalBudget P gap out scale primalBase dualBase residualBudget =
      (∃ U : Ω → ℝ, Integrable U P ∧
        (∫ ω, U ω ∂P ≤ residualBudget) ∧
        (∀ᵐ ω ∂P, scale * gap (out ω) ≤ primalBase + dualBase + U ω)) := by
  rfl

/-- An integrable residual with a mean budget and pathwise bound builds a gap descent envelope.

Layer: Layer1 | Gap: Level 1 (gap descent envelope construction)
Proof: use the supplied residual as the existential witness and keep its
  integrability, mean bound, and almost-everywhere pathwise bound unchanged.
Source: stochastic descent-envelope algebra and Mathlib almost-everywhere
  predicates
Used in: accelerated stochastic primal-dual saddle-gap envelope after the
  canonical residual mean bound is proved
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gapDescentEnvelopeWithPrimalBudget_intro
    {Ω Out : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {gap : Out → ℝ} {out : Ω → Out}
    {scale primalBase dualBase residualBudget : ℝ} {U : Ω → ℝ}
    (hU_int : Integrable U P)
    (hU_mean : ∫ ω, U ω ∂P ≤ residualBudget)
    (hpath : ∀ᵐ ω ∂P, scale * gap (out ω) ≤ primalBase + dualBase + U ω) :
    gapDescentEnvelopeWithPrimalBudget P gap out scale primalBase dualBase residualBudget := by
  exact ⟨U, hU_int, hU_mean, hpath⟩


-- Generalization plan (G0):
-- concept/name: scaled pathwise gap bound with residual; orig was
--   GeneratedGapEq4472PathwiseCanonicalU, renamed away from equation numbers,
--   algorithm acronyms, and the paper-local canonical `U_t` label.
-- generality used: arbitrary measurable sample space, arbitrary output type,
--   arbitrary Measure Ω, a real-valued gap on outputs, an output process,
--   deterministic scale/base constants, and a real-valued residual; no
--   probability, independence, Hilbert-space, convexity, smoothness, or oracle
--   hypotheses are used.
-- portable call pattern: stochastic mirror descent, accelerated stochastic
--   gradient, mirror-prox, and primal-dual proofs after a pathwise telescope
--   has produced a scaled output-gap inequality with a residual; output maps,
--   deterministic constants, and residual construction change while the
--   conclusion shape stays the same.
-- counterargument checked: this is a formula-bodied predicate, but it names the
--   recurring pathwise half of the descent-envelope interface used separately
--   from mean control; it is not just paper traceability because later
--   expectation bridges and stage-separated boundaries can consume the same
--   predicate before any residual moment estimate is available.
-- coverage search: LeanSearch for a.e. scaled gap/residual bounds found only
--   norm essential-sup and measure-filter lemmas; SOptLib/catalog search found
--   `gapDescentEnvelopeWithPrimalBudget`,
--   `pathwise_gap_envelope_with_mean_residual`, and
--   `integral_le_inv_mul_budget_of_ae_mul_le_add`, all partial because they
--   either include integrability/mean control or integrate the bound rather
--   than naming the standalone pathwise predicate.
-- minimal hypotheses: all already minimal; only the measure and the scalar a.e.
--   inequality are present, with the two deterministic base terms left
--   separate to match common primal/dual or initial/telescope decompositions.

/-- A scaled output gap is almost everywhere bounded by deterministic bases plus a residual.

This predicate records the pathwise half of a stochastic descent envelope before
any integrability or residual mean estimate is supplied.

Layer: Layer1 | Concept: Gap
Proof: (definitional construction; almost-everywhere scaled gap inequality
  with two deterministic base terms and a residual)
Source: stochastic descent-envelope algebra and Mathlib almost-everywhere
  predicates
Used in: accelerated stochastic primal-dual saddle-gap pathwise envelope before
  canonical residual expectation control
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def pathwiseGapBoundWithResidual
    {Ω Out : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (gap : Out → ℝ) (out : Ω → Out)
    (scale primalBase dualBase : ℝ) (residual : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, scale * gap (out ω) ≤ primalBase + dualBase + residual ω

/-- The pathwise gap bound with residual unfolds to its a.e. scalar inequality.

Layer: Layer1 | Gap: Level 0 (pathwise residual gap bound unfolding)
Proof: by rfl after unfolding `pathwiseGapBoundWithResidual`.
Source: stochastic descent-envelope algebra and Mathlib almost-everywhere
  predicates
Used in: accelerated stochastic primal-dual saddle-gap pathwise envelope before
  canonical residual expectation control
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem pathwiseGapBoundWithResidual_def
    {Ω Out : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (gap : Out → ℝ) (out : Ω → Out)
    (scale primalBase dualBase : ℝ) (residual : Ω → ℝ) :
    pathwiseGapBoundWithResidual μ gap out scale primalBase dualBase residual =
      (∀ᵐ ω ∂μ, scale * gap (out ω) ≤ primalBase + dualBase + residual ω) := by
  rfl


-- Generalization plan (G0):
-- concept/name: pathwise residual gap bound from source components; orig was
--   GeneratedGapEq4472PathwiseCanonicalU_of_generated_oracle_realization,
--   renamed away from theorem numbers and setup fields while preserving the
--   proof role: assemble the gap-lambda, auxiliary residual, and diameter
--   components into the named pathwise residual envelope.
-- generality used: arbitrary measurable sample space, arbitrary output type,
--   arbitrary measure, a real-valued gap on outputs, an output process,
--   deterministic scale/base constants, and three a.e. scalar component
--   inequalities; no probability, independence, integrability, Hilbert-space,
--   convexity, smoothness, or oracle hypotheses are used.
-- portable call pattern: stochastic primal-dual, mirror-prox, and stochastic
--   mirror-descent gap proofs after a selected gap/lambda bound, a finite
--   auxiliary/residual assembly, and a diameter/telescope bound have been
--   proved separately; the selected point, lambda formula, auxiliary term, and
--   residual formula vary while the pathwise residual-envelope conclusion stays
--   the same.
-- counterargument checked: this is not merely paper traceability because it is
--   the reusable Layer1 composition boundary between source component lemmas and
--   the pathwise residual envelope consumed by later expectation lemmas.  It is
--   not a duplicate of `pathwiseGapBoundWithResidual`, which is only the target
--   predicate, nor of the Lambda auxiliary lemma, which proves only one of the
--   three component hypotheses.
-- coverage search: searched SOptLib/catalog/staging for pathwise gap residual,
--   canonical residual, Lambda auxiliary, and diameter-bound assemblies; closest
--   hits were `pathwiseGapBoundWithResidual`,
--   `lambda_sum_le_auxiliary_boundary_add_canonical_residual`, and
--   `pathwiseGapMaxLambdaBound`, all partial because none combines the
--   gap/lambda component, auxiliary residual component, and auxiliary diameter
--   component into the final named pathwise residual envelope.  Mathlib supplies
--   only the ordered-ring arithmetic and a.e. filter tools used in the proof.
-- minimal hypotheses: global algorithm setup fields were replaced by pointwise
--   a.e. scalar inequalities; the measure is arbitrary rather than a probability
--   measure, and all stochastic/topological/vector-space assumptions were
--   dropped.

/-- Three source pathwise components assemble into a residual gap bound.

If a scaled gap is bounded by deterministic gap bases plus a lambda component,
that lambda component is bounded by an auxiliary term plus a residual, the
auxiliary term is bounded by deterministic auxiliary bases, and the combined
bases fit into the final budget, then the scaled gap is bounded by the final
bases plus the residual.

Layer: Layer1 | Gap: Level 1 (pathwise residual gap source-component assembly)
Proof: filter the three almost-everywhere component inequalities to one sample,
  compose them by transitivity, and regroup the real terms by ordered-ring
  arithmetic.
Source: Mathlib almost-everywhere filter combinators and ordered real
  arithmetic for stochastic descent-envelope algebra
Used in: stochastic accelerated primal-dual saddle-gap pathwise envelope after
  source gap-lambda, auxiliary residual, and Bregman diameter components are
  available
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem pathwiseGapBoundWithResidual_of_source_components
    {Ω Out : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (gap : Out → ℝ) (out : Ω → Out)
    (scale gapPrimalBase gapDualBase auxPrimalBase auxDualBase
      finalPrimalBase finalDualBase : ℝ)
    (lambda auxiliary residual : Ω → ℝ)
    (h_base :
      gapPrimalBase + gapDualBase + (auxPrimalBase + auxDualBase) ≤
        finalPrimalBase + finalDualBase)
    (h_gap_lambda :
      ∀ᵐ ω ∂P,
        scale * gap (out ω) ≤ gapPrimalBase + gapDualBase + lambda ω)
    (h_aux :
      ∀ᵐ ω ∂P,
        lambda ω ≤ auxiliary ω + residual ω)
    (h_diam :
      ∀ᵐ ω ∂P,
        auxiliary ω ≤ auxPrimalBase + auxDualBase) :
    pathwiseGapBoundWithResidual P gap out scale
      finalPrimalBase finalDualBase residual := by
  filter_upwards [h_gap_lambda, h_aux, h_diam] with ω hgap haux hdiam
  calc
    scale * gap (out ω) ≤ gapPrimalBase + gapDualBase + lambda ω := hgap
    _ ≤ gapPrimalBase + gapDualBase + (auxiliary ω + residual ω) := by
      linarith
    _ ≤ gapPrimalBase + gapDualBase + ((auxPrimalBase + auxDualBase) + residual ω) := by
      linarith
    _ = gapPrimalBase + gapDualBase + (auxPrimalBase + auxDualBase) + residual ω := by
      ring
    _ ≤ finalPrimalBase + finalDualBase + residual ω := by
      linarith


-- Generalization plan (G0):
-- concept/name: sharp gradient-mismatch gap envelope; orig was
--   GeneratedGapEq4472EnvelopeWithMismatch, renamed away from equation
--   numbers, generated-stream setup fields, and SAPD-specific variance names.
-- generality used: deterministic finite-horizon budget predicates over
--   indexed real sequences; no measure, Hilbert, convexity, smoothness,
--   filtration, independence, integrability, or finite-dimensional hypotheses
--   are used by this envelope-lifting boundary.
-- portable call pattern: accelerated primal-dual, mirror-prox, and
--   mixed-center stochastic-gradient proofs after proving a deterministic
--   same-sample gradient-mismatch budget and before invoking a gap envelope
--   that consumes an indexed primal-noise budget; the mismatch predicate, base
--   variances, and downstream envelope predicate vary while the sharp
--   same-sample budget transformation remains the same.
-- counterargument checked: this could look like a one-line paper wrapper, but
--   the staged declaration removes the paper equation number and setup-field
--   names and captures the reusable same-sample budget-lifting contract. It is
--   not covered by the approved loose envelope, whose induced budget is
--   `2 * (2 * sameQueryVariance + 2 * M i) + 2 * additiveVariance`.
-- coverage search: searched SOptLib catalog and staging files for gap
--   envelope, primal budget envelope, gradient mismatch budget, loose
--   mismatch, and same-sample budget; closest hits were
--   `gapDescentEnvelopeWithPrimalBudget`,
--   `gapEnvelopeWithLooseGradientMismatchBudget`, and Mathlib gradient
--   calculus primitives from LeanSearch, all partial because none package the
--   existential mismatch witness with the sharp indexed envelope budget.
-- minimal hypotheses: the SAPD output process, measure, residual random
--   variables, oracle assumptions, and cross-moment proof are reduced to two
--   Prop-valued contracts; the retained formula is the reusable sharp
--   primal-noise budget induced by a same-sample mismatch witness.

/-- A mismatch budget can be lifted to a sharp indexed gap-envelope budget.

The predicate records the common stochastic-optimization boundary where a
finite-horizon gradient-mismatch budget `M` is converted into the sharper
same-sample per-index primal-noise budget consumed by a downstream gap
envelope.

Layer: Layer1 | Concept: Gap
Proof: (definitional construction; existential mismatch witness plus sharp
  same-sample indexed budget transformation)
Source: stochastic square-noise envelope algebra and Mathlib real ordered-ring
  notation
Used in: accelerated stochastic primal-dual mixed-center gap envelope after
  deterministic gradient-mismatch control and same-sample square-noise algebra
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def gapEnvelopeWithGradientMismatchBudget
    (mismatchBudget : (ℕ → ℝ) → Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (envelopeWithBudget : (ℕ → ℝ) → Prop) : Prop :=
  ∃ M : ℕ → ℝ,
    mismatchBudget M ∧
      envelopeWithBudget
        (fun i => (2 * sameQueryVariance + 2 * M i) + additiveVariance)

/-- The sharp gradient-mismatch gap envelope unfolds to its existential budget form.

Layer: Layer1 | Gap: Level 0 (sharp gradient-mismatch envelope unfolding)
Proof: by rfl after unfolding `gapEnvelopeWithGradientMismatchBudget`.
Source: stochastic square-noise envelope algebra and Mathlib real ordered-ring
  notation
Used in: accelerated stochastic primal-dual mixed-center gap envelope after
  deterministic gradient-mismatch control
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem gapEnvelopeWithGradientMismatchBudget_def
    (mismatchBudget : (ℕ → ℝ) → Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (envelopeWithBudget : (ℕ → ℝ) → Prop) :
    gapEnvelopeWithGradientMismatchBudget
        mismatchBudget sameQueryVariance additiveVariance envelopeWithBudget =
      (∃ M : ℕ → ℝ,
        mismatchBudget M ∧
          envelopeWithBudget
            (fun i => (2 * sameQueryVariance + 2 * M i) +
              additiveVariance)) := by
  rfl

/-- A mismatch witness and its sharp indexed-budget envelope build the gap envelope.

Layer: Layer1 | Gap: Level 1 (sharp gradient-mismatch envelope construction)
Proof: use the supplied mismatch witness as the existential witness and keep
  the downstream indexed-budget envelope unchanged.
Source: stochastic square-noise envelope algebra and Mathlib existential
  packaging APIs
Used in: accelerated stochastic primal-dual mixed-center gap envelope after
  the sharp primal-noise budget is derived
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gapEnvelopeWithGradientMismatchBudget_intro
    {mismatchBudget : (ℕ → ℝ) → Prop}
    {sameQueryVariance additiveVariance : ℝ}
    {envelopeWithBudget : (ℕ → ℝ) → Prop}
    {M : ℕ → ℝ}
    (hM : mismatchBudget M)
    (henv :
      envelopeWithBudget
        (fun i => (2 * sameQueryVariance + 2 * M i) + additiveVariance)) :
    gapEnvelopeWithGradientMismatchBudget
      mismatchBudget sameQueryVariance additiveVariance envelopeWithBudget := by
  exact ⟨M, hM, henv⟩


-- Generalization plan (G0):
-- concept/name: same-sample guarded sharp gap-envelope construction; orig was
--   GeneratedGapEq4472EnvelopeWithMismatch_of_generated_oracle_realization_same_sample_cross_guards,
--   renamed away from generated-process notation, equation numbers, and SAPD
--   setup-field names.
-- generality used: fixed-horizon stochastic-optimization proof contracts over
--   an arbitrary sample type: realization, source moment, same-sample moment,
--   cross-moment nonpositivity, martingale nonpositivity, mismatch budget,
--   square-noise budget, canonical mean budget, pathwise envelope, and
--   indexed-budget envelope. No measure, filtration, Hilbert, convexity,
--   smoothness, or finite-dimensional structure is used by this assembly step.
-- portable call pattern: accelerated primal-dual, mirror-prox, and
--   same-sample stochastic mirror-descent proofs after source/same-sample
--   oracle guards and cross-moment cancellation have produced a sharp
--   square-noise budget and before that budget is exposed as a gradient
--   mismatch gap envelope; the guard predicates and downstream envelope
--   predicates vary while the construction shape stays fixed.
-- counterargument checked: this is not only paper-local traceability because
--   it isolates the recurring sharp square-noise plus martingale plus pathwise
--   envelope assembly used by guarded stochastic gap proofs. It is not covered
--   by `gapEnvelopeWithGradientMismatchBudget_intro`, which only packages an
--   already-built indexed-budget envelope, nor by the loose same-sample lemma,
--   whose indexed budget has the larger two-plus-two formula and no cross
--   guard.
-- coverage search: searched project/SOptLib/Staging for "gap envelope
--   mismatch same sample cross guards square noise martingale",
--   "GeneratedDeltaXHatfXACrossMomentNonpos", and "gapEnvelopeWithGradientMismatchBudget";
--   closest hits were `gapEnvelopeWithGradientMismatchBudget_intro`,
--   `gapEnvelopeWithLooseMismatch_of_sameSampleGuards`, and the sharp
--   envelope def, all partial. Lean symbol search was unavailable because the
--   session server was not running; registry and direct source search showed
--   no approved sharp same-sample-cross assembly entry.
-- minimal hypotheses: all SAPD setup fields, residual formulas, and delta
--   random-variable definitions are reduced to the proof contracts actually
--   consumed; same-sample independence and integrability details are not
--   included because this lemma starts after the square-noise supplier has
--   already been established.

/-- Same-sample square-noise, cross, and martingale guards build a sharp gap envelope.

At a fixed stochastic-optimization horizon, a source/same-sample/cross
square-noise supplier produces an existential mismatch budget and the sharp
indexed square-noise bound.  Combining that bound with martingale mean
nonpositivity and a pathwise canonical envelope yields the indexed-budget
envelope required by the sharp gradient-mismatch gap envelope.

Layer: Layer1 | Gap: Level 1 (same-sample cross-guarded sharp gap-envelope assembly)
Proof: obtain the mismatch witness from the square-noise supplier, convert the
  square-noise budget to a canonical mean budget using the martingale guard,
  combine it with the pathwise envelope, and introduce the sharp mismatch
  envelope with the same witness.
Source: stochastic finite-horizon square-noise, cross-moment, and martingale
  decomposition algebra for gap-envelope proofs
Used in: stochastic accelerated primal-dual mixed-center gap envelope after
  same-sample oracle moment guards, cross-moment cancellation, and martingale
  cancellation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gapEnvelopeWithMismatch_of_sameSampleCrossGuards
    {Sample : Type*}
    (sample : Sample) (t : ℕ)
    (Realized SourceMoment SameSampleMoment CrossMoment MartingaleMeanNonpos :
      Sample → ℕ → Prop)
    (MismatchBudget : (ℕ → ℝ) → Prop)
    (SquareNoiseBudget CanonicalMeanBudget EnvelopeWithBudget : (ℕ → ℝ) → Prop)
    (PathwiseEnvelope : Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (hrealized : Realized sample t)
    (hsource : SourceMoment sample t)
    (hmoment : SameSampleMoment sample t)
    (hcross : CrossMoment sample t)
    (hmart : MartingaleMeanNonpos sample t)
    (hsquare :
      Realized sample t → SourceMoment sample t → SameSampleMoment sample t →
        CrossMoment sample t →
          ∃ M : ℕ → ℝ,
            MismatchBudget M ∧
              SquareNoiseBudget
                (fun i => (2 * sameQueryVariance + 2 * M i) +
                  additiveVariance))
    (hpath : Realized sample t → PathwiseEnvelope)
    (hmean :
      ∀ SX : ℕ → ℝ,
        SquareNoiseBudget SX → MartingaleMeanNonpos sample t →
          CanonicalMeanBudget SX)
    (henvelope :
      ∀ SX : ℕ → ℝ,
        PathwiseEnvelope → CanonicalMeanBudget SX → EnvelopeWithBudget SX) :
    gapEnvelopeWithGradientMismatchBudget
      MismatchBudget sameQueryVariance additiveVariance EnvelopeWithBudget := by
  rcases hsquare hrealized hsource hmoment hcross with ⟨M, hM, hsq⟩
  exact
    gapEnvelopeWithGradientMismatchBudget_intro
      (M := M) hM
      (henvelope
        (fun i => (2 * sameQueryVariance + 2 * M i) + additiveVariance)
        (hpath hrealized)
        (hmean
          (fun i => (2 * sameQueryVariance + 2 * M i) + additiveVariance)
          hsq hmart))


-- Generalization plan (G0):
-- concept/name: loose gradient-mismatch gap envelope; orig was
--   GeneratedGapEq4472EnvelopeWithLooseMismatch, renamed away from equation
--   numbers, generated-stream setup fields, and SAPD-specific variance names.
-- generality used: deterministic finite-horizon budget predicates over
--   indexed real sequences; no measure, Hilbert, convexity, smoothness,
--   filtration, independence, or finite-dimensional hypotheses are used by
--   this envelope-lifting boundary.
-- portable call pattern: accelerated primal-dual, mirror-prox, and
--   mixed-center stochastic-gradient proofs after proving a deterministic
--   gradient-mismatch budget and before invoking a gap envelope that consumes
--   an indexed primal-noise budget; the mismatch predicate, two base variances,
--   and downstream envelope predicate vary while the loose two-plus-two budget
--   transformation remains the same.
-- counterargument checked: this could look like paper-local traceability, but
--   the staged declaration removes the source equation number and setup-field
--   names and captures the reusable budget-lifting contract caused by applying
--   the loose squared-norm bound twice. It is not a Mathlib duplicate, and it
--   differs from `gapDescentEnvelopeWithPrimalBudget`, which starts only after
--   a concrete indexed budget is already supplied.
-- coverage search: searched SOptLib/Staging/catalog for gap envelope, primal
--   budget envelope, gradient mismatch budget, loose mismatch, and two-stream
--   square-noise budgets; closest hits were
--   `gapDescentEnvelopeWithPrimalBudget`,
--   `mixed_center_residual_moment_step_of_lipschitz_bounded_domain`, and
--   Mathlib norm-square inequalities, all partial because none packages the
--   existential mismatch witness together with the induced indexed envelope.
-- minimal hypotheses: the SAPD output process, measure, residual random
--   variables, and oracle assumptions are reduced to two Prop-valued contracts;
--   the only retained formula is the reusable loose primal-noise budget.

/-- A mismatch budget can be lifted to a loose indexed gap-envelope budget.

The predicate records the common stochastic-optimization boundary where a
finite-horizon gradient-mismatch budget `M` is converted into the larger
per-index primal-noise budget obtained by two applications of the loose
two-term squared-norm estimate.

Layer: Layer1 | Concept: Gap
Proof: (definitional construction; existential mismatch witness plus loose
  two-plus-two indexed budget transformation)
Source: stochastic square-noise envelope algebra and Mathlib real ordered-ring
  notation
Used in: accelerated stochastic primal-dual mixed-center gap envelope after
  deterministic gradient-mismatch control and before expected-gap integration
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def gapEnvelopeWithLooseGradientMismatchBudget
    (mismatchBudget : (ℕ → ℝ) → Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (envelopeWithBudget : (ℕ → ℝ) → Prop) : Prop :=
  ∃ M : ℕ → ℝ,
    mismatchBudget M ∧
      envelopeWithBudget
        (fun i => 2 * (2 * sameQueryVariance + 2 * M i) + 2 * additiveVariance)

/-- The loose gradient-mismatch gap envelope unfolds to its existential budget form.

Layer: Layer1 | Gap: Level 0 (loose gradient-mismatch envelope unfolding)
Proof: by rfl after unfolding `gapEnvelopeWithLooseGradientMismatchBudget`.
Source: stochastic square-noise envelope algebra and Mathlib real ordered-ring
  notation
Used in: accelerated stochastic primal-dual mixed-center gap envelope after
  deterministic gradient-mismatch control
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem gapEnvelopeWithLooseGradientMismatchBudget_def
    (mismatchBudget : (ℕ → ℝ) → Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (envelopeWithBudget : (ℕ → ℝ) → Prop) :
    gapEnvelopeWithLooseGradientMismatchBudget
        mismatchBudget sameQueryVariance additiveVariance envelopeWithBudget =
      (∃ M : ℕ → ℝ,
        mismatchBudget M ∧
          envelopeWithBudget
            (fun i => 2 * (2 * sameQueryVariance + 2 * M i) +
              2 * additiveVariance)) := by
  rfl

/-- A mismatch witness and its loose indexed-budget envelope build the gap envelope.

Layer: Layer1 | Gap: Level 1 (loose gradient-mismatch envelope construction)
Proof: use the supplied mismatch witness as the existential witness and keep
  the downstream indexed-budget envelope unchanged.
Source: stochastic square-noise envelope algebra and Mathlib existential
  packaging APIs
Used in: accelerated stochastic primal-dual mixed-center gap envelope after
  the loose primal-noise budget is derived
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gapEnvelopeWithLooseGradientMismatchBudget_intro
    {mismatchBudget : (ℕ → ℝ) → Prop}
    {sameQueryVariance additiveVariance : ℝ}
    {envelopeWithBudget : (ℕ → ℝ) → Prop}
    {M : ℕ → ℝ}
    (hM : mismatchBudget M)
    (henv :
      envelopeWithBudget
        (fun i => 2 * (2 * sameQueryVariance + 2 * M i) + 2 * additiveVariance)) :
    gapEnvelopeWithLooseGradientMismatchBudget
      mismatchBudget sameQueryVariance additiveVariance envelopeWithBudget := by
  exact ⟨M, hM, henv⟩


-- Generalization plan (G0):
-- concept/name: same-sample guarded loose gap-envelope construction; orig was
--   GeneratedGapEq4472EnvelopeWithLooseMismatch_of_generated_oracle_realization_same_sample_guards,
--   renamed away from generated-process notation, equation numbers, and SAPD
--   setup-field names.
-- generality used: fixed-horizon stochastic-optimization proof contracts over
--   an arbitrary sample type: realization, source moment, same-sample moment,
--   martingale nonpositivity, mismatch budget, square-noise budget, canonical
--   mean budget, pathwise envelope, and indexed-budget envelope. No measure,
--   filtration, Hilbert, convexity, smoothness, or finite-dimensional structure
--   is used by this assembly step.
-- portable call pattern: accelerated primal-dual, mirror-prox, and
--   generated-query stochastic mirror-descent proofs after same-sample oracle
--   guards have produced square-noise and martingale components and before the
--   indexed primal-noise budget is exposed as a loose gap envelope; the guard
--   predicates and downstream envelope predicates vary while the construction
--   shape stays fixed.
-- counterargument checked: this is not only paper-local traceability because
--   it isolates the recurring square-noise plus martingale plus pathwise
--   envelope assembly used by guarded stochastic gap proofs. It is not covered
--   by `gapEnvelopeWithLooseGradientMismatchBudget_intro`, which only packages
--   an already-built indexed-budget envelope and does not derive that envelope
--   from same-sample square-noise, martingale, and pathwise contracts.
-- coverage search: searched project/SOptLib/Staging for "gap envelope loose
--   mismatch same sample guards square noise martingale" and "gapEnvelopeWithLooseGradientMismatchBudget
--   intro envelope budget martingale square noise"; closest hits were
--   `gapEnvelopeWithLooseGradientMismatchBudget_intro`,
--   `generated_gap_descent_envelope_of_realization_same_sample_guards`, and
--   `expectedGapWithPrimalBudget_of_fixedDomainComplete_sameSampleGuards`,
--   all partial. LeanSearch for "existential budget envelope from square noise
--   bound and martingale nonpositive" returned martingale maximal/upcrossing
--   APIs, not this stochastic-optimization envelope assembly.
-- minimal hypotheses: all SAPD setup fields and delta formulas are reduced to
--   the proof contracts actually consumed; same-sample independence is not
--   included because this lemma starts after the same-sample moment guard has
--   already been supplied.

/-- Same-sample square-noise and martingale guards build a loose gap envelope.

At a fixed stochastic-optimization horizon, a source/same-sample square-noise
supplier produces an existential mismatch budget and indexed square-noise
bound.  Combining that bound with martingale mean nonpositivity and a pathwise
canonical envelope yields the indexed-budget envelope required by the loose
gradient-mismatch gap envelope.

Layer: Layer1 | Gap: Level 1 (same-sample guarded loose gap-envelope assembly)
Proof: obtain the mismatch witness from the square-noise supplier, convert the
  square-noise budget to a canonical mean budget using the martingale guard,
  combine it with the pathwise envelope, and introduce the loose mismatch
  envelope with the same witness.
Source: stochastic finite-horizon square-noise and martingale decomposition
  algebra for gap-envelope proofs
Used in: stochastic accelerated primal-dual mixed-center gap envelope after
  same-sample oracle moment guards and martingale cancellation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gapEnvelopeWithLooseMismatch_of_sameSampleGuards
    {Sample : Type*}
    (sample : Sample) (t : ℕ)
    (Realized SourceMoment SameSampleMoment MartingaleMeanNonpos :
      Sample → ℕ → Prop)
    (MismatchBudget : (ℕ → ℝ) → Prop)
    (SquareNoiseBudget CanonicalMeanBudget EnvelopeWithBudget : (ℕ → ℝ) → Prop)
    (PathwiseEnvelope : Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (hrealized : Realized sample t)
    (hsource : SourceMoment sample t)
    (hmoment : SameSampleMoment sample t)
    (hmart : MartingaleMeanNonpos sample t)
    (hsquare :
      Realized sample t → SourceMoment sample t → SameSampleMoment sample t →
        ∃ M : ℕ → ℝ,
          MismatchBudget M ∧
            SquareNoiseBudget
              (fun i => 2 * (2 * sameQueryVariance + 2 * M i) +
                2 * additiveVariance))
    (hpath : Realized sample t → PathwiseEnvelope)
    (hmean :
      ∀ SX : ℕ → ℝ,
        SquareNoiseBudget SX → MartingaleMeanNonpos sample t →
          CanonicalMeanBudget SX)
    (henvelope :
      ∀ SX : ℕ → ℝ,
        PathwiseEnvelope → CanonicalMeanBudget SX → EnvelopeWithBudget SX) :
    gapEnvelopeWithLooseGradientMismatchBudget
      MismatchBudget sameQueryVariance additiveVariance EnvelopeWithBudget := by
  rcases hsquare hrealized hsource hmoment with ⟨M, hM, hsq⟩
  exact
    gapEnvelopeWithLooseGradientMismatchBudget_intro
      (M := M) hM
      (henvelope
        (fun i => 2 * (2 * sameQueryVariance + 2 * M i) +
          2 * additiveVariance)
        (hpath hrealized)
        (hmean
          (fun i => 2 * (2 * sameQueryVariance + 2 * M i) +
            2 * additiveVariance)
          hsq hmart))


-- Generalization plan (G0):
-- concept/name: smooth bounded-domain generated-realization loose gap-envelope
--   assembly; orig was
--   GeneratedGapEq4472EnvelopeWithLooseMismatch_of_generated_oracle_realization_smooth_bounded_domain,
--   renamed away from equation numbers, SAPD setup fields, and delta notation.
-- generality used: arbitrary measurable probability frame for the per-index
--   independence guard; arbitrary sample/process type; smoothness and gradient
--   measurability are proof contracts used only to derive the source residual
--   moment predicate. No Hilbert, convexity, or finite-dimensional structure is
--   used by this final assembly step.
-- portable call pattern: accelerated primal-dual, generated-query mirror-prox,
--   and stochastic mirror-descent proofs where smooth bounded-domain data first
--   supplies a mixed-center residual moment package, same-sample independence
--   supplies an additive oracle-noise package, and both feed a loose gap
--   envelope with a martingale mean bound.
-- counterargument checked: the theorem is close to a wrapper, but it captures a
--   recurring proof-composition boundary not covered by
--   `gapEnvelopeWithLooseMismatch_of_sameSampleGuards`, which starts after the
--   source and same-sample moment guards have already been constructed.
-- coverage search: searched catalog/source/staging for "loose mismatch smooth
--   bounded domain", "same sample guards", "gradient mismatch moment budget",
--   and "IndepFun same sample moment"; closest hits were
--   `mixed_center_residual_moment_step_of_lipschitz_bounded_domain`,
--   `GeneratedDeltaXASameSamplePerIndexMomentBound.of_generated_query_independence`,
--   and `gapEnvelopeWithLooseMismatch_of_sameSampleGuards`, all partial.
--   LeanSearch for independence-to-oracle moment bounds returned generic
--   independence moment APIs, not this stochastic-optimization envelope bridge.
-- minimal hypotheses: smoothness and measurability are kept as opaque
--   proof-contract propositions because this lemma only consumes the resulting
--   source-moment supplier; the measure frame is only needed to state the
--   per-index `IndepFun` premise.

/-- Smooth bounded-domain and independence suppliers build a loose gap envelope.

At a fixed stochastic-optimization horizon, smooth bounded-domain data produces
the source residual moment package, and per-index query/sample independence
produces the same-sample moment package.  Once these two guards and martingale
mean nonpositivity are available, the same-sample loose-envelope assembly gives
the final gradient-mismatch gap envelope.

Layer: Layer1 | Gap: Level 1 (smooth bounded-domain loose gap-envelope assembly)
Proof: derive the source-moment and same-sample moment guards from their
  suppliers, then invoke the same-sample loose gap-envelope assembly theorem.
Source: stochastic smooth-residual moment estimates, Mathlib probability
  independence APIs, and finite-horizon gap-envelope algebra
Used in: stochastic accelerated primal-dual mixed-center gap envelope after
  smooth gradient-mismatch control and same-sample oracle independence
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gap_envelope_with_loose_mismatch_of_smooth_source_and_same_sample_independence
    {Ω Query Fresh Sample : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Query] [MeasurableSpace Fresh]
    (P : Measure Ω)
    (sample : Sample) (t : ℕ)
    (query : ℕ → Ω → Query) (freshSample : ℕ → Ω → Fresh)
    (Realized SourceMoment SameSampleMoment MartingaleMeanNonpos :
      Sample → ℕ → Prop)
    (GradientLipschitzOnDomain GradientMeasurableOnDomain : Prop)
    (MismatchBudget : (ℕ → ℝ) → Prop)
    (SquareNoiseBudget CanonicalMeanBudget EnvelopeWithBudget : (ℕ → ℝ) → Prop)
    (PathwiseEnvelope : Prop)
    (sameQueryVariance additiveVariance : ℝ)
    (hrealized : Realized sample t)
    (hgrad_lip : GradientLipschitzOnDomain)
    (hgrad_meas : GradientMeasurableOnDomain)
    (hdelta_indep :
      ∀ i, ∀ _hi : i ∈ Finset.Icc 1 t,
        ProbabilityTheory.IndepFun (query i) (freshSample i) P)
    (hmart : MartingaleMeanNonpos sample t)
    (hsource_of_smooth :
      Realized sample t →
        GradientLipschitzOnDomain → GradientMeasurableOnDomain →
          SourceMoment sample t)
    (hsameSample_of_indep :
      Realized sample t →
        (∀ i, ∀ _hi : i ∈ Finset.Icc 1 t,
          ProbabilityTheory.IndepFun (query i) (freshSample i) P) →
          SameSampleMoment sample t)
    (hsquare :
      Realized sample t → SourceMoment sample t → SameSampleMoment sample t →
        ∃ M : ℕ → ℝ,
          MismatchBudget M ∧
            SquareNoiseBudget
              (fun i => 2 * (2 * sameQueryVariance + 2 * M i) +
                2 * additiveVariance))
    (hpath : Realized sample t → PathwiseEnvelope)
    (hmean :
      ∀ SX : ℕ → ℝ,
        SquareNoiseBudget SX → MartingaleMeanNonpos sample t →
          CanonicalMeanBudget SX)
    (henvelope :
      ∀ SX : ℕ → ℝ,
        PathwiseEnvelope → CanonicalMeanBudget SX → EnvelopeWithBudget SX) :
    gapEnvelopeWithLooseGradientMismatchBudget
      MismatchBudget sameQueryVariance additiveVariance EnvelopeWithBudget := by
  exact
    gapEnvelopeWithLooseMismatch_of_sameSampleGuards
      (sample := sample) (t := t)
      (Realized := Realized)
      (SourceMoment := SourceMoment)
      (SameSampleMoment := SameSampleMoment)
      (MartingaleMeanNonpos := MartingaleMeanNonpos)
      (MismatchBudget := MismatchBudget)
      (SquareNoiseBudget := SquareNoiseBudget)
      (CanonicalMeanBudget := CanonicalMeanBudget)
      (EnvelopeWithBudget := EnvelopeWithBudget)
      (PathwiseEnvelope := PathwiseEnvelope)
      (sameQueryVariance := sameQueryVariance)
      (additiveVariance := additiveVariance)
      hrealized
      (hsource_of_smooth hrealized hgrad_lip hgrad_meas)
      (hsameSample_of_indep hrealized hdelta_indep)
      hmart
      hsquare hpath hmean henvelope


-- Generalization plan (G0):
-- concept/name: generated realization to gap descent envelope through
--   same-sample mixed-center guards; orig was
--   GeneratedGapDescentEnvelope_of_generated_oracle_realization_mixed_center,
--   renamed to expose the reusable guard-assembly proof boundary while
--   dropping theorem numbers and setup-field names.
-- generality used: arbitrary generated sample type and finite horizon;
--   realization, source-moment, same-sample independence, same-sample moment,
--   martingale, indexed primal-budget envelope, and descent envelope are
--   abstract stochastic-optimization contracts. No measure,
--   Hilbert, convexity, smoothness, or finite-dimensional structure is used by
--   this assembly step.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   generated-query mirror-descent proofs after a generated oracle realization
--   and source residual moment have been established, before converting an
--   indexed primal-noise pathwise envelope into the integrable gap descent
--   envelope; only the guard predicates and indexed noise-budget formula
--   change.
-- counterargument checked: this is not the lower pathwise envelope theorem or
--   the absolute-envelope scaling lemma; it packages the recurring
--   same-sample-independence-to-moment bridge followed by guarded
--   indexed-envelope construction and descent-envelope consumption. It is not
--   a formula-equality wrapper.
-- coverage search: searched SOptLib/Staging/source for "generated gap descent
--   envelope", "same sample guards", "indexed primal budget", and "realization
--   mixed center". Closest hits were
--   `generatedGapDescentEnvelope_of_realization_le` and
--   `expectedGapWithPrimalBudget_of_fixedDomainComplete_sameSampleGuards`;
--   both are partial because the former only restricts a longer realization
--   and the latter proves an expected-gap budget with completion/output
--   rewriting rather than the direct generated descent envelope.
-- minimal hypotheses: all setup fields were reduced to the contracts consumed
--   by the proof; same-sample independence is used only through the supplied
--   moment-construction hypothesis, and the concrete mixed-center budget is a
--   caller-supplied indexed `noiseBudget`.

/-- Same-sample guarded realization supplies a generated gap descent envelope.

If a realized generated stream has the source residual moment guard,
same-sample independence supplies the corresponding moment package, those
guards build an indexed primal-budget envelope, and indexed primal-budget
envelopes imply the descent envelope, then the generated stream satisfies the
descent envelope at the reporting horizon.

Layer: Layer1 | Gap: Level 1 (same-sample guarded generated descent envelope assembly)
Proof: derive the same-sample moment guard from realization and independence,
  obtain the indexed primal-budget envelope from the guarded envelope supplier,
  and invoke the descent-envelope consumer at the resulting noise budget.
Source: stochastic generated-oracle guard assembly and indexed primal-noise
  envelope bookkeeping for saddle-gap descent proofs
Used in: stochastic accelerated primal-dual generated saddle-gap integrability
  after mixed-center same-sample oracle guards and martingale cancellation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem generated_gap_descent_envelope_of_realization_same_sample_guards
    {Sample : Type*}
    (sample : Sample) (t : ℕ)
    (Realized SourceMoment SameSampleIndependent SameSampleMoment
      MartingaleMeanNonpos : Sample → ℕ → Prop)
    (PrimalBudgetEnvelope : Sample → ℕ → (ℕ → ℝ) → Prop)
    (Envelope : Sample → ℕ → Prop)
    (noiseBudget : (ℕ → ℝ) → ℕ → ℝ)
    (hrealized : Realized sample t)
    (hsource : SourceMoment sample t)
    (hindep : SameSampleIndependent sample t)
    (hmart : MartingaleMeanNonpos sample t)
    (hsameSampleMoment :
      Realized sample t → SameSampleIndependent sample t → SameSampleMoment sample t)
    (hguardedEnvelope :
      Realized sample t → SourceMoment sample t → SameSampleMoment sample t →
        MartingaleMeanNonpos sample t →
          ∃ M : ℕ → ℝ, PrimalBudgetEnvelope sample t (noiseBudget M))
    (hdescent :
      ∀ SX : ℕ → ℝ, PrimalBudgetEnvelope sample t SX → Envelope sample t) :
    Envelope sample t := by
  have hmoment : SameSampleMoment sample t :=
    hsameSampleMoment hrealized hindep
  rcases hguardedEnvelope hrealized hsource hmoment hmart with
    ⟨M, henv⟩
  exact hdescent (noiseBudget M) henv


-- Generalization plan (G0):
-- concept/name: finite-horizon generated-oracle realization prefix to gap
--   descent envelope; orig was
--   GeneratedGapDescentEnvelope_of_fixedDomainComplete_mixed_center, renamed to
--   describe the reusable prefix-realization bridge rather than the
--   paper-local completion and mixed-center guard assembly.
-- generality used: arbitrary outcome, query, and oracle-sample types; no
--   measure, Hilbert, convexity, smoothness, or finite-dimensional hypotheses
--   are used. The only concrete stochastic-optimization contract retained is
--   `generatedOracleRealization`, because the proof uses its finite-window
--   one-based horizon shape.
-- portable call pattern: stochastic accelerated primal-dual, stochastic
--   mirror-prox, and generated-query mirror-descent proofs after a source run
--   has produced a generated oracle realization through any horizon `T`
--   covering `t`, and before a generated-stream envelope theorem is called at
--   horizon `t`; source moment, independence, martingale, and envelope
--   predicates vary.
-- counterargument checked: this is not the underlying gap envelope definition
--   or expected-gap consumer already staged; it packages the recurring
--   realization-prefix restriction and guarded generated-envelope call. The
--   statement is intentionally not a formula-equality wrapper.
-- coverage search: searched for fixed-domain completion, generated envelope,
--   realization prefix, Finset.Icc monotonicity, and completion same-sample
--   guards. Closest hits were `generatedOracleRealization`,
--   `generatedOracleRealization_of_state_query_sample_eq`, and
--   `expectedGapWithPrimalBudget_of_fixedDomainComplete_sameSampleGuards`;
--   all are partial, and none returns the generated gap envelope directly from
--   a successor-horizon realization and the guard consumer.
-- minimal hypotheses: the algorithm-specific completion object is reduced to
--   a horizon-covering `generatedOracleRealization`; all remaining stochastic
--   guard assumptions are pointwise contracts at the reporting horizon.

/-- A longer generated-oracle realization supplies a guarded gap envelope.

If a source run realizes a generated oracle stream through a horizon `T` with
`t ≤ T`, then the same realization contract holds through `t`.  Any generated
gap-envelope theorem whose remaining hypotheses are source-moment, same-sample
independence, and martingale guards can therefore be invoked at the reporting
horizon.

Layer: Layer1 | Gap: Level 1 (realization-prefix generated gap envelope assembly)
Proof: restrict the generated-oracle realization from `Icc 1 T` to `Icc 1 t`
  using natural-number monotonicity, then apply the supplied
  generated-envelope consumer.
Source: stochastic generated-oracle realization contracts and Mathlib finite
  closed intervals over natural numbers
Used in: stochastic accelerated primal-dual generated gap integrability after a
  longer generated-oracle realization and same-sample guard assembly
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem generatedGapDescentEnvelope_of_realization_le
    {Ω E Y : Type*} {X : Set E}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → E}
    {oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y}
    (t T : ℕ)
    (SourceMoment SameSampleIndependent MartingaleMeanNonpos Envelope :
      (ℕ → Ω → Y) → ℕ → Prop)
    (hT : t ≤ T)
    (hrealize_full : generatedOracleRealization X sample query oracleSample T)
    (hsource : SourceMoment sample t)
    (hindep : SameSampleIndependent sample t)
    (hmart : MartingaleMeanNonpos sample t)
    (henvelope :
      generatedOracleRealization X sample query oracleSample t →
        SourceMoment sample t →
        SameSampleIndependent sample t →
        MartingaleMeanNonpos sample t →
        Envelope sample t) :
    Envelope sample t := by
  have hrealize_t : generatedOracleRealization X sample query oracleSample t := by
    intro i hi ω
    have hi_full : i ∈ Finset.Icc 1 T :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
        Nat.le_trans (Finset.mem_Icc.mp hi).2 hT⟩
    exact hrealize_full i hi_full ω
  exact henvelope hrealize_t hsource hindep hmart


-- Generalization plan (G0):
-- concept/name: twoBlockWeightedBregmanBoundary_eq_of_eq_on_Icc_succ; orig was
--   algorithm43FixedDomainBTermOfComplete_eq_generatedBTerm. The concept is
--   finite-window transport of a two-block weighted Bregman boundary observable
--   through equality of the underlying product-state stream on the current and
--   successor indices.
-- generality used: arbitrary outcome and block-state types; scalar schedules
--   and block Bregman kernels are explicit functions; no measure,
--   measurability, independence, integrability, convexity, topology, algebraic
--   block structure, or finite-dimensional assumptions are used.
-- portable call pattern: completed fixed-domain stochastic primal-dual runs,
--   generated-query mirror-prox runs, and block mirror-descent recursions can
--   call this after proving iterate-stream equality on `Icc 1 (t+1)`; the
--   process construction and equality proof change while the Bregman boundary
--   transport conclusion stays the same.
-- counterargument checked: this is a short `Finset.sum_congr` proof, but it is
--   not only paper traceability because callers repeatedly need to transport a
--   named adjacent-index Bregman boundary across generated/completed process
--   representations. It is not a pure wrapper around Mathlib `Finset.sum_congr`
--   because it packages the `i` and `i+1` interval obligations for the named
--   two-block boundary formula.
-- coverage search: searched catalog/project tokens `BTerm`,
--   `twoBlockWeightedBregmanBoundary`, `sum_congr`, `Icc succ`, and
--   `sequence transport`; relevant hits were
--   `twoBlockWeightedBregmanBoundary`,
--   `twoBlockWeightedBregmanBoundary_def`, `sum_Icc_sub_succ`, and generic
--   telescope/weighted-sum lemmas. Coverage is partial: existing entries name
--   the boundary formula or telescope scalar sums, but none transport this
--   two-block adjacent finite-window boundary across sequence equality on the
--   successor horizon.
-- minimal hypotheses: all already minimal; the theorem needs only equality of
--   the two streams on `Finset.Icc 1 (t + 1)` at the fixed outcome.



/-- A two-block weighted Bregman boundary is invariant under stream equality on
the successor horizon.

The summand over `i ∈ Icc 1 t` reads both `zSeq i` and `zSeq (i+1)`, so equality
on `Icc 1 (t+1)` is exactly enough to transport the complete boundary sum.

Layer: Layer1 | Gap: Level 0 (two-block Bregman boundary stream transport)
Proof: apply `Finset.sum_congr`; interval arithmetic turns each summand index
  into current and successor membership in `Icc 1 (t+1)`, and the stream
  equality rewrites both Bregman differences.
Source: Mathlib finite interval membership and finite-sum congruence APIs
Used in: stochastic accelerated primal-dual completed-process Bregman boundary
  transport before generated-process gap-envelope assembly
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem twoBlockWeightedBregmanBoundary_eq_of_eq_on_Icc_succ
    {Ω X Y : Type*}
    (gamma eta tau : ℕ → ℝ)
    (VX : X → X → ℝ) (VY : Y → Y → ℝ)
    (zSeq zSeq' : ℕ → Ω → X × Y)
    (t : ℕ) (z : X × Y) (ω : Ω)
    (hseq : ∀ i, i ∈ Finset.Icc 1 (t + 1) → zSeq i ω = zSeq' i ω) :
    twoBlockWeightedBregmanBoundary gamma eta tau VX VY zSeq t z ω =
      twoBlockWeightedBregmanBoundary gamma eta tau VX VY zSeq' t z ω := by
  classical
  unfold twoBlockWeightedBregmanBoundary
  apply Finset.sum_congr rfl
  intro i hi_mem
  have hi_bounds := Finset.mem_Icc.mp hi_mem
  have hi_i : i ∈ Finset.Icc 1 (t + 1) :=
    Finset.mem_Icc.mpr ⟨hi_bounds.1, Nat.le_trans hi_bounds.2 (Nat.le_succ t)⟩
  have hi_next : i + 1 ∈ Finset.Icc 1 (t + 1) :=
    Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le i),
      Nat.succ_le_succ hi_bounds.2⟩
  simp [hseq i hi_i, hseq (i + 1) hi_next]


-- Generalization plan (G0):
-- concept/name: twoBlockStochasticLambdaTerm_eq_of_eq_at_succ_and_delta; orig
--   was algorithm43FixedDomainLambdaTermOfComplete_eq_LambdaTerm. The concept
--   is transport of a named two-block Lambda residual through equality of the
--   current iterate, successor iterate, and current two-block residual.
-- generality used: two arbitrary real Hilbert blocks with
--   `[NormedAddCommGroup]` and `[InnerProductSpace ℝ]`; scalar schedules and
--   acceleration parameters are explicit. No measure, filtration,
--   measurability, independence, integrability, convexity, smoothness, oracle
--   law, topology beyond the Hilbert norm, or finite-dimensional assumption is
--   used.
-- portable call pattern: completed fixed-domain stochastic primal-dual runs,
--   generated-query mirror-prox runs, and block mirror-descent residual
--   assemblies can call this after proving two process representations agree
--   at the adjacent states and residual index; the process construction and
--   equality proofs change while the Lambda residual equality conclusion stays
--   the same.
-- counterargument checked: the proof is a congruence step, but it is not only
--   paper-local traceability because the named Lambda residual is already a
--   reusable SOptLib model object and this theorem packages the recurring
--   adjacent-index transport obligations for that object. It is not covered by
--   Mathlib congruence lemmas, which do not know the Lambda residual's
--   current/successor/delta dependency shape.
-- coverage search: searched project/catalog tokens `twoBlockStochasticLambdaTerm`,
--   `LambdaTerm`, `eq_of_eq`, `zSeq delta`, and `completed process Lambda`.
--   Existing hits define the deterministic and process-valued Lambda residuals
--   and provide a comparison-state subtraction lemma, but no theorem transports
--   the residual across equality of the underlying stream and residual pair.
--   LeanSearch for function equality over norm-square and inner-product
--   expressions returned primitive inner-product/norm facts such as
--   `real_inner_self_eq_norm_sq`, not this named stochastic-optimization
--   transport statement.
-- minimal hypotheses: all already minimal; only the three pointwise equalities
--   for data actually read by the residual at index `i` are required.


/-- A two-block stochastic Lambda residual is invariant under equality of the
current state, successor state, and current residual pair.

The one-step Lambda residual reads only `zSeq i`, `zSeq (i+1)`, and `delta i`.
Pointwise equality at exactly those three positions is therefore sufficient to
transport the residual between two process representations.

Layer: Layer1 | Gap: Level 0 (two-block Lambda residual stream transport)
Proof: unfold the named Lambda residual and rewrite the current iterate,
  successor iterate, and residual-pair equalities.
Source: Mathlib equality rewriting for real Hilbert-space norm and
  inner-product expressions
Used in: stochastic accelerated primal-dual completed-process Lambda residual
  transport before generated-process gap-envelope assembly
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem twoBlockStochasticLambdaTerm_eq_of_eq_at_succ_and_delta
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (gamma eta tau : ℕ → ℝ) (p q : ℝ)
    (zSeq zSeq' : ℕ → E × F) (delta delta' : ℕ → E × F)
    (i : ℕ) (z : E × F)
    (hz_i : zSeq i = zSeq' i)
    (hz_next : zSeq (i + 1) = zSeq' (i + 1))
    (hdelta : delta i = delta' i) :
    twoBlockStochasticLambdaTerm gamma eta tau p q zSeq delta i z =
      twoBlockStochasticLambdaTerm gamma eta tau p q zSeq' delta' i z := by
  simp [twoBlockStochasticLambdaTerm, hz_i, hz_next, hdelta]

end SOptLib



-- Batch 13 promoted staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: partialProcessStateOfComplete_eq_generatedProcess_of_init_succ;
--   orig was algorithm43FixedDomainStateOfComplete_eq_generatedAxExtensionProcess.
--   The concept is finite-horizon state transport from a completed
--   option-valued partial process to a total generated recursive process.
-- generality used: arbitrary outcome and state types, an arbitrary state
--   invariant, a total generated process, and a pointwise recursive step; no
--   measure, measurability, independence, integrability, algebraic structure,
--   convexity, topology, or finite-dimensional assumptions.
-- portable call pattern: fixed-domain oracle completions, generated-query
--   mirror-prox runs, and stochastic-gradient processes with partial source
--   domains can call this after proving initial-state agreement and one-step
--   agreement; only the state invariant, generated step, and process equations
--   change.
-- counterargument checked: this is not only paper-local traceability because
--   it lifts the already staged one-step completed-process transport to a full
--   finite-horizon induction. Existing recursive-process lemmas cover total
--   processes or component projections, but not selected states from an
--   Option-valued completed process with a one-based/zero-based index shift.
-- coverage search: searched project tokens `partialProcessStateOfComplete`,
--   `generated process`, `recursive-process transport`, and `state equality`;
--   relevant hits were `partialProcessStateOfComplete_succ_eq_generatedStep`,
--   `generatedExtensionProcess_succ`, and recursive-process component
--   transports. These are partial: none proves the finite-horizon completed
--   state equals the total generated process at index `i - 1`.
-- minimal hypotheses: all already minimal; the theorem uses only the initial
--   selected-state equality, the completed-process successor equality, and the
--   total generated-process successor equality at the fixed outcome.



/-- A completed partial process agrees with a total generated process on a finite horizon.

If the selected state at one-based time `1` agrees with the zero-indexed
generated process, and every completed successor step agrees with the same
step used by the generated process, then the selected state at one-based time
`i` is the generated-process state at index `i - 1`.

Layer: Layer1 | Gap: Level 1 (completed partial-process finite-horizon transport)
Proof: strong induction on the one-based time. The base case uses the supplied
  initial equality; the successor case rewrites both recursions through the
  shared step and applies the induction hypothesis to the predecessor state.
Source: stochastic approximation partial-process semantics, Mathlib finite
  interval indexing, natural-number subtraction, and recursive-process APIs
Used in: stochastic accelerated primal-dual fixed-domain completion transport
  to a generated oracle-extension state process
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem partialProcessStateOfComplete_eq_generatedProcess_of_init_succ
    {Ω State : Type*}
    (state? : ℕ → Ω → Option State)
    (stateInvariant : State → Prop)
    (generatedProcess : ℕ → Ω → State)
    (step : (i : ℕ) → 1 ≤ i → State → Ω → State)
    (T i : ℕ)
    (hcomplete : finiteHorizonOptionProcessComplete state? stateInvariant T)
    (hi : i ∈ Finset.Icc 1 T)
    (ω : Ω)
    (hinit :
      ∀ hi_one : 1 ∈ Finset.Icc 1 T,
        partialProcessStateOfComplete state? stateInvariant T 1 hcomplete hi_one ω =
          generatedProcess 0 ω)
    (hselected_succ :
      ∀ (j : ℕ) (hj : j ∈ Finset.Icc 1 T)
          (hj_next : j + 1 ∈ Finset.Icc 1 T) (hj_pos : 1 ≤ j),
        partialProcessStateOfComplete state? stateInvariant T (j + 1) hcomplete hj_next ω =
          step j hj_pos
            (partialProcessStateOfComplete state? stateInvariant T j hcomplete hj ω) ω)
    (hgenerated_succ :
      ∀ k : ℕ,
        generatedProcess (k + 1) ω =
          step (k + 1) (Nat.succ_pos k) (generatedProcess k ω) ω) :
    partialProcessStateOfComplete state? stateInvariant T i hcomplete hi ω =
      generatedProcess (i - 1) ω := by
  classical
  induction i using Nat.strong_induction_on with
  | h i ih =>
      rcases Finset.mem_Icc.mp hi with ⟨hi_pos, hiT⟩
      cases i with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              simpa using hinit hi
          | succ j =>
              let iPrev := Nat.succ j
              have hiPrev : iPrev ∈ Finset.Icc 1 T :=
                Finset.mem_Icc.mpr ⟨by omega, by omega⟩
              have hi_next : iPrev + 1 ∈ Finset.Icc 1 T := by
                simpa [iPrev] using hi
              have hprev :
                  partialProcessStateOfComplete state? stateInvariant T iPrev hcomplete
                      hiPrev ω =
                    generatedProcess (iPrev - 1) ω :=
                ih iPrev (by omega) hiPrev
              calc
                partialProcessStateOfComplete state? stateInvariant T
                    (Nat.succ (Nat.succ j)) hcomplete hi ω =
                    step iPrev (by omega)
                      (partialProcessStateOfComplete state? stateInvariant T iPrev
                        hcomplete hiPrev ω) ω := by
                      simpa [iPrev] using
                        hselected_succ iPrev hiPrev hi_next (by omega)
                _ =
                    step (j + 1) (Nat.succ_pos j) (generatedProcess j ω) ω := by
                      have hprev' :
                          partialProcessStateOfComplete state? stateInvariant T iPrev
                              hcomplete hiPrev ω =
                            generatedProcess j ω := by
                        simpa [iPrev] using hprev
                      simpa [iPrev] using congrArg
                        (fun st => step iPrev (by omega) st ω) hprev'
                _ =
                    generatedProcess ((Nat.succ (Nat.succ j)) - 1) ω := by
                      simpa [Nat.succ_eq_add_one] using (hgenerated_succ j).symm


-- Generalization plan (G0):
-- concept/name: completedPartialProcess_state_succ_eq_generated_step; orig was
--   algorithm43FixedDomainStateOfComplete_succ_eq_generated_stepOfComplete.
--   The concept is successor transport for a completed finite-horizon state
--   family after the carrier-domain sample call has been packaged as a named
--   generated sample stream.
-- generality used: arbitrary outcome, state, query, and sample types; an
--   arbitrary carrier set for subtype-packaged samples; `[Zero Sample]` only
--   because the generated sample stream is totalized outside the completed
--   horizon. No measure, measurability, independence, integrability,
--   algebraic geometry, convexity, topology, or finite-dimensional structure
--   is used.
-- portable call pattern: fixed-domain stochastic oracle completions,
--   generated-query mirror-prox recursions, and constrained stochastic
--   gradient methods can call this after proving that their completed state
--   successor uses the carrier-domain oracle sample; the completed state
--   family, query projection, carrier, sampled oracle, and step rule change
--   while the conclusion shape stays the same.
-- counterargument checked: the proof is a short rewrite, but it is not merely
--   paper-local traceability because it composes a completed-state successor
--   equation with the named generated sample stream API. It is not a duplicate
--   of `partialProcessStateOfComplete_succ_eq_generatedStep`, which proves the
--   raw successor from an `Option` process rather than normalizing a completed
--   state family through `completedPartialProcessGeneratedOracleSample`.
-- coverage search: searched project/catalog tokens `completedPartialProcess`,
--   `generated sample`, `state successor`, and `generatedStep`; relevant hits
--   were `partialProcessStateOfComplete_succ_eq_generatedStep` and
--   `completedPartialProcessGeneratedOracleSample_of_mem`. LeanSearch for
--   finite-horizon process successor transport returned only generic stream
--   and natural-recursion lemmas, not this carrier-sample normalization.
-- minimal hypotheses: all already minimal; the theorem needs only on-horizon
--   membership for the current and successor times, pointwise query
--   feasibility, and the raw completed-state successor equality.



/-- A completed state successor rewrites through the induced generated sample stream.

If a completed finite-horizon state family advances by a step driven by the
carrier-domain sample at the current state's feasible query, then the same
successor is the step driven by the completed process's generated sample
stream at that time.

Layer: Layer1 | Gap: Level 1 (completed-state generated-sample successor transport)
Proof: unfold the on-horizon branch of
  `completedPartialProcessGeneratedOracleSample` using the current-time
  interval membership, then rewrite the supplied raw successor equality.
Source: stochastic approximation finite-horizon process semantics, Mathlib
  finite interval membership, subtype packaging, and `if_pos` simplification APIs
Used in: stochastic accelerated primal-dual completed fixed-domain state
  recursion transported to the generated oracle-sample stream
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem completedPartialProcess_state_succ_eq_generated_step
    {Ω State Query Sample : Type*} [Zero Sample] {C : Set Query}
    (T i : ℕ)
    (completedState : ∀ j, j ∈ Finset.Icc 1 T → Ω → State)
    (query : State → Query)
    (hquery_mem :
      ∀ j, ∀ hj : j ∈ Finset.Icc 1 T, ∀ ω : Ω,
        query (completedState j hj ω) ∈ C)
    (sample : ℕ → {x : Query // x ∈ C} → Ω → Sample)
    (step : ℕ → State → Sample → Ω → State)
    (hi : i ∈ Finset.Icc 1 T) (hi_next : i + 1 ∈ Finset.Icc 1 T)
    (ω : Ω)
    (hsucc :
      completedState (i + 1) hi_next ω =
        step i (completedState i hi ω)
          (sample i
            ⟨query (completedState i hi ω), hquery_mem i hi ω⟩ ω) ω) :
    completedState (i + 1) hi_next ω =
      step i (completedState i hi ω)
        (completedPartialProcessGeneratedOracleSample T completedState query
          hquery_mem sample i ω) ω := by
  simpa [completedPartialProcessGeneratedOracleSample, hi] using hsucc


-- Generalization plan (G0):
-- concept/name: partialProcessStateOfComplete_succ_eq_generatedStep; orig was
--   algorithm43FixedDomainStateOfComplete_succ_eq_stepFromGeneratedAx. The
--   concept is successor transport for a completed option-valued process whose
--   partial transition realizes a total generated step at a feasible state
--   query.
-- generality used: arbitrary outcome, state, query, and sample types; an
--   arbitrary carrier set for subtype-packaged samples; no measure,
--   measurability, independence, integrability, algebraic structure,
--   convexity, topology, or finite-dimensional assumptions.
-- portable call pattern: fixed-domain stochastic oracle recursions,
--   generated-query mirror-prox processes, and constrained stochastic-gradient
--   methods can use the same theorem when a completed partial process is
--   transported to a total generated process; only the state invariant, query,
--   sample, partial transition, and generated step change.
-- counterargument checked: the proof is short and performs option-state
--   bookkeeping, but it is not just paper-local traceability because it
--   composes the reusable completed-state selector with a pointwise successor
--   bind equation and a partial-step realization theorem. Existing total
--   recursive-process transport lemmas do not cover completion-selected states
--   from an `Option` process.
-- coverage search: searched project tokens `partialProcessStateOfComplete`,
--   `recursive_process_components`, `stepFromGeneratedAx`, and
--   `completed partial process generated step`; existing hits cover the
--   completed-state selector, generated sample streams, residual streams, and
--   total recursive process component transport, but no theorem states this
--   completed option-process successor-to-generated-step bridge.
-- minimal hypotheses: all already minimal; the theorem is pathwise and needs
--   only the current/successor completion certificates, one successor equation,
--   and one pointwise partial-step realization at the selected state.



/-- A completed option-valued process successor is the realized generated step.

If the selected current and successor states come from a completed partial
process, the process successor unfolds through a partial transition, and that
partial transition realizes a total generated step at the selected state's
feasible query, then the completed successor state is exactly that generated
step.

Layer: Layer1 | Gap: Level 1 (completed partial-process successor transport)
Proof: use the completed-state specification at the current and successor
  times, rewrite the pointwise successor equation through `Option.bind`, insert
  the partial-step realization, and cancel `Option.some`.
Source: stochastic approximation partial-process semantics, Mathlib `Option`
  bind/cancellation APIs, and finite natural-time interval indexing
Used in: stochastic accelerated primal-dual fixed-domain partial recursion
  transport to a generated-query total state step
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem partialProcessStateOfComplete_succ_eq_generatedStep
    {Ω State Query Sample : Type*} {C : Set Query}
    (state? : ℕ → Ω → Option State)
    (stateInvariant : State → Prop)
    (query : State → Query)
    (sample : ℕ → {x : Query // x ∈ C} → Ω → Sample)
    (step? : ℕ → State → Ω → Option State)
    (generatedStep : ℕ → Sample → State → Ω → State)
    (hquery_mem : ∀ st : State, stateInvariant st → query st ∈ C)
    (T i : ℕ)
    (hcomplete : finiteHorizonOptionProcessComplete state? stateInvariant T)
    (hi : i ∈ Finset.Icc 1 T)
    (hi_next : i + 1 ∈ Finset.Icc 1 T)
    (ω : Ω)
    (hsucc :
      state? (i + 1) ω = (state? i ω).bind (fun st => step? i st ω))
    (hstep :
      ∀ st : State, ∀ hst : stateInvariant st,
        step? i st ω =
          some (generatedStep i
            (sample i ⟨query st, hquery_mem st hst⟩ ω) st ω)) :
    let st := partialProcessStateOfComplete state? stateInvariant T i hcomplete hi ω
    let hst := (partialProcessStateOfComplete_spec state? stateInvariant T i hcomplete hi ω).2
    partialProcessStateOfComplete state? stateInvariant T (i + 1) hcomplete hi_next ω =
      generatedStep i (sample i ⟨query st, hquery_mem st hst⟩ ω) st ω := by
  classical
  let st := partialProcessStateOfComplete state? stateInvariant T i hcomplete hi ω
  let stNext := partialProcessStateOfComplete state? stateInvariant T (i + 1) hcomplete hi_next ω
  let hst := (partialProcessStateOfComplete_spec state? stateInvariant T i hcomplete hi ω).2
  have hcur :
      state? i ω = some st :=
    (partialProcessStateOfComplete_spec state? stateInvariant T i hcomplete hi ω).1
  have hnext :
      state? (i + 1) ω = some stNext :=
    (partialProcessStateOfComplete_spec state? stateInvariant T (i + 1) hcomplete hi_next ω).1
  have hgenerated :
      state? (i + 1) ω =
        some (generatedStep i (sample i ⟨query st, hquery_mem st hst⟩ ω) st ω) := by
    rw [hsucc, hcur]
    exact hstep st hst
  have hsome_eq :
      some stNext =
        some (generatedStep i (sample i ⟨query st, hquery_mem st hst⟩ ω) st ω) :=
    hnext.symm.trans hgenerated
  exact Option.some.inj hsome_eq


open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: accelerated primal smooth aggregate bound; orig was
--   deterministic_apd_hatf_aggregate_bound_core.
-- generality used: arbitrary complete real inner-product normed additive group, a
--   real-valued objective convex on a carrier, one pointwise gradient at the
--   midpoint, a pointwise smoothness upper bound for the averaged endpoint, and
--   two affine APD displacement identities; no measure, filtration, oracle law,
--   finite-dimensionality, or algorithm setup fields.
-- portable call pattern: accelerated primal-dual, accelerated gradient, and
--   smooth composite mirror/proximal proofs call this after forming an
--   inverse-scale output average and a midpoint/search point; the carrier,
--   objective, selected gradient, step points, beta, and smoothness constant
--   vary while the aggregate descent inequality stays the same.
-- counterargument checked: this is not just paper traceability or a pure
--   caller-side expression because it composes two convex support inequalities,
--   a smooth quadratic upper model, and the accelerated midpoint identities
--   into the canonical two-point APD recurrence. Mathlib/SOptLib provide
--   Jensen, support, smoothness, and affine-identity ingredients, but not this
--   aggregate inequality.
-- coverage search: queried project catalog and symbols for "smooth convex
--   aggregate average midpoint bound" and LeanSearch for "smooth convex two
--   point aggregate inequality midpoint average accelerated gradient"; top
--   hits were `ConvexOn.map_sum_le`, `ConvexOn.map_add_sum_le`,
--   `SOptLib.ConvexOn.supporting_hyperplane_of_hasGradientAt`,
--   `Convex.carrier_smooth_quadratic_upper_bound`,
--   `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`, and
--   `inverse_scale_average_midpoint_displacement_identities`; coverage is
--   partial, not a duplicate of the aggregate statement.
-- minimal hypotheses: drops finite dimension, stochastic data,
--   and `xBarNext ∈ X`; the latter is needed by callers only to prove the
--   pointwise smoothness premise, not by this aggregate algebra itself.

/-- A smooth convex objective satisfies the accelerated primal aggregate bound.

At an inverse-scale APD midpoint, convex support at the previous average and
target point controls the midpoint value, while the smooth quadratic model
controls the next average. The two APD displacement identities combine these
into the usual two-point accelerated primal descent inequality.

Layer: Layer1 | Gap: Level 1 (accelerated smooth primal aggregate inequality)
Proof: apply the convex supporting-hyperplane inequality at the midpoint for
  the previous average and target, scale by `β - 1`, insert the smooth upper
  model at the next average, and rewrite the midpoint/step inner products with
  the supplied APD displacement identities.
Source: Mathlib convex support inequalities, real Hilbert-space inner-product
  algebra, and smooth first-order quadratic upper models
Used in: stochastic accelerated primal-dual smooth primal objective aggregate
  descent after midpoint and output-average identities are established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem apd_primal_smooth_aggregate_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {f : E → ℝ} {grad xBarPrev xPrev xNext xBarNext xMid xTarget : E}
    {β L : ℝ}
    (hβ : 1 ≤ β)
    (hfconv : ConvexOn ℝ X f)
    (hxMid : xMid ∈ X) (hxBarPrev : xBarPrev ∈ X) (hxTarget : xTarget ∈ X)
    (hgrad : HasGradientAt f grad xMid)
    (hsmooth :
      f xBarNext - f xMid - ⟪grad, xBarNext - xMid⟫_ℝ ≤
        (L / 2) * ‖xBarNext - xMid‖ ^ 2)
    (hbar_disp : xBarNext - xMid = β⁻¹ • (xNext - xPrev))
    (hmid_comb :
      (β - 1) • (xBarPrev - xMid) + (xTarget - xMid) = xTarget - xPrev) :
    β * f xBarNext - (β - 1) * f xBarPrev - f xTarget ≤
      ⟪grad, xNext - xTarget⟫_ℝ + (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 := by
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hβne : β ≠ 0 := ne_of_gt hβpos
  have hβm1 : 0 ≤ β - 1 := sub_nonneg.mpr hβ
  have hsupport_bar :
      f xMid + ⟪grad, xBarPrev - xMid⟫_ℝ ≤ f xBarPrev := by
    simpa [InnerProductSpace.toDual_apply_apply] using
      ConvexOn.supporting_hyperplane_of_hasGradientAt
        hfconv hxMid hxBarPrev hgrad.hasFDerivAt
  have hsupport_target :
      f xMid + ⟪grad, xTarget - xMid⟫_ℝ ≤ f xTarget := by
    simpa [InnerProductSpace.toDual_apply_apply] using
      ConvexOn.supporting_hyperplane_of_hasGradientAt
        hfconv hxMid hxTarget hgrad.hasFDerivAt
  have hsupport_bar_scaled :
      (β - 1) * (f xMid + ⟪grad, xBarPrev - xMid⟫_ℝ) ≤
        (β - 1) * f xBarPrev :=
    mul_le_mul_of_nonneg_left hsupport_bar hβm1
  have hsupport_sum :
      (β - 1) * (f xMid + ⟪grad, xBarPrev - xMid⟫_ℝ) +
          (f xMid + ⟪grad, xTarget - xMid⟫_ℝ) ≤
        (β - 1) * f xBarPrev + f xTarget := by
    linarith
  have hinner_mid :
      (β - 1) * ⟪grad, xBarPrev - xMid⟫_ℝ +
          ⟪grad, xTarget - xMid⟫_ℝ =
        ⟪grad, xTarget - xPrev⟫_ℝ := by
    calc
      (β - 1) * ⟪grad, xBarPrev - xMid⟫_ℝ +
          ⟪grad, xTarget - xMid⟫_ℝ
          = ⟪grad, (β - 1) • (xBarPrev - xMid) + (xTarget - xMid)⟫_ℝ := by
              rw [inner_add_right, real_inner_smul_right]
      _ = ⟪grad, xTarget - xPrev⟫_ℝ := by rw [hmid_comb]
  have hmid_bound :
      β * f xMid + ⟪grad, xTarget - xPrev⟫_ℝ ≤
        (β - 1) * f xBarPrev + f xTarget := by
    nlinarith [hsupport_sum, hinner_mid]
  have hsmooth_le :
      f xBarNext ≤
        f xMid + ⟪grad, xBarNext - xMid⟫_ℝ +
          (L / 2) * ‖xBarNext - xMid‖ ^ 2 := by
    linarith
  have hsmooth_scaled :
      β * f xBarNext ≤
        β * f xMid + ⟪grad, xNext - xPrev⟫_ℝ +
          (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsmooth_le hβnonneg
    have hinner_scaled :
        β * ⟪grad, xBarNext - xMid⟫_ℝ = ⟪grad, xNext - xPrev⟫_ℝ := by
      rw [hbar_disp, real_inner_smul_right]
      field_simp [hβne]
    have hnorm_scaled :
        β * ((L / 2) * ‖xBarNext - xMid‖ ^ 2) =
          (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 := by
      rw [hbar_disp, norm_smul]
      have hinv_nonneg : 0 ≤ β⁻¹ := inv_nonneg.mpr hβnonneg
      rw [Real.norm_of_nonneg hinv_nonneg]
      field_simp [hβne]
    nlinarith [hmul, hinner_scaled, hnorm_scaled]
  have hmid_bound_rearr :
      β * f xMid ≤
        (β - 1) * f xBarPrev + f xTarget + ⟪grad, xPrev - xTarget⟫_ℝ := by
    have hinner_neg :
        ⟪grad, xPrev - xTarget⟫_ℝ = -⟪grad, xTarget - xPrev⟫_ℝ := by
      have hvec : xPrev - xTarget = -(xTarget - xPrev) := by
        abel
      rw [hvec, inner_neg_right]
    nlinarith [hmid_bound, hinner_neg]
  have hcombined :
      β * f xBarNext ≤
        (β - 1) * f xBarPrev + f xTarget +
          ⟪grad, xPrev - xTarget⟫_ℝ +
          ⟪grad, xNext - xPrev⟫_ℝ +
          (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 := by
    nlinarith [hsmooth_scaled, hmid_bound_rearr]
  have hinner_join :
      ⟪grad, xPrev - xTarget⟫_ℝ + ⟪grad, xNext - xPrev⟫_ℝ =
        ⟪grad, xNext - xTarget⟫_ℝ := by
    rw [← inner_add_right]
    congr 1
    abel
  nlinarith [hcombined, hinner_join]


open scoped InnerProductSpace


-- Generalization plan (G0):
-- concept/name: accelerated primal smooth aggregate bound from a deterministic
--   aggregate run; orig was deterministic_apd_hatf_aggregate_bound. The name
--   exposes the run-level smooth primal aggregate proof step without paper
--   `hatf` notation, theorem numbers, or Algorithm42-specific prox fields.
-- generality used: arbitrary real Hilbert-style normed additive group, an
--   arbitrary state type, a deterministic accelerated aggregate run, abstract
--   state projections for current and averaged primal coordinates, one
--   pointwise midpoint formula, pointwise convex membership, pointwise
--   gradient and smoothness hypotheses, and no measure, filtration, oracle,
--   independence, integrability, or finite-dimensional assumptions.
-- portable call pattern: accelerated primal-dual, accelerated gradient, and
--   composite proximal-gradient proofs call this after extracting an
--   inverse-beta averaged-output recurrence from a deterministic run; the
--   state record, carrier, objective, gradient selector, beta schedule, and
--   smoothness constant vary while the scaled aggregate bound stays the same.
-- counterargument checked: the existing
--   `accelerated_primal_dual_smooth_aggregate_bound` covers the analytic core,
--   so this is not restaging that theorem. The new value is the reusable
--   run-level handoff that reads `run.xbar_step`, derives the midpoint
--   displacement identities, and specializes the smooth aggregate inequality.
-- coverage search: checked the catalog/source hits for "aggregate smooth
--   primal accelerated run", `accelerated_primal_dual_smooth_aggregate_bound`,
--   `inverse_scale_average_midpoint_displacement_identities`, and
--   `accelerated_convex_aggregate_gap_bound_of_run`. Coverage is partial:
--   existing entries cover the analytic inequality, affine identities, and
--   dual convex run handoff, but not the primal smooth run handoff.
-- minimal hypotheses: global differentiability/smoothness are reduced to the
--   single pointwise gradient and smoothness premises used at the selected
--   midpoint and next averaged point; `xBarNext ∈ X` is not a theorem
--   hypothesis except insofar as callers use it to prove the smoothness bound.

/-- A deterministic accelerated aggregate run gives the smooth primal aggregate bound.

The theorem reads the inverse-beta averaged primal recurrence from an abstract
deterministic run, combines it with the matching midpoint formula, and applies
the smooth convex accelerated primal aggregate inequality at one time index.

Layer: Layer1 | Gap: Level 1 (accelerated primal smooth aggregate run handoff)
Proof: extract the averaged-coordinate formula from `run.xbar_step`, use the
  inverse-scale midpoint displacement identities, and delegate the analytic
  convex-support and smoothness algebra to
  `accelerated_primal_dual_smooth_aggregate_bound`.
Source: Lan accelerated primal-dual aggregate recurrence algebra, Mathlib
  convex support inequalities, and real Hilbert-space smooth upper models
Used in: accelerated primal-dual smooth primal objective aggregate descent
  after a deterministic averaged-output recurrence is available
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem accelerated_primal_dual_smooth_aggregate_bound_of_run
    {E State : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {initState : State}
    {xbarStep ybarStep : (t : ℕ) → 1 ≤ t → State → State → Prop}
    {X : Set E} {f : E → ℝ} (grad : E → E)
    (run : DeterministicAcceleratedAggregateRun State initState xbarStep ybarStep)
    (xBar x : State → E) (midpoint : (t : ℕ) → 1 ≤ t → State → E)
    (β : ℕ → ℝ) (L : ℝ)
    (hxbarStep :
      ∀ t, ∀ ht : 1 ≤ t, ∀ prev next,
        xbarStep t ht prev next →
          xBar next = (1 - (β t)⁻¹) • xBar prev + (β t)⁻¹ • x next)
    (hfconv : ConvexOn ℝ X f)
    (t : ℕ) (ht : 1 ≤ t)
    (hmidpoint :
      midpoint t ht (run.state t) =
        (1 - (β t)⁻¹) • xBar (run.state t) + (β t)⁻¹ • x (run.state t))
    (hβ : 1 ≤ β t)
    (target : E)
    (hmid_mem : midpoint t ht (run.state t) ∈ X)
    (hxBar_mem : xBar (run.state t) ∈ X)
    (htarget_mem : target ∈ X)
    (hgrad :
      HasFDerivAt f (innerSL ℝ (grad (midpoint t ht (run.state t))))
        (midpoint t ht (run.state t)))
    (hsmooth :
      f (xBar (run.state (t + 1))) - f (midpoint t ht (run.state t)) -
          ⟪grad (midpoint t ht (run.state t)),
            xBar (run.state (t + 1)) - midpoint t ht (run.state t)⟫_ℝ ≤
        (L / 2) * ‖xBar (run.state (t + 1)) - midpoint t ht (run.state t)‖ ^ 2) :
    β t * f (xBar (run.state (t + 1))) -
        (β t - 1) * f (xBar (run.state t)) - f target ≤
      ⟪grad (midpoint t ht (run.state t)), x (run.state (t + 1)) - target⟫_ℝ +
        (L / (2 * β t)) * ‖x (run.state (t + 1)) - x (run.state t)‖ ^ 2 := by
  let beta := β t
  let xBarPrev := xBar (run.state t)
  let xPrev := x (run.state t)
  let xNext := x (run.state (t + 1))
  let xBarNext := xBar (run.state (t + 1))
  let xMid := midpoint t ht (run.state t)
  let gMid := grad xMid
  have hβpos : 0 < beta := lt_of_lt_of_le zero_lt_one (by simpa [beta] using hβ)
  have hβne : beta ≠ 0 := ne_of_gt hβpos
  have hxbar_eq :
      xBarNext = (1 - beta⁻¹) • xBarPrev + beta⁻¹ • xNext := by
    simpa [beta, xBarPrev, xNext, xBarNext] using
      hxbarStep t ht (run.state t) (run.state (t + 1)) (run.xbar_step t ht)
  have hxmid_eq :
      xMid = (1 - beta⁻¹) • xBarPrev + beta⁻¹ • xPrev := by
    simpa [beta, xBarPrev, xPrev, xMid] using hmidpoint
  have hids := apd_average_midpoint_displacement_identities
    (β := beta) (xBarPrev := xBarPrev) (xPrev := xPrev) (xNext := xNext)
    (xBarNext := xBarNext) (xMid := xMid) (xTarget := target)
    hβne hxbar_eq hxmid_eq
  have hcore :=
    apd_primal_smooth_aggregate_bound
      (X := X) (f := f) (grad := gMid)
      (xBarPrev := xBarPrev) (xPrev := xPrev) (xNext := xNext)
      (xBarNext := xBarNext) (xMid := xMid) (xTarget := target)
      (β := beta) (L := L)
      (by simpa [beta] using hβ)
      hfconv
      (by simpa [xMid] using hmid_mem)
      (by simpa [xBarPrev] using hxBar_mem)
      htarget_mem
      (by simpa [xMid, gMid] using hgrad)
      (by simpa [xBarNext, xMid, gMid] using hsmooth)
      hids.1 hids.2.2
  simpa [beta, xBarPrev, xPrev, xNext, xBarNext, xMid, gMid] using hcore


-- Generalization plan (G0):
-- concept/name: accelerated convex aggregate gap bound; orig was
--   deterministic_apd_hatg_aggregate_bound. The name exposes the aggregate
--   proof step while avoiding paper-local hat-g notation and theorem numbers.
-- generality used: arbitrary module over `ℝ`, arbitrary state type, a concrete
--   deterministic accelerated aggregate run, pointwise feasibility for the two
--   dual endpoints, one `ConvexOn ℝ Y g` hypothesis, and no measure,
--   smoothness, oracle, norm, or finite-dimensional assumptions.
-- portable call pattern: accelerated primal-dual and accelerated composite
--   methods can call this after a deterministic averaged-output recurrence;
--   the state record, carrier, objective, and schedule change while the
--   scaled aggregate-gap conclusion is unchanged.
-- counterargument checked: the analytic Jensen step is already covered by
--   `SOptLib.ConvexOn.beta_smul_average_le`, but the run-level statement is not a pure
--   rename: it packages extraction of the positive-time aggregate recurrence
--   from `DeterministicAcceleratedAggregateRun` with the translated gap form.
-- coverage search: checked `convexOn_weighted_average_le_weighted_sum` in
--   `SOptLib/Layer1/Telescope.lean` and `SOptLib.ConvexOn.beta_smul_average_le` in
--   staging. They cover finite Jensen and the scaled two-point convexity step,
--   but not the deterministic aggregate-run handoff used by APD proofs.
-- minimal hypotheses: endpoint membership is pointwise; the target only
--   appears in real gap algebra and does not need feasibility.

/-- A deterministic accelerated dual aggregate recurrence gives the scaled
convex aggregate-gap bound.

For any run whose dual averaged coordinate satisfies the inverse-beta affine
recurrence, convexity of the dual objective turns the recurrence into the
standard accelerated aggregate gap inequality against an arbitrary target.

Layer: Layer1 | Gap: Level 1 (accelerated dual aggregate convexity handoff)
Proof: read the positive-time averaged-coordinate recurrence from the abstract
  deterministic aggregate run, apply the scaled two-point Jensen bridge, and
  rearrange the target gap terms by ordered-ring arithmetic.
Source: Mathlib convex-analysis API for `ConvexOn` and Lan accelerated
  primal-dual aggregate recurrence algebra
Used in: accelerated primal-dual dual aggregate bound from the averaged dual
  output recurrence before the one-step saddle-gap inequality
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem accelerated_convex_aggregate_gap_bound_of_run
    {E State : Type*} [AddCommGroup E] [Module ℝ E]
    {initState : State}
    {xbarStep ybarStep : (t : ℕ) → 1 ≤ t → State → State → Prop}
    {Y : Set E} {g : E → ℝ}
    (run : DeterministicAcceleratedAggregateRun State initState xbarStep ybarStep)
    (yBar y : State → E) (β : ℕ → ℝ)
    (hybarStep :
      ∀ t, ∀ ht : 1 ≤ t, ∀ prev next,
        ybarStep t ht prev next →
          yBar next = (1 - (β t)⁻¹) • yBar prev + (β t)⁻¹ • y next)
    (hg : ConvexOn ℝ Y g)
    (t : ℕ) (ht : 1 ≤ t) (hβ : 1 ≤ β t)
    (hyBar_mem : yBar (run.state t) ∈ Y)
    (hyNext_mem : y (run.state (t + 1)) ∈ Y)
    (target : E) :
    β t * (g (yBar (run.state (t + 1))) - g target) -
        (β t - 1) * (g (yBar (run.state t)) - g target) ≤
      g (y (run.state (t + 1))) - g target := by
  have hybar_eq :
      yBar (run.state (t + 1)) =
        (1 - (β t)⁻¹) • yBar (run.state t) + (β t)⁻¹ • y (run.state (t + 1)) :=
    hybarStep t ht (run.state t) (run.state (t + 1)) (run.ybar_step t ht)
  have hweighted :
      β t * g (yBar (run.state (t + 1))) ≤
        (β t - 1) * g (yBar (run.state t)) + g (y (run.state (t + 1))) :=
    ConvexOn.beta_smul_average_le hg hβ hyBar_mem hyNext_mem hybar_eq
  nlinarith [hweighted]


-- Generalization plan (G0):
-- concept/name: displayedState_eq_generatedProcess_shift; orig was
--   displayed_state_eq_generated_shift. The concept is a warm-started
--   one-based displayed recursive state transported to the corresponding
--   zero-based generated process.
-- generality used: arbitrary outcome, state, and query types with a shared
--   pointwise recursive step; no measure, measurability, independence,
--   integrability, algebraic structure, convexity, topology, or oracle
--   assumptions are used.
-- portable call pattern: accelerated, mirror-prox, stochastic-gradient, and
--   generated-oracle extension proofs can call this when a paper-facing
--   displayed process is initialized at times 0 and 1 while the executable
--   generated process starts at time 0; only the query stream and step
--   equation change.
-- counterargument checked: this is not merely paper-local traceability because
--   the statement exposes the recurring warm-start index shift between two
--   recursive processes. It is not a pure wrapper around a Mathlib sequence
--   shift lemma because the proof composes two distinct successor equations
--   with a one-based step proof.
-- coverage search: searched project tokens `displayed state generated shift`,
--   `recursive process shift`, `generatedProcess`, and LeanSearch query
--   `sequence shifted by one equality generated process displayed state`.
--   Relevant SOptLib hits were recursive-process measurability/component
--   transport lemmas and `partialProcessStateOfComplete_eq_generatedProcess_of_init_succ`;
--   coverage is partial, since none states this total-process warm-start
--   displayed/generated shift.
-- minimal hypotheses: all already minimal; the theorem needs only the two
--   initial alignments and the displayed/generated successor equations at the
--   fixed outcome.



/-- A warm-started displayed recursive process equals the shifted generated process.

If displayed times `0` and `1` both align with generated time `0`, and the
displayed and generated recursions use the same one-based step and query stream,
then displayed time `k` equals generated time `k - 1` for every natural index.

Layer: Layer1 | Gap: Level 1 (warm-start recursive-process index shift)
Proof: split off the two warm-start base indices, then induct on the remaining
  successor index and rewrite both recursions through the shared one-based step.
Source: Mathlib natural-number recursion and subtype-free one-based indexing
  APIs for recursive stochastic-optimization processes
Used in: stochastic accelerated primal-dual displayed-state transport to a
  generated oracle-extension process before pathwise recurrence rewriting
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem displayedState_eq_generatedProcess_shift
    {Ω State Query : Type*}
    (displayedState generatedProcess : ℕ → Ω → State)
    (query : ℕ → Ω → Query)
    (step : (t : ℕ) → 1 ≤ t → Query → State → Ω → State)
    (hdisplayed_zero : ∀ ω, displayedState 0 ω = generatedProcess 0 ω)
    (hdisplayed_one : ∀ ω, displayedState 1 ω = generatedProcess 0 ω)
    (hdisplayed_succ :
      ∀ (t : ℕ) (ht : 1 ≤ t) (ω : Ω),
        displayedState (t + 1) ω =
          step t ht (query t ω) (displayedState t ω) ω)
    (hgenerated_succ :
      ∀ (k : ℕ) (ω : Ω),
        generatedProcess (k + 1) ω =
          step (k + 1) (Nat.succ_pos k) (query (k + 1) ω)
            (generatedProcess k ω) ω)
    (k : ℕ) (ω : Ω) :
    displayedState k ω = generatedProcess (k - 1) ω := by
  cases k with
  | zero =>
      simpa using hdisplayed_zero ω
  | succ k =>
      induction k with
      | zero =>
          simpa using hdisplayed_one ω
      | succ k ih =>
          calc
            displayedState (Nat.succ (Nat.succ k)) ω =
                step (k + 1) (Nat.succ_pos k) (query (k + 1) ω)
                  (displayedState (k + 1) ω) ω := by
                  simpa [Nat.succ_eq_add_one] using
                    hdisplayed_succ (k + 1) (Nat.succ_pos k) ω
            _ =
                step (k + 1) (Nat.succ_pos k) (query (k + 1) ω)
                  (generatedProcess ((k + 1) - 1) ω) ω := by
                  rw [ih]
            _ = generatedProcess (Nat.succ (Nat.succ k) - 1) ω := by
                  simpa [Nat.succ_eq_add_one] using (hgenerated_succ k ω).symm


-- Generalization plan (G0):
-- concept/name: expected gap with an indexed primal budget from an
--   expectation-ready stage-separated boundary; orig was
--   expected_gap_le_Q0StageSeparatedWithPrimalBudget_of_stageSeparated_boundary.
-- generality used: arbitrary mismatch-budget, pathwise-boundary,
--   stage-square-noise, canonical-mean, and expected-gap-bound predicates over
--   indexed real budgets; no measure, probability, Hilbert, convexity,
--   smoothness, oracle, or finite-dimensional structure is used by this
--   proof-composition step.
-- portable call pattern: accelerated primal-dual, mirror-prox, stochastic
--   mirror descent with fresh validation samples, and variance-reduced
--   generated-query proofs after a stage-separated expectation-ready boundary
--   has produced a shared mismatch witness and before an expected-gap consumer
--   is invoked; the concrete boundary predicates and budget formula vary while
--   the existential mismatch-budget expected-gap conclusion stays fixed.
-- counterargument checked: this is not the scalar integration theorem
--   `expectedGap_le_primalBudget_of_scaled_envelope` and not the fixed-domain
--   completion theorem
--   `expectedGapWithPrimalBudget_of_fixedDomainComplete_stageSeparatedBoundary`;
--   it isolates the inner reusable boundary-consumption step. It is not merely
--   a paper traceability wrapper because future stage-separated stochastic
--   proofs can reuse the same witness-preserving transition from boundary
--   components to an expected-gap budget.
-- coverage search: searched source/staging/catalog with direct grep for
--   "expectedGapWithPrimalBudget", "stageSeparatedBoundary",
--   "mismatchBudget", and "expected gap primal budget"; closest hits were
--   `stageSeparatedExpectedGapBoundaryWithLooseMismatch`,
--   `expectedGap_le_primalBudget_of_scaled_envelope`, and
--   `expectedGapWithPrimalBudget_of_fixedDomainComplete_stageSeparatedBoundary`,
--   all partial. LeanSearch for "exists mismatch budget pathwise mean implies
--   expected gap bound" returned unrelated martingale/upcrossing APIs.
-- minimal hypotheses: the source stage boundary is reduced to the four
--   components actually unpacked; the stage-square-noise component is retained
--   as part of the boundary contract but is intentionally unused by the
--   expected-gap consumer, matching the proof boundary in expectation-ready
--   stage-separated arguments.

/-- An expectation-ready stage-separated boundary yields an indexed expected-gap budget.

If a stage-separated boundary provides a shared mismatch witness, a pathwise
gap component, a stage-square-noise component, and a canonical mean component
at the same indexed primal budget, and the pathwise plus canonical mean
components imply the expected-gap bound for any indexed budget, then the
expected-gap bound holds for the boundary's existential mismatch witness.

Layer: Layer1 | Gap: Level 1 (stage-separated expected-gap budget assembly)
Proof: unpack the stage-separated boundary witness, keep the same mismatch
  budget, and apply the expected-gap consumer to the pathwise and canonical
  mean components at the indexed primal budget.
Source: stochastic primal-dual stage-separated descent-envelope algebra and
  elementary existential-witness transport
Used in: stochastic accelerated primal-dual expected saddle-gap proof after an
  expectation-ready stage-separated boundary has been established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem expectedGapWithPrimalBudget_of_stageSeparatedBoundary
    (mismatchBudget : (ℕ → ℝ) → Prop)
    (pathwiseBoundary : Prop)
    (stageNoiseBoundary canonicalMeanBoundary expectedGapBound : (ℕ → ℝ) → Prop)
    (noiseBudget : (ℕ → ℝ) → ℕ → ℝ)
    (hboundary :
      ∃ M : ℕ → ℝ,
        mismatchBudget M ∧
          pathwiseBoundary ∧
            stageNoiseBoundary (noiseBudget M) ∧
              canonicalMeanBoundary (noiseBudget M))
    (hexpected :
      ∀ SX : ℕ → ℝ,
        pathwiseBoundary → canonicalMeanBoundary SX → expectedGapBound SX) :
    ∃ M : ℕ → ℝ,
      mismatchBudget M ∧ expectedGapBound (noiseBudget M) := by
  rcases hboundary with ⟨M, hM, hpath, _hstageNoise, hcanonicalMean⟩
  exact ⟨M, hM, hexpected (noiseBudget M) hpath hcanonicalMean⟩


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: expected gap with an indexed primal budget from fixed-domain
--   completion and an expectation-ready stage-separated boundary; orig was
--   expected_gap_le_Q0StageSeparatedWithPrimalBudget_of_fixedDomainComplete_mixedCenter.
-- generality used: arbitrary measurable sample space, generated-sample type,
--   output type, measure, real-valued gap process, prefix realization,
--   stream/one-step measurability contracts, an abstract stage-separated
--   expected-boundary predicate, an indexed mismatch-budget predicate, and a
--   generated expected-gap consumer; no Hilbert, convexity, smoothness,
--   finite-dimensional, oracle, or probability structure is used by this
--   assembly step.
-- portable call pattern: stochastic accelerated primal-dual, stochastic
--   mirror-prox, and generated-query mirror-descent proofs after fixed-domain
--   completion has produced a generated stream and the proof already has an
--   expectation-ready stage-separated boundary; the concrete boundary,
--   measurability derivation, output map, and budget formula vary while the
--   completed-output expected-gap conclusion has the same shape.
-- counterargument checked: this is not the scalar integration lemma
--   `expectedGap_le_primalBudget_of_scaled_envelope`, nor the earlier
--   same-sample guard assembler, because it starts from a stage-separated
--   expectation-ready boundary and isolates only the reusable completion,
--   measurability, expected-boundary consumption, and output-transfer step.
-- coverage search: searched source/staging/catalog for "expected gap fixed
--   domain complete stage separated boundary primal budget", "stage separated
--   expectation boundary with loose mismatch", and "gap envelope primal
--   budget"; closest hits were
--   `expectedGapWithPrimalBudget_of_fixedDomainComplete_sameSampleGuards`,
--   `expectedGap_le_primalBudget_of_scaled_envelope`, and
--   `stageSeparatedExpectedGapBoundaryWithLooseMismatch`, all partial because
--   none covers the completed-output transfer from an already expectation-ready
--   stage-separated boundary.
-- minimal hypotheses: the source-moment hypothesis from the paper wrapper is
--   dropped because this proof does not consume it; completion is reduced to
--   prefix realization, stream measurability from that realization, one-step
--   measurability, the stage boundary, the expected-boundary consumer, and
--   equality of completed and generated gap integrands.

/-- Fixed-domain completion transfers an expectation-ready stage-separated budget.

If a completed finite-horizon run realizes the generated stream through the
next horizon, that realization yields the reporting-horizon stream
measurability, the one-step boundary is available, and an expectation-ready
stage-separated boundary implies the generated expected-gap budget, then the
completed public output satisfies the same indexed-primal budget after rewriting
its gap integrand to the generated output.

Layer: Layer1 | Gap: Level 1 (completion stage-separated expected-gap budget assembly)
Proof: restrict the completed realization to the reporting horizon, derive the
  generated-stream measurability contract, consume the stage-separated
  expected-boundary theorem, and rewrite the completed gap integral to the
  generated one.
Source: stochastic generated-process completion and Mathlib Bochner integral
  rewriting for real-valued expected-gap bounds
Used in: stochastic accelerated primal-dual expected saddle-gap proof after
  fixed-domain generated-query completion and stage-separated expectation
  boundary construction
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem expectedGapWithPrimalBudget_of_fixedDomainComplete_stageSeparatedBoundary
    {Ω Sample Out : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (gap : Out → ℝ)
    (completedOut generatedOut : Ω → Out)
    (sample : Sample) (t : ℕ)
    (Realized StreamMeasurable OneStepMeasurable StageBoundary : Sample → ℕ → Prop)
    (MismatchBudget : Sample → ℕ → (ℕ → ℝ) → Prop)
    (noiseBudget : (ℕ → ℝ) → ℕ → ℝ)
    (budget : (ℕ → ℝ) → ℝ)
    (hrealized_full : Realized sample (t + 1))
    (hrealized_prefix : Realized sample (t + 1) → Realized sample t)
    (hstream : Realized sample t → StreamMeasurable sample t)
    (hstep : OneStepMeasurable sample t)
    (hstage : StageBoundary sample t)
    (hexpected :
      StreamMeasurable sample t → OneStepMeasurable sample t → StageBoundary sample t →
        ∃ M : ℕ → ℝ,
          MismatchBudget sample t M ∧
            ∫ ω, gap (generatedOut ω) ∂μ ≤ budget (noiseBudget M))
    (hgap_eq :
      (fun ω => gap (completedOut ω)) = (fun ω => gap (generatedOut ω))) :
    ∃ M : ℕ → ℝ,
      MismatchBudget sample t M ∧
        ∫ ω, gap (completedOut ω) ∂μ ≤ budget (noiseBudget M) := by
  have hrealized_t : Realized sample t := hrealized_prefix hrealized_full
  have hstream_t : StreamMeasurable sample t := hstream hrealized_t
  rcases hexpected hstream_t hstep hstage with ⟨M, hbudget, hgen⟩
  refine ⟨M, hbudget, ?_⟩
  rw [hgap_eq]
  exact hgen


open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: expected gap bound from a scaled descent envelope and indexed primal budget; orig was expected_gap_le_Q0WithPrimalBudget_of_eq4472_envelope
-- generality used: arbitrary output type, probability measure, real-valued gap process, integrable residual, positive scalar schedules, and the concrete two-block indexed primal-noise budget formula
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, or accelerated saddle-point proofs after deriving a pathwise scaled gap envelope and a residual mean budget; the output map, residual, schedules, and indexed primal budget change while the expected-gap conclusion has the same form
-- counterargument checked: not paper-local traceability because it removes generated-process/setup fields and theorem-number names; not a duplicate of `integral_le_inv_mul_budget_of_ae_mul_le_add` because it additionally assembles the primal-dual indexed budget formula and proves the diameter-budget inflation step
-- coverage search: checked SOptLib catalog and symbol search for expected gap budget, scaled envelope integration, and primal noise budget; closest hits were `integral_le_inv_mul_budget_of_ae_mul_le_add` and `primalDualExpectedGapBudgetWithPrimalNoiseBudget`, which supply components but not this Layer1 assembly statement
-- minimal hypotheses: all already minimal for the assembled formula; positivity is only required at the current time for beta/gamma/eta/tau, and all stochastic structure is reduced to integrability plus an a.e. scaled envelope

/-- A scaled expected-gap envelope implies the indexed-primal two-block budget.

If a probability-space gap process satisfies a pathwise scaled upper envelope
with an integrable residual, and the residual mean is bounded by the finite
indexed primal/dual noise budget, then its expectation is bounded by the
closed-form two-block expected-gap budget with indexed primal noise.

Layer: Layer1 | Gap: Level 1 (scaled expected-gap envelope to indexed primal budget)
Proof: first enlarge the two deterministic diameter terms to the standard
  four-times budget using positivity of the current schedules, then call the
  scaled a.e. envelope integration lemma and simplify to the named budget.
Source: Mathlib Bochner integral monotonicity and real ordered-field arithmetic
  for stochastic primal-dual convergence-rate budgets
Used in: stochastic accelerated primal-dual expected saddle-gap proof after a
  pathwise descent envelope and per-index primal residual budget are available
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem expectedGap_le_primalBudget_of_scaled_envelope
    {Ω Out : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (gap : Out → ℝ) (out : Ω → Out) (U : Ω → ℝ)
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y : ℝ) (primalNoiseBudget : ℕ → ℝ)
    (sigmaY p q : ℝ) (t : ℕ)
    (hbeta_pos : 0 < beta t)
    (hgamma_pos : 0 < gamma t)
    (heta_pos : 0 < eta t)
    (htau_pos : 0 < tau t)
    (hgap_int : Integrable (fun ω => gap (out ω)) μ)
    (hU_int : Integrable U μ)
    (hupper :
      ∀ᵐ ω ∂μ,
        (beta t * gamma t) * gap (out ω) ≤
          (2 * gamma t / eta t * D_X ^ 2 +
            2 * gamma t / tau t * D_Y ^ 2) + U ω)
    (hUmean :
      ∫ ω, U ω ∂μ ≤
        (1 / 2) *
          Finset.sum (Finset.Icc 1 t) (fun i =>
            ((2 - q) * eta i * gamma i / (1 - q)) *
                primalNoiseBudget i +
              ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2)) :
    ∫ ω, gap (out ω) ∂μ ≤
      primalDualExpectedGapBudgetWithPrimalNoiseBudget beta gamma eta tau
        D_X D_Y primalNoiseBudget sigmaY p q t := by
  let c : ℝ := beta t * gamma t
  let B0 : ℝ :=
    2 * gamma t / eta t * D_X ^ 2 +
      2 * gamma t / tau t * D_Y ^ 2
  let S0 : ℝ :=
    Finset.sum (Finset.Icc 1 t) (fun i =>
      ((2 - q) * eta i * gamma i / (1 - q)) *
          primalNoiseBudget i +
        ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2)
  have hcpos : 0 < c := mul_pos hbeta_pos hgamma_pos
  have hB0_le :
      B0 ≤
        4 * gamma t / eta t * D_X ^ 2 +
          4 * gamma t / tau t * D_Y ^ 2 := by
    let xTerm : ℝ := 2 * gamma t / eta t * D_X ^ 2
    let yTerm : ℝ := 2 * gamma t / tau t * D_Y ^ 2
    have hx : 0 ≤ xTerm := by
      dsimp [xTerm]
      positivity
    have hy : 0 ≤ yTerm := by
      dsimp [yTerm]
      positivity
    have hx_le : xTerm ≤ 2 * xTerm := by nlinarith
    have hy_le : yTerm ≤ 2 * yTerm := by nlinarith
    have hxy : xTerm + yTerm ≤ 2 * xTerm + 2 * yTerm := add_le_add hx_le hy_le
    calc
      B0 = xTerm + yTerm := by simp [B0, xTerm, yTerm]
      _ ≤ 2 * xTerm + 2 * yTerm := hxy
      _ =
          4 * gamma t / eta t * D_X ^ 2 +
            4 * gamma t / tau t * D_Y ^ 2 := by
            simp [xTerm, yTerm]
            ring
  have hbudget :
      B0 + ∫ ω, U ω ∂μ ≤
        (4 * gamma t / eta t * D_X ^ 2 +
          4 * gamma t / tau t * D_Y ^ 2) + (1 / 2) * S0 := by
    nlinarith [hB0_le, hUmean]
  calc
    ∫ ω, gap (out ω) ∂μ
        ≤ c⁻¹ *
          ((4 * gamma t / eta t * D_X ^ 2 +
            4 * gamma t / tau t * D_Y ^ 2) + (1 / 2) * S0) := by
          exact
            integral_le_inv_mul_budget_of_ae_mul_le_add
              (μ := μ)
              (f := fun ω => gap (out ω))
              (U := U)
              (c := c)
              (B0 := B0)
              (R :=
                (4 * gamma t / eta t * D_X ^ 2 +
                    4 * gamma t / tau t * D_Y ^ 2) +
                  (1 / 2) * S0)
              hcpos hgap_int hU_int (by simpa [c, B0] using hupper) hbudget
    _ =
      primalDualExpectedGapBudgetWithPrimalNoiseBudget beta gamma eta tau
        D_X D_Y primalNoiseBudget sigmaY p q t := by
          simp [primalDualExpectedGapBudgetWithPrimalNoiseBudget, c, S0]
          ring


open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: expected gap bound from a scaled descent envelope and constant variance budget; orig was expected_gap_le_Q0_of_eq4472_envelope
-- generality used: arbitrary output type, probability measure, real-valued gap process, integrable residual, positive scalar schedules, and the concrete two-block constant-variance expected-gap budget formula
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, or accelerated saddle-point proofs after deriving a pathwise scaled gap envelope and a residual mean budget with fixed primal/dual variance scales; the output map, residual, schedules, and variance constants change while the expected-gap conclusion has the same form
-- counterargument checked: close to the indexed-primal theorem `expectedGap_le_primalBudget_of_scaled_envelope`; this scalar version is kept separate because it exposes the canonical constant-variance `primalDualExpectedGapBudget` API and avoids making callers manufacture an indexed constant budget
-- coverage search: searched catalog/source for expected gap budget, scaled envelope integration, and constant primal-dual variance budget; closest hits were `integral_le_inv_mul_budget_of_ae_mul_le_add`, `expectedGap_le_primalBudget_of_scaled_envelope`, and `primalDualExpectedGapBudgetWithPrimalNoiseBudget_const`, which combine to prove this canonical scalar-budget handoff
-- minimal hypotheses: positivity is only required at the terminal index for beta/gamma/eta/tau, and stochastic structure is reduced to integrability plus an a.e. scaled envelope; no convexity, smoothness, oracle, filtration, or finite-dimensional hypotheses are used

/-- A scaled expected-gap envelope implies the constant-variance two-block budget.

If a probability-space gap process satisfies a pathwise scaled upper envelope
with an integrable residual, and the residual mean is bounded by the finite
constant primal/dual variance budget, then its expectation is bounded by the
closed-form two-block expected-gap budget.

Layer: Layer1 | Gap: Level 1 (scaled expected-gap envelope to scalar budget)
Proof: instantiate the indexed-primal expected-gap theorem with the constant
  primal variance budget and rewrite via the constant-budget compatibility
  lemma.
Source: Mathlib Bochner integral monotonicity and real ordered-field arithmetic
  for stochastic primal-dual convergence-rate budgets
Used in: stochastic accelerated primal-dual expected saddle-gap proof after a
  pathwise descent envelope and constant primal/dual variance budgets are available
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem expected_gap_le_budget_of_scaled_envelope
    {Ω Out : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (gap : Out → ℝ) (out : Ω → Out) (U : Ω → ℝ)
    (beta gamma eta tau : ℕ → ℝ)
    (D_X D_Y sigmaX sigmaY p q : ℝ) (t : ℕ)
    (hbeta_pos : 0 < beta t)
    (hgamma_pos : 0 < gamma t)
    (heta_pos : 0 < eta t)
    (htau_pos : 0 < tau t)
    (hgap_int : Integrable (fun ω => gap (out ω)) μ)
    (hU_int : Integrable U μ)
    (hupper :
      ∀ᵐ ω ∂μ,
        (beta t * gamma t) * gap (out ω) ≤
          (2 * gamma t / eta t * D_X ^ 2 +
            2 * gamma t / tau t * D_Y ^ 2) + U ω)
    (hUmean :
      ∫ ω, U ω ∂μ ≤
        (1 / 2) *
          Finset.sum (Finset.Icc 1 t) (fun i =>
            ((2 - q) * eta i * gamma i / (1 - q)) * sigmaX ^ 2 +
              ((2 - p) * tau i * gamma i / (1 - p)) * sigmaY ^ 2)) :
    ∫ ω, gap (out ω) ∂μ ≤
      primalDualExpectedGapBudget beta gamma eta tau D_X D_Y sigmaX sigmaY p q t := by
  simpa [primalDualExpectedGapBudgetWithPrimalNoiseBudget_const] using
    (expectedGap_le_primalBudget_of_scaled_envelope
      (μ := μ)
      (gap := gap)
      (out := out)
      (U := U)
      (beta := beta)
      (gamma := gamma)
      (eta := eta)
      (tau := tau)
      (D_X := D_X)
      (D_Y := D_Y)
      (primalNoiseBudget := fun _ => sigmaX ^ 2)
      (sigmaY := sigmaY)
      (p := p)
      (q := q)
      (t := t)
      hbeta_pos hgamma_pos heta_pos htau_pos hgap_int hU_int hupper
      (by simpa using hUmean))


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: expected gap with an indexed primal budget from completion and
--   same-sample guards; orig was
--   expected_gap_le_Q0WithPrimalBudget_of_fixedDomainComplete_mixedCenter_sameSampleGuards.
-- generality used: arbitrary measurable sample space, arbitrary generated
--   sample type, arbitrary output type, an abstract measure, real-valued gap
--   process, finite-horizon realization/source/independence/martingale
--   contracts, an indexed mismatch-budget predicate, and an expected-envelope
--   consumer; no Hilbert, convexity, smoothness, or finite-dimensional
--   structure is used by this assembly step.
-- portable call pattern: stochastic accelerated primal-dual, stochastic
--   mirror-prox, and generated-query mirror-descent proofs after a partial
--   fixed-domain completion has produced a generated stream and the remaining
--   same-sample oracle guards build an indexed primal-noise envelope.
-- counterargument checked: this is not merely the scalar integration lemma
--   `expectedGap_le_primalBudget_of_scaled_envelope`; it assembles the
--   recurring completion-prefix, same-sample moment, guarded envelope, and
--   completed-output transfer steps. It deliberately leaves the concrete
--   envelope and expected-bound predicates as caller-supplied contracts rather
--   than introducing paper-shaped formulas.
-- coverage search: searched catalog/source for "expected gap primal budget",
--   "fixed domain complete same sample guards", "generated expected gap
--   completion", and "gap envelope primal budget"; closest hits were
--   `expectedGap_le_primalBudget_of_scaled_envelope`,
--   `gapDescentEnvelopeWithPrimalBudget`, and completion/output Model helpers,
--   all partial because none combines completion-to-prefix realization with
--   same-sample guard envelope assembly and final output transfer.
-- minimal hypotheses: global setup fields were reduced to the exact contracts
--   consumed by the proof: prefix realization, moment extraction from
--   same-sample independence, guarded envelope construction, expected-envelope
--   consumer, and equality of the completed and generated gap integrands.

/-- Completion and same-sample guards transfer an indexed-primal expected-gap budget.

If a completed finite-horizon run yields a generated realization through the
reporting horizon, same-sample independence supplies the moment guard, those
guards build a generated descent envelope with an indexed mismatch budget, and
the generated envelope has an expected-gap consumer, then the completed public
output satisfies the same indexed-primal budget.

Layer: Layer1 | Gap: Level 1 (completion guarded expected-gap budget assembly)
Proof: restrict the completed realization to the reporting horizon, derive the
  same-sample moment guard, obtain the indexed-budget envelope, invoke the
  expected-envelope consumer, and rewrite the completed gap integrand to the
  generated one.
Source: stochastic generated-process completion and Mathlib Bochner integral
  rewriting for real-valued expected-gap bounds
Used in: stochastic accelerated primal-dual expected saddle-gap proof after
  fixed-domain generated-query completion and same-sample oracle guard assembly
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem expectedGapWithPrimalBudget_of_fixedDomainComplete_sameSampleGuards
    {Ω Sample Out : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (gap : Out → ℝ)
    (completedOut generatedOut : Ω → Out)
    (sample : Sample) (t : ℕ)
    (Realized : Sample → ℕ → Prop)
    (SourceMoment SameSampleIndependent SameSampleMoment
      MartingaleMeanNonpos : Sample → ℕ → Prop)
    (MismatchBudget : Sample → ℕ → (ℕ → ℝ) → Prop)
    (Envelope : Sample → ℕ → (ℕ → ℝ) → Prop)
    (noiseBudget : (ℕ → ℝ) → ℕ → ℝ)
    (budget : (ℕ → ℝ) → ℝ)
    (hrealized_full : Realized sample (t + 1))
    (hrealized_prefix : Realized sample (t + 1) → Realized sample t)
    (hsource : SourceMoment sample t)
    (hindep : SameSampleIndependent sample t)
    (hmart : MartingaleMeanNonpos sample t)
    (hsameSampleMoment :
      Realized sample t → SameSampleIndependent sample t → SameSampleMoment sample t)
    (henvelope :
      Realized sample t → SourceMoment sample t → SameSampleMoment sample t →
        MartingaleMeanNonpos sample t →
          ∃ M : ℕ → ℝ, MismatchBudget sample t M ∧ Envelope sample t (noiseBudget M))
    (hexpected :
      Realized sample t → ∀ SX : ℕ → ℝ, Envelope sample t SX →
        ∫ ω, gap (generatedOut ω) ∂μ ≤ budget SX)
    (hgap_eq :
      (fun ω => gap (completedOut ω)) = (fun ω => gap (generatedOut ω))) :
    ∃ M : ℕ → ℝ,
      MismatchBudget sample t M ∧
        ∫ ω, gap (completedOut ω) ∂μ ≤ budget (noiseBudget M) := by
  have hrealized_t : Realized sample t := hrealized_prefix hrealized_full
  have hmoment : SameSampleMoment sample t := hsameSampleMoment hrealized_t hindep
  rcases henvelope hrealized_t hsource hmoment hmart with ⟨M, hbudget, henv⟩
  refine ⟨M, hbudget, ?_⟩
  rw [hgap_eq]
  exact hexpected hrealized_t (noiseBudget M) henv


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: measurable-output gap integrability from a descent envelope;
--   orig was `gap_generatedExtensionFeasibleOutput_integrable_via_descent`.
--   The statement removes SAPD setup fields and keeps only the stochastic
--   output, the real-valued gap functional, and the named absolute descent
--   envelope boundary.
-- generality used: arbitrary measurable sample and output spaces, arbitrary
--   measure, a measurable output random variable, a measurable real-valued gap
--   functional, and an existing `GapDescentEnvelope`; no probability,
--   filtration, independence, finite-dimensional, Hilbert, convexity,
--   smoothness, oracle, or update-rule hypotheses are used.
-- portable call pattern: stochastic mirror descent, stochastic primal-dual,
--   mirror-prox, and accelerated stochastic-gradient expected-gap proofs after
--   proving output measurability and a pathwise integrable descent envelope;
--   the output selector, gap functional, and envelope witness change while the
--   conclusion remains integrability of the composed gap random variable.
-- counterargument checked: `GapDescentEnvelope.integrable_of_measurable`
--   already covers a measurable random gap, so this theorem is intentionally
--   not a new envelope definition; it adds the common output-composition
--   boundary needed by algorithm files that separately prove output
--   measurability and gap-function measurability.
-- coverage search: searched catalog/project for "integrable gap",
--   "gap descent envelope", and "measurable output composition"; closest
--   SOptLib hit is `GapDescentEnvelope.integrable_of_measurable`, which is
--   partial because it expects measurability of the composed gap directly.
--   LeanSearch Mathlib hits included `Integrable.mono`,
--   `Integrable.comp_measurable`, and `Integrable.comp_aemeasurable`, none of
--   which package the descent-envelope proof boundary.
-- minimal hypotheses: output measurability and gap measurability replace the
--   algorithm-local generated-output measurability route; the measure is
--   arbitrary and the codomain is exactly `ℝ` because the algorithm integrates
--   a real expected gap.

/-- A measurable output with a measurable real gap is integrable under a gap descent envelope.

This is the reusable boundary between algorithm-specific output measurability
and the SOptLib absolute descent-envelope API.  Once the composed gap has a
`GapDescentEnvelope`, output and gap measurability provide the measurability
input needed to eliminate that envelope.

Layer: Layer1 | Gap: Level 1 (measurable output gap descent-envelope integrability)
Proof: compose the measurable gap with the measurable output and apply
  `GapDescentEnvelope.integrable_of_measurable`.
Source: Mathlib measurable-function composition and Bochner integrability
  domination APIs
Used in: accelerated stochastic primal-dual feasible-output saddle-gap
  integrability after the generated descent envelope is established
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem GapDescentEnvelope.integrable_comp_measurable
    {Ω Out : Type*} [MeasurableSpace Ω] [MeasurableSpace Out]
    {μ : Measure Ω} {gap : Out → ℝ} {out : Ω → Out}
    (hout : Measurable out)
    (hgap : Measurable gap)
    (henv : GapDescentEnvelope μ (fun ω => gap (out ω))) :
    Integrable (fun ω => gap (out ω)) μ := by
  exact GapDescentEnvelope.integrable_of_measurable (hgap.comp hout) henv


-- Generalization plan (G0):
-- concept/name: generated oracle realization monotonicity under horizon
--   restriction; orig was generatedAxOracleRealization_restrict_succ_horizon,
--   renamed to remove the APD-local `Ax` marker and expose the finite-horizon
--   oracle-realization concept.
-- generality used: arbitrary outcome, query, carrier, and sample types; no
--   measure, filtration, Hilbert, convexity, smoothness, or finite-dimensional
--   assumptions are used. The proof only needs the one-based finite-horizon
--   shape of `generatedOracleRealization`.
-- portable call pattern: generated-query stochastic optimization proofs that
--   first construct an oracle realization through a construction horizon `t`
--   and then invoke a descent, measurability, or martingale statement at any
--   shorter reporting horizon `s`.
-- counterargument checked: this is a short API theorem, but not paper-local
--   traceability; it is the monotonicity rule for a named Model oracle contract
--   and prevents future callers from reopening the dependent realization
--   definition at every prefix horizon.
-- coverage search: searched CATALOG, SOptLib, Staging, and the algorithm for
--   `generatedOracleRealization`, `restrict_le`, realization-prefix, and
--   `Finset.Icc` monotonicity. Existing hits define the contract, project
--   feasibility/sample equality, or package a larger gap-envelope bridge; none
--   states this standalone horizon-restriction theorem.
-- minimal hypotheses: all already minimal; the successor case is generalized
--   from `t ≤ t + 1` to an arbitrary `s ≤ t` and no formula-equality or
--   caller-specific guard predicates are introduced.

/-- A generated-oracle realization through a longer horizon restricts to any
shorter one.

For a one-based finite-horizon generated oracle contract, every index in
`Icc 1 s` is also in `Icc 1 t` when `s ≤ t`, so the same feasibility witness
and fixed-domain oracle equality apply.

Layer: Model | Gap: Level 0 (generated oracle realization horizon restriction)
Proof: specialize the longer realization after transporting membership in
  `Finset.Icc 1 s` to membership in `Finset.Icc 1 t` by natural-number
  monotonicity.
Source: stochastic approximation oracle-domain contracts and Mathlib finite
  closed intervals over natural numbers
Used in: stochastic accelerated primal-dual fixed-domain completion before
  invoking generated-stream descent and martingale envelope lemmas
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generatedOracleRealization_restrict_le
    {Ω E Y : Type*} {X : Set E}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → E}
    {oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y}
    {s t : ℕ}
    (hst : s ≤ t)
    (hrealize : generatedOracleRealization X sample query oracleSample t) :
    generatedOracleRealization X sample query oracleSample s := by
  intro i hi ω
  have hi_t : i ∈ Finset.Icc 1 t :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
      Nat.le_trans (Finset.mem_Icc.mp hi).2 hst⟩
  exact hrealize i hi_t ω


open scoped BigOperators InnerProductSpace

/-- A finite weighted two-stream square-noise residual.

Layer: Layer1 | Concept: Oracle residual
Proof: (definitional construction; finite weighted sum of squared residual norms)
Source: Mathlib finite big operators and normed additive groups
Used in: stochastic accelerated primal-dual canonical residual formulas
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def twoStreamSquareNoiseResidual
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (wx wy : ι → ℝ) (ω : Ω) : ℝ :=
  Finset.sum I (fun i =>
    if hi : active i then
      (1 / 2 : ℝ) * (wx i * ‖dx i hi ω‖ ^ 2 + wy i * ‖dy i hi ω‖ ^ 2)
    else 0)

/-- The finite weighted two-stream square-noise residual unfolds to its guarded sum.

Layer: Layer1 | Gap: Level 0 (two-stream square-noise residual unfolding)
Proof: by rfl after unfolding `twoStreamSquareNoiseResidual`.
Source: Mathlib finite big operators and normed additive groups
Used in: stochastic accelerated primal-dual residual simplification
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem twoStreamSquareNoiseResidual_def
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (wx wy : ι → ℝ) (ω : Ω) :
    twoStreamSquareNoiseResidual I active dx dy wx wy ω =
      Finset.sum I (fun i =>
        if hi : active i then
          (1 / 2 : ℝ) * (wx i * ‖dx i hi ω‖ ^ 2 + wy i * ‖dy i hi ω‖ ^ 2)
        else 0) := rfl

/-- A weighted finite sum of two-block martingale residual inner products.

Layer: Layer1 | Concept: Martingale residual
Proof: (definitional construction; finite weighted two-block inner-product residual)
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual canonical residual formulas
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def weightedTwoBlockMartingaleResidual
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (gamma : ι → ℝ)
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F) (ω : Ω) : ℝ :=
  Finset.sum I fun i =>
    if hi : active i then
      gamma i *
        (⟪dx i hi ω, (zv i ω).1 - (z i ω).1⟫_ℝ +
          ⟪dy i hi ω, (zv i ω).2 - (z i ω).2⟫_ℝ)
    else 0

/-- The weighted two-block martingale residual unfolds to its guarded sum.

Layer: Layer1 | Gap: Level 0 (martingale residual unfolding)
Proof: by rfl after unfolding `weightedTwoBlockMartingaleResidual`.
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual residual simplification
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem weightedTwoBlockMartingaleResidual_def
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (gamma : ι → ℝ)
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F) (ω : Ω) :
    weightedTwoBlockMartingaleResidual I active gamma dx dy zv z ω =
      Finset.sum I (fun i =>
        if hi : active i then
          gamma i *
            (⟪dx i hi ω, (zv i ω).1 - (z i ω).1⟫_ℝ +
              ⟪dy i hi ω, (zv i ω).2 - (z i ω).2⟫_ℝ)
        else 0) := rfl

/-- The canonical square-noise plus weighted martingale residual.

Layer: Layer1 | Concept: Martingale residual
Proof: (definitional construction; sum of square-noise and martingale residuals)
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual canonical residual formulas
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def twoStreamSquareNoiseAddWeightedMartingaleResidual
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F)
    (gamma eta tau : ι → ℝ) (p q : ℝ) (ω : Ω) : ℝ :=
  twoStreamSquareNoiseResidual I active dx dy
      (fun i => (2 - q) * eta i * gamma i / (1 - q))
      (fun i => (2 - p) * tau i * gamma i / (1 - p)) ω +
    weightedTwoBlockMartingaleResidual I active gamma dx dy zv z ω

/-- The canonical square-noise plus weighted martingale residual unfolds.

Layer: Layer1 | Gap: Level 0 (canonical residual unfolding)
Proof: by rfl after unfolding `twoStreamSquareNoiseAddWeightedMartingaleResidual`.
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual canonical residual simplification
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem twoStreamSquareNoiseAddWeightedMartingaleResidual_def
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F)
    (gamma eta tau : ι → ℝ) (p q : ℝ) (ω : Ω) :
    twoStreamSquareNoiseAddWeightedMartingaleResidual I active dx dy zv z gamma eta tau p q ω =
      twoStreamSquareNoiseResidual I active dx dy
          (fun i => (2 - q) * eta i * gamma i / (1 - q))
          (fun i => (2 - p) * tau i * gamma i / (1 - p)) ω +
        weightedTwoBlockMartingaleResidual I active gamma dx dy zv z ω := rfl

-- Generalization plan (G0):
-- concept/name: weighted two-block martingale residual finite sum; orig was
--   generatedEq4471MartingaleU, a paper-local Eq. (4.4.71) component.
-- generality used: arbitrary sample and finite-index types; two real
--   inner-product residual spaces; an active-index predicate; deterministic
--   scalar weights; no measure, filtration, independence, convexity,
--   smoothness, or finite-dimensional assumptions are used by the formula.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   block-coordinate stochastic descent proofs use the same finite-window
--   martingale residual before per-index conditional-mean cancellation; the
--   residual streams, comparison/iterate points, active window, and weights
--   change while the residual-sum expression remains the same.
-- counterargument checked: this is a definition, so the risk is paper-local
--   traceability; it still has SOptLib-core value because it names the
--   recurring two-block weighted martingale residual consumed by generic
--   finite-sum cancellation and mean-bound lemmas, rather than encoding a
--   theorem number or setup field.
-- coverage search: searched catalog/project for "martingale residual",
--   "inner product residual", "finite residual aggregation", and LeanSearch
--   for "finite sum inner product martingale residual"; Mathlib and SOptLib
--   have conditional-expectation cancellation and finite integral aggregation
--   lemmas, but no named two-block residual finite-sum object with active
--   index guards.
-- minimal hypotheses: all already minimal for the formula; global SAPD setup
--   fields were reduced to `dx`, `dy`, `zv`, `z`, `gamma`, the finite window,
--   and the active-index predicate.

/-- A weighted finite sum of two-block martingale residual inner products.

For each active index, the summand pairs a primal residual with the primal
coordinate displacement and a dual residual with the dual coordinate
displacement, then scales the sum by a deterministic weight.

Layer: Layer1 | Concept: Martingale residual
Proof: (definitional construction; finite weighted two-block inner-product
  residual)
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual finite-window martingale residual
  before per-index conditional-mean cancellation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def sapdMartingaleResidualU
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [∀ i, Decidable (active i)]
    (gamma : ι → ℝ)
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F) (ω : Ω) : ℝ :=
  Finset.sum I fun i =>
    if hi : active i then
      gamma i *
        (⟪dx i hi ω, (zv i ω).1 - (z i ω).1⟫_ℝ +
          ⟪dy i hi ω, (zv i ω).2 - (z i ω).2⟫_ℝ)
    else 0

/-- The two-block martingale residual finite sum unfolds to its guarded summand.

Layer: Layer1 | Gap: Level 0 (martingale residual unfolding)
Proof: by rfl after unfolding `sapdMartingaleResidualU`.
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual residual simplification before
  finite-sum integration
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem sapdMartingaleResidualU_apply
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [∀ i, Decidable (active i)]
    (gamma : ι → ℝ)
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F) (ω : Ω) :
    sapdMartingaleResidualU I active gamma dx dy zv z ω =
      Finset.sum I (fun i =>
        if hi : active i then
          gamma i *
            (⟪dx i hi ω, (zv i ω).1 - (z i ω).1⟫_ℝ +
              ⟪dy i hi ω, (zv i ω).2 - (z i ω).2⟫_ℝ)
        else 0) := by
  rfl


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-window two-stream square-noise residual with accelerated
--   primal-dual sampling weights; orig was generatedEq4471SquareNoiseU,
--   renamed from an equation-number source artifact to the named residual
--   formula used by stochastic primal-dual descent proofs.
-- generality used: arbitrary sample type, two NormedAddCommGroup-valued noise
--   streams, scalar schedules gamma/eta/tau, and scalar sampling parameters p/q;
--   no measure, independence, integrability, Hilbert inner product, convexity,
--   smoothness, or oracle hypotheses are needed to define the residual.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   two-block stochastic mirror descent proofs collect primal and dual
--   square-noise terms into the same finite-window weighted residual; the
--   concrete noise streams and schedules change while the residual formula
--   remains the same.
-- counterargument checked: this is not the expectation-bound theorem already
--   staged as weighted_two_noise_finset_sq_integrable_and_bound; it names the
--   caller-side finite residual that those bounds consume.  It is more than a
--   pure paper traceability alias because future two-block stochastic proofs
--   can expose this formula directly in their descent residuals.
-- coverage search: searched "square noise residual", "weighted two noise
--   finset square noise residual", and existing staged square-noise files.
--   Mathlib has finite-sum and norm primitives, while SOptLib/Staging has
--   aggregation theorems but no named accelerated two-stream residual formula;
--   coverage is partial, not duplicate.
-- minimal hypotheses: all stochastic assumptions were removed; the definition
--   keeps only the scalar schedules, sampling parameters, two noise streams,
--   time horizon, and sample point used by the formula.

/-- Finite-window two-stream square-noise residual with accelerated primal-dual weights.

The residual sums half of the weighted squared norms of a primal noise stream
and a dual noise stream over the positive time window `1..t`, using the
standard `(2 - q)/(1 - q)` and `(2 - p)/(1 - p)` sampling weights.

Layer: Layer1 | Concept: Oracle
Proof: (definitional construction; finite-window weighted two-stream square-noise residual)
Source: Lan accelerated stochastic primal-dual descent algebra and Mathlib
  finite-sum/norm notation for normed additive groups
Used in: stochastic accelerated primal-dual descent residual before the
  square-noise expectation budget is assembled
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def sapdSquareNoiseResidualU
    {Ω EX EY : Type*} [NormedAddCommGroup EX] [NormedAddCommGroup EY]
    (dx : ∀ i : ℕ, 1 ≤ i → Ω → EX)
    (dy : ∀ i : ℕ, 1 ≤ i → Ω → EY)
    (gamma eta tau : ℕ → ℝ) (p q : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.Icc 1 t) (fun i =>
    if hi : 1 ≤ i then
      (1 / 2 : ℝ) *
        (((2 - q) * eta i * gamma i / (1 - q)) * ‖dx i hi ω‖ ^ 2 +
          ((2 - p) * tau i * gamma i / (1 - p)) * ‖dy i hi ω‖ ^ 2)
    else 0)

/-- The accelerated two-stream square-noise residual unfolds to its finite-sum formula.

Layer: Layer1 | Gap: Level 0 (two-stream square-noise residual unfolding)
Proof: by rfl after unfolding sapdSquareNoiseResidualU.
Source: Lan accelerated stochastic primal-dual descent algebra and Mathlib
  finite-sum/norm notation for normed additive groups
Used in: stochastic accelerated primal-dual descent residual before the
  square-noise expectation budget is assembled
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp] theorem sapdSquareNoiseResidualU_def
    {Ω EX EY : Type*} [NormedAddCommGroup EX] [NormedAddCommGroup EY]
    (dx : ∀ i : ℕ, 1 ≤ i → Ω → EX)
    (dy : ∀ i : ℕ, 1 ≤ i → Ω → EY)
    (gamma eta tau : ℕ → ℝ) (p q : ℝ) (t : ℕ) (ω : Ω) :
    sapdSquareNoiseResidualU dx dy gamma eta tau p q t ω =
      Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then
          (1 / 2 : ℝ) *
            (((2 - q) * eta i * gamma i / (1 - q)) * ‖dx i hi ω‖ ^ 2 +
              ((2 - p) * tau i * gamma i / (1 - p)) * ‖dy i hi ω‖ ^ 2)
        else 0) := rfl


open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite-window canonical two-stream residual; orig was
--   generatedEq4471U, a paper-local Eq. (4.4.71) residual name.
-- generality used: arbitrary sample and finite-index types; two real
--   inner-product residual spaces; an active-index predicate; deterministic
--   schedules `gamma`, `eta`, `tau` and scalar Young parameters `p`, `q`; no
--   measure, filtration, independence, convexity, smoothness, or oracle
--   hypotheses are needed by the formula.
-- portable call pattern: accelerated primal-dual, mirror-prox, and two-block
--   stochastic mirror-descent proofs collect the same square-noise plus
--   martingale correction residual before expectation or high-probability
--   budgets; residual streams, comparison processes, finite windows, and
--   schedules vary while the residual shape remains unchanged.
-- counterargument checked: this is a definition, so the risk is local
--   traceability; the counterargument does not win because the object is the
--   reusable combination consumed by generic pathwise gap envelopes and
--   residual mean bounds, and it is not just a theorem-number wrapper.
-- coverage search: searched catalog/project for "canonical residual",
--   "square-noise martingale residual", "two-stream residual", and
--   "weighted two-block martingale residual"; SOptLib/Mathlib cover finite
--   sums and the two staged components, but no existing declaration names
--   their canonical combined residual.
-- minimal hypotheses: all already minimal for the formula; global SAPD setup
--   fields were reduced to `dx`, `dy`, `zv`, `z`, `gamma`, `eta`, `tau`, `p`,
--   `q`, the finite window, and the active-index predicate.

/-- The canonical finite-window residual combining square noise and martingale correction.

The residual adds a two-stream weighted square-noise sum to the corresponding
two-block martingale inner-product residual.  The accelerated weights are
passed as schedules, so the same object can be instantiated by related
two-block stochastic descent arguments with different windows and processes.

Layer: Layer1 | Concept: Martingale residual
Proof: (definitional construction; sum of the finite two-stream square-noise
  residual and weighted two-block martingale residual)
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual pathwise gap envelope before
  square-noise and martingale mean estimates are combined
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def sapdCanonicalResidualU
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F)
    (gamma eta tau : ι → ℝ) (p q : ℝ) (ω : Ω) : ℝ :=
  twoStreamSquareNoiseResidual I active dx dy
      (fun i => (2 - q) * eta i * gamma i / (1 - q))
      (fun i => (2 - p) * tau i * gamma i / (1 - p)) ω +
    weightedTwoBlockMartingaleResidual I active gamma dx dy zv z ω

/-- The canonical residual unfolds into its square-noise and martingale components.

Layer: Layer1 | Gap: Level 0 (canonical residual component decomposition)
Proof: by rfl after unfolding `sapdCanonicalResidualU`.
Source: Mathlib finite big operators and real inner-product spaces
Used in: stochastic accelerated primal-dual residual simplification before
  finite-window expectation bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem sapdCanonicalResidualU_def
    {Ω ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : Finset ι) (active : ι → Prop) [DecidablePred active]
    (dx : ∀ i, active i → Ω → E)
    (dy : ∀ i, active i → Ω → F)
    (zv z : ι → Ω → E × F)
    (gamma eta tau : ι → ℝ) (p q : ℝ) (ω : Ω) :
    sapdCanonicalResidualU I active dx dy zv z gamma eta tau p q ω =
      twoStreamSquareNoiseResidual I active dx dy
          (fun i => (2 - q) * eta i * gamma i / (1 - q))
          (fun i => (2 - p) * tau i * gamma i / (1 - p)) ω +
        weightedTwoBlockMartingaleResidual I active gamma dx dy zv z ω := by
  rfl


-- Generalization plan (G0):
-- concept/name: ordered-additive upper-bound assembly from scalar atoms.
-- generality used: ordered additive-group scalar algebra only; no measure,
--   filtration, convexity, smoothness, Hilbert-space, or finite dimensional
--   assumptions are used by this final assembly step.
-- portable call pattern: additive estimate proofs after a left-hand side has
--   been expanded into scalar atoms and separate left/right, coupling, square,
--   and residual split bounds have been proved; the scalar atoms change while
--   the conclusion shape stays.
-- counterargument checked: this is an assembly lemma and close to caller-side
--   arithmetic, but it removes a recurring proof-composition boundary above the
--   lower scalar lemma, without naming a paper formula or introducing a
--   single-use definition.
-- coverage search: searched the SOptLib catalog, Staging, and project symbols
--   for upper-bound assembly, bilinear square residual assembly, and scalar
--   additive-bound assembly; the lower atom inequality does not cover the
--   left-side and residual expansion boundary consumed by this block.
-- minimal hypotheses: all hypotheses are pointwise scalar equalities or
--   inequalities; no global assumptions remain.

/-- Assemble an expanded additive left-hand side from scalar atoms.

Once a left-hand side has been expanded into scalar atoms for two upper bounds,
a bilinear coupling identity, a squared-term normalization, and an additive
residual split, this theorem rewrites it to the final upper bound.

Layer: Glue | Gap: Level 1 (additive upper-bound atom assembly)
Proof: rewrite the left-hand side to the atom sum, add the two scalar upper
  bounds, and reassociate the coupling, square, and residual terms.
Source: Mathlib ordered additive-group arithmetic and subtraction APIs
Used in: scalar additive estimate assembly after two component upper bounds and
  coupling, square, and residual identities -/
theorem additive_upper_bound_assembly_from_atoms
    {R : Type*} [AddCommGroup R] [Preorder R] [IsOrderedAddMonoid R]
    {lhs residual a b q c e vx sx vy sy atTerm dxn dyn gt coupling square : R}
    (hlhs : lhs = a + b + q + c - e)
    (hleft : a ≤ vx - sx - atTerm - dxn)
    (hright : b ≤ vy - sy - dyn + gt)
    (hbilinear : -atTerm + c - e + gt = coupling)
    (hsquare : -sx + q = square)
    (hresidual : residual = -dxn - dyn) :
    lhs ≤ vx + vy + coupling + square - sy + residual := by
  rw [hlhs]
  have hsum :
      a + b ≤ (vx - sx - atTerm - dxn) + (vy - sy - dyn + gt) :=
    add_le_add hleft hright
  have hassembled :
      a + b + q + c - e ≤
        ((vx - sx - atTerm - dxn) + (vy - sy - dyn + gt)) + q + c - e :=
    by
      simpa [add_assoc, add_comm, add_left_comm] using
        sub_le_sub_right (add_le_add_right (add_le_add_right hsum q) c) e
  refine hassembled.trans_eq ?_
  calc
    ((vx - sx - atTerm - dxn) + (vy - sy - dyn + gt)) + q + c - e =
        vx + vy + (-atTerm + c - e + gt) + (-sx + q) - sy - dxn - dyn := by
      abel
    _ = vx + vy + coupling + square - sy - dxn - dyn := by
      rw [hbilinear, hsquare]
    _ = vx + vy + coupling + square - sy + (-dxn - dyn) := by
      abel
    _ = vx + vy + coupling + square - sy + residual := by
      rw [hresidual]

/-- Isolate the left scaled summand from a common-multiplier three-term upper
bound.

If `γ * (a + b + c)` is bounded above by `r`, then `γ * a` is bounded by
subtracting the other two scaled summands from `r`.

Layer: Glue | Gap: Level 0 (scaled three-summand order rearrangement)
Proof: distribute the common left multiplier across the three-term sum, then
  apply the additive ordered-group subtraction API twice to isolate the first
  scaled summand.
Source: Mathlib ordered ring distributivity and additive subtraction APIs
Used in: stochastic accelerated primal-dual prox expansion scaled-term
  isolation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem mul_left_le_sub_sub_of_mul_add_add_le
    {R : Type*} [NonUnitalNonAssocRing R] [PartialOrder R] [IsOrderedAddMonoid R]
    (γ a b c r : R) (h : γ * (a + b + c) ≤ r) :
    γ * a ≤ r - γ * b - γ * c := by
  have h' : γ * a + γ * b + γ * c ≤ r := by
    simpa [mul_add, add_assoc] using h
  have h'' : γ * a + (γ * b + γ * c) ≤ r := by
    simpa [add_assoc] using h'
  have hle : γ * a ≤ r - (γ * b + γ * c) :=
    le_sub_right_of_add_le h''
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle


open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: accelerated primal-dual one-step prox/noise/coupling assembly;
--   orig was generated_eq_4461_one_step_bound. The declaration uses a
--   concept-rooted name for backfill, and the statement removes setup fields,
--   generated processes, and theorem-number notation from the API.
-- generality used: arbitrary real Hilbert spaces with complete-space instances,
--   one continuous linear map, pointwise scalar schedules, pointwise gap/prox
--   inequalities, a target decomposition, and a residual-pair equality. No
--   measure, filtration, independence, integrability, convexity, or smoothness
--   assumptions are used by this assembly step.
-- portable call pattern: accelerated primal-dual, mirror-prox, and
--   extragradient one-step descent proofs after a deterministic gap recurrence,
--   primal prox bound, dual composite prox bound, oracle residual split, and
--   lagged operator-query decomposition have been proved; the process,
--   oracle residuals, schedules, and prox models vary while the conclusion
--   keeps the same one-step bound shape.
-- counterargument checked: this is not a duplicate of the lower scalar
--   `additive_upper_bound_assembly_from_atoms`, which assumes already-isolated
--   scalar atoms, nor of the adjoint lagged cancellation, primal/dual prox
--   lemmas, or finite-window telescope entries. It is a proof-composition
--   boundary above those pieces, not paper-local traceability alone.
-- coverage search: searched the SOptLib catalog and staging files for
--   `one step descent assembly`, `prox dual primal noise bilinear`, `rhs
--   assembly from atoms`, and `adjoint lagged bilinear cancellation`; hits were
--   the scalar atom assembler, lagged adjoint cancellation, prox component
--   bounds, and finite-sum telescope lemmas, all partial but none covering this
--   combined pointwise APD/mirror-prox descent statement.
-- minimal hypotheses: all global setup fields were replaced by pointwise
--   hypotheses; the only typeclass assumptions are those required for real
--   inner products, norms, and continuous-linear-map adjoints.

/-- Assemble a one-step accelerated primal-dual bound from gap, prox, residual,
and lagged coupling hypotheses.

The theorem consumes a proposition-style gap recurrence, primal and dual
proximal descent bounds, a two-block residual identity, and a lagged linear
operator target decomposition. It returns the standard one-step saddle-gap
upper bound with Bregman-drop scalars, current coupling, two lagged coupling
terms, squared-step penalties, and the paired residual inner products.

Layer: Layer1 | Gap: Level 1 (accelerated primal-dual one-step descent assembly)
Proof: split the primal and dual prox inequalities into scalar atoms, use the
  continuous-linear-map adjoint cancellation for the coupling terms, assemble
  the scalar upper bound, and compose it with the gap recurrence.
Source: Mathlib real inner-product adjoints, ordered-ring arithmetic, and
  finite-dimensional-free Hilbert-space norm algebra
Used in: stochastic accelerated primal-dual and mirror-prox one-step descent
  after prox estimates and oracle residual decompositions
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem accelerated_primal_dual_one_step_bound_of_gap_prox_residual_coupling
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (A : X →L[ℝ] Y)
    (β γ γPrev η τ L gap gapPrev vxDrop vyDrop gdiff : ℝ)
    (grad δx : X) (δy target : Y) (delta : X × Y)
    (xPrev xNext xLag zx : X) (yPrev yNext zy : Y)
    (hgap :
      γ * (β * gap - (β - 1) * gapPrev) ≤
        γ *
          (⟪grad, xNext - zx⟫_ℝ +
            (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 +
            gdiff +
            ⟪A xNext, zy⟫_ℝ -
            ⟪A zx, yNext⟫_ℝ))
    (hprimal :
      γ * ⟪grad + A.adjoint yNext + δx, xNext - zx⟫_ℝ ≤
        γ / η * vxDrop -
          γ / (2 * η) * ‖xNext - xPrev‖ ^ 2)
    (hdual :
      γ * (⟪δy - target, yNext - zy⟫_ℝ + gdiff) ≤
        γ / τ * vyDrop -
          γ / (2 * τ) * ‖yNext - yPrev‖ ^ 2)
    (htarget :
      γ * ⟪target, yNext - zy⟫_ℝ =
        γ * ⟪A xPrev, yNext - zy⟫_ℝ +
          γPrev * ⟪A xLag, yNext - zy⟫_ℝ)
    (hdelta : delta = (δx, δy)) :
    β * γ * gap - (β - 1) * γ * gapPrev ≤
      γ / η * vxDrop +
        γ / τ * vyDrop +
        γ * ⟪A (xNext - xPrev), zy - yNext⟫_ℝ -
        γPrev * ⟪A xLag, zy - yPrev⟫_ℝ -
        γPrev * ⟪A xLag, yPrev - yNext⟫_ℝ -
        γ * (1 / (2 * η) - L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 -
        γ / (2 * τ) * ‖yNext - yPrev‖ ^ 2 -
        γ *
          (⟪delta.1, xNext - zx⟫_ℝ +
            ⟪delta.2, yNext - zy⟫_ℝ) := by
  have hgap_left :
      β * γ * gap - (β - 1) * γ * gapPrev ≤
        γ *
          (⟪grad, xNext - zx⟫_ℝ +
            (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 +
            gdiff +
            ⟪A xNext, zy⟫_ℝ -
            ⟪A zx, yNext⟫_ℝ) := by
    have hleft :
        γ * (β * gap - (β - 1) * gapPrev) =
          β * γ * gap - (β - 1) * γ * gapPrev := by
      ring
    simpa [hleft] using hgap
  have hprimal_exp :
      γ *
          (⟪grad, xNext - zx⟫_ℝ +
            ⟪A.adjoint yNext, xNext - zx⟫_ℝ +
            ⟪δx, xNext - zx⟫_ℝ) ≤
        γ / η * vxDrop -
          γ / (2 * η) * ‖xNext - xPrev‖ ^ 2 := by
    calc
      γ *
          (⟪grad, xNext - zx⟫_ℝ +
            ⟪A.adjoint yNext, xNext - zx⟫_ℝ +
            ⟪δx, xNext - zx⟫_ℝ) =
          γ * ⟪grad + A.adjoint yNext + δx, xNext - zx⟫_ℝ := by
            rw [mul_inner_add_add_left]
      _ ≤ γ / η * vxDrop -
            γ / (2 * η) * ‖xNext - xPrev‖ ^ 2 := hprimal
  have hgrad_bound :
      γ * ⟪grad, xNext - zx⟫_ℝ ≤
        γ / η * vxDrop -
          γ / (2 * η) * ‖xNext - xPrev‖ ^ 2 -
          γ * ⟪A.adjoint yNext, xNext - zx⟫_ℝ -
          γ * ⟪δx, xNext - zx⟫_ℝ := by
    exact
      mul_left_le_sub_sub_of_mul_add_add_le
        γ
        (⟪grad, xNext - zx⟫_ℝ)
        (⟪A.adjoint yNext, xNext - zx⟫_ℝ)
        (⟪δx, xNext - zx⟫_ℝ)
        (γ / η * vxDrop -
          γ / (2 * η) * ‖xNext - xPrev‖ ^ 2)
        hprimal_exp
  have hdual_split_scaled :
      γ * ⟪δy - target, yNext - zy⟫_ℝ =
        γ * ⟪δy, yNext - zy⟫_ℝ -
          γ * ⟪target, yNext - zy⟫_ℝ := by
    rw [inner_sub_left]
    ring
  have hgdiff_bound :
      γ * gdiff ≤
        γ / τ * vyDrop -
          γ / (2 * τ) * ‖yNext - yPrev‖ ^ 2 -
          γ * ⟪δy, yNext - zy⟫_ℝ +
          γ * ⟪target, yNext - zy⟫_ℝ := by
    exact
      mul_add_sub_isolate_second_term
        γ
        (⟪δy - target, yNext - zy⟫_ℝ)
        (⟪δy, yNext - zy⟫_ℝ)
        (⟪target, yNext - zy⟫_ℝ)
        gdiff
        (γ / τ * vyDrop -
          γ / (2 * τ) * ‖yNext - yPrev‖ ^ 2)
        hdual hdual_split_scaled
  have hbilinear :
      -(γ * ⟪A.adjoint yNext, xNext - zx⟫_ℝ) +
          γ * ⟪A xNext, zy⟫_ℝ -
          γ * ⟪A zx, yNext⟫_ℝ +
          γ * ⟪target, yNext - zy⟫_ℝ =
        γ * ⟪A (xNext - xPrev), zy - yNext⟫_ℝ -
          γPrev * ⟪A xLag, zy - yPrev⟫_ℝ -
          γPrev * ⟪A xLag, yPrev - yNext⟫_ℝ := by
    rw [htarget]
    simpa [neg_mul, add_assoc] using
      linearMap_adjoint_lagged_bilinear_cancellation
        (A := A) γ γPrev xPrev xNext xLag zx yPrev yNext zy
  have hsquare :
      -(γ / (2 * η) * ‖xNext - xPrev‖ ^ 2) +
          γ * ((L / (2 * β)) * ‖xNext - xPrev‖ ^ 2) =
        -γ * (1 / (2 * η) - L / (2 * β)) *
          ‖xNext - xPrev‖ ^ 2 := by
    ring
  have hresidual :
      -γ *
          (⟪delta.1, xNext - zx⟫_ℝ +
            ⟪delta.2, yNext - zy⟫_ℝ) =
        -(γ * ⟪δx, xNext - zx⟫_ℝ) -
          γ * ⟪δy, yNext - zy⟫_ℝ := by
    rw [hdelta]
    simp
    ring
  have hgap_rhs :
      γ *
          (⟪grad, xNext - zx⟫_ℝ +
            (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 +
            gdiff +
            ⟪A xNext, zy⟫_ℝ -
            ⟪A zx, yNext⟫_ℝ) ≤
        γ / η * vxDrop +
          γ / τ * vyDrop +
          γ * ⟪A (xNext - xPrev), zy - yNext⟫_ℝ -
          γPrev * ⟪A xLag, zy - yPrev⟫_ℝ -
          γPrev * ⟪A xLag, yPrev - yNext⟫_ℝ -
          γ * (1 / (2 * η) - L / (2 * β)) *
            ‖xNext - xPrev‖ ^ 2 -
          γ / (2 * τ) * ‖yNext - yPrev‖ ^ 2 -
          γ *
            (⟪delta.1, xNext - zx⟫_ℝ +
              ⟪delta.2, yNext - zy⟫_ℝ) := by
    have hlhs :
        γ *
            (⟪grad, xNext - zx⟫_ℝ +
              (L / (2 * β)) * ‖xNext - xPrev‖ ^ 2 +
              gdiff +
              ⟪A xNext, zy⟫_ℝ -
              ⟪A zx, yNext⟫_ℝ) =
          γ * ⟪grad, xNext - zx⟫_ℝ +
            γ * gdiff +
            γ * ((L / (2 * β)) * ‖xNext - xPrev‖ ^ 2) +
            γ * ⟪A xNext, zy⟫_ℝ -
            γ * ⟪A zx, yNext⟫_ℝ := by
      ring
    have hassembled :=
      additive_upper_bound_assembly_from_atoms
        (hlhs := hlhs)
        (hleft := hgrad_bound)
        (hright := hgdiff_bound)
        (hbilinear := hbilinear)
        (hsquare := hsquare)
        (hresidual := hresidual)
    ring_nf at hassembled ⊢
    exact hassembled
  exact hgap_left.trans hgap_rhs


-- Generalization plan (G0):
-- concept/name: recursive generated-driver process regularity from a realized
--   driver supplier and one-step regularity; orig was
--   generatedAxExtensionProcess_measurable_of_realization_variational_stability.
-- generality used: arbitrary sample, state, and generated-driver types with
--   abstract state and driver regularity predicates. The realization is an
--   arbitrary proposition supplying driver regularity from previous-state
--   regularity. No measure, independence, integrability, topology, convexity,
--   smoothness, oracle, or finite-dimensional hypotheses are used.
-- portable call pattern: generated stochastic mirror descent, accelerated
--   gradient, mirror-prox, and accelerated primal-dual process-measurability
--   proofs where a realized oracle sample at time `i + 1` becomes measurable
--   only after the induction hypothesis proves regularity of the state at
--   time `i`, and a generated-driver one-step interface propagates the state.
-- counterargument checked: close to
--   `recursive_process_measurable_of_stream_and_one_step` and
--   `recursive_process_state_regular_of_realized_call`, but neither is
--   alpha-equivalent. The former requires a premeasurable stream independent
--   of the induction hypothesis; the latter is the positive-time displayed-call
--   variant with state index `i` and next state `i + 1`. This theorem exposes
--   the zero-based generated-driver variant with driver index `i + 1`.
-- coverage search: searched `recursiveProcessOneStepMeasurableUpTo`,
--   `recursive process state regular realized call`, and
--   `generated process measurable realization stream one step`; inspected
--   `recursive_process_measurable_of_stream_and_one_step`,
--   `recursive_process_state_regular_of_realized_call`,
--   `recursiveProcessOneStepMeasurableUpTo`, and Mathlib recursive-process
--   measurability APIs. Coverage is partial: existing entries cover fixed
--   stream regularity or positive-time displayed calls, not this generated
--   driver realization induction shape.
-- minimal hypotheses: all already minimal; the proof uses only initial state
--   regularity, the realization-to-driver regularity supplier, the one-step
--   generated-driver interface, and finite-horizon natural-number induction.


/-- A generated-driver recursive process is regular when realized drivers are
regular from previous regular states.

At successor time `i + 1`, the realization supplier may use the induction
hypothesis for `process i` to prove regularity of the generated driver
`driver (i + 1)`. The generated-driver one-step interface then propagates
regularity to the next process state.

Layer: Layer1 | Gap: Level 1 (generated-driver realized recursive-process regularity)
Proof: strong induction on the requested process index; the successor case
  realizes the next driver from the previous state regularity and applies the
  generated-driver one-step regularity interface.
Source: stochastic approximation recursive-process measurability inductions
  and Mathlib natural-number order APIs
Used in: stochastic accelerated primal-dual generated-driver state
  measurability after concrete oracle realization and variational-stability
  selected-prox regularity
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem recursive_process_measurable_of_realized_driver_and_one_step
    {Ω State Driver : Type*}
    (stateRegular : (Ω → State) → Prop)
    (driverRegular : (Ω → Driver) → Prop)
    (process : ℕ → Ω → State)
    (driver : ℕ → Ω → Driver)
    (Realization : Prop)
    (T : ℕ)
    (hinit : stateRegular (process 0))
    (hdriver_of_realization :
      Realization →
        ∀ i, 1 ≤ i → i ≤ T →
          stateRegular (process (i - 1)) →
            driverRegular (driver i))
    (hstep :
      recursiveProcessOneStepMeasurableUpTo
        stateRegular driverRegular process driver T)
    (hrealize : Realization) :
    ∀ i, i ≤ T → stateRegular (process i) := by
  intro i hiT
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          exact hinit
      | succ k =>
          have hprev : stateRegular (process k) :=
            ih k (Nat.lt_succ_self k) (Nat.le_trans (Nat.le_succ k) hiT)
          have hkT : k < T := Nat.lt_of_succ_le hiT
          have hdriver : driverRegular (driver (k + 1)) :=
            hdriver_of_realization hrealize (k + 1) (Nat.succ_pos k) hiT
              (by simpa using hprev)
          exact recursiveProcessOneStepMeasurableUpTo.step hstep hkT hprev hdriver

/-- A gamma-weighted linear target at an accelerated extrapolate decomposes
into the current target plus the lagged forward-difference target.

At time `i = 1`, the base coordinate identity supplies the degenerate branch.
For `2 ≤ i`, the accelerated extrapolate formula and the recurrence
`gamma i * theta i = gamma (i - 1)` convert the momentum term into the lagged
gamma-weighted difference.

Layer: Layer1 | Gap: Level 1 (accelerated extrapolated target decomposition)
Proof: split on `2 ≤ i`; unfold the named accelerated extrapolate in the
  positive branch, use linearity of `A` and the real inner product, then apply
  the gamma recurrence and ring normalization.
Source: Mathlib linear-map and real inner-product algebra for accelerated
  first-order method iterate recurrences
Used in: stochastic accelerated primal-dual descent algebra before combining
  primal and dual prox inequalities at an extrapolated linear-operator query
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem accelerated_extrapolated_target_gamma_decomposition
    {Ω State X Y : Type*}
    [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (process : ℕ → Ω → State)
    (stateX stateXTilde : State → X)
    (theta gamma : ℕ → ℝ) (A : X →ₗ[ℝ] Y)
    (hbase : ∀ ω, stateXTilde (process 0 ω) = stateX (process 0 ω))
    (hstep :
      ∀ {i : ℕ}, 2 ≤ i → ∀ ω,
        stateXTilde (process (i - 1) ω) =
          SOptLib.acceleratedExtrapolateValue theta (i - 1)
            (stateX (process (i - 2) ω)) (stateX (process (i - 1) ω)))
    (hgamma : ∀ {i : ℕ}, 2 ≤ i → gamma i * theta i = gamma (i - 1))
    (i : ℕ) (hi : 1 ≤ i) (ω : Ω) (v : Y) :
    gamma i * ⟪A (stateXTilde (process (i - 1) ω)), v⟫_ℝ =
      gamma i * ⟪A (stateX (process (i - 1) ω)), v⟫_ℝ +
        (if _h2 : 2 ≤ i then
          gamma (i - 1) *
            ⟪A (stateX (process (i - 1) ω) - stateX (process (i - 2) ω)), v⟫_ℝ
        else 0) := by
  by_cases h2 : 2 ≤ i
  · simp only [h2, dif_pos]
    rw [hstep h2 ω]
    simp only [SOptLib.acceleratedExtrapolateValue_def]
    have htheta_idx : i - 1 + 1 = i := by omega
    simp only [htheta_idx]
    rw [map_add, map_smul, inner_add_left, real_inner_smul_left]
    rw [mul_add, ← mul_assoc, hgamma h2]
    ring
  · have hi1 : i = 1 := by omega
    subst i
    simp [hbase]

/-- Transport an accelerated gap recurrence across equal run representations.

If a generated process satisfies the one-step accelerated primal-dual gap
recurrence, and another process representation has the same output, Bregman
boundary scalar, adjacent primal states, next dual state, and Lambda residuals
on the finite window, then the same recurrence holds for the second
representation.

Layer: Layer1 | Gap: Level 1 (accelerated gap recurrence representation transport)
Proof: finite-sum congruence transports the Lambda window, then equality
  rewriting transports the generated recurrence across the output, boundary,
  and adjacent-state equalities.
Source: Mathlib finite-sum congruence and equality rewriting for real
  Hilbert-space norm and inner-product expressions
Used in: stochastic accelerated primal-dual fixed-domain completion transport
  after the generated-process Lemma 4.9 recurrence has been proved
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem accelerated_gap_recurrence_transport_of_output_state_boundary_lambda_eq
    {E F Output Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (beta gamma eta : ℕ → ℝ) (q L : ℝ)
    (A : E → F) (Q : Output → Z → ℝ) (zDual : Z → F)
    (t : ℕ) (z : Z)
    (fixedOutput generatedOutput : Output)
    (fixedBoundary generatedBoundary : ℝ)
    (fixedPrevX fixedNextX generatedPrevX generatedNextX : E)
    (fixedNextY generatedNextY : F)
    (fixedLambda : ℕ → ℝ)
    (generatedLambda : (i : ℕ) → 1 ≤ i → ℝ)
    (hgenerated :
      beta t * gamma t * Q generatedOutput z ≤
        generatedBoundary +
          gamma t * ⟪A (generatedNextX - generatedPrevX), zDual z - generatedNextY⟫_ℝ -
          gamma t * (q / (2 * eta t) - L / (2 * beta t)) *
            ‖generatedNextX - generatedPrevX‖ ^ 2 +
          Finset.sum (Finset.Icc 1 t) (fun i =>
            if hi : 1 ≤ i then generatedLambda i hi else 0))
    (hOutput : fixedOutput = generatedOutput)
    (hBoundary : fixedBoundary = generatedBoundary)
    (hPrevX : fixedPrevX = generatedPrevX)
    (hNextX : fixedNextX = generatedNextX)
    (hNextY : fixedNextY = generatedNextY)
    (hLambda :
      ∀ i, ∀ hi_mem : i ∈ Finset.Icc 1 t,
        fixedLambda i = generatedLambda i (Finset.mem_Icc.mp hi_mem).1) :
    beta t * gamma t * Q fixedOutput z ≤
      fixedBoundary +
        gamma t * ⟪A (fixedNextX - fixedPrevX), zDual z - fixedNextY⟫_ℝ -
        gamma t * (q / (2 * eta t) - L / (2 * beta t)) *
          ‖fixedNextX - fixedPrevX‖ ^ 2 +
        Finset.sum (Finset.Icc 1 t) fixedLambda := by
  classical
  have hsum :
      Finset.sum (Finset.Icc 1 t) fixedLambda =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if hi : 1 ≤ i then generatedLambda i hi else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi_mem
    have hi_pos : 1 ≤ i := (Finset.mem_Icc.mp hi_mem).1
    simpa [hi_pos] using hLambda i hi_mem
  simpa [hOutput, hBoundary, hPrevX, hNextX, hNextY, hsum] using hgenerated

/-- A guarded positive-time sum over `[1, t]` transports to an unguarded sum.

If each guarded summand agrees with an unguarded summand on the finite positive
time window `Finset.Icc 1 t`, then the corresponding finite sums agree.  The
guard branch is discharged from membership in the interval.

Layer: Glue | Gap: Level 0 (positive-window guarded finite-sum transport)
Proof: apply `Finset.sum_congr`; every index in `Finset.Icc 1 t` supplies the
  positive-time proof needed to select the guarded branch.
Source: Mathlib finite-sum congruence and locally finite natural intervals
Used in: stochastic accelerated primal-dual source-boundary residual transport
  from displayed positive-time Lambda summands to unguarded source terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem sum_Icc_guarded_eq_plain_of_eq_on_Icc
    {M : Type*} [AddCommMonoid M]
    (t : ℕ)
    (guarded : (i : ℕ) → 1 ≤ i → M)
    (plain : ℕ → M)
    (h_eq :
      ∀ i, ∀ hi_mem : i ∈ Finset.Icc 1 t,
        guarded i (Finset.mem_Icc.mp hi_mem).1 = plain i) :
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then guarded i hi else 0) =
      Finset.sum (Finset.Icc 1 t) plain := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i hi_mem
  have hi_pos : 1 ≤ i := (Finset.mem_Icc.mp hi_mem).1
  simpa [hi_pos] using h_eq i hi_mem

/-- A generated-driver accelerated primal-dual step is componentwise measurable
from selected-step and oracle-sample measurability.

The theorem abstracts the common accelerated primal-dual dependency chain:
a measurable driver sample and previous dual coordinate produce a measurable
selected dual update; the previous primal coordinate and selected dual update
produce two measurable oracle samples; the selected primal update and
deterministic extrapolation/averaging maps then assemble a measurable
five-coordinate state.

Layer: Layer1 | Gap: Level 1 (selected generated-driver APD step measurability)
Proof: name the next dual coordinate, oracle samples, next primal coordinate,
  and averaged/extrapolated coordinates; apply the supplied measurability
  transformers in dependency order and fold them into the componentwise APD
  state-map predicate.
Source: Mathlib measurable-function composition and product APIs with SOptLib
  accelerated primal-dual iterate-state constructors
Used in: stochastic accelerated primal-dual generated-driver selected-prox
  one-step measurability before recursive process propagation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generatedDriverAcceleratedPrimalDualStep_measurable_of_components
    {Ω E F Driver Grad Adj : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace Driver] [MeasurableSpace Grad] [MeasurableSpace Adj]
    {X : Set E} {Y : Set F}
    (dualStep : ℕ → Driver → {y : F // y ∈ Y} → Ω → {y : F // y ∈ Y})
    (primalStep : ℕ → {x : E // x ∈ X} → Grad → Adj → Ω → {x : E // x ∈ X})
    (gradientSample : ℕ → {x : E // x ∈ X} → Ω → Grad)
    (adjointSample : ℕ → {y : F // y ∈ Y} → Ω → Adj)
    (extrapolate : ℕ → {x : E // x ∈ X} → {x : E // x ∈ X} → E)
    (avgX : ℕ → {x : E // x ∈ X} → {x : E // x ∈ X} → {x : E // x ∈ X})
    (avgY : ℕ → {y : F // y ∈ Y} → {y : F // y ∈ Y} → {y : F // y ∈ Y})
    (t : ℕ)
    {driver : Ω → Driver} {state : Ω → PrimalDualAcceleratedState E F X Y}
    (hdriver : Measurable driver)
    (hstate : primalDualAcceleratedStateMapMeasurable state)
    (hdualStep :
      ∀ {driver' : Ω → Driver} {yPrev : Ω → {y : F // y ∈ Y}},
        Measurable driver' → Measurable yPrev →
          Measurable (fun ω => dualStep t (driver' ω) (yPrev ω) ω))
    (hgradientSample :
      ∀ {xQuery : Ω → {x : E // x ∈ X}},
        Measurable xQuery →
          Measurable (fun ω => gradientSample t (xQuery ω) ω))
    (hadjointSample :
      ∀ {yQuery : Ω → {y : F // y ∈ Y}},
        Measurable yQuery →
          Measurable (fun ω => adjointSample t (yQuery ω) ω))
    (hprimalStep :
      ∀ {xPrev : Ω → {x : E // x ∈ X}} {gSample : Ω → Grad}
          {aSample : Ω → Adj},
        Measurable xPrev → Measurable gSample → Measurable aSample →
          Measurable
            (fun ω => primalStep t (xPrev ω) (gSample ω) (aSample ω) ω))
    (hextrapolate :
      ∀ {xPrev xNext : Ω → {x : E // x ∈ X}},
        Measurable xPrev → Measurable xNext →
          Measurable (fun ω => extrapolate t (xPrev ω) (xNext ω)))
    (havgX :
      ∀ {xBarPrev xNext : Ω → {x : E // x ∈ X}},
        Measurable xBarPrev → Measurable xNext →
          Measurable (fun ω => avgX t (xBarPrev ω) (xNext ω)))
    (havgY :
      ∀ {yBarPrev yNext : Ω → {y : F // y ∈ Y}},
        Measurable yBarPrev → Measurable yNext →
          Measurable (fun ω => avgY t (yBarPrev ω) (yNext ω))) :
    primalDualAcceleratedStateMapMeasurable
      (fun ω =>
        acceleratedPrimalDualStep
          (fun i st sample ω => dualStep i sample st.y ω)
          (fun i st yNext ω =>
            primalStep i st.x
              (gradientSample i st.x ω) (adjointSample i yNext ω) ω)
          extrapolate avgX avgY t (driver ω) (state ω) ω) := by
  let yNext : Ω → {y : F // y ∈ Y} :=
    fun ω => dualStep t (driver ω) (state ω).y ω
  have hyNext : Measurable yNext := by
    exact hdualStep hdriver hstate.2.1
  let gSample : Ω → Grad :=
    fun ω => gradientSample t (state ω).x ω
  have hgSample : Measurable gSample := by
    exact hgradientSample hstate.1
  let aSample : Ω → Adj :=
    fun ω => adjointSample t (yNext ω) ω
  have haSample : Measurable aSample := by
    exact hadjointSample hyNext
  let xNext : Ω → {x : E // x ∈ X} :=
    fun ω => primalStep t (state ω).x (gSample ω) (aSample ω) ω
  have hxNext : Measurable xNext := by
    exact hprimalStep hstate.1 hgSample haSample
  have hxTildeNext :
      Measurable (fun ω => extrapolate t (state ω).x (xNext ω)) := by
    exact hextrapolate hstate.1 hxNext
  have hxBarNext :
      Measurable (fun ω => avgX t (state ω).xBar (xNext ω)) := by
    exact havgX hstate.2.2.1 hxNext
  have hyBarNext :
      Measurable (fun ω => avgY t (state ω).yBar (yNext ω)) := by
    exact havgY hstate.2.2.2.1 hyNext
  simpa [primalDualAcceleratedStateMapMeasurable, acceleratedPrimalDualStep,
    yNext, xNext, gSample, aSample] using
    (show
      Measurable xNext ∧ Measurable yNext ∧
        Measurable (fun ω => avgX t (state ω).xBar (xNext ω)) ∧
        Measurable (fun ω => avgY t (state ω).yBar (yNext ω)) ∧
        Measurable (fun ω => extrapolate t (state ω).x (xNext ω)) from
      ⟨hxNext, hyNext, hxBarNext, hyBarNext, hxTildeNext⟩)

end SOptLib
