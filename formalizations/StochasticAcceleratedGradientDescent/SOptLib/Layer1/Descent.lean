-- SOptLib/Layer1/Descent.lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Probability
import SOptLib.Model.Bregman
import SOptLib.Model.Filtration
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Iterates
import SOptLib.Model.StochasticOracle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Adapted
import SOptLib.Model.Objective
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
