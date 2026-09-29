import SOptLib.Layer0.Objective
-- SOptLib/Layer1/Descent.lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Probability
import SOptLib.Model.Bregman
import SOptLib.Model.Filtration
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Iterates
import SOptLib.Model.Saddle
import SOptLib.Model.StochasticOracle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Adapted
import SOptLib.Model.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Telescope
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
-- concept/name: selected-coordinate inner-product extrapolation split; orig was
--   `proposition56_gradient_extrapolation_step_inner_sum_split_positive_domain`,
--   renamed away from theorem number, positive-domain bookkeeping, and
--   algorithm-local setup names while retaining the genuine extrapolation
--   algebra.
-- generality used: arbitrary finite index type and real inner-product carrier,
--   three coordinate tables, one sampled coordinate, a test vector, and a real
--   scalar; no measure, probability, filtration, independence, integrability,
--   convexity, smoothness, oracle, completeness, or finite-dimensional
--   assumptions are used.
-- portable call pattern: gradient extrapolation, momentum, table-memory
--   coordinate descent, and variance-reduced methods call the same one-step
--   selected-current/lagged-sum split after proving that the current table
--   change has support at the sampled coordinate; the table sequence, sampled
--   coordinate, displacement vector, and scalar coefficient change.
-- counterargument checked: this is algebraic and short, but it is not only a
--   caller-side expression because it packages the recurring combination of
--   inner-product subtraction, scalar extraction, finite-sum distribution, and
--   the sampled-current support identity. It is not covered by Mathlib as a
--   pure rename; Mathlib supplies `inner_sub_right`, `inner_smul_right`, and
--   `Finset.sum_sub_distrib` as separate ingredients.
-- coverage search: searched CATALOG.md/SOptLib/Staging/source for
--   `sum_inner_selected`, `selected_extrapolation`, `inner lagged sum`,
--   `selected current lagged`, and nearby theorem names; closest staged hit was
--   `sum_update_sub_eq_sampled_sub_of_update_off`, which proves the vector
--   current-support collapse but not this inner-product extrapolation split.
--   LeanSearch for finite-sum inner selected-coordinate lagged split returned
--   Mathlib `inner_sum`, `sum_inner`, and `Finset.sum_update_of_mem`, all
--   proof ingredients but not the combined statement. The LSP symbol-search
--   server was unavailable during the check, so direct source/catalog search
--   supplied the SOptLib comparison.
-- minimal hypotheses: weakened from the algorithm setup to `[Fintype iota]`,
--   `[SeminormedAddCommGroup E]`, and `[InnerProductSpace ℝ E]`; no decidable
--   equality, nonemptiness, completeness, finite-dimensionality, or measurable
--   structure is needed.

/-- A selected current table-change split extracts the lagged extrapolation sum.

If the finite sum of current table-change inner products is represented by one
sampled coordinate, then the sum of inner products against
`current - c • lagged` equals the selected current term minus `c` times the
lagged inner-product sum.

Layer: Layer1 | Gap: Level 1 (selected-coordinate extrapolation inner-sum split)
Proof: rewrite each inner product by right-slot subtraction and scalar
  linearity, distribute the finite sum over subtraction, factor the scalar from
  the lagged sum, and substitute the supplied selected-current identity.
Source: Mathlib finite sums and real inner-product bilinearity
Used in: randomized gradient extrapolation and finite-memory coordinate
  methods after a sampled-coordinate table update is collapsed
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation -/
theorem sum_inner_selected_extrapolation_split
    {iota E : Type*} [Fintype iota]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (yPrevPrev yPrev yNext : iota → E) (sampled : iota) (u : E) (c : ℝ)
    (hcurrent :
      Finset.sum Finset.univ (fun i => ⟪u, yNext i - yPrev i⟫_ℝ) =
        ⟪u, yNext sampled - yPrev sampled⟫_ℝ) :
    Finset.sum Finset.univ
        (fun i =>
          ⟪u, (yNext i - yPrev i) - c • (yPrev i - yPrevPrev i)⟫_ℝ) =
      ⟪u, yNext sampled - yPrev sampled⟫_ℝ -
        c * Finset.sum Finset.univ
          (fun i => ⟪u, yPrev i - yPrevPrev i⟫_ℝ) := by
  classical
  calc
    Finset.sum Finset.univ
        (fun i =>
          ⟪u, (yNext i - yPrev i) - c • (yPrev i - yPrevPrev i)⟫_ℝ) =
      Finset.sum Finset.univ
        (fun i =>
          ⟪u, yNext i - yPrev i⟫_ℝ -
            c * ⟪u, yPrev i - yPrevPrev i⟫_ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [inner_sub_right, inner_smul_right]
    _ =
      Finset.sum Finset.univ
          (fun i => ⟪u, yNext i - yPrev i⟫_ℝ) -
        c * Finset.sum Finset.univ
          (fun i => ⟪u, yPrev i - yPrevPrev i⟫_ℝ) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [← Finset.mul_sum]
    _ =
      ⟪u, yNext sampled - yPrev sampled⟫_ℝ -
        c * Finset.sum Finset.univ
          (fun i => ⟪u, yPrev i - yPrevPrev i⟫_ℝ) := by
        rw [hcurrent]

-- Generalization plan (G0):
-- concept/name: relaxed-memory refresh component descent from a smoothness-gap
--   certificate; orig was relaxed_memory_component_descent_of_smooth_gap.
-- generality used: arbitrary real inner-product additive group `E`; no measure,
--   finite index, generated process, or carrier set is needed once the caller
--   supplies the pointwise convex-support and smoothness-gap inequalities.
-- portable call pattern: randomized coordinate, finite-memory, and
--   variance-reduced accelerated proofs call this before summing components;
--   the objective, gradient, relaxation parameter, proposal, memory point,
--   comparator, and smoothness-gap certificate vary while the conclusion shape
--   stays fixed.
-- counterargument checked: not paper-local traceability, because the theorem
--   packages the reusable algebra connecting a refreshed memory point with
--   convex support and smoothness-gap certificates; not a one-line wrapper
--   around Mathlib because the conclusion combines three independent premises.
-- coverage search: searched CATALOG/SOptLib/Staging for relaxedMemory,
--   component descent, smooth gap, and Baillon-Haddad; relevant partial hits
--   were relaxedMemoryRefreshPoint_solve,
--   carrier_baillon_haddad_gap_of_affineDirectionDualNorm_lipschitz, and
--   carrier_baillon_haddad_gap_of_nonneg_lipschitz. LeanSearch for "inner
--   product convex support smooth gap descent inequality relaxed memory point"
--   found no Mathlib theorem with this combined refresh-descent shape.
-- minimal hypotheses: global convexity and smoothness were reduced to the two
--   pointwise scalar certificates and the single refresh identity.

/-- A relaxed-memory refresh point satisfies component descent from a
smoothness-gap certificate.

If `a` is the relaxed memory point solving
`xNext = (1 + tau) • a - tau • prev`, convex support at `a` bounds
`f a - f x`, and a smoothness-gap certificate bounds the stale-memory
linearization error, then the standard per-component relaxed-memory descent
inequality follows.

Layer: Layer1 | Gap: Level 1 (relaxed-memory component descent assembly)
Proof: scale the smoothness-gap certificate by the nonnegative relaxation
  parameter, rewrite the refresh identity inside the inner product, and collect
  the convex-support and smoothness terms by ordered-ring arithmetic.
Source: convex first-order support algebra, smoothness-gap descent estimates,
  and Mathlib real inner-product linearity APIs
Used in: randomized finite-memory component descent before summing refreshed
  component objectives and smoothness-gap penalties
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem relaxedMemoryRefresh_component_descent_of_smooth_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (tau : ℝ) (xNext prev x a : E) (gap : ℝ)
    (htau_nonneg : 0 ≤ tau)
    (hconv : f a - f x ≤ ⟪a - x, grad a⟫_ℝ)
    (hsmooth : gap ≤ f prev - f a - ⟪grad a, prev - a⟫_ℝ)
    (hrefresh : xNext = (1 + tau) • a - tau • prev) :
    (1 + tau) * f a - f x ≤
      tau * f prev + ⟪xNext - x, grad a⟫_ℝ - tau * gap := by
  have hsmooth_scaled :
      tau * gap ≤
        tau * (f prev - f a - ⟪grad a, prev - a⟫_ℝ) :=
    mul_le_mul_of_nonneg_left hsmooth htau_nonneg
  have hsolve :
      xNext - x = a - x + tau • (a - prev) := by
    calc
      xNext - x = ((1 + tau) • a - tau • prev) - x := by
        rw [hrefresh]
      _ = a - x + tau • (a - prev) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add]
        module
  have hinner_x :
      ⟪xNext - x, grad a⟫_ℝ =
        ⟪a - x, grad a⟫_ℝ + tau * ⟪a - prev, grad a⟫_ℝ := by
    rw [hsolve]
    simp [inner_add_left, inner_smul_left]
  have hcomponent' :
      f a - f x + tau * f a ≤
        ⟪a - x, grad a⟫_ℝ +
          tau * (f prev - ⟪grad a, prev - a⟫_ℝ - gap) := by
    have htmp :
        tau * f a ≤
          tau * (f prev - ⟪grad a, prev - a⟫_ℝ - gap) := by
      nlinarith [hsmooth_scaled]
    nlinarith [hconv, htmp]
  have hrewrite :
      ⟪a - x, grad a⟫_ℝ +
          tau * (f prev - ⟪grad a, prev - a⟫_ℝ - gap) =
        tau * f prev + ⟪xNext - x, grad a⟫_ℝ - tau * gap := by
    rw [hinner_x]
    have hinner_flip :
        ⟪grad a, prev - a⟫_ℝ = -⟪a - prev, grad a⟫_ℝ := by
      rw [real_inner_comm]
      simp [sub_eq_add_neg, inner_add_left]
    rw [hinner_flip]
    ring
  have hleft :
      (1 + tau) * f a - f x = f a - f x + tau * f a := by ring
  rw [hleft]
  exact hcomponent'.trans_eq hrewrite

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: stale memory residual square splits into initial/no-hit and
--   zero/hit branches; orig was
--   `stale_gradient_error_pointwise_split_positive_domain`, renamed away from
--   RGEM-specific gradient and positive-eta setup wording while exposing the
--   reusable selected-coordinate memory residual split.
-- generality used: arbitrary sample-path type, coordinate type, additive
--   group-valued memory space, component target map, point-memory table,
--   value-memory table, real-valued residual size, and initial point; no
--   measure, independence, filtration, convexity, smoothness, oracle,
--   topology, norm, inner-product, finite coordinate, or finite-dimensional
--   assumptions are used, except the residual size must vanish at zero.
-- portable call pattern: finite-memory coordinate SGD, SAG/SAGA-style table
--   refreshes, randomized block mirror descent, and stale-memory stochastic
--   approximation call this pointwise step after proving that an unvisited
--   coordinate still stores the initial point and zero value memory, while a
--   visited coordinate stores the current target value; the sample stream,
--   target map, memory tables, initial point, and residual size change while
--   the initial-or-zero split stays fixed.
-- counterargument checked: not paper-local traceability because the theorem
--   has no setup fields, theorem numbers, gradient notation, or RGEM acronym;
--   not a caller-side expression because it packages the recurring branch
--   rewrite boundary consumed by expectation-level stale-memory estimates.
--   Existing staged entries cover the history invariant and the expectation
--   assembly separately, but not this pointwise residual-square bridge.
-- coverage search: searched CATALOG/SOptLib/Staging/project for `stale memory
--   residual`, `no hit initial zero`, `selected coordinate gradient memory`,
--   and `previous hit residual split`; relevant hits were
--   `selectedCoordinateGradientMemory_characterization`,
--   `selectedCoordinateRefresh_branch_identities`, and
--   `selectedStaleMemoryResidual_expectation_eq_geometric_initial`, which are
--   proof ingredients or downstream consumers rather than this branch split.
--   LeanSearch for a no-previous-sample memory residual split returned only
--   unrelated zero-memory, affine-coordinate, and alternating-map zero lemmas.
-- minimal hypotheses: the original generated-process facts are replaced by
--   exactly the two no-hit branch equalities, the hit-branch memory equality,
--   and the zero-residual-size fact used by the proof; the norm-like residual
--   is an arbitrary function `E -> Real`, and `E` only needs additive-group
--   subtraction laws.

/-- A stale memory residual is initial on no-hit paths and zero after a hit.

If a coordinate has not appeared in the one-based strict prefix, the point
memory is still the initial point and the value memory is zero; if it has
appeared, the value memory equals the current target value. Under those branch
facts, the squared residual size is the initial residual on the no-hit event
and zero on the hit event.

Layer: Layer1 | Gap: Level 1 (stale-memory residual pointwise branch split)
Proof: split on the strict-prefix hit event, rewrite by the supplied point- and
  value-memory branch identities, and simplify `x - 0` and `x - x`.
Source: Mathlib propositional case-splitting, natural-number interval
  predicates, and additive-group subtraction simplification APIs
Used in: randomized coordinate-memory stochastic methods before converting a
  pointwise stale residual split into a selected-coordinate expectation bound
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem staleMemoryResidual_sq_eq_initial_or_zero
    {Ω I E : Type*} [AddGroup E]
    (sample : ℕ → Ω → I) (target : I → E → E)
    (xmem ymem : ℕ → Ω → I → E) (N : E → ℝ) (x0 : E)
    (t : ℕ) (ω : Ω) (i : I)
    (hN_zero : N 0 = 0)
    (hx_no :
      (¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i) →
        xmem (t - 1) ω i = x0)
    (hy_no :
      (¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i) →
        ymem (t - 1) ω i = 0)
    (hy_hit :
      (∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i) →
        ymem (t - 1) ω i = target i (xmem (t - 1) ω i)) :
    N (target i (xmem (t - 1) ω i) - ymem (t - 1) ω i) ^ 2 =
      (by
        classical
        exact
          if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i then
            N (target i x0) ^ 2
          else
            0) := by
  classical
  by_cases hno : ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i
  · have hx := hx_no hno
    have hy := hy_no hno
    rw [if_pos hno, hx, hy]
    simp
  · have hex : ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i := not_not.mp hno
    have hy := hy_hit hex
    rw [if_neg hno, hy]
    simp [hN_zero]

end SOptLib


-- Batch 2 promoted from Staging/integral_update_displacement_sq_eq_mul_integral_direction_sq.lean
-- Generalization plan (G0):
-- concept/name: integral squared displacement scaling from an affine update; orig was expectedDisplacementSq_succ_eq_gamma_sq_mul_stochasticGradientMappingSq
-- generality used: arbitrary measurable sample space, arbitrary measure, and a real normed additive group/vector space; no probability, filtration, convexity, smoothness, or oracle assumptions
-- portable call pattern: SGD, stochastic mirror descent, variance-reduced, proximal-gradient, and accelerated proofs can call this after proving `xNext - x = -gamma • direction`; the process, measure, direction, and stepsize vary while the integral identity is unchanged
-- counterargument checked: not paper-local traceability because the same update-to-L2-displacement conversion recurs across stochastic-optimization descent and variance proofs; not a pure wrapper around a named Mathlib theorem because Mathlib supplies scalar integral and norm APIs separately but not this assembled update identity
-- coverage search: searched SOptLib/catalog and source for `displacement`, `integral norm square`, `gamma direction`, and `integral norm smul squared`; relevant hits were martingale L2 identities and recursive variance bounds, but none states the pointwise affine-update squared-displacement integral equality; LeanSearch returned scalar Bochner integral lemmas such as `MeasureTheory.integral_smul`, which are only component APIs
-- minimal hypotheses: pointwise update equality only; measurability and integrability hypotheses are unnecessary for Bochner integral congruence and constant multiplication

open MeasureTheory

/-- The squared displacement integral of an affine update is the squared stepsize
times the squared direction integral.

If a process step satisfies `xNext ω - x ω = -gamma • g ω` pointwise, then its
expected squared displacement is `gamma^2` times the expected squared direction.

Layer: Layer1 | Gap: Level 1 (affine-update squared-displacement integral scaling)
Proof: rewrite the Bochner integral of a constant multiple, use pointwise
  integral congruence, and reduce the integrand by `norm_smul`, `norm_neg`, and
  real squared-absolute-value algebra.
Source: Mathlib Bochner integral scalar-linearity and normed real vector-space
  scalar norm APIs
Used in: variance-reduced stochastic mirror descent displacement variance
  substitution after the generated prox update
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem integral_update_displacement_sq_eq_mul_integral_direction_sq
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (x xNext g : Ω → E) (gamma : ℝ)
    (h_update : ∀ ω, xNext ω - x ω = -(gamma • g ω)) :
    (∫ ω, ‖xNext ω - x ω‖ ^ 2 ∂μ) =
      gamma ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  have hdist_sq :
      ‖xNext ω - x ω‖ ^ 2 = gamma ^ 2 * ‖g ω‖ ^ 2 := by
    calc
      ‖xNext ω - x ω‖ ^ 2 = ‖gamma • g ω‖ ^ 2 := by
        rw [h_update ω, norm_neg]
      _ = gamma ^ 2 * ‖g ω‖ ^ 2 := by
        rw [norm_smul]
        simp [Real.norm_eq_abs, mul_pow, sq_abs]
  simp [hdist_sq]


-- Batch 2 promoted from Staging/smooth_descent_of_approx_variational_step_with_estimator_error_raw.lean
-- Generalization plan (G0):
-- concept/name: smooth_descent_of_approx_variational_step_with_estimator_error_raw
--   exposes the pre-Young smooth descent algebra for an approximate
--   variational step with an estimator residual inner product.
-- generality used: arbitrary real inner-product seminormed additive group;
--   no measure, convexity, or differentiability classes are used after the
--   caller supplies the pointwise smooth upper bound and variational inequality.
-- portable call pattern: proximal-gradient, mirror-descent, and
--   variance-reduced one-step proofs instantiate f, grad, x, y, G, gamma, eta,
--   and L, then absorb or cancel the residual inner product by a later budget.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   the existing absorbed SOptLib theorem applies Young's inequality, while
--   this raw form leaves the residual inner product available to share a
--   separate scalar budget or martingale cancellation.
-- coverage search: searched SOptLib catalog and full signatures for
--   `smooth_descent_of_approx_variational_step_with_estimator_error`,
--   `one_step_descent_absorb_residual_cross_term`, and Glue Young lemmas;
--   Mathlib LeanSearch for smooth descent with approximate-gradient residuals
--   found only gradient calculus facts. Coverage is partial, not full.
-- minimal hypotheses: global smoothness and prox optimality are reduced to the
--   two pointwise inequalities used by the proof; no positivity hypothesis on
--   gamma or L is needed for the raw algebraic rearrangement.

/-- A smooth upper bound and approximate variational descent give raw
estimator-residual descent.

The conclusion stops before Young absorption: the estimator error remains as
the inner product `-⟪G - grad x, y - x⟫_ℝ`, so callers can absorb, cancel, or
budget that term using information not present in the smooth/prox step.

Layer: Layer1 | Gap: Level 1 (raw approximate prox-step estimator residual descent)
Proof: write the true gradient as the estimator minus its residual, split the
  inner product by linearity, insert the approximate variational descent bound,
  and finish by ordered-ring arithmetic.
Source: smooth first-order descent calculus in real Hilbert spaces and real
  ordered-ring inequality algebra
Used in: nonconvex variance-reduced mirror descent one-step descent before
  estimator residual inner-product budget absorption
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem smooth_descent_of_approx_variational_step_with_estimator_error_raw
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (x y G : E) (gamma eta L : ℝ)
    (hsmooth :
      f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2)
    (hproj :
      ⟪G, y - x⟫_ℝ ≤ eta - gamma⁻¹ * ‖y - x‖ ^ 2) :
    f y ≤
      f x - (gamma⁻¹ - L / 2) * ‖y - x‖ ^ 2 -
        ⟪G - grad x, y - x⟫_ℝ + eta := by
  let delta : E := G - grad x
  have hgrad : grad x = G - delta := by
    simp [delta]
  have hinner_decomp :
      ⟪grad x, y - x⟫_ℝ =
        ⟪G, y - x⟫_ℝ - ⟪delta, y - x⟫_ℝ := by
    rw [hgrad]
    simp [inner_sub_left]
  nlinarith [hsmooth, hproj, hinner_decomp]

namespace SOptLib

/-- A one-based line-search update is no worse than the trial point with weight
`2 / (t + 1)`.

If a positive one-based successor is given by an update map, that update is the
segment point selected by a stepsize, and the selected segment point minimizes
the objective over all admissible segment weights, then the next iterate is
bounded by the standard trial segment point with weight `2 / (t + 1)`.

Layer: Layer1 | Gap: Level 1 (one-based line-search trial comparison)
Proof: rewrite the successor iterate through the update rule, rewrite the
  update as the selected line-search segment point, and apply the line-search
  comparison at the admissible weight `2 / (t + 1)`.
Source: Conditional-gradient and Frank-Wolfe line-search algebra with Mathlib
  natural-number cast and interval APIs
Used in: stochastic conditional-gradient sliding inner-loop descent when
  comparing the selected CndG update against Lan's trial weight
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem one_based_line_search_iterate_succ_le_two_div
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (obj : E -> E -> ℝ) (iterate : Nat -> E) (update oracle : E -> E)
    (stepsize : E -> ℝ)
    (hsucc : ∀ ⦃t : Nat⦄, 1 <= t -> iterate (t + 1) = update (iterate t))
    (hupdate :
      ∀ x : E, update x = (1 - stepsize x) • x + stepsize x • oracle x)
    (hlineSearch :
      ∀ (x : E) (a : ℝ), a ∈ Set.Icc (0 : ℝ) 1 ->
        obj x ((1 - stepsize x) • x + stepsize x • oracle x) ≤
          obj x ((1 - a) • x + a • oracle x))
    {t : Nat} (ht : 1 <= t) :
    let ut := iterate t
    let v := oracle ut
    let lam := (2 : ℝ) / ((t + 1 : Nat) : ℝ)
    obj ut (iterate (t + 1)) ≤ obj ut ((1 - lam) • ut + lam • v) := by
  let ut := iterate t
  let v := oracle ut
  let lam := (2 : ℝ) / ((t + 1 : Nat) : ℝ)
  change obj ut (iterate (t + 1)) ≤ obj ut ((1 - lam) • ut + lam • v)
  rw [hsucc ht, hupdate ut]
  exact hlineSearch ut lam
    (by
      simpa [lam, Nat.succ_eq_add_one] using
        (SOptLib.two_div_nat_cast_mem_Icc (K := ℝ) (Nat.succ t)
          (Nat.succ_le_succ ht)))

/-- A line-search gap decrease with a diameter curvature budget gives a residual recursion.

If the next line-search value is bounded by the current value plus a quadratic
coefficient minus `gap * lambda`, the gap controls the current residual, and
the quadratic coefficient is bounded by half a curvature-diameter budget, then
the next residual satisfies the standard `(1 - lambda)` recurrence.

Layer: Layer1 | Gap: Level 1 (line-search gap residual recurrence)
Proof: multiply the gap-controls-residual inequality by the nonnegative
  stepsize, multiply the diameter coefficient bound by `lambda^2`, and close
  the scalar ordered-ring inequality.
Source: Conditional-gradient and Frank-Wolfe line-search recurrence algebra
  with Mathlib ordered-ring arithmetic
Used in: stochastic conditional-gradient sliding inner-loop residual recursion
  after the line-search gap-quadratic estimate and feasible-set diameter bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem lineSearchGap_residual_recursion_of_diameter
    {E : Type*}
    (phi : ℕ → E → ℝ) (iterate : ℕ → E) (x : E)
    (Delta gap lam : ℕ → ℝ) (A : ℝ) {t : ℕ}
    (hstep :
      phi t (iterate (t + 1)) ≤
        phi t (iterate t) + Delta t * lam t ^ 2 - gap t * lam t)
    (hgap : phi t (iterate t) - phi t x ≤ gap t)
    (hlam_nonneg : 0 ≤ lam t)
    (hdiam : Delta t ≤ A / 2) :
    phi t (iterate (t + 1)) - phi t x ≤
      (1 - lam t) * (phi t (iterate t) - phi t x) +
        (A / 2) * lam t ^ 2 := by
  have hgap_mul :
      (phi t (iterate t) - phi t x) * lam t ≤ gap t * lam t := by
    exact mul_le_mul_of_nonneg_right hgap hlam_nonneg
  have hdiam_mul : Delta t * lam t ^ 2 ≤ (A / 2) * lam t ^ 2 := by
    exact mul_le_mul_of_nonneg_right hdiam (sq_nonneg (lam t))
  nlinarith [hstep, hgap_mul, hdiam_mul]

/-- A line-search gap-quadratic step gives a Wolfe-gap drop after a curvature
budget replacement.

If the next scalar value is bounded by the current value plus a curvature term
minus `gap * lambda`, and the curvature term is bounded by the chosen
curvature budget, then `lambda * gap` is bounded by the scalar drop plus that
budget.

Layer: Layer1 | Gap: Level 1 (line-search Wolfe-gap drop with curvature budget)
Proof: substitute the curvature-term bound into the one-step line-search
  inequality and rearrange the real scalar terms.
Source: Conditional-gradient and Frank-Wolfe line-search descent algebra with
  Mathlib ordered-ring arithmetic
Used in: stochastic conditional-gradient sliding inner-loop weighted Wolfe-gap
  summation after the gap-quadratic step and feasible-set diameter bound
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem line_search_wolfe_gap_one_step_le_phi_drop_add_curvature
    (phi gap lam : ℕ → ℝ) (A : ℝ) {j : ℕ} {curvatureTerm : ℝ}
    (hstep : phi (j + 1) ≤ phi j + curvatureTerm - gap j * lam j)
    (hcurvature : curvatureTerm ≤ (A / 2) * lam j ^ 2) :
    lam j * gap j ≤ phi j - phi (j + 1) + (A / 2) * lam j ^ 2 := by
  nlinarith

set_option maxHeartbeats 800000 in
/-- A pathwise stochastic conditional-gradient sliding one-step descent follows
from local model, projection, residual, and averaging facts.

The theorem isolates the deterministic algebra behind the stochastic recursion:
an averaged smooth upper model is combined with a lower model at the previous and
comparison points, an approximate projection distance drop, and a Young bound on
the estimator residual.

Layer: Layer1 | Gap: Level 1 (conditional-gradient sliding pathwise descent assembly)
Proof: substitute the local-model comparison and projection distance-drop
  inequalities into the smooth averaged model, then split the residual through
  the previous iterate and complete the square with the positive gap
  `beta - L * gamma`.
Source: Lan conditional-gradient sliding one-step model algebra, Mathlib real
  Hilbert-space inner-product identities, and ordered-field Young inequality
Used in: stochastic conditional-gradient sliding one-step recursion before
  martingale cancellation, variance control, and finite-window telescoping
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem stochastic_cgs_one_step_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f model : E → ℝ)
    (xPrev xNext yPrev yNext z compare delta batchGradient : E)
    (gamma beta eta L : ℝ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (hgap : 0 < beta - L * gamma)
    (hsmooth :
      f yNext ≤ model yNext + L / 2 * ‖yNext - z‖ ^ 2)
    (hmodel_y :
      model yNext = (1 - gamma) * model yPrev + gamma * model xNext)
    (hyz :
      yNext - z = gamma • (xNext - xPrev))
    (hlower_prev :
      model yPrev ≤ f yPrev)
    (hproj :
      ⟪batchGradient, xNext - compare⟫_ℝ ≤
        eta + beta / 2 *
          (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2 -
            ‖xNext - xPrev‖ ^ 2))
    (hmodel_decomp :
      model xNext =
        model compare + ⟪batchGradient, xNext - compare⟫_ℝ +
          ⟪delta, compare - xNext⟫_ℝ)
    (hlower_compare :
      model compare ≤ f compare) :
    f yNext ≤
      (1 - gamma) * f yPrev +
        gamma * f compare +
          beta * gamma / 2 *
            (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2) +
          eta * gamma +
          gamma * ⟪delta, compare - xPrev⟫_ℝ +
          gamma * ‖delta‖ ^ 2 / (2 * (beta - L * gamma)) := by
  let d : E := xNext - xPrev
  let gap : ℝ := beta - L * gamma
  have h_one_sub_nonneg : 0 ≤ 1 - gamma := sub_nonneg.mpr hgamma_le_one
  have hgap_pos : 0 < gap := by simpa [gap] using hgap
  have hnorm_yz :
      ‖yNext - z‖ ^ 2 = gamma ^ 2 * ‖d‖ ^ 2 := by
    rw [hyz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hgamma_nonneg]
    simp [d]
    ring
  have hprev_scaled :
      (1 - gamma) * model yPrev ≤ (1 - gamma) * f yPrev :=
    mul_le_mul_of_nonneg_left hlower_prev h_one_sub_nonneg
  have hmodel_x_le :
      model xNext ≤
        f compare + eta +
          beta / 2 *
            (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2 - ‖d‖ ^ 2) +
          ⟪delta, compare - xNext⟫_ℝ := by
    dsimp [d]
    nlinarith [hmodel_decomp, hproj, hlower_compare]
  have hmodel_x_scaled :
      gamma * model xNext ≤
        gamma *
          (f compare + eta +
            beta / 2 *
              (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2 - ‖d‖ ^ 2) +
            ⟪delta, compare - xNext⟫_ℝ) :=
    mul_le_mul_of_nonneg_left hmodel_x_le hgamma_nonneg
  have hdescent_model :
      f yNext ≤
        (1 - gamma) * f yPrev +
          gamma *
            (f compare + eta +
              beta / 2 *
                (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2 - ‖d‖ ^ 2) +
              ⟪delta, compare - xNext⟫_ℝ) +
          L / 2 * (gamma ^ 2 * ‖d‖ ^ 2) := by
    calc
      f yNext ≤ model yNext + L / 2 * ‖yNext - z‖ ^ 2 := hsmooth
      _ =
          ((1 - gamma) * model yPrev + gamma * model xNext) +
            L / 2 * (gamma ^ 2 * ‖d‖ ^ 2) := by
            rw [hmodel_y, hnorm_yz]
      _ ≤
          (1 - gamma) * f yPrev +
            gamma *
              (f compare + eta +
                beta / 2 *
                  (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2 - ‖d‖ ^ 2) +
                ⟪delta, compare - xNext⟫_ℝ) +
            L / 2 * (gamma ^ 2 * ‖d‖ ^ 2) := by
            nlinarith [hprev_scaled, hmodel_x_scaled]
  have hpre_young :
      f yNext ≤
        (1 - gamma) * f yPrev +
          gamma * f compare +
          beta * gamma / 2 *
            (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2) +
          eta * gamma +
          gamma *
            (⟪delta, compare - xNext⟫_ℝ -
              gap / 2 * ‖d‖ ^ 2) := by
    dsimp [gap]
    nlinarith [hdescent_model]
  have hyoung :
      ⟪delta, compare - xNext⟫_ℝ - gap / 2 * ‖d‖ ^ 2 ≤
        ⟪delta, compare - xPrev⟫_ℝ + ‖delta‖ ^ 2 / (2 * gap) := by
    have hsplit : compare - xNext = (compare - xPrev) + -d := by
      simp [d]
    have hinner_abs : ⟪delta, -d⟫_ℝ ≤ ‖delta‖ * ‖d‖ := by
      calc
        ⟪delta, -d⟫_ℝ ≤ |⟪delta, -d⟫_ℝ| := le_abs_self _
        _ ≤ ‖delta‖ * ‖-d‖ := abs_real_inner_le_norm delta (-d)
        _ = ‖delta‖ * ‖d‖ := by simp
    have hscalar :
        ‖delta‖ * ‖d‖ - gap / 2 * ‖d‖ ^ 2 ≤
          ‖delta‖ ^ 2 / (2 * gap) := by
      have hsq : 0 ≤ (‖delta‖ - gap * ‖d‖) ^ 2 := sq_nonneg _
      have hden : 0 < 2 * gap := by positivity
      rw [le_div_iff₀ hden]
      nlinarith
    rw [hsplit, inner_add_right]
    nlinarith
  have hyoung_scaled :
      gamma *
          (⟪delta, compare - xNext⟫_ℝ - gap / 2 * ‖d‖ ^ 2) ≤
        gamma *
          (⟪delta, compare - xPrev⟫_ℝ + ‖delta‖ ^ 2 / (2 * gap)) :=
    mul_le_mul_of_nonneg_left hyoung hgamma_nonneg
  calc
    f yNext ≤
        (1 - gamma) * f yPrev +
          gamma * f compare +
          beta * gamma / 2 *
            (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2) +
          eta * gamma +
          gamma *
            (⟪delta, compare - xNext⟫_ℝ - gap / 2 * ‖d‖ ^ 2) := hpre_young
    _ ≤
        (1 - gamma) * f yPrev +
          gamma * f compare +
          beta * gamma / 2 *
            (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2) +
          eta * gamma +
          gamma *
            (⟪delta, compare - xPrev⟫_ℝ + ‖delta‖ ^ 2 / (2 * gap)) := by
          nlinarith [hyoung_scaled]
    _ =
        (1 - gamma) * f yPrev +
          gamma * f compare +
          beta * gamma / 2 *
            (‖xPrev - compare‖ ^ 2 - ‖xNext - compare‖ ^ 2) +
          eta * gamma +
          gamma * ⟪delta, compare - xPrev⟫_ℝ +
          gamma * ‖delta‖ ^ 2 / (2 * (beta - L * gamma)) := by
          dsimp [gap]
          ring

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

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: primal-dual saddle-gap recursion from primal descent, summed
--   dual descent, and coupling mismatch; orig was
--   lemma55_pointwise_gap_hat_form, renamed away from lemma numbering and the
--   RPDG hat notation.
-- generality used: finite coordinate family, arbitrary primal carrier `X`,
--   dependent coordinate dual carriers `Y i`, and a real Hilbert ambient space
--   for the linear coupling. No measure, filtration, convexity, smoothness,
--   oracle, update, Bregman, completeness, or finite-dimensional assumptions
--   are used once the pointwise primal and summed dual descent inequalities
--   have been proved.
-- portable call pattern: primal-dual mirror descent, mirror-prox, block
--   coordinate saddle methods, and stochastic primal-dual gradient proofs call
--   this after separately proving a primal prox/descent inequality and a
--   coordinatewise dual prox/descent inequality; the carriers, penalties,
--   iterates, and right-hand descent budgets change while the saddle-gap
--   conclusion keeps the same shape.
-- counterargument checked: this is more than paper traceability because it is
--   the reusable algebraic boundary that combines two descent certificates
--   with the linear saddle coupling. It is not a one-line wrapper around
--   Mathlib order lemmas, and it avoids the over-abstraction trap by using the
--   existing named `saddleGap` and `linearCoupledSaddleValue` model objects
--   instead of a formula-equality hypothesis for the gap.
-- coverage search: searched CATALOG/SOptLib/Staging for "saddle gap",
--   "primal dual descent", "mismatch", and "pointwise saddle gap"; relevant
--   partial hits were `SOptLib.saddleGap`,
--   `SOptLib.linearCoupledSaddleValue`, and
--   `SOptLib.saddleGap_weightedProductOutput_le_weighted_sum`. LeanSearch for
--   "saddle gap bounded by primal descent dual descent and mismatch" returned
--   Mathlib `IsSaddlePointOn` facts, which cover saddle predicates but not this
--   descent-certificate assembly.
-- minimal hypotheses: dropped all paper setup fields, probability objects,
--   update equations, Bregman formulas, and finite-dimensional assumptions;
--   retained only the two pointwise descent inequalities needed by the proof.

/-- A separable linearly coupled saddle gap is bounded by primal and dual
descent certificates plus the coupling mismatch.

The primal descent certificate controls the regularizer and the current
coordinate predictor, while the summed dual certificate controls the separable
dual penalties and the prediction point. The remaining terms are exactly the
three inner-product mismatch terms between the primal predictor, current primal
point, reference primal point, and the two coordinate dual predictions.

Layer: Layer1 | Gap: Level 1 (primal-dual descent and mismatch saddle-gap assembly)
Proof: expand the named saddle gap and linearly coupled saddle value, rewrite
  the summed dual inner products as one inner product against the coordinate
  sum, then combine the supplied primal and dual descent inequalities by real
  ordered-ring arithmetic.
Source: convex-analysis saddle-gap algebra, separable Fenchel-dual objectives,
  and Mathlib finite-sum inner-product identities
Used in: random primal-dual gradient one-step pointwise saddle-gap recursion
  after primal and coordinate-dual prox descent certificates
Book citation: book/FOML/RandomPrimalDualGradient.json#/setup/gap_function
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem saddle_gap_le_of_primal_dual_descent_and_mismatch
    {ι X E : Type*} {Y : ι → Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (evalY : ∀ i, Y i → E)
    (regularizer : X → ℝ) (dualPenalty : ∀ i, Y i → ℝ)
    (xCur xRef : X) (xTilde : E)
    (yTilde : ι → E) (yHat yRef : ∀ i, Y i)
    (primalR dualR : ℝ)
    (hprimal :
      ⟪evalX xCur - evalX xRef, ∑ i : ι, yTilde i⟫_ℝ +
          regularizer xCur - regularizer xRef ≤
        primalR)
    (hdual :
      (∑ i : ι,
        (⟪-xTilde, evalY i (yHat i) - evalY i (yRef i)⟫_ℝ +
          dualPenalty i (yHat i) - dualPenalty i (yRef i))) ≤
        dualR) :
    saddleGap
        (linearCoupledSaddleValue evalX regularizer
          (fun y : (∀ i, Y i) => ∑ i : ι, evalY i (y i))
          (fun y : (∀ i, Y i) => ∑ i : ι, dualPenalty i (y i)))
        (xCur, yHat) (xRef, yRef) ≤
      primalR + dualR +
        (⟪xTilde,
            (∑ i : ι, evalY i (yHat i)) -
              ∑ i : ι, evalY i (yRef i)⟫_ℝ -
          ⟪evalX xCur,
            (∑ i : ι, yTilde i) -
              ∑ i : ι, evalY i (yRef i)⟫_ℝ +
          ⟪evalX xRef,
            (∑ i : ι, yTilde i) -
              ∑ i : ι, evalY i (yHat i)⟫_ℝ) := by
  classical
  let primalL : ℝ :=
    ⟪evalX xCur - evalX xRef, ∑ i : ι, yTilde i⟫_ℝ +
      regularizer xCur - regularizer xRef
  let dualL : ℝ :=
    ∑ i : ι,
      (⟪-xTilde, evalY i (yHat i) - evalY i (yRef i)⟫_ℝ +
        dualPenalty i (yHat i) - dualPenalty i (yRef i))
  let mismatch : ℝ :=
    ⟪xTilde,
      (∑ i : ι, evalY i (yHat i)) -
        ∑ i : ι, evalY i (yRef i)⟫_ℝ -
      ⟪evalX xCur,
        (∑ i : ι, yTilde i) -
          ∑ i : ι, evalY i (yRef i)⟫_ℝ +
      ⟪evalX xRef,
        (∑ i : ι, yTilde i) -
          ∑ i : ι, evalY i (yHat i)⟫_ℝ
  have hp : primalL ≤ primalR := by
    simpa [primalL] using hprimal
  have hd : dualL ≤ dualR := by
    simpa [dualL] using hdual
  have hdualInner :
      (∑ i : ι,
          ⟪-xTilde, evalY i (yHat i) - evalY i (yRef i)⟫_ℝ) =
        -⟪xTilde,
          (∑ i : ι, evalY i (yHat i)) -
            ∑ i : ι, evalY i (yRef i)⟫_ℝ := by
    calc
      (∑ i : ι,
          ⟪-xTilde, evalY i (yHat i) - evalY i (yRef i)⟫_ℝ) =
          ⟪-xTilde,
            (∑ i : ι, evalY i (yHat i)) -
              ∑ i : ι, evalY i (yRef i)⟫_ℝ := by
            simpa [Finset.sum_sub_distrib] using
              (inner_sum (𝕜 := ℝ) (Finset.univ)
                (fun i : ι => evalY i (yHat i) - evalY i (yRef i))
                (-xTilde)).symm
      _ =
          -⟪xTilde,
            (∑ i : ι, evalY i (yHat i)) -
              ∑ i : ι, evalY i (yRef i)⟫_ℝ := by
            simp [inner_neg_left]
  have hdualL :
      dualL =
        -⟪xTilde,
          (∑ i : ι, evalY i (yHat i)) -
            ∑ i : ι, evalY i (yRef i)⟫_ℝ +
          (∑ i : ι, dualPenalty i (yHat i)) -
          ∑ i : ι, dualPenalty i (yRef i) := by
    dsimp [dualL]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hdualInner]
  have hgap :
      saddleGap
          (linearCoupledSaddleValue evalX regularizer
            (fun y : (∀ i, Y i) => ∑ i : ι, evalY i (y i))
            (fun y : (∀ i, Y i) => ∑ i : ι, dualPenalty i (y i)))
          (xCur, yHat) (xRef, yRef) =
        primalL + dualL + mismatch := by
    rw [hdualL]
    simp [saddleGap, linearCoupledSaddleValue, primalL, mismatch,
      inner_sub_left, inner_sub_right]
    ring_nf
  change
    saddleGap
        (linearCoupledSaddleValue evalX regularizer
          (fun y : (∀ i, Y i) => ∑ i : ι, evalY i (y i))
          (fun y : (∀ i, Y i) => ∑ i : ι, dualPenalty i (y i)))
        (xCur, yHat) (xRef, yRef) ≤
      primalR + dualR + mismatch
  rw [hgap]
  linarith

end SOptLib



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

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: coordinate gradient-memory preservation under a one-hot refresh;
--   orig was `ambientFixedInnerProcess_yMem_gradPsiOnAt_of_initial`, renamed
--   away from ambient fixed-run and paper setup terminology
-- generality used: arbitrary sample space, coordinate type, state type, carrier
--   set, process, sample selector, memory projections, and component-gradient
--   selector on feasible points; no measure, filtration, convexity, smoothness,
--   topology, vector-space, or finite-index structure is used
-- portable call pattern: sampled table-gradient methods such as SAG/SAGA,
--   SVRG/SARAH-style memory tables, and proximal variance-reduced methods
--   prove that the sampled coordinate refreshes to the current gradient while
--   every nonsampled coordinate keeps both point memory and gradient memory
-- counterargument checked: not just paper traceability because this packages
--   the recurring induction that turns one-hot table updates into an
--   all-coordinate gradient-memory invariant; the existing
--   `coordinateGradientMemoryMatches` only names the invariant and does not
--   prove preservation
-- coverage search: searched SOptLib catalog/symbols for `gradient memory`,
--   `coordinateGradientMemoryMatches`, `one hot refresh`, `yMem`, and `xMem`;
--   semantic Mathlib search for `coordinate memory invariant one hot refresh
--   gradient table` returned only unrelated gradient calculus and coordinate
--   projection hits, so coverage is partial only through the existing predicate
-- minimal hypotheses: all already minimal; the proof needs initial agreement,
--   feasible x-memory witnesses, sampled y-refresh, nonsampled y-staleness,
--   and nonsampled x-staleness, with no finiteness or decidable equality

/-- A coordinate gradient-memory invariant is preserved by one-hot table refreshes.

If initially each stored `y` entry is the gradient at the corresponding stored
`x` entry, each sampled successor refreshes that coordinate to the new gradient,
and nonsampled coordinates keep both `x` and `y` memories, then every generated
time has matching coordinate gradient memories.

Layer: Layer1 | Gap: Level 1 (one-hot coordinate gradient-memory preservation)
Proof: induction on generated time. The sampled branch is the refresh
  hypothesis, and the stale branch transports the previous invariant through
  subtype extensionality for the unchanged point memory.
Source: Mathlib natural-number induction, subtype extensionality, and
  coordinate table-update APIs
Used in: randomized accelerated proximal-point fixed inner-loop gradient-memory
  preservation for component table refreshes
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem coordinateGradientMemoryMatches_of_oneHotRefresh
    {Ω ι E State : Type*} {X : Set E}
    (N : ℕ) (proc : ℕ → Ω → State) (sample : ℕ → Ω → ι)
    (xMem yMem : State → ι → E)
    (grad : ι → {x : E // x ∈ X} → E)
    (hxMem : ∀ n, n ≤ N → ∀ ω : Ω, ∀ i : ι, xMem (proc n ω) i ∈ X)
    (hinit :
      ∀ ω : Ω,
        coordinateGradientMemoryMatches grad
          (fun i => xMem (proc 0 ω) i) (fun i => yMem (proc 0 ω) i)
          (fun i => hxMem 0 (Nat.zero_le N) ω i))
    (hrefresh :
      ∀ n, ∀ hn : n + 1 ≤ N, ∀ ω : Ω,
        yMem (proc (n + 1) ω) (sample n ω) =
          grad (sample n ω)
            ⟨xMem (proc (n + 1) ω) (sample n ω),
              hxMem (n + 1) hn ω (sample n ω)⟩)
    (hy_stale :
      ∀ n, n + 1 ≤ N → ∀ ω : Ω, ∀ i : ι, i ≠ sample n ω →
        yMem (proc (n + 1) ω) i = yMem (proc n ω) i)
    (hx_stale :
      ∀ n, n + 1 ≤ N → ∀ ω : Ω, ∀ i : ι, i ≠ sample n ω →
        xMem (proc (n + 1) ω) i = xMem (proc n ω) i) :
    ∀ n, ∀ hn : n ≤ N, ∀ ω : Ω,
      coordinateGradientMemoryMatches grad
        (fun i => xMem (proc n ω) i) (fun i => yMem (proc n ω) i)
        (fun i => hxMem n hn ω i) := by
  intro n hn
  induction n with
  | zero =>
      exact hinit
  | succ n ih =>
      intro ω
      apply coordinateGradientMemoryMatches_intro
      intro i
      have hn' : n ≤ N := Nat.le_of_succ_le hn
      by_cases hi : i = sample n ω
      · subst i
        exact hrefresh n hn ω
      · calc
          yMem (proc (n + 1) ω) i = yMem (proc n ω) i := hy_stale n hn ω i hi
          _ = grad i ⟨xMem (proc n ω) i, hxMem n hn' ω i⟩ :=
            coordinateGradientMemoryMatches_apply (ih hn' ω) i
          _ = grad i ⟨xMem (proc (n + 1) ω) i, hxMem (n + 1) hn ω i⟩ := by
            exact congrArg (grad i) (Subtype.ext (hx_stale n hn ω i hi).symm)

end SOptLib

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Layer1/lineSearch_iterate_succ_le_gap_quadratic.lean
/-!
-- Generalization plan (G0):
-- concept/name: lineSearch_iterate_succ_le_gap_quadratic exposes the standard
--   line-search assembly step from a selected next-iterate comparison and a
--   quadratic trial expansion; orig was
--   cndGLineSearchObjective_iterate_succ_le_gap_quadratic / current file's
--   cndGLineSearchQuadratic_iterate_succ_le_gap_quadratic.
-- generality used: arbitrary real module `E`, abstract two-point objective
--   `obj`, scalar gap `gap`, quadratic coefficient `Dcoef`, iterate sequence,
--   oracle point map, and trial stepsize sequence; no measure, independence,
--   integrability, convexity, smoothness, topology, norm, inner product, or
--   finite-dimensional assumptions are used.
-- portable call pattern: conditional-gradient, Frank-Wolfe, projection
--   sliding, and proximal-linear line-search proofs can supply their own
--   selected update comparison and quadratic expansion while reusing the same
--   next-iterate gap-quadratic upper bound.
-- counterargument checked: not paper-local traceability because the statement
--   abstracts exactly the recurring proof-composition boundary; not a pure
--   formula wrapper because it combines a line-search comparison with a
--   separately proved quadratic expansion, and it does not parameterize a
--   named formula by an equality to its definition.
-- coverage search: searched source/catalog for `lineSearch`,
--   `iterate_succ_le`, `gap_quadratic`, `quadratic expansion`, and
--   `two_div_candidate`; relevant hits were
--   `one_based_line_search_iterate_succ_le_two_div` and
--   `linear_centered_quadratic_along_line_eq_quadratic`, which are the two
--   inputs to this assembly step rather than duplicates. LeanSearch for
--   `line search comparison quadratic expansion next iterate gap bound`
--   returned only generic minimizer and quadratic facts, no full duplicate.
-- minimal hypotheses: global setup fields are reduced to pointwise comparison
--   and expansion hypotheses at the chosen index; `AddCommMonoid` and
--   `Module ℝ` are used only to state the affine trial point.
-/

namespace SOptLib

/-- A line-search next iterate inherits the gap-quadratic bound of a trial step.

If the selected successor is no worse than the affine trial point and that
trial point has a quadratic expansion with gap term, then the same
gap-quadratic expression bounds the selected successor.

Layer: Layer1 | Gap: Level 1 (line-search quadratic trial assembly)
Proof: apply transitivity from the selected line-search comparison to the
  quadratic expansion of the trial point.
Source: Conditional-gradient and Frank-Wolfe line-search algebra with Mathlib
  ordered real arithmetic
Used in: stochastic conditional-gradient sliding inner-loop descent when the
  selected line-search update is compared against a quadratic trial step
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem lineSearch_iterate_succ_le_gap_quadratic
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (obj : E → E → ℝ) (gap Dcoef : E → ℝ)
    (iterate : ℕ → E) (oracle : E → E) (stepsize : ℕ → ℝ)
    {t : ℕ}
    (hlineSearch :
      obj (iterate t) (iterate (t + 1)) ≤
        obj (iterate t)
          ((1 - stepsize t) • iterate t + stepsize t • oracle (iterate t)))
    (hquadratic :
      obj (iterate t)
          ((1 - stepsize t) • iterate t + stepsize t • oracle (iterate t)) =
        obj (iterate t) (iterate t) +
          Dcoef (iterate t) * stepsize t ^ 2 - gap (iterate t) * stepsize t) :
    let current := iterate t
    let lam := stepsize t
    obj current (iterate (t + 1)) ≤
      obj current current + Dcoef current * lam ^ 2 - gap current * lam := by
  let current := iterate t
  let lam := stepsize t
  change
    obj current (iterate (t + 1)) ≤
      obj current current + Dcoef current * lam ^ 2 - gap current * lam
  calc
    obj current (iterate (t + 1)) ≤
        obj current ((1 - lam) • current + lam • oracle current) := by
      simpa [current, lam] using hlineSearch
    _ = obj current current + Dcoef current * lam ^ 2 - gap current * lam := by
      simpa [current, lam] using hquadratic

end SOptLib

namespace SOptLib

theorem line_search_iterate_succ_le_gap_quadratic
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (obj : E → E → ℝ) (gap Dcoef : E → ℝ)
    (iterate : ℕ → E) (oracle : E → E) (stepsize : ℕ → ℝ)
    {t : ℕ}
    (hlineSearch :
      obj (iterate t) (iterate (t + 1)) ≤
        obj (iterate t)
          ((1 - stepsize t) • iterate t + stepsize t • oracle (iterate t)))
    (hquadratic :
      obj (iterate t)
          ((1 - stepsize t) • iterate t + stepsize t • oracle (iterate t)) =
        obj (iterate t) (iterate t) +
          Dcoef (iterate t) * stepsize t ^ 2 - gap (iterate t) * stepsize t) :
    let current := iterate t
    let lam := stepsize t
    obj current (iterate (t + 1)) ≤
      obj current current + Dcoef current * lam ^ 2 - gap current * lam :=
  lineSearch_iterate_succ_le_gap_quadratic obj gap Dcoef iterate oracle stepsize
    hlineSearch hquadratic

end SOptLib

-- Batch 2 promoted from Staging/affine_iterate_mem_of_convex_update.lean
-- Generalization plan (G0):
-- concept/name: affine iterate feasibility under convex updates; orig was
--   `affine_line_search_iterates_mem_of_start_mem` / local CndG feasibility.
-- generality used: a module over an ordered ring, a convex feasible set,
--   an abstract iterate sequence, selected feasible points, and scalar weights;
--   no measure, smoothness, oracle, compactness, or inner-product hypotheses.
-- portable call pattern: conditional-gradient, Frank-Wolfe, projection-sliding,
--   and restarted line-search recurrences where the selected point, stepsize
--   rule, and stop predicate change but the invariant `∀ n, x n ∈ X` is the
--   same.
-- counterargument checked: Mathlib has the one-step `Convex.lineMap_mem` and
--   `Convex.add_smul_sub_mem`, while SOptLib has model-specific one-step
--   helpers such as `acceleratedAveragePoint_mem`; neither packages the
--   sequence-level stopped-or-affine update induction needed at call sites.
-- coverage search: LeanSearch query "convex set affine recursive update
--   remains in set" returned `Convex.lineMap_mem`, `Convex.add_smul_sub_mem`,
--   and `Convex.mapsTo_lineMap`; project/catalog search for "affine iterate
--   mem convex update" found no alpha-equivalent SOptLib theorem.
-- minimal hypotheses: compactness and line-search quotient algebra stay at the
--   caller; this lemma only needs pointwise selected-point feasibility,
--   pointwise coefficient membership in `[0,1]`, and the stopped/update
--   successor equation.

/-- A sequence remains in a convex feasible set under stopped or affine updates.

Starting from a feasible point, if every successor is either unchanged or the
affine blend of the current point with a selected feasible point using a weight
in `[0,1]`, then all iterates are feasible.

Layer: Layer1 | Gap: Level 1 (affine-update feasibility induction)
Proof: induction on the iterate index; the stopped branch rewrites to the
  induction hypothesis, and the update branch uses convex closure under a
  two-point affine combination.
Source: Mathlib convex-set API for real and ordered-ring affine combinations
Used in: conditional-gradient line-search feasibility for stopped and raw
  inner iterates
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem affine_iterate_mem_of_convex_update
    {R E : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommMonoid E] [Module R E]
    {X : Set E} (hX : Convex R X)
    (x selected : ℕ → E) (alpha : ℕ → R)
    (hx0 : x 0 ∈ X)
    (hselected : ∀ n : ℕ, x n ∈ X → selected n ∈ X)
    (halpha : ∀ n : ℕ, x n ∈ X → alpha n ∈ Set.Icc (0 : R) 1)
    (hstep : ∀ n : ℕ,
      x (n + 1) = x n ∨
        x (n + 1) = (1 - alpha n) • x n + alpha n • selected n) :
    ∀ n : ℕ, x n ∈ X := by
  intro n
  induction n with
  | zero =>
      simpa using hx0
  | succ n ih =>
      rcases hstep n with hstay | hupdate
      · simpa [hstay] using ih
      · rw [hupdate]
        exact convex_iff_add_mem.mp hX ih (hselected n ih)
          (sub_nonneg.mpr (Set.mem_Icc.mp (halpha n ih)).2)
          (Set.mem_Icc.mp (halpha n ih)).1
          (sub_add_cancel 1 (alpha n))


-- Batch 2 promoted from Staging/positiveTime_estimator_eq_target_of_refresh_step.lean
-- Generalization plan (G0):
-- concept/name: positive-time estimator refresh transport; orig was `paperEstimator_refresh`,
--   renamed away from paper notation while retaining the positive-time indexing concept.
-- generality used: arbitrary sample, state, iterate, and estimator types; no measure,
--   measurability, independence, integrability, convexity, norm, inner product, or finite
--   dimension assumptions are used.
-- portable call pattern: epoch-recursive stochastic estimators at refresh steps; future
--   variance-reduced SGD, mirror-descent, proximal-gradient, or conditional-gradient runs
--   can vary state projections, target maps, update relations, and refresh predicates while
--   keeping the same positive-time estimator-equals-target conclusion.
-- counterargument checked: not just paper-local traceability, because the statement packages
--   the recurring zero-based successor versus one-based paper-time view alignment; not a
--   duplicate of residual-zero or concrete finite-sum refresh lemmas, which assume specific
--   process definitions rather than an arbitrary refresh-step update law.
-- coverage search: queries `positive time estimator refresh target run state`,
--   `recursive process estimator refresh equals target`, and catalog grep for
--   `estimator refresh target`; top hits were `SOptLib.estimatorProcess_epochStart_eq_target`,
--   `SOptLib.estimator_at_epoch_start_eq_refresh_minibatch`, and
--   `SOptLib.positiveTimeIterateView_eq`; coverage partial, since existing hits either
--   target a concrete process/minibatch formula or only unfold the positive-time view.
-- minimal hypotheses: all already minimal; the only hypotheses are the paper-view
--   accessors and the pointwise refresh successor identity.

namespace SOptLib

/-- A positive-time estimator view equals its target at refresh successor steps.

If the positive-time iterate at `k` reads the zero-based state at `k - 1`, the
positive-time estimator at `k` reads the zero-based state at `k`, and every
refresh successor step stores the target of the predecessor iterate, then the
positive-time estimator equals the target at that positive-time iterate.

Layer: Layer1 | Gap: Level 1 (positive-time refresh estimator transport)
Proof: normalize `k - 1 + 1` to `k`, apply the pointwise refresh successor
  identity, and rewrite the named positive-time iterate and estimator views.
Source: Mathlib natural-number subtraction, subtype indexing, and stochastic
  optimization recursive-process notation
Used in: epoch-recursive stochastic estimator refresh base cases before
  estimator-residual recursion
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem positiveTime_estimator_eq_target_of_refresh_step
    {Ω State Iter Est : Type*}
    (run : ℕ → Ω → State)
    (iterOf : State → Iter) (estOf : State → Est)
    (target : Iter → Est)
    (paperIter : {k : ℕ // 1 ≤ k} → Ω → Iter)
    (paperEst : {k : ℕ // 1 ≤ k} → Ω → Est)
    (refreshStep : ℕ → Prop)
    (hpaperIter :
      ∀ k ω,
        paperIter k ω =
          positiveTimeIterateView (fun n ω => iterOf (run n ω)) k ω)
    (hpaperEst : ∀ k ω, paperEst k ω = estOf (run k.1 ω))
    (hrefresh :
      ∀ n ω, refreshStep (n + 1) →
        estOf (run (n + 1) ω) = target (iterOf (run n ω)))
    (k : {k : ℕ // 1 ≤ k}) (ω : Ω)
    (hk : refreshStep k.1) :
    paperEst k ω = target (paperIter k ω) := by
  let n : ℕ := k.1 - 1
  have hn : n + 1 = k.1 := by
    dsimp [n]
    exact Nat.sub_add_cancel k.2
  have hupdate :
      estOf (run k.1 ω) = target (iterOf (run (k.1 - 1) ω)) := by
    have h := hrefresh n ω (by simpa [hn] using hk)
    simpa [n, hn] using h
  calc
    paperEst k ω = estOf (run k.1 ω) := hpaperEst k ω
    _ = target (iterOf (run (k.1 - 1) ω)) := hupdate
    _ = target (paperIter k ω) := by
      rw [hpaperIter]
      simp [positiveTimeIterateView_eq]

end SOptLib


-- Batch 2 promoted from Staging/recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch.lean
open MeasureTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: recursive estimator residual one-step second-moment recurrence
--   from a centered mini-batch increment; orig was
--   recursive_estimator_one_step_second_moment_recurrence.
-- generality used: arbitrary measurable space and measure; Hilbert-valued
--   residuals in `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`; no
--   probability normalization, convexity, objective, or filtration assumption is
--   used after the mini-batch centering and cross-moment facts are available.
-- portable call pattern: SARAH/SPIDER/SVRG-style recursive estimator proofs use
--   the same step after proving centered batch residuals, diagonal variance
--   budgets, and previous-residual orthogonality; the process, oracle residual,
--   batch index set, and displacement process vary.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   `second_moment_add_recurrence_le_of_cross_zero` covers only the final
--   Hilbert add-recurrence, while this theorem additionally packages centered
--   mini-batch L2 closure and variance reduction into the estimator step.
-- coverage search: searched "recursive estimator residual second moment",
--   "second_moment_add_recurrence_le_of_cross_zero", and centered mini-batch
--   variance lemmas; hits were partial (`second_moment_add_recurrence_le_of_cross_zero`,
--   `centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero`,
--   `integrable_sq_norm_centeredMiniBatchAverage`,
--   `pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero`), none states
--   the combined recursive residual step with an explicit displacement budget.
-- minimal hypotheses: all global algorithm setup fields are replaced by
--   pointwise/a.e. recurrence, measurability, L2, centered-batch, and
--   cross-moment hypotheses; no finite-dimensional or probability instance is
--   required.

/-- A centered mini-batch recursive residual has the standard one-step second-moment bound.

If the next residual is the previous residual plus a centered mini-batch
increment, each centered summand has second moment bounded by an `L ^ 2` times a
displacement budget, off-diagonal summand cross moments vanish, and the previous
residual is orthogonal in expectation to the increment, then the next residual
second moment is bounded by the previous one plus the mini-batch variance budget.

Layer: Layer1 | Gap: Level 1 (recursive estimator centered mini-batch second-moment step)
Proof: obtain L2 integrability and the `1 / b` mini-batch variance bound from
  the centered finite-batch API, then apply the Hilbert-valued additive
  second-moment recurrence with the supplied previous-residual cross cancellation.
Source: Mathlib Bochner integration, finite mini-batch variance reduction, and
  Hilbert-space norm-square recurrence APIs
Used in: stochastic nonconvex conditional-gradient recursive estimator residual
  recurrence inside a non-refresh epoch step
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq ι]
    (μ : Measure Ω) (I : Finset ι) (b : ℕ)
    (deltaPrev deltaNext inc : Ω → E) (eps : ι → Ω → E)
    (xPrev xCurr : Ω → E) (L : ℝ)
    (hbpos : 0 < b)
    (hcard : I.card = b)
    (hprev_meas : AEStronglyMeasurable deltaPrev μ)
    (heps_meas : ∀ i ∈ I, AEStronglyMeasurable (eps i) μ)
    (hprev_sq : Integrable (fun ω => ‖deltaPrev ω‖ ^ 2) μ)
    (heps_diag :
      ∀ i ∈ I,
        Integrable (fun ω => ‖eps i ω‖ ^ 2) μ ∧
          ∫ ω, ‖eps i ω‖ ^ 2 ∂μ ≤
            L ^ 2 * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ)
    (hinc_eq :
      inc = fun ω => ((b : ℝ)⁻¹) • Finset.sum I (fun i => eps i ω))
    (hrec :
      Filter.EventuallyEq (ae μ) deltaNext (fun ω => deltaPrev ω + inc ω))
    (heps_cross :
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∫ ω, ⟪eps i ω, eps j ω⟫_ℝ ∂μ = 0)
    (hprev_increment_cross :
      ∫ ω, ⟪deltaPrev ω, inc ω⟫_ℝ ∂μ = 0) :
    ∫ ω, ‖deltaNext ω‖ ^ 2 ∂μ ≤
      ∫ ω, ‖deltaPrev ω‖ ^ 2 ∂μ +
        (L ^ 2 / (b : ℝ)) * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ := by
  classical
  have hinc_meas : AEStronglyMeasurable inc μ := by
    have havg_meas :
        AEStronglyMeasurable
          (((b : ℝ)⁻¹) • Finset.sum I (fun i => eps i)) μ := by
      exact
        (Finset.aestronglyMeasurable_sum (s := I)
          (fun i hi => heps_meas i hi)).const_smul ((b : ℝ)⁻¹)
    have havg_eq :
        (((b : ℝ)⁻¹) • Finset.sum I (fun i => eps i)) =
          fun ω => ((b : ℝ)⁻¹) • Finset.sum I (fun i => eps i ω) := by
      funext ω
      simp [Finset.sum_apply]
    simpa [hinc_eq, havg_eq] using havg_meas
  have hinc_sq : Integrable (fun ω => ‖inc ω‖ ^ 2) μ := by
    exact
      integrable_sq_norm_centeredMiniBatchAverage
        (μ := μ) (I := I) (m := b) (δ := eps) (avg := inc)
        heps_meas
        (fun i hi => (heps_diag i hi).1)
        hinc_eq
  have hinc_bound :
      ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
        (L ^ 2 / (b : ℝ)) * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ := by
    have hraw :
        ∫ ω, ‖(b : ℝ)⁻¹ • Finset.sum I (fun i => eps i ω)‖ ^ 2 ∂μ ≤
          (L ^ 2 * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ) / (b : ℝ) :=
      centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero
        (P := μ) (I := I) (m := b) (eps := eps)
        (varianceBudget := L ^ 2 * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ)
        hbpos hcard heps_meas heps_diag heps_cross
    calc
      ∫ ω, ‖inc ω‖ ^ 2 ∂μ
          ≤ (L ^ 2 * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ) / (b : ℝ) := by
            simpa [hinc_eq] using hraw
      _ = (L ^ 2 / (b : ℝ)) *
            ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ := by
            ring
  exact
    (second_moment_add_recurrence_le_of_cross_zero
      (μ := μ) (deltaPrev := deltaPrev) (deltaNext := deltaNext)
      (inc := inc)
      (B := (L ^ 2 / (b : ℝ)) * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂μ)
      hprev_meas hinc_meas hprev_sq hinc_sq hrec hprev_increment_cross hinc_bound).2


-- Batch 2 promoted from Staging/smooth_descent_of_approx_cndg_with_estimator_error.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: smooth descent after an approximate variational/prox step with
--   estimator residual absorption; orig was
--   theorem718_cndg_smooth_descent_with_estimator_error, renamed away from the
--   theorem number and setup fields.
-- generality used: real inner-product seminormed additive group `E`; no measure,
--   filtration, compactness, convexity, or finite-dimensional hypotheses. The
--   proof only needs a pointwise smooth quadratic upper bound and a pointwise
--   approximate variational/descent inequality for the update.
-- portable call pattern: variance-reduced conditional-gradient, prox-linear,
--   and projected-gradient one-step proofs instantiate `f`, `grad`, current
--   point `x`, update `y`, estimator `G`, and scalars `gamma eta L q`; the
--   smoothness and approximate model certificates change while the descent
--   conclusion stays the same.
-- counterargument checked: not just paper-local traceability and not a pure
--   wrapper; it packages the recurring composition of smoothness, approximate
--   model descent, gradient-estimator residual decomposition, and q-Young
--   absorption. Existing SOptLib conditional-gradient descent lemmas assume an
--   affine LMO update/diameter bound or Wolfe-gap structure, not this prox
--   variational premise.
-- coverage search: searched CATALOG/SOptLib/Staging for `smooth descent`,
--   `estimator error`, `approx variational`, and `cndg`; top hits were
--   `conditional_gradient_smooth_descent_premise_of_estimator`,
--   `wolfeGap_descent_of_trueGradient_linearMinimizer_descent`,
--   `prox_descent_inner_bound_of_variational`, and the staged negative-inner
--   Young lemma. Coverage is partial rather than full because none combine the
--   abstract prox variational descent premise with estimator-error absorption.
-- minimal hypotheses: global smoothness and feasibility were reduced to the
--   pointwise upper-bound and pointwise approximate descent premises actually
--   used; positivity is needed only for the Young parameter `q`.

/-- A smooth upper bound and approximate prox descent give estimator-error descent.

If a smooth quadratic upper bound holds at `y`, and the estimator-driven
approximate variational step controls the estimator inner product by the
quadratic displacement penalty plus `eta`, then the true-gradient descent bound
follows after absorbing the estimator residual with a positive Young parameter.

Layer: Layer1 | Gap: Level 1 (approximate prox-step estimator-error descent)
Proof: split the true gradient as estimator minus residual, insert the
  approximate variational descent bound, and absorb the residual inner product
  using Hilbert-space Cauchy-Schwarz plus q-Young.
Source: smooth first-order descent calculus in real Hilbert spaces and
  ordered-field Young inequality algebra
Used in: variance-reduced conditional-gradient and prox-linear one-step
  descent before estimator second-moment aggregation
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/key_lemmas/0/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem smooth_descent_of_approx_variational_step_with_estimator_error
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (x y G : E) (gamma eta L q : ℝ)
    (hq : 0 < q)
    (hsmooth :
      f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2)
    (hproj :
      ⟪G, y - x⟫_ℝ ≤ eta - gamma⁻¹ * ‖y - x‖ ^ 2) :
    f y ≤
      f x - (gamma⁻¹ - L / 2 - q / 2) * ‖y - x‖ ^ 2 +
        (1 / (2 * q)) * ‖G - grad x‖ ^ 2 + eta := by
  let delta : E := G - grad x
  have hgrad : grad x = G - delta := by
    simp [delta]
  have hnoise :
      -⟪delta, y - x⟫_ℝ ≤
        (q / 2) * ‖y - x‖ ^ 2 + (1 / (2 * q)) * ‖delta‖ ^ 2 := by
    exact neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq hq delta (y - x)
  have hinner_decomp :
      ⟪grad x, y - x⟫_ℝ =
        ⟪G, y - x⟫_ℝ - ⟪delta, y - x⟫_ℝ := by
    rw [hgrad]
    simp [inner_sub_left]
  nlinarith [hsmooth, hproj, hnoise, hinner_decomp]


-- Batch 2 promoted from Staging/projectedGradient_sq_le_three_term_of_model_distance_and_oracle_error.lean
-- Generalization plan (G0):
-- concept/name: projectedGradient_sq_le_three_term_of_model_distance_and_oracle_error
--   exposes the three-term projected-gradient stationarity comparison obtained
--   from an approximate model output, an exact model/prox point, and an
--   oracle-error stability bound; orig was
--   theorem718_projected_gradient_three_term_bound, renamed away from theorem
--   numbering and paper-local setup fields.
-- generality used: an arbitrary real normed vector-space ambient type `E`,
--   real stepsize/tolerance scalars, points `x y zbar xhat`, and vectors
--   `grad G`. No measure, independence, integrability, convexity,
--   differentiability, compactness, completeness, or inner-product hypotheses
--   are used once the pointwise model-distance and oracle-stability bounds are
--   supplied.
-- portable call pattern: conditional-gradient sliding, proximal-gradient, and
--   variance-reduced stationarity proofs can vary the base point, approximate
--   model output, exact oracle model minimizer, exact true-gradient projected
--   point, oracle vector, and stability proof while reusing the same
--   three-term squared-certificate conclusion.
-- counterargument checked: not paper-local traceability because the statement
--   is a paper-free pointwise proof-composition boundary; not a pure wrapper
--   because it packages two nested norm-square Young inequalities, conversion
--   of the model-distance budget into an inverse-stepsize residual square, and
--   oracle-error orientation. No inner formula is extracted because the
--   projected-gradient displacement is already the named mathematical object
--   in `SOptLib.projectedGradient` for prox selectors, while this theorem is
--   the pointwise algebraic comparison between selected points.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `projectedGradient`, `three term`, `model distance`, `oracle error`, and
--   `norm square`; relevant hits were `SOptLib.projectedGradient`,
--   `projectedGradient_lipschitz_oracle_of_prox_scaled_dist`,
--   `exact_projectedGradient_sq_le_oracle_projectedGradient_sq_add_residual`,
--   and `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`.
--   LeanSearch for Hilbert-space norm-squared three-term bounds returned
--   generic triangle inequalities such as `norm_add₃_le`, not this
--   model-distance/oracle-error certificate. Coverage is partial, not
--   duplicate.
-- minimal hypotheses: source global feasible-set, projected-point, and
--   positive-stepsize assumptions are reduced to the two pointwise inequalities
--   actually consumed by the algebra; all remaining hypotheses are minimal.

open scoped InnerProductSpace

/-- A projected-gradient square is bounded by base displacement, model residual,
and oracle error.

If an approximate output `y` is close to the exact oracle model point `zbar` in
the model-distance budget and the true projected point `xhat` is close to
`zbar` by oracle stability, then the scaled displacement from `x` to `xhat`
has the standard three-term squared-norm bound.

Layer: Layer1 | Gap: Level 1 (projected-gradient model-distance oracle-error comparison)
Proof: decompose `x - xhat` through `y` and `zbar`, apply the binary
  norm-square Young inequality twice, convert the model-distance budget into an
  inverse-stepsize residual-square bound, and square the oracle-stability
  estimate.
Source: Mathlib normed vector-space scalar algebra and SOptLib squared-norm
  Young inequality APIs
Used in: stochastic nonconvex conditional-gradient sliding projected-gradient
  stationarity comparison after the approximate conditional-gradient model step
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem projectedGradient_sq_le_three_term_of_model_distance_and_oracle_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {gamma eta : ℝ} (x y zbar xhat grad G : E)
    (hgamma : 0 < gamma)
    (hmodel_distance : (1 / (2 * gamma)) * ‖y - zbar‖ ^ 2 ≤ eta)
    (horacle_error : ‖gamma⁻¹ • (zbar - xhat)‖ ≤ ‖G - grad‖) :
    ‖gamma⁻¹ • (x - xhat)‖ ^ 2 ≤
      2 * ‖gamma⁻¹ • (x - y)‖ ^ 2 +
        8 * eta / gamma + 4 * ‖G - grad‖ ^ 2 := by
  let a : E := gamma⁻¹ • (x - y)
  let b : E := gamma⁻¹ • (y - zbar)
  let c : E := gamma⁻¹ • (zbar - xhat)
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma
  have hgamma_inv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
  have hb_sq : ‖b‖ ^ 2 ≤ 2 * eta / gamma := by
    have hmul := mul_le_mul_of_nonneg_left hmodel_distance
      (show 0 ≤ 2 * gamma⁻¹ by positivity)
    have hb_eq :
        ‖b‖ ^ 2 =
          (2 * gamma⁻¹) * ((1 / (2 * gamma)) * ‖y - zbar‖ ^ 2) := by
      simp [b, norm_smul, Real.norm_of_nonneg hgamma_inv_nonneg]
      field_simp [hgamma_ne]
    calc
      ‖b‖ ^ 2 =
          (2 * gamma⁻¹) * ((1 / (2 * gamma)) * ‖y - zbar‖ ^ 2) := hb_eq
      _ ≤ (2 * gamma⁻¹) * eta := hmul
      _ = 2 * eta / gamma := by
        field_simp [hgamma_ne]
  have hc_sq : ‖c‖ ^ 2 ≤ ‖G - grad‖ ^ 2 := by
    nlinarith [horacle_error, norm_nonneg c, norm_nonneg (G - grad)]
  have hdecomp_vec : x - xhat = (x - y) + (y - zbar) + (zbar - xhat) := by
    abel
  have hpg_decomp : gamma⁻¹ • (x - xhat) = a + (b + c) := by
    calc
      gamma⁻¹ • (x - xhat)
          = gamma⁻¹ • ((x - y) + (y - zbar) + (zbar - xhat)) := by
            rw [hdecomp_vec]
      _ = a + (b + c) := by
        rw [smul_add, smul_add]
        simp [a, b, c, add_assoc]
  have htri₁ :
      ‖a + (b + c)‖ ^ 2 ≤
        2 * ‖a‖ ^ 2 + 2 * ‖b + c‖ ^ 2 :=
    SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq a (b + c)
  have htri₂ :
      ‖b + c‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖c‖ ^ 2 :=
    SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq b c
  have htri :
      ‖gamma⁻¹ • (x - xhat)‖ ^ 2 ≤
        2 * ‖a‖ ^ 2 + 4 * ‖b‖ ^ 2 + 4 * ‖c‖ ^ 2 := by
    rw [hpg_decomp]
    nlinarith [htri₁, htri₂]
  calc
    ‖gamma⁻¹ • (x - xhat)‖ ^ 2
        ≤ 2 * ‖a‖ ^ 2 + 4 * ‖b‖ ^ 2 + 4 * ‖c‖ ^ 2 := htri
    _ ≤ 2 * ‖a‖ ^ 2 + 8 * eta / gamma + 4 * ‖G - grad‖ ^ 2 := by
      have hb4 : 4 * ‖b‖ ^ 2 ≤ 8 * eta / gamma := by
        calc
          4 * ‖b‖ ^ 2 ≤ 4 * (2 * eta / gamma) :=
            mul_le_mul_of_nonneg_left hb_sq (by norm_num)
          _ = 8 * eta / gamma := by ring
      have hc4 : 4 * ‖c‖ ^ 2 ≤ 4 * ‖G - grad‖ ^ 2 := by
        nlinarith [hc_sq]
      nlinarith
    _ =
        2 * ‖gamma⁻¹ • (x - y)‖ ^ 2 +
          8 * eta / gamma + 4 * ‖G - grad‖ ^ 2 := by
      simp [a]


-- Batch 7 promoted from Staging/accelerated_vr_prox_conditional_expectation_step.lean
-- Generalization plan (G0):
-- concept/name: accelerated variance-reduced proximal conditional-expectation
--   one-step recurrence; orig was
--   `lemma516_guarded_relational_conditional_expectation_step_boundary`, renamed
--   away from theorem-number and source-route vocabulary while retaining the
--   genuine stochastic-optimization terms accelerated, variance-reduced,
--   proximal, conditional expectation, and one-step.
-- generality used: arbitrary finite sample type with normalized nonnegative
--   weights and an arbitrary real Hilbert space; the proof uses pointwise
--   prox-descent, composite upper-model, residual zero-mean/second-moment, and
--   scalar curvature/noise guards only. No filtration, independence, or
--   integrability assumptions are needed after the conditional expectation is
--   expanded into a finite weighted sum.
-- portable call pattern: future accelerated stochastic proximal-gradient,
--   mirror-prox, or variance-reduced finite-sum proofs can instantiate their
--   own smooth part, nonsmooth part, linear model, target-fixed Bregman-like potential,
--   residual estimator, and accelerated affine displacement certificate while
--   keeping the guarded conditional Lyapunov recurrence conclusion unchanged.
-- counterargument checked: not paper-local traceability because the statement
--   has no setup record, theorem numbers, component-objective fields, or
--   source-route names; not a pure wrapper because it composes pointwise
--   prox descent, smooth/convex composite upper bounds, Young residual
--   absorption, second-moment budgeting, scalar noise absorption, and
--   positive-ratio expectation rescaling.
-- coverage search: searched CATALOG.md/SOptLib/Staging for accelerated
--   conditional recurrence, prox conditional expectation, variance recurrence,
--   residual expectation budget, composite upper model, and weighted-fiber
--   expectation; relevant partial hits were
--   `SOptLib.composite_upper_model_at_convex_average`,
--   `weighted_sum_nonneg_mul_budget_add_zero_mean_le`,
--   `sub_mul_le_absorb_add_mul_of_le`, and
--   `finset_weighted_expectation_rescale_predivided_recurrence`, but no
--   declaration covered the full one-step accelerated variance-reduced
--   conditional recursion assembly.
-- minimal hypotheses: global algorithm fields are replaced by pointwise
--   certificates exactly used in the proof: weight normalization/nonnegativity,
--   pointwise composite upper model, alpha-scaled prox descent, target/bar/snapshot
--   linear-model bounds, residual zero mean and second-moment budget, and the
--   scalar positivity/noise guards.

set_option maxHeartbeats 0 in
/-- A finite conditional expectation closes an accelerated variance-reduced prox step.

Given a pointwise composite upper model, an alpha-scaled prox descent
certificate, an unbiased residual with a second-moment budget, and the scalar
guards that absorb the residual noise into the snapshot objective, the
accelerated conditional Lyapunov recurrence follows after rescaling by
`gamma / alpha`.

Layer: Layer1 | Gap: Level 1 (accelerated variance-reduced prox conditional recurrence)
Proof: assemble the pointwise composite/prox model, use Hilbert-space Young
  absorption for the residual, average over a normalized finite law, absorb the
  residual second-moment budget into the snapshot term, and call the finite
  weighted pre-divided recurrence rescaling lemma.
Source: Mathlib finite big-operator algebra, real Hilbert-space Young
  inequalities, and SOptLib composite objective notation
Used in: variance-reduced accelerated proximal-gradient one-step conditional
  Lyapunov recursion after the finite-sample oracle residual estimate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem accelerated_variance_reduced_prox_conditional_expectation_step
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ι → ℝ) (Phi H Lin : E → ℝ)
    (Bunder Bprev : ℝ) (Bnext : ι → ℝ)
    (gamma alpha p mu L LQ den : ℝ)
    (xBarPrev snapshot xTarget aux : E)
    (xNext xBarNext residual : ι → E)
    (halpha_pos : 0 < alpha)
    (hgamma_pos : 0 < gamma)
    (hbar : 0 ≤ 1 - alpha - p)
    (hden_def : den = 1 + mu * gamma - L * alpha * gamma)
    (hden_pos : 0 < den)
    (hnoise : 0 ≤ p - LQ * alpha * gamma / den)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : Finset.univ.sum w = 1)
    (hresidual_mean :
      Finset.univ.sum (fun i : ι => w i * ⟪residual i, aux - xTarget⟫_ℝ) = 0)
    (hsecond :
      Finset.univ.sum (fun i : ι => w i * ‖residual i‖ ^ 2) ≤
        2 * LQ * (Phi snapshot - Lin snapshot))
    (hsnapshot_linearization : Lin snapshot ≤ Phi snapshot)
    (hbar_linearization : Lin xBarPrev ≤ Phi xBarPrev)
    (htarget_model : Lin xTarget + mu * Bunder ≤ Phi xTarget)
    (hcompositeBarUpper : ∀ i,
      SOptLib.compositeObjective Phi H (xBarNext i) ≤
        ((1 - alpha - p) * Lin xBarPrev +
            alpha * Lin (xNext i) + p * Lin snapshot) +
          (L / 2) * (alpha ^ 2 * ‖xNext i - aux‖ ^ 2) +
          ((1 - alpha - p) * H xBarPrev +
            alpha * H (xNext i) + p * H snapshot))
    (hproxScaled : ∀ i,
      alpha * (Lin (xNext i) - Lin xTarget + H (xNext i) - H xTarget) ≤
        alpha * mu * Bunder +
          (alpha / gamma) * Bprev -
          (alpha / gamma) * ((1 + mu * gamma) * Bnext i) -
          (alpha / gamma) *
            (((1 + mu * gamma) / 2) * ‖xNext i - aux‖ ^ 2) -
          alpha * ⟪residual i, xNext i - xTarget⟫_ℝ) :
    Finset.univ.sum (fun i : ι =>
        w i *
          (gamma / alpha *
              (SOptLib.compositeObjective Phi H (xBarNext i) -
                SOptLib.compositeObjective Phi H xTarget) +
            (1 + mu * gamma) * Bnext i)) ≤
      gamma / alpha * (1 - alpha - p) *
          (SOptLib.compositeObjective Phi H xBarPrev -
            SOptLib.compositeObjective Phi H xTarget) +
        gamma / alpha * p *
          (SOptLib.compositeObjective Phi H snapshot -
            SOptLib.compositeObjective Phi H xTarget) +
        Bprev := by
  classical
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  let Obj : E → ℝ := SOptLib.compositeObjective Phi H
  have hresidCoeff_nonneg : 0 ≤ alpha * gamma / (2 * den) := by
    have hden2 : 0 < 2 * den := mul_pos (by norm_num) hden_pos
    exact div_nonneg (mul_nonneg halpha_nonneg (le_of_lt hgamma_pos)) (le_of_lt hden2)
  have hresidualBudgetNeg :
      Finset.univ.sum (fun i : ι =>
          w i *
            ((alpha * gamma / (2 * den)) * ‖residual i‖ ^ 2 -
              alpha * ⟪residual i, aux - xTarget⟫_ℝ)) ≤
        (alpha * gamma / (2 * den)) *
          (2 * LQ * (Phi snapshot - Lin snapshot)) := by
    simpa [sub_eq_add_neg] using
      (SOptLib.weighted_sum_nonneg_mul_budget_add_zero_mean_le
        (s := Finset.univ) (w := w)
        (U := fun i : ι => ‖residual i‖ ^ 2)
        (V := fun i : ι => ⟪residual i, aux - xTarget⟫_ℝ)
        (a := alpha * gamma / (2 * den)) (b := -alpha)
        (C := 2 * LQ * (Phi snapshot - Lin snapshot))
        hresidCoeff_nonneg hresidual_mean hsecond)
  have hnoiseBracket :
      (p - LQ * alpha * gamma / den) * Lin snapshot +
          (LQ * alpha * gamma / den) * Phi snapshot ≤
        p * Phi snapshot := by
    exact
      SOptLib.sub_mul_le_absorb_add_mul_of_le p (LQ * alpha * gamma / den)
        (Lin snapshot) (Phi snapshot) hnoise hsnapshot_linearization
  have hnoiseComposite :
      p * (Lin snapshot + H snapshot) +
          (alpha * gamma / (2 * den)) *
            (2 * LQ * (Phi snapshot - Lin snapshot)) ≤
        p * Obj snapshot := by
    have hcoef :
        (alpha * gamma / (2 * den)) *
            (2 * LQ * (Phi snapshot - Lin snapshot)) =
          LQ * alpha * gamma / den * (Phi snapshot - Lin snapshot) := by
      field_simp [ne_of_gt hden_pos]
    rw [hcoef]
    dsimp [Obj, SOptLib.compositeObjective]
    nlinarith [hnoiseBracket]
  have htargetScaled :
      alpha * (Lin xTarget + H xTarget + mu * Bunder) ≤
        alpha * Obj xTarget := by
    have hbase : Lin xTarget + H xTarget + mu * Bunder ≤ Obj xTarget := by
      dsimp [Obj, SOptLib.compositeObjective]
      nlinarith [htarget_model]
    exact mul_le_mul_of_nonneg_left hbase halpha_nonneg
  have hbarLinScaled :
      (1 - alpha - p) * Lin xBarPrev ≤
        (1 - alpha - p) * Phi xBarPrev := by
    exact mul_le_mul_of_nonneg_left hbar_linearization hbar
  have hpointwisePre : ∀ i,
      Obj (xBarNext i) ≤
        (1 - alpha - p) * Obj xBarPrev +
          alpha * Obj xTarget +
          p * (Lin snapshot + H snapshot) +
          (alpha / gamma) * Bprev -
          (alpha / gamma) * ((1 + mu * gamma) * Bnext i) +
          (L / 2 * (alpha ^ 2 * ‖xNext i - aux‖ ^ 2) -
            (alpha / gamma) *
              (((1 + mu * gamma) / 2) * ‖xNext i - aux‖ ^ 2)) -
          alpha * ⟪residual i, xNext i - xTarget⟫_ℝ := by
    intro i
    have hc := hcompositeBarUpper i
    have hp' := hproxScaled i
    dsimp [Obj, SOptLib.compositeObjective] at hc hp' ⊢
    nlinarith [hc, hp', htargetScaled, hbarLinScaled]
  have hquadCoeff : ∀ i,
      L / 2 * (alpha ^ 2 * ‖xNext i - aux‖ ^ 2) -
          (alpha / gamma) *
            (((1 + mu * gamma) / 2) * ‖xNext i - aux‖ ^ 2) =
        - (alpha / (2 * gamma)) * den * ‖xNext i - aux‖ ^ 2 := by
    intro i
    rw [hden_def]
    field_simp [ne_of_gt hgamma_pos]
    ring
  have hresidualAbsorbPointwise : ∀ i,
      (L / 2 * (alpha ^ 2 * ‖xNext i - aux‖ ^ 2) -
          (alpha / gamma) *
            (((1 + mu * gamma) / 2) * ‖xNext i - aux‖ ^ 2)) -
          alpha * ⟪residual i, xNext i - xTarget⟫_ℝ ≤
        (alpha * gamma / (2 * den)) * ‖residual i‖ ^ 2 -
          alpha * ⟪residual i, aux - xTarget⟫_ℝ := by
    intro i
    let r := residual i
    let d := xNext i - aux
    let u := aux - xTarget
    have hq : 0 < den / gamma := div_pos hden_pos hgamma_pos
    have hy :=
      neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq
        (q := den / gamma) hq r d
    have hy_scaled := mul_le_mul_of_nonneg_left hy halpha_nonneg
    have hsplit : xNext i - xTarget = d + u := by
      simp only [d, u]
      abel
    have hquad :
        L / 2 * (alpha ^ 2 * ‖xNext i - aux‖ ^ 2) -
            (alpha / gamma) *
              (((1 + mu * gamma) / 2) * ‖xNext i - aux‖ ^ 2) =
          - (alpha / (2 * gamma)) * den * ‖xNext i - aux‖ ^ 2 := hquadCoeff i
    rw [hquad, hsplit]
    simp only [inner_add_right]
    dsimp [r, d, u] at hy_scaled ⊢
    field_simp [ne_of_gt hgamma_pos, ne_of_gt hden_pos] at hy_scaled ⊢
    nlinarith
  have hpointwiseAbsorbed : ∀ i,
      Obj (xBarNext i) +
          (alpha / gamma) * ((1 + mu * gamma) * Bnext i) ≤
        (1 - alpha - p) * Obj xBarPrev +
          alpha * Obj xTarget +
          p * (Lin snapshot + H snapshot) +
          (alpha / gamma) * Bprev +
          ((alpha * gamma / (2 * den)) * ‖residual i‖ ^ 2 -
            alpha * ⟪residual i, aux - xTarget⟫_ℝ) := by
    intro i
    have hpw := hpointwisePre i
    have hres := hresidualAbsorbPointwise i
    linarith
  let C : ℝ :=
    (1 - alpha - p) * Obj xBarPrev +
      alpha * Obj xTarget +
      p * (Lin snapshot + H snapshot) +
      (alpha / gamma) * Bprev
  let R : ι → ℝ := fun i =>
    (alpha * gamma / (2 * den)) * ‖residual i‖ ^ 2 -
      alpha * ⟪residual i, aux - xTarget⟫_ℝ
  have hE :
      Finset.univ.sum (fun i : ι =>
          w i *
            (Obj (xBarNext i) +
              (alpha / gamma) * ((1 + mu * gamma) * Bnext i))) ≤
        C + Finset.univ.sum (fun i : ι => w i * R i) := by
    calc
      Finset.univ.sum (fun i : ι =>
          w i *
            (Obj (xBarNext i) +
              (alpha / gamma) * ((1 + mu * gamma) * Bnext i))) ≤
        Finset.univ.sum (fun i : ι => w i * (C + R i)) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact mul_le_mul_of_nonneg_left
            (by simpa [C, R] using hpointwiseAbsorbed i) (hw_nonneg i)
      _ = C + Finset.univ.sum (fun i : ι => w i * R i) := by
          calc
            Finset.univ.sum (fun i : ι => w i * (C + R i)) =
                Finset.univ.sum (fun i : ι => w i * C) +
                  Finset.univ.sum (fun i : ι => w i * R i) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
            _ = Finset.univ.sum w * C +
                  Finset.univ.sum (fun i : ι => w i * R i) := by
              rw [Finset.sum_mul]
            _ = C * Finset.univ.sum w +
                  Finset.univ.sum (fun i : ι => w i * R i) := by
              ring
            _ = C + Finset.univ.sum (fun i : ι => w i * R i) := by
              rw [hw_sum]
              ring
  have hR :
      Finset.univ.sum (fun i : ι => w i * R i) ≤
        (alpha * gamma / (2 * den)) *
          (2 * LQ * (Phi snapshot - Lin snapshot)) := by
    simpa [R] using hresidualBudgetNeg
  have hpre :
      Finset.univ.sum (fun i : ι =>
          w i *
            (Obj (xBarNext i) +
              (alpha / gamma) * ((1 + mu * gamma) * Bnext i))) ≤
        (1 - alpha - p) * Obj xBarPrev +
          alpha * Obj xTarget +
          p * Obj snapshot +
          (alpha / gamma) * Bprev := by
    nlinarith [hE, hR, hnoiseComposite]
  simpa [Obj, mul_assoc] using
    SOptLib.finset_weighted_expectation_rescale_predivided_recurrence
      (s := Finset.univ) (w := w)
      (A := fun i : ι => Obj (xBarNext i))
      (B := fun i : ι => (1 + mu * gamma) * Bnext i)
      (gamma := gamma) (alpha := alpha) (p := p)
      (basePrev := Obj xBarPrev) (baseTarget := Obj xTarget)
      (baseSnapshot := Obj snapshot) (tailPrev := Bprev)
      halpha_pos hgamma_pos hw_sum hpre

-- Batch 1 promoted from Staging/pointwise_descent_with_exact_certificate_of_perturb_budget.lean
/-- Pointwise smooth/prox descent with an exact certificate absorbed by a
perturbation budget.

The theorem starts from a pointwise smooth upper bound and approximate
variational inequality, rewrites the step displacement as a stochastic
certificate, and absorbs the exact-certificate square together with the residual
inner product under the same scalar budget.

Layer: Layer1 | Gap: Level 1 (exact-certificate perturbation-budget pointwise descent)
Proof: first establish the raw smooth/prox descent algebra and the supplied
  composite-objective compatibility; then rewrite the displacement and residual
  identities into stochastic-certificate form and call the Hilbert perturbation
  budget lemma for the final absorption.
Source: smooth first-order descent calculus in real Hilbert spaces, proximal
  variational inequalities, and Mathlib ordered-ring/Hilbert-space norm algebra
Used in: nonconvex variance-reduced mirror descent one-step pointwise descent
  before expectation and epoch telescoping
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem pointwise_descent_with_exact_certificate_of_perturb_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (psi f : E → ℝ) (grad : E → E)
    (x y G exact stoch delta : E) (gamma L p q eta : ℝ)
    (hgamma_pos : 0 < gamma) (hp : 0 < p) (hq : 0 < q)
    (hbudget : gamma + 4 * p ≤ 2 * p / q)
    (hsmooth :
      f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2)
    (hproj :
      ⟪G, y - x⟫_ℝ ≤ eta - gamma⁻¹ * ‖y - x‖ ^ 2)
    (hpsi_eta : psi y ≤ f y + psi x - f x - eta)
    (hstoch : stoch = gamma⁻¹ • (x - y))
    (hdelta : G - grad x = delta)
    (hperturb : ‖exact - stoch‖ ≤ ‖delta‖) :
    psi y + p * ‖exact‖ ^ 2 ≤
      psi x - (gamma * (1 - L * gamma / 2) - 2 * p) * ‖stoch‖ ^ 2 +
        (gamma / (2 * q) + 2 * p) * ‖delta‖ ^ 2 := by
  have hraw :
      f y ≤
        f x - (gamma⁻¹ - L / 2) * ‖y - x‖ ^ 2 -
          ⟪G - grad x, y - x⟫_ℝ + eta := by
    let delta0 : E := G - grad x
    have hgrad : grad x = G - delta0 := by
      simp [delta0]
    have hinner_decomp :
        ⟪grad x, y - x⟫_ℝ =
          ⟪G, y - x⟫_ℝ - ⟪delta0, y - x⟫_ℝ := by
      rw [hgrad]
      simp [inner_sub_left]
    nlinarith [hsmooth, hproj, hinner_decomp]
  have hcomposite_raw :
      psi y ≤
        psi x - (gamma⁻¹ - L / 2) * ‖y - x‖ ^ 2 -
          ⟪G - grad x, y - x⟫_ℝ := by
    nlinarith
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hgamma_smul_stoch : gamma • stoch = x - y := by
    rw [hstoch, smul_smul, mul_inv_cancel₀ hgamma_ne, one_smul]
  have hdisp : y - x = -(gamma • stoch) := by
    calc
      y - x = -(x - y) := by abel
      _ = -(gamma • stoch) := by rw [← hgamma_smul_stoch]
  have hdist_sq :
      ‖y - x‖ ^ 2 = gamma ^ 2 * ‖stoch‖ ^ 2 := by
    rw [hdisp, norm_neg, norm_smul, Real.norm_of_nonneg (le_of_lt hgamma_pos)]
    ring
  have hcoeff_disp :
      (gamma⁻¹ - L / 2) * ‖y - x‖ ^ 2 =
        (gamma * (1 - L * gamma / 2)) * ‖stoch‖ ^ 2 := by
    rw [hdist_sq]
    field_simp [hgamma_ne]
  have hnoise :
      -⟪G - grad x, y - x⟫_ℝ = gamma * ⟪delta, stoch⟫_ℝ := by
    rw [hdelta, hdisp, inner_neg_right, inner_smul_right]
    ring
  have hpathwise :
      psi y ≤
        psi x - (gamma * (1 - L * gamma / 2)) * ‖stoch‖ ^ 2 +
          gamma * ⟪delta, stoch⟫_ℝ := by
    rw [hcoeff_disp] at hcomposite_raw
    nlinarith [hnoise]
  have hscalar :
      p * ‖exact‖ ^ 2 + gamma * ⟪delta, stoch⟫_ℝ ≤
        2 * p * ‖stoch‖ ^ 2 + (gamma / (2 * q) + 2 * p) * ‖delta‖ ^ 2 :=
    norm_sq_add_inner_le_base_sq_add_err_sq_of_norm_sub_le_of_budget
      (gamma := gamma) (p := p) (q := q)
      (le_of_lt hgamma_pos) hp hq hbudget hperturb
  linarith


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: selected-coordinate gradient-memory history characterization;
--   orig was `gradientStateCharacterization_of_process_equations`, renamed away
--   from RGEM equation numbering while exposing the reusable invariant for a
--   memory table updated at one sampled coordinate.
-- generality used: arbitrary sample-path type, coordinate type with
--   decidable equality, state type, value type with zero, selected-coordinate
--   stream, state run, gradient-memory projection, component-point memory
--   projection, and component gradient kernel; no measure, independence,
--   filtration, convexity, smoothness, topology, norm, inner-product, finite
--   coordinate, or finite-dimensional assumptions are used.
-- portable call pattern: finite-memory coordinate SGD, variance-reduced
--   gradient-table methods, and randomized block methods prove that an
--   unvisited coordinate still stores zero while a visited coordinate stores
--   the component gradient at its current stored component point; the state
--   record, selected-coordinate stream, point table, memory table, and gradient
--   kernel change while the two-case history conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   is independent of RGEM setup fields and theorem numbering; not a wrapper
--   around `Function.update` because it packages the induction over a whole
--   one-based sampled history and also transports stale component points for
--   previously visited coordinates.
-- coverage search: searched CATALOG/SOptLib/Staging for `selected coordinate
--   gradient memory`, `no previous hit`, `memory refresh`, `sampledAffineMemoryRefresh`,
--   and `selectedValueTableUpdate`; closest hits were one-step update APIs,
--   especially `sampledAffineMemoryRefresh` and `selectedValueTableUpdate`,
--   which do not state the history-level hit/no-hit invariant. LeanSearch for
--   coordinate memory recursion returned only unrelated coordinate/basis and
--   recursion primitives, so coverage is partial through proof ingredients.
-- minimal hypotheses: replaced the paper process relation by exactly the
--   initial zero memory, selected-coordinate gradient-memory successor
--   equation, and stale-coordinate component-point preservation used in the
--   proof.

/-- A selected-coordinate gradient-memory recursion has the expected history
characterization.

If the memory table starts at zero, each successor refreshes only the selected
coordinate to `grad selected (xmem current selected)`, and non-selected point
memories are preserved, then a coordinate that has never been selected still
has zero memory, while any selected coordinate stores the component gradient at
its current stored point.

Layer: Layer1 | Gap: Level 1 (selected-coordinate gradient-memory history invariant)
Proof: induction on the time horizon. The selected successor case is discharged
  by `Function.update`; the stale successor case uses the induction hypothesis
  and transports the component-point memory through the non-selected
  preservation equation.
Source: Mathlib natural-number induction, one-based interval arithmetic, and
  `Function.update` coordinate APIs
Used in: finite-memory stochastic coordinate methods characterizing stale
  gradient tables before no-hit and hit expectation splits
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem selectedCoordinateGradientMemory_characterization
    {Ω I E State : Type*} [DecidableEq I] [Zero E]
    (sample : ℕ → Ω → I) (run : ℕ → Ω → State)
    (y : State → I → E) (xmem : State → I → E) (grad : I → E → E)
    (h_zero : ∀ ω i, y (run 0 ω) i = 0)
    (h_y_succ :
      ∀ n ω,
        y (run (n + 1) ω) =
          Function.update (y (run n ω)) (sample (n + 1) ω)
            (grad (sample (n + 1) ω)
              (xmem (run (n + 1) ω) (sample (n + 1) ω))))
    (h_xmem_succ_of_ne :
      ∀ n ω {i : I}, i ≠ sample (n + 1) ω →
        xmem (run (n + 1) ω) i = xmem (run n ω) i)
    (t : ℕ) (ω : Ω) (i : I) :
    ((¬ ∃ r, 1 ≤ r ∧ r ≤ t ∧ sample r ω = i) →
        y (run t ω) i = 0) ∧
      ((∃ r, 1 ≤ r ∧ r ≤ t ∧ sample r ω = i) →
        y (run t ω) i = grad i (xmem (run t ω) i)) := by
  induction t with
  | zero =>
      constructor
      · intro _hno
        exact h_zero ω i
      · intro hex
        rcases hex with ⟨r, hr1, hrle, _hrsample⟩
        omega
  | succ n ih =>
      constructor
      · intro hno
        by_cases hsel : i = sample (n + 1) ω
        · exfalso
          exact hno ⟨n + 1, Nat.succ_pos n, le_rfl, hsel.symm⟩
        · have hyi :
              y (run (n + 1) ω) i = y (run n ω) i := by
            simpa [hsel] using congrFun (h_y_succ n ω) i
          have hprev_no : ¬ ∃ r, 1 ≤ r ∧ r ≤ n ∧ sample r ω = i := by
            intro hex
            rcases hex with ⟨r, hr1, hrle, hrsample⟩
            exact hno ⟨r, hr1, Nat.le_trans hrle (Nat.le_succ n), hrsample⟩
          exact hyi.trans (ih.1 hprev_no)
      · intro hex
        by_cases hsel : i = sample (n + 1) ω
        · have hyi :
              y (run (n + 1) ω) i =
                grad i (xmem (run (n + 1) ω) i) := by
            have hy_selected :
                y (run (n + 1) ω) (sample (n + 1) ω) =
                  grad (sample (n + 1) ω)
                    (xmem (run (n + 1) ω) (sample (n + 1) ω)) := by
              simpa using congrFun (h_y_succ n ω) (sample (n + 1) ω)
            simpa [hsel] using hy_selected
          exact hyi
        · have hprev_exists :
              ∃ r, 1 ≤ r ∧ r ≤ n ∧ sample r ω = i := by
            rcases hex with ⟨r, hr1, hrle, hrsample⟩
            have hrne : r ≠ n + 1 := by
              intro hre
              apply hsel
              rw [← hrsample, hre]
            have hrlt : r < n + 1 := lt_of_le_of_ne hrle hrne
            exact ⟨r, hr1, Nat.lt_succ_iff.mp hrlt, hrsample⟩
          have hyi :
              y (run (n + 1) ω) i = y (run n ω) i := by
            simpa [hsel] using congrFun (h_y_succ n ω) i
          have hxi :
              xmem (run (n + 1) ω) i = xmem (run n ω) i :=
            h_xmem_succ_of_ne n ω hsel
          calc
            y (run (n + 1) ω) i = y (run n ω) i := hyi
            _ = grad i (xmem (run n ω) i) := ih.2 hprev_exists
            _ = grad i (xmem (run (n + 1) ω) i) := by
              simpa using (congrArg (grad i) hxi).symm

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: selected-coordinate refresh branch identities; orig was
--   `positiveEtaGeneratedProcess_branch_identities`, renamed away from the
--   positive-eta generated RGEM process and exposed as the reusable branch
--   expansion for one sampled coordinate refresh.
-- generality used: arbitrary sample-path type, coordinate type with decidable
--   equality, refreshed/stale value families, refreshed/stale memory families,
--   a transformed memory payload, and a residual with a zero self-residual;
--   no measure, independence, filtration, convexity, smoothness, topology,
--   norm, inner-product, finite coordinate, or finite-dimensional assumptions
--   are used.
-- portable call pattern: sampled coordinate-memory methods such as finite-sum
--   coordinate SGD, SAG/SAGA-style table refreshes, randomized block methods,
--   and mini-batch refresh/stale proofs first establish selected and stale
--   branch equations, then repeatedly rewrite payloads and residuals before
--   conditional expectation or finite-average arguments.
-- counterargument checked: not paper-local traceability because the statement
--   is independent of RGEM setup fields and theorem numbering; not a duplicate
--   of Mathlib `Function.update` or SOptLib affine-refresh APIs because it
--   consumes an arbitrary branch law and packages the transformed payload plus
--   zero-residual stale branch that downstream expectation proofs use.
-- coverage search: searched SOptLib/catalog/source for `selectedCoordinate`,
--   `sampledAffineMemoryRefresh`, `selectedCoordinateSubtypeUpdate`, `branch
--   identities`, `payload`, and `residual`; closest hits unfold concrete
--   `Function.update` or affine refresh definitions and do not cover arbitrary
--   refreshed/stale branch equations with transformed payload and residual
--   conclusions. LeanSearch for selected-coordinate memory refresh branch
--   payload residual returned unrelated coordinate and topological residual
--   lemmas, so coverage is partial through lower-level update ingredients.
-- minimal hypotheses: the proof uses exactly the value branch equation, the
--   memory branch equation, and pointwise zero self-residual on stale memory;
--   all algorithm update, measurability, and sampling-law assumptions stay at
--   the caller that proves the two branch equations.

/-- Branch identities generated by a selected-coordinate refresh.

If a value table and a memory table have selected/stale branch equations at a
fixed query coordinate, then any payload of the memory table has the same branch
split, and any residual against the stale memory has zero stale branch whenever
the residual vanishes on equal stale inputs.

Layer: Layer1 | Gap: Level 1 (selected-coordinate refresh branch expansion)
Proof: rewrite by the supplied branch equations, split on whether the sampled
  coordinate is the query coordinate, and use the zero self-residual hypothesis
  in the stale branch.
Source: Mathlib decidable equality, `if` simplification, and coordinate
  table-update case-splitting APIs
Used in: randomized coordinate-memory refresh proofs before conditional
  expectation splits of refreshed payloads and stale residuals
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/4/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem selectedCoordinateRefresh_branch_identities
    {Ω I Value Mem Payload Residual : Type*} [DecidableEq I] [Zero Residual]
    (sample : Ω → I) (query : I)
    (valueStale valueRefreshed : Ω → Value)
    (valueAfter : Ω → I → Value)
    (stale refreshed : Ω → Mem)
    (memAfter : Ω → I → Mem)
    (payload : Mem → Payload)
    (residual : Mem → Mem → Residual)
    (hvalue_branch :
      ∀ ω : Ω,
        valueAfter ω query =
          if sample ω = query then valueRefreshed ω else valueStale ω)
    (hmem_branch :
      ∀ ω : Ω,
        memAfter ω query =
          if sample ω = query then refreshed ω else stale ω)
    (hresidual_self :
      ∀ ω : Ω, residual (stale ω) (stale ω) = 0) :
    (∀ ω : Ω,
      valueAfter ω query =
        if sample ω = query then valueRefreshed ω else valueStale ω) ∧
    (∀ ω : Ω,
      memAfter ω query =
        if sample ω = query then refreshed ω else stale ω) ∧
    (∀ ω : Ω,
      payload (memAfter ω query) =
        if sample ω = query then payload (refreshed ω) else payload (stale ω)) ∧
    (∀ ω : Ω,
      residual (memAfter ω query) (stale ω) =
        if sample ω = query then residual (refreshed ω) (stale ω) else 0) := by
  refine ⟨hvalue_branch, hmem_branch, ?_, ?_⟩
  · intro ω
    rw [hmem_branch ω]
    by_cases hsel : sample ω = query <;> simp [hsel]
  · intro ω
    rw [hmem_branch ω]
    by_cases hsel : sample ω = query
    · simp [hsel]
    · simp [hsel, hresidual_self ω]

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: pre-update readout determinism from a strict driver prefix; orig
--   was `positiveEtaXIterate_eq_of_strictPastWindow_eq`, renamed away from RGEM
--   positive-eta process terminology while exposing the algorithm-frame fact
--   that a time-`t` readout computed from state `t-1` ignores the current driver.
-- generality used: arbitrary sample space, driver type, state type, readout
--   type, Nat-indexed driver stream, recursive state process, finite-window
--   offset, constant initial state, successor congruence, a public current
--   readout, its bridge to the pre-update readout, and strict-prefix pre-update
--   readout invariance; no measure, independence, filtration, convexity,
--   smoothness, topology, norm, inner-product, or oracle assumptions are used.
-- portable call pattern: stochastic algorithms whose public iterate at time
--   `t` is computed from the previous state before applying the current sampled
--   coordinate use this to prove strict-past measurability or integrability; the
--   state record, driver stream, update congruence, offset, current readout, and
--   pre-update readout map vary while the strict-prefix current-readout equality
--   conclusion stays fixed.
-- counterargument checked: not paper-local traceability, because the theorem is
--   independent of RGEM fields and theorem numbering; not a duplicate of
--   `recursive_process_eq_of_driver_prefix_eq`, because that existing theorem
--   proves equality of full prior states, while this theorem adds the reusable
--   pre-update readout layer and its strict-prefix invariance hypothesis.
-- coverage search: searched SOptLib/project for `recursive process`, `driver
--   prefix`, `readout`, `strict past`, and `sampleWindow`; the closest hit is
--   `recursive_process_eq_of_driver_prefix_eq` in `SOptLib.Model.Iterates`,
--   which is used as a proof ingredient but does not state readout equality.
--   LeanSearch for "recursive process equal if driver prefix equal readout"
--   returned only generic Nat recursion congruence lemmas, so coverage is
--   partial through proof ingredients.
-- minimal hypotheses: localized to the segment needed at time `t`; the proof
--   uses constant initialization, successor congruence only through `t - 1`,
--   the public-to-pre-update readout bridge at time `t`, and strict-prefix
--   invariance of the time-`t` pre-update readout.

/-- A pre-update readout is determined by the strict driver prefix.

If a recursive state process is driven by a Nat-indexed driver stream and a
time-`n+1` readout of a candidate previous state is invariant under equal
length-`n` driver windows, then the public readout at time `t` agrees for two
sample paths with the same strict driver past.

Layer: Layer1 | Gap: Level 1 (pre-update readout strict-prefix determinism)
Proof: apply recursive-process finite-prefix determinism to identify the
  previous states, then use the public readout bridge, the pre-update readout's
  strict-prefix invariance, and rewriting.
Source: Mathlib natural-number subtraction, Fin-indexed sample windows, and
  SOptLib recursive-process finite-prefix determinism
Used in: sampled-coordinate stochastic methods proving that a current iterate
  computed before the coordinate refresh is strict-past determined
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation -/
theorem pre_update_readout_eq_of_strict_driver_prefix_eq
    {Omega Driver State X : Type*}
    (driver : Nat → Omega → Driver)
    (process : Nat → Omega → State)
    (current : Nat → Omega → X)
    (readout : Nat → Omega → State → X)
    (offset : Nat)
    (initial : State)
    (h_zero : ∀ omega : Omega, process 0 omega = initial)
    {t : Nat} (ht : 1 ≤ t)
    (h_succ_congr :
      ∀ n : Nat, n + 1 ≤ t - 1 → ∀ ⦃omega omega' : Omega⦄,
        process n omega = process n omega' →
        driver (offset + n) omega = driver (offset + n) omega' →
        process (n + 1) omega = process (n + 1) omega')
    (h_current_readout :
      ∀ omega : Omega, current t omega = readout t omega (process (t - 1) omega))
    (h_readout_strict :
      ∀ ⦃omega omega' : Omega⦄ (state : State),
        sampleWindow driver offset (t - 1) omega =
          sampleWindow driver offset (t - 1) omega' →
        readout t omega state = readout t omega' state) :
    ∀ ⦃omega omega' : Omega⦄,
      sampleWindow driver offset (t - 1) omega =
        sampleWindow driver offset (t - 1) omega' →
      current t omega = current t omega' := by
  intro omega omega' hprefix
  let n : Nat := t - 1
  have hn_succ : n + 1 = t := by
    dsimp [n]
    exact Nat.sub_add_cancel ht
  have hprev : process n omega = process n omega' := by
    exact recursive_process_eq_of_driver_prefix_eq
      (ξ := driver) (process := process)
      (offset := offset) (R := n) (t := n)
      (initial := initial)
      h_zero
      (by
        intro k _hk omega omega' hprocess hdriver
        exact h_succ_congr k (by simpa [n] using _hk) hprocess hdriver)
      (Nat.le_refl n)
      (by simpa [n] using hprefix)
  have hreadout :
      readout t omega (process (t - 1) omega) =
        readout t omega' (process (t - 1) omega') := by
    calc
      readout t omega (process (t - 1) omega)
        = readout t omega' (process n omega) := by
          simpa [n] using h_readout_strict (process n omega) hprefix
      _ = readout t omega' (process n omega') := by
          rw [hprev]
      _ = readout t omega' (process (t - 1) omega') := by
          simp [n]
  calc
    current t omega = readout t omega (process (t - 1) omega) :=
      h_current_readout omega
    _ = readout t omega' (process (t - 1) omega') := hreadout
    _ = current t omega' := (h_current_readout omega').symm

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: selected-coordinate memory remains initial without a previous
--   hit; orig was `positiveEta_block_iterate_eq_x0_of_no_previous_update`,
--   renamed away from positive-eta/RGEM terminology to expose the reusable
--   table-memory invariant.
-- generality used: arbitrary sample-path type, coordinate type, memory value
--   type, state type, selected-coordinate stream, generated run, memory
--   projection, and initial memory value; no measure, independence,
--   filtration, convexity, smoothness, topology, norm, inner-product,
--   decidable equality, finite-coordinate, or finite-dimensional assumptions
--   are used.
-- portable call pattern: randomized coordinate descent, finite-sum
--   variance-reduced table methods, and block-memory mirror-descent proofs can
--   show an unvisited coordinate's stored point/value still equals its
--   initializer; the state record, sampled coordinate stream, memory
--   projection, initial value, and stale-coordinate preservation equation
--   change while the no-previous-hit conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   is independent of RGEM setup fields, eta domains, and theorem numbering;
--   not a caller-side expression because it packages the recurring induction
--   from one-step nonselected-coordinate preservation to a history-level
--   no-hit invariant; not covered by `Function.update` because this theorem
--   does not require the selected branch to be an update formula.
-- coverage search: searched CATALOG/SOptLib/Staging/project for `selected
--   coordinate memory`, `no previous hit`, `memory init`, `one hot refresh`,
--   and `sampledAffineMemoryRefresh`; closest hits were
--   `selectedCoordinateGradientMemory_characterization`,
--   `coordinateGradientMemoryMatches_of_oneHotRefresh`, and one-step refresh
--   APIs, which either characterize gradient memory or only state a one-step
--   stale coordinate rule. LeanSearch for coordinate memory no-hit recursion
--   returned hitting-time and `Function.update` lemmas only, so coverage is
--   partial through proof ingredients rather than statement-level API.
-- minimal hypotheses: replaced the paper process equations by exactly the
--   initial memory equality and the nonselected-coordinate successor
--   preservation equation used in the proof.

/-- A selected-coordinate memory entry remains at its initializer until it is hit.

If a memory table starts with value `init` at every coordinate, and every
successor preserves each nonselected coordinate, then any coordinate absent from
the one-based sample prefix still stores `init` at the end of that prefix.

Layer: Layer1 | Gap: Level 1 (selected-coordinate no-hit memory invariant)
Proof: induction on the time horizon. The selected successor branch contradicts
  the no-hit hypothesis, and the stale successor branch combines the one-step
  preservation equation with the induction hypothesis.
Source: Mathlib natural-number induction and one-based interval arithmetic APIs
Used in: randomized coordinate-memory methods before stale residual no-hit
  branch simplification
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem selectedCoordinateMemory_eq_init_of_no_previous_hit
    {Ω I M State : Type*}
    (sample : ℕ → Ω → I) (run : ℕ → Ω → State)
    (mem : State → I → M) (init : M)
    (h_init : ∀ ω i, mem (run 0 ω) i = init)
    (hmem_succ_of_ne :
      ∀ n ω {i : I}, i ≠ sample (n + 1) ω →
        mem (run (n + 1) ω) i = mem (run n ω) i)
    {t : ℕ} {ω : Ω} {i : I}
    (hno : ¬ ∃ r, 1 ≤ r ∧ r ≤ t ∧ sample r ω = i) :
    mem (run t ω) i = init := by
  induction t with
  | zero =>
      exact h_init ω i
  | succ n ih =>
      by_cases hsel : i = sample (n + 1) ω
      · exfalso
        exact hno ⟨n + 1, Nat.succ_pos n, le_rfl, hsel.symm⟩
      · have hprev_no :
            ¬ ∃ r, 1 ≤ r ∧ r ≤ n ∧ sample r ω = i := by
          intro hex
          rcases hex with ⟨r, hr1, hrle, hrsample⟩
          exact hno ⟨r, hr1, Nat.le_trans hrle (Nat.le_succ n), hrsample⟩
        calc
          mem (run (n + 1) ω) i = mem (run n ω) i := by
            exact hmem_succ_of_ne n ω hsel
          _ = init := ih hprev_no

end SOptLib


-- Generalization plan (G0):
-- concept/name: finite-sum support collapse for a single-coordinate table update; orig was positiveEta_y_update_sum_eq_sample_delta
-- generality used: finite index type with decidable equality and an additive commutative group target; no measure, convexity, smoothness, oracle, norm, or inner-product assumptions are used
-- portable call pattern: randomized coordinate, block-memory, and variance-reduced methods that refresh one table entry and then collapse a componentwise finite-sum delta before telescoping or taking expectations; the index type, table values, sampled coordinate, and off-sampled update equation change while the conclusion shape stays fixed
-- counterargument checked: this is not paper-local traceability because the statement is paper-free and captures the recurring sampled-update support reduction; it is not a pure wrapper over one caller expression because callers otherwise reprove the off-sampled zero summand step
-- coverage search: searched project/SOptLib/catalog for `sum update off sampled`, `sampled coordinate sub`, and `Finset.sum sub update`; LeanSearch returned `Finset.sum_update_of_mem`, `Fintype.sum_eq_add_sum_compl`, `Finset.sum_sub_distrib`, and adjacent-difference telescopes, which are partial ingredients but not this difference-collapse statement
-- minimal hypotheses: all already minimal for this proof: `[Fintype iota]` supplies `univ`, and `[AddCommGroup E]` supplies finite sums, subtraction, and additive cancellation

/-- If two finite tables differ only at a sampled coordinate, the sum of all
componentwise differences is the sampled-coordinate difference.

Layer: Layer1 | Gap: Level 1 (sampled-coordinate finite-sum update collapse)
Proof: apply `Finset.sum_eq_single` at the sampled coordinate; every other
  summand is zero by the off-sampled update hypothesis.
Source: Mathlib finite sums over fintypes and `Finset.sum_eq_single`
Used in: random gradient extrapolation sampled-memory update before the
  inner-product and expectation telescopes
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation -/
theorem sum_update_sub_eq_sampled_sub_of_update_off
    {iota E : Type*} [Fintype iota] [AddCommGroup E]
    (yPrev yNext : iota → E) (sampled : iota)
    (hupdate_off : ∀ i, i ≠ sampled → yNext i = yPrev i) :
    Finset.sum Finset.univ (fun i => yNext i - yPrev i) =
      yNext sampled - yPrev sampled := by
  classical
  rw [Finset.sum_eq_single sampled]
  · intro i _hi hi_ne
    simp [hupdate_off i hi_ne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ sampled))

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: selected stale-memory residual expectation equals a geometric
--   no-refresh factor times the initial residual budget; orig was
--   `selected_stale_gradient_expectation_eq_positive_domain`, renamed away
--   from RGEM-specific gradient/setup wording while keeping the stochastic
--   finite-memory residual concept.
-- generality used: arbitrary measurable probability space, finite nonempty
--   measurable coordinate type with decidable equality, an independent
--   finite-uniform sample stream, an abstract coordinate residual process,
--   a pointwise no-previous-hit residual split, and an initial finite-average
--   residual budget; no objective, oracle, convexity, norm, inner product,
--   Hilbert-space, or finite-dimensional assumptions are used.
-- portable call pattern: randomized coordinate descent, table-refresh
--   variance-reduction, block mirror descent, and stale-memory stochastic
--   approximation proofs call the same step after proving that an unrefreshed
--   selected coordinate carries its initial residual while a previously
--   refreshed coordinate contributes zero; the residual map, memory process,
--   sample law, and initial budget change while the geometric conclusion stays
--   fixed.
-- counterargument checked: not paper-local traceability because the theorem
--   has no setup fields, theorem numbers, gradient formula, or algorithm
--   acronym; not a one-line wrapper because it packages the selected-coordinate
--   finite-sum expansion, integrability of the hit/no-hit summands, the
--   first-hit expectation formula, and the initial average budget. Existing
--   staged entries cover the scalar first-hit expectation and no-hit
--   probability separately, not this residual-table expectation assembly.
-- coverage search: searched CATALOG/SOptLib/Staging for selected stale memory
--   residual, geometric initial, no previous hit expectation, and finite
--   uniform sample stream. Relevant hits were
--   `expectation_current_hit_no_previous_hit_const_eq`,
--   `measureReal_no_hit_prefix_of_iid_uniform_finite`, and
--   `measurableSet_noHit_of_sampleWindow_comap`; they are proof ingredients
--   and do not state the selected residual expectation from a residual split
--   plus initial average budget.
-- minimal hypotheses: the algorithm-specific gradient norm square is replaced
--   by an arbitrary real residual table; the process equation is replaced by
--   the pointwise no-hit split actually used; probability is needed for the
--   first-hit expectation and finite measure integrability.

/-- The selected stale-memory residual has geometric initial expectation.

If an independent finite-uniform coordinate stream selects the current
coordinate and a residual table is equal to its initial coordinate residual
exactly on the event that the coordinate has not appeared in the strict
one-based prefix, then the expected selected residual equals the geometric
no-refresh factor times the finite-average initial residual budget.

Layer: Layer1 | Gap: Level 1 (selected stale-memory residual expectation assembly)
Proof: expand the selected residual as a finite sum over current-coordinate
  hit/no-previous-hit summands, integrate the finite sum, apply the finite
  uniform first-hit expectation formula to each coordinate, and fold the
  initial average budget.
Source: Mathlib probability independence, finite measurable spaces, Bochner
  finite-sum integral APIs, and finite-memory stochastic approximation algebra
Used in: randomized gradient extrapolation stale gradient-memory residual
  estimate after the no-previous-refresh split and before the final residual
  budget telescope
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem selectedStaleMemoryResidual_expectation_eq_geometric_initial
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [mι : MeasurableSpace ι]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : ℕ → Ω → ι) (residual : ι → ℕ → Ω → ℝ)
    (initialResidual : ι → ℝ) (sigma0 : ℝ) (t : ℕ)
    (hsample_measurable : ∀ n : ℕ, Measurable (sample n))
    (hsample_iIndep : iIndepFun sample μ)
    (hsample_uniform :
      ∀ n : ℕ, ∀ i : ι,
        (Measure.map (sample n) μ).real ({i} : Set ι) =
          (Fintype.card ι : ℝ)⁻¹)
    (hresidual_split :
      ∀ i : ι, ∀ ω : Ω,
        residual i t ω =
          (by
            classical
            exact
              if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i then
                initialResidual i
              else
                0))
    (hinitial :
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => initialResidual i) =
        sigma0 ^ 2) :
    SOptLib.expectation μ (fun ω : Ω => residual (sample t ω) t ω) =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
        sigma0 ^ 2 := by
  classical
  let q : ℝ := (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1)
  let term : ι → Ω → ℝ := fun i ω =>
    if sample t ω = i then
      if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i then
        initialResidual i
      else
        0
    else
      0
  have hpoint :
      (fun ω : Ω => residual (sample t ω) t ω) =
        fun ω => Finset.sum Finset.univ (fun i : ι => term i ω) := by
    funext ω
    let j : ι := sample t ω
    have hsum :
        Finset.sum Finset.univ (fun i : ι => term i ω) = term j ω := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro b _hb hbj
        dsimp [term]
        rw [if_neg]
        exact fun h => hbj h.symm
      · intro hjnot
        exact False.elim (hjnot (Finset.mem_univ j))
    have htermj : term j ω = residual (sample t ω) t ω := by
      dsimp [term, j]
      rw [if_pos rfl]
      exact (hresidual_split (sample t ω) ω).symm
    exact htermj.symm.trans hsum.symm
  have hterm_int :
      ∀ i ∈ Finset.univ, Integrable (fun ω : Ω => term i ω) μ := by
    intro i _hi
    let Event : Set Ω :=
      {ω | sample t ω = i ∧
        ∀ r, 1 ≤ r → r ≤ t - 1 → sample r ω ≠ i}
    have hsample_t_meas :
        MeasurableSet ((sample t) ⁻¹' ({i} : Set ι)) :=
      (measurableSet_singleton i).preimage (hsample_measurable t)
    have hcurrent_meas : MeasurableSet {ω : Ω | sample t ω = i} := by
      have hset :
          {ω : Ω | sample t ω = i} = (sample t) ⁻¹' ({i} : Set ι) := by
        ext ω
        simp
      rw [hset]
      exact hsample_t_meas
    have hno_past :
        @MeasurableSet Ω
          (MeasurableSpace.comap (SOptLib.sampleWindow sample 1 (t - 1))
            (by infer_instance : MeasurableSpace (Fin (t - 1) → ι)))
          {ω : Ω | ∀ r : ℕ, 1 ≤ r → r < t → sample r ω ≠ i} := by
      simpa using
        (SOptLib.measurableSet_noHit_of_sampleWindow_comap
          (sample := sample) (offset := 1) (stop := t) (a := i))
    have hK_meas :
        Measurable (SOptLib.sampleWindow sample 1 (t - 1)) := by
      refine measurable_pi_lambda (f := SOptLib.sampleWindow sample 1 (t - 1)) ?_
      intro r
      exact by
        simpa [SOptLib.sampleWindow] using hsample_measurable (1 + r.1)
    have hno_ambient_lt :
        MeasurableSet {ω : Ω | ∀ r : ℕ, 1 ≤ r → r < t → sample r ω ≠ i} :=
      hK_meas.comap_le _ hno_past
    have hset_le_lt :
        {ω : Ω | ∀ r : ℕ, 1 ≤ r → r ≤ t - 1 → sample r ω ≠ i} =
          {ω : Ω | ∀ r : ℕ, 1 ≤ r → r < t → sample r ω ≠ i} := by
      ext ω
      constructor
      · intro h r hr_one hr_lt
        exact h r hr_one (by omega)
      · intro h r hr_one hr_le
        exact h r hr_one (by omega)
    have hno_meas :
        MeasurableSet {ω : Ω |
          ∀ r : ℕ, 1 ≤ r → r ≤ t - 1 → sample r ω ≠ i} := by
      rw [hset_le_lt]
      exact hno_ambient_lt
    have hEvent_meas : MeasurableSet Event := by
      simpa [Event, Set.setOf_and] using hcurrent_meas.inter hno_meas
    have hterm_indicator :
        (fun ω : Ω => term i ω) =
          Event.indicator (fun _ : Ω => initialResidual i) := by
      funext ω
      have hiff :
          (¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i) ↔
            (∀ r, 1 ≤ r → r ≤ t - 1 → sample r ω ≠ i) := by
        constructor
        · intro hno r hr_one hr_le heq
          exact hno ⟨r, hr_one, hr_le, heq⟩
        · intro hno hex
          rcases hex with ⟨r, hr_one, hr_le, heq⟩
          exact hno r hr_one hr_le heq
      by_cases hsel : sample t ω = i
      · by_cases hno : ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i
        · have hmem : ω ∈ Event := ⟨hsel, hiff.mp hno⟩
          rw [Set.indicator_of_mem hmem]
          dsimp [term]
          rw [if_pos hsel, if_pos hno]
        · have hnotmem : ω ∉ Event := by
            intro hmem
            exact hno (hiff.mpr hmem.2)
          rw [Set.indicator_of_notMem hnotmem]
          dsimp [term]
          rw [if_pos hsel, if_neg hno]
      · have hnotmem : ω ∉ Event := by
          intro hmem
          exact hsel hmem.1
        rw [Set.indicator_of_notMem hnotmem]
        dsimp [term]
        rw [if_neg hsel]
    rw [hterm_indicator]
    exact (integrable_const (initialResidual i)).indicator hEvent_meas
  calc
    SOptLib.expectation μ (fun ω : Ω => residual (sample t ω) t ω)
        = SOptLib.expectation μ
            (fun ω : Ω => Finset.sum Finset.univ (fun i : ι => term i ω)) := by
          rw [hpoint]
    _ = Finset.sum Finset.univ
        (fun i : ι => SOptLib.expectation μ (fun ω : Ω => term i ω)) := by
          unfold SOptLib.expectation
          exact MeasureTheory.integral_finset_sum Finset.univ hterm_int
    _ = Finset.sum Finset.univ
        (fun i : ι =>
          (Fintype.card ι : ℝ)⁻¹ * q * initialResidual i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa [term, q, mul_assoc] using
            SOptLib.expectation_current_hit_no_previous_hit_const_eq
              (μ := μ) (sample := sample) t i (initialResidual i)
              hsample_measurable hsample_iIndep hsample_uniform
    _ = q * ((Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => initialResidual i)) := by
          calc
            Finset.sum Finset.univ
                (fun i : ι =>
                  (Fintype.card ι : ℝ)⁻¹ * q * initialResidual i)
                = Finset.sum Finset.univ
                    (fun i : ι => initialResidual i *
                      ((Fintype.card ι : ℝ)⁻¹ * q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  ring
            _ = Finset.sum Finset.univ (fun i : ι => initialResidual i) *
                  ((Fintype.card ι : ℝ)⁻¹ * q) := by
                  rw [Finset.sum_mul]
            _ = q * ((Fintype.card ι : ℝ)⁻¹ *
                  Finset.sum Finset.univ (fun i : ι => initialResidual i)) := by
                  ring
    _ = q * sigma0 ^ 2 := by
          rw [hinitial]
    _ = (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
        sigma0 ^ 2 := by
          rfl

end SOptLib

-- Generalization plan (G0):
-- concept/name: terminal residual Young split bounded by stale residual; orig
--   was `proposition56_terminal_residual_pointwise_positive_domain`.
-- generality used: arbitrary real inner-product space, abstract Bregman-like
--   potential `V`, abstract primal/dual size functionals, pointwise support,
--   lower-bound, residual-split, current-residual nonnegativity, penalty
--   coefficient domination, and zero-penalty branch hypotheses; no measure,
--   independence, integrability, convexity, oracle, filtration, or
--   finite-dimensional assumptions are used by the proof.
-- portable call pattern: mirror-descent, block-coordinate, variance-reduced,
--   and gradient-extrapolation terminal residual proofs can call this after
--   proving a terminal displacement support bound, Bregman lower bound, memory
--   residual split, smoothness-penalty domination, and zero-smoothness collapse;
--   the displacement, residuals, gauges, Bregman model, and scalar schedules
--   vary while the stale-residual conclusion keeps the same shape.
-- counterargument checked: this is not paper-local traceability because it
--   packages the reusable composition of Young absorption, residual splitting,
--   current-residual cancellation, and the totalized zero-`L` branch. It is not
--   a duplicate of the already-staged inner Young, residual split, zero-`L`,
--   or scalar coefficient lemmas, which cover proper substeps but not the
--   terminal residual assembly.
-- coverage search: searched CATALOG/SOptLib/Staging for `terminal residual`,
--   `Young split stale residual`, `Bregman lower residual split dualNorm`, and
--   `current residual penalty coefficient`; hits were the partial staged
--   lemmas `neg_inner_sub_bregman_young_le_scaled_dualNorm_sq`,
--   `size_sub_sq_le_two_mul_size_sub_sq_add_two_mul_size_sub_sq_of_add_sq`,
--   `residual_coeff_nonpos_of_two_mul_alpha_mul_L_le`, and
--   `zero_lipschitz_gradient_residual_dualNorm_sq_eq_zero`, but no full
--   positive terminal-residual assembly. LeanSearch for the same Young
--   Bregman residual assembly failed with an upstream 521 response.
-- minimal hypotheses: all algorithm fields are replaced by pointwise facts;
--   the proof uses exactly `0 <= theta`, `0 < M`, `0 <= L`, support, Bregman
--   lower bound, residual split, `0 <= Ecur`, `4 * L <= tau * M`, and
--   `L = 0 -> Ecur = 0`.

/-- A terminal residual Young split is bounded by the stale residual term.

The terminal inner product is first absorbed by a Bregman lower bound and a
dual/primal support inequality.  A two-way residual split then separates the
current and stale residuals; the current residual is cancelled either by the
positive penalty coefficient or by the zero-`L` collapse branch.

Layer: Layer1 | Gap: Level 1 (terminal residual Young split assembly)
Proof: complete the scalar Young square against the Bregman lower bound, scale
  the residual split, and cancel the current residual using the penalty
  coefficient when `L > 0`; when `L = 0`, rewrite the current residual to zero.
Source: convex optimization mirror-descent residual algebra and Mathlib real
  inner-product/ordered-field arithmetic APIs
Used in: randomized gradient extrapolation terminal gradient-memory residual
  absorption before the final stale-residual telescope
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/proof/proposition_5_6/terminal_residual
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem terminal_residual_young_split_le_stale_residual
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E → ℝ) (primalNorm dualNorm : E → ℝ)
    (theta M tau L Ecur Estale : ℝ) (x y d zeta : E)
    (htheta_nonneg : 0 ≤ theta)
    (hM_pos : 0 < M)
    (hL_nonneg : 0 ≤ L)
    (hsupport : |⟪zeta, d⟫_ℝ| ≤ dualNorm zeta * primalNorm d)
    (hV_lower : (1 / 2 : ℝ) * primalNorm d ^ 2 ≤ V x y)
    (hsplit : dualNorm zeta ^ 2 ≤ 2 * Ecur + 2 * Estale)
    (hEcur_nonneg : 0 ≤ Ecur)
    (hpenalty_dom : 4 * L ≤ tau * M)
    (hEcur_zero : L = 0 → Ecur = 0) :
    theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y -
        theta * (tau / (2 * L) * Ecur) ≤
      (2 * theta / M) * Estale := by
  have hcoeff_nonneg : 0 ≤ theta / M :=
    div_nonneg htheta_nonneg (le_of_lt hM_pos)
  have hinner_support :
      ⟪d, zeta⟫_ℝ ≤ dualNorm zeta * primalNorm d := by
    have hle_abs : ⟪d, zeta⟫_ℝ ≤ |⟪zeta, d⟫_ℝ| := by
      simpa [real_inner_comm] using (le_abs_self ⟪zeta, d⟫_ℝ)
    exact hle_abs.trans hsupport
  have hyoung :
      theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y ≤
        (theta / M) * dualNorm zeta ^ 2 := by
    by_cases htheta_pos : 0 < theta
    · let c : ℝ := theta
      let A : ℝ := theta * M / 2
      have hc_nonneg : 0 ≤ c := by
        dsimp [c]
        exact htheta_nonneg
      have hA_pos : 0 < A := by
        dsimp [A]
        nlinarith [htheta_pos, hM_pos]
      have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
      have hcoef : c ^ 2 / (2 * A) = theta / M := by
        have hM_ne : M ≠ 0 := ne_of_gt hM_pos
        have htheta_ne : theta ≠ 0 := ne_of_gt htheta_pos
        dsimp [c, A]
        field_simp [hM_ne, htheta_ne]
      have hyoung_base :
          c * (dualNorm zeta * primalNorm d) -
              A * ((1 / 2 : ℝ) * primalNorm d ^ 2) ≤
            (c ^ 2 / (2 * A)) * dualNorm zeta ^ 2 := by
        have hsq : 0 ≤ (A * primalNorm d - c * dualNorm zeta) ^ 2 :=
          sq_nonneg _
        have hA_ne : A ≠ 0 := ne_of_gt hA_pos
        field_simp [hA_ne]
        nlinarith [hsq, hA_pos]
      have hinner_scaled :
          c * ⟪d, zeta⟫_ℝ ≤ c * (dualNorm zeta * primalNorm d) :=
        mul_le_mul_of_nonneg_left hinner_support hc_nonneg
      have hV_scaled :
          -A * V x y ≤ -A * ((1 / 2 : ℝ) * primalNorm d ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hV_lower hA_nonneg]
      calc
        theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y
            = c * ⟪d, zeta⟫_ℝ - A * V x y := by
              simp [c, A]
        _ ≤ c * (dualNorm zeta * primalNorm d) -
              A * ((1 / 2 : ℝ) * primalNorm d ^ 2) := by
            nlinarith [hinner_scaled, hV_scaled]
        _ ≤ (c ^ 2 / (2 * A)) * dualNorm zeta ^ 2 := hyoung_base
        _ = (theta / M) * dualNorm zeta ^ 2 := by
            rw [hcoef]
    · have htheta_zero : theta = 0 :=
        le_antisymm (le_of_not_gt htheta_pos) htheta_nonneg
      simp [htheta_zero]
  have hsplit_scaled :
      (theta / M) * dualNorm zeta ^ 2 ≤
        (2 * theta / M) * Ecur + (2 * theta / M) * Estale := by
    have hmul := mul_le_mul_of_nonneg_left hsplit hcoeff_nonneg
    calc
      (theta / M) * dualNorm zeta ^ 2 ≤
          (theta / M) * (2 * Ecur + 2 * Estale) := hmul
      _ = (2 * theta / M) * Ecur + (2 * theta / M) * Estale := by
          ring
  have hbase :
      theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y ≤
        (2 * theta / M) * Ecur + (2 * theta / M) * Estale :=
    hyoung.trans hsplit_scaled
  by_cases hLpos : 0 < L
  · let penCoeff : ℝ := theta * tau / (2 * L)
    have hcoeff_pen : 2 * theta / M - penCoeff ≤ 0 := by
      have h2L_pos : 0 < 2 * L := by nlinarith
      have hbase_coeff : 2 / M ≤ tau / (2 * L) := by
        field_simp [hM_pos.ne', h2L_pos.ne']
        nlinarith [hpenalty_dom]
      have hscaled :
          theta * (2 / M) ≤ theta * (tau / (2 * L)) :=
        mul_le_mul_of_nonneg_left hbase_coeff htheta_nonneg
      have hscaled' :
          2 * theta / M ≤ penCoeff := by
        dsimp [penCoeff]
        convert hscaled using 1 <;> ring
      nlinarith
    have hcancel : (2 * theta / M - penCoeff) * Ecur ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoeff_pen hEcur_nonneg
    calc
      theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y -
          theta * (tau / (2 * L) * Ecur)
          =
          (theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y) -
            penCoeff * Ecur := by
            dsimp [penCoeff]
            ring
      _ ≤ ((2 * theta / M) * Ecur + (2 * theta / M) * Estale) -
            penCoeff * Ecur :=
          sub_le_sub_right hbase _
      _ = (2 * theta / M - penCoeff) * Ecur +
            (2 * theta / M) * Estale := by
          ring
      _ ≤ 0 + (2 * theta / M) * Estale :=
          add_le_add hcancel le_rfl
      _ = (2 * theta / M) * Estale := by
          ring
  · have hLzero : L = 0 :=
      le_antisymm (le_of_not_gt hLpos) hL_nonneg
    have hcur_zero : Ecur = 0 := hEcur_zero hLzero
    have hbase_zero :
        theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y ≤
          (2 * theta / M) * Estale := by
      rw [hcur_zero] at hbase
      simpa using hbase
    calc
      theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y -
          theta * (tau / (2 * L) * Ecur)
          =
          theta * ⟪d, zeta⟫_ℝ - (theta * M / 2) * V x y := by
          rw [hcur_zero]
          ring
      _ ≤ (2 * theta / M) * Estale := hbase_zero


-- Promoted from Staging/smooth_descent_affine_update_with_direction_error.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: smooth descent for an affine direction update with direction
--   error; orig was `lemma1_pointwise_descent_bound_of_generated_quotient_boundary`
-- generality used: arbitrary real inner-product seminormed additive commutative
--   group, an objective and selected gradient, two points, a direction and its
--   pointwise error, and real smoothness/stepsize scalars; no measure,
--   probability, completeness, finite-dimensionality, or convexity is used
-- portable call pattern: biased SGD, stochastic recursive momentum,
--   variance-reduced gradient, and learned-direction methods supply their own
--   pointwise smooth upper model, affine update, and direction-error identity
--   while reusing the same objective-decrease conclusion
-- counterargument checked: not paper-local traceability or a caller-side
--   expression because it composes three independently supplied algorithm
--   contracts with nontrivial Hilbert coefficient absorption; existing prox
--   descent lemmas use a variational certificate and conclude in displacement
--   form, while the existing staged algebra helper does not mention objectives
--   or affine updates
-- coverage search: symbol queries `smooth function affine update objective
--   decrease upper bound direction estimator error stepsize` and `objective
--   difference affine update negative stepsize direction squared gradient
--   squared direction error`, plus Mathlib LeanSearch for the full approximate
--   gradient descent bound, found only partial hits
--   `smooth_descent_of_approx_variational_step_with_estimator_error`,
--   `smooth_descent_of_approx_variational_step_with_estimator_error_raw`, and
--   `inner_neg_smul_add_half_mul_norm_sq_le_of_le_inv_four_mul`
-- minimal hypotheses: the global smoothness and algorithm recurrences are
--   reduced to the pointwise upper model, affine-update equality, error
--   equality, positivity of `L`, and the exact nonnegative stepsize interval

/-- A smooth quadratic upper model along an affine direction update yields a
gradient decrease bound with a squared direction-error penalty.

For `xNext = x - eta • d` and `epsilon = d - grad x`, positivity of `L` and
`0 ≤ eta ≤ 1 / (4 * L)` turn the smooth upper model into the standard
`-eta / 4` gradient-square decrease plus `3 * eta / 4` error-square penalty.

Layer: Layer1 | Gap: Level 1 (affine-direction smooth descent with direction error)
Proof: rewrite the smooth-model displacement using the affine update, then apply the Hilbert inner-product and norm-square coefficient collection bound.
Source: smooth first-order descent calculus in real Hilbert spaces, Mathlib inner-product algebra, and ordered-field Young absorption
Used in: biased SGD and stochastic recursive-momentum one-step descent before integrating the pointwise gradient/error estimate
Book citation: book/STORM/StochasticRecursiveMomentum.json#/key_lemmas/0/proof
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem smooth_descent_affine_update_with_direction_error
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (x xNext d epsilon : E) (L eta : ℝ)
    (hsmooth :
      f xNext ≤
        f x + inner ℝ (grad x) (xNext - x) + (L / 2) * ‖xNext - x‖ ^ 2)
    (hupdate : xNext = x - eta • d)
    (hepsilon : epsilon = d - grad x)
    (hL_pos : 0 < L)
    (heta_nonneg : 0 ≤ eta)
    (heta_le : eta ≤ (1 : ℝ) / (4 * L)) :
    f xNext - f x ≤
      (-eta / 4) * ‖grad x‖ ^ 2 + (3 * eta / 4) * ‖epsilon‖ ^ 2 := by
  have hmodel :
      f xNext - f x ≤
        inner ℝ (grad x) (xNext - x) + (L / 2) * ‖xNext - x‖ ^ 2 := by
    linarith
  have hdiff : xNext - x = -eta • d := by
    rw [hupdate]
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have halgebra :
      inner ℝ (grad x) (-eta • d) + (L / 2) * ‖-eta • d‖ ^ 2 ≤
        (-eta / 4) * ‖grad x‖ ^ 2 + (3 * eta / 4) * ‖epsilon‖ ^ 2 := by
    exact inner_neg_smul_add_half_mul_norm_sq_le_of_le_inv_four_mul
      (grad x) d epsilon hL_pos heta_nonneg heta_le hepsilon
  exact le_trans (by simpa [hdiff] using hmodel) halgebra


-- Promoted from Staging/recursiveMomentumResidual_eq_three_term.lean

-- Generalization plan (G0):
-- concept/name: recursive_momentum_residual_eq_three_term_of_update exposes the three-term
--   residual decomposition of an affine recursive-momentum estimator update;
--   orig was `lemma2_error_succ_three_term_decomposition`.
-- generality used: arbitrary additive commutative group `E` with a real module
--   structure; no norm, topology, inner product, completeness, measure,
--   independence, integrability, convexity, smoothness, or oracle assumptions.
-- portable call pattern: STORM, SARAH-style, and control-variate estimator
--   proofs use this after a pointwise affine recursive update; the estimator
--   values, oracle values, targets, residuals, and momentum coefficient vary
--   while the three-term residual identity stays unchanged.
-- counterargument checked: although the proof is algebraic, this is not merely
--   paper traceability or a caller-side rename: it packages the recurring
--   transition from an affine estimator update to the fresh-noise,
--   centered-difference, and previous-residual split used by moment recurrences.
-- coverage search: symbol searches for `recursive estimator residual`, `affine
--   recursive momentum estimator residual`, and `momentum residual equality`
--   found `estimatorResidualProcess_succ_eq_of_estimator_update` and
--   `recursive_estimator_residual_eq_prev_add_centered_batch_diff_of_not_epoch_start`;
--   their full signatures give unweighted finite-batch two-term recursions and
--   do not cover this weighted three-term decomposition. Mathlib semantic search
--   returned only general module-algebra infrastructure.
-- minimal hypotheses: the algorithm update is reduced to one pointwise equality;
--   all remaining typeclasses are used by additive and scalar-module algebra.

/-- The residual of an affine recursive-momentum update splits into three terms.

The terms are the weighted fresh residual, the complementary-weight centered
two-point oracle difference, and the complementary-weight previous residual.

Layer: Layer1 | Gap: Level 0 (recursive-momentum residual affine decomposition)
Proof: rewrite the next estimator with the supplied affine update and normalize
  the resulting real-module expression with module algebra.
Source: Mathlib additive commutative group and real module identities
Used in: recursive-momentum, SARAH-style, and control-variate estimator analyses before bounding the next residual moment
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/5
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem recursive_momentum_residual_eq_three_term_of_update
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (dPrev dNext gNextAtNext gNextAtPrev targetNext targetPrev : E)
    (a : ℝ)
    (h_update :
      dNext = gNextAtNext + (1 - a) • (dPrev - gNextAtPrev)) :
    dNext - targetNext =
      a • (gNextAtNext - targetNext) +
        (1 - a) •
          (gNextAtNext - gNextAtPrev - targetNext + targetPrev) +
        (1 - a) • (dPrev - targetPrev) := by
  rw [h_update]
  module


-- Promoted from Staging/weighted_smooth_difference_add_error_sq_le_of_affine_update.lean

-- Generalization plan (G0):
-- concept/name: weighted smooth-difference and previous-error square bound under
--   an affine update; orig was
--   `lemma2_uncentered_gradient_difference_plus_error_pointwise_le`
-- generality used: arbitrary seminormed additive commutative group with a real
--   normed-space structure, real weights, and pointwise smooth-difference,
--   affine-displacement, and direction-splitting hypotheses; no measure,
--   probability, completeness, inner product, convexity, or finite dimension
-- portable call pattern: recursive-gradient, SARAH/SPIDER, and momentum methods
--   substitute their step size, momentum weight, smooth estimator difference,
--   consecutive iterates, direction error, and target gradient while preserving
--   the affine update and direction decomposition
-- counterargument checked: this is not a paper-local expression or pure wrapper;
--   it composes smoothness, update transport, a norm-square Young split, positive
--   weighting, and coefficient normalization into the recurring estimator-error
--   bound, whereas the available library result covers only the Young split
-- coverage search: symbol queries `weighted smooth difference squared error
--   upper bound affine update direction decomposition` and `affine update norm
--   square error`, plus Mathlib LeanSearch for the norm-square split, found only
--   `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`, Mathlib
--   `add_sq_le`, and unrelated affine-update integrability/descent results
-- minimal hypotheses: the algorithm recurrence and samplewise smoothness are
--   reduced to pointwise equalities/inequality; positivity is required only of
--   the step size, and no separate sign assumption on the smoothness factor or
--   momentum weight is used

/-- A weighted smooth estimator difference plus a previous-error square is
bounded after an affine update and a direction-error split.

If the estimator difference is `L`-Lipschitz along an update displacement,
the displacement is `-eta • dir`, and `dir = err + target`, then the weighted
difference square is absorbed into explicit error and target squares.

Layer: Layer1 | Gap: Level 1 (weighted smooth-difference affine-update error split)
Proof: transport the smooth-difference bound through the affine update, square it, split the direction square by the two-term norm Young inequality, and normalize the positive-step coefficients.
Source: Mathlib normed-module scalar-norm identities and ordered-field power arithmetic, together with SOptLib's binary norm-square Young inequality
Used in: recursive-momentum and variance-reduced gradient recurrences when a same-sample gradient difference and the previous estimator error are converted into target-gradient and error-square terms
Book citation: book/STORM/StochasticRecursiveMomentum.json#/key_lemmas/3/proof/15/math
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem weighted_smooth_difference_add_error_sq_le_of_affine_update
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {eta a L : ℝ} {g xNext xPrev dir err target : E}
    (heta_pos : 0 < eta)
    (hdiff : ‖g‖ ≤ L * ‖xNext - xPrev‖)
    (hupdate : xNext - xPrev = -eta • dir)
    (hdir : dir = err + target) :
    2 * (1 - a) ^ 2 / eta * ‖g‖ ^ 2 +
        (1 - a) ^ 2 * ‖err‖ ^ 2 / eta ≤
      (1 - a) ^ 2 * (1 + 4 * L ^ 2 * eta ^ 2) * ‖err‖ ^ 2 / eta +
        4 * (1 - a) ^ 2 * L ^ 2 * eta * ‖target‖ ^ 2 := by
  have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
  have hweight_nonneg : 0 ≤ 2 * (1 - a) ^ 2 / eta := by positivity
  have hdisp_norm : ‖xNext - xPrev‖ = eta * ‖dir‖ := by
    rw [hupdate, norm_smul, norm_neg, Real.norm_of_nonneg heta_nonneg]
  have hg_sq_le : ‖g‖ ^ 2 ≤ L ^ 2 * eta ^ 2 * ‖dir‖ ^ 2 := by
    have hbase : ‖g‖ ≤ L * (eta * ‖dir‖) := by
      simpa [hdisp_norm, mul_assoc] using hdiff
    have hsq := pow_le_pow_left₀ (norm_nonneg g) hbase 2
    calc
      ‖g‖ ^ 2 ≤ (L * (eta * ‖dir‖)) ^ 2 := hsq
      _ = L ^ 2 * eta ^ 2 * ‖dir‖ ^ 2 := by ring
  have hdir_sq_le : ‖dir‖ ^ 2 ≤ 2 * ‖err‖ ^ 2 + 2 * ‖target‖ ^ 2 := by
    simpa [hdir] using
      SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq err target
  have hg_sq_split :
      ‖g‖ ^ 2 ≤ L ^ 2 * eta ^ 2 * (2 * ‖err‖ ^ 2 + 2 * ‖target‖ ^ 2) := by
    exact hg_sq_le.trans
      (mul_le_mul_of_nonneg_left hdir_sq_le (by positivity))
  have hweighted_le :
      2 * (1 - a) ^ 2 / eta * ‖g‖ ^ 2 ≤
        2 * (1 - a) ^ 2 / eta *
          (L ^ 2 * eta ^ 2 * (2 * ‖err‖ ^ 2 + 2 * ‖target‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hg_sq_split hweight_nonneg
  have heta_ne : eta ≠ 0 := ne_of_gt heta_pos
  calc
    2 * (1 - a) ^ 2 / eta * ‖g‖ ^ 2 +
        (1 - a) ^ 2 * ‖err‖ ^ 2 / eta ≤
      2 * (1 - a) ^ 2 / eta *
          (L ^ 2 * eta ^ 2 * (2 * ‖err‖ ^ 2 + 2 * ‖target‖ ^ 2)) +
        (1 - a) ^ 2 * ‖err‖ ^ 2 / eta := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hweighted_le ((1 - a) ^ 2 * ‖err‖ ^ 2 / eta)
    _ =
      (1 - a) ^ 2 * (1 + 4 * L ^ 2 * eta ^ 2) * ‖err‖ ^ 2 / eta +
        4 * (1 - a) ^ 2 * L ^ 2 * eta * ‖target‖ ^ 2 := by
          field_simp [heta_ne]
          ring


-- Promoted from Staging/recursive_momentum_error_integral_recurrence.lean
open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: recursive-momentum error integral recurrence; orig was
--   `lemma2_error_recurrence_of_generated_quotient_boundary`
-- generality used: arbitrary measurable sample space and measure, arbitrary real
--   inner-product seminormed additive commutative group, random positive step and
--   momentum weights, pointwise estimator decomposition/update contracts, and
--   only the integrability and centered-moment comparisons used by the proof
-- portable call pattern: STORM, SARAH, SPIDER, and recursive-gradient analyses
--   substitute their iterate, estimator-error, paired sample-gradient, target,
--   stepsize, and momentum processes while retaining the same one-step recurrence
-- counterargument checked: the theorem is not paper-local traceability or a thin
--   wrapper; it composes an asymmetric three-term Hilbert expansion, two centered
--   cross cancellations, two second-moment contractions, and an affine-update
--   smooth-difference absorption into a reusable expected-error recurrence
-- coverage search: symbol queries for recursive estimator expected squared-error
--   recurrences and centered cross-term integral bounds found the partial results
--   `norm_three_term_sq_div_le_of_first_coeff_eq`,
--   `integral_le_integral_of_ae_le_add_of_integral_eq_zero`, and
--   `weighted_smooth_difference_add_error_sq_le_of_affine_update`, but no theorem
--   with this complete recurrence contract
-- minimal hypotheses: probability, finite measure, completeness, finite dimension,
--   convexity, filtration, and oracle structures are unused; global algorithm
--   assumptions are reduced to pointwise/a.e. identities and exact integrability

/-- A recursive momentum estimator satisfies its one-step weighted error recurrence.

The next error is decomposed into a fresh centered residual, a centered paired
gradient difference, and the previous error.  Vanishing expected cross terms
remove the previous-error interactions, centering contracts the two square
terms, and smoothness along an affine iterate update absorbs the paired square.

Layer: Layer1 | Gap: Level 1 (recursive-momentum expected squared-error recurrence)
Proof: apply the asymmetric three-term Hilbert norm-square bound pointwise, cancel the two integrable zero-mean crosses, contract the centered square terms, and use the affine-update smooth-difference bound for the remaining paired term.
Source: Hilbert-space polarization, Bochner integral monotonicity and linearity, and the standard STORM/SARAH recursive-estimator second-moment argument
Used in: one-step variance recurrences for recursive momentum and paired-gradient estimators before Lyapunov or finite-window aggregation
Book citation: book/STORM/StochasticRecursiveMomentum.json#/key_lemmas/3
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem recursive_momentum_error_integral_recurrence
    {Ω E : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω)
    (x xNext err errNext sampleGradNext sampleGradPrev targetNext targetPrev dir : Ω → E)
    (eta momentum : Ω → ℝ) (c L : ℝ)
    (heta_pos : ∀ ω, 0 < eta ω)
    (hmomentum : ∀ ω, momentum ω = c * eta ω ^ 2)
    (hdecomp : ∀ ω,
      errNext ω =
        momentum ω • (sampleGradNext ω - targetNext ω) +
          (1 - momentum ω) •
            (sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω) +
          (1 - momentum ω) • err ω)
    (hupdate : ∀ ω, xNext ω - x ω = -(eta ω) • dir ω)
    (hdir : ∀ ω, dir ω = err ω + targetPrev ω)
    (hsmooth : ∀ᵐ ω ∂μ,
      ‖sampleGradNext ω - sampleGradPrev ω‖ ≤
        L * ‖xNext ω - x ω‖)
    (hlhs_int : Integrable (fun ω => ‖errNext ω‖ ^ 2 / eta ω) μ)
    (hfresh_centered_int : Integrable (fun ω =>
      2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω - targetNext ω‖ ^ 2) μ)
    (hpaired_centered_int : Integrable (fun ω =>
      2 * (1 - momentum ω) ^ 2 / eta ω *
        ‖sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω‖ ^ 2) μ)
    (hprev_int : Integrable (fun ω =>
      (1 - momentum ω) ^ 2 * ‖err ω‖ ^ 2 / eta ω) μ)
    (hfresh_int : Integrable (fun ω =>
      2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω‖ ^ 2) μ)
    (hpaired_int : Integrable (fun ω =>
      2 * (1 - momentum ω) ^ 2 / eta ω *
        ‖sampleGradNext ω - sampleGradPrev ω‖ ^ 2) μ)
    (hrhs_int : Integrable (fun ω =>
      2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω‖ ^ 2 +
        (1 - momentum ω) ^ 2 * (1 + 4 * L ^ 2 * eta ω ^ 2) *
            ‖err ω‖ ^ 2 / eta ω +
          4 * (1 - momentum ω) ^ 2 * L ^ 2 * eta ω * ‖targetPrev ω‖ ^ 2) μ)
    (hfresh_cross :
      Integrable (fun ω => inner ℝ (sampleGradNext ω - targetNext ω)
        ((2 * momentum ω * (1 - momentum ω) / eta ω) • err ω)) μ ∧
      ∫ ω, inner ℝ (sampleGradNext ω - targetNext ω)
        ((2 * momentum ω * (1 - momentum ω) / eta ω) • err ω) ∂μ = 0)
    (hpaired_cross :
      Integrable (fun ω =>
        inner ℝ
          (sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω)
          ((2 * (1 - momentum ω) ^ 2 / eta ω) • err ω)) μ ∧
      ∫ ω,
        inner ℝ
          (sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω)
          ((2 * (1 - momentum ω) ^ 2 / eta ω) • err ω) ∂μ = 0)
    (hfresh_centered_le :
      (∫ ω, 2 * c ^ 2 * eta ω ^ 3 *
        ‖sampleGradNext ω - targetNext ω‖ ^ 2 ∂μ) ≤
      ∫ ω, 2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω‖ ^ 2 ∂μ)
    (hpaired_centered_le :
      (∫ ω, 2 * (1 - momentum ω) ^ 2 / eta ω *
        ‖(sampleGradNext ω - sampleGradPrev ω) -
          (targetNext ω - targetPrev ω)‖ ^ 2 ∂μ) ≤
      ∫ ω, 2 * (1 - momentum ω) ^ 2 / eta ω *
        ‖sampleGradNext ω - sampleGradPrev ω‖ ^ 2 ∂μ) :
    (∫ ω, ‖errNext ω‖ ^ 2 / eta ω ∂μ) ≤
      ∫ ω,
        2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω‖ ^ 2 +
          (1 - momentum ω) ^ 2 * (1 + 4 * L ^ 2 * eta ω ^ 2) *
              ‖err ω‖ ^ 2 / eta ω +
            4 * (1 - momentum ω) ^ 2 * L ^ 2 * eta ω *
              ‖targetPrev ω‖ ^ 2 ∂μ := by
  let lhs : Ω → ℝ := fun ω => ‖errNext ω‖ ^ 2 / eta ω
  let freshCentered : Ω → ℝ := fun ω =>
    2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω - targetNext ω‖ ^ 2
  let pairedCentered : Ω → ℝ := fun ω =>
    2 * (1 - momentum ω) ^ 2 / eta ω *
      ‖sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω‖ ^ 2
  let previous : Ω → ℝ := fun ω =>
    (1 - momentum ω) ^ 2 * ‖err ω‖ ^ 2 / eta ω
  let fresh : Ω → ℝ := fun ω =>
    2 * c ^ 2 * eta ω ^ 3 * ‖sampleGradNext ω‖ ^ 2
  let paired : Ω → ℝ := fun ω =>
    2 * (1 - momentum ω) ^ 2 / eta ω *
      ‖sampleGradNext ω - sampleGradPrev ω‖ ^ 2
  let crossFresh : Ω → ℝ := fun ω =>
    inner ℝ (sampleGradNext ω - targetNext ω)
      ((2 * momentum ω * (1 - momentum ω) / eta ω) • err ω)
  let crossPaired : Ω → ℝ := fun ω =>
    inner ℝ
      (sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω)
      ((2 * (1 - momentum ω) ^ 2 / eta ω) • err ω)
  let rhs : Ω → ℝ := fun ω =>
    fresh ω +
      (1 - momentum ω) ^ 2 * (1 + 4 * L ^ 2 * eta ω ^ 2) *
          ‖err ω‖ ^ 2 / eta ω +
        4 * (1 - momentum ω) ^ 2 * L ^ 2 * eta ω * ‖targetPrev ω‖ ^ 2
  have hpoint : ∀ᵐ ω ∂μ,
      lhs ω ≤ freshCentered ω + pairedCentered ω + previous ω +
        crossFresh ω + crossPaired ω := by
    filter_upwards with ω
    have hbase := norm_three_term_sq_div_le_of_first_coeff_eq
      (b := 1 - momentum ω)
      (heta_pos ω) (hmomentum ω)
      (sampleGradNext ω - targetNext ω)
      (sampleGradNext ω - sampleGradPrev ω - targetNext ω + targetPrev ω)
      (err ω)
    simpa [lhs, freshCentered, pairedCentered, previous, crossFresh, crossPaired,
      hdecomp ω] using hbase
  have hcross_removed :
      (∫ ω, lhs ω ∂μ) ≤
        ∫ ω, freshCentered ω + pairedCentered ω + previous ω ∂μ := by
    have hfreshCentered_int : Integrable freshCentered μ := by
      simpa [freshCentered] using hfresh_centered_int
    have hpairedCentered_int : Integrable pairedCentered μ := by
      simpa [pairedCentered] using hpaired_centered_int
    have hprevious_int : Integrable previous μ := by
      simpa [previous] using hprev_int
    have hcrossFresh_int : Integrable crossFresh μ := by
      simpa [crossFresh] using hfresh_cross.1
    have hcrossPaired_int : Integrable crossPaired μ := by
      simpa [crossPaired] using hpaired_cross.1
    have hretained_int :
        Integrable (fun ω => freshCentered ω + pairedCentered ω + previous ω) μ :=
      (hfreshCentered_int.add hpairedCentered_int).add hprevious_int
    have hcorrection_int :
        Integrable (fun ω => crossFresh ω + crossPaired ω) μ :=
      hcrossFresh_int.add hcrossPaired_int
    refine integral_le_integral_of_ae_le_add_of_integral_eq_zero
      (lhs := lhs)
      (retained := fun ω => freshCentered ω + pairedCentered ω + previous ω)
      (correction := fun ω => crossFresh ω + crossPaired ω)
      (by simpa [lhs] using hlhs_int)
      hretained_int hcorrection_int
      (by
        filter_upwards [hpoint] with ω hω
        simpa only [Pi.add_apply, add_assoc] using hω)
      (by
        rw [integral_add hcrossFresh_int hcrossPaired_int]
        simp [crossFresh, crossPaired, hfresh_cross.2, hpaired_cross.2])
  have hpaired_centered_le' :
      (∫ ω, pairedCentered ω ∂μ) ≤ ∫ ω, paired ω ∂μ := by
    have heq : (fun ω => pairedCentered ω) = fun ω =>
        2 * (1 - momentum ω) ^ 2 / eta ω *
          ‖(sampleGradNext ω - sampleGradPrev ω) -
            (targetNext ω - targetPrev ω)‖ ^ 2 := by
      funext ω
      simp only [pairedCentered]
      congr 2
      abel
    rw [heq]
    simpa [paired] using hpaired_centered_le
  have hpoint_final : ∀ᵐ ω ∂μ,
      fresh ω + paired ω + previous ω ≤ rhs ω := by
    filter_upwards [hsmooth] with ω hsmoothω
    have hbound := weighted_smooth_difference_add_error_sq_le_of_affine_update
      (eta := eta ω) (a := momentum ω) (L := L)
      (g := sampleGradNext ω - sampleGradPrev ω)
      (xNext := xNext ω) (xPrev := x ω) (dir := dir ω)
      (err := err ω) (target := targetPrev ω)
      (heta_pos ω) hsmoothω (hupdate ω) (hdir ω)
    dsimp [fresh, paired, previous, rhs]
    linarith
  have hretained_le :
      (∫ ω, freshCentered ω + pairedCentered ω + previous ω ∂μ) ≤
        ∫ ω, rhs ω ∂μ := by
    have hfreshCentered_int : Integrable freshCentered μ := by
      simpa [freshCentered] using hfresh_centered_int
    have hpairedCentered_int : Integrable pairedCentered μ := by
      simpa [pairedCentered] using hpaired_centered_int
    have hprevious_int : Integrable previous μ := by
      simpa [previous] using hprev_int
    have hfreshInt : Integrable fresh μ := by simpa [fresh] using hfresh_int
    have hpairedInt : Integrable paired μ := by simpa [paired] using hpaired_int
    have hrhsInt : Integrable rhs μ := by simpa [rhs, fresh] using hrhs_int
    have hcentered_add :
        (∫ ω, freshCentered ω + pairedCentered ω ∂μ) =
          (∫ ω, freshCentered ω ∂μ) + ∫ ω, pairedCentered ω ∂μ := by
      simpa only [Pi.add_apply] using
        integral_add hfreshCentered_int hpairedCentered_int
    have hcentered_add_previous :
        (∫ ω, (freshCentered ω + pairedCentered ω) + previous ω ∂μ) =
          (∫ ω, freshCentered ω + pairedCentered ω ∂μ) +
            ∫ ω, previous ω ∂μ := by
      simpa only [Pi.add_apply] using
        integral_add (hfreshCentered_int.add hpairedCentered_int) hprevious_int
    have hfresh_add_paired :
        (∫ ω, fresh ω + paired ω ∂μ) =
          (∫ ω, fresh ω ∂μ) + ∫ ω, paired ω ∂μ := by
      simpa only [Pi.add_apply] using integral_add hfreshInt hpairedInt
    have huncentered_add_previous :
        (∫ ω, (fresh ω + paired ω) + previous ω ∂μ) =
          (∫ ω, fresh ω + paired ω ∂μ) + ∫ ω, previous ω ∂μ := by
      simpa only [Pi.add_apply] using
        integral_add (hfreshInt.add hpairedInt) hprevious_int
    calc
      (∫ ω, freshCentered ω + pairedCentered ω + previous ω ∂μ) =
          (∫ ω, freshCentered ω ∂μ) + (∫ ω, pairedCentered ω ∂μ) +
            ∫ ω, previous ω ∂μ := by
        calc
          _ = (∫ ω, freshCentered ω + pairedCentered ω ∂μ) +
                ∫ ω, previous ω ∂μ := hcentered_add_previous
          _ = _ := by rw [hcentered_add]
      _ ≤ (∫ ω, fresh ω ∂μ) + (∫ ω, paired ω ∂μ) +
            ∫ ω, previous ω ∂μ := by
        linarith [hfresh_centered_le, hpaired_centered_le']
      _ = ∫ ω, fresh ω + paired ω + previous ω ∂μ := by
        calc
          _ = (∫ ω, fresh ω + paired ω ∂μ) + ∫ ω, previous ω ∂μ := by
            rw [hfresh_add_paired]
          _ = _ := huncentered_add_previous.symm
      _ ≤ ∫ ω, rhs ω ∂μ :=
        integral_mono_ae ((hfreshInt.add hpairedInt).add hprevious_int)
          hrhsInt hpoint_final
  exact hcross_removed.trans hretained_le


-- Promoted from Staging/recursiveMomentumDirection_eventually_bounded.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: finite-time a.e. boundedness of a recursive momentum direction;
--   orig was lemma3_generated_direction_eventually_bound
-- generality used: arbitrary measure on a measurable space and any real seminormed additive
--   commutative group; no probability, measurability, integrability, inner product,
--   smoothness, oracle structure, or finite-dimensionality is used
-- portable call pattern: recursive-momentum, SARAH, and related corrected-estimator proofs
--   supply an initial direction bound, bounds for the fresh and correction oracle terms,
--   finite-time coefficient bounds, and the affine correction recurrence; the processes,
--   coefficients, measure, and time may change while the conclusion remains unchanged
-- counterargument checked: this is not paper-local traceability or a caller-side wrapper;
--   it packages the nontrivial finite-time induction through random coefficients and a.e.
--   intersections, and neither Mathlib nor SOptLib exposes this recurrence contract
-- coverage search: searches for "recursive affine direction norm eventually bounded from
--   bounded inputs and coefficient bounds", "exists constant almost everywhere norm bounded
--   sequence recurrence", and "bounded recursive process norm bounded input scalar
--   coefficient" found only linear-recurrence/asymptotic APIs and
--   exists_nonneg_ae_bound_accumulator_of_ae_bounded_increments; coverage is partial because
--   the latter has an ordered additive accumulator rather than a normed affine correction
-- minimal hypotheses: probability was weakened to an arbitrary measure, all oracle and
--   continuity assumptions were replaced by the a.e. bounds actually consumed, and the
--   recursive update is retained only as a pointwise equation

/-- Every fixed iterate of a recursive momentum direction is almost everywhere norm bounded
when its initial value, two input processes, and complementary coefficients have finite bounds.

The recurrence has the corrected-estimator form
`d_(n+1) = gNext_n + coeff_n • (d_n - gCorr_n)`; the resulting bound may grow
with the requested finite time, so no contraction assumption on `coeff` is required.

Layer: Layer1 | Gap: Level 1 (finite-time recursive-momentum direction boundedness)
Proof: induct on time, intersect the preceding direction bound with the two input bounds and
  the current coefficient bound, then apply the norm triangle, subtraction, and smul bounds.
Source: Mathlib normed-space inequalities and almost-everywhere filter intersections
Used in: recursive-momentum and SARAH-style estimator proofs establishing bounded generated
  directions before proving finite-measure integrability of descent and error terms
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/5
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD,
  STOchastic Recursive Momentum -/
theorem exists_nonneg_ae_norm_bound_of_recursive_affine_correction
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (direction gNext gCorr : ℕ → Ω → E)
    (coeff : ℕ → Ω → ℝ) (G : ℝ)
    (hG_nonneg : 0 ≤ G)
    (hzero : ∀ᵐ ω ∂μ, ‖direction 0 ω‖ ≤ G)
    (hgNext : ∀ n, ∀ᵐ ω ∂μ, ‖gNext n ω‖ ≤ G)
    (hgCorr : ∀ n, ∀ᵐ ω ∂μ, ‖gCorr n ω‖ ≤ G)
    (hcoeff : ∀ n, ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖coeff n ω‖ ≤ A)
    (hrec : ∀ n ω,
      direction (n + 1) ω =
        gNext n ω + coeff n ω • (direction n ω - gCorr n ω))
    (t : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᵐ ω ∂μ, ‖direction t ω‖ ≤ D := by
  induction t with
  | zero =>
      exact ⟨G, hG_nonneg, hzero⟩
  | succ n ih =>
      rcases ih with ⟨D, hD_nonneg, hD⟩
      rcases hcoeff n with ⟨A, hA_nonneg, hA⟩
      refine
        ⟨G + A * (D + G),
          add_nonneg hG_nonneg
            (mul_nonneg hA_nonneg (add_nonneg hD_nonneg hG_nonneg)), ?_⟩
      filter_upwards [hD, hA, hgNext n, hgCorr n] with
        ω hDω hAω hNextω hCorrω
      have hdiff : ‖direction n ω - gCorr n ω‖ ≤ D + G :=
        (norm_sub_le (direction n ω) (gCorr n ω)).trans
          (add_le_add hDω hCorrω)
      have hsmul :
          ‖coeff n ω • (direction n ω - gCorr n ω)‖ ≤ A * (D + G) := by
        rw [norm_smul]
        exact mul_le_mul hAω hdiff (norm_nonneg _) hA_nonneg
      rw [hrec]
      exact (norm_add_le _ _).trans (add_le_add hNextω hsmul)


-- Promoted from Staging/recursiveMomentumProcess_prefixAEMeasurable.lean
open MeasureTheory

namespace SOptLib

private theorem aestronglyMeasurable_comp_measurable
    {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
    [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [SecondCountableTopology β] [BorelSpace β]
    {m : MeasurableSpace Ω} {f : Ω → α} {g : α → β} {μ : @Measure Ω mΩ}
    (hf : AEStronglyMeasurable[m] f μ) (hg : Measurable g) :
    AEStronglyMeasurable[m] (fun ω => g (f ω)) μ := by
  exact (hg.comp hf.measurable_mk).aestronglyMeasurable.congr
    (hf.ae_eq_mk.fun_comp g).symm

-- Generalization plan (G0):
-- concept/name: sample-prefix adaptedness of a recursive-momentum process; orig was
--   `lemma3_generated_history_prefixAEMeasurable_early`
-- generality used: arbitrary path and sample types, a second-countable real normed
--   additive group, an arbitrary measure, measurable sample coordinates, measurable
--   scalar schedules, and a law-scoped adaptive-oracle measurability contract; no
--   probability, independence, integrability, convexity, smoothness, or inner product
--   assumptions are used
-- portable call pattern: STORM-family and same-sample recursive-momentum analyses prove
--   that the current/next iterates, current direction, and accumulated squared oracle
--   norm are `AEStronglyMeasurable` in the pre-fresh-sample filtration; the oracle,
--   sample law, initial point, and scalar schedules may all change
-- counterargument checked: generic recursive-process measurability lemmas require an
--   exactly measurable driver and globally measurable update, while this theorem
--   propagates only law-scoped `AEStronglyMeasurable` facts and uses the transition ordering to
--   expose the next iterate before the fresh oracle response
-- coverage search: queries "recursive momentum process prefix a.e. measurable sample
--   transition", "adapted recursive process measurable sample kernel coordinates",
--   and "recursive process prefix a.e. measurable representative oracle query" found
--   `recursive_process_measurable_wrt_sample_prefix`,
--   `process_prefix_measurable_wrt_sampleBlock`, and
--   `recursive_process_measurable_of_measurable_update_oracle`; all require exact
--   measurability and therefore only partially cover the law-scoped statement
-- minimal hypotheses: removed the source probability, independence, finite-dimensional,
--   complete, Hilbert, objective, smoothness, and moment assumptions; retained only the
--   adaptive-oracle representative property actually consumed by the induction

/-- The iterate pair, direction, and accumulated sampled-oracle square of a
recursive-momentum process are `AEStronglyMeasurable` in the exact sample prefix.

The oracle premise is deliberately law-scoped: evaluating the next sample at any
query that is a.e.-strongly measurable for the prefix must again be
a.e.-strongly measurable after adjoining that sample. This supports product-law or conditional
regularity arguments that do not provide a globally measurable oracle kernel.

Layer: Layer1 | Gap: Level 1 (law-scoped recursive-momentum prefix adaptedness)
Proof: induct on time, lift representatives along the sample-prefix filtration, apply
  the adaptive-oracle premise at the new and correction queries, and close under the
  continuous recursive-momentum coordinate operations
Source: Mathlib measurable-space monotonicity and continuous normed-space operations,
  together with `recursive_momentum_step_from_sample` and the sample-prefix filtration
Used in: STORM-family pre-fresh-sample conditioning, where the next iterate is adapted
  before the fresh oracle response while the direction and accumulator update afterward
Book citation: book/STORM/StochasticRecursiveMomentum.json#/key_lemmas/1
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum (STORM) -/
theorem recursive_momentum_process_prefix_aestronglyMeasurable
    {Ω Sample E : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Sample]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : @Measure Ω mΩ)
    (sample : ℕ → Ω → Sample) (hsample : ∀ n, Measurable (sample n))
    (oracle : E → Sample → E) (x0 : E)
    (stepSize momentumWeight : ℝ → ℝ)
    (hstepSize : Measurable stepSize) (hmomentumWeight : Measurable momentumWeight)
    (horacle :
      ∀ n (query : Ω → E),
        AEStronglyMeasurable[(filtration sample hsample).seq n] query μ →
          AEStronglyMeasurable[(filtration sample hsample).seq (n + 1)]
            (fun ω => oracle (query ω) (sample n ω)) μ)
    (t : ℕ) :
    let process :=
      recursive_process_from_random_initial
        (recursiveMomentumInitialState x0 oracle (sample 0))
        (fun n state ω =>
          recursive_momentum_step_from_sample oracle stepSize momentumWeight state
            (sample (n + 1) ω))
    AEStronglyMeasurable[(filtration sample hsample).seq (t + 1)]
        (fun ω => (process t ω).x) μ ∧
      AEStronglyMeasurable[(filtration sample hsample).seq (t + 1)]
        (fun ω => (process (t + 1) ω).x) μ ∧
      AEStronglyMeasurable[(filtration sample hsample).seq (t + 1)]
        (fun ω => (process t ω).direction) μ ∧
      AEStronglyMeasurable[(filtration sample hsample).seq (t + 1)]
        (fun ω => (process t ω).gradNormSqSum) μ := by
  classical
  let process :=
    recursive_process_from_random_initial
      (recursiveMomentumInitialState x0 oracle (sample 0))
      (fun n state ω =>
        recursive_momentum_step_from_sample oracle stepSize momentumWeight state
          (sample (n + 1) ω))
  induction t with
  | zero =>
      have hx0 :
          AEStronglyMeasurable[(filtration sample hsample).seq 1]
            (fun ω => (process 0 ω).x) μ := by
        refine
          (aestronglyMeasurable_const :
            AEStronglyMeasurable[(filtration sample hsample).seq 1]
              (fun _ω : Ω => x0) μ).congr ?_
        filter_upwards with ω
        rfl
      have hquery0 :
          AEStronglyMeasurable[(filtration sample hsample).seq 0]
            (fun _ω : Ω => x0) μ :=
        (aestronglyMeasurable_const :
          AEStronglyMeasurable[(filtration sample hsample).seq 0]
            (fun _ω : Ω => x0) μ)
      have hgrad0 := horacle 0 (fun _ω : Ω => x0) hquery0
      have hdir0 :
          AEStronglyMeasurable[(filtration sample hsample).seq 1]
            (fun ω => (process 0 ω).direction) μ := by
        refine hgrad0.congr ?_
        filter_upwards with ω
        rfl
      have hsum0 :
          AEStronglyMeasurable[(filtration sample hsample).seq 1]
            (fun ω => (process 0 ω).gradNormSqSum) μ := by
        refine ((continuous_norm.pow 2).comp_aestronglyMeasurable hgrad0).congr ?_
        filter_upwards with ω
        rfl
      have hη0 :
          AEStronglyMeasurable[(filtration sample hsample).seq 1]
            (fun ω => stepSize (process 0 ω).gradNormSqSum) μ :=
        aestronglyMeasurable_comp_measurable hsum0 hstepSize
      have hx1 :
          AEStronglyMeasurable[(filtration sample hsample).seq 1]
            (fun ω => (process 1 ω).x) μ := by
        refine (hx0.sub (hη0.smul hdir0)).congr ?_
        filter_upwards with ω
        rfl
      exact ⟨hx0, hx1, hdir0, hsum0⟩
  | succ t ih =>
      rcases ih with ⟨hxCurr, hxNext, hdirCurr, hsumCurr⟩
      have hle : t + 1 ≤ t + 2 := Nat.le_succ (t + 1)
      have hxCurr' :=
        AEStronglyMeasurable.mono ((filtration sample hsample).mono hle) hxCurr
      have hxNext' :=
        AEStronglyMeasurable.mono ((filtration sample hsample).mono hle) hxNext
      have hdirCurr' :=
        AEStronglyMeasurable.mono ((filtration sample hsample).mono hle) hdirCurr
      have hsumCurr' :=
        AEStronglyMeasurable.mono ((filtration sample hsample).mono hle) hsumCurr
      have hη := aestronglyMeasurable_comp_measurable hsumCurr' hstepSize
      have hgNext := horacle (t + 1) (fun ω => (process (t + 1) ω).x) hxNext
      have hcorr := horacle (t + 1) (fun ω => (process t ω).x) hxCurr
      have haBase := aestronglyMeasurable_comp_measurable hη hmomentumWeight
      have ha :
          AEStronglyMeasurable[(filtration sample hsample).seq (t + 2)]
            (fun ω => 1 - momentumWeight (stepSize (process t ω).gradNormSqSum)) μ := by
        exact
          (aestronglyMeasurable_const :
            AEStronglyMeasurable[(filtration sample hsample).seq (t + 2)]
              (fun _ω : Ω => (1 : ℝ)) μ).sub haBase
      have hdirNext :
          AEStronglyMeasurable[(filtration sample hsample).seq (t + 2)]
            (fun ω => (process (t + 1) ω).direction) μ := by
        refine (hgNext.add (ha.smul (hdirCurr'.sub hcorr))).congr ?_
        filter_upwards with ω
        rfl
      have hsumNext :
          AEStronglyMeasurable[(filtration sample hsample).seq (t + 2)]
            (fun ω => (process (t + 1) ω).gradNormSqSum) μ := by
        refine (hsumCurr'.add ((continuous_norm.pow 2).comp_aestronglyMeasurable hgNext)).congr ?_
        filter_upwards with ω
        rfl
      have hηNext := aestronglyMeasurable_comp_measurable hsumNext hstepSize
      have hxAfterNext :
          AEStronglyMeasurable[(filtration sample hsample).seq (t + 2)]
            (fun ω => (process (t + 2) ω).x) μ := by
        refine (hxNext'.sub (hηNext.smul hdirNext)).congr ?_
        filter_upwards with ω
        rfl
      exact ⟨hxNext', hxAfterNext, hdirNext, hsumNext⟩

end SOptLib

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: inner_update_eq_sq_dist_sub_sq_dist_add_norm_sq exposes the
--   Hilbert-space distance-drop identity obtained from an explicit affine
--   update rule; orig was stochastic_three_point_identity_of_update, renamed
--   away from stochastic and paper-local algorithm language.
-- generality used: a real inner-product space with a seminormed additive group,
--   four points/vectors, two real scalars, a nonzero step size, and the
--   pointwise affine update equality; no measure, independence, integrability,
--   convexity, smoothness, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: accelerated stochastic-gradient, plain gradient
--   descent, variance-reduced, and learned-direction proofs can call this when
--   an update `xNext = xPrev - lam • v` must convert an inner product against a
--   comparison displacement into a squared-distance telescope plus `‖v‖^2`.
-- counterargument checked: this is not paper-local traceability because the
--   same update-to-distance-drop bridge recurs across first-order methods; it
--   is not a pure Mathlib rename because Mathlib provides norm-square
--   polarization but not this update-specialized scaled identity.
-- coverage search: searched `inner product update squared distance difference
--   norm squared`, `xNext = xPrev - lambda v inner equals distance drop`, and
--   LeanSearch for the full update identity; closest hits were Mathlib
--   `norm_sub_sq_real`, SOptLib's projected-gradient inequality
--   `inner_le_eta_add_half_smul_norm_sub_sq_sub_of_add_smul_inner_le`, and
--   mirror-descent three-point transport lemmas, all partial rather than full.
-- minimal hypotheses: all hypotheses are pointwise algebraic assumptions; the
--   carrier is generalized from Euclidean space to a seminormed real
--   inner-product space and the step-size condition is exactly `lam ≠ 0`.

open scoped InnerProductSpace

/-- An affine update converts a scaled inner product into a distance drop plus
a squared-direction term.

If `xNext = xPrev - lam • v` with `lam ≠ 0`, then the comparison inner product
`alpha * ⟪v, xPrev - xRef⟫_ℝ` is exactly the standard Hilbert-space
three-point distance identity for the update.

Layer: Layer1 | Gap: Level 1 (Hilbert update distance-drop identity)
Proof: rewrite the update into the norm-square of `(xPrev - xRef) - lam • v`,
  expand with `norm_sub_sq_real`, and rearrange by real field arithmetic.
Source: Mathlib real inner-product norm-square polarization and scalar-norm APIs
Used in: nonconvex stochastic accelerated gradient descent converting the
  stochastic update inner product into the squared-distance telescope in the
  convex-case one-step recurrence
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/components/Stochastic_three_point_identity
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic accelerated gradient descent -/
theorem inner_update_eq_sq_dist_sub_sq_dist_add_norm_sq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (xPrev xNext xRef v : E) (alpha lam : ℝ) (hlam : lam ≠ 0)
    (hupdate : xNext = xPrev - lam • v) :
    alpha * inner ℝ v (xPrev - xRef) =
      alpha / (2 * lam) *
          (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) +
        alpha * lam / 2 * ‖v‖ ^ 2 := by
  subst xNext
  have hnorm :
      ‖xPrev - lam • v - xRef‖ ^ 2 =
        ‖xPrev - xRef‖ ^ 2 - 2 * lam * inner ℝ v (xPrev - xRef) +
          lam ^ 2 * ‖v‖ ^ 2 := by
    have hvec : xPrev - lam • v - xRef = (xPrev - xRef) - lam • v := by
      module
    rw [hvec, norm_sub_sq_real, norm_smul]
    simp [inner_smul_right, real_inner_comm, Real.norm_eq_abs, mul_comm,
      mul_left_comm, mul_assoc]
    rw [mul_pow, sq_abs]
  rw [hnorm]
  field_simp [hlam]
  ring


-- Generalization plan (G0):
-- concept/name: accelerated_two_state_adapted_of_observable_error exposes the
--   adaptedness induction for two accelerated state coordinates driven by an
--   observable error and affine update rules; orig was
--   generated_state_adapted_from_error_observable, renamed away from generated
--   sample-stream setup fields.
-- generality used: arbitrary measurable sample space, a natural-number
--   filtration, an abstract measurable additive/scalar state space, two state
--   coordinates, a search coordinate, an observable error, a measurable target
--   map, and pointwise affine update laws; no measure, independence,
--   integrability, convexity, smoothness, Hilbert, probability, or
--   finite-dimensional assumptions are used.
-- portable call pattern: accelerated stochastic-gradient, accelerated
--   mirror-style, and variance-reduced two-sequence proofs can call this after
--   proving the innovation/error is observable at the next filtration level
--   and the two recursive coordinates satisfy affine update equations.
-- counterargument checked: this is not only paper-local traceability because
--   the same two-coordinate adaptedness induction recurs whenever a search
--   point is an affine blend of previous coordinates and both next coordinates
--   use a shared observable direction; it is not covered by a one-line Mathlib
--   adaptedness projection or by the existing one-coordinate recursive update
--   lemmas.
-- coverage search: searched `adaptedness two state affine update observable
--   error filtration measurable previous coordinates`, `Adapted recursive
--   process affine update measurable filtration`, `two coordinate adaptedness
--   affine update error gradient measurable filtration conclusion both
--   coordinates`, and LeanSearch `measurable adapted recursive two coordinate
--   affine update filtration`; closest hits were Mathlib
--   `MeasureTheory.Adapted.measurable`, SOptLib
--   `adapted_iterate_of_recursive_adapted_update`,
--   `recursive_process_measurable_wrt_sample_prefix`, and
--   `TwoCoordinateProcessAdapted`, all partial rather than this explicit
--   two-coordinate affine adaptedness contract.
-- minimal hypotheses: all hypotheses are already pointwise or measurability
--   assumptions; the carrier is generalized from Euclidean space to measurable
--   algebra with `Add`, `Sub`, and real scalar multiplication closure.

/-- Two accelerated affine state coordinates are adapted when the shared error is observable.

If the search coordinate is an affine blend of the previous two coordinates,
the next state and averaged state are affine updates by the same measurable
target-plus-error direction, and each successor error at time `t + 1` is
measurable at filtration level `(t + 1) + 1`, then both coordinates are adapted
at level `t + 1`.

Layer: Layer1 | Gap: Level 1 (two-coordinate affine adaptedness induction)
Proof: induct on time, lift previous-coordinate measurability by filtration
  monotonicity, close the affine search and update coordinates under measurable
  add/sub/scalar operations, and compose the measurable target map with the
  measurable search coordinate.
Source: Mathlib filtration monotonicity and measurable algebra closure APIs
Used in: nonconvex stochastic accelerated gradient descent proving generated
  iterate and averaged-iterate adaptedness before martingale cancellation and
  finite-window expectation bounds
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem accelerated_two_state_adapted_of_observable_error
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Add E] [Sub E] [SMul ℝ E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E] [MeasurableConstSMul ℝ E]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (x xBar xUnder err : ℕ → Ω → E) (target : E → E)
    (alpha beta lam : ℕ → ℝ)
    (htarget : Measurable target)
    (hx_zero : Measurable[filt.seq 1] (x 0))
    (hxBar_zero : Measurable[filt.seq 1] (xBar 0))
    (herr_observable :
      ∀ t : ℕ, Measurable[filt.seq ((t + 1) + 1)] (err (t + 1)))
    (hxUnder_update :
      ∀ t : ℕ,
        xUnder (t + 1) =
          fun ω => (1 - alpha (t + 1)) • xBar t ω + alpha (t + 1) • x t ω)
    (hx_update :
      ∀ t : ℕ,
        x (t + 1) =
          fun ω =>
            x t ω - lam (t + 1) • (target (xUnder (t + 1) ω) + err (t + 1) ω))
    (hxBar_update :
      ∀ t : ℕ,
        xBar (t + 1) =
          fun ω =>
            xUnder (t + 1) ω -
              beta (t + 1) • (target (xUnder (t + 1) ω) + err (t + 1) ω)) :
    ∀ t : ℕ,
      Measurable[filt.seq (t + 1)] (x t) ∧
        Measurable[filt.seq (t + 1)] (xBar t) := by
  intro t
  induction t with
  | zero =>
      exact ⟨hx_zero, hxBar_zero⟩
  | succ t ih =>
      have hpast_le_current : filt.seq (t + 1) ≤ filt.seq ((t + 1) + 1) :=
        filt.mono (Nat.le_succ (t + 1))
      have hx_prev_current : Measurable[filt.seq ((t + 1) + 1)] (x t) :=
        ih.1.mono hpast_le_current le_rfl
      have hxBar_prev_current : Measurable[filt.seq ((t + 1) + 1)] (xBar t) :=
        ih.2.mono hpast_le_current le_rfl
      have hxUnder_past : Measurable[filt.seq (t + 1)] (xUnder (t + 1)) := by
        rw [hxUnder_update t]
        exact (ih.2.const_smul (1 - alpha (t + 1))).add
          (ih.1.const_smul (alpha (t + 1)))
      have hxUnder_current :
          Measurable[filt.seq ((t + 1) + 1)] (xUnder (t + 1)) :=
        hxUnder_past.mono hpast_le_current le_rfl
      have htarget_current :
          Measurable[filt.seq ((t + 1) + 1)]
            (fun ω => target (xUnder (t + 1) ω)) :=
        htarget.comp hxUnder_current
      have herr_current : Measurable[filt.seq ((t + 1) + 1)] (err (t + 1)) :=
        herr_observable t
      have hx_succ :
          Measurable[filt.seq ((t + 1) + 1)] (x (t + 1)) := by
        rw [hx_update t]
        exact hx_prev_current.sub
          ((htarget_current.add herr_current).const_smul (lam (t + 1)))
      have hxBar_succ :
          Measurable[filt.seq ((t + 1) + 1)] (xBar (t + 1)) := by
        rw [hxBar_update t]
        exact hxUnder_current.sub
          ((htarget_current.add herr_current).const_smul (beta (t + 1)))
      exact ⟨hx_succ, hxBar_succ⟩


-- Generalization plan (G0):
-- concept/name: accelerated_two_state_l2_of_oracle_error_l2 exposes the
--   square-integrability induction for two accelerated state coordinates driven
--   by a shared gradient-plus-oracle-error direction; orig was
--   generated_state_l2_of_adaptiveOracleProcess, renamed away from generated
--   sample-stream setup fields.
-- generality used: arbitrary finite measure space, an abstract real normed
--   vector group, a base point, two state coordinates, a search coordinate, an
--   oracle-error process, a gradient-like map, scalar schedules, a gradient L2
--   bridge from centered search-point L2, pointwise oracle-error L2, and a.e.
--   affine update laws; no convexity, smoothness statement, probability class,
--   Hilbert structure, independence, or finite-dimensional assumption is used.
-- portable call pattern: accelerated stochastic-gradient, accelerated
--   mirror-style, and variance-reduced two-sequence proofs can call this after
--   adaptedness/measurability is established, centered L2 at the search point is
--   converted to gradient L2, and each centered oracle error has a second
--   moment bound.
-- counterargument checked: this is not only paper-local traceability because
--   the same induction recurs for any two-coordinate accelerated recursion with
--   a search affine blend and two affine updates by a shared noisy direction;
--   it is larger than a caller-side expression and not a pure wrapper around a
--   single existing affine L2 transport lemma.
-- coverage search: searched `MemLp affine update square integrable two state
--   oracle error`, `integrable squared norm const sub affine combination MemLp`,
--   and `two accelerated state l2 induction affine updates gradient error
--   integrable squared norm`; closest hits were SOptLib
--   `integrable_sq_norm_const_sub_two_stage_affine`,
--   `integrable_sq_norm_const_sub_affine_update`,
--   `accelerated_two_state_adapted_of_observable_error`, and
--   `integrable_sq_norm_grad_of_lipschitz_grad_centered_l2`, all component
--   lemmas rather than this full two-state L2 induction.
-- minimal hypotheses: global setup assumptions are replaced by pointwise
--   measurability, a gradient L2 bridge, error L2, and a.e. update equations;
--   the finite-measure frame is retained from the stochastic-optimization
--   probability setting and makes constant integrability available directly.

/-- Two accelerated affine state coordinates remain centered square-integrable
when the shared oracle error is square-integrable.

If the search point is an affine blend of the previous raw and averaged
coordinates, the gradient-like direction is L2 whenever the search point is
centered L2, and both next coordinates are affine updates by the same
gradient-plus-error direction, then both state coordinates have integrable
squared distance from the fixed base point at every time.

Layer: Layer1 | Gap: Level 1 (two-coordinate accelerated L2 induction)
Proof: induct on time, convert centered squared integrability to `MemLp` at
  exponent two, close the search blend and noisy update directions under
  addition and scalar multiplication, and transport through the three a.e.
  update identities.
Source: Mathlib Lp-space closure and Bochner squared-norm integrability APIs
Used in: nonconvex stochastic accelerated gradient descent proving generated
  raw and averaged iterates are square-integrable before gradient, value-gap,
  and martingale-integrability steps
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem accelerated_two_state_l2_of_oracle_error_l2
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P]
    (base : E) (x xBar xUnder err : ℕ → Ω → E) (grad : E → E)
    (alpha beta lam : ℕ → ℝ)
    (hx_meas : ∀ t : ℕ, AEStronglyMeasurable (x t) P)
    (hxBar_meas : ∀ t : ℕ, AEStronglyMeasurable (xBar t) P)
    (hgrad_meas :
      ∀ t : ℕ, AEStronglyMeasurable (fun ω => grad (xUnder t ω)) P)
    (herr_meas : ∀ t : ℕ, AEStronglyMeasurable (err t) P)
    (hgrad_sq :
      ∀ t : ℕ,
        Integrable (fun ω => ‖base - xUnder t ω‖ ^ 2) P →
          Integrable (fun ω => ‖grad (xUnder t ω)‖ ^ 2) P)
    (herr_sq : ∀ t : ℕ, Integrable (fun ω => ‖err t ω‖ ^ 2) P)
    (hx_zero : x 0 =ᵐ[P] fun _ => base)
    (hxBar_zero : xBar 0 =ᵐ[P] fun _ => base)
    (hxUnder_update :
      ∀ t : ℕ,
        xUnder (t + 1) =ᵐ[P]
          fun ω => (1 - alpha (t + 1)) • xBar t ω + alpha (t + 1) • x t ω)
    (hx_update :
      ∀ t : ℕ,
        x (t + 1) =ᵐ[P]
          fun ω =>
            x t ω - lam (t + 1) • (grad (xUnder (t + 1) ω) + err (t + 1) ω))
    (hxBar_update :
      ∀ t : ℕ,
        xBar (t + 1) =ᵐ[P]
          fun ω =>
            xUnder (t + 1) ω -
              beta (t + 1) • (grad (xUnder (t + 1) ω) + err (t + 1) ω)) :
    ∀ t : ℕ,
      Integrable (fun ω => ‖base - x t ω‖ ^ 2) P ∧
        Integrable (fun ω => ‖base - xBar t ω‖ ^ 2) P := by
  intro t
  induction t with
  | zero =>
      constructor
      · exact
          (integrable_const (c := (0 : ℝ))).congr
            (by
              filter_upwards [hx_zero] with ω hω
              rw [hω]
              simp)
      · exact
          (integrable_const (c := (0 : ℝ))).congr
            (by
              filter_upwards [hxBar_zero] with ω hω
              rw [hω]
              simp)
  | succ t ih =>
      have hx_disp_l2 : MemLp (fun ω => base - x t ω) 2 P :=
        (memLp_two_iff_integrable_sq_norm
          (aestronglyMeasurable_const.sub (hx_meas t))).2 ih.1
      have hxBar_disp_l2 : MemLp (fun ω => base - xBar t ω) 2 P :=
        (memLp_two_iff_integrable_sq_norm
          (aestronglyMeasurable_const.sub (hxBar_meas t))).2 ih.2
      have hxUnder_raw_l2 :
          MemLp
            (fun ω =>
              (1 - alpha (t + 1)) • (base - xBar t ω) +
                alpha (t + 1) • (base - x t ω))
            2 P :=
        (hxBar_disp_l2.const_smul (1 - alpha (t + 1))).add
          (hx_disp_l2.const_smul (alpha (t + 1)))
      have hxUnder_l2 : MemLp (fun ω => base - xUnder (t + 1) ω) 2 P := by
        refine MemLp.ae_eq ?_ hxUnder_raw_l2
        filter_upwards [hxUnder_update t] with ω hω
        rw [hω]
        module
      have hxUnder_sq :
          Integrable (fun ω => ‖base - xUnder (t + 1) ω‖ ^ 2) P :=
        (memLp_two_iff_integrable_sq_norm hxUnder_l2.aestronglyMeasurable).1
          hxUnder_l2
      have hgrad_l2 : MemLp (fun ω => grad (xUnder (t + 1) ω)) 2 P :=
        (memLp_two_iff_integrable_sq_norm (hgrad_meas (t + 1))).2
          (hgrad_sq (t + 1) hxUnder_sq)
      have herr_l2 : MemLp (err (t + 1)) 2 P :=
        (memLp_two_iff_integrable_sq_norm (herr_meas (t + 1))).2
          (herr_sq (t + 1))
      have hxUnder_disp_l2 : MemLp (fun ω => base - xUnder (t + 1) ω) 2 P :=
        hxUnder_l2
      have hdirection_l2 :
          MemLp (fun ω => grad (xUnder (t + 1) ω) + err (t + 1) ω) 2 P :=
        hgrad_l2.add herr_l2
      have hx_succ_l2 : MemLp (fun ω => base - x (t + 1) ω) 2 P := by
        have hraw :=
          hx_disp_l2.add (hdirection_l2.const_smul (lam (t + 1)))
        refine MemLp.ae_eq ?_ hraw
        filter_upwards [hx_update t] with ω hω
        rw [hω]
        change
          (base - x t ω) +
              lam (t + 1) • (grad (xUnder (t + 1) ω) + err (t + 1) ω) =
            base -
              (x t ω -
                lam (t + 1) • (grad (xUnder (t + 1) ω) + err (t + 1) ω))
        module
      have hxBar_succ_l2 : MemLp (fun ω => base - xBar (t + 1) ω) 2 P := by
        have hraw :=
          hxUnder_disp_l2.add (hdirection_l2.const_smul (beta (t + 1)))
        refine MemLp.ae_eq ?_ hraw
        filter_upwards [hxBar_update t] with ω hω
        rw [hω]
        change
          (base - xUnder (t + 1) ω) +
              beta (t + 1) • (grad (xUnder (t + 1) ω) + err (t + 1) ω) =
            base -
              (xUnder (t + 1) ω -
                beta (t + 1) • (grad (xUnder (t + 1) ω) + err (t + 1) ω))
        module
      constructor
      · exact
          (memLp_two_iff_integrable_sq_norm hx_succ_l2.aestronglyMeasurable).1
            hx_succ_l2
      · exact
          (memLp_two_iff_integrable_sq_norm hxBar_succ_l2.aestronglyMeasurable).1
            hxBar_succ_l2


-- Generalization plan (G0):
-- concept/name: accelerated search-point convex linearization; orig was
--   partB_convex_search_point_linearization, renamed away from the local Part B
--   theorem boundary while keeping the accelerated search-point concept.
-- generality used: deterministic complete real Hilbert space
--   [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E], an
--   arbitrary convex feasible set X, scalar objective f, selected gradient
--   vector g at the search point, scalar a in [0,1], points z, b, xp, and
--   xRef, and the pointwise identity z = (1-a)b + a xp; no measure,
--   filtration, oracle, independence, integrability, smoothness, or
--   finite-dimensional assumptions are used.
-- portable call pattern: accelerated convex stochastic-gradient,
--   variance-reduced accelerated-gradient, and accelerated proximal proofs use
--   the same search-point step when z is the convex combination of the previous
--   averaged point b and the previous main iterate xp; f, grad, a, and the
--   comparison point xRef vary while the conclusion stays unchanged.
-- counterargument checked: this is more than paper-local traceability because
--   it packages the standard accelerated convex linearization used before a
--   one-step recurrence; it is not a pure wrapper because existing SOptLib
--   gives the one-endpoint support inequality but not the two-endpoint
--   weighted assembly and search-point algebra.
-- coverage search: searched `convex function linearization at convex
--   combination weighted inner product`, `ConvexOn HasGradientAt convex linear
--   lower bound inner`, and LeanSearch for the full weighted search-point
--   inequality. Top hits were
--   `ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt`,
--   `ConvexOn.map_sum_le`, and smooth upper-model lemmas; these are partial
--   ingredients and none states the accelerated two-endpoint conclusion.
-- minimal hypotheses: the proof uses only pointwise support at z for xRef and
--   b, nonnegativity of a and 1-a, and the affine search-point equality; xp
--   need not be feasible because it only appears through that equality.

/-- Convexity at an accelerated search point gives the weighted linearization.

If `z = (1 - a) • b + a • xp` with `0 ≤ a ≤ 1`, and `f` is convex with
gradient `g` at `z`, then the gap from `f z` to the weighted endpoint
values is bounded by `a` times the linear model from `xp` to `xRef`.

Layer: Layer1 | Gap: Level 1 (accelerated search-point convex linearization)
Proof: apply the convex first-order support inequality from `z` to `xRef` and
  from `z` to `b`, scale them by `a` and `1-a`, and use the affine
  search-point identity to collapse the two inner products.
Source: SOptLib convex first-order support inequality, Mathlib convex-set
  within-gradient calculus, and Hilbert-space inner-product algebra
Used in: nonconvex stochastic accelerated gradient descent convex-case
  one-step recursion, converting the search-point value into an accelerated
  comparison-point linearization before the distance telescope
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/key_lemmas/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic accelerated gradient descent -/
theorem convex_accelerated_search_point_linearization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (f : E → ℝ) (g : E)
    (a : ℝ) (z b xp xRef : E)
    (hf : ConvexOn ℝ X f) (hz : z ∈ X) (hb : b ∈ X) (hxRef : xRef ∈ X)
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1)
    (hgrad : HasGradientWithinAt f g X z)
    (hz_eq : z = (1 - a) • b + a • xp) :
    f z - ((1 - a) * f b + a * f xRef) ≤
      a * inner ℝ g (xp - xRef) := by
  have hone_minus_nonneg : 0 ≤ 1 - a := by linarith
  have hsupport_ref :
      f z - f xRef ≤ inner ℝ g (z - xRef) := by
    have hsupport :=
      ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
        (E := E) (X := X) (f := f) (g := g) (z := z) (x := xRef)
        hf hz hxRef hgrad
    have hinner : inner ℝ g (xRef - z) =
        - inner ℝ g (z - xRef) := by
      rw [← inner_neg_right]
      simp
    linarith
  have hsupport_bar :
      f z - f b ≤ inner ℝ g (z - b) := by
    have hsupport :=
      ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
        (E := E) (X := X) (f := f) (g := g) (z := z) (x := b)
        hf hz hb hgrad
    have hinner : inner ℝ g (b - z) =
        - inner ℝ g (z - b) := by
      rw [← inner_neg_right]
      simp
    linarith
  have hcomb :
      a * (f z - f xRef) + (1 - a) * (f z - f b) ≤
        a * inner ℝ g (z - xRef) +
          (1 - a) * inner ℝ g (z - b) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hsupport_ref ha_nonneg)
      (mul_le_mul_of_nonneg_left hsupport_bar hone_minus_nonneg)
  have hright :
      a * inner ℝ g (z - xRef) +
          (1 - a) * inner ℝ g (z - b) =
        a * inner ℝ g (xp - xRef) := by
    rw [hz_eq]
    simp [sub_eq_add_neg, inner_add_right, inner_smul_right, inner_neg_right,
      add_comm, add_left_comm]
    ring
  calc
    f z - ((1 - a) * f b + a * f xRef) =
        a * (f z - f xRef) + (1 - a) * (f z - f b) := by
      ring
    _ ≤ a * inner ℝ g (z - xRef) +
          (1 - a) * inner ℝ g (z - b) := hcomb
    _ = a * inner ℝ g (xp - xRef) := hright


-- Generalization plan (G0):
-- concept/name: accelerated_sgd_convex_one_step_recursion exposes the
--   accelerated stochastic-gradient convex one-step recurrence assembled from
--   a smooth upper model, convex search-point linearization, and Hilbert update
--   identity; orig was partB_one_step_convex_recursion, renamed away from the
--   local Part B proof boundary.
-- generality used: a deterministic real Hilbert space, an objective f with a
--   selected gradient map, seven point variables, the local step-size scalars,
--   nonzero stochastic-gradient and main stepsizes beta and lam,
--   two affine update equalities, and the exact pointwise smooth and convex
--   linearization inequalities; no measure, filtration, oracle law,
--   integrability, global convexity class, or finite-dimensional assumption is
--   used by this assembly lemma.
-- portable call pattern: accelerated stochastic-gradient, variance-reduced
--   accelerated-gradient, and randomized accelerated proximal-gradient proofs
--   call this after deriving the local smooth model and convex search-point
--   support inequality, while changing f, grad, the iterates, reference point,
--   step sizes, and centered residual.
-- counterargument checked: this is not merely paper-local traceability because
--   the same pathwise recurrence is the reusable boundary before Gamma
--   telescoping in accelerated stochastic-gradient analyses; existing SOptLib
--   `accelerated_composite_one_step_recursion` is prox/Bregman-composite and
--   does not expose this smooth convex gradient-step residual formula.
-- coverage search: searched `accelerated stochastic gradient convex one step
--   recursion noise inner update squared distance`, `convex accelerated search
--   point linearization`, and `smooth upper bound function value gradient
--   lipschitz norm square`. Top hits were SOptLib
--   `accelerated_composite_one_step_recursion`, staged
--   `convex_accelerated_search_point_linearization`, staged
--   `inner_update_eq_sq_dist_sub_sq_dist_add_norm_sq`, and smooth upper-model
--   lemmas; these are partial ingredients rather than the full recurrence.
-- minimal hypotheses: global convexity and Lipschitz-gradient assumptions are
--   weakened to the exact local inequalities they provide; beta nonzeroness is
--   exactly what the scalar coefficient collection needs and lam nonzeroness is
--   exactly what the distance-drop identity needs.

/-- A smooth convex accelerated stochastic-gradient step satisfies the pathwise
one-step recursion.

If the averaged point is updated by `z - beta • (grad z + delta)`, the main
iterate by `xPrev - lam • (grad z + delta)`, a smooth upper model holds from
`z` to the averaged point, and convexity has already supplied the accelerated
search-point linearization, then the usual squared-distance recursion with the
explicit residual cross term follows.

Layer: Layer1 | Gap: Level 1 (accelerated stochastic-gradient convex one-step recurrence)
Proof: expand the smooth model along the stochastic averaged update, insert the
  convex search-point linearization, convert the main-update inner product with
  the Hilbert distance-drop identity, and collect the gradient, residual, and
  cross terms by real field arithmetic.
Source: accelerated stochastic-gradient estimate-sequence algebra, Mathlib
  real Hilbert-space norm-square identities, and ordered real-field arithmetic
Used in: nonconvex stochastic accelerated gradient descent convex branch before
  Gamma normalization, distance telescoping, and martingale residual cancellation
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/key_lemmas/Convex_search_point_linearization
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem accelerated_sgd_convex_one_step_recursion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E)
    (xPrev xNext bPrev bNext z xRef delta : E)
    (alpha beta lam L : ℝ)
    (hbeta_ne : beta ≠ 0)
    (hlam_ne : lam ≠ 0)
    (hb_update : bNext = z - beta • (grad z + delta))
    (hx_update : xNext = xPrev - lam • (grad z + delta))
    (hsmooth :
      f bNext ≤
        f z + inner ℝ (grad z) (bNext - z) +
          (L / 2) * ‖bNext - z‖ ^ 2)
    (hconv :
      f z ≤
        (1 - alpha) * f bPrev + alpha * f xRef +
          alpha * inner ℝ (grad z) (xPrev - xRef)) :
    f bNext - f xRef ≤
      (1 - alpha) * (f bPrev - f xRef) +
        alpha / (2 * lam) *
          (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) -
        beta * (1 - L * beta / 2 - alpha * lam / (2 * beta)) *
          ‖grad z‖ ^ 2 +
        (L * beta ^ 2 + alpha * lam) / 2 * ‖delta‖ ^ 2 +
        inner ℝ delta
          (((L * beta ^ 2 + alpha * lam - beta) • grad z) +
            alpha • (xRef - xPrev)) := by
  let g : E := grad z
  have hb_disp : bNext - z = (-beta) • (g + delta) := by
    rw [hb_update]
    simp [g, sub_eq_add_neg, neg_smul]
    abel
  have hnorm_bar :
      ‖bNext - z‖ ^ 2 = beta ^ 2 * ‖g + delta‖ ^ 2 := by
    rw [hb_disp, norm_smul, mul_pow]
    have hnorm_neg_beta_sq : ‖(-beta)‖ ^ 2 = beta ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs, neg_sq]
    rw [hnorm_neg_beta_sq]
  have hsmooth_exp :
      f bNext ≤
        f z -
          beta * (1 - L * beta / 2) * ‖g‖ ^ 2 +
          (L * beta ^ 2 / 2) * ‖delta‖ ^ 2 +
          (L * beta ^ 2 - beta) * inner ℝ g delta := by
    have halg :
        f z + inner ℝ (grad z) (bNext - z) +
            (L / 2) * ‖bNext - z‖ ^ 2 =
          f z -
            beta * (1 - L * beta / 2) * ‖g‖ ^ 2 +
            (L * beta ^ 2 / 2) * ‖delta‖ ^ 2 +
            (L * beta ^ 2 - beta) * inner ℝ g delta := by
      rw [hnorm_bar, hb_disp]
      simp [g, norm_add_sq_real, inner_add_right, inner_smul_right]
      ring
    exact le_trans hsmooth (le_of_eq halg)
  have hpre :
      f bNext - f xRef ≤
        (1 - alpha) * (f bPrev - f xRef) +
          alpha * inner ℝ g (xPrev - xRef) -
          beta * (1 - L * beta / 2) * ‖g‖ ^ 2 +
          (L * beta ^ 2 / 2) * ‖delta‖ ^ 2 +
          (L * beta ^ 2 - beta) * inner ℝ g delta := by
    nlinarith [hsmooth_exp, hconv]
  have hthree :
      alpha * inner ℝ (g + delta) (xPrev - xRef) =
        alpha / (2 * lam) *
            (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) +
          alpha * lam / 2 * ‖g + delta‖ ^ 2 := by
    exact inner_update_eq_sq_dist_sub_sq_dist_add_norm_sq
      xPrev xNext xRef (g + delta) alpha lam hlam_ne (by simpa [g] using hx_update)
  have hsplit :
      alpha * inner ℝ g (xPrev - xRef) =
        alpha / (2 * lam) *
            (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) +
          alpha * lam / 2 * ‖g + delta‖ ^ 2 -
          alpha * inner ℝ delta (xPrev - xRef) := by
    have hadd :
        alpha * inner ℝ (g + delta) (xPrev - xRef) =
          alpha * inner ℝ g (xPrev - xRef) +
            alpha * inner ℝ delta (xPrev - xRef) := by
      simp [inner_add_left, mul_add]
    nlinarith [hthree, hadd]
  have halg_final :
      (1 - alpha) * (f bPrev - f xRef) +
          alpha * inner ℝ g (xPrev - xRef) -
          beta * (1 - L * beta / 2) * ‖g‖ ^ 2 +
          (L * beta ^ 2 / 2) * ‖delta‖ ^ 2 +
          (L * beta ^ 2 - beta) * inner ℝ g delta =
        (1 - alpha) * (f bPrev - f xRef) +
          alpha / (2 * lam) *
            (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) -
          beta * (1 - L * beta / 2 - alpha * lam / (2 * beta)) * ‖g‖ ^ 2 +
          (L * beta ^ 2 + alpha * lam) / 2 * ‖delta‖ ^ 2 +
          inner ℝ delta
            (((L * beta ^ 2 + alpha * lam - beta) • g) +
              alpha • (xRef - xPrev)) := by
    rw [hsplit, norm_add_sq_real]
    simp [inner_add_right, inner_smul_right, real_inner_comm]
    have hxref : inner ℝ delta (xRef - xPrev) =
        -inner ℝ delta (xPrev - xRef) := by
      rw [← inner_neg_right]
      congr 1
      abel
    rw [hxref]
    field_simp [hbeta_ne]
    ring
  calc
    f bNext - f xRef
        ≤
        (1 - alpha) * (f bPrev - f xRef) +
          alpha * inner ℝ g (xPrev - xRef) -
          beta * (1 - L * beta / 2) * ‖g‖ ^ 2 +
          (L * beta ^ 2 / 2) * ‖delta‖ ^ 2 +
          (L * beta ^ 2 - beta) * inner ℝ g delta := hpre
    _ =
        (1 - alpha) * (f bPrev - f xRef) +
          alpha / (2 * lam) *
            (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) -
          beta * (1 - L * beta / 2 - alpha * lam / (2 * beta)) * ‖g‖ ^ 2 +
          (L * beta ^ 2 + alpha * lam) / 2 * ‖delta‖ ^ 2 +
          inner ℝ delta
            (((L * beta ^ 2 + alpha * lam - beta) • g) +
              alpha • (xRef - xPrev)) := halg_final
    _ =
      (1 - alpha) * (f bPrev - f xRef) +
        alpha / (2 * lam) *
          (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) -
        beta * (1 - L * beta / 2 - alpha * lam / (2 * beta)) *
          ‖grad z‖ ^ 2 +
        (L * beta ^ 2 + alpha * lam) / 2 * ‖delta‖ ^ 2 +
        inner ℝ delta
          (((L * beta ^ 2 + alpha * lam - beta) • grad z) +
            alpha • (xRef - xPrev)) := by
      rfl

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: selected-block composite pathwise descent from update and prox;
--   orig was `theorem69_selected_block_pathwise_stochastic_descent`, renamed
--   away from theorem numbering and paper setup names while retaining the
--   stochastic-optimization selected-block descent concept.
-- generality used: a finite decidable block index type, an abstract state, and
--   one real Hilbert selected-block direction space.  No measure, filtration,
--   independence, integrability, convexity, or finite-dimensional assumption is
--   used; the proof consumes only pointwise smooth descent, off-block simple
--   term preservation, a selected-block prox inequality, and the residual
--   identity.
-- portable call pattern: randomized block coordinate, stochastic block mirror,
--   and coordinate proximal-gradient proofs call this after establishing the
--   local smooth upper model and selected-block prox inequality; the state
--   representation, selected coordinate map, oracle vector, gradient block,
--   simple terms, and update rule vary while the composite descent conclusion
--   stays unchanged.
-- counterargument checked: not paper-local traceability because it packages
--   the recurring one-step composite descent assembly above the smooth-model
--   and prox-inequality APIs; not a pure wrapper because existing SOptLib hits
--   cover the smooth model and prox projected-gradient lower bound separately,
--   but not their selected-block composite objective assembly.
-- coverage search: queried `selected block composite pathwise descent update
--   prox inequality smooth upper bound`, `composite objective descent of block
--   smooth upper model prox inequality unchanged coordinates`, `smooth decrease
--   plus simple term prox inequality composite descent`, and LeanSearch
--   `one step composite descent from smooth upper bound and proximal gradient
--   inequality`; relevant partial hits were
--   `block_smooth_upper_bound_of_coordinate_gradient_lipschitz`,
--   `composite_prox_projectedGradient_inner_ge_norm_sq_add_hdiff_of_isMinOn`,
--   and accelerated composite recurrences, but no full selected-block
--   composite descent assembler with this conclusion.
-- minimal hypotheses: the update rule is represented by the already-derived
--   pointwise smooth descent inequality, and unchanged off-coordinates are
--   represented only as equality of off-block simple terms; all hypotheses are
--   pointwise at the selected step.

/-- A selected-block smooth decrease and prox inequality give one-step
composite pathwise descent.

If the smooth part decreases according to the selected block displacement, all
non-selected simple terms are unchanged, and the selected prox step controls
the selected simple-term change, then the composite objective decreases up to
the selected residual inner product.

Layer: Layer1 | Gap: Level 1 (selected-block composite descent assembly)
Proof: split the finite simple-term sum into selected and off-selected parts,
  scale the prox lower bound by the positive stepsize, rewrite the residual
  inner product, and collect the smooth and simple-term inequalities.
Source: coordinate proximal-gradient descent algebra, Mathlib finite-sum
  erase identities, real inner-product algebra, and ordered-field arithmetic
Used in: nonconvex stochastic block mirror descent selected-block pathwise
  descent after the block smooth model and selected-block prox inequality
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/key_lemmas/1/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem selected_block_composite_pathwise_descent_of_update_prox
    {I State E : Type*} [Fintype I] [DecidableEq I]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (smoothPart : State → ℝ) (simple : I → State → ℝ)
    (x xNext : State) (i : I) (gamma L : ℝ)
    (gradBlock y spg delta : E)
    (hgamma : 0 < gamma)
    (hsmooth :
      smoothPart xNext ≤
        smoothPart x - gamma * ⟪gradBlock, spg⟫_ℝ +
          (L / 2) * gamma ^ 2 * ‖spg‖ ^ 2)
    (hsimple_other : ∀ j, j ≠ i → simple j xNext = simple j x)
    (hprox :
      ‖spg‖ ^ 2 + gamma⁻¹ * (simple i xNext - simple i x) ≤
        ⟪y, spg⟫_ℝ)
    (hdelta : delta = y - gradBlock) :
    gamma * (1 - L / 2 * gamma) * ‖spg‖ ^ 2 ≤
      (smoothPart x + ∑ j, simple j x) -
        (smoothPart xNext + ∑ j, simple j xNext) +
          gamma * ⟪delta, spg⟫_ℝ := by
  classical
  have hsimple_erase :
      (Finset.univ.erase i).sum (fun j => simple j xNext) =
        (Finset.univ.erase i).sum (fun j => simple j x) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hsimple_other j (Finset.mem_erase.mp hj).1
  have hsimple_sum :
      (∑ j, simple j xNext) =
        (∑ j, simple j x) + (simple i xNext - simple i x) := by
    have hnew_split :
        (∑ j, simple j xNext) =
          simple i xNext + (Finset.univ.erase i).sum (fun j => simple j xNext) := by
      exact
        (Finset.add_sum_erase (s := Finset.univ) (f := fun j => simple j xNext)
          (a := i) (Finset.mem_univ i)).symm
    have hold_split :
        (∑ j, simple j x) =
          simple i x + (Finset.univ.erase i).sum (fun j => simple j x) := by
      exact
        (Finset.add_sum_erase (s := Finset.univ) (f := fun j => simple j x)
          (a := i) (Finset.mem_univ i)).symm
    calc
      (∑ j, simple j xNext)
          = simple i xNext + (Finset.univ.erase i).sum (fun j => simple j xNext) :=
            hnew_split
      _ = simple i xNext + (Finset.univ.erase i).sum (fun j => simple j x) := by
            rw [hsimple_erase]
      _ = (simple i x + (Finset.univ.erase i).sum (fun j => simple j x)) +
            (simple i xNext - simple i x) := by
            ring
      _ = (∑ j, simple j x) + (simple i xNext - simple i x) := by
            rw [hold_split]
  have hprox_scaled :
      gamma * ‖spg‖ ^ 2 + (simple i xNext - simple i x) ≤
        gamma * ⟪y, spg⟫_ℝ := by
    have hmul := mul_le_mul_of_nonneg_left hprox hgamma.le
    calc
      gamma * ‖spg‖ ^ 2 + (simple i xNext - simple i x)
          = gamma * (‖spg‖ ^ 2 + gamma⁻¹ * (simple i xNext - simple i x)) := by
            field_simp [hgamma.ne']
      _ ≤ gamma * ⟪y, spg⟫_ℝ := hmul
  have hdelta_inner :
      ⟪delta, spg⟫_ℝ = ⟪y, spg⟫_ℝ - ⟪gradBlock, spg⟫_ℝ := by
    subst delta
    simp [inner_sub_left]
  rw [hsimple_sum]
  nlinarith [hsmooth, hprox_scaled, hdelta_inner]

end SOptLib


-- Phase 4 batch 2 merge from Staging/auxiliaryResidualProcess_measurable_wrt_strictPast.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: strict-past measurability of an auxiliary residual-driven
--   recursive process; orig was `auxiliaryIterate_strictPast_measurable`,
--   renamed away from the saddle-point iterate label to expose the reusable
--   residual-process adaptedness step.
-- generality used: arbitrary source type and strict-past sigma-algebra family,
--   arbitrary measurable current-query, sample, residual, auxiliary-state, and
--   output spaces; no measure, independence, convexity, Hilbert, norm, or
--   finite-dimensional assumptions are used.
-- portable call pattern: mirror-descent, variance-reduction, and auxiliary
--   sequence proofs where an auxiliary recursion is updated by a residual
--   `G (current j) (sample j) - target (current j)` built from an already
--   strict-past measurable current query and the revealed sample coordinate.
-- counterargument checked: not paper-local traceability because it packages the
--   reusable residual-driver composition with recursive strict-past
--   measurability; not a duplicate of `recursiveProcess_measurable_wrt_strictPast`
--   because that base lemma requires the driver measurability as a hypothesis,
--   while this theorem derives it from the current/sample residual contract.
-- coverage search: searched `recursive process measurable strict past adapted
--   residual update`, `measurable composition filtration monotone generated
--   process update`, and `residual process measurable adapted query sample
--   target update strict past`; top hits were SOptLib
--   `recursiveProcess_measurable_wrt_strictPast`,
--   `recursive_process_measurable_wrt_sample_prefix`, and Layer0
--   `oracleResidual_aestronglyMeasurable_of_query_sample_measurable`, all partial
--   rather than this strict-past recursive residual-process wrapper.
-- minimal hypotheses: the global saddle setup is replaced by pointwise
--   measurability of current queries, samples, residual kernel, target map,
--   update kernel, output projection, and only the monotonicity needed to lift
--   `past j` to the target strict-past sigma-algebra `past N`.

/-- An auxiliary residual-driven recursion is measurable with respect to a strict-past prefix.

If the current query at step `j` is measurable in `past j`, the sample coordinate
and auxiliary state live in a common target prefix `past N`, the residual kernel
`G x s - target x` is jointly measurable through its components, and the
auxiliary recursion updates by a measurable state-residual kernel, then the
projected auxiliary state at time `N` is measurable for `past N`.

Layer: Layer1 | Gap: Level 1 (strict-past residual-process adaptedness)
Proof: derive measurability of each residual driver by lifting the current query
  along strict-past monotonicity and composing the measurable kernel and target;
  then invoke `SOptLib.recursiveProcess_measurable_wrt_strictPast`.
Source: Mathlib measure-theory product, subtraction, and composition APIs
  together with SOptLib recursive-process strict-past measurability
Used in: stochastic saddle-point mirror descent adaptedness of the auxiliary
  mirror sequence driven by the current oracle residual
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic convex-concave saddle point -/
theorem auxiliaryResidualProcess_measurable_wrt_strictPast
    {Ω S X E V Y : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace E] [Sub E] [MeasurableSub₂ E] [MeasurableSpace V]
    [MeasurableSpace Y]
    (past : ℕ → MeasurableSpace Ω)
    (sample : ℕ → Ω → S)
    (current : ℕ → Ω → X)
    (aux : ℕ → Ω → V)
    (project : V → Y)
    (G : X → S → E)
    (target : X → E)
    (step : ℕ → V → E → V)
    (N : ℕ)
    (h_past_mono : ∀ {a b : ℕ}, a ≤ b → past a ≤ past b)
    (h_init : Measurable[past N] (aux 0))
    (h_sample : ∀ j, j + 1 ≤ N → Measurable[past N] (sample j))
    (h_current : ∀ j, j + 1 ≤ N → Measurable[past j] (current j))
    (h_G : Measurable (fun p : X × S => G p.1 p.2))
    (h_target : Measurable target)
    (h_step : ∀ j, j + 1 ≤ N →
      Measurable (fun p : V × E => step j p.1 p.2))
    (h_update : ∀ j, j + 1 ≤ N →
      aux (j + 1) =
        fun ω => step j (aux j ω) (G (current j ω) (sample j ω) - target (current j ω)))
    (h_project : Measurable project) :
    Measurable[past N] (fun ω => project (aux N ω)) := by
  let driver : ℕ → Ω → E :=
    fun j ω => G (current j ω) (sample j ω) - target (current j ω)
  have hdriver :
      ∀ j, j + 1 ≤ N →
        Measurable[past N] (driver j) := by
    intro j hj
    have hjN : j ≤ N := Nat.le_of_succ_le hj
    have hcurrent_N : Measurable[past N] (current j) :=
      (h_current j hj).mono (h_past_mono hjN) le_rfl
    have hG_slice : Measurable[past N] (fun ω => G (current j ω) (sample j ω)) :=
      h_G.comp (hcurrent_N.prodMk (h_sample j hj))
    have htarget_slice : Measurable[past N] (fun ω => target (current j ω)) :=
      h_target.comp hcurrent_N
    simpa [driver] using hG_slice.sub htarget_slice
  have hcore : Measurable[past N] (aux N) :=
    SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past)
      (process := aux)
      (driver := driver)
      (step := step)
      (k := N)
      (N := N)
      h_init (fun j hj _hprocess => hdriver j hj) h_step
      (by
        intro j hj
        simpa [driver] using h_update j hj)
      N le_rfl
  exact h_project.comp hcore

/-- Combine sampled-oracle and auxiliary-residual one-step bounds into a mean-oracle budget.

If `mean = gt - dt`, a sampled-oracle step controls the pairing with `zt - u`,
and an auxiliary residual step controls the pairing with `u - vt`, then their
sum controls the mean-oracle pairing with the retained cross correction
`γ * ⟪zt - vt, dt⟫_ℝ`.

Layer: Layer1 | Gap: Level 1 (mean-oracle one-step budget assembly with residual cross correction)
Proof: expand `mean = gt - dt`, split the residual pairing through `zt - vt` and `vt - u`, then compose the two supplied one-step inequalities by ordered-ring arithmetic.
Source: Mathlib real Hilbert-space inner-product algebra and ordered-ring inequality arithmetic
Used in: stochastic convex-concave saddle-point mirror descent when the sampled mirror step and auxiliary residual mirror step are combined before finite-window telescoping
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
theorem combined_mean_oracle_one_step_budget_of_residual_auxiliary_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (dualNorm : E → ℝ) (γ : ℝ)
    (zt vt u gt dt mean : E) (zDrop vDrop : ℝ)
    (hmean : mean = gt - dt)
    (hStochastic :
      γ * ⟪gt, zt - u⟫_ℝ ≤
        zDrop + (1 / 2 : ℝ) * γ ^ 2 * dualNorm gt ^ 2)
    (hAuxiliary :
      γ * ⟪dt, u - vt⟫_ℝ ≤
        vDrop + (1 / 2 : ℝ) * γ ^ 2 * dualNorm dt ^ 2) :
    γ * ⟪mean, zt - u⟫_ℝ ≤
      zDrop + vDrop +
        (1 / 2 : ℝ) * γ ^ 2 * dualNorm gt ^ 2 +
        (1 / 2 : ℝ) * γ ^ 2 * dualNorm dt ^ 2 -
        γ * ⟪zt - vt, dt⟫_ℝ := by
  have hsplit :
      γ * ⟪mean, zt - u⟫_ℝ =
        γ * ⟪gt, zt - u⟫_ℝ +
          γ * ⟪dt, u - vt⟫_ℝ -
          γ * ⟪zt - vt, dt⟫_ℝ := by
    rw [hmean]
    simp only [inner_sub_left, mul_sub]
    rw [real_inner_comm dt zt, real_inner_comm dt vt]
    have hvec : zt - u = (zt - vt) + (vt - u) := by
      abel
    rw [hvec]
    simp_rw [inner_add_right]
    have huv : vt - u = -(u - vt) := by
      abel
    rw [huv]
    simp_rw [inner_neg_right]
    simp_rw [inner_sub_right]
    ring
  nlinarith [hStochastic, hAuxiliary, hsplit]


-- Phase 4 batch 3 merge from Staging/recursive_prefix_iterate_and_sampled_direction_aestronglyMeasurable.lean

open MeasureTheory

noncomputable section

-- Generalization plan (G0):
-- concept/name: finite-prefix a.e.-strong measurability induction for a
--   recursive iterate and its sampled direction; orig was
--   `rsgfPrefixIterate_and_oracle_aestronglyMeasurable`
-- generality used: arbitrary sample type, arbitrary topological state/direction
--   type, arbitrary base measurable space and measure, an abstract sampled
--   kernel, and an abstract time-indexed update; no probability, independence,
--   integrability, algebraic, convexity, smoothness, or finite-dimensional
--   assumptions are used
-- portable call pattern: finite-horizon stochastic-gradient, zeroth-order, and
--   randomized-coordinate recursions repeatedly prove the current iterate and
--   its fresh sampled direction a.e.-strongly measurable; the prefix law,
--   sample coordinates, kernel, update, and horizon vary while the induction
--   conclusion stays the same
-- counterargument checked: not paper-local traceability and not a one-line
--   wrapper, because it packages the complete finite-horizon law-scoped
--   induction; existing recursive-process lemmas require exact measurability,
--   while the sampled-coordinate staging lemma supplies only the kernel step
--   for one already-measurable query
-- coverage search: queried `recursive iterate and sampled oracle a.e. strongly
--   measurable from measurable update kernel and prefix product measure` and
--   `finite product prefix recursive iterate sampled coordinate kernel both
--   aestrongly measurable induction`; closest hits were
--   `SOptLib.recursive_process_measurable_of_measurable_update`,
--   `recursive_process_measurable_of_measurable_update_oracle`,
--   `SOptLib.recursive_momentum_process_prefix_aestronglyMeasurable`, and
--   `aestronglyMeasurable_sampled_coordinate_kernel_of_adapted_query`, all
--   partial because they respectively require exact measurability, specialize
--   the state recursion, or establish only one sampled-kernel step
-- minimal hypotheses: all are pointwise in time and law-scoped; bounded
--   indices expose the finite-horizon domain directly, the update premise asks
--   only for preservation of a.e.-strong measurability for the actual
--   state/direction target, and the recursion is assumed only at valid steps

/-- Every pre-update iterate and its sampled direction are a.e.-strongly
measurable along a finite recursive process.

The sampled-kernel premise is deliberately law-scoped: it can be discharged by
independence or finite-product coordinate splitting even when the kernel is not
known to be globally measurable.

Layer: Layer1 | Gap: Level 1 (law-scoped finite-prefix recursion measurability)
Proof: induct over the pre-update time index; the base process is constant, and each successor first applies the sampled-kernel premise and then the update's a.e.-strong measurability closure.
Source: Mathlib a.e.-strong measurability closure and bounded-index induction APIs
Used in: stochastic gradient and zeroth-order finite-prefix arguments that need both the current query and its fresh sampled update direction measurable before taking prefix expectations
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/steps
Origin algorithm: Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem recursive_prefix_iterate_and_sampled_direction_aestronglyMeasurable
    {Ω Z E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    (μ : Measure Ω) (N : ℕ) (x0 : E)
    (sample : Fin N → Ω → Z)
    (kernel : E → Z → E) (step : Fin N → E → E → E)
    (process : Fin (N + 1) → Ω → E)
    (h_zero : process 0 = fun _ => x0)
    (h_kernel :
      ∀ n : Fin N,
        AEStronglyMeasurable (process n.castSucc) μ →
          AEStronglyMeasurable
            (fun ω => kernel (process n.castSucc ω) (sample n ω)) μ)
    (h_step :
      ∀ n : Fin N, ∀ X D : Ω → E,
        AEStronglyMeasurable X μ → AEStronglyMeasurable D μ →
          AEStronglyMeasurable (fun ω => step n (X ω) (D ω)) μ)
    (h_succ :
      ∀ n : Fin N,
        process n.succ = fun ω =>
          step n (process n.castSucc ω)
            (kernel (process n.castSucc ω) (sample n ω))) :
    ∀ n : Fin N,
      AEStronglyMeasurable (process n.castSucc) μ ∧
        AEStronglyMeasurable
          (fun ω => kernel (process n.castSucc ω) (sample n ω)) μ := by
  have hprocess :
      ∀ n : Fin (N + 1), AEStronglyMeasurable (process n) μ := by
    intro n
    refine Fin.induction ?_ ?_ n
    · have hconst : AEStronglyMeasurable (fun _ : Ω => x0) μ :=
        aestronglyMeasurable_const
      simpa only [h_zero] using hconst
    · intro n hprev
      have hdirection := h_kernel n hprev
      have hupdated := h_step n (process n.castSucc)
        (fun ω => kernel (process n.castSucc ω) (sample n ω))
        hprev hdirection
      simpa only [h_succ n] using hupdated
  intro n
  have hcurrent := hprocess n.castSucc
  exact ⟨hcurrent, h_kernel n hcurrent⟩

/-- The expected squared distance after an affine oracle update splits into
target, residual, and oracle second-moment terms.

If `xNext = x - eta • oracle` and `oracle = target + residual`, current
distance and oracle second moments together with residual cross-term
integrability suffice for the exact integrated Hilbert-space identity.

Layer: Layer1 | Gap: Level 1 (integrated affine-update distance identity with oracle residual split)
Proof: expand the update pointwise by real Hilbert polarization, split the oracle inner product, derive target-inner integrability from the oracle and residual terms, and apply Bochner integral linearity.
Source: Mathlib real inner-product norm-square polarization and Bochner integral linearity, with SOptLib L2 inner-product integrability
Used in: stochastic gradient, zeroth-order, and variance-reduced one-step analyses before residual cancellation and distance telescoping
Book citation: book/FOML/StochasticZerothOrder.json#/main_theorem/proof/13
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem integral_sq_dist_update_eq_sq_dist_sub_inner_add_norm_sq_of_oracle_eq_target_add_residual
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    (P : Measure Omega)
    (x xNext target residual oracle : Omega -> E)
    (xStar : E) (eta : Real)
    (h_update : forall omega, xNext omega = x omega - eta • oracle omega)
    (h_split : forall omega, oracle omega = target omega + residual omega)
    (hx_meas : AEStronglyMeasurable x P)
    (horacle_meas : AEStronglyMeasurable oracle P)
    (hx_sq : Integrable (fun omega => ‖x omega - xStar‖ ^ (2 : Nat)) P)
    (horacle_sq : Integrable (fun omega => ‖oracle omega‖ ^ (2 : Nat)) P)
    (hresidual_inner :
      Integrable (fun omega => inner Real (residual omega) (x omega - xStar)) P) :
    (∫ omega, ‖xNext omega - xStar‖ ^ (2 : Nat) ∂P) =
      (∫ omega, ‖x omega - xStar‖ ^ (2 : Nat) ∂P) -
        2 * eta * (∫ omega, inner Real (target omega) (x omega - xStar) ∂P) -
        2 * eta * (∫ omega, inner Real (residual omega) (x omega - xStar) ∂P) +
        eta ^ (2 : Nat) * (∫ omega, ‖oracle omega‖ ^ (2 : Nat) ∂P) := by
  have hdisp_meas :
      AEStronglyMeasurable (fun omega => x omega - xStar) P :=
    hx_meas.sub aestronglyMeasurable_const
  have horacle_inner :
      Integrable (fun omega => inner Real (oracle omega) (x omega - xStar)) P :=
    integrable_inner_of_integrable_sq_norm
      horacle_meas hdisp_meas horacle_sq hx_sq
  have htarget_inner :
      Integrable (fun omega => inner Real (target omega) (x omega - xStar)) P := by
    refine (horacle_inner.sub hresidual_inner).congr
      (Filter.Eventually.of_forall fun omega => ?_)
    change
      inner Real (oracle omega) (x omega - xStar) -
          inner Real (residual omega) (x omega - xStar) =
        inner Real (target omega) (x omega - xStar)
    rw [h_split omega, inner_add_left]
    ring
  have hpoint :
      (fun omega => ‖xNext omega - xStar‖ ^ (2 : Nat)) =ᵐ[P]
        (fun omega =>
          ‖x omega - xStar‖ ^ (2 : Nat) -
            2 * eta * inner Real (target omega) (x omega - xStar) -
            2 * eta * inner Real (residual omega) (x omega - xStar) +
            eta ^ (2 : Nat) * ‖oracle omega‖ ^ (2 : Nat)) := by
    filter_upwards with omega
    rw [h_update omega]
    have hreassoc :
        (x omega - eta • oracle omega) - xStar =
          (x omega - xStar) - eta • oracle omega := by
      abel
    rw [hreassoc, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, h_split omega, inner_add_right,
      real_inner_comm (x omega - xStar) (target omega),
      real_inner_comm (x omega - xStar) (residual omega)]
    ring
  have htarget_scaled :
      Integrable
        (fun omega => 2 * eta * inner Real (target omega) (x omega - xStar)) P :=
    htarget_inner.const_mul (2 * eta)
  have hresidual_scaled :
      Integrable
        (fun omega => 2 * eta * inner Real (residual omega) (x omega - xStar)) P :=
    hresidual_inner.const_mul (2 * eta)
  have horacle_scaled :
      Integrable (fun omega => eta ^ (2 : Nat) * ‖oracle omega‖ ^ (2 : Nat)) P :=
    horacle_sq.const_mul (eta ^ (2 : Nat))
  have hfirst_sub :
      Integrable
        (fun omega =>
          ‖x omega - xStar‖ ^ (2 : Nat) -
            2 * eta * inner Real (target omega) (x omega - xStar)) P :=
    hx_sq.sub htarget_scaled
  calc
    (∫ omega, ‖xNext omega - xStar‖ ^ (2 : Nat) ∂P) =
        ∫ omega,
          ‖x omega - xStar‖ ^ (2 : Nat) -
            2 * eta * inner Real (target omega) (x omega - xStar) -
            2 * eta * inner Real (residual omega) (x omega - xStar) +
            eta ^ (2 : Nat) * ‖oracle omega‖ ^ (2 : Nat) ∂P :=
      integral_congr_ae hpoint
    _ =
        (∫ omega,
          (‖x omega - xStar‖ ^ (2 : Nat) -
              2 * eta * inner Real (target omega) (x omega - xStar)) -
            2 * eta * inner Real (residual omega) (x omega - xStar) ∂P) +
          ∫ omega, eta ^ (2 : Nat) * ‖oracle omega‖ ^ (2 : Nat) ∂P := by
      exact integral_add (hfirst_sub.sub hresidual_scaled) horacle_scaled
    _ =
      (∫ omega, ‖x omega - xStar‖ ^ (2 : Nat) ∂P) -
        2 * eta * (∫ omega, inner Real (target omega) (x omega - xStar) ∂P) -
        2 * eta * (∫ omega, inner Real (residual omega) (x omega - xStar) ∂P) +
        eta ^ (2 : Nat) * (∫ omega, ‖oracle omega‖ ^ (2 : Nat) ∂P) := by
      rw [integral_sub hfirst_sub hresidual_scaled,
        integral_sub hx_sq htarget_scaled,
        integral_const_mul, integral_const_mul, integral_const_mul]
