import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Martingale
import SOptLib.Glue.Probability
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope
import SOptLib.Analysis.OpenCocoercivity

/-!
# Variance-Reduced Mirror Descent

Formalization of Lan's variance-reduced mirror descent method
for smooth finite-sum composite optimization from Section 5.3 of
*First-Order and Stochastic Optimization Methods for Machine Learning*.

The file packages the finite-sum objective, the sampling distribution, the
distance-generating function, and the multi-epoch variance-reduced recursion
into `VarianceReducedMirrorDescentSetup`. It then derives the finite-sum
gradient, composite objective, Bregman distance, canonical prox update, epoch
process, variance-reduced estimator and noise term, weighted snapshot/output
averages, and declares the full lemma chain together with the two final
corollaries. This repaired version adds convexity of each intrinsic component
gradient image on the relative interior of the feasible set. The open-chart
Baillon--Haddad theorem and the gradient-image bridge are proved in the imported
analysis modules; the false unrestricted carrier bridge is not used.
-/

open MeasureTheory ProbabilityTheory
open Topology
open SOptLib
open scoped InnerProductSpace
open scoped BigOperators

/-- Local compatibility bridge for independence of a past-measurable random variable
and a fresh sample.

Reuse audit: `SOptLib/Glue/Probability.lean` contains
`indepFun_of_past_measurable_current_iid_sample`, but the fresh verifier for this
target does not expose that imported root name.  This local wrapper is the same
Mathlib independence API bridge, not a new stochastic assumption. -/
private theorem vrmd_indepFun_of_past_measurable_current_iid_sample
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {μ : Measure Ω} {past : MeasurableSpace Ω} {X : Ω → W} {Y : Ω → S}
    (hX_past : Measurable[past] X)
    (h_past_indep_current :
      Indep past (MeasurableSpace.comap Y (by infer_instance : MeasurableSpace S)) μ) :
    IndepFun X Y μ := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left h_past_indep_current hX_past.comap_le

/-- Local compatibility bridge for bounded real observables on finite measures.

Reuse audit: `SOptLib/Glue/Probability.lean` contains
`integrable_of_measurable_bounded_real`, but the fresh verifier for this target
does not expose that imported root name.  This local wrapper repeats the same
bounded-integrability proof. -/
private theorem vrmd_integrable_of_measurable_bounded_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ} (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    Integrable Z μ := by
  exact Integrable.of_bound hZ.aestronglyMeasurable C (ae_of_all μ hC)


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Core finite maximum in Lan's sampling constant
`L_Q = (1 / m) max_i L_i / q_i`.

This helper exists so the setup-level Algorithm 5.6 prox selector can state its
objective before the namespaced paper aliases are available. No SOptLib match:
searched "finite sum smoothness constant" and "importance sampling max";
`SOptLib/Model/Iterates.lean` has generic finite extrema but not this Eq.
(5.3.4) constant. -/
noncomputable def vrmdLQCore (Li q : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    (Finset.univ.image (fun i : ι => Li i / q i)).max' (by
      classical
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact ⟨Li i / q i, by simp⟩)

/-- Core Corollary 5.8 stepsize `γ = 1 / (16 L_Q)`, used in the setup-level
Algorithm 5.6 prox selector. -/
noncomputable def vrmdEtaCore (Li q : ι → ℝ) : ℝ :=
  (16 * vrmdLQCore Li q)⁻¹

/-- Intrinsic component-gradient realization on the feasible carrier.

The paper writes `∇ f_i(x)` only for feasible `x ∈ X`. Lean needs a total
ambient representative for `f_i`, but the gradient appearing in the paper's
carrier-smoothness statements is the intrinsic gradient on the affine span of
`X`, not the ambient gradient of an arbitrary extension. Reuse audit: searched
"carrier gradient" and checked `SOptLib.carrierGradient` /
`SOptLib.carrierGradientFrom`; `SOptLib.carrierGradient` is the canonical
affine-span chart gradient for a feasible base point, whose body bottoms out in
Mathlib `gradientWithin` on `(affineSpan ℝ X).direction`. -/
private noncomputable def vrmdComponentGradientCore
    (X : Set E) (f : ι → E → ℝ) (i : ι) (x : {x : E // x ∈ X}) : E :=
  SOptLib.carrierGradient X (fun y : {x : E // x ∈ X} => f i y.1) x


/-- Private core Bregman expression with the boundary-safe within-gradient realization.

This is the same canonical object later exposed as `VarianceReducedMirrorDescentSetup.V`. -/
private noncomputable def vrmdBregmanCore (X : Set E) (v : E → ℝ) (x z : E) : ℝ :=
  v z - v x - ⟪gradientWithin v X x, z - x⟫_ℝ

/-- Core literal Algorithm 5.6 prox objective
`γ [⟪G_t, x⟫ + h(x)] + V(x_t, x)`.

The public alias `proxObjective` unfolds to this core; the setup selector field
uses it because Algorithm 5.6 states the argmin update as part of the process
definition. -/
noncomputable def vrmdProxObjectiveCore
    (X : Set E) (h v : E → ℝ) (Li q : ι → ℝ) (x g z : E) : ℝ :=
  vrmdEtaCore Li q * (⟪g, z⟫_ℝ + h z) + vrmdBregmanCore X v x z

/-- Internal realization state for the recursive implementation of Algorithm 5.6.

The field `innerCarrier` is a Lean realization device: it is the unbounded
primitive-recursive carrier used to compute the finite paper iterates in one
epoch.  The public paper-facing epoch object below restricts this carrier to
`InnerStep s`, the finite window `t = 1, ..., T_s`. -/
structure VarianceReducedMirrorDescentInternalState (E : Type*) where
  xEpoch : E
  snapshot : E
  innerCarrier : ℕ → E

/-- Complete setup for variance-reduced mirror descent.

The structure stores the paper's primitive finite-dimensional model data and a
realization scaffold for the repeated random draws in Algorithm 5.6.  The paper
object `Q` is derived below as a finite PMF from the real masses `q`; the stream
`ξ` and its independence/law fields are the ambient probability-space realization
of the instruction "pick `i_t` according to `Q`", not additional optimization
assumptions.  The composite objective, Bregman distance, full finite-sum gradient,
sampling constants `L`/`L_Q`, Corollary 5.8 parameter choices, and mirror-prox
update are derived below as definitions. -/
structure VarianceReducedMirrorDescentSetup
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
  Quote: `X \subseteq \mathbb{R}^m \text{ closed convex}`. -/
  X : Set E
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/initialization/math`.
  Quote: `x^0 \in X, \; \tilde{x}^0 = x^0`. -/
  w₀ : E
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/0/parameters/0`.
  Quote: `L_i > 0`. -/
  Li : ι → ℝ
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/4/math`.
  Quote: `Q = \{q_1, \ldots, q_m\} \text{ probability distribution}`. -/
  q : ι → ℝ
  /-- Ambient differentiable extension of the component functions whose
  paper-facing restrictions to `X` are `componentOn` below.

  Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
  Quote: `f(x) = \frac{1}{m} \sum_{i=1}^{m} f_i(x)`. -/
  f : ι → E → ℝ
  /-- Ambient extension of the paper function `h : X → ℝ`; the canonical
  source-facing restriction is `hOn` below.

  Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
  Quote: `h : X \to \mathbb{R} \text{ simple convex (possibly nondifferentiable)}`. -/
  h : E → ℝ
  /-- Ambient extension of the paper distance-generating function `v : X → ℝ`;
  the canonical source-facing restriction is `vOn` below.

  Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/5/math`.
  Quote: `v : X \to \mathbb{R} \text{ continuously differentiable, 1-strongly convex}`. -/
  v : E → ℝ
  /-- Lean realization scaffold for the book instruction
  `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/1/math`.
  Quote: `Pick i_t ... randomly according to Q`. -/
  ξ : ℕ → Ω → ι
  /-- Ambient probability measure for realizing the repeated random draws from
  `Q`; this is Lean scaffolding for Algorithm 5.6, not an optimization
  assumption beyond the quoted sampling instruction. -/
  P : Measure Ω
  /-- Lean probability-space scaffold for Algorithm 5.6's repeated draws from
  `Q`; not a paper optimization assumption. -/
  hP : IsProbabilityMeasure P
  /-- Algorithm 5.6 mirror-descent prox update as process data.

  Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/2/math`.
  Quote: `x_{t+1} = \operatorname{argmin}_{x \in X} \left\{ \gamma [\langle G_t, x \rangle + h(x)] + V(x_t, x) \right\}`.

  This is not a derived lemma field: the algorithm itself defines the next
  iterate by selecting such an argmin. The public `proxStep` below projects this
  selector and exposes the minimization certificate via `proxStep_is_argmin`. -/
  proxMap :
    ∀ x g : E,
      {z : E //
        z ∈ X ∧
          ∀ y, y ∈ X →
            vrmdProxObjectiveCore X h v Li q x g z ≤
              vrmdProxObjectiveCore X h v Li q x g y}
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
  Quote: `X \subseteq \mathbb{R}^m \text{ closed convex}`. -/
  hX_closed : IsClosed X
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
  Quote: `X \subseteq \mathbb{R}^m \text{ closed convex}`. -/
  hX_convex : Convex ℝ X
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/initialization/math`.
  Quote: `x^0 \in X`. -/
  hw₀_mem : w₀ ∈ X
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/0/parameters/0`.
  Quote: `L_i > 0`. -/
  hLi_pos : ∀ i, 0 < Li i
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/4/math`.
  Quote: `Q = \{q_1, \ldots, q_m\} \text{ probability distribution}`. -/
  hq_pos : ∀ i, 0 < q i
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/4/math`.
  Quote: `Q = \{q_1, \ldots, q_m\} \text{ probability distribution}`. -/
  hq_sum : Finset.sum Finset.univ q = 1
  /-- Lean measurability scaffold for realizing Algorithm 5.6 random draws from
  the finite distribution `Q`. -/
  hξ_meas : ∀ n, Measurable (ξ n)
  /-- Lean independence scaffold for the repeated Algorithm 5.6 draws
  `Pick i_t ... randomly according to Q`. -/
  hξ_indep : iIndepFun (β := fun _ => ι) ξ P
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/1/math`.
  Quote: `Pick i_t ... randomly according to Q`. -/
  hξ_law : ∀ n i, P {ω | ξ n ω = i} = ENNReal.ofReal (q i)
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/3/math`.
  Quote: `h : X \to \mathbb{R} \text{ is convex}`. -/
  hh_convex : ConvexOn ℝ X h
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/1/math`.
  Quote: `f_i \text{ is convex on } X, \quad \forall i = 1, \ldots, m`. -/
  hcomponent_convex : ∀ i, ConvexOn ℝ X (f i)
  /-- Differentiability realization of the gradients appearing in
  `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/0/math`.
  Quote: `\|\nabla f_i(x) - \nabla f_i(y)\|_* \le L_i \|x - y\|`. -/
  hcomponent_differentiable : ∀ i, DifferentiableOn ℝ (f i) X
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/5/math`.
  Quote: `v : X \to \mathbb{R} \text{ continuously differentiable}`. -/
  hv_contDiff : ContDiffOn ℝ 1 v X
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/5/math`.
  Quote: `v ... 1-strongly convex w.r.t. \|\cdot\|`. -/
  hv_strongConvex : StrongConvexOn X 1 v
  /-- Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/0/math`.
  Quote: `\|\nabla f_i(x) - \nabla f_i(y)\|_* \le L_i \|x - y\|`. -/
  hcomponent_smooth :
    ∀ i (x y : E) (hx : x ∈ X) (hy : y ∈ X),
      SOptLib.dualNorm
          (vrmdComponentGradientCore X f i ⟨x, hx⟩ -
            vrmdComponentGradientCore X f i ⟨y, hy⟩) ≤
        Li i * ‖x - y‖

  /-- Additional assumption for the repaired theorem: the intrinsic component
  gradient image over the relative interior of X is convex. The open domain is
  derived from X in its affine span; no ambient openness assumption is imposed.
  Source: Wachsmuth--Wachsmuth (2022), Lemma 3.3. -/
  hcomponent_gradient_image_convex : ∀ i,
    Convex ℝ ((SOptLib.totalizeOn X (vrmdComponentGradientCore X f i)) ''
      intrinsicInterior ℝ X)

namespace VarianceReducedMirrorDescentSetup

variable (setup : VarianceReducedMirrorDescentSetup ι E Ω)


/-- The averaged component smoothness constant
`L = (1 / m) ∑ᵢ Lᵢ` from Section 5.3.

This local definition follows the paper's stated finite average. SOptLib has
smoothness bridge theorems such as `Convex.carrier_smooth_quadratic_upper_bound`,
but no canonical finite-sum constant; searched "Component smoothness" and
"finite sum smoothness constant", scanned `SOptLib/Glue/Calculus.lean`, and none
define the literal `L ≡ 1/m ∑ᵢ Lᵢ` object. -/
noncomputable def L : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ setup.Li


/-- Nonempty finite image of the component ratios `Lᵢ / qᵢ`, used to form
Lan's `max_i L_i / q_i`. -/
private theorem componentRatioImage_nonempty :
    (Finset.univ.image (fun i : ι => setup.Li i / setup.q i)).Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨setup.Li i / setup.q i, by simp⟩

/-- The importance-sampling smoothness constant
`L_Q = (1 / m) max_i L_i / q_i` from Eq. (5.3.4).

This local definition is the paper's literal finite maximum. Considered
`finiteRunMaxValue`, `le_finite_image_max`, and `finite_image_max_attained` from
`SOptLib/Model/Iterates.lean`; those are generic finite-run extrema, while this
object is the named Eq. (5.3.4) sampling constant depending on `L_i/q_i`. -/
noncomputable def LQ : ℝ :=
  vrmdLQCore setup.Li setup.q

/-- Corollary 5.8 step size `γ = 1 / (16 L_Q)`, named `η` in this file's
algorithm setup convention.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/0/math`.
Quote: `theta = 1, \; gamma = 1/(16 L_Q)`.

This is a paper-local closed-form parameter. No SOptLib match: checked the
pre-searched parameter-choice candidates in `SOptLib/Model/ParameterChoices.lean`;
they encode two-phase generic schedules, not Lan's Corollary 5.8 VRMD step size. -/
noncomputable def η : ℝ :=
  vrmdEtaCore setup.Li setup.q

/-- Corollary 5.8 constant inner weight `θ_t = 1`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/0/math`.
Quote: `theta = 1, \; gamma = 1/(16 L_Q)`.

No SOptLib match: searched the supplied candidates for `θ`; none define this
paper's constant inner-loop averaging weight. -/
def θ (_setup : VarianceReducedMirrorDescentSetup ι E Ω) (_t : ℕ) : ℝ :=
  1

/-- Corollary 5.8 epoch length schedule `T₁ = 7`, `T_s = 2 T_{s-1}` for
`s ≥ 2`, encoded by the closed form `7 * 2^(s-1)` for positive epochs.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/1/math`.
Quote: `T_s = 2 T_{s-1}, \; s = 2, 3, \ldots, \; T_1 = 7`.

The paper only has positive epochs. The value at `s = 0` is Lean-only
scaffolding for total recursive state initialization; public inner-step objects
below restrict back to `1 ≤ t ≤ T_s`. No SOptLib match: checked the listed
algebraic schedule helpers, which prove inequalities but do not define this
VRMD epoch-length schedule. -/
def T (_setup : VarianceReducedMirrorDescentSetup ι E Ω) (s : ℕ) : ℕ :=
  if s = 0 then 0 else 7 * 2 ^ (s - 1)

/-- Literal Eq. (5.3.14) formula for the epoch-output weight.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/2/math`.
Quote: `w_s := (1 - 4 L_Q gamma)(T_{s-1} - 1) - 4 L_Q gamma T_s > 0, s >= 2`.

No SOptLib match: searched "weighted output average" and checked
`_root_.SOptLib.weightedOutputAverage`; that primitive packages normalized averages but
does not define Lan's VRMD weight formula. -/
noncomputable def paperWeightFormula (s : ℕ) : ℝ :=
  (1 - 4 * setup.LQ * setup.η) * ((setup.T (s - 1) : ℝ) - 1) -
    4 * setup.LQ * setup.η * setup.T s

/-- Epoch-output weight used in the paper-facing average
`\bar{x}^S = (∑_{s=1}^S w_s \tilde{x}^s)/(∑_{s=1}^S w_s)`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/2/math`.
Quote: `w_s := (1 - 4 L_Q gamma)(T_{s-1} - 1) - 4 L_Q gamma T_s > 0, s >= 2`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/proof/4/description`.
Quote: `then w_s = \frac{1}{8} T_s - \frac{3}{4} \ge \frac{1}{56} T_s`.

The formula in Eq. (5.3.14) is stated only for `s >= 2`, while Eq. (5.3.16)
sums `s = 1..S`.  Under Corollary 5.8's fixed choices this closed-form bridge
is the paper's own proof-step convention for the output weights; the theorem
`w_eq_paperWeightFormula_of_two_le` records agreement with Eq. (5.3.14) on its
stated domain. No SOptLib match: searched "weighted output average" and checked
`_root_.SOptLib.weightedOutputAverage`; it normalizes supplied weights but does not
provide Lan's VRMD first-weight/index bridge. -/
noncomputable def w (s : ℕ) : ℝ :=
  if s = 0 then 0 else (1 / 8 : ℝ) * setup.T s - 3 / 4

/-- Defining equation for the Section 5.3 averaged smoothness constant. -/
theorem L_def :
    setup.L = (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ setup.Li := by
  rfl

/-- Positivity of the averaged smoothness constant `L`, derived from the stated
component positivity `L_i > 0`. -/
theorem L_pos : 0 < setup.L := by
  have hcardpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hsumpos : 0 < Finset.sum Finset.univ setup.Li := by
    exact Finset.sum_pos (fun i _ => setup.hLi_pos i) Finset.univ_nonempty
  rw [setup.L_def]
  exact mul_pos (inv_pos.mpr hcardpos) hsumpos


/-- Every sampled index has the finite law `Q`, making "pick `i_t` according
to `Q`" part of the object layer rather than a theorem-local assumption. -/
theorem sampledIndex_law (n : ℕ) (i : ι) :
    setup.P {ω | setup.ξ n ω = i} = ENNReal.ofReal (setup.q i) :=
  setup.hξ_law n i


/-- Bridge inequality following from the finite maximum definition of `L_Q`;
later proofs may use the old upper-bound shape without axiomatizing it. -/
theorem Li_le_card_mul_q_mul_LQ (i : ι) :
    setup.Li i ≤ (Fintype.card ι : ℝ) * setup.q i * setup.LQ := by
  classical
  let M :=
    (Finset.univ.image (fun j : ι => setup.Li j / setup.q j)).max'
      (componentRatioImage_nonempty setup)
  have hmax : setup.Li i / setup.q i ≤ M := by
    simpa [M] using
      (by
        exact Finset.le_max' _ (setup.Li i / setup.q i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hq : 0 < setup.q i := setup.hq_pos i
  have hmul : setup.Li i ≤ M * setup.q i := by
    exact (div_le_iff₀ hq).mp hmax
  have hcard_ne : ((Fintype.card ι : ℝ) ≠ 0) := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card ι))
  have hM : M = (Fintype.card ι : ℝ) * setup.LQ := by
    unfold LQ vrmdLQCore
    change M = (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ)⁻¹ * M)
    field_simp [hcard_ne]
  nlinarith [hmul]

/-- Corollary 5.8 parameter equation `γ = 1/(16 L_Q)`. -/
theorem eta_corollary_5_8 : setup.η = (16 * setup.LQ)⁻¹ := by
  rfl

/-- Positivity of the importance-sampling smoothness constant `L_Q`, derived from
the stated positivity of `L_i` and `q_i`. -/
theorem LQ_pos : 0 < setup.LQ := by
  classical
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let M :=
    (Finset.univ.image (fun i : ι => setup.Li i / setup.q i)).max'
      (componentRatioImage_nonempty setup)
  have hratio : 0 < setup.Li i0 / setup.q i0 :=
    div_pos (setup.hLi_pos i0) (setup.hq_pos i0)
  have hle : setup.Li i0 / setup.q i0 ≤ M := by
    simpa [M] using
      (by
        exact Finset.le_max' _ (setup.Li i0 / setup.q i0) (Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩))
  have hMpos : 0 < M := lt_of_lt_of_le hratio hle
  have hcardpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  dsimp [LQ, vrmdLQCore]
  exact mul_pos (inv_pos.mpr hcardpos) hMpos

/-- Positivity of Corollary 5.8's step size `γ = 1/(16 L_Q)`. -/
theorem eta_pos : 0 < setup.η := by
  rw [eta_corollary_5_8]
  exact inv_pos.mpr (mul_pos (by norm_num) setup.LQ_pos)

/-- The averaged component smoothness constant is bounded by the
importance-sampling constant `L_Q`.

This is the finite-sum algebra behind using Lemma 5.14 inside Theorem 5.6:
from `L_i ≤ m q_i L_Q` and `∑ᵢ q_i = 1`, summing gives `L ≤ L_Q`. -/
theorem L_le_LQ : setup.L ≤ setup.LQ := by
  classical
  let m : ℝ := Fintype.card ι
  have hm_pos : 0 < m := by
    simpa [m] using
      (show 0 < (Fintype.card ι : ℝ) by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι))
  have hsum_le :
      Finset.sum Finset.univ setup.Li ≤
        Finset.sum Finset.univ (fun i : ι => m * setup.q i * setup.LQ) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    simpa [m, mul_assoc] using setup.Li_le_card_mul_q_mul_LQ i
  have hsum_rhs :
      Finset.sum Finset.univ (fun i : ι => m * setup.q i * setup.LQ) =
        m * setup.LQ := by
    calc
      Finset.sum Finset.univ (fun i : ι => m * setup.q i * setup.LQ) =
          (Finset.sum Finset.univ (fun i : ι => m * setup.q i)) * setup.LQ := by
            rw [Finset.sum_mul]
      _ =
          m * (Finset.sum Finset.univ setup.q) * setup.LQ := by
            rw [Finset.mul_sum]
      _ = m * setup.LQ := by
            rw [setup.hq_sum]
            ring
  have hscaled :
      m⁻¹ * Finset.sum Finset.univ setup.Li ≤ m⁻¹ * (m * setup.LQ) := by
    exact mul_le_mul_of_nonneg_left (by simpa [hsum_rhs] using hsum_le)
      (inv_nonneg.mpr (le_of_lt hm_pos))
  rw [setup.L_def]
  calc
    m⁻¹ * Finset.sum Finset.univ setup.Li ≤ m⁻¹ * (m * setup.LQ) := hscaled
    _ = setup.LQ := by
      field_simp [ne_of_gt hm_pos]

/-- Corollary 5.8's stepsize satisfies the smoothness side-condition in
Lemma 5.14. -/
theorem L_eta_le_half : setup.L * setup.η ≤ 1 / 2 := by
  have hη_nonneg : 0 ≤ setup.η := le_of_lt setup.eta_pos
  have hmain : setup.L * setup.η ≤ setup.LQ * setup.η :=
    mul_le_mul_of_nonneg_right setup.L_le_LQ hη_nonneg
  have hLQη : setup.LQ * setup.η = (1 / 16 : ℝ) := by
    rw [setup.eta_corollary_5_8]
    field_simp [ne_of_gt setup.LQ_pos]
  nlinarith

/-- Corollary 5.8 parameter equation `θ_t = 1`. -/
theorem theta_corollary_5_8 (t : ℕ) : setup.θ t = 1 := by
  rfl

/-- Eq. (5.3.17) initial epoch length `T₁ = 7`. -/
theorem T_one_corollary_5_8 : setup.T 1 = 7 := by
  simp [T]

/-- Eq. (5.3.17) recurrence `T_s = 2 T_{s-1}` for `s ≥ 2`. -/
theorem T_rec_corollary_5_8 (s : ℕ) (hs : 2 ≤ s) :
    setup.T s = 2 * setup.T (s - 1) := by
  classical
  have hs0 : s ≠ 0 := by
    intro h
    omega
  have hlt : 1 < s := by
    exact lt_of_lt_of_le (by norm_num : 1 < 2) hs
  have hsm10 : s - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hlt
  have hpow : 2 ^ (s - 1) = 2 * 2 ^ ((s - 1) - 1) := by
    have h : s - 1 = ((s - 1) - 1) + 1 := by omega
    calc
      2 ^ (s - 1) = 2 ^ (((s - 1) - 1) + 1) := by
        exact congrArg (fun n : ℕ => 2 ^ n) h
      _ = 2 ^ ((s - 1) - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ ((s - 1) - 1) := by ring
  simp [T, hs0, hsm10, hpow, Nat.mul_assoc, Nat.mul_comm]

/-- Eq. (5.3.14) epoch-output weight formula for `s ≥ 2`. -/
theorem w_corollary_5_8 (s : ℕ) (hs : 2 ≤ s) :
    setup.w s =
      (1 - 4 * setup.LQ * setup.η) * ((setup.T (s - 1) : ℝ) - 1) -
        4 * setup.LQ * setup.η * setup.T s := by
  classical
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let M :=
    (Finset.univ.image (fun i : ι => setup.Li i / setup.q i)).max'
      (componentRatioImage_nonempty setup)
  have hratio : 0 < setup.Li i0 / setup.q i0 :=
    div_pos (setup.hLi_pos i0) (setup.hq_pos i0)
  have hle : setup.Li i0 / setup.q i0 ≤ M := by
    simpa [M] using
      (by
        exact Finset.le_max' _ (setup.Li i0 / setup.q i0) (Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩))
  have hMpos : 0 < M := lt_of_lt_of_le hratio hle
  have hcardpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hLQpos : 0 < setup.LQ := by
    dsimp [LQ]
    exact mul_pos (inv_pos.mpr hcardpos) hMpos
  have hquarter : 4 * setup.LQ * setup.η = (1 / 4 : ℝ) := by
    rw [eta_corollary_5_8]
    field_simp [ne_of_gt hLQpos]
    ring
  have hs0 : s ≠ 0 := by omega
  have hT : (setup.T s : ℝ) = 2 * (setup.T (s - 1) : ℝ) := by
    exact_mod_cast setup.T_rec_corollary_5_8 s hs
  simp [w, hs0, hquarter]
  nlinarith [hT]


/-- Corollary 5.8's proof supplies the first output weight used by
Eq. (5.3.16), avoiding a shifted public output. -/
theorem w_one_corollary_5_8 : setup.w 1 = (1 / 8 : ℝ) := by
  norm_num [w, T]


/-- The Corollary 5.8 step-size choice entails `4 L_Q γ ≤ 1`; this is a
derived parameter fact, not a setup assumption. -/
theorem four_LQ_eta_le_one : 4 * setup.LQ * setup.η ≤ 1 := by
  classical
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let M :=
    (Finset.univ.image (fun i : ι => setup.Li i / setup.q i)).max'
      (componentRatioImage_nonempty setup)
  have hratio : 0 < setup.Li i0 / setup.q i0 :=
    div_pos (setup.hLi_pos i0) (setup.hq_pos i0)
  have hle : setup.Li i0 / setup.q i0 ≤ M := by
    simpa [M] using
      (by
        exact Finset.le_max' _ (setup.Li i0 / setup.q i0) (Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩))
  have hMpos : 0 < M := lt_of_lt_of_le hratio hle
  have hcardpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hLQpos : 0 < setup.LQ := by
    dsimp [LQ]
    exact mul_pos (inv_pos.mpr hcardpos) hMpos
  have hquarter : 4 * setup.LQ * setup.η = (1 / 4 : ℝ) := by
    rw [eta_corollary_5_8]
    field_simp [ne_of_gt hLQpos]
    ring
  rw [hquarter]
  norm_num

/-- Positivity of the Eq. (5.3.14) weights under the Corollary 5.8 choices. -/
theorem w_pos_corollary_5_8 (s : ℕ) (hs : 2 ≤ s) : 0 < setup.w s := by
  have hs0 : s ≠ 0 := by omega
  have hsm1 : 1 ≤ s - 1 := by omega
  have hpow : 2 ≤ 2 ^ (s - 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s - 1) := by
        exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hsm1
  have hTnat : 14 ≤ setup.T s := by
    simp [T, hs0]
    nlinarith [hpow]
  have hTge : (14 : ℝ) ≤ setup.T s := by
    exact_mod_cast hTnat
  simp [w, hs0]
  nlinarith

/-- The averaged smooth finite-sum part `f(x) = (1 / m) ∑ᵢ fᵢ(x)`.

This is local because no SOptLib match was found for a deterministic finite-sum
objective: searched "finite sum objective" and scanned `SOptLib/Model/Objective.lean`;
`objectiveKernel` is stochastic-kernel oriented, while Eq. (5.3.1) is the literal
finite average. -/
noncomputable def fAvg (x : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)

/-- Paper-facing component function `f_i : X → ℝ`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
Quote: `f(x) = \frac{1}{m} \sum_{i=1}^{m} f_i(x)`.

The setup fields `f i : E → ℝ` are ambient differentiable extensions used to
form gradients; this restriction is the object whose domain matches the book's
closed convex feasible set.  No SOptLib match: checked `objectiveKernel` and
`objectiveExpectation` in `SOptLib/Model/Objective.lean`; they model stochastic
objectives rather than deterministic component restrictions to a carrier
subtype. -/
noncomputable def componentOn (i : ι) : {x : E // x ∈ setup.X} → ℝ :=
  fun x => setup.f i x.1

/-- Paper-facing finite-sum objective `f : X → ℝ`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
Quote: `f(x) = \frac{1}{m} \sum_{i=1}^{m} f_i(x)`.

Reuse audit: `SOptLib.objectiveKernel` and `SOptLib.objectiveExpectation`
encode stochastic objective kernels, while `SOptLib.compositeObjective` only
adds two already-formed objectives; the paper object here is the deterministic
finite average of component functions restricted to the feasible carrier. -/
noncomputable def fOn : {x : E // x ∈ setup.X} → ℝ :=
  fun x => setup.fAvg x.1

/-- Paper-facing nonsmooth term `h : X → ℝ`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/variable_space/math`.
Quote: `h : X \to \mathbb{R} \text{ simple convex (possibly nondifferentiable)}`.

Reuse audit: no SOptLib objective primitive constructs this paper datum from a
carrier-domain nonsmooth function; `SOptLib.compositeObjective` is reused below
only after the separate `h : X → ℝ` object has been named. -/
noncomputable def hOn : {x : E // x ∈ setup.X} → ℝ :=
  fun x => setup.h x.1

/-- Paper-facing distance-generating function `v : X → ℝ`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/5/math`.
Quote: `v : X \to \mathbb{R} \text{ continuously differentiable, 1-strongly convex w.r.t. } \|\cdot\|`.

Reuse audit: `bregmanDivergence` consumes an ambient differentiable
representative to form the Bregman expression, but the paper's primitive
potential is carrier-domain `v : X → ℝ`; this definition names that restricted
object and leaves the ambient field as its differentiability realization. -/
noncomputable def vOn : {x : E // x ∈ setup.X} → ℝ :=
  fun x => setup.v x.1

/-- Paper-facing component gradient `∇fᵢ(x)` on the feasible carrier.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/0/math`.
Quote: `\|\nabla f_i(x) - \nabla f_i(y)\|_* \le L_i \|x - y\|, \quad \forall x, y \in X`.

This is the canonical carrier-gradient object from `SOptLib.Model.Carrier`,
specialized to the component restriction `componentOn`.  The ambient
`componentGrad` below is only its totalization outside the paper domain `X`;
the realization contract for that ambient selector exposes this carrier-domain
object as the partial paper object. -/
noncomputable def componentGradOn (i : ι) (x : {x : E // x ∈ setup.X}) : E :=
  SOptLib.carrierGradient setup.X (setup.componentOn i) x


/-- Totalized component gradient used by ambient recursive process formulas.

On feasible points this is exactly `componentGradOn`; off `X` it is the standard
Lean totalization of a paper object whose source domain is the carrier.  In the
partial-function-totalization realization contract, `componentGradOn` is the
internal partial object and this declaration is the ambient wrapper. -/
noncomputable def componentGrad
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) (i : ι) (x : E) : E :=
  SOptLib.totalizeOn setup.X (setup.componentGradOn i) x

/-- The full finite-sum gradient `∇f(x) = (1 / m) ∑ᵢ ∇fᵢ(x)`, totalized off
the feasible carrier. -/
noncomputable def gradF
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) (x : E) : E :=
  (Fintype.card ι : ℝ)⁻¹ •
    Finset.sum Finset.univ (fun i => setup.componentGrad i x)


/-- Internal ambient realization of the composite objective `Ψ(x) = f(x) + h(x)`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/problem/math`.
Quote: `\min_{x \in X} \left\{ \Psi(x) := f(x) + h(x) \right\}`.

This is aligned with `_root_.compositeObjectiveAmbient` for the paper's
ambient finite-sum objective `fAvg`.  Source-facing statements use the
carrier-domain object `PsiOn`; this ambient helper is retained for proof
bridges and differentiability/prox realization over `E`. -/
noncomputable def Psi (x : E) : ℝ :=
  setup.fAvg x + setup.h x

/-- Private boundary-safe extension of the paper gradient `∇v(x)` on `X`.

The paper writes the Bregman formula with `∇v(x)`.  In Lean the feasible point
may lie on the boundary of `X`, so the total ambient realization uses Mathlib's
within-gradient on the stated carrier; the public `literalV` and bridge theorem
below recover the ordinary gradient formula on `interior X`. -/
private noncomputable def vGradExtension (x : E) : E :=
  gradientWithin setup.v setup.X x

/-- Carrier-domain gradient selector for the distance-generating function.

It is the subtype form of the boundary-safe `gradientWithin` extension used by
the ambient Bregman realization.  The paper's literal ordinary-gradient formula
is still exposed by `literalV` and `vGradExtension_eq_literal_of_interior`.
This is a public carrier object, not an internal totalization witness for the
ambient `V` realization contract. -/
noncomputable def vGradOn (x : {x : E // x ∈ setup.X}) : E :=
  vGradExtension setup x.1

/-- Internal ambient Bregman realization used by the public `V`.

This is the boundary-safe total form of the paper formula: it uses
`vGradExtension`, whose body is Mathlib `gradientWithin`, and is bridged below
to `literalV` on interior base points. -/
private noncomputable def extendedV (x z : E) : ℝ :=
  setup.v z - setup.v x - ⟪vGradExtension setup x, z - x⟫_ℝ

/-- Internal ambient realization of the Bregman distance generated by `v`, using
the boundary-safe within-gradient extension of the paper's `∇v(x)`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/3/math`.
Quote: `V(x, z) = v(z) - [v(x) + \langle \nabla v(x), z - x \rangle] \text{ (Bregman divergence)}`.

The local definition follows the accepted boundary-safe realization pattern:
`gradientWithin` is used only for the total ambient object, while `literalV`
below records the ordinary paper formula on interior base points. -/
noncomputable def V (x z : E) : ℝ :=
  extendedV setup x z


/-- Carrier-domain composite objective `Ψ : X → ℝ` from Eq. (5.3.1).

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/setup/problem/math`.
Quote: `\min_{x \in X} \left\{ \Psi(x) := f(x) + h(x) \right\}`.

Reuse audit: this directly specializes `SOptLib.compositeObjective` to the
carrier-restricted finite-sum objective `fOn` and nonsmooth term `hOn`; the
ambient `_root_.compositeObjectiveAmbient` is retained only as `Psi`, a
feasible-point bridge for proof work. -/
noncomputable def PsiOn : {x : E // x ∈ setup.X} → ℝ :=
  SOptLib.compositeObjective setup.fOn setup.hOn

/-- Carrier-domain Bregman divergence generated by `v : X → ℝ`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/assumptions/5/math`.
Quote: `V(x, z) = v(z) - [v(x) + \langle \nabla v(x), z - x \rangle]`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/3/math`.
Quote: `V(x, z) = v(z) - [v(x) + \langle \nabla v(x), z - x \rangle] \text{ (Bregman divergence)}`.

Reuse audit: this is the canonical carrier Bregman object from
`SOptLib.Model.Bregman`, specialized to the paper potential and boundary-safe
carrier gradient.  The ambient `V` is retained only as the totalized bridge used
by recursive process formulas. -/
noncomputable def VOn (x z : {x : E // x ∈ setup.X}) : ℝ :=
  _root_.carrierBregmanDivergence setup.vOn setup.vGradOn x z


/-- Coercion bridge for the paper finite-sum objective on `X`. -/
theorem fOn_coe (x : {x : E // x ∈ setup.X}) :
    setup.fOn x = setup.fAvg x.1 := by
  rfl

/-- Coercion bridge for the paper nonsmooth term on `X`. -/
theorem hOn_coe (x : {x : E // x ∈ setup.X}) :
    setup.hOn x = setup.h x.1 := by
  rfl


/-- The carrier-domain component gradient agrees with the original core
realization used by setup-level assumptions. -/
theorem componentGradOn_eq_core (i : ι) (x : {x : E // x ∈ setup.X}) :
    setup.componentGradOn i x =
      vrmdComponentGradientCore setup.X setup.f i x := by
  rfl


/-- Coercion bridge from the carrier-domain composite objective to the ambient
extension used by proof statements. -/
theorem PsiOn_coe (x : {x : E // x ∈ setup.X}) :
    setup.PsiOn x = setup.Psi x.1 := by
  simp [PsiOn, Psi, fOn, hOn, SOptLib.compositeObjective]

/-- Coercion bridge from the carrier-domain Bregman divergence to the ambient
extension used by proof statements. -/
theorem VOn_coe (x z : {x : E // x ∈ setup.X}) :
    setup.VOn x z = setup.V x.1 z.1 := by
  simp [VOn, V, extendedV, _root_.carrierBregmanDivergence,
    vOn, vGradOn, vGradExtension]


/-- Defining equation for the finite-sum gradient. -/
theorem gradF_def (x : E) :
    setup.gradF x =
      (Fintype.card ι : ℝ)⁻¹ •
        Finset.sum Finset.univ (fun i => setup.componentGrad i x) := by
  rfl

/-- On feasible points, the total component-gradient selector is the canonical
within-gradient on `X`. -/
theorem componentGrad_of_mem (i : ι) {x : E} (hx : x ∈ setup.X) :
    setup.componentGrad i x =
      vrmdComponentGradientCore setup.X setup.f i ⟨x, hx⟩ := by
  rw [componentGrad, SOptLib.totalizeOn_of_mem setup.X (setup.componentGradOn i) hx]
  exact setup.componentGradOn_eq_core i ⟨x, hx⟩


/-- Pair the canonical carrier gradient with any affine-span direction as the
ambient within-derivative of the representative, in the early setup namespace.

This is the differentiable-on chart bridge needed to align the paper's ordinary
interior gradient notation with `SOptLib.carrierGradient`.  Considered
`SOptLib.carrierGradientFrom_eq_gradient_of_mem_interior`, which requires
`ContDiffOn`, and the later local
`carrierGradient_inner_eq_fderivWithin_on_affine_direction`, which is not in
scope at this setup-side bridge; this copy uses only the available
`DifferentiableOn` hypothesis. -/
private theorem component_carrierGradient_inner_eq_fderivWithin_on_affine_direction
    {X : Set E} (F : E → ℝ) (f : {x : E // x ∈ X} → ℝ)
    (hX : Convex ℝ X)
    (hdiff : DifferentiableOn ℝ F X)
    (hf : ∀ y : {x : E // x ∈ X}, f y = F y.1)
    (x : {x : E // x ∈ X}) (du : (affineSpan ℝ X).direction) :
    ⟪SOptLib.carrierGradient X f x, (du : E)⟫_ℝ =
      (fderivWithin ℝ F X x.1) (du : E) := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨x.1, subset_affineSpan ℝ X x.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := SOptLib.carrierChartSet X x
  let cf : A.direction → ℝ := SOptLib.carrierChartFunction X f x
  let u : A.direction := SOptLib.carrierChartPoint X x x
  let Lchart : A.direction →ᴬ[ℝ] E := SOptLib.carrierChartToAmbient X x
  have hu : u ∈ T := by
    simpa [A, T, u] using SOptLib.carrierChartPoint_mem X x x
  have huniq : UniqueDiffWithinAt ℝ T u := by
    exact (SOptLib.carrierChartSet_uniqueDiffOn X x hX) u hu
  have hLu : Lchart u = x.1 := by
    simpa [A, Lchart, u] using SOptLib.carrierChartToAmbient_chartPoint X x x
  have hFdiff : DifferentiableWithinAt ℝ F X (Lchart u) := by
    rw [hLu]
    exact hdiff x.1 x.2
  have hLhas : HasFDerivWithinAt (fun y : A.direction => Lchart y) Lchart.contLinear T u := by
    rw [Lchart.decomp]
    exact Lchart.contLinear.hasFDerivWithinAt.add_const (Lchart 0)
  have hLdiff : DifferentiableWithinAt ℝ (fun y : A.direction => Lchart y) T u :=
    hLhas.differentiableWithinAt
  have hmap : Set.MapsTo (fun y : A.direction => Lchart y) T X := by
    intro y hy
    simpa [A, T, Lchart, SOptLib.carrierChartSet] using hy
  have hcongr : Set.EqOn cf (fun y : A.direction => F (Lchart y)) T := by
    intro y hy
    have hyX : Lchart y ∈ X := hmap hy
    calc
      cf y = SOptLib.totalizeOn X f (Lchart y) := rfl
      _ = f ⟨Lchart y, hyX⟩ := by
          exact SOptLib.totalizeOn_of_mem X f hyX
      _ = F (Lchart y) := by
          rw [hf]
  have hleft_congr :
      fderivWithin ℝ cf T u =
        fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u := by
    exact fderivWithin_congr' hcongr hu
  have hcomp :
      fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u =
        (fderivWithin ℝ F X (Lchart u)).comp
          (fderivWithin ℝ (fun y : A.direction => Lchart y) T u) := by
    exact fderivWithin_comp' (x := u) hFdiff hLdiff hmap huniq
  have hLder :
      fderivWithin ℝ (fun y : A.direction => Lchart y) T u = Lchart.contLinear := by
    exact hLhas.fderivWithin huniq
  have hLlin : Lchart.contLinear du = Lchart du - Lchart 0 := by
    simpa [vsub_eq_sub] using Lchart.contLinear_map_vsub du 0
  have hLdu_apply : Lchart du = (du : E) + x.1 := by
    let a : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        du : A) : E) = (du : E) + x.1
    simp [a]
  have hLzero : Lchart 0 = x.1 := by
    let a : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        (0 : A.direction) : A) : E) = x.1
    simp [a]
  have hLdu : Lchart.contLinear du = (du : E) := by
    rw [hLlin, hLdu_apply, hLzero]
    simp
  have hchart :
      (fderivWithin ℝ cf T u) du =
        (fderivWithin ℝ F X x.1) (du : E) := by
    calc
      (fderivWithin ℝ cf T u) du
          = (fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u) du := by
              rw [hleft_congr]
      _ = ((fderivWithin ℝ F X (Lchart u)).comp
            (fderivWithin ℝ (fun y : A.direction => Lchart y) T u)) du := by
              rw [hcomp]
      _ = (fderivWithin ℝ F X x.1) (du : E) := by
              rw [hLder]
              simp [ContinuousLinearMap.comp_apply, hLdu, hLu]
  have hcompInst : CompleteSpace A.direction := instComplete
  calc
    ⟪SOptLib.carrierGradient X f x, (du : E)⟫_ℝ
        = (fderivWithin ℝ cf T u) du := by
          unfold SOptLib.carrierGradient SOptLib.carrierGradientFrom
          change
            ⟪((@gradientWithin ℝ A.direction _ _ _ hcompInst cf T u : A.direction) : E),
              (du : E)⟫_ℝ =
              (fderivWithin ℝ cf T u) du
          rw [← A.direction.coe_inner
            (@gradientWithin ℝ A.direction _ _ _ hcompInst cf T u) du]
          simp [gradientWithin]
          rfl
    _ = (fderivWithin ℝ F X x.1) (du : E) := hchart


/-- The finite average is convex on the feasible carrier.

This aligns with Lan Eq. (5.3.2) at `μ = 0`: the displayed convexity of `f`
is derived here from the source assumption that each component `f_i` is convex
on `X`.  Considered `Convex.normalized_weighted_sum_mem`,
`weightedExpectedStationarity`, `weightedExpectedExactStationarity`,
`weighted_variance_sum_expectation_bound`, and the telescope helpers; they
concern point membership, stationarity/oracle averages, or convergence sums, not
ConvexOn of the deterministic finite average from Eq. (5.3.1). -/
private theorem fAvg_convexOn_from_components
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) :
    ConvexOn ℝ setup.X setup.fAvg := by
  classical
  change ConvexOn ℝ setup.X
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
  have hsum_all : ∀ s : Finset ι,
      ConvexOn ℝ setup.X (fun x => Finset.sum s (fun i => setup.f i x)) := by
    intro s
    refine Finset.induction_on s ?hbase ?hstep
    · simpa using
        (convexOn_const (𝕜 := ℝ) (s := setup.X) (E := E) (0 : ℝ)
          setup.hX_convex)
    · intro a s ha hs
      have hfa : ConvexOn ℝ setup.X (setup.f a) := setup.hcomponent_convex a
      have hadd :
          ConvexOn ℝ setup.X
            ((fun x => setup.f a x) + fun x => Finset.sum s (fun i => setup.f i x)) :=
        hfa.add hs
      simpa [Finset.sum_insert, ha, Pi.add_apply] using hadd
  have hsum : ConvexOn ℝ setup.X
      (fun x => Finset.sum Finset.univ (fun i => setup.f i x)) :=
    hsum_all Finset.univ
  have hc : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by
    have hpos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    exact inv_nonneg.mpr (le_of_lt hpos)
  simpa [smul_eq_mul] using
    (ConvexOn.smul (𝕜 := ℝ) (s := setup.X)
      (f := fun x => Finset.sum Finset.univ (fun i => setup.f i x)) hc hsum)

/-- Segment derivative of the finite-sum smooth part at a feasible base point.

This is the declaration-order-safe copy needed for Lan Eq. (5.3.2): along the
feasible segment from `xStar` to `x`, the right derivative of the finite average
is the averaged carrier gradient paired with the segment direction.  Considered
`Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`, which consumes a
derivative but does not construct this finite-sum gradient identity; the later
local `fAvg_segment_hasDerivWithinAt_gradF` has exactly this shape but is not
available before `f_convex_mu0`. -/
private theorem fAvg_segment_hasDerivWithinAt_gradF_for_convexity
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X}) :
    HasDerivWithinAt
      (fun t : ℝ => setup.fAvg (xStar.1 + t • (x.1 - xStar.1)))
      ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  let d : E := x.1 - xStar.1
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => xStar.1 + t • d
  have hd_dir : d ∈ (affineSpan ℝ setup.X).direction := by
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ setup.X x.2)
      (subset_affineSpan ℝ setup.X xStar.2)
  have hline_eq : ∀ t : ℝ, line t = AffineMap.lineMap xStar.1 x.1 t := by
    intro t
    simp [line, d, AffineMap.lineMap_apply_module', add_comm, sub_eq_add_neg]
  have hmaps : Set.MapsTo line I setup.X := by
    intro t ht
    rw [hline_eq t]
    exact setup.hX_convex.lineMap_mem xStar.2 x.2 ht
  have hline_deriv : HasDerivWithinAt line d I 0 := by
    have hline_at : HasDerivAt (fun t : ℝ => xStar.1 + t • d) d 0 := by
      simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add xStar.1
    simpa [line] using hline_at.hasDerivWithinAt
  have hcomp : ∀ i : ι,
      HasDerivWithinAt (fun t : ℝ => setup.f i (line t))
        ⟪setup.componentGrad i xStar.1, d⟫_ℝ I 0 := by
    intro i
    have hF : HasFDerivWithinAt (setup.f i)
        (fderivWithin ℝ (setup.f i) setup.X xStar.1) setup.X xStar.1 :=
      (setup.hcomponent_differentiable i xStar.1 xStar.2).hasFDerivWithinAt
    have hchain : HasDerivWithinAt (fun t : ℝ => setup.f i (line t))
        ((fderivWithin ℝ (setup.f i) setup.X xStar.1) d) I 0 := by
      have h := hF.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line, d])
      simpa [line] using h
    have hcarrier : setup.componentGrad i xStar.1 =
        SOptLib.carrierGradient setup.X (setup.componentOn i) xStar := by
      simpa [VarianceReducedMirrorDescentSetup.componentOn,
        vrmdComponentGradientCore, SOptLib.carrierGradient] using
        VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i xStar.2
    let du : (affineSpan ℝ setup.X).direction := ⟨d, hd_dir⟩
    have hpair_carrier :=
      VarianceReducedMirrorDescentSetup.component_carrierGradient_inner_eq_fderivWithin_on_affine_direction
        (X := setup.X) (F := setup.f i) (f := setup.componentOn i)
        setup.hX_convex (setup.hcomponent_differentiable i) (by intro y; rfl) xStar du
    have hpair : (fderivWithin ℝ (setup.f i) setup.X xStar.1) d =
        ⟪setup.componentGrad i xStar.1, d⟫_ℝ := by
      simpa [du, hcarrier] using hpair_carrier.symm
    simpa [hpair] using hchain
  have hsum : HasDerivWithinAt
      (fun t : ℝ => Finset.sum Finset.univ (fun i : ι => setup.f i (line t)))
      (Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ))
      I 0 := by
    exact HasDerivWithinAt.fun_sum (fun i _hi => hcomp i)
  have havg : HasDerivWithinAt
      (fun t : ℝ => (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => setup.f i (line t)))
      ((Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ))
      I 0 := by
    simpa using hsum.const_mul (Fintype.card ι : ℝ)⁻¹
  have hgrad : ⟪setup.gradF xStar.1, d⟫_ℝ =
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ) := by
    simp [VarianceReducedMirrorDescentSetup.gradF_def, inner_smul_left, sum_inner]
  simpa [VarianceReducedMirrorDescentSetup.fAvg, line, d, I, hgrad] using havg

/-- Left-endpoint derivative/secant-slope comparison for a convex scalar function on `[0,1]`.

Reuse audit: pre-searched candidates listed no exported SOptLib/Mathlib wrapper for this exact
`HasDerivWithinAt`/`Icc 0 1` form; searched `convexOn slope derivative Icc endpoint`, inspected
`SOptLib/Glue/Calculus.lean` endpoint-minimum helpers, and imported Mathlib's concept-level
`ConvexOn.le_slope_of_hasDerivWithinAt`. This private shim aligns with Lan §5.3.2's one-dimensional
segment support inequality while keeping call sites independent of Mathlib API drift. -/
private theorem convexOn_Icc_hasDerivWithinAt_left_le_slope
    {φ : ℝ → ℝ} {D : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ)
    (hderiv : HasDerivWithinAt φ D (Set.Icc (0 : ℝ) 1) 0) :
    D ≤ slope φ 0 1 := by
  exact hconv.le_slope_of_hasDerivWithinAt
    (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hderiv


/-- Derived Eq. (5.3.2) first-order convexity bridge for the finite-sum
objective `f = (1/m)∑ᵢ fᵢ` on `X`.

This is no longer a setup field: the inequality is derived from the stated
component convexity/differentiability assumptions and the carrier-gradient
realization of `gradF`. -/
theorem f_convex_mu0 (x y : E) (hx : x ∈ setup.X) (hy : y ∈ setup.X) :
    setup.fAvg y ≥ setup.fAvg x + ⟪setup.gradF x, y - x⟫_ℝ := by
  classical
  let xX : {x : E // x ∈ setup.X} := ⟨x, hx⟩
  let yX : {x : E // x ∈ setup.X} := ⟨y, hy⟩
  let line : ℝ → E := fun t => AffineMap.lineMap x y t
  have hline_mem : Set.Icc (0 : ℝ) 1 ⊆ line ⁻¹' setup.X := by
    intro t ht
    exact setup.hX_convex.lineMap_mem hx hy ht
  have hφconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t => setup.fAvg (line t)) := by
    simpa [line] using
      ((fAvg_convexOn_from_components setup).comp_affineMap
        (AffineMap.lineMap x y)).subset hline_mem (convex_Icc 0 1)
  have hderiv : HasDerivWithinAt (fun t => setup.fAvg (line t))
      ⟪setup.gradF x, y - x⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [line, xX, yX, AffineMap.lineMap_apply_module', add_comm, sub_eq_add_neg]
      using fAvg_segment_hasDerivWithinAt_gradF_for_convexity setup yX xX
  have hslope := convexOn_Icc_hasDerivWithinAt_left_le_slope hφconv hderiv
  have hinner_le : ⟪setup.gradF x, y - x⟫_ℝ ≤ setup.fAvg y - setup.fAvg x := by
    simpa [line, slope_def_field] using hslope
  linarith


/-- Carrier-level Bregman three-point identity for the paper divergence `V`. -/
theorem VOn_three_point_identity
    (x z y : {x : E // x ∈ setup.X}) :
    setup.VOn x y =
      setup.VOn x z +
        ⟪setup.vGradOn z - setup.vGradOn x, y.1 - z.1⟫_ℝ +
          setup.VOn z y := by
  exact
    carrierBregmanDivergence_three_point_identity
      setup.vOn (fun u : {x : E // x ∈ setup.X} => (u.1 : E)) setup.vGradOn
      setup.VOn (by intro u v; rfl) x z y


/-- Boundary-safe Bregman nonnegativity with Mathlib's within-gradient.

Considered `bregmanDivergence_nonneg_of_convexOn` and
`bregmanDivergence_nonneg_of_strongConvexOn`; both are ambient-gradient
forms requiring `HasGradientAt` at the base point, while Lan's carrier-domain
assumption only gives differentiability within `X`, including boundary points. -/
private theorem bregman_core_nonneg_of_convexOn_differentiableOn
    {X : Set E} {v : E → ℝ} {x z : E}
    (hv : ConvexOn ℝ X v)
    (hdiff : DifferentiableOn ℝ v X)
    (hx : x ∈ X) (hz : z ∈ X) :
    0 ≤ v z - v x - ⟪gradientWithin v X x, z - x⟫_ℝ := by
  let line : ℝ → E := fun t => AffineMap.lineMap x z t
  have hline_mem : Set.Icc (0 : ℝ) 1 ⊆ line ⁻¹' X := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : 1 - t + t = 1 := by ring
    have hmem : (1 - t) • x + t • z ∈ X := hv.1 hx hz h1t ht0 hsum
    simpa [line, AffineMap.lineMap_apply_module] using hmem
  have hg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => v (line t)) := by
    simpa [line] using
      (hv.comp_affineMap (AffineMap.lineMap x z)).subset hline_mem (convex_Icc 0 1)
  have hmaps : Set.MapsTo line (Set.Icc (0 : ℝ) 1) X := by
    intro t ht
    exact hline_mem ht
  have hline_deriv :
      HasDerivWithinAt line (z - x) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [line] using
      (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := z)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hvdiff : DifferentiableWithinAt ℝ v X x := hdiff x hx
  have hg_deriv :
      HasDerivWithinAt (fun t => v (line t))
        ((fderivWithin ℝ v X x) (z - x)) (Set.Icc (0 : ℝ) 1) 0 :=
    hvdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line])
  have hslope :
      (fderivWithin ℝ v X x) (z - x) ≤
        slope (fun t => v (line t)) 0 1 := by
    exact convexOn_Icc_hasDerivWithinAt_left_le_slope hg_conv hg_deriv
  have hgrad_apply :
      (fderivWithin ℝ v X x) (z - x) =
        ⟪gradientWithin v X x, z - x⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hslope_expanded :
      ⟪gradientWithin v X x, z - x⟫_ℝ ≤ v z - v x := by
    rw [hgrad_apply] at hslope
    simpa [slope_def_field, line] using hslope
  linarith

/-- Nonnegativity of the Bregman distance generated by the stated
1-strongly-convex distance-generating function. -/
theorem V_nonneg (x z : E) (hx : x ∈ setup.X) (hz : z ∈ setup.X) :
    0 ≤ setup.V x z := by
  have hdiff : DifferentiableOn ℝ setup.v setup.X := by
    exact setup.hv_contDiff.differentiableOn (by norm_num)
  have hconv : ConvexOn ℝ setup.X setup.v := by
    have hv0 : StrongConvexOn setup.X 0 setup.v :=
      setup.hv_strongConvex.mono (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hv0
  simpa [V, extendedV] using
    bregman_core_nonneg_of_convexOn_differentiableOn hconv hdiff hx hz

/-- Literal Algorithm 5.6 prox objective minimized to produce `x_{t+1}`.

On feasible base and candidate points this is the positive stepsize multiple of
SOptLib's canonical carrier prox objective.  The literal ambient formula is kept
only as the Lean totalization outside the paper domain `X`. -/
noncomputable def proxObjective (x g z : E) : ℝ :=
  by
    classical
    exact
      if hx : x ∈ setup.X then
        if hz : z ∈ setup.X then
          setup.η *
            SOptLib.paperProxObjective
              (eval := fun u : {x : E // x ∈ setup.X} => (u.1 : E))
              (V := setup.VOn) (h := setup.hOn) ⟨x, hx⟩ g setup.η ⟨z, hz⟩
        else
          vrmdProxObjectiveCore setup.X setup.h setup.v setup.Li setup.q x g z
      else
        vrmdProxObjectiveCore setup.X setup.h setup.v setup.Li setup.q x g z

/-- The old literal ambient formula agrees with the SOptLib carrier prox
objective on the paper domain. -/
private theorem vrmdProxObjectiveCore_eq_eta_mul_paperProxObjective
    (x z : {x : E // x ∈ setup.X}) (g : E) :
    vrmdProxObjectiveCore setup.X setup.h setup.v setup.Li setup.q x.1 g z.1 =
      setup.η *
        SOptLib.paperProxObjective
          (eval := fun u : {x : E // x ∈ setup.X} => (u.1 : E))
          (V := setup.VOn) (h := setup.hOn) x g setup.η z := by
  have hη : setup.η ≠ 0 := ne_of_gt setup.eta_pos
  unfold vrmdProxObjectiveCore SOptLib.paperProxObjective hOn
  rw [show vrmdEtaCore setup.Li setup.q = setup.η by rfl]
  rw [show setup.VOn x z = vrmdBregmanCore setup.X setup.v x.1 z.1 by
    simpa [V, vrmdBregmanCore] using setup.VOn_coe x z]
  field_simp [hη]
  ring_nf

/-- Carrier-domain Algorithm 5.6 prox point.

The paper's prox update is defined for feasible base points `x ∈ X`; this
carrier object is the source-facing partial step.  The ambient `proxStep` below
is only the Lean totalization used by the recursive process. -/
noncomputable def proxPoint (x : {x : E // x ∈ setup.X}) (g : E) :
    {z : E // z ∈ setup.X} :=
  ⟨(setup.proxMap x.1 g).1, (setup.proxMap x.1 g).2.1⟩

/-- The literal Algorithm 5.6 objective is the positive step-size multiple of
SOptLib's canonical composite prox objective on the carrier. -/
theorem proxObjective_eq_eta_mul_paperProxObjective
    (x z : {x : E // x ∈ setup.X}) (g : E) :
    setup.proxObjective x.1 g z.1 =
      setup.η *
        SOptLib.paperProxObjective
          (eval := fun u : {x : E // x ∈ setup.X} => (u.1 : E))
          (V := setup.VOn) (h := setup.hOn) x g setup.η z := by
  simp [proxObjective, x.2, z.2]

/-- The carrier-domain prox point minimizes the literal Algorithm 5.6 objective
over feasible points. -/
theorem proxPoint_minimizes_literal (x : {x : E // x ∈ setup.X}) (g : E) :
    ∀ y : {x : E // x ∈ setup.X},
      setup.proxObjective x.1 g (setup.proxPoint x g).1 ≤
        setup.proxObjective x.1 g y.1 := by
  intro y
  have hmin := (setup.proxMap x.1 g).2.2 y.1 y.2
  change
    vrmdProxObjectiveCore setup.X setup.h setup.v setup.Li setup.q x.1 g
        (setup.proxPoint x g).1 ≤
      vrmdProxObjectiveCore setup.X setup.h setup.v setup.Li setup.q x.1 g y.1 at hmin
  rw [vrmdProxObjectiveCore_eq_eta_mul_paperProxObjective setup x (setup.proxPoint x g) g,
    vrmdProxObjectiveCore_eq_eta_mul_paperProxObjective setup x y g] at hmin
  simpa [setup.proxObjective_eq_eta_mul_paperProxObjective x (setup.proxPoint x g) g,
    setup.proxObjective_eq_eta_mul_paperProxObjective x y g] using hmin


/-- Ambient totalization of the canonical Algorithm 5.6 mirror-descent prox
point.

On feasible base points this is the carrier-domain SOptLib prox point above.
Away from `X`, where the paper does not define the update, the setup selector
provides a harmless total value that preserves the existing ambient bridge
theorems. -/
noncomputable def proxStep (x g : E) : E :=
  by
    classical
    exact
      if hx : x ∈ setup.X then
        (setup.proxPoint ⟨x, hx⟩ g).1
      else
        (setup.proxMap x g).1

/-- On feasible base points, the ambient totalization agrees with the
carrier-domain SOptLib prox point. -/
theorem proxStep_eq_proxPoint (x : {x : E // x ∈ setup.X}) (g : E) :
    setup.proxStep x.1 g = (setup.proxPoint x g).1 := by
  simp [proxStep, x.2]

/-- Feasibility of the canonical Algorithm 5.6 prox step. -/
theorem proxStep_mem (x g : E) :
    setup.proxStep x g ∈ setup.X := by
  by_cases hx : x ∈ setup.X
  · simpa [proxStep, hx, proxPoint] using (setup.proxMap x g).2.1
  · simpa [proxStep, hx] using (setup.proxMap x g).2.1


/-- Number of sampled component-gradient queries consumed by the first `s`
epochs. This lets one global IID sample process drive the whole multi-epoch
recursion. -/
noncomputable def epochOffset (s : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 s) setup.T

/-- Global sample index used at inner step `t` of epoch `s + 1`. -/
noncomputable def sampleIndex (s t : ℕ) : ℕ :=
  setup.epochOffset s + t

/-- Variance-reduced estimator from Algorithm 5.6.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/1/math`.
Quote: `G_t = \frac{\nabla f_{i_t}(x_t) - \nabla f_{i_t}(\tilde{x})}{q_{i_t} m} + \tilde{g}`.

Considered `SOptLib.sampledOracleProcess`, `SOptLib.stagedOracleValue`, and
`SOptLib.empiricalOracleAverage`; those model generic oracle evaluation or
averaging, while this paper needs the SVRG finite-sum correction with
`q_i m` in the denominator and `\tilde{g} = \nabla f(\tilde{x})`. -/
noncomputable def estimator (xTilde x : E) (i : ι) : E :=
  (((Fintype.card ι : ℝ) * setup.q i)⁻¹) •
      (setup.componentGrad i x - setup.componentGrad i xTilde) +
    setup.gradF xTilde

/-- Noise term `δ_t = G_t - ∇f(x_t)` attached to the VR estimator.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/parameters/4/math`.
Quote: `\delta_t := G_t - \nabla f(x_t)`.

Considered `SOptLib.centeredStagedOracleValue` and
`SOptLib.centeredMiniBatchResidualProcess`; those center generic stochastic
oracle values, while this paper's residual is specifically the SVRG estimator
above minus the deterministic finite-sum gradient. -/
noncomputable def delta (xTilde x : E) (i : ι) : E :=
  setup.estimator xTilde x i - setup.gradF x

/-- Internal epoch recursion realizing Algorithm 5.6. `internalProcess 0` stores
the initial point `x⁰ = \tilde{x}⁰ = w₀`, and `internalProcess (s + 1)` executes
one inner loop using the snapshot from the previous epoch.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/0/math`.
Quote: `\tilde{x} = \tilde{x}^{s-1}, \; \tilde{g} = \nabla f(\tilde{x}), \; x_1 = x^{s-1}, \; T = T_s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/2/math`.
Quote: `x_{t+1} = \operatorname{argmin}_{x \in X} \{ \gamma [\langle G_t, x \rangle + h(x)] + V(x_t, x) \}`.

Considered `SOptLib.recursiveIterateProcess` and
`SOptLib.proxOracleUpdate`; they cover one flat recursive process.  This
declaration is intentionally named internal because it is the global realization
carrier; the source-facing Algorithm 5.6 epoch object is `paperEpoch`, indexed by
the finite paper domain `InnerStep s`. -/
noncomputable def internalProcess : ℕ → Ω → VarianceReducedMirrorDescentInternalState E
  | 0 => fun _ =>
      { xEpoch := setup.w₀
        snapshot := setup.w₀
        innerCarrier := fun _ => setup.w₀ }
  | s + 1 => fun ω =>
      let prev := internalProcess s ω
      let xInner : ℕ → E :=
        Nat.rec prev.xEpoch (fun t x_t =>
          let i_t := setup.ξ (setup.sampleIndex s t) ω
          let G_t := setup.estimator prev.snapshot x_t i_t
          setup.proxStep x_t G_t)
      let denom := Finset.sum (Finset.Icc 2 (setup.T (s + 1))) setup.θ
      let xTildeNext : E :=
        denom⁻¹ •
          Finset.sum (Finset.Icc 2 (setup.T (s + 1)))
            (fun t => setup.θ t • xInner (t - 1))
      { xEpoch := xInner (setup.T (s + 1))
        snapshot := xTildeNext
        innerCarrier := xInner }

/-- Finite paper-facing inner-step domain for Algorithm 5.6 inside epoch `s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/0/math`.
Quote: `T = T_s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/proof/0/description`.
Quote: `over t=1,...,T inside one epoch`.

No SOptLib match: checked `SOptLib.positiveTimeIterateView` and
`SOptLib.PositiveOutputWindow.times`; those model positive or output-window
views over an already supplied process, while Algorithm 5.6 needs the epoch-local
finite inner-loop domain bounded by `T_s`. -/
abbrev InnerStep (s : ℕ) := {t : ℕ // 1 ≤ t ∧ t ≤ setup.T s}

/-- Paper-facing finite epoch object for Algorithm 5.6.

It exposes exactly the finite objects from the source algorithm: the epoch
endpoint `x^s`, the next snapshot `\tilde{x}^s`, and inner iterates indexed by
`t = 1, ..., T_s`.  The unbounded recursion is confined to the bridge theorem
`paperEpoch_inner_eq_internalCarrier`. -/
structure PaperEpochState (s : ℕ) where
  xEpoch : E
  snapshot : E
  inner : setup.InnerStep s → E

/-- Canonical paper epoch process with finite inner iterates.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/0/math`.
Quote: `x_1 = x^{s-1}, \; T = T_s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/3/math`.
Quote: `x^s = x_{T+1}, \quad \tilde{x}^s = \frac{\sum_{t=2}^{T} \theta_t x_t}{\sum_{t=2}^{T} \theta_t}`.

No SOptLib match: checked `SOptLib.recursiveIterateProcess` and
`SOptLib.positiveTimeIterateView`; they provide generic total recursive and
positive-time views, while the paper-facing object here is the finite epoch
state of Algorithm 5.6. -/
noncomputable def paperEpoch (s : ℕ) : Ω → setup.PaperEpochState s :=
  fun ω =>
    { xEpoch := (setup.internalProcess s ω).xEpoch
      snapshot := (setup.internalProcess s ω).snapshot
      inner := fun t => (setup.internalProcess s ω).innerCarrier (t.1 - 1) }

/-- Epoch endpoint `x^s`. -/
noncomputable def xEpochIter (s : ℕ) : Ω → E :=
  fun ω => (setup.paperEpoch s ω).xEpoch

/-- Snapshot point `\tilde{x}^s`. -/
noncomputable def snapshotIter (s : ℕ) : Ω → E :=
  fun ω => (setup.paperEpoch s ω).snapshot

/-- Internal zero-based carrier bridge: `internalInnerIter s 0` realizes the
paper's `x_1`, and `internalInnerIter s t` realizes `x_{t+1}`.

This declaration is not the paper-facing iterate object; use
`paperInnerIterAt` on `InnerStep s` for source statements. -/
noncomputable def internalInnerIter (s t : ℕ) : Ω → E :=
  fun ω => (setup.internalProcess s ω).innerCarrier t


/-- Paper-facing inner iterate `x_t` on the finite Algorithm 5.6 domain
`t = 1, ..., T_s`. -/
noncomputable def paperInnerIterAt (s : ℕ) (t : setup.InnerStep s) : Ω → E :=
  fun ω => (setup.paperEpoch s ω).inner t

/-- Ambient helper for formulas that sum over the literal window
`Finset.Icc 1 (T_s)`.

Inside the stated window this is `paperInnerIterAt`; outside the window it has a
dummy value and should not be used in source-facing theorem heads. -/
noncomputable def paperInnerIterInWindow (s t : ℕ) : Ω → E :=
  if ht : 1 ≤ t ∧ t ≤ setup.T s then
    setup.paperInnerIterAt s ⟨t, ht⟩
  else
    fun _ => setup.w₀

/-- On the literal finite inner-loop window, `paperInnerIterInWindow` agrees
with the finite paper iterate. -/
theorem paperInnerIterInWindow_eq_at (s : ℕ) (t : setup.InnerStep s) :
    setup.paperInnerIterInWindow s t.1 = setup.paperInnerIterAt s t := by
  simp [paperInnerIterInWindow, t.2]

/-- Bridge from a finite paper inner-step to the internal realization carrier. -/
theorem paperEpoch_inner_eq_internalCarrier (s : ℕ) (t : setup.InnerStep s) :
    setup.paperInnerIterAt s t = setup.internalInnerIter s (t.1 - 1) := by
  rfl

/-- Internal feasibility invariant for the epoch recursion.

No SOptLib match: searched `recursive process membership proxStep_mem internal
carrier`; the available hits give generic prox-step facts or this file's
one-step `proxStep_mem`, while this proof needs the local Algorithm 5.6
epoch-recursion invariant for `internalProcess`. -/
private theorem internalProcess_xEpoch_innerCarrier_mem (s : ℕ) (ω : Ω) :
    (setup.internalProcess s ω).xEpoch ∈ setup.X ∧
      ∀ t, (setup.internalProcess s ω).innerCarrier t ∈ setup.X := by
  induction s with
  | zero =>
      constructor
      · simp [VarianceReducedMirrorDescentSetup.internalProcess, setup.hw₀_mem]
      · intro t
        simp [VarianceReducedMirrorDescentSetup.internalProcess, setup.hw₀_mem]
  | succ s ih =>
      let prev := setup.internalProcess s ω
      let xInner : ℕ → E :=
        Nat.rec prev.xEpoch (fun t x_t =>
          let i_t := setup.ξ (setup.sampleIndex s t) ω
          let G_t := setup.estimator prev.snapshot x_t i_t
          setup.proxStep x_t G_t)
      have hxInner : ∀ t, xInner t ∈ setup.X := by
        intro t
        induction t with
        | zero =>
            simpa [xInner, prev] using (ih).1
        | succ t ht =>
            simpa [xInner, prev] using
              setup.proxStep_mem (xInner t)
                (setup.estimator prev.snapshot (xInner t)
                  (setup.ξ (setup.sampleIndex s t) ω))
      constructor
      · simpa [VarianceReducedMirrorDescentSetup.internalProcess, xInner, prev] using
          hxInner (setup.T (s + 1))
      · intro t
        simpa [VarianceReducedMirrorDescentSetup.internalProcess, xInner, prev] using
          hxInner t

/-- Feasibility of the internal zero-based carrier iterate, obtained by
projecting the local Algorithm 5.6 recursion invariant above. -/
private theorem internalInnerIter_mem (s t : ℕ) (ω : Ω) :
    setup.internalInnerIter s t ω ∈ setup.X := by
  exact (internalProcess_xEpoch_innerCarrier_mem setup s ω).2 t

/-- Feasibility of the finite paper inner iterate `x_t`.

This is a derived invariant of the canonical prox recursion, not a setup
assumption. -/
theorem paperInnerIterAt_mem (s : ℕ) (t : setup.InnerStep s) (ω : Ω) :
    setup.paperInnerIterAt s t ω ∈ setup.X := by
  rw [setup.paperEpoch_inner_eq_internalCarrier s t]
  exact internalInnerIter_mem setup s (t.1 - 1) ω

/-- Paper-facing next inner iterate `x_{t+1}` for `t = 1, ..., T_s`.

At the last inner step this is the epoch endpoint `x^s = x_{T_s+1}`; before the
last step it is the next finite inner iterate. -/
noncomputable def paperNextInnerIterAt (s : ℕ) (t : setup.InnerStep s) : Ω → E :=
  fun ω =>
    if ht : t.1 < setup.T s then
      (setup.paperEpoch s ω).inner
        ⟨t.1 + 1, ⟨Nat.succ_pos t.1, Nat.succ_le_of_lt ht⟩⟩
    else
      (setup.paperEpoch s ω).xEpoch

/-- Bridge from the paper-facing next iterate to the internal zero-based
realization carrier. -/
theorem paperNextInnerIterAt_eq_internalCarrier (s : ℕ) (t : setup.InnerStep s) :
    setup.paperNextInnerIterAt s t = setup.internalInnerIter s t.1 := by
  funext ω
  by_cases ht : t.1 < setup.T s
  · simp [VarianceReducedMirrorDescentSetup.paperNextInnerIterAt,
      VarianceReducedMirrorDescentSetup.paperEpoch,
      VarianceReducedMirrorDescentSetup.internalInnerIter, ht]
  · have htEq : t.1 = setup.T s := by omega
    have hlast :
        (setup.paperEpoch s ω).xEpoch = setup.internalInnerIter s (setup.T s) ω := by
      cases s <;> simp [VarianceReducedMirrorDescentSetup.paperEpoch,
        VarianceReducedMirrorDescentSetup.internalInnerIter,
        VarianceReducedMirrorDescentSetup.internalProcess,
        VarianceReducedMirrorDescentSetup.T]
    simp [VarianceReducedMirrorDescentSetup.paperNextInnerIterAt, htEq, hlast]

/-- Feasibility of the next finite paper inner iterate `x_{t+1}`.

This is a derived invariant of the canonical prox recursion, not a setup
assumption. -/
theorem paperNextInnerIterAt_mem (s : ℕ) (t : setup.InnerStep s) (ω : Ω) :
    setup.paperNextInnerIterAt s t ω ∈ setup.X := by
  rw [setup.paperNextInnerIterAt_eq_internalCarrier s t]
  exact internalInnerIter_mem setup s t.1 ω

/-- Epoch endpoint bridge: for positive epoch `s`, `x^s` is the paper's
`x_{T_s+1}` from the inner recursion. -/
theorem xEpochIter_eq_paper_last (s : ℕ) :
    setup.xEpochIter s = setup.internalInnerIter s (setup.T s) := by
  funext ω
  cases s <;> simp [VarianceReducedMirrorDescentSetup.xEpochIter,
    VarianceReducedMirrorDescentSetup.paperEpoch,
    VarianceReducedMirrorDescentSetup.internalInnerIter,
    VarianceReducedMirrorDescentSetup.internalProcess,
    VarianceReducedMirrorDescentSetup.T]

/-- Realized sampled index at paper inner step `t` of epoch `s`. -/
noncomputable def sampledIndex (s t : ℕ) : Ω → ι :=
  fun ω => setup.ξ (setup.sampleIndex (s - 1) (t - 1)) ω

/-- Realized sampled index at finite paper inner step `t = 1, ..., T_s` of
epoch `s`. This is the public Algorithm 5.6 index object; the unbounded
`sampledIndex` above is the internal totalized bridge to the sample stream. -/
noncomputable def sampledIndexAt (s : ℕ) (t : setup.InnerStep s) : Ω → ι :=
  fun ω => setup.sampledIndex s t.1 ω

/-- Bridge from the finite paper sampled-index object to the internal stream. -/
theorem sampledIndexAt_eq (s : ℕ) (t : setup.InnerStep s) :
    setup.sampledIndexAt s t =
      fun ω => setup.ξ (setup.sampleIndex (s - 1) (t.1 - 1)) ω := by
  rfl

/-- The finite paper sampled index at any Algorithm 5.6 inner step has the
component law `Q`.

This is the direct law bridge for Lemma 5.13's conditioning step; it derives the
paper statement "pick `i_t` according to `Q`" from the global sample stream
realization rather than storing a theorem-local sampling hypothesis. -/
theorem sampledIndexAt_law (s : ℕ) (t : setup.InnerStep s) (i : ι) :
    setup.P {ω | setup.sampledIndexAt s t ω = i} = ENNReal.ofReal (setup.q i) := by
  rw [setup.sampledIndexAt_eq]
  exact setup.sampledIndex_law (setup.sampleIndex (s - 1) (t.1 - 1)) i


/-- Realized VR estimator `G_t` on the finite Algorithm 5.6 domain
`t = 1, ..., T_s`. -/
noncomputable def estimatorProcessAt (s : ℕ) (t : setup.InnerStep s) : Ω → E :=
  fun ω =>
    setup.estimator (setup.snapshotIter (s - 1) ω) (setup.paperInnerIterAt s t ω)
      (setup.sampledIndexAt s t ω)


/-- Algorithm 5.6 update bridge on the finite paper inner-step domain.

This exposes the source equation
`x_{t+1} = argmin_x { γ [⟪G_t,x⟫ + h(x)] + V(x_t,x) }` through the canonical
objects already defined in this file: the finite paper iterates,
`estimatorProcessAt`, and the carrier-backed `proxStep`.  It is the deterministic
process bridge needed before applying the SOptLib mirror-prox three-point API in
Lemma 5.14. -/
theorem paperNextInnerIterAt_eq_proxStep
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    setup.paperNextInnerIterAt s t =
      fun ω =>
        setup.proxStep (setup.paperInnerIterAt s t ω)
          (setup.estimatorProcessAt s t ω) := by
  funext ω
  cases s with
  | zero =>
      omega
  | succ s' =>
      rw [setup.paperNextInnerIterAt_eq_internalCarrier (s' + 1) t]
      have ht_succ : t.1 = (t.1 - 1) + 1 := by omega
      let prev := setup.internalProcess s' ω
      let xInner : ℕ → E :=
        Nat.rec prev.xEpoch (fun n x_n =>
          let i_n := setup.ξ (setup.sampleIndex s' n) ω
          let G_n := setup.estimator prev.snapshot x_n i_n
          setup.proxStep x_n G_n)
      change xInner t.1 =
        setup.proxStep (xInner (t.1 - 1))
          (setup.estimator prev.snapshot (xInner (t.1 - 1))
            (setup.ξ (setup.sampleIndex s' (t.1 - 1)) ω))
      rw [ht_succ]
      rfl


/-- Realized noise term `δ_t = G_t - ∇f(x_t)` on the finite Algorithm 5.6
domain `t = 1, ..., T_s`. -/
noncomputable def deltaProcessAt (s : ℕ) (t : setup.InnerStep s) : Ω → E :=
  fun ω =>
    setup.delta (setup.snapshotIter (s - 1) ω) (setup.paperInnerIterAt s t ω)
      (setup.sampledIndexAt s t ω)


/-- Finite-sum unbiasedness of the variance-reduced estimator for fixed feasible
points.

This is the deterministic algebra behind Lemma 5.13's conditional expectation
claim: averaging Algorithm 5.6's estimator over the paper distribution `Q`
returns the full finite-sum gradient at the current iterate. -/
theorem estimator_finite_weighted_sum_eq_gradF
    (xTilde x : {x : E // x ∈ setup.X}) :
    Finset.sum Finset.univ
        (fun i : ι => setup.q i • setup.estimator xTilde.1 x.1 i) =
      setup.gradF x.1 := by
  classical
  have hcard_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hq_ne : ∀ i : ι, setup.q i ≠ 0 := fun i => ne_of_gt (setup.hq_pos i)
  have hcoef :
      ∀ i : ι,
        setup.q i * (((Fintype.card ι : ℝ) * setup.q i)⁻¹) =
          (Fintype.card ι : ℝ)⁻¹ := by
    intro i
    field_simp [hcard_ne, hq_ne i]
  calc
    Finset.sum Finset.univ
        (fun i : ι => setup.q i • setup.estimator xTilde.1 x.1 i)
        =
      Finset.sum Finset.univ
        (fun i : ι =>
          (Fintype.card ι : ℝ)⁻¹ •
              (setup.componentGrad i x.1 - setup.componentGrad i xTilde.1) +
            setup.q i • setup.gradF xTilde.1) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        unfold estimator
        rw [smul_add, smul_smul, hcoef i]
    _ =
      (Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ
            (fun i : ι => setup.componentGrad i x.1 - setup.componentGrad i xTilde.1) +
        (Finset.sum Finset.univ setup.q) • setup.gradF xTilde.1 := by
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul]
    _ = setup.gradF x.1 := by
        rw [setup.hq_sum, one_smul, Finset.sum_sub_distrib]
        unfold gradF
        rw [smul_sub]
        abel

/-- The fixed-point finite average of the VRMD noise term is zero.

This is the pointwise finite-distribution form consumed by conditional
expectation proofs for Lemma 5.13. -/
theorem delta_finite_weighted_sum_eq_zero
    (xTilde x : {x : E // x ∈ setup.X}) :
    Finset.sum Finset.univ
        (fun i : ι => setup.q i • setup.delta xTilde.1 x.1 i) =
      0 := by
  classical
  have hmean := setup.estimator_finite_weighted_sum_eq_gradF xTilde x
  have hqsum : Finset.sum Finset.univ setup.q = 1 := setup.hq_sum
  simp only [delta]
  calc
    Finset.sum Finset.univ
        (fun i : ι => setup.q i • (setup.estimator xTilde.1 x.1 i - setup.gradF x.1))
        =
      Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i • setup.estimator xTilde.1 x.1 i -
              setup.q i • setup.gradF x.1) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [smul_sub]
    _ =
      Finset.sum Finset.univ
          (fun i : ι => setup.q i • setup.estimator xTilde.1 x.1 i) -
        (Finset.sum Finset.univ setup.q) • setup.gradF x.1 := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_smul]
    _ = setup.gradF x.1 - setup.gradF x.1 := by
        rw [hmean, hqsum, one_smul]
    _ = 0 := by
        simp

/-- Fixed-fiber law form of the Lemma 5.13 mean-zero estimator identity.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 1: after freezing the feasible pair `(tilde{x}, x_t)`, averaging
over the fresh sampled index with law `Q` gives zero.  Reuse audit: checked
`fixedOracleDeviation_integral_law_eq_zero`, `MeasureTheory.integral_fintype`,
and local `delta_finite_weighted_sum_eq_zero`; the generic SOptLib lemma centers
an oracle through an already-proved reference mean, while this paper step is the
direct finite `Q`-weighted VRMD algebra. -/
private theorem delta_fixed_law_integral_eq_zero
    (s : ℕ) (t : setup.InnerStep s)
    (xTilde x : {x : E // x ∈ setup.X}) :
    ∫ i, setup.delta xTilde.1 x.1 i ∂Measure.map (setup.sampledIndexAt s t) setup.P =
      0 := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure (Measure.map (setup.sampledIndexAt s t) setup.P) :=
    Measure.isFiniteMeasure_map setup.P (setup.sampledIndexAt s t)
  have hfin :
      Integrable (fun i : ι => setup.delta xTilde.1 x.1 i)
        (Measure.map (setup.sampledIndexAt s t) setup.P) := by
    exact Integrable.of_finite
  have hY : Measurable (setup.sampledIndexAt s t) := by
    rw [setup.sampledIndexAt_eq]
    exact setup.hξ_meas _
  rw [MeasureTheory.integral_fintype hfin]
  calc
    Finset.sum Finset.univ
        (fun i : ι =>
          (Measure.map (setup.sampledIndexAt s t) setup.P).real {i} •
            setup.delta xTilde.1 x.1 i)
        =
      Finset.sum Finset.univ
        (fun i : ι => setup.q i • setup.delta xTilde.1 x.1 i) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        have hmass :
            (Measure.map (setup.sampledIndexAt s t) setup.P).real {i} =
              setup.q i := by
          rw [MeasureTheory.measureReal_def,
            Measure.map_apply hY (measurableSet_singleton i)]
          change (setup.P {ω | setup.sampledIndexAt s t ω = i}).toReal =
            setup.q i
          rw [setup.sampledIndexAt_law s t i]
          exact ENNReal.toReal_ofReal (le_of_lt (setup.hq_pos i))
        rw [hmass]
    _ = 0 := setup.delta_finite_weighted_sum_eq_zero xTilde x

/-- Defining equation for Algorithm 5.6's snapshot
`\tilde{x}^s = (∑_{t=2}^{T_s} θ_t x_t) / (∑_{t=2}^{T_s} θ_t)`. -/
theorem snapshotIter_eq_paper_window (s : ℕ) (hs : 1 ≤ s) :
    setup.snapshotIter s =
      fun ω =>
        (Finset.sum (Finset.Icc 2 (setup.T s)) setup.θ)⁻¹ •
          Finset.sum (Finset.Icc 2 (setup.T s))
            (fun t => setup.θ t • setup.paperInnerIterInWindow s t ω) := by
  funext ω
  cases s with
  | zero => omega
  | succ s' =>
      simp [VarianceReducedMirrorDescentSetup.snapshotIter,
        VarianceReducedMirrorDescentSetup.paperEpoch,
        VarianceReducedMirrorDescentSetup.internalProcess]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨ht2, htT⟩
      have htInner : 1 ≤ t ∧ t ≤ setup.T (s' + 1) :=
        ⟨le_trans (by norm_num : 1 ≤ 2) ht2, htT⟩
      simp [VarianceReducedMirrorDescentSetup.paperInnerIterInWindow,
        VarianceReducedMirrorDescentSetup.paperInnerIterAt,
        VarianceReducedMirrorDescentSetup.paperEpoch,
        VarianceReducedMirrorDescentSetup.internalProcess, htInner]

/-- Natural filtration generated by the global sample stream `ξ`, reusing
`SOptLib.filtration` for the sample-prefix construction. -/
noncomputable def filtration : Filtration ℕ ‹MeasurableSpace Ω› :=
  SOptLib.filtration setup.ξ setup.hξ_meas

/-- Paper-facing conditioning object for Lemma 5.13: the sigma-algebra generated
by the epoch snapshot `\tilde{x}^{s-1}` and the finite epoch history
`x_1, ..., x_t`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/key_lemmas/2/statement_math`.
Quote: `Conditionally on x_1, \ldots, x_t`.

The book proof treats the epoch snapshot `\tilde{x}` as fixed while averaging
over the fresh sampled component. In the global multi-epoch realization
`\tilde{x}^{s-1}` is random from earlier samples, so the Lean conditioning
object includes it explicitly.

No SOptLib match: checked `SOptLib.filtration` and
`SOptLib.strictPastSampleBlockMeasurableSpace`; they generate sigma-algebras
from raw sample coordinates, while Lemma 5.13 conditions on the finite paper
snapshot and inner iterates themselves. -/
@[reducible] noncomputable def epochIteratePast (s : ℕ) (t : setup.InnerStep s) : MeasurableSpace Ω :=
  MeasurableSpace.comap (setup.snapshotIter (s - 1))
      (by infer_instance : MeasurableSpace E) ⊔
    ⨆ k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1},
      MeasurableSpace.comap
        (setup.paperInnerIterAt s
          ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
        (by infer_instance : MeasurableSpace E)

/-- Explicit unfolding bridge for the paper iterate-history conditioning object.
Proofs should unfold through this theorem rather than relying on global
`@[reducible]` transparency. -/
theorem epochIteratePast_eq (s : ℕ) (t : setup.InnerStep s) :
    setup.epochIteratePast s t =
      MeasurableSpace.comap (setup.snapshotIter (s - 1))
          (by infer_instance : MeasurableSpace E) ⊔
        ⨆ k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1},
          MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E) := by
  rfl

/-- The finite vector of global samples before prefix length `N` is measurable
with respect to the generated sample-prefix filtration.

Reuse audit: this specializes `SOptLib.measurable_sample_le_prefixFiltration`
coordinatewise; `SOptLib.sampleBlock_coordinate_measurable` was considered but
the current paper bridge uses the global prefix filtration from Algorithm 5.6
rather than an arbitrary finite block. -/
private theorem sample_prefix_vector_measurable (N : ℕ) :
    Measurable[(setup.filtration).seq N]
      (fun ω : Ω => fun j : Fin N => setup.ξ j.1 ω) := by
  refine Measurable.of_comap_le ?_
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def]
  refine iSup_le ?_
  intro j
  have hcoord :=
    SOptLib.measurable_sample_le_prefixFiltration setup.ξ setup.hξ_meas j.1
  have hj : j.1 + 1 ≤ N := Nat.succ_le_of_lt j.2
  exact (hcoord.mono ((setup.filtration).mono hj) le_rfl).comap_le

/-- Successor epoch offsets split off exactly the samples consumed in the new
epoch.

Reuse audit: checked the candidate prefix/measurability SOptLib lemmas and
Mathlib `Finset.sum_Icc_succ_top`; this is only the local arithmetic alignment
between Algorithm 5.6's epoch counter and the global sample prefix. -/
private theorem epochOffset_succ_eq (s : ℕ) :
    setup.epochOffset (s + 1) = setup.epochOffset s + setup.T (s + 1) := by
  simp [VarianceReducedMirrorDescentSetup.epochOffset, Finset.sum_Icc_succ_top]

/-- Completed-epoch state factorization through any global sample prefix that
contains all samples consumed before that epoch.

Reuse audit: searched the recursive-process and sample-prefix SOptLib lemmas;
they give measurable recursive processes under measurable updates, while this
paper step needs a deterministic decoder for the pair `(x^s, \tilde x^s)` and
does not assume measurability of `proxMap`. -/
private theorem epoch_summary_factorizes_through_prefix
    (s N : ℕ) (hN : setup.epochOffset s ≤ N) :
    ∃ decode : (Fin N → ι) → E × E,
      (fun ω => ((setup.internalProcess s ω).xEpoch,
        (setup.internalProcess s ω).snapshot)) =
        fun ω => decode (fun j => setup.ξ j.1 ω) := by
  classical
  induction s generalizing N with
  | zero =>
      refine ⟨fun _ => (setup.w₀, setup.w₀), ?_⟩
      funext ω
      simp [VarianceReducedMirrorDescentSetup.internalProcess]
  | succ s ih =>
      have hOff : setup.epochOffset (s + 1) =
          setup.epochOffset s + setup.T (s + 1) :=
        epochOffset_succ_eq setup s
      have hTBound : setup.epochOffset s + setup.T (s + 1) ≤ N := by
        simpa [hOff] using hN
      have hPrevN : setup.epochOffset s ≤ N := by omega
      obtain ⟨decodePrev, hprev⟩ := ih N hPrevN
      let innerFactor : ∀ n, setup.epochOffset s + n ≤ N →
          ∃ decode : (Fin N → ι) → E,
            (fun ω => (setup.internalProcess (s + 1) ω).innerCarrier n) =
              fun ω => decode (fun j => setup.ξ j.1 ω) := by
        intro n
        induction n with
        | zero =>
            intro hn
            refine ⟨fun xs => (decodePrev xs).1, ?_⟩
            funext ω
            have hpair := congrFun hprev ω
            simpa [VarianceReducedMirrorDescentSetup.internalProcess] using
              congrArg Prod.fst hpair
        | succ n ihn =>
            intro hn
            have hNn : setup.epochOffset s + n ≤ N := by omega
            obtain ⟨decodeN, hdecodeN⟩ := ihn hNn
            refine ⟨fun xs =>
              let x := decodeN xs
              let prev := decodePrev xs
              let i := xs ⟨setup.sampleIndex s n, by
                simp [VarianceReducedMirrorDescentSetup.sampleIndex]
                omega⟩
              setup.proxStep x (setup.estimator prev.2 x i), ?_⟩
            funext ω
            have hx := congrFun hdecodeN ω
            have hpair := congrFun hprev ω
            have hsnap :
                (setup.internalProcess s ω).snapshot =
                  (decodePrev fun j => setup.ξ j.1 ω).2 :=
              congrArg Prod.snd hpair
            have hbase :
                (setup.internalProcess s ω).xEpoch =
                  (decodePrev fun j => setup.ξ j.1 ω).1 :=
              congrArg Prod.fst hpair
            simpa [VarianceReducedMirrorDescentSetup.internalProcess,
              VarianceReducedMirrorDescentSetup.sampleIndex, hbase, hsnap] using
              congrArg
                (fun x => setup.proxStep x
                  (setup.estimator (decodePrev (fun j => setup.ξ j.1 ω)).2 x
                    (setup.ξ (setup.epochOffset s + n) ω)))
                hx
      have hWindowBound
          (t : ℕ) (ht : t ∈ Finset.Icc 2 (setup.T (s + 1))) :
          setup.epochOffset s + (t - 1) ≤ N := by
        have htT := (Finset.mem_Icc.mp ht).2
        omega
      let endpointWitness := innerFactor (setup.T (s + 1)) hTBound
      let decodeEndpoint : (Fin N → ι) → E := Classical.choose endpointWitness
      let decodeSnapshot : (Fin N → ι) → E := fun xs =>
        (Finset.sum (Finset.Icc 2 (setup.T (s + 1))) setup.θ)⁻¹ •
          Finset.sum (Finset.Icc 2 (setup.T (s + 1))).attach
            (fun th => setup.θ th.1 •
              Classical.choose (innerFactor (th.1 - 1)
                (hWindowBound th.1 th.2)) xs)
      refine ⟨fun xs => (decodeEndpoint xs, decodeSnapshot xs), ?_⟩
      funext ω
      apply Prod.ext
      · exact congrFun (Classical.choose_spec endpointWitness) ω
      · simp [VarianceReducedMirrorDescentSetup.internalProcess, decodeSnapshot]
        apply congrArg
          (fun z : E =>
            ((Finset.sum (Finset.Icc 2 (setup.T (s + 1))) setup.θ)⁻¹) • z)
        rw [← Finset.sum_attach]
        refine Finset.sum_congr rfl ?_
        intro t ht
        have hspec := congrFun
          (Classical.choose_spec
            (innerFactor (t.1 - 1) (hWindowBound t.1 t.2))) ω
        exact congrArg (fun x => setup.θ t.1 • x) (by
          simpa [VarianceReducedMirrorDescentSetup.internalProcess] using hspec)

/-- Bounded finite-prefix factorization for the zero-based inner carrier of a
positive epoch.

Reuse audit: `SOptLib.process_prefix_measurable_wrt_sampleBlock` and
`SOptLib.recursive_process_measurable_of_measurable_update` were checked, but
they prove measurability from measurable update maps.  This helper records the
strictly weaker deterministic factorization needed here, avoiding any
non-source measurability assumption on the arbitrary prox selector. -/
private theorem innerCarrier_succ_factorizes_through_prefix
    (s n N : ℕ) (hN : setup.epochOffset s + n ≤ N) :
    ∃ decode : (Fin N → ι) → E,
      (fun ω => (setup.internalProcess (s + 1) ω).innerCarrier n) =
        fun ω => decode (fun j => setup.ξ j.1 ω) := by
  classical
  induction n with
  | zero =>
      have hPrevN : setup.epochOffset s ≤ N := by
        simpa using hN
      obtain ⟨decodePrev, hprev⟩ :=
        epoch_summary_factorizes_through_prefix setup s N hPrevN
      refine ⟨fun xs => (decodePrev xs).1, ?_⟩
      funext ω
      have hpair := congrFun hprev ω
      simpa [VarianceReducedMirrorDescentSetup.internalProcess] using congrArg Prod.fst hpair
  | succ n ih =>
      have hNn : setup.epochOffset s + n ≤ N := by omega
      obtain ⟨decodeN, hdecodeN⟩ := ih hNn
      have hPrevN : setup.epochOffset s ≤ N := by omega
      obtain ⟨decodePrev, hprev⟩ :=
        epoch_summary_factorizes_through_prefix setup s N hPrevN
      refine ⟨fun xs =>
        let x := decodeN xs
        let prev := decodePrev xs
        let i := xs ⟨setup.sampleIndex s n, by
          simp [VarianceReducedMirrorDescentSetup.sampleIndex]
          omega⟩
        setup.proxStep x (setup.estimator prev.2 x i), ?_⟩
      funext ω
      have hx := congrFun hdecodeN ω
      have hpair := congrFun hprev ω
      have hsnap :
          (setup.internalProcess s ω).snapshot =
            (decodePrev fun j => setup.ξ j.1 ω).2 :=
        congrArg Prod.snd hpair
      have hbase :
          (setup.internalProcess s ω).xEpoch =
            (decodePrev fun j => setup.ξ j.1 ω).1 :=
        congrArg Prod.fst hpair
      simpa [VarianceReducedMirrorDescentSetup.internalProcess,
        VarianceReducedMirrorDescentSetup.sampleIndex, hbase, hsnap] using
        congrArg
          (fun x => setup.proxStep x
            (setup.estimator (decodePrev (fun j => setup.ξ j.1 ω)).2 x
              (setup.ξ (setup.epochOffset s + n) ω)))
          hx

/-- Finite-prefix factorization for Algorithm 5.6 paper inner iterates.

This is the algorithm-semantics bridge behind Lan Lemma 5.13's conditioning on
`x_1, ..., x_t`: for `k ≤ t`, the iterate `x_k` is a deterministic function of
the global samples drawn strictly before the sample used at `t`.

Reuse audit: considered `SOptLib.process_prefix_measurable_wrt_sampleBlock`,
`SOptLib.recursiveProcess_measurable_wrt_strictPast`, and
`SOptLib.Layer1.Descent.adapted_iterate_of_recursive_sample_update`; all require
measurable update/oracle maps, while this setup intentionally stores an arbitrary
paper prox selector.  The finite-discrete sample vector factorization avoids
adding a non-source measurability field for `proxMap` and aligns with Algorithm
5.6's deterministic recursion. -/
private theorem paper_inner_iter_factorizes_through_prefix
    (s : ℕ) (k t : setup.InnerStep s) (hkt : k.1 ≤ t.1) :
    ∃ decode : (Fin (setup.sampleIndex (s - 1) (t.1 - 1)) → ι) → E,
      setup.paperInnerIterAt s k =
        fun ω => decode (fun j => setup.ξ j.1 ω) := by
  classical
  cases s with
  | zero =>
      exfalso
      have hkT : k.1 ≤ 0 := by
        simpa [VarianceReducedMirrorDescentSetup.T] using k.2.2
      omega
  | succ s' =>
      let N := setup.sampleIndex s' (t.1 - 1)
      have hN : setup.epochOffset s' + (k.1 - 1) ≤ N := by
        simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
        omega
      obtain ⟨decode, hdecode⟩ :=
        innerCarrier_succ_factorizes_through_prefix setup s' (k.1 - 1) N hN
      refine ⟨decode, ?_⟩
      rw [setup.paperEpoch_inner_eq_internalCarrier]
      simpa [N, VarianceReducedMirrorDescentSetup.internalInnerIter] using hdecode

/-- Paper inner iterates are measurable with respect to the strict global sample
prefix before the current sampled component.

This is the direct form needed to compare Lan's `x_1, ..., x_t` conditioning
sigma-algebra with the reusable SOptLib sample-prefix filtration. -/
private theorem paperInnerIterAt_measurable_globalSamplePrefix
    (s : ℕ) (k t : setup.InnerStep s) (hkt : k.1 ≤ t.1) :
    Measurable[(setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]
      (setup.paperInnerIterAt s k) := by
  classical
  obtain ⟨decode, hdecode⟩ :=
    paper_inner_iter_factorizes_through_prefix setup s k t hkt
  rw [hdecode]
  exact (Measurable.of_discrete (f := decode)).comp
    (sample_prefix_vector_measurable setup (setup.sampleIndex (s - 1) (t.1 - 1)))

/-- Bridge from the paper iterate-history conditioning object to the internal
global sample-prefix realization. -/
theorem epochIteratePast_le_globalSamplePrefix (s : ℕ) (t : setup.InnerStep s) :
    setup.epochIteratePast s t ≤
      (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1)) := by
  rw [setup.epochIteratePast_eq]
  refine sup_le ?_ ?_
  · classical
    let N := setup.sampleIndex (s - 1) (t.1 - 1)
    have hNepoch : setup.epochOffset (s - 1) ≤ N := by
      simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
    obtain ⟨decodePair, hdecodePair⟩ :=
      epoch_summary_factorizes_through_prefix setup (s - 1) N hNepoch
    have hdecode :
        setup.snapshotIter (s - 1) =
          fun ω => (decodePair (fun j : Fin N => setup.ξ j.1 ω)).2 := by
      funext ω
      have hpair := congrFun hdecodePair ω
      simpa [VarianceReducedMirrorDescentSetup.snapshotIter,
        VarianceReducedMirrorDescentSetup.paperEpoch] using congrArg Prod.snd hpair
    have hmeas :
        Measurable[(setup.filtration).seq N] (setup.snapshotIter (s - 1)) := by
      rw [hdecode]
      exact (Measurable.of_discrete (f := fun xs : Fin N → ι => (decodePair xs).2)).comp
        (sample_prefix_vector_measurable setup N)
    simpa [N] using hmeas.comap_le
  · refine iSup_le ?_
    intro k
    let kt : setup.InnerStep s :=
      ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩
    have hmeas := paperInnerIterAt_measurable_globalSamplePrefix setup s kt t k.2.2
    simpa [kt] using hmeas.comap_le


/-- Paper-facing conditioning object for Lemma 5.14 in the global process:
the sigma-algebra generated by the epoch snapshot/current paper iterate history
together with the finite within-epoch sample history `i_1, ..., i_{t-1}`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/key_lemmas/4/statement_math`.
Quote: `conditionally on i_1, \ldots, i_{t-1}`.

The paper conditions inside one epoch after fixing `\tilde x`, `x_1`, and the
already-generated iterates.  In Lean's single global stochastic process those
epoch-state objects are random functions of earlier samples, so the canonical
global realization joins the paper iterate-history conditioner with the strict
sample-past coordinates.

No SOptLib match: checked `SOptLib.filtration` and
`SOptLib.strictPastSampleBlockMeasurableSpace`; they expose global stream-prefix
or generic block filtrations, while this object names the paper's epoch-local
conditioning object with fixed epoch state. -/
@[reducible] noncomputable def epochSamplePastBefore (s : ℕ) (t : setup.InnerStep s) :
    MeasurableSpace Ω :=
  setup.epochIteratePast s t ⊔
    ⨆ k : {k : ℕ // 1 ≤ k ∧ k < t.1},
      MeasurableSpace.comap
        (setup.sampledIndexAt s
          ⟨k.1, ⟨k.2.1, le_trans (Nat.le_of_lt k.2.2) t.2.2⟩⟩)
        (by infer_instance : MeasurableSpace ι)

/-- Explicit unfolding bridge for the paper epoch-local sample-past conditioning
object. Proofs should unfold through this theorem rather than relying on global
`@[reducible]` transparency. -/
theorem epochSamplePastBefore_eq (s : ℕ) (t : setup.InnerStep s) :
    setup.epochSamplePastBefore s t =
      setup.epochIteratePast s t ⊔
        ⨆ k : {k : ℕ // 1 ≤ k ∧ k < t.1},
          MeasurableSpace.comap
            (setup.sampledIndexAt s
              ⟨k.1, ⟨k.2.1, le_trans (Nat.le_of_lt k.2.2) t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace ι) := by
  rfl

/-- Bridge from the paper epoch-local sample-past object to the internal global
sample-prefix realization. -/
theorem epochSamplePastBefore_le_globalSamplePrefix (s : ℕ) (t : setup.InnerStep s) :
    setup.epochSamplePastBefore s t ≤
      (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1)) := by
  rw [setup.epochSamplePastBefore_eq]
  refine sup_le (setup.epochIteratePast_le_globalSamplePrefix s t) ?_
  refine iSup_le ?_
  intro k
  rw [setup.sampledIndexAt_eq]
  have hidx :
      setup.sampleIndex (s - 1) (k.1 - 1) + 1 ≤
        setup.sampleIndex (s - 1) (t.1 - 1) := by
    unfold VarianceReducedMirrorDescentSetup.sampleIndex
    omega
  have hcoord :=
    SOptLib.measurable_sample_le_prefixFiltration setup.ξ setup.hξ_meas
      (setup.sampleIndex (s - 1) (k.1 - 1))
  exact le_trans hcoord.comap_le ((setup.filtration).mono hidx)


/-- Positive output horizons `S ≥ 1` for Eq. (5.3.16). -/
abbrev OutputHorizon := {S : ℕ // 1 ≤ S}

/-- Paper epoch index window `s = 1, ..., S` used by Eq. (5.3.16).

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/output/math`.
Quote: `\bar{x}^S = \frac{\sum_{s=1}^{S} w_s \tilde{x}^s}{\sum_{s=1}^{S} w_s}`.

Considered `SOptLib.PositiveOutputWindow.times`; it packages positive-time
windows over a subtype, while this paper's source-facing formula is the literal
natural-number interval in Eq. (5.3.16). -/
def outputEpochs (_setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : OutputHorizon) : Finset ℕ :=
  Finset.Icc 1 S.1

/-- Denominator of the paper weighted output average over `s = 1, ..., S`.

This is the SOptLib canonical finite output-weight denominator specialized to
the literal epoch window `1..S` and Lan's Corollary 5.8 weights. -/
noncomputable def outputWeightSum (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : OutputHorizon) : ℝ :=
  _root_.SOptLib.outputWeightSum (fun S : OutputHorizon => setup.outputEpochs S) setup.w S


/-- Snapshot feasibility bridge for the carrier-aware weighted output average. -/
theorem snapshotIter_mem (s : ℕ) (ω : Ω) :
    setup.snapshotIter s ω ∈ setup.X := by
  cases s with
  | zero =>
      simp [VarianceReducedMirrorDescentSetup.snapshotIter,
        VarianceReducedMirrorDescentSetup.paperEpoch,
        VarianceReducedMirrorDescentSetup.internalProcess, setup.hw₀_mem]
  | succ s' =>
      rw [setup.snapshotIter_eq_paper_window (s' + 1) (Nat.succ_pos s')]
      have hWpos : 0 < Finset.sum (Finset.Icc 2 (setup.T (s' + 1))) setup.θ := by
        refine _root_.SOptLib.outputWeightDenominator_pos
          (Finset.Icc 2 (setup.T (s' + 1))) setup.θ ?_ ?_
        · intro t ht
          rw [setup.theta_corollary_5_8 t]
          norm_num
        · refine ⟨2, ?_⟩
          have hpow : 0 < 2 ^ s' := by
            exact pow_pos (by norm_num : 0 < 2) s'
          simp [VarianceReducedMirrorDescentSetup.T]
          omega
      exact Convex.normalized_weighted_sum_mem setup.hX_convex
        (Finset.Icc 2 (setup.T (s' + 1))) setup.θ
        (fun t => setup.paperInnerIterInWindow (s' + 1) t ω)
        hWpos
        (by
          intro t ht
          rw [setup.theta_corollary_5_8 t]
          norm_num)
        (by
          intro t ht
          rcases Finset.mem_Icc.mp ht with ⟨ht2, htT⟩
          have htInner : 1 ≤ t ∧ t ≤ setup.T (s' + 1) :=
            ⟨le_trans (by norm_num : 1 ≤ 2) ht2, htT⟩
          simpa [VarianceReducedMirrorDescentSetup.paperInnerIterInWindow, htInner] using
            setup.paperInnerIterAt_mem (s' + 1) ⟨t, htInner⟩ ω)

/-- Output weights are nonnegative on Eq. (5.3.16)'s epoch window. -/
theorem outputWeight_nonneg (S : OutputHorizon) (s : ℕ)
    (hs : s ∈ setup.outputEpochs S) :
    0 ≤ setup.w s := by
  have hmem : s ∈ Finset.Icc 1 S.1 := by
    simpa [outputEpochs] using hs
  rcases Finset.mem_Icc.mp hmem with ⟨hs1, _hsS⟩
  by_cases h : s = 1
  · subst s
    rw [setup.w_one_corollary_5_8]
    norm_num
  · have hs2 : 2 ≤ s := by omega
    exact le_of_lt (setup.w_pos_corollary_5_8 s hs2)

/-- Denominator positivity for Eq. (5.3.16)'s output average, exposed
as a bridge rather than hidden by totalized scalar inversion. -/
theorem outputWeightSum_pos (S : OutputHorizon) :
    0 < setup.outputWeightSum S := by
  rw [outputWeightSum]
  refine _root_.SOptLib.outputWeightDenominator_pos (setup.outputEpochs S) setup.w ?_ ?_
  · intro s hs
    have hmem : s ∈ Finset.Icc 1 S.1 := by
      simpa [outputEpochs] using hs
    rcases Finset.mem_Icc.mp hmem with ⟨hs1, _hsS⟩
    by_cases h : s = 1
    · subst s
      rw [setup.w_one_corollary_5_8]
      norm_num
    · have hs2 : 2 ≤ s := by omega
      exact setup.w_pos_corollary_5_8 s hs2
  · exact ⟨1, by simp [outputEpochs, S.2]⟩

/-- Defining equation for the Eq. (5.3.16) output denominator. -/
theorem outputWeightSum_eq (S : OutputHorizon) :
    setup.outputWeightSum S = Finset.sum (setup.outputEpochs S) setup.w := by
  exact _root_.SOptLib.outputWeightSum_eq_sum
    (fun S : OutputHorizon => setup.outputEpochs S) setup.w S


/-- Carrier-valued epoch-weighted output average `\bar{x}^S` from Eq. (5.3.16),
indexed exactly as `s = 1, ..., S`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/output/math`.
Quote: `\bar{x}^S = \frac{\sum_{s=1}^{S} w_s \tilde{x}^s}{\sum_{s=1}^{S} w_s}`.

This specializes `_root_.SOptLib.weightedOutputAverage` to Lan's snapshot process and
the Corollary 5.8 output weights, after `w` has recorded the paper's first-weight
bridge from the proof of Corollary 5.8. -/
noncomputable def barXCarrier (S : OutputHorizon) : Ω → {x : E // x ∈ setup.X} :=
  _root_.SOptLib.weightedOutputAverage setup.X
    (fun S : OutputHorizon => setup.outputEpochs S)
    setup.w
    (fun s ω => setup.snapshotIter s ω)
    setup.outputWeightSum
    setup.hX_convex
    (fun S s hs => setup.outputWeight_nonneg S s hs)
    (fun _S s _hs ω => setup.snapshotIter_mem s ω)
    (fun S => setup.outputWeightSum_pos S)
    (fun S => setup.outputWeightSum_eq S)
    S

/-- Ambient value of the paper output `\bar{x}^S`. -/
noncomputable def barX (S : OutputHorizon) : Ω → E :=
  fun ω => (setup.barXCarrier S ω).1


/-- Ambient formula for Eq. (5.3.16), inherited from
`_root_.SOptLib.weightedOutputAverage_val`. -/
theorem barX_def (S : OutputHorizon) (ω : Ω) :
    setup.barX S ω =
      (setup.outputWeightSum S)⁻¹ •
        Finset.sum (setup.outputEpochs S)
          (fun s => setup.w s • setup.snapshotIter s ω) := by
  unfold VarianceReducedMirrorDescentSetup.barX
  simpa [VarianceReducedMirrorDescentSetup.barXCarrier] using
    (_root_.SOptLib.weightedOutputAverage_val setup.X
      (fun S : OutputHorizon => setup.outputEpochs S)
      setup.w
      (fun s ω => setup.snapshotIter s ω)
      setup.outputWeightSum
      setup.hX_convex
      (fun S s hs => setup.outputWeight_nonneg S s hs)
      (fun _S s _hs ω => setup.snapshotIter_mem s ω)
      (fun S => setup.outputWeightSum_pos S)
      (fun S => setup.outputWeightSum_eq S)
      S
      ω)

/-- Convexity of the composite paper objective on the feasible carrier.

This derives the source-facing convexity of `Ψ = f + h` from component convexity
and the stated convexity of `h`, exposing the hypothesis needed by the finite
weighted Jensen bridge rather than treating output convexity as an assumption. -/
theorem Psi_convexOn :
    ConvexOn ℝ setup.X setup.Psi := by
  simpa [VarianceReducedMirrorDescentSetup.Psi] using
    (fAvg_convexOn_from_components setup).add setup.hh_convex

/-- Jensen bridge for Eq. (5.3.16)'s epoch-weighted output average. -/
theorem Psi_barXCarrier_le_weighted_sum (S : OutputHorizon) (ω : Ω) :
    setup.PsiOn (setup.barXCarrier S ω) ≤
      (setup.outputWeightSum S)⁻¹ *
        Finset.sum (setup.outputEpochs S)
          (fun s =>
            setup.w s *
              setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩) := by
  classical
  have hJ :=
    _root_.convexOn_weighted_average_le_weighted_sum
      (hf := setup.Psi_convexOn)
      (s := setup.outputEpochs S)
      (γ := setup.w)
      (p := fun s => setup.snapshotIter s ω)
      (xbar := (setup.barXCarrier S ω).1)
      (W := setup.outputWeightSum S)
      (hγ_nonneg := fun s hs => setup.outputWeight_nonneg S s hs)
      (hp_mem := fun s _hs => setup.snapshotIter_mem s ω)
      (hW_pos := setup.outputWeightSum_pos S)
      (hW_eq := setup.outputWeightSum_eq S)
      (hxbar := by
        simpa [VarianceReducedMirrorDescentSetup.barX] using setup.barX_def S ω)
  simpa [VarianceReducedMirrorDescentSetup.PsiOn_coe] using hJ

/-- Component-gradient evaluations consumed by epoch `s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/proof/4/description`.
Quote: `each epoch s costs m + T_s component gradient evaluations`.

No reusable SOptLib match fits this finite-sum VRMD accounting object:
checked `SOptLib.oracleCallsForTwoPhaseChoices` and `SOptLib.twoPhaseSFOCallBound`,
but those package two-phase repeated-run accounting rather than Lan's
per-epoch full-gradient plus inner-loop component-gradient count. -/
def epochSFOCost (s : ℕ) : ℕ :=
  Fintype.card ι + setup.T s

/-- Cumulative component-gradient evaluations through `S` epochs. -/
def cumulativeSFOCalls (S : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 S) setup.epochSFOCost


/-- Defining equation for the cumulative SFO count used in Corollary 5.8. -/
theorem cumulativeSFOCalls_eq (S : ℕ) :
    setup.cumulativeSFOCalls S =
      Finset.sum (Finset.Icc 1 S) (fun s => Fintype.card ι + setup.T s) := by
  rfl

/-- Initial accuracy scale in the displayed Corollary 5.8 complexity rate,
formed from the carrier-domain objective and Bregman objects. -/
noncomputable def complexityRadius (xStar : {x : E // x ∈ setup.X}) : ℝ :=
  setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar +
    setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar

/-- Literal displayed SFO complexity rate from Corollary 5.8.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/rate`.
Quote: `O{ m log ((Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon) + (Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon }`.

The SOptLib complexity candidates are for two-phase stochastic mirror descent;
this local definition is the literal finite-sum VRMD rate expression with
`m = Fintype.card ι`. -/
noncomputable def displayedSFOComplexityRate
    (xStar : {x : E // x ∈ setup.X}) (ε : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) * Real.log (setup.complexityRadius xStar / ε) +
    setup.complexityRadius xStar / ε

/-- Defining equation for the literal displayed Corollary 5.8 SFO rate object. -/
theorem displayedSFOComplexityRate_eq (xStar : {x : E // x ∈ setup.X}) (ε : ℝ) :
    setup.displayedSFOComplexityRate xStar ε =
      (Fintype.card ι : ℝ) * Real.log (setup.complexityRadius xStar / ε) +
        setup.complexityRadius xStar / ε := by
  rfl

/-- Totalized SFO complexity-rate envelope for Corollary 5.8.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/rate`.
Quote: `O{ m log ((Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon) + (Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon }`.

The displayed logarithmic expression is the paper object when the initial
radius is nonzero.  In the already-optimal zero-radius case, Lean's total
`Real.log (0 / ε)` would make the literal expression identically zero, while
Corollary 5.8's complexity statement only needs a constant zero-radius envelope.
No SOptLib match: searched "oracle call complexity logarithmic rate asymptotic"
and "complexity rate totalized zero radius", checked `SOptLib/Model/Complexity.lean`
and `SOptLib/Layer1/Complexity.lean`; those primitives model two-phase
stochastic mirror descent rates, not this finite-sum VRMD radius totalization. -/
noncomputable def sfoComplexityRate (xStar : {x : E // x ∈ setup.X}) (ε : ℝ) : ℝ :=
  if setup.complexityRadius xStar = 0 then
    1
  else
    setup.displayedSFOComplexityRate xStar ε


/-- For nonzero initial radius, the totalized rate is exactly the paper's
displayed logarithmic expression. -/
theorem sfoComplexityRate_eq_displayed_of_radius_ne_zero
    (xStar : {x : E // x ∈ setup.X}) (ε : ℝ)
    (hR : setup.complexityRadius xStar ≠ 0) :
    setup.sfoComplexityRate xStar ε =
      setup.displayedSFOComplexityRate xStar ε := by
  simp [sfoComplexityRate, hR]

/-- In the already-optimal zero-radius case, the totalized rate is the constant
envelope needed for the asymptotic SFO-count statement. -/
theorem sfoComplexityRate_eq_one_of_radius_eq_zero
    (xStar : {x : E // x ∈ setup.X}) (ε : ℝ)
    (hR : setup.complexityRadius xStar = 0) :
    setup.sfoComplexityRate xStar ε = 1 := by
  simp [sfoComplexityRate, hR]

/-- Public wrapper for the finite sample-prefix vector measurability bridge.

This exposes the private prefix infrastructure to later paper proofs outside
the setup namespace. Reuse audit: this is exactly the local specialization of
`SOptLib.measurable_sample_le_prefixFiltration` already proved in
`sample_prefix_vector_measurable`, aligned with Algorithm 5.6's global sample
stream realization. -/
theorem samplePrefixVector_measurable (N : ℕ) :
    Measurable[(setup.filtration).seq N]
      (fun ω : Ω => fun j : Fin N => setup.ξ j.1 ω) := by
  exact sample_prefix_vector_measurable setup N

/-- Public wrapper for completed-epoch finite-prefix factorization.

This is not a new primitive: it re-exports the route-local decoder
`epoch_summary_factorizes_through_prefix` so Lemma 5.13 can freeze the
snapshot as a deterministic function of the strict sample prefix. -/
theorem snapshotIter_factorizes_through_globalPrefix
    (s N : ℕ) (hN : setup.epochOffset s ≤ N) :
    ∃ decode : (Fin N → ι) → E,
      setup.snapshotIter s =
        fun ω => decode (fun j => setup.ξ j.1 ω) := by
  obtain ⟨decodePair, hdecodePair⟩ :=
    epoch_summary_factorizes_through_prefix setup s N hN
  refine ⟨fun xs => (decodePair xs).2, ?_⟩
  funext ω
  have hpair := congrFun hdecodePair ω
  simpa [VarianceReducedMirrorDescentSetup.snapshotIter,
    VarianceReducedMirrorDescentSetup.paperEpoch] using congrArg Prod.snd hpair

/-- Public wrapper for paper inner-iterate finite-prefix factorization.

This exposes the already-proved Algorithm 5.6 recursion decoder to later
conditional-expectation proofs; it is the same bridge as
`paper_inner_iter_factorizes_through_prefix`, not a distinct model object. -/
theorem paperInnerIter_factorizes_through_globalPrefix
    (s : ℕ) (k t : setup.InnerStep s) (hkt : k.1 ≤ t.1) :
    ∃ decode : (Fin (setup.sampleIndex (s - 1) (t.1 - 1)) → ι) → E,
      setup.paperInnerIterAt s k =
        fun ω => decode (fun j => setup.ξ j.1 ω) := by
  exact paper_inner_iter_factorizes_through_prefix setup s k t hkt

/-- Public wrapper for next-paper-iterate finite-prefix factorization.

This aligns with Lan Lemma 5.14's conditioning step for `x_{t+1}`. Search
audit: checked the local `paperNextInnerIterAt_eq_internalCarrier` and
`innerCarrier_succ_factorizes_through_prefix`; together they provide exactly
the finite-prefix decoder for the post-update iterate, while SOptLib's generic
recursive-process measurability lemmas require measurable update maps not
assumed by this setup. -/
theorem paperNextInnerIter_factorizes_through_globalPrefix
    (s : ℕ) (t : setup.InnerStep s) :
    ∃ decode : (Fin (setup.sampleIndex (s - 1) t.1) → ι) → E,
      setup.paperNextInnerIterAt s t =
        fun ω => decode (fun j => setup.ξ j.1 ω) := by
  classical
  cases s with
  | zero =>
      exfalso
      have ht0 : t.1 ≤ 0 := by
        simpa [VarianceReducedMirrorDescentSetup.T] using t.2.2
      omega
  | succ s' =>
      let N := setup.sampleIndex s' t.1
      have hN : setup.epochOffset s' + t.1 ≤ N := by
        simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
      obtain ⟨decode, hdecode⟩ :=
        innerCarrier_succ_factorizes_through_prefix setup s' t.1 N hN
      refine ⟨decode, ?_⟩
      rw [setup.paperNextInnerIterAt_eq_internalCarrier]
      simpa [N, VarianceReducedMirrorDescentSetup.internalInnerIter] using hdecode

/-- Public wrapper for the fixed-fiber finite-law centering identity.

This re-exports `delta_fixed_law_integral_eq_zero` for the later stochastic
conditioning argument and aligns with Lan Lemma 5.13 proof step 1: after
freezing the feasible snapshot/current pair, averaging over the fresh `Q` draw
gives zero. -/
theorem deltaFixedLawIntegralEqZero
    (s : ℕ) (t : setup.InnerStep s)
    (xTilde x : {x : E // x ∈ setup.X}) :
    ∫ i, setup.delta xTilde.1 x.1 i ∂Measure.map (setup.sampledIndexAt s t) setup.P =
      0 := by
  exact delta_fixed_law_integral_eq_zero setup s t xTilde x

end VarianceReducedMirrorDescentSetup

namespace VarianceReducedMirrorDescent

/-- Current-namespace copy of the scalar convex endpoint slope bridge above.

Reuse audit: same as `VarianceReducedMirrorDescentSetup.convexOn_Icc_hasDerivWithinAt_left_le_slope`;
this copy is needed because that helper is private to the setup namespace. -/
private theorem convexOn_Icc_hasDerivWithinAt_left_le_slope
    {φ : ℝ → ℝ} {D : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ)
    (hderiv : HasDerivWithinAt φ D (Set.Icc (0 : ℝ) 1) 0) :
    D ≤ slope φ 0 1 := by
  exact hconv.le_slope_of_hasDerivWithinAt
    (x := (0 : ℝ)) (y := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hderiv


/-- Boundary-safe carrier supporting-hyperplane inequality for a convex
differentiable-on ambient representative.

This is the current-namespace copy of the setup-side
`bregman_core_nonneg_of_convexOn_differentiableOn`, which is private to
`VarianceReducedMirrorDescentSetup` and cannot be specialized here.  Considered
`bregmanDivergence_nonneg_of_convexOn` and
`bregman_core_nonneg_of_convexOn_differentiableOn`; the SOptLib theorem is an
ambient-gradient form, while the existing local theorem is namespace-private,
so this helper records the needed `gradientWithin` support form. -/
private theorem carrier_linearized_gap_nonneg_of_convexOn_differentiableOn
    {X : Set E} {v : E → ℝ} {x z : E}
    (hv : ConvexOn ℝ X v)
    (hdiff : DifferentiableOn ℝ v X)
    (hx : x ∈ X) (hz : z ∈ X) :
    0 ≤ v z - v x - ⟪gradientWithin v X x, z - x⟫_ℝ := by
  let line : ℝ → E := fun t => AffineMap.lineMap x z t
  have hline_mem : Set.Icc (0 : ℝ) 1 ⊆ line ⁻¹' X := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : 1 - t + t = 1 := by ring
    have hmem : (1 - t) • x + t • z ∈ X := hv.1 hx hz h1t ht0 hsum
    simpa [line, AffineMap.lineMap_apply_module] using hmem
  have hg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => v (line t)) := by
    simpa [line] using
      (hv.comp_affineMap (AffineMap.lineMap x z)).subset hline_mem (convex_Icc 0 1)
  have hmaps : Set.MapsTo line (Set.Icc (0 : ℝ) 1) X := by
    intro t ht
    exact hline_mem ht
  have hline_deriv :
      HasDerivWithinAt line (z - x) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [line] using
      (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := z)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hvdiff : DifferentiableWithinAt ℝ v X x := hdiff x hx
  have hg_deriv :
      HasDerivWithinAt (fun t => v (line t))
        ((fderivWithin ℝ v X x) (z - x)) (Set.Icc (0 : ℝ) 1) 0 :=
    hvdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line])
  have hslope :
      (fderivWithin ℝ v X x) (z - x) ≤
        slope (fun t => v (line t)) 0 1 := by
    exact convexOn_Icc_hasDerivWithinAt_left_le_slope hg_conv hg_deriv
  have hgrad_apply :
      (fderivWithin ℝ v X x) (z - x) =
        ⟪gradientWithin v X x, z - x⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hslope_expanded :
      ⟪gradientWithin v X x, z - x⟫_ℝ ≤ v z - v x := by
    rw [hgrad_apply] at hslope
    simpa [slope_def_field, line] using hslope
  linarith

/-- Pair the canonical carrier gradient with a feasible displacement as the
ambient within-derivative of the representative.

This is the local chart bridge needed for Lan Lemma 5.8 on a carrier.  Considered
`SOptLib.carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior` and
`SOptLib.carrierChart_fderivWithin_eq_intrinsicInterior_fderivWithin_on_feasible_direction`;
those are intrinsic-interior/`ContDiffOn` bridges, while this proof unit needs
the boundary `DifferentiableOn` form for the carrier chart selected by
`SOptLib.carrierGradient`. -/
private theorem carrierGradient_inner_eq_fderivWithin_on_feasible_direction
    {X : Set E} (F : E → ℝ) (f : {x : E // x ∈ X} → ℝ)
    (hX : Convex ℝ X)
    (hdiff : DifferentiableOn ℝ F X)
    (hf : ∀ y : {x : E // x ∈ X}, f y = F y.1)
    (x z : {x : E // x ∈ X}) :
    ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ =
      (fderivWithin ℝ F X x.1) (z.1 - x.1) := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨x.1, subset_affineSpan ℝ X x.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := SOptLib.carrierChartSet X x
  let cf : A.direction → ℝ := SOptLib.carrierChartFunction X f x
  let u : A.direction := SOptLib.carrierChartPoint X x x
  let du : A.direction :=
    ⟨z.1 - x.1,
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ X z.2) (subset_affineSpan ℝ X x.2)⟩
  let Lchart : A.direction →ᴬ[ℝ] E := SOptLib.carrierChartToAmbient X x
  have hdu_sub : (A.direction.subtypeL) du = z.1 - x.1 := rfl
  have hu : u ∈ T := by
    simpa [A, T, u] using SOptLib.carrierChartPoint_mem X x x
  have huniq : UniqueDiffWithinAt ℝ T u := by
    exact (SOptLib.carrierChartSet_uniqueDiffOn X x hX) u hu
  have hLu : Lchart u = x.1 := by
    simpa [A, Lchart, u] using SOptLib.carrierChartToAmbient_chartPoint X x x
  have hFdiff : DifferentiableWithinAt ℝ F X (Lchart u) := by
    rw [hLu]
    exact hdiff x.1 x.2
  have hLhas : HasFDerivWithinAt (fun y : A.direction => Lchart y) Lchart.contLinear T u := by
    rw [Lchart.decomp]
    exact Lchart.contLinear.hasFDerivWithinAt.add_const (Lchart 0)
  have hLdiff : DifferentiableWithinAt ℝ (fun y : A.direction => Lchart y) T u :=
    hLhas.differentiableWithinAt
  have hmap : Set.MapsTo (fun y : A.direction => Lchart y) T X := by
    intro y hy
    simpa [A, T, Lchart, SOptLib.carrierChartSet] using hy
  have hcongr : Set.EqOn cf (fun y : A.direction => F (Lchart y)) T := by
    intro y hy
    have hyX : Lchart y ∈ X := hmap hy
    calc
      cf y = SOptLib.totalizeOn X f (Lchart y) := rfl
      _ = f ⟨Lchart y, hyX⟩ := by
          exact SOptLib.totalizeOn_of_mem X f hyX
      _ = F (Lchart y) := by
          rw [hf]
  have hleft_congr :
      fderivWithin ℝ cf T u =
        fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u := by
    exact fderivWithin_congr' hcongr hu
  have hcomp :
      fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u =
        (fderivWithin ℝ F X (Lchart u)).comp
          (fderivWithin ℝ (fun y : A.direction => Lchart y) T u) := by
    exact fderivWithin_comp' (x := u) hFdiff hLdiff hmap huniq
  have hLder :
      fderivWithin ℝ (fun y : A.direction => Lchart y) T u = Lchart.contLinear := by
    exact hLhas.fderivWithin huniq
  have hLlin : Lchart.contLinear du = Lchart du - Lchart 0 := by
    simpa [vsub_eq_sub] using Lchart.contLinear_map_vsub du 0
  have hLdu_apply : Lchart du = (du : E) + x.1 := by
    let a : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        du : A) : E) = (du : E) + x.1
    simp [a]
  have hLzero : Lchart 0 = x.1 := by
    let a : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        (0 : A.direction) : A) : E) = x.1
    simp [a]
  have hLdu : Lchart.contLinear du = z.1 - x.1 := by
    rw [hLlin, hLdu_apply, hLzero]
    simp [du]
  have hchart :
      (fderivWithin ℝ cf T u) du =
        (fderivWithin ℝ F X x.1) (z.1 - x.1) := by
    calc
      (fderivWithin ℝ cf T u) du
          = (fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u) du := by
              rw [hleft_congr]
      _ = ((fderivWithin ℝ F X (Lchart u)).comp
            (fderivWithin ℝ (fun y : A.direction => Lchart y) T u)) du := by
              rw [hcomp]
      _ = (fderivWithin ℝ F X x.1) (z.1 - x.1) := by
              rw [hLder]
              simp [ContinuousLinearMap.comp_apply, hLdu, hLu]
  have hcompInst : CompleteSpace A.direction := instComplete
  calc
    ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ
        = (fderivWithin ℝ cf T u) du := by
          unfold SOptLib.carrierGradient SOptLib.carrierGradientFrom
          rw [← hdu_sub]
          change
            ⟪((@gradientWithin ℝ A.direction _ _ _ hcompInst cf T u : A.direction) : E),
              (du : E)⟫_ℝ =
              (fderivWithin ℝ cf T u) du
          rw [← A.direction.coe_inner
            (@gradientWithin ℝ A.direction _ _ _ hcompInst cf T u) du]
          simp [gradientWithin]
          rfl
    _ = (fderivWithin ℝ F X x.1) (z.1 - x.1) := hchart

/-- Supporting-hyperplane gap using the canonical carrier gradient.

This aligns with Lan Lemma 5.8 proof step 1 after translating the paper
gradient notation to `SOptLib.carrierGradient`.  Considered
`carrier_linearized_gap_nonneg_of_convexOn_differentiableOn`, which gives the
same support inequality for `gradientWithin`; the pairing bridge above is the
missing carrier-gradient specialization. -/
private theorem carrier_linearized_gap_nonneg_with_carrierGradient
    {X : Set E} (F : E → ℝ) (f : {x : E // x ∈ X} → ℝ)
    (hX : Convex ℝ X)
    (hconv : ConvexOn ℝ X F)
    (hdiff : DifferentiableOn ℝ F X)
    (hf : ∀ y : {x : E // x ∈ X}, f y = F y.1)
    (x z : {x : E // x ∈ X}) :
    0 ≤ f z - f x - ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ := by
  have hsupport :=
    carrier_linearized_gap_nonneg_of_convexOn_differentiableOn
      (X := X) (v := F) (x := x.1) (z := z.1) hconv hdiff x.2 z.2
  have hpair :
      ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ =
        ⟪gradientWithin F X x.1, z.1 - x.1⟫_ℝ := by
    calc
      ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ
          = (fderivWithin ℝ F X x.1) (z.1 - x.1) := by
              exact carrierGradient_inner_eq_fderivWithin_on_feasible_direction
                F f hX hdiff hf x z
      _ = ⟪gradientWithin F X x.1, z.1 - x.1⟫_ℝ := by
              rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  rw [hf x, hf z, hpair]
  exact hsupport

/-- Pair the canonical carrier gradient with any affine-span direction as the
ambient within-derivative of the representative.

This is the affine-direction variant needed by Lan Lemma 5.8's segment FTC
argument.  Considered
`SOptLib.carrierChart_fderivWithin_eq_intrinsicInterior_fderivWithin_on_feasible_direction`
and the local `carrierGradient_inner_eq_fderivWithin_on_feasible_direction`;
both are stated for feasible point differences, while the derivative of a
feasible segment is an arbitrary direction in `(affineSpan ℝ X).direction`. -/
private theorem carrierGradient_inner_eq_fderivWithin_on_affine_direction
    {X : Set E} (F : E → ℝ) (f : {x : E // x ∈ X} → ℝ)
    (hX : Convex ℝ X)
    (hdiff : DifferentiableOn ℝ F X)
    (hf : ∀ y : {x : E // x ∈ X}, f y = F y.1)
    (x : {x : E // x ∈ X}) (du : (affineSpan ℝ X).direction) :
    ⟪SOptLib.carrierGradient X f x, (du : E)⟫_ℝ =
      (fderivWithin ℝ F X x.1) (du : E) := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨x.1, subset_affineSpan ℝ X x.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := SOptLib.carrierChartSet X x
  let cf : A.direction → ℝ := SOptLib.carrierChartFunction X f x
  let u : A.direction := SOptLib.carrierChartPoint X x x
  let Lchart : A.direction →ᴬ[ℝ] E := SOptLib.carrierChartToAmbient X x
  have hu : u ∈ T := by
    simpa [A, T, u] using SOptLib.carrierChartPoint_mem X x x
  have huniq : UniqueDiffWithinAt ℝ T u := by
    exact (SOptLib.carrierChartSet_uniqueDiffOn X x hX) u hu
  have hLu : Lchart u = x.1 := by
    simpa [A, Lchart, u] using SOptLib.carrierChartToAmbient_chartPoint X x x
  have hFdiff : DifferentiableWithinAt ℝ F X (Lchart u) := by
    rw [hLu]
    exact hdiff x.1 x.2
  have hLhas : HasFDerivWithinAt (fun y : A.direction => Lchart y) Lchart.contLinear T u := by
    rw [Lchart.decomp]
    exact Lchart.contLinear.hasFDerivWithinAt.add_const (Lchart 0)
  have hLdiff : DifferentiableWithinAt ℝ (fun y : A.direction => Lchart y) T u :=
    hLhas.differentiableWithinAt
  have hmap : Set.MapsTo (fun y : A.direction => Lchart y) T X := by
    intro y hy
    simpa [A, T, Lchart, SOptLib.carrierChartSet] using hy
  have hcongr : Set.EqOn cf (fun y : A.direction => F (Lchart y)) T := by
    intro y hy
    have hyX : Lchart y ∈ X := hmap hy
    calc
      cf y = SOptLib.totalizeOn X f (Lchart y) := rfl
      _ = f ⟨Lchart y, hyX⟩ := by
          exact SOptLib.totalizeOn_of_mem X f hyX
      _ = F (Lchart y) := by
          rw [hf]
  have hleft_congr :
      fderivWithin ℝ cf T u =
        fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u := by
    exact fderivWithin_congr' hcongr hu
  have hcomp :
      fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u =
        (fderivWithin ℝ F X (Lchart u)).comp
          (fderivWithin ℝ (fun y : A.direction => Lchart y) T u) := by
    exact fderivWithin_comp' (x := u) hFdiff hLdiff hmap huniq
  have hLder :
      fderivWithin ℝ (fun y : A.direction => Lchart y) T u = Lchart.contLinear := by
    exact hLhas.fderivWithin huniq
  have hLlin : Lchart.contLinear du = Lchart du - Lchart 0 := by
    simpa [vsub_eq_sub] using Lchart.contLinear_map_vsub du 0
  have hLdu_apply : Lchart du = (du : E) + x.1 := by
    let a : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        du : A) : E) = (du : E) + x.1
    simp [a]
  have hLzero : Lchart 0 = x.1 := by
    let a : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        (0 : A.direction) : A) : E) = x.1
    simp [a]
  have hLdu : Lchart.contLinear du = (du : E) := by
    rw [hLlin, hLdu_apply, hLzero]
    simp
  have hchart :
      (fderivWithin ℝ cf T u) du =
        (fderivWithin ℝ F X x.1) (du : E) := by
    calc
      (fderivWithin ℝ cf T u) du
          = (fderivWithin ℝ (fun y : A.direction => F (Lchart y)) T u) du := by
              rw [hleft_congr]
      _ = ((fderivWithin ℝ F X (Lchart u)).comp
            (fderivWithin ℝ (fun y : A.direction => Lchart y) T u)) du := by
              rw [hcomp]
      _ = (fderivWithin ℝ F X x.1) (du : E) := by
              rw [hLder]
              simp [ContinuousLinearMap.comp_apply, hLdu, hLu]
  have hcompInst : CompleteSpace A.direction := instComplete
  calc
    ⟪SOptLib.carrierGradient X f x, (du : E)⟫_ℝ
        = (fderivWithin ℝ cf T u) du := by
          unfold SOptLib.carrierGradient SOptLib.carrierGradientFrom
          change
            ⟪((@gradientWithin ℝ A.direction _ _ _ hcompInst cf T u : A.direction) : E),
              (du : E)⟫_ℝ =
              (fderivWithin ℝ cf T u) du
          rw [← A.direction.coe_inner
            (@gradientWithin ℝ A.direction _ _ _ hcompInst cf T u) du]
          simp [gradientWithin]
          rfl
    _ = (fderivWithin ℝ F X x.1) (du : E) := hchart

/-- Carrier smooth quadratic upper bound from the exact hypotheses available in
Lan Lemma 5.8.

This aligns with Lan Lemma 5.8's smoothness step on the feasible carrier.
Considered `Convex.carrier_smooth_quadratic_upper_bound`; it has the same
mathematical conclusion but requires `ContDiffOn`, while the VRMD setup supplies
`DifferentiableOn` plus an explicit Lipschitz bound for
`SOptLib.carrierGradient`, so this local bridge repeats the scalar segment FTC
argument under those hypotheses. -/
private theorem carrierGradient_smooth_upper_bound_from_diff_lipschitz
    {X : Set E} (F : E → ℝ) (f : {x : E // x ∈ X} → ℝ) (L : ℝ)
    (hX : Convex ℝ X)
    (hdiff : DifferentiableOn ℝ F X)
    (hf : ∀ y : {x : E // x ∈ X}, f y = F y.1)
    (hsmooth : ∀ x y : {x : E // x ∈ X},
      SOptLib.dualNorm
          (SOptLib.carrierGradient X f x - SOptLib.carrierGradient X f y) ≤
        L * ‖x.1 - y.1‖)
    (x y : {x : E // x ∈ X}) :
    f y ≤ f x + ⟪SOptLib.carrierGradient X f x, y.1 - x.1⟫_ℝ +
      (L / 2) * ‖y.1 - x.1‖ ^ 2 := by
  classical
  let grad : {x : E // x ∈ X} → E := fun x => SOptLib.carrierGradient X f x
  let d : E := y.1 - x.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap x.1 y.1 t
  let Fseg : ℝ → ℝ := fun t => F (line t)
  have hF0 : Fseg 0 = f x := by
    simpa [Fseg, line] using (hf x).symm
  have hF1 : Fseg 1 = f y := by
    simpa [Fseg, line] using (hf y).symm
  have hline_mem : ∀ t ∈ s, line t ∈ X := by
    intro t ht
    exact hX.lineMap_mem x.2 y.2 ht
  have hmaps : Set.MapsTo line s X := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg
        ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := x.1) (b := y.1)
          (s := s) (x := t))
    have hfdiff : DifferentiableWithinAt ℝ F X (line t) :=
      hdiff (line t) (hline_mem t ht)
    have hfseg : HasDerivWithinAt Fseg
        ((fderivWithin ℝ F X (line t)) d) s t := by
      simpa [Fseg, Function.comp_def] using
        hfdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps
          (by simp [line])
    have hgrad_apply :
        (fderivWithin ℝ F X (line t)) d =
          ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ := by
      symm
      have hd_mem : d ∈ (affineSpan ℝ X).direction := by
        exact AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ X y.2) (subset_affineSpan ℝ X x.2)
      let du : (affineSpan ℝ X).direction := ⟨d, hd_mem⟩
      simpa [du] using
        carrierGradient_inner_eq_fderivWithin_on_affine_direction
          F f hX hdiff hf ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩ du
    simpa [hgrad_apply] using hfseg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ ≤
        ⟪grad x, d⟫_ℝ + L * t * ‖d‖ ^ 2 := by
    intro t ht
    let zt : {x : E // x ∈ X} := ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : zt.1 - x.1 = t • d := by
      simp [zt, line, d, AffineMap.lineMap_apply_module']
    have hnorm_line : ‖zt.1 - x.1‖ = t * ‖d‖ := by
      rw [hseg_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hlip : ‖grad zt - grad x‖ ≤ L * (t * ‖d‖) := by
      calc
        ‖grad zt - grad x‖
            = SOptLib.dualNorm (grad zt - grad x) := by
                rw [SOptLib.dualNorm_eq_norm]
        _ ≤ L * ‖zt.1 - x.1‖ := hsmooth zt x
        _ = L * (t * ‖d‖) := by rw [hnorm_line]
    have hinner_diff :
        ⟪grad zt, d⟫_ℝ - ⟪grad x, d⟫_ℝ =
          ⟪grad zt - grad x, d⟫_ℝ := by
      rw [inner_sub_left]
    have hcs :
        ⟪grad zt - grad x, d⟫_ℝ ≤ ‖grad zt - grad x‖ * ‖d‖ := by
      calc
        ⟪grad zt - grad x, d⟫_ℝ
            ≤ |⟪grad zt - grad x, d⟫_ℝ| := le_abs_self _
        _ ≤ ‖grad zt - grad x‖ * ‖d‖ :=
          abs_real_inner_le_norm (grad zt - grad x) d
    have hmul :
        ‖grad zt - grad x‖ * ‖d‖ ≤ L * t * ‖d‖ ^ 2 := by
      have hmul' :
          ‖grad zt - grad x‖ * ‖d‖ ≤
            (L * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
      calc
        ‖grad zt - grad x‖ * ‖d‖
            ≤ (L * (t * ‖d‖)) * ‖d‖ := hmul'
        _ = L * t * ‖d‖ ^ 2 := by ring
    have hdiff_le :
        ⟪grad zt, d⟫_ℝ - ⟪grad x, d⟫_ℝ ≤
          L * t * ‖d‖ ^ 2 := by
      calc
        ⟪grad zt, d⟫_ℝ - ⟪grad x, d⟫_ℝ
            = ⟪grad zt - grad x, d⟫_ℝ := hinner_diff
        _ ≤ ‖grad zt - grad x‖ * ‖d‖ := hcs
        _ ≤ L * t * ‖d‖ ^ 2 := hmul
    linarith
  let phi : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ
    else 0
  have hderiv_phi : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg (phi t) s t := by
    intro t ht
    rw [show phi t =
        ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ by
      dsimp [phi]
      rw [dif_pos ht]]
    exact hderiv t ht
  have hbound_phi : ∀ (t : ℝ) (ht : t ∈ s),
      phi t ≤ ⟪grad x, d⟫_ℝ + (L * ‖d‖ ^ 2) * t := by
    intro t ht
    have hb := hbound t ht
    rw [show phi t =
        ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ by
      dsimp [phi]
      rw [dif_pos ht]]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hb
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪grad x, d⟫_ℝ + (L * ‖d‖ ^ 2) / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg phi
      ⟪grad x, d⟫_ℝ (L * ‖d‖ ^ 2) hderiv_phi hbound_phi
  rw [hF0, hF1] at hscalar
  change f y ≤ f x + ⟪grad x, y.1 - x.1⟫_ℝ +
    (L / 2) * ‖y.1 - x.1‖ ^ 2
  rw [show d = y.1 - x.1 by rfl] at hscalar
  calc
    f y ≤ f x + ⟪grad x, y.1 - x.1⟫_ℝ +
        (L * ‖y.1 - x.1‖ ^ 2) / 2 := hscalar
    _ = f x + ⟪grad x, y.1 - x.1⟫_ℝ +
        (L / 2) * ‖y.1 - x.1‖ ^ 2 := by ring


/-- The canonical carrier gradient lives in the direction of the carrier affine span.

This is a model-transport fact for the chart proof of Lan Lemma 5.8.  Considered
`SOptLib.vsub_mem_carrierAffineSpan_direction`, which covers feasible point
differences but not the selected gradient vector; unfolding
`SOptLib.carrierGradientFrom` gives the chart gradient included through the
direction-submodule map, which is exactly the needed range statement. -/
private theorem carrierGradient_mem_affineSpan_direction
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (x : {x : E // x ∈ X}) :
    SOptLib.carrierGradient X f x ∈ (affineSpan ℝ X).direction := by
  classical
  unfold SOptLib.carrierGradient SOptLib.carrierGradientFrom
  simp


/-- Support plus a quadratic upper model identify the selected carrier gradient
as the within-gradient of the totalized carrier objective.

This is the differentiability-realization step in the chart-safe route for Lan
Lemma 5.8.  Search audit: considered
`hasFDerivWithinAt_of_contDiffOn_gradientWithin_comp`,
`Convex.carrier_smooth_quadratic_upper_bound`,
`carrierGradient_inner_eq_fderivWithin_on_feasible_direction`, and
`carrierChart_fderivWithin_eq_intrinsicInterior_fderivWithin_on_feasible_direction`;
they either require a `ContDiffOn`/ambient representative hypothesis, give only
the smooth upper model, or identify an already-existing derivative rather than
constructing one from support plus the quadratic remainder bound. -/
private theorem carrier_support_upper_hasGradientWithinAt
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (L : ℝ)
    (hsupport :
      ∀ x z : {x : E // x ∈ X},
        0 ≤ f z - f x - ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ)
    (hupper :
      ∀ x y : {x : E // x ∈ X},
        f y ≤ f x + ⟪SOptLib.carrierGradient X f x, y.1 - x.1⟫_ℝ +
          (L / 2) * ‖y.1 - x.1‖ ^ 2) :
    ∀ x : {x : E // x ∈ X},
      HasGradientWithinAt (SOptLib.totalizeOn X f)
        (SOptLib.carrierGradient X f x) X x.1 := by
  intro x
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt]
  have hbig :
      (fun y : E =>
        SOptLib.totalizeOn X f y - SOptLib.totalizeOn X f x.1 -
          (innerSL ℝ (SOptLib.carrierGradient X f x)) (y - x.1))
        =O[𝓝[X] x.1] (fun y : E => ‖y - x.1‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound ‖L / 2‖ ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    let r : ℝ :=
      f ⟨y, hy⟩ - f x - ⟪SOptLib.carrierGradient X f x, y - x.1⟫_ℝ
    have hres_nonneg : 0 ≤ r := by
      simpa [r] using hsupport x ⟨y, hy⟩
    have hres_upper : r ≤ (L / 2) * ‖y - x.1‖ ^ 2 := by
      have h := hupper x ⟨y, hy⟩
      calc
        r ≤ (f x + ⟪SOptLib.carrierGradient X f x, y - x.1⟫_ℝ +
              (L / 2) * ‖y - x.1‖ ^ 2) - f x -
              ⟪SOptLib.carrierGradient X f x, y - x.1⟫_ℝ := by
          simpa [r] using
            (sub_le_sub_right
              (sub_le_sub_right h (f x))
              ⟪SOptLib.carrierGradient X f x, y - x.1⟫_ℝ)
        _ = (L / 2) * ‖y - x.1‖ ^ 2 := by ring
    have hres_eq :
        SOptLib.totalizeOn X f y - SOptLib.totalizeOn X f x.1 -
            (innerSL ℝ (SOptLib.carrierGradient X f x)) (y - x.1) = r := by
      simp [r, SOptLib.totalizeOn_of_mem X f hy,
        SOptLib.totalizeOn_of_mem X f x.2, innerSL]
    have hnorm_res : ‖r‖ ≤ ‖L / 2‖ * ‖y - x.1‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hres_nonneg]
      exact hres_upper.trans
        (mul_le_mul_of_nonneg_right (le_abs_self (L / 2)) (sq_nonneg ‖y - x.1‖))
    simpa [← hres_eq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x.1‖)]
      using hnorm_res
  have hsub_tendsto :
      Filter.Tendsto (fun y : E => y - x.1) (𝓝[X] x.1) (𝓝 (0 : E)) := by
    have hcont :
        ContinuousWithinAt (fun y : E => y - x.1) X x.1 :=
      ((continuous_id.sub (continuous_const : Continuous fun _ : E => x.1)).continuousWithinAt
        (x := x.1) (s := X))
    simpa using hcont.tendsto
  have hquad :
      (fun y : E => ‖y - x.1‖ ^ 2) =o[𝓝[X] x.1] (fun y : E => y - x.1) := by
    simpa using
      ((Asymptotics.isLittleO_norm_pow_id (E' := E) (n := 2)
        (by norm_num : 1 < 2)).comp_tendsto hsub_tendsto)
  exact HasFDerivWithinAt.of_isLittleO (hbig.trans_isLittleO hquad)


/-- Carrier value and selected-gradient continuity from support, smooth upper
model, and a pointwise Lipschitz gradient bound.

This is the boundary-continuity input for the constrained Lan Lemma 5.8 bridge.
Search audit: considered `lipschitzWith_of_norm_sub_le_mul`,
`lipschitzOn_of_forall_subgradient_norm_le`,
`carrierBregmanDivergence_continuous`, and
`carrierGradient_continuous_of_carrierContDiffOn`; they either package only the
gradient Lipschitz side, require a bundled `ContDiffOn` carrier hypothesis, or
work for carrier Bregman data rather than the abstract `ψ`/`G` semantics here.
The proof should combine `hGLip` for `G` with the support/upper-model sandwich
`0 ≤ ψ y - ψ a - ⟪G a, y-a⟫ ≤ (L/2)‖y-a‖²` for `ψ`. -/
private theorem constrained_value_and_gradient_continuity_on_carrier
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ψ : H → ℝ) (G : H → H) (T : Set H) (L : ℝ)
    (hsupport : ∀ u ∈ T, ∀ v ∈ T,
      0 ≤ ψ v - ψ u - ⟪G u, v - u⟫_ℝ)
    (hgrad : ∀ u ∈ T, HasGradientWithinAt ψ (G u) T u)
    (hupper : ∀ a ∈ T, ∀ b ∈ T,
      ψ b ≤ ψ a + ⟪G a, b - a⟫_ℝ + (L / 2) * ‖b - a‖ ^ 2)
    (hGLip : ∀ u ∈ T, ∀ v ∈ T, ‖G u - G v‖ ≤ L * ‖u - v‖) :
    ∀ a ∈ T, ContinuousWithinAt ψ T a ∧ ContinuousWithinAt G T a := by
  intro a ha
  constructor
  · exact (hgrad a ha).continuousWithinAt
  · have hLip : LipschitzWith (Real.toNNReal L) (fun x : T => G x.1) := by
      exact lipschitzWith_of_norm_sub_le_mul (fun x : T => G x.1) L (by
        intro x y
        calc
          ‖G x.1 - G y.1‖ ≤ L * ‖x.1 - y.1‖ := hGLip x.1 x.2 y.1 y.2
          _ = L * dist x y := by simp [Subtype.dist_eq, dist_eq_norm])
    have hcont_sub : ContinuousAt (fun x : T => G x.1) ⟨a, ha⟩ :=
      hLip.continuous.continuousAt
    rw [continuousWithinAt_iff_continuousAt_restrict]
    exact hcont_sub


/-- Extend the shifted Baillon-Haddad inequality from the intrinsic interior to
the carrier boundary by finite-dimensional relative-interior density.

This is the boundary-continuity step needed by Lan Lemma 5.8 after the paper's
`X ⊆ ℝ^m` setting is exposed as `[FiniteDimensional ℝ H]`. Search audit:
checked `subset_closure_intrinsicInterior_of_nonempty_convex`,
`dense_subtype_of_subset_closure`, `le_of_continuousOn_of_dense_le`, and
`nonneg_of_continuousOn_of_dense_nonneg`; these provide exactly the dense-order
extension, while the local proof only packages the continuity of the residual
`2LΦ - ‖B‖²` on the carrier subtype. -/
private theorem constrained_baillon_haddad_boundary_extension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (Φ : H → ℝ) (B : H → H) (T : Set H) (L : ℝ)
    (hTconv : Convex ℝ T)
    (hcont : ∀ a ∈ T, ContinuousWithinAt Φ T a ∧ ContinuousWithinAt B T a)
    (hint :
      ∀ u ∈ intrinsicInterior ℝ T,
        ‖B u‖ ^ 2 ≤ 2 * L * Φ u)
    (x : H) (hx : x ∈ T) :
    ‖B x‖ ^ 2 ≤ 2 * L * Φ x := by
  classical
  let α := {y : H // y ∈ T}
  have hΦon : ContinuousOn Φ T := by
    intro y hy
    exact (hcont y hy).1
  have hBon : ContinuousOn B T := by
    intro y hy
    exact (hcont y hy).2
  have hΦcont : Continuous (fun y : α => Φ y.1) := by
    exact continuous_subtype_of_continuousOn_ambient
      (fun y : α => Φ y.1) Φ hΦon (by intro y; rfl)
  have hBcont : Continuous (fun y : α => B y.1) := by
    exact continuous_subtype_of_continuousOn_ambient
      (fun y : α => B y.1) B hBon (by intro y; rfl)
  have hres_cont :
      ContinuousOn
        (fun y : α => (2 * L * Φ y.1) - ‖B y.1‖ ^ 2)
        Set.univ := by
    have hleft : Continuous (fun y : α => 2 * L * Φ y.1) :=
      continuous_const.mul hΦcont
    have hright : Continuous (fun y : α => ‖B y.1‖ ^ 2) :=
      hBcont.norm.pow 2
    exact (hleft.sub hright).continuousOn
  have hTnonempty : T.Nonempty := ⟨x, hx⟩
  have hdense :
      Dense {y : α | (y : H) ∈ intrinsicInterior ℝ T} := by
    exact dense_subtype_of_subset_closure
      (X := T) (U := intrinsicInterior ℝ T)
      intrinsicInterior_subset
      (subset_closure_intrinsicInterior_of_nonempty_convex hTconv hTnonempty)
  have hle_sub :
      (fun y : α => ‖B y.1‖ ^ 2) ⟨x, hx⟩ ≤
        (fun y : α => 2 * L * Φ y.1) ⟨x, hx⟩ := by
    exact le_of_continuousOn_of_dense_le
      (f := fun y : α => 2 * L * Φ y.1)
      (g := fun y : α => ‖B y.1‖ ^ 2)
      (s := {y : α | (y : H) ∈ intrinsicInterior ℝ T})
      (by simpa using hres_cont)
      hdense
      (by
        intro y hy
        exact hint y.1 hy)
      ⟨x, hx⟩
  simpa using hle_sub

/-- Extend the pairwise shifted Baillon-Haddad residual in the second endpoint
from the intrinsic interior to the carrier boundary.

This packages the boundary step in Lan Lemma 5.8 after the first endpoint `x`
has already been fixed in the intrinsic interior. Search audit: reused
`constrained_baillon_haddad_boundary_extension`, after checking
`subset_closure_intrinsicInterior_of_nonempty_convex`,
`dense_subtype_of_subset_closure`, and `le_of_continuousOn_of_dense_le`; those
prove the dense boundary transport, while this helper only builds the continuous
residual `z ↦ 2L(Φ x - Φ z - ⟪B z,x-z⟫) - ‖B x-B z‖²`. -/
private theorem second_endpoint_boundary_extension_for_pairwise_gap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (Φ : H → ℝ) (B : H → H) (T : Set H) (L : ℝ)
    (hTconv : Convex ℝ T)
    (hcont : ∀ a ∈ T, ContinuousWithinAt Φ T a ∧ ContinuousWithinAt B T a)
    (x : H) (hx : x ∈ intrinsicInterior ℝ T)
    (hint :
      ∀ z ∈ intrinsicInterior ℝ T,
        ‖B x - B z‖ ^ 2 ≤
          2 * L * (Φ x - Φ z - ⟪B z, x - z⟫_ℝ))
    (z : H) (hz : z ∈ T) :
    ‖B x - B z‖ ^ 2 ≤
      2 * L * (Φ x - Φ z - ⟪B z, x - z⟫_ℝ) := by
  classical
  let Ψ : H → ℝ := fun y => Φ x - Φ y - ⟪B y, x - y⟫_ℝ
  let C : H → H := fun y => B x - B y
  have hcontΨC : ∀ a ∈ T, ContinuousWithinAt Ψ T a ∧ ContinuousWithinAt C T a := by
    intro a ha
    rcases hcont a ha with ⟨hΦ_cont, hB_cont⟩
    constructor
    · dsimp [Ψ]
      exact (continuousWithinAt_const.sub hΦ_cont).sub
        (hB_cont.inner (continuousWithinAt_const.sub continuousWithinAt_id))
    · dsimp [C]
      exact continuousWithinAt_const.sub hB_cont
  have hmain :
      ‖C z‖ ^ 2 ≤ 2 * L * Ψ z := by
    exact constrained_baillon_haddad_boundary_extension
      Ψ C T L hTconv hcontΨC
      (by
        intro y hy
        exact hint y hy)
      z hz
  simpa [Ψ, C] using hmain


/-
Retired legacy route.

The old canonical interval route tried to prove exact
Q-form absorption from the compressed canonical interval.  The scratch bridge
and skew-linear tests showed that this loses the signed split information needed
for the Q-level statement.  The active proof frontier is now
`source_named_splits_to_q_form_absorption_leaf`, which keeps the positive and
negative source split components available.

/-- Retired canonical source-work interval theorem.

This is the remaining finite reflected-mesh leaf.  It explicitly materializes
the actual averaged freezing-error normalization, the Lipschitz source budget,
the canonical two-sign work lower bound, and the correct signed mesh telescope.
The false absorbed-cross scaled inequality is not used. -/
private theorem retired_canonical_work_interval_to_q_form_absorption
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → ℝ) (B : H → H) (U : Set H) (L : ℝ)
    (hL_pos : 0 < L)
    (hsupport : ∀ x ∈ U, ∀ y ∈ U,
      0 ≤ Φ y - Φ x - ⟪B x, y - x⟫_ℝ)
    (hupper : ∀ x ∈ U, ∀ y ∈ U,
      Φ y ≤ Φ x + ⟪B x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2)
    (hBLip : ∀ x ∈ U, ∀ y ∈ U, ‖B x - B y‖ ≤ L * ‖x - y‖)
    {n : ℕ} (hn_pos : 0 < n) {τ : ℝ}
    (hτ_pos : 0 < τ)
    (d : H) (x g r : ℕ → H)
    (hx_mem_range : ∀ k ∈ Finset.range n, x k ∈ U)
    (hyPert_mem_pos :
      ∀ k, k ≤ n + 1 → reflectedPerturbedCycle L τ n x r k ∈ U)
    (hyPert_mem_neg :
      ∀ k, k ≤ n + 1 →
        reflectedPerturbedCycle L τ n x (fun j => -r j) k ∈ U)
    (hg : ∀ k, g k = B (x k))
    (hr :
      ∀ k ∈ Finset.range n,
        r k = (L / (n : ℝ)) • d - (g (k + 1) - g k))
    (hstep :
      ∀ k ∈ Finset.range n, x (k + 1) - x k = (1 / (n : ℝ)) • d)
    (hclose : x 0 - x n = -d)
    (hg0 : g 0 = 0)
    (hinterval :
      let baseStep : ℝ :=
        Finset.sum (Finset.range n)
            (fun k => ⟪L • x k, (1 / (n : ℝ)) • d⟫_ℝ) +
          ⟪L • x n, -d⟫_ℝ
      let predSkewNF : ℝ :=
        τ * ((1 / L) *
          ((⟪g n - g 0, r 0⟫_ℝ -
            ⟪(L • x n - g n) - (L • x 0 - g 0), r 0⟫_ℝ) +
            Finset.sum (Finset.range (n - 1))
              (fun k =>
                ⟪r k - (L / (n : ℝ)) • d, r (k + 1)⟫_ℝ -
                  ⟪-r k, r (k + 1)⟫_ℝ)))
      let residualPosNF : ℝ :=
        τ * ((1 / (n : ℝ)) *
            Finset.sum (Finset.range n) (fun k => ⟪r k, d⟫_ℝ)) +
          τ ^ 2 * (1 / L) *
            (Finset.sum (Finset.range (n - 1))
                (fun k => ⟪r k, r (k + 1) - r k⟫_ℝ) -
              ‖r (n - 1)‖ ^ 2)
      let residualNegNF : ℝ :=
        -(τ * ((1 / (n : ℝ)) *
            Finset.sum (Finset.range n) (fun k => ⟪r k, d⟫_ℝ))) +
          τ ^ 2 * (1 / L) *
            (Finset.sum (Finset.range (n - 1))
                (fun k => ⟪r k, r (k + 1) - r k⟫_ℝ) -
              ‖r (n - 1)‖ ^ 2)
      let canonicalDriftError : ℝ :=
        Finset.sum (Finset.range (n - 1))
            (fun k =>
              ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
                  (1 / (n : ℝ)) • d⟫_ℝ -
                ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
                  (1 / (n : ℝ)) • d⟫_ℝ) +
          (⟪B (reflectedPerturbedCycle L τ n x r (n - 1)) - g (n - 1),
              (1 / (n : ℝ)) • d⟫_ℝ -
            ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) (n - 1)) -
                g (n - 1),
              (1 / (n : ℝ)) • d⟫_ℝ)
      let canonicalOscillationError : ℝ :=
        Finset.sum (Finset.range (n - 1))
            (fun k =>
              ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
                  (1 / L) • (r (k + 1) - r k)⟫_ℝ +
                ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
                  (1 / L) • (r (k + 1) - r k)⟫_ℝ) -
          (⟪B (reflectedPerturbedCycle L τ n x r (n - 1)) - g (n - 1),
              (1 / L) • r (n - 1)⟫_ℝ +
            ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) (n - 1)) -
                g (n - 1),
              (1 / L) • r (n - 1)⟫_ℝ)
      (baseStep - predSkewNF + residualPosNF ≤
          canonicalDriftError + τ * canonicalOscillationError) ∧
        (canonicalDriftError + τ * canonicalOscillationError ≤
          -(baseStep + predSkewNF + residualNegNF)))
    {Rsum Q Eavg : ℝ}
    (hRsum_def :
      Rsum = Finset.sum (Finset.range n) (fun k => ⟪g k, r k⟫_ℝ))
    (hQ_def :
      Q = Finset.sum (Finset.range n) (fun k => ‖g (k + 1) - g k‖ ^ 2))
    (hEavg_def :
      Eavg =
        (Finset.sum (Finset.range n)
            (fun k =>
              ‖(1 / L) •
                (B (reflectedPerturbedCycle L τ n x r k) - g k)‖) +
          Finset.sum (Finset.range n)
            (fun k =>
              ‖(1 / L) •
                (B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) -
                  g k)‖)) /
          2) :
    0 ≤ 2 * Rsum + Q + Eavg := by
  classical
  have hτ_nonneg : 0 ≤ τ := le_of_lt hτ_pos
  have hcanonical_error_context :=
    canonical_reflected_error_context
      (H := H) hn_pos L τ d B x g r hstep hEavg_def
  have hcanonical_pos_edge := hcanonical_error_context.1
  have hcanonical_neg_edge := hcanonical_error_context.2.1
  have hEavg_nonneg := hcanonical_error_context.2.2
  have hcanonical_Eavg_budget_from_source :
      Eavg ≤
        τ * Finset.sum (Finset.range n)
          (fun k => ‖(1 / L) • r k‖) := by
    rw [hEavg_def]
    exact
      canonical_reflected_error_average_le_lipschitz_budget
        B U L τ hL_pos hτ_nonneg x g r hx_mem_range
        hyPert_mem_pos hyPert_mem_neg hg hBLip
  have hmesh_sub_q_endpoint :
      2 * Rsum - Q =
        2 * L *
            ((1 / (n : ℝ)) *
              Finset.sum (Finset.range n) (fun k => ⟪g k, d⟫_ℝ)) -
          ‖g n‖ ^ 2 :=
    mesh_rsum_sub_q_endpoint_identity
      (H := H) d L g r hg0 hr hRsum_def hQ_def
  have hmesh_plus_q_endpoint :
      2 * Rsum + Q =
        2 * L *
            ((1 / (n : ℝ)) *
              Finset.sum (Finset.range n) (fun k => ⟪g k, d⟫_ℝ)) -
          ‖g n‖ ^ 2 + 2 * Q :=
    mesh_rsum_plus_q_endpoint_identity
      (H := H) d L g r hg0 hr hRsum_def hQ_def
  have htwo_sign_work :
      let pairNorm : ℕ → ℝ := fun k =>
        ‖(1 / L) • (B (reflectedPerturbedCycle L τ n x r k) - g k)‖ +
          ‖(1 / L) •
            (B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k)‖
      let driftPart : ℝ :=
        Finset.sum (Finset.range (n - 1))
            (fun k =>
              ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
                  (1 / (n : ℝ)) • d⟫_ℝ -
                ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
                  (1 / (n : ℝ)) • d⟫_ℝ) +
          (⟪B (reflectedPerturbedCycle L τ n x r (n - 1)) - g (n - 1),
              (1 / (n : ℝ)) • d⟫_ℝ -
            ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) (n - 1)) -
                g (n - 1),
              (1 / (n : ℝ)) • d⟫_ℝ)
      let oscillationWeight : ℝ :=
        Finset.sum (Finset.range (n - 1))
            (fun k => pairNorm k * ‖r (k + 1) - r k‖) +
          pairNorm (n - 1) * ‖r (n - 1)‖
      Finset.sum (Finset.range n) pairNorm = 2 * Eavg ∧
        -(τ * oscillationWeight) ≤
          ((Finset.sum (Finset.range n)
              (fun k =>
                ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
                  reflectedPerturbedCycle L τ n x r (k + 1) -
                    reflectedPerturbedCycle L τ n x r k⟫_ℝ)) -
            (Finset.sum (Finset.range n)
              (fun k =>
                ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
                  reflectedPerturbedCycle L τ n x (fun j => -r j) (k + 1) -
                    reflectedPerturbedCycle L τ n x (fun j => -r j) k⟫_ℝ))) -
            driftPart := by
    exact
      canonical_two_sign_error_work_lower_bound
        (hn_pos := hn_pos) (hL_pos := hL_pos) (hτ_nonneg := hτ_nonneg)
        d B x g r
        (Eavg := Eavg)
        hEavg_def hcanonical_pos_edge hcanonical_neg_edge
  let baseStep : ℝ :=
    Finset.sum (Finset.range n)
        (fun k => ⟪L • x k, (1 / (n : ℝ)) • d⟫_ℝ) +
      ⟪L • x n, -d⟫_ℝ
  let predSkewNF : ℝ :=
    τ * ((1 / L) *
      ((⟪g n - g 0, r 0⟫_ℝ -
        ⟪(L • x n - g n) - (L • x 0 - g 0), r 0⟫_ℝ) +
        Finset.sum (Finset.range (n - 1))
          (fun k =>
            ⟪r k - (L / (n : ℝ)) • d, r (k + 1)⟫_ℝ -
              ⟪-r k, r (k + 1)⟫_ℝ)))
  let residualPosNF : ℝ :=
    τ * ((1 / (n : ℝ)) *
        Finset.sum (Finset.range n) (fun k => ⟪r k, d⟫_ℝ)) +
      τ ^ 2 * (1 / L) *
        (Finset.sum (Finset.range (n - 1))
            (fun k => ⟪r k, r (k + 1) - r k⟫_ℝ) -
          ‖r (n - 1)‖ ^ 2)
  let residualNegNF : ℝ :=
    -(τ * ((1 / (n : ℝ)) *
        Finset.sum (Finset.range n) (fun k => ⟪r k, d⟫_ℝ))) +
      τ ^ 2 * (1 / L) *
        (Finset.sum (Finset.range (n - 1))
            (fun k => ⟪r k, r (k + 1) - r k⟫_ℝ) -
          ‖r (n - 1)‖ ^ 2)
  let canonicalDriftError : ℝ :=
    Finset.sum (Finset.range (n - 1))
        (fun k =>
          ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
              (1 / (n : ℝ)) • d⟫_ℝ -
            ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
              (1 / (n : ℝ)) • d⟫_ℝ) +
      (⟪B (reflectedPerturbedCycle L τ n x r (n - 1)) - g (n - 1),
          (1 / (n : ℝ)) • d⟫_ℝ -
        ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) (n - 1)) -
            g (n - 1),
          (1 / (n : ℝ)) • d⟫_ℝ)
  let canonicalOscillationError : ℝ :=
    Finset.sum (Finset.range (n - 1))
        (fun k =>
          ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
              (1 / L) • (r (k + 1) - r k)⟫_ℝ +
            ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
              (1 / L) • (r (k + 1) - r k)⟫_ℝ) -
      (⟪B (reflectedPerturbedCycle L τ n x r (n - 1)) - g (n - 1),
          (1 / L) • r (n - 1)⟫_ℝ +
        ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) (n - 1)) -
            g (n - 1),
          (1 / L) • r (n - 1)⟫_ℝ)
  let canonicalErrorWork_pos : ℝ :=
    Finset.sum (Finset.range n)
      (fun k =>
        ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
          reflectedPerturbedCycle L τ n x r (k + 1) -
            reflectedPerturbedCycle L τ n x r k⟫_ℝ)
  let canonicalErrorWork_neg : ℝ :=
    Finset.sum (Finset.range n)
      (fun k =>
        ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
          reflectedPerturbedCycle L τ n x (fun j => -r j) (k + 1) -
            reflectedPerturbedCycle L τ n x (fun j => -r j) k⟫_ℝ)
  have hcanonical_defect_interval :
      (baseStep - predSkewNF + residualPosNF ≤
          canonicalDriftError + τ * canonicalOscillationError) ∧
        (canonicalDriftError + τ * canonicalOscillationError ≤
          -(baseStep + predSkewNF + residualNegNF)) := by
    simpa [baseStep, predSkewNF, residualPosNF, residualNegNF,
      canonicalDriftError, canonicalOscillationError] using hinterval
  have hcanonical_signed_edge :
      canonicalDriftError + τ * canonicalOscillationError =
        canonicalErrorWork_pos - canonicalErrorWork_neg := by
    exact
      signed_defect_edge_reconstruction_from_edges
        L τ d B g r
        (reflectedPerturbedCycle L τ n x r)
        (reflectedPerturbedCycle L τ n x (fun j => -r j))
        (hdriftError_def := rfl)
        (hoscillationError_def := rfl)
        hcanonical_pos_edge hcanonical_neg_edge
  have hcanonical_errorwork_interval :
      (baseStep - predSkewNF + residualPosNF ≤
          canonicalErrorWork_pos - canonicalErrorWork_neg) ∧
        (canonicalErrorWork_pos - canonicalErrorWork_neg ≤
          -(baseStep + predSkewNF + residualNegNF)) := by
    constructor
    · rw [← hcanonical_signed_edge]
      exact hcanonical_defect_interval.1
    · rw [← hcanonical_signed_edge]
      exact hcanonical_defect_interval.2
  have hx_succ_mem :
      ∀ k ∈ Finset.range n, x (k + 1) ∈ U := by
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    by_cases hksucc : k + 1 < n
    · exact hx_mem_range (k + 1) (Finset.mem_range.mpr hksucc)
    · have hkeq : k + 1 = n := by omega
      have hy := hyPert_mem_pos n (by omega)
      have hyn : reflectedPerturbedCycle L τ n x r n = x n := by
        simp [reflectedPerturbedCycle]
      simpa [hkeq, hyn] using hy
  have hsource_monotone :
      ∀ k ∈ Finset.range n,
        0 ≤ ⟪g (k + 1) - g k, x (k + 1) - x k⟫_ℝ := by
    intro k hk
    have hxk : x k ∈ U := hx_mem_range k hk
    have hxk1 : x (k + 1) ∈ U := hx_succ_mem k hk
    have hs_forward := hsupport (x k) hxk (x (k + 1)) hxk1
    have hs_backward := hsupport (x (k + 1)) hxk1 (x k) hxk
    have hsum := add_nonneg hs_forward hs_backward
    have hrewrite :
        (Φ (x (k + 1)) - Φ (x k) -
              ⟪B (x k), x (k + 1) - x k⟫_ℝ) +
            (Φ (x k) - Φ (x (k + 1)) -
              ⟪B (x (k + 1)), x k - x (k + 1)⟫_ℝ) =
          ⟪B (x (k + 1)) - B (x k),
            x (k + 1) - x k⟫_ℝ := by
      have hback : x k - x (k + 1) = -(x (k + 1) - x k) := by
        abel
      rw [hback, inner_neg_right]
      simp [inner_sub_left]
      ring
    have hmonoB :
        0 ≤ ⟪B (x (k + 1)) - B (x k),
          x (k + 1) - x k⟫_ℝ := by
      simpa [hrewrite] using hsum
    simpa [hg (k + 1), hg k] using hmonoB
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ_def]
    exact Finset.sum_nonneg (by
      intro k hk
      exact sq_nonneg _)
  have hQ_mesh_budget :
      Q ≤ L ^ 2 * ‖d‖ ^ 2 / (n : ℝ) := by
    rw [hQ_def]
    exact
      gradient_increment_energy_le_lipschitz_uniform_mesh_budget
        B U L hL_pos hn_pos d x g hBLip hg
        hx_mem_range hx_succ_mem hstep
  have hendpoint :
      ‖g n‖ ^ 2 ≤
        2 * L *
            ((1 / (n : ℝ)) *
              Finset.sum (Finset.range n) (fun k => ⟪g k, d⟫_ℝ)) +
          2 * Q + Eavg := by
    -- Endpoint-slack frontier for Lan Lemma 5.8: this is the remaining
    -- source-preserving reflected two-sign absorption, with the canonical
    -- interval, actual two-sign freezing work, and source Eavg budget all
    -- kept visible for the finite Hilbert/Finset normalization.
    have hwork_interval_visible := hcanonical_errorwork_interval
    have htwo_sign_visible := htwo_sign_work
    have hbudget_visible := hcanonical_Eavg_budget_from_source
    have hmesh_visible := hmesh_plus_q_endpoint
    have hresidual_sum_nonpos :
        residualPosNF + residualNegNF ≤ 0 := by
      exact
        residual_nf_pair_sum_nonpos_of_defs
          (H := H) hn_pos hL_pos d r
          (hresidualPosNF_def := rfl) (hresidualNegNF_def := rfl)
    have hinterval_cancel :
        2 * baseStep + residualPosNF + residualNegNF ≤ 0 := by
      linarith only [hwork_interval_visible.1, hwork_interval_visible.2]
    -- Concrete remaining obstruction: identify the endpoint defect
    -- `‖g n‖² - (2L/n) Σ⟪g k,d⟫ - 2Q` with the signed reflected
    -- defect controlled by `hwork_interval_visible` and `htwo_sign_visible`,
    -- while preserving the actual `Eavg` rather than replacing it by the
    -- one-sided Lipschitz upper budget.
    let pairNorm_visible : ℕ → ℝ := fun k =>
      ‖(1 / L) •
          (B (reflectedPerturbedCycle L τ n x r k) - g k)‖ +
        ‖(1 / L) •
          (B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) -
            g k)‖
    let driftPart_visible : ℝ :=
      Finset.sum (Finset.range (n - 1))
          (fun k =>
            ⟪B (reflectedPerturbedCycle L τ n x r k) - g k,
                (1 / (n : ℝ)) • d⟫_ℝ -
              ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) k) - g k,
                (1 / (n : ℝ)) • d⟫_ℝ) +
        (⟪B (reflectedPerturbedCycle L τ n x r (n - 1)) - g (n - 1),
            (1 / (n : ℝ)) • d⟫_ℝ -
          ⟪B (reflectedPerturbedCycle L τ n x (fun j => -r j) (n - 1)) -
              g (n - 1),
            (1 / (n : ℝ)) • d⟫_ℝ)
    let oscillationWeight_visible : ℝ :=
      Finset.sum (Finset.range (n - 1))
          (fun k => pairNorm_visible k * ‖r (k + 1) - r k‖) +
        pairNorm_visible (n - 1) * ‖r (n - 1)‖
    have hpairNorm_sum_visible :
        Finset.sum (Finset.range n) pairNorm_visible = 2 * Eavg := by
      exact htwo_sign_visible.1
    have hfreezing_lower_visible :
        -(τ * oscillationWeight_visible) ≤
          (canonicalErrorWork_pos - canonicalErrorWork_neg) -
            driftPart_visible := by
      exact htwo_sign_visible.2
    have habsorbed_upper_visible :
        canonicalDriftError - τ * oscillationWeight_visible ≤
          -(baseStep + predSkewNF + residualNegNF) := by
      have hdrift_visible_eq : driftPart_visible = canonicalDriftError := by
        dsimp [driftPart_visible, canonicalDriftError]
      have hfreezing_canonical :
          -(τ * oscillationWeight_visible) ≤
            (canonicalErrorWork_pos - canonicalErrorWork_neg) -
              canonicalDriftError := by
        rw [← hdrift_visible_eq]
        exact hfreezing_lower_visible
      linarith only [hfreezing_canonical, hwork_interval_visible.2]
    have hsource_mesh_work_nonneg :
        0 ≤ Finset.sum (Finset.range n)
          (fun k => ⟪g (k + 1) - g k, (L / (n : ℝ)) • d⟫_ℝ) := by
      refine Finset.sum_nonneg ?_
      intro k hk
      have hmono_step :
          0 ≤ ⟪g (k + 1) - g k, (1 / (n : ℝ)) • d⟫_ℝ := by
        simpa [hstep k hk] using hsource_monotone k hk
      have hscale :
          ⟪g (k + 1) - g k, (L / (n : ℝ)) • d⟫_ℝ =
            L * ⟪g (k + 1) - g k, (1 / (n : ℝ)) • d⟫_ℝ := by
        simp [inner_smul_right]
        ring
      rw [hscale]
      exact mul_nonneg (le_of_lt hL_pos) hmono_step
    have hsource_residual_mesh_nonneg :
        0 ≤ Finset.sum (Finset.range n)
          (fun k =>
            ⟪(L / (n : ℝ)) • d - r k, (L / (n : ℝ)) • d⟫_ℝ) := by
      refine hsource_mesh_work_nonneg.trans_eq ?_
      apply Finset.sum_congr rfl
      intro k hk
      have hrk := hr k hk
      have hdelta :
        g (k + 1) - g k = (L / (n : ℝ)) • d - r k := by
        rw [hrk]
        abel
      rw [hdelta]
    have hsource_residual_mesh_nf :
        0 ≤
          L ^ 2 * ‖d‖ ^ 2 / (n : ℝ) -
            Finset.sum (Finset.range n)
              (fun k => ⟪r k, (L / (n : ℝ)) • d⟫_ℝ) := by
      let a : H := (L / (n : ℝ)) • d
      have hsum_expand :
          Finset.sum (Finset.range n)
              (fun k => ⟪a - r k, a⟫_ℝ) =
            Finset.sum (Finset.range n) (fun _ : ℕ => ⟪a, a⟫_ℝ) -
              Finset.sum (Finset.range n) (fun k => ⟪r k, a⟫_ℝ) := by
        simp [Finset.sum_sub_distrib, inner_sub_left]
      have hconst :
          Finset.sum (Finset.range n) (fun _ : ℕ => ⟪a, a⟫_ℝ) =
            L ^ 2 * ‖d‖ ^ 2 / (n : ℝ) := by
        have hnR_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn_pos)
        have hnorm_a :
            ‖a‖ = (L / (n : ℝ)) * ‖d‖ := by
          have hscale_nonneg : 0 ≤ L / (n : ℝ) := by positivity
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
        calc
          Finset.sum (Finset.range n) (fun _ : ℕ => ⟪a, a⟫_ℝ)
              = (n : ℝ) * ‖a‖ ^ 2 := by
                simp [real_inner_self_eq_norm_sq]
          _ = (n : ℝ) * ((L / (n : ℝ)) * ‖d‖) ^ 2 := by
                rw [hnorm_a]
          _ = L ^ 2 * ‖d‖ ^ 2 / (n : ℝ) := by
                field_simp [hnR_ne]
      have hsrc :
          0 ≤ Finset.sum (Finset.range n) (fun k => ⟪a - r k, a⟫_ℝ) := by
        simpa [a] using hsource_residual_mesh_nonneg
      rw [hsum_expand, hconst] at hsrc
      simpa [a] using hsrc
    have hpair_q :
        -(2 * Rsum + Q) ≤
          (1 / 2) * Finset.sum (Finset.range n) pairNorm_visible := by
      have hscaled_q : -(τ * Eavg) ≤ τ * (2 * Rsum + Q) := by
        have hfirst_unscaled : -(2 * Rsum + Q) ≤ Eavg := by
          -- T1 remains: prove the finite reflected-mesh absorption in the
          -- unscaled Q form from the absorbed canonical interval, the actual
          -- two-sign freezing lower bound, source residual mesh normal form,
          -- and route-local R/Q definitions.  This is the Hilbert/Finset
          -- signed-defect-to-Q bridge; downstream Q-form wrappers are not used
          -- at this declaration-order frontier.
          have habsorbed_core := habsorbed_upper_visible
          have hsource_core := hsource_residual_mesh_nf
          have hRsum_core := hRsum_def
          have hQ_core := hQ_def
          have hresidual_core := hresidual_sum_nonpos
          have hfreezing_core := hfreezing_lower_visible
          have hpair_core := hpairNorm_sum_visible
          have hbudget_core := hbudget_visible
          have hmesh_core := hmesh_visible
          legacy_placeholder
        have hfirst_scale : -Eavg ≤ 2 * Rsum + Q := by
          linarith only [hfirst_unscaled]
        exact
          scale_nonnegative_perturbation_first_variation
            (le_of_lt hτ_pos) hfirst_scale
      have hfirst_unscaled : -(2 * Rsum + Q) ≤ Eavg := by
        have hfirst_scale : -Eavg ≤ 2 * Rsum + Q :=
          positive_tau_cancel_scaled_q_absorption hτ_pos hscaled_q
        linarith only [hfirst_scale]
      exact
        pairnorm_q_slack_from_unscaled_eavg
          (n := n) (pairNorm := pairNorm_visible)
          (Rsum := Rsum) (Q := Q) (Eavg := Eavg)
          hfirst_unscaled hpairNorm_sum_visible
    have hqform : 0 ≤ 2 * Rsum + Q + Eavg :=
      pairnorm_sum_close_qform hpair_q hpairNorm_sum_visible
    have hendpoint' :
        ‖g n‖ ^ 2 ≤
          2 * L *
              ((1 / (n : ℝ)) *
                Finset.sum (Finset.range n) (fun k => ⟪g k, d⟫_ℝ)) +
            2 * Q + Eavg := by
      rw [hmesh_visible] at hqform
      linarith only [hqform]
    exact hendpoint'
  have hgoal_rewrite :
      2 * Rsum + Q + Eavg =
        (2 * L *
            ((1 / (n : ℝ)) *
              Finset.sum (Finset.range n) (fun k => ⟪g k, d⟫_ℝ)) -
          ‖g n‖ ^ 2 + 2 * Q) + Eavg := by
    rw [hmesh_plus_q_endpoint]
  rw [hgoal_rewrite]
  linarith only [hendpoint]
-/


/-! Retired reflected Q-form scaffold

The old named-split Q-form absorption chain has been removed from the main
proof path. Its theorem head did not carry the open-domain endpoint/cocoercive
information needed to prove the Q-form absorption, and the final Lemma 5.8 proof
now uses the carrier/open-chart Baillon-Haddad route below.
-/


/-! Retired before-endpoint reflected mesh scaffold

The fixed reflected-mesh route below depended on the retired named-split Q-form
absorption chain. The final Lemma 5.8 proof proceeds through the carrier/open
Baillon-Haddad transport, so these private before-endpoint wrappers are removed
from the checked proof path.
-/


/-! Compatibility bridges retained while retiring the old reflected chain.

These declarations resolve older private wrapper dependencies so the file can be
checked while the final Lemma 5.8 route is migrated to the carrier/open-domain
Baillon-Haddad terminal. They are not part of the public theorem surface.
-/


set_option maxHeartbeats 800000


/-- The carrier chart preserves differences through the ambient inclusion.

This is the affine-chart algebra used to transport Lan Lemma 5.8's support,
upper-model, and Lipschitz hypotheses. Search audit: considered the SOptLib
chart lemmas `carrierChartToAmbient`, `AffineSubspace.vaddConst_contLinear_eq_subtypeL`,
and `affineSpan_chartPoint_sub_subtypeL`; they provide the affine chart and
endpoint subtraction facts, but no imported lemma states this reusable
two-coordinate `carrierChartToAmbient` vsub form directly. -/
private theorem carrier_chart_to_ambient_vsub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (T : Set H) (anchor : {x : H // x ∈ T})
    (p q : (affineSpan ℝ T).direction) :
    ((q - p : (affineSpan ℝ T).direction) : H) =
      SOptLib.carrierChartToAmbient T anchor q -
        SOptLib.carrierChartToAmbient T anchor p := by
  classical
  let A : AffineSubspace ℝ H := affineSpan ℝ T
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ T anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ H) : Set H) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let Lchart : A.direction →ᴬ[ℝ] H := SOptLib.carrierChartToAmbient T anchor
  have hlin :
      Lchart.contLinear (q - p) = Lchart q - Lchart p := by
    simpa [vsub_eq_sub] using Lchart.contLinear_map_vsub q p
  have hcont : Lchart.contLinear = A.direction.subtypeL := by
    let a : A := ⟨anchor.1, subset_affineSpan ℝ T anchor.2⟩
    apply AffineSubspace.vaddConst_contLinear_eq_subtypeL a Lchart
    intro du
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        du : A) : H) = (du : H) + (a : H)
    simp
  calc
    ((q - p : A.direction) : H) = A.direction.subtypeL (q - p) := rfl
    _ = Lchart.contLinear (q - p) := by rw [hcont]
    _ = Lchart q - Lchart p := hlin

/-- Transport the intrinsic-interior carrier statement to the affine-span chart
and apply the open-chart Baillon-Haddad theorem.

This is the chart-reduction layer for Lan Lemma 5.8. Search audit: checked
`SOptLib.carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior`,
`SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet`,
`SOptLib.carrierChartSet_convex`, and `affineSpan_chartPoint_sub_subtypeL`;
these are exactly the chart membership/convexity/algebra primitives, but no
existing lemma packages the full support/upper/Lipschitz transport for an
abstract selected gradient `B`, so this helper isolates that transport from the
open analytic core. -/
private theorem intrinsic_pairwise_baillon_haddad_chart_transport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H]
    (Φ : H → ℝ) (B : H → H) (T : Set H) (L : ℝ)
    (hL_pos : 0 < L)
    (hTconv : Convex ℝ T)
    (hsupport : ∀ u ∈ T, ∀ v ∈ T,
      0 ≤ Φ v - Φ u - ⟪B u, v - u⟫_ℝ)
    (hupper : ∀ u ∈ T, ∀ v ∈ T,
      Φ v ≤ Φ u + ⟪B u, v - u⟫_ℝ + (L / 2) * ‖v - u‖ ^ 2)
    (hBdir : ∀ u ∈ T, B u ∈ (affineSpan ℝ T).direction)
    (hBLip : ∀ u ∈ T, ∀ v ∈ T, ‖B u - B v‖ ≤ L * ‖u - v‖)
    (himage : Convex ℝ (B '' intrinsicInterior ℝ T)) :
    ∀ u ∈ intrinsicInterior ℝ T, ∀ v ∈ intrinsicInterior ℝ T,
      ‖B u - B v‖ ^ 2 ≤
        2 * L * (Φ u - Φ v - ⟪B v, u - v⟫_ℝ) := by
  classical
  intro u hu v hv
  have huT : u ∈ T := intrinsicInterior_subset hu
  have hvT : v ∈ T := intrinsicInterior_subset hv
  let anchor : {x : H // x ∈ T} := ⟨u, huT⟩
  let A : AffineSubspace ℝ H := affineSpan ℝ T
  let Uc : Set A.direction := interior (SOptLib.carrierChartSet T anchor)
  let Lchart : A.direction →ᴬ[ℝ] H := SOptLib.carrierChartToAmbient T anchor
  let Φc : A.direction → ℝ := fun p => Φ (Lchart p)
  let Bc : A.direction → A.direction := fun p =>
    if hp : p ∈ Uc then
      ⟨B (Lchart p),
        hBdir (Lchart p)
          (intrinsicInterior_subset
            (SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
              T anchor (by simpa [Uc] using hp)))⟩
    else 0
  let uc : A.direction := SOptLib.carrierChartPoint T anchor ⟨u, huT⟩
  let vc : A.direction := SOptLib.carrierChartPoint T anchor ⟨v, hvT⟩
  have hUc_open : IsOpen Uc := by
    simpa [Uc] using isOpen_interior
  have hUc_conv : Convex ℝ Uc := by
    simpa [Uc] using (SOptLib.carrierChartSet_convex T anchor hTconv).interior
  have huc : uc ∈ Uc := by
    simpa [Uc, uc] using
      SOptLib.carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior
        T anchor ⟨u, huT⟩ hu
  have hvc : vc ∈ Uc := by
    simpa [Uc, vc] using
      SOptLib.carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior
        T anchor ⟨v, hvT⟩ hv
  have hsupport_c : ∀ p ∈ Uc, ∀ q ∈ Uc,
      0 ≤ Φc q - Φc p - ⟪Bc p, q - p⟫_ℝ := by
    intro p hp q hq
    have hpInt :
        Lchart p ∈ intrinsicInterior ℝ T := by
      exact SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hp)
    have hqInt :
        Lchart q ∈ intrinsicInterior ℝ T := by
      exact SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hq)
    have hpT : Lchart p ∈ T := intrinsicInterior_subset hpInt
    have hqT : Lchart q ∈ T := intrinsicInterior_subset hqInt
    have hsrc := hsupport (Lchart p) hpT (Lchart q) hqT
    have hsub :
        ((q - p : A.direction) : H) = Lchart q - Lchart p := by
      simpa [A, Lchart] using carrier_chart_to_ambient_vsub T anchor p q
    have hinner :
        ⟪Bc p, q - p⟫_ℝ =
          ⟪B (Lchart p), Lchart q - Lchart p⟫_ℝ := by
      simp [Bc, hp, hsub]
    simpa [Φc, hinner] using hsrc
  have hupper_c : ∀ p ∈ Uc, ∀ q ∈ Uc,
      Φc q ≤ Φc p + ⟪Bc p, q - p⟫_ℝ + (L / 2) * ‖q - p‖ ^ 2 := by
    intro p hp q hq
    have hpInt :
        Lchart p ∈ intrinsicInterior ℝ T := by
      exact SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hp)
    have hqInt :
        Lchart q ∈ intrinsicInterior ℝ T := by
      exact SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hq)
    have hpT : Lchart p ∈ T := intrinsicInterior_subset hpInt
    have hqT : Lchart q ∈ T := intrinsicInterior_subset hqInt
    have hsrc := hupper (Lchart p) hpT (Lchart q) hqT
    have hsub :
        ((q - p : A.direction) : H) = Lchart q - Lchart p := by
      simpa [A, Lchart] using carrier_chart_to_ambient_vsub T anchor p q
    have hinner :
        ⟪Bc p, q - p⟫_ℝ =
          ⟪B (Lchart p), Lchart q - Lchart p⟫_ℝ := by
      simp [Bc, hp, hsub]
    have hnorm : ‖q - p‖ = ‖Lchart q - Lchart p‖ := by
      rw [← hsub]
      rfl
    simpa [Φc, hinner, hnorm] using hsrc
  have hBLip_c : ∀ p ∈ Uc, ∀ q ∈ Uc,
      ‖Bc p - Bc q‖ ≤ L * ‖p - q‖ := by
    intro p hp q hq
    have hpInt :
        Lchart p ∈ intrinsicInterior ℝ T := by
      exact SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hp)
    have hqInt :
        Lchart q ∈ intrinsicInterior ℝ T := by
      exact SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hq)
    have hpT : Lchart p ∈ T := intrinsicInterior_subset hpInt
    have hqT : Lchart q ∈ T := intrinsicInterior_subset hqInt
    have hsrc := hBLip (Lchart p) hpT (Lchart q) hqT
    have hsub :
        ((p - q : A.direction) : H) = Lchart p - Lchart q := by
      simpa [A, Lchart] using carrier_chart_to_ambient_vsub T anchor q p
    have hnorm_right : ‖p - q‖ = ‖Lchart p - Lchart q‖ := by
      rw [← hsub]
      rfl
    simpa [Bc, hp, hq, hnorm_right] using hsrc
  have hBc_image : Convex ℝ (Bc '' Uc) := by
    intro a ha b hb α β hα hβ hsum
    rcases ha with ⟨p, hp, rfl⟩
    rcases hb with ⟨q, hq, rfl⟩
    have hpInt : Lchart p ∈ intrinsicInterior ℝ T :=
      SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hp)
    have hqInt : Lchart q ∈ intrinsicInterior ℝ T :=
      SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
        T anchor (by simpa [Uc] using hq)
    have hpImage : (Bc p : H) ∈ B '' intrinsicInterior ℝ T :=
      ⟨Lchart p, hpInt, by simp [Bc, hp]⟩
    have hqImage : (Bc q : H) ∈ B '' intrinsicInterior ℝ T :=
      ⟨Lchart q, hqInt, by simp [Bc, hq]⟩
    obtain ⟨w, hw, hBw⟩ := himage hpImage hqImage hα hβ hsum
    let wc : A.direction := SOptLib.carrierChartPoint T anchor
      ⟨w, intrinsicInterior_subset hw⟩
    have hwc : wc ∈ Uc := by
      simpa [wc, Uc] using
        SOptLib.carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior
          T anchor ⟨w, intrinsicInterior_subset hw⟩ hw
    have hLwc : Lchart wc = w := by
      simpa [wc, Lchart] using
        SOptLib.carrierChartToAmbient_chartPoint T anchor
          ⟨w, intrinsicInterior_subset hw⟩
    refine ⟨wc, hwc, ?_⟩
    apply Subtype.ext
    change (Bc wc : H) = α • (Bc p : H) + β • (Bc q : H)
    simpa only [Bc, dif_pos hwc, hLwc] using hBw
  have hsupport_c' : ∀ p ∈ Uc, ∀ q ∈ Uc,
      0 ≤ Φc p - Φc q - ⟪Bc q, p - q⟫_ℝ := by
    intro p hp q hq
    exact hsupport_c q hq p hp
  have hcoco := SOptLib.open_cocoercivity_of_support_upper_lipschitz
    Φc Bc Uc L hL_pos hUc_open hUc_conv hsupport_c' hupper_c hBLip_c
  have hopen := SOptLib.bregman_gap_of_cocoercive_convex_gradient_image
    Φc Bc Uc L hL_pos hsupport_c' hcoco hBc_image uc huc vc hvc
  have hLuc : Lchart uc = u := by
    simpa [Lchart, uc] using
      SOptLib.carrierChartToAmbient_chartPoint T anchor ⟨u, huT⟩
  have hLvc : Lchart vc = v := by
    simpa [Lchart, vc] using
      SOptLib.carrierChartToAmbient_chartPoint T anchor ⟨v, hvT⟩
  have hsub_uv : ((uc - vc : A.direction) : H) = u - v := by
    calc
      ((uc - vc : A.direction) : H) = Lchart uc - Lchart vc := by
        simpa [A, Lchart] using carrier_chart_to_ambient_vsub T anchor vc uc
      _ = u - v := by rw [hLuc, hLvc]
  have hinner_uv :
      ⟪Bc vc, uc - vc⟫_ℝ = ⟪B v, u - v⟫_ℝ := by
    simp [Bc, hvc, hLvc, hsub_uv]
  have hsub_uv' : (uc : H) - (vc : H) = u - v := by
    simpa using hsub_uv
  simpa [Φc, Bc, huc, hvc, hLuc, hLvc, hsub_uv'] using hopen


/-- Repaired single-sided carrier bound under convexity of the intrinsic
gradient image. Apply open-domain cocoercivity on the affine chart, use the
Wachsmuth--Wachsmuth gradient-image bridge, and extend both endpoints to the
boundary by continuity. The coefficient remains `1 / (2 * L)`. -/
private theorem carrierGradient_smooth_convex_gap_inequality
    {X : Set E} (F : E → ℝ) (f : {x : E // x ∈ X} → ℝ) (L : ℝ)
    (hL_pos : 0 < L)
    (hX : Convex ℝ X)
    (hconv : ConvexOn ℝ X F)
    (hdiff : DifferentiableOn ℝ F X)
    (hf : ∀ y : {x : E // x ∈ X}, f y = F y.1)
    (hsmooth : ∀ x y : {x : E // x ∈ X},
      SOptLib.dualNorm
          (SOptLib.carrierGradient X f x - SOptLib.carrierGradient X f y) ≤
        L * ‖x.1 - y.1‖)
    (himage : Convex ℝ
      ((SOptLib.totalizeOn X (SOptLib.carrierGradient X f)) '' intrinsicInterior ℝ X))
    (x z : {x : E // x ∈ X}) :
    (1 / (2 * L : ℝ)) *
        SOptLib.dualNorm
          (SOptLib.carrierGradient X f x - SOptLib.carrierGradient X f z) ^ 2 ≤
      f x - f z - ⟪SOptLib.carrierGradient X f z, x.1 - z.1⟫_ℝ := by
  have hsupport :
      ∀ x z : {x : E // x ∈ X},
        0 ≤ f z - f x - ⟪SOptLib.carrierGradient X f x, z.1 - x.1⟫_ℝ :=
    carrier_linearized_gap_nonneg_with_carrierGradient F f hX hconv hdiff hf
  have hupper :
      ∀ x y : {x : E // x ∈ X},
        f y ≤ f x + ⟪SOptLib.carrierGradient X f x, y.1 - x.1⟫_ℝ +
          (L / 2) * ‖y.1 - x.1‖ ^ 2 :=
    carrierGradient_smooth_upper_bound_from_diff_lipschitz
      F f L hX hdiff hf hsmooth
  have hgrad :
      ∀ y : {x : E // x ∈ X},
        HasGradientWithinAt (SOptLib.totalizeOn X f)
          (SOptLib.carrierGradient X f y) X y.1 :=
    carrier_support_upper_hasGradientWithinAt f L hsupport hupper
  have hsmooth_norm :
      ∀ x y : {x : E // x ∈ X},
        ‖SOptLib.carrierGradient X f x - SOptLib.carrierGradient X f y‖ ≤
          L * ‖x.1 - y.1‖ := by
    intro x y
    simpa [SOptLib.dualNorm_eq_norm] using hsmooth x y
  let Φ := SOptLib.totalizeOn X f
  let B := SOptLib.totalizeOn X (SOptLib.carrierGradient X f)
  have hsupport' : ∀ a ∈ X, ∀ b ∈ X,
      0 ≤ Φ b - Φ a - ⟪B a, b - a⟫_ℝ := by
    intro a ha b hb
    simpa [Φ, B, SOptLib.totalizeOn_of_mem X f ha,
      SOptLib.totalizeOn_of_mem X f hb,
      SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) ha] using
      hsupport ⟨a, ha⟩ ⟨b, hb⟩
  have hupper' : ∀ a ∈ X, ∀ b ∈ X,
      Φ b ≤ Φ a + ⟪B a, b - a⟫_ℝ + L / 2 * ‖b - a‖ ^ 2 := by
    intro a ha b hb
    simpa [Φ, B, SOptLib.totalizeOn_of_mem X f ha,
      SOptLib.totalizeOn_of_mem X f hb,
      SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) ha] using
      hupper ⟨a, ha⟩ ⟨b, hb⟩
  have hgrad' : ∀ a ∈ X, HasGradientWithinAt Φ (B a) X a := by
    intro a ha
    simpa [Φ, B, SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) ha] using
      hgrad ⟨a, ha⟩
  have hdir : ∀ a ∈ X, B a ∈ (affineSpan ℝ X).direction := by
    intro a ha
    simpa [B, SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) ha] using
      carrierGradient_mem_affineSpan_direction f ⟨a, ha⟩
  have hLip : ∀ a ∈ X, ∀ b ∈ X, ‖B a - B b‖ ≤ L * ‖a - b‖ := by
    intro a ha b hb
    simpa [B, SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) ha,
      SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) hb] using
      hsmooth_norm ⟨a, ha⟩ ⟨b, hb⟩
  have hcont := constrained_value_and_gradient_continuity_on_carrier
    Φ B X L hsupport' hgrad' hupper' hLip
  have hint := intrinsic_pairwise_baillon_haddad_chart_transport
    Φ B X L hL_pos hX hsupport' hupper' hdir hLip himage
  let Ψ : E → ℝ := fun a => Φ a - Φ z.1 - ⟪B z.1, a - z.1⟫_ℝ
  let C : E → E := fun a => B a - B z.1
  have hcontShift : ∀ a ∈ X,
      ContinuousWithinAt Ψ X a ∧ ContinuousWithinAt C X a := by
    intro a ha
    constructor
    · exact ((hcont a ha).1.sub continuousWithinAt_const).sub
        (continuousWithinAt_const.inner
          (continuousWithinAt_id.sub continuousWithinAt_const))
    · exact (hcont a ha).2.sub continuousWithinAt_const
  have hintShift : ∀ a ∈ intrinsicInterior ℝ X, ‖C a‖ ^ 2 ≤ 2 * L * Ψ a := by
    intro a ha
    exact second_endpoint_boundary_extension_for_pairwise_gap
      Φ B X L hX hcont a ha (hint a ha) z.1 z.2
  have hfinal := constrained_baillon_haddad_boundary_extension
    Ψ C X L hX hcontShift hintShift x.1 x.2
  have hfinal' : ‖SOptLib.carrierGradient X f x - SOptLib.carrierGradient X f z‖ ^ 2 ≤
      2 * L * (f x - f z - ⟪SOptLib.carrierGradient X f z, x.1 - z.1⟫_ℝ) := by
    simpa [Ψ, C, Φ, B, SOptLib.totalizeOn_of_mem X f x.2,
      SOptLib.totalizeOn_of_mem X f z.2,
      SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) x.2,
      SOptLib.totalizeOn_of_mem X (SOptLib.carrierGradient X f) z.2] using hfinal
  have hdiv : ‖SOptLib.carrierGradient X f x - SOptLib.carrierGradient X f z‖ ^ 2 /
      (2 * L) ≤ f x - f z - ⟪SOptLib.carrierGradient X f z, x.1 - z.1⟫_ℝ :=
    (div_le_iff₀ (show 0 < 2 * L by positivity)).mpr
      (by nlinarith [hfinal'])
  simpa [div_eq_mul_inv, mul_comm, SOptLib.dualNorm_eq_norm] using hdiv

/-- Carrier-level smooth model for each component function.

The source JSON states component smoothness and differentiability data here; the
separate component-convexity assumption is exposed by `setup.hcomponent_convex`
and consumed by the Lemma 5.12 route below. -/
private theorem component_carrier_smooth_model
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) (i : ι) :
    DifferentiableOn ℝ (setup.f i) setup.X ∧
      ∀ x y, x ∈ setup.X → y ∈ setup.X →
        SOptLib.dualNorm (setup.componentGrad i x - setup.componentGrad i y) ≤
          setup.Li i * ‖x - y‖ := by
  constructor
  · exact setup.hcomponent_differentiable i
  · intro x y hx hy
    rw [VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i hx,
      VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i hy]
    exact setup.hcomponent_smooth i x y hx hy

/-- Two-component witness showing component convexity is not derivable from
average convexity alone.

The average of these two components is identically zero, hence convex, while the
second component is concave.  This is not a paper object; it records why the
source-backed component-convexity assumption must be represented directly in
`Setup` rather than derived from convexity of the finite average. -/
private noncomputable def componentConvexityCounterexample (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then x ^ 2 else -x ^ 2


/-- The paper averaged gradient inherits the carrier Lipschitz bound from the
component assumptions, with no ambient `Set.univ` smoothness premise. -/
private theorem gradF_carrier_lipschitz_of_components
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) :
    ∀ x y, x ∈ setup.X → y ∈ setup.X →
      SOptLib.dualNorm (setup.gradF x - setup.gradF y) ≤ setup.L * ‖x - y‖ := by
  classical
  intro x y hx hy
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hm_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (le_of_lt hm_pos)
  have hgrad_sub :
      setup.gradF x - setup.gradF y =
        c • Finset.sum Finset.univ
          (fun i => setup.componentGrad i x - setup.componentGrad i y) := by
    simp [VarianceReducedMirrorDescentSetup.gradF_def, c, Finset.sum_sub_distrib,
      smul_sub]
  have hnorm_sum :
      ‖Finset.sum Finset.univ
          (fun i => setup.componentGrad i x - setup.componentGrad i y)‖ ≤
        Finset.sum Finset.univ
          (fun i => ‖setup.componentGrad i x - setup.componentGrad i y‖) := by
    exact norm_sum_le Finset.univ (fun i => setup.componentGrad i x - setup.componentGrad i y)
  have hcomponent :
      Finset.sum Finset.univ
          (fun i => ‖setup.componentGrad i x - setup.componentGrad i y‖) ≤
        Finset.sum Finset.univ (fun i => setup.Li i * ‖x - y‖) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    rw [VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i hx,
      VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i hy]
    simpa [SOptLib.dualNorm_eq_norm] using setup.hcomponent_smooth i x y hx hy
  have hscaled :
      c * ‖Finset.sum Finset.univ
          (fun i => setup.componentGrad i x - setup.componentGrad i y)‖ ≤
        c * Finset.sum Finset.univ (fun i => setup.Li i * ‖x - y‖) := by
    exact mul_le_mul_of_nonneg_left (le_trans hnorm_sum hcomponent) hc_nonneg
  calc
    SOptLib.dualNorm (setup.gradF x - setup.gradF y)
        = ‖setup.gradF x - setup.gradF y‖ := by
            simp [SOptLib.dualNorm_eq_norm]
    _ = c * ‖Finset.sum Finset.univ
          (fun i => setup.componentGrad i x - setup.componentGrad i y)‖ := by
            rw [hgrad_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
    _ ≤ c * Finset.sum Finset.univ (fun i => setup.Li i * ‖x - y‖) := hscaled
    _ = setup.L * ‖x - y‖ := by
            rw [VarianceReducedMirrorDescentSetup.L_def]
            dsimp [c]
            rw [← Finset.sum_mul Finset.univ setup.Li ‖x - y‖]
            ring

/-- The finite average inherits the carrier-level smooth-convex model from the
component functions, without strengthening the ambient extension outside `X`.

This is the faithful replacement for the previous global `Set.univ` bridge:
Lan's assumptions only quantify over feasible `x,y ∈ X`, so downstream Lemma
5.8 work must route through carrier smoothness, e.g.
`Convex.carrier_smooth_quadratic_upper_bound`, rather than an unrestricted
ambient smooth-convex theorem. -/
private theorem fAvg_carrier_smooth_convex_model
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) :
    ConvexOn ℝ setup.X setup.fAvg ∧
      DifferentiableOn ℝ setup.fAvg setup.X ∧
        ∀ x y, x ∈ setup.X → y ∈ setup.X →
          SOptLib.dualNorm (setup.gradF x - setup.gradF y) ≤
            setup.L * ‖x - y‖ := by
  classical
  refine ⟨?hconv, ?hdiff, ?hlip⟩
  · dsimp [VarianceReducedMirrorDescentSetup.fAvg]
    have hsum_all : ∀ s : Finset ι,
        ConvexOn ℝ setup.X (fun x => Finset.sum s (fun i => setup.f i x)) := by
      intro s
      refine Finset.induction_on s ?hbase ?hstep
      · simpa using
          (convexOn_const (𝕜 := ℝ) (s := setup.X) (E := E) (0 : ℝ)
            setup.hX_convex)
      · intro a s ha hs
        have hfa : ConvexOn ℝ setup.X (setup.f a) := setup.hcomponent_convex a
        have hadd :
            ConvexOn ℝ setup.X
              ((fun x => setup.f a x) + fun x => Finset.sum s (fun i => setup.f i x)) :=
          hfa.add hs
        simpa [Finset.sum_insert, ha, Pi.add_apply] using hadd
    have hsum : ConvexOn ℝ setup.X
        (fun x => Finset.sum Finset.univ (fun i => setup.f i x)) :=
      hsum_all Finset.univ
    have hc : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by
      have hpos : 0 < (Fintype.card ι : ℝ) := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
      exact inv_nonneg.mpr (le_of_lt hpos)
    simpa [smul_eq_mul] using
      (ConvexOn.smul (𝕜 := ℝ) (s := setup.X)
        (f := fun x => Finset.sum Finset.univ (fun i => setup.f i x)) hc hsum)
  · dsimp [VarianceReducedMirrorDescentSetup.fAvg]
    have hsum : DifferentiableOn ℝ
        (fun x => Finset.sum Finset.univ (fun i => setup.f i x)) setup.X := by
      exact DifferentiableOn.fun_sum (u := Finset.univ) (A := fun i => setup.f i)
        (by
          intro i _hi
          exact setup.hcomponent_differentiable i)
    simpa [smul_eq_mul] using hsum.const_mul (Fintype.card ι : ℝ)⁻¹
  · exact gradF_carrier_lipschitz_of_components setup

/-- Componentwise carrier co-coercivity used to assemble Lan Lemma 5.8 for the
finite average.

This aligns with Lan §5.3 Lemma 5.8 applied to a single component `f_i`.
Considered the pre-searched `weightedExpectedStationarity`,
`weightedExpectedExactStationarity`, `empiricalOracleAverage`, and
`_root_.convexOn_weighted_average_le_weighted_sum`; the first three are stationarity or
oracle averaging primitives and the Jensen helper is only for scalar convex
outputs.  The applicable local primitive is
`carrierGradient_smooth_convex_gap_inequality`, specialized to the component
carrier objective. -/
private theorem component_carrier_cocoercive_gap_for_lemma_5_8
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (i : ι) (x z : {x : E // x ∈ setup.X}) :
    (1 / (2 * setup.Li i : ℝ)) *
        SOptLib.dualNorm (setup.componentGrad i x.1 - setup.componentGrad i z.1) ^ 2 ≤
      setup.f i x.1 - setup.f i z.1 -
        ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ := by
  have hgrad_mem_x :
      setup.componentGrad i x.1 =
        SOptLib.carrierGradient setup.X (setup.componentOn i) x := by
    simpa [VarianceReducedMirrorDescentSetup.componentOn,
      vrmdComponentGradientCore, SOptLib.carrierGradient] using
      VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i x.2
  have hgrad_mem_z :
      setup.componentGrad i z.1 =
        SOptLib.carrierGradient setup.X (setup.componentOn i) z := by
    simpa [VarianceReducedMirrorDescentSetup.componentOn,
      vrmdComponentGradientCore, SOptLib.carrierGradient] using
      VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i z.2
  simpa [VarianceReducedMirrorDescentSetup.componentOn, hgrad_mem_x, hgrad_mem_z]
    using
      carrierGradient_smooth_convex_gap_inequality
        (X := setup.X) (F := setup.f i) (f := setup.componentOn i)
        (L := setup.Li i) (setup.hLi_pos i) setup.hX_convex
        (setup.hcomponent_convex i) (setup.hcomponent_differentiable i)
        (by intro y; rfl)
        (by
          intro a b
          simpa [VarianceReducedMirrorDescentSetup.componentOn,
            vrmdComponentGradientCore, SOptLib.carrierGradient] using
            setup.hcomponent_smooth i a.1 b.1 a.2 b.2)
        (by simpa [VarianceReducedMirrorDescentSetup.componentOn,
          vrmdComponentGradientCore] using setup.hcomponent_gradient_image_convex i)
        x z

/-- Weighted finite Hilbert Cauchy inequality for positive component weights.

This is the sharp vector Cauchy step needed by Lan Lemma 5.8 after summing
component co-coercivity.  Search audit: checked Mathlib names around
`norm_sum_le`, scalar Cauchy-Schwarz finite sums, and SOptLib finite weighted
average lemmas; no imported theorem states this positive-weight Hilbert form. -/
private theorem weighted_cauchy_for_component_gradient_average
    (w : ι → ℝ) (d : ι → E) (hw : ∀ i : ι, 0 < w i) :
    ‖Finset.sum Finset.univ d‖ ^ 2 ≤
      (Finset.sum Finset.univ w) *
        Finset.sum Finset.univ (fun i => ‖d i‖ ^ 2 / w i) := by
  classical
  have htri :
      ‖Finset.sum Finset.univ d‖ ≤ Finset.sum Finset.univ (fun i => ‖d i‖) := by
    simpa using norm_sum_le Finset.univ d
  have htri_sq :
      ‖Finset.sum Finset.univ d‖ ^ 2 ≤
        (Finset.sum Finset.univ (fun i => ‖d i‖)) ^ 2 := by
    have hleft : 0 ≤ ‖Finset.sum Finset.univ d‖ := norm_nonneg _
    have hright : 0 ≤ Finset.sum Finset.univ (fun i => ‖d i‖) := by
      exact Finset.sum_nonneg (fun i _hi => norm_nonneg (d i))
    nlinarith
  have hW_pos : 0 < Finset.sum Finset.univ w := by
    exact Finset.sum_pos (fun i _hi => hw i) (by simp)
  have hscalar_div :
      (Finset.sum Finset.univ (fun i => ‖d i‖)) ^ 2 / Finset.sum Finset.univ w ≤
        Finset.sum Finset.univ (fun i => ‖d i‖ ^ 2 / w i) := by
    exact Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ)
      (f := fun i => ‖d i‖) (g := w) (fun i _hi => hw i)
  have hscalar :
      (Finset.sum Finset.univ (fun i => ‖d i‖)) ^ 2 ≤
        (Finset.sum Finset.univ w) *
          Finset.sum Finset.univ (fun i => ‖d i‖ ^ 2 / w i) := by
    have h := (div_le_iff₀ hW_pos).mp hscalar_div
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  exact le_trans htri_sq hscalar

/-- Finite average of component linearized gaps is the `fOn`/`gradF` gap.

This aligns with Lan Eq. (5.3.1): `f = m⁻¹ ∑ᵢ f_i` and
`∇f = m⁻¹ ∑ᵢ ∇f_i` on the carrier.  Considered
`empiricalOracleAverage_eq_sum`, which averages stochastic oracle samples, while
this is the deterministic objective/gradient finite average. -/
private theorem finite_average_component_gap_rewrite_for_lemma_5_8
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x z : {x : E // x ∈ setup.X}) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            setup.f i x.1 - setup.f i z.1 -
              ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ) =
      setup.fOn x - setup.fOn z -
        ⟪setup.gradF z.1, x.1 - z.1⟫_ℝ := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let d : E := x.1 - z.1
  let A : ℝ := Finset.sum Finset.univ (fun i : ι => setup.f i x.1)
  let B : ℝ := Finset.sum Finset.univ (fun i : ι => setup.f i z.1)
  let C : ℝ :=
    Finset.sum Finset.univ
      (fun i : ι => ⟪setup.componentGrad i z.1, d⟫_ℝ)
  have hsum_gap :
      Finset.sum Finset.univ
          (fun i : ι =>
            setup.f i x.1 - setup.f i z.1 -
              ⟪setup.componentGrad i z.1, d⟫_ℝ) =
        A - B - C := by
    dsimp [A, B, C]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hinner : ⟪setup.gradF z.1, d⟫_ℝ = m⁻¹ * C := by
    simp [VarianceReducedMirrorDescentSetup.gradF_def, m, C, inner_smul_left,
      sum_inner]
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            setup.f i x.1 - setup.f i z.1 -
              ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ)
        = m⁻¹ * (A - B - C) := by
            simp [m, d, hsum_gap]
    _ = m⁻¹ * A - m⁻¹ * B - m⁻¹ * C := by ring
    _ = setup.fOn x - setup.fOn z -
          ⟪setup.gradF z.1, x.1 - z.1⟫_ℝ := by
            simp [VarianceReducedMirrorDescentSetup.fOn,
              VarianceReducedMirrorDescentSetup.fAvg, A, B, d, hinner, m]

/-- Finite component aggregation for Lan Lemma 5.8.

This is the remaining finite-dimensional algebra after applying componentwise
carrier co-coercivity: expand `gradF` and `fAvg`, use the sharp weighted Hilbert
Cauchy bound
`‖∑ d_i‖^2 ≤ (∑ L_i) * ∑ ‖d_i‖^2 / L_i`, and normalize by
`L = m⁻¹ ∑ L_i`.  Search audit: checked SOptLib `_root_.convexOn_weighted_average_le_weighted_sum`,
`weighted_average_sub_baseline_le_weighted_gap`, `empiricalOracleAverage_eq_sum`,
and Mathlib/target searches for finite weighted Cauchy-Schwarz; no imported
lemma states this vector weighted-Cauchy form with positive component weights. -/
private theorem finite_average_component_gap_for_lemma_5_8
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x z : {x : E // x ∈ setup.X})
    (hcomp : ∀ i : ι,
      (1 / (2 * setup.Li i : ℝ)) *
          SOptLib.dualNorm (setup.componentGrad i x.1 - setup.componentGrad i z.1) ^ 2 ≤
        setup.f i x.1 - setup.f i z.1 -
          ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ) :
    (1 / (2 * setup.L : ℝ)) *
        SOptLib.dualNorm (setup.gradF x.1 - setup.gradF z.1) ^ 2 ≤
      setup.fOn x - setup.fOn z - ⟪setup.gradF z.1, x.1 - z.1⟫_ℝ := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let c : ℝ := m⁻¹
  let d : ι → E := fun i => setup.componentGrad i x.1 - setup.componentGrad i z.1
  let gap : ι → ℝ := fun i =>
    setup.f i x.1 - setup.f i z.1 -
      ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ
  let Q : ℝ := Finset.sum Finset.univ (fun i : ι => ‖d i‖ ^ 2 / setup.Li i)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hc_nonneg : 0 ≤ c := by
    exact inv_nonneg.mpr (le_of_lt hm_pos)
  have hsumL_pos : 0 < Finset.sum Finset.univ setup.Li := by
    exact Finset.sum_pos (fun i _hi => setup.hLi_pos i) Finset.univ_nonempty
  have hL_eq : setup.L = c * Finset.sum Finset.univ setup.Li := by
    rw [VarianceReducedMirrorDescentSetup.L_def]
  have hL_pos' : 0 < setup.L := by
    exact setup.L_pos
  have hgrad_sub :
      setup.gradF x.1 - setup.gradF z.1 =
        c • Finset.sum Finset.univ d := by
    calc
      setup.gradF x.1 - setup.gradF z.1 =
          c • Finset.sum Finset.univ (fun i : ι => setup.componentGrad i x.1) -
            c • Finset.sum Finset.univ (fun i : ι => setup.componentGrad i z.1) := by
            simp [VarianceReducedMirrorDescentSetup.gradF_def, c, m]
      _ = c •
            (Finset.sum Finset.univ (fun i : ι => setup.componentGrad i x.1) -
              Finset.sum Finset.univ (fun i : ι => setup.componentGrad i z.1)) := by
            rw [smul_sub]
      _ = c • Finset.sum Finset.univ d := by
            simp [d, Finset.sum_sub_distrib]
  have hcomp' : ∀ i : ι, ‖d i‖ ^ 2 / (2 * setup.Li i) ≤ gap i := by
    intro i
    have h := hcomp i
    simpa [d, gap, SOptLib.dualNorm_eq_norm, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using h
  have hsum_comp :
      Finset.sum Finset.univ (fun i : ι => ‖d i‖ ^ 2 / (2 * setup.Li i)) ≤
        Finset.sum Finset.univ gap := by
    exact Finset.sum_le_sum (fun i _hi => hcomp' i)
  have hQ_half :
      (1 / 2 : ℝ) * Q =
        Finset.sum Finset.univ (fun i : ι => ‖d i‖ ^ 2 / (2 * setup.Li i)) := by
    dsimp [Q]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    field_simp [ne_of_gt (setup.hLi_pos i)]
  have hQ_gap : (1 / 2 : ℝ) * Q ≤ Finset.sum Finset.univ gap := by
    calc
      (1 / 2 : ℝ) * Q =
          Finset.sum Finset.univ (fun i : ι => ‖d i‖ ^ 2 / (2 * setup.Li i)) := hQ_half
      _ ≤ Finset.sum Finset.univ gap := hsum_comp
  have hcauchy :
      ‖Finset.sum Finset.univ d‖ ^ 2 ≤
        (Finset.sum Finset.univ setup.Li) * Q := by
    simpa [Q] using
      weighted_cauchy_for_component_gradient_average setup.Li d setup.hLi_pos
  have hnorm_avg :
      ‖setup.gradF x.1 - setup.gradF z.1‖ ^ 2 ≤
        c ^ 2 * ((Finset.sum Finset.univ setup.Li) * Q) := by
    rw [hgrad_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
    nlinarith [sq_nonneg c, hcauchy]
  have hleft_le :
      (1 / (2 * setup.L : ℝ)) *
          ‖setup.gradF x.1 - setup.gradF z.1‖ ^ 2 ≤
        c * ((1 / 2 : ℝ) * Q) := by
    have hfactor_nonneg : 0 ≤ (1 / (2 * setup.L : ℝ)) := by
      positivity
    have hsumL_ne : Finset.sum Finset.univ setup.Li ≠ 0 := ne_of_gt hsumL_pos
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      exact inv_ne_zero hm_ne
    calc
      (1 / (2 * setup.L : ℝ)) *
          ‖setup.gradF x.1 - setup.gradF z.1‖ ^ 2
          ≤ (1 / (2 * setup.L : ℝ)) *
              (c ^ 2 * ((Finset.sum Finset.univ setup.Li) * Q)) := by
              exact mul_le_mul_of_nonneg_left hnorm_avg hfactor_nonneg
      _ = c * ((1 / 2 : ℝ) * Q) := by
              rw [hL_eq]
              field_simp [hc_ne, hsumL_ne]
  have hscaled_gap :
      c * ((1 / 2 : ℝ) * Q) ≤
        c * Finset.sum Finset.univ gap := by
    exact mul_le_mul_of_nonneg_left hQ_gap hc_nonneg
  have hgap_eq :
      c * Finset.sum Finset.univ gap =
        setup.fOn x - setup.fOn z -
          ⟪setup.gradF z.1, x.1 - z.1⟫_ℝ := by
    simpa [c, gap] using
      finite_average_component_gap_rewrite_for_lemma_5_8 setup x z
  rw [SOptLib.dualNorm_eq_norm]
  exact le_trans hleft_le (le_trans hscaled_gap (le_of_eq hgap_eq))

/-- Lemma 5.8 in the paper-facing finite-sum form on `X`: the gradient in the
statement is the canonical averaged gradient `setup.gradF`, and the objective
is the canonical averaged finite-sum objective `setup.fAvg`.

Considered `Convex.carrier_smooth_quadratic_upper_bound` and
`objectiveKernel`; the former is a smoothness upper-bound helper and the latter
is a stochastic-kernel primitive, so neither states the source Lemma 5.8
co-coercivity gap on the finite-sum objective from Eq. (5.3.1). -/
theorem lemma_5_8
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x z : {x : E // x ∈ setup.X}) :
    (1 / (2 * setup.L : ℝ)) *
        SOptLib.dualNorm (setup.gradF x.1 - setup.gradF z.1) ^ 2 ≤
      setup.fOn x - setup.fOn z - ⟪setup.gradF z.1, x.1 - z.1⟫_ℝ := by
  exact
    finite_average_component_gap_for_lemma_5_8 setup x z
      (fun i => component_carrier_cocoercive_gap_for_lemma_5_8 setup i x z)

/-! The next two helpers are the two source proof steps of Lemma 5.12. -/

/-- Componentwise form of Lemma 5.8, parameterized by the component-convexity
fact used for this component.

This aligns with Lan Lemma 5.12, proof step 1: apply Lemma 5.8 with
`f = f_i`.  The paper states component convexity in the Section 5.3 setup; the
paper-facing Lemma 5.12 obtains this premise from `setup.hcomponent_convex`. -/
theorem component_lemma_5_8_of_component_convex
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (i : ι) (hconv_i : ConvexOn ℝ setup.X (setup.f i))
    (x z : {x : E // x ∈ setup.X}) :
    (1 / (2 * setup.Li i : ℝ)) *
        SOptLib.dualNorm (setup.componentGrad i x.1 - setup.componentGrad i z.1) ^ 2 ≤
      setup.f i x.1 - setup.f i z.1 -
        ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ := by
  have _hmodel := component_carrier_smooth_model setup i
  have hgrad_mem_x :
      setup.componentGrad i x.1 =
        SOptLib.carrierGradient setup.X (setup.componentOn i) x := by
    simpa [VarianceReducedMirrorDescentSetup.componentOn,
      vrmdComponentGradientCore, SOptLib.carrierGradient] using
      VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i x.2
  have hgrad_mem_z :
      setup.componentGrad i z.1 =
        SOptLib.carrierGradient setup.X (setup.componentOn i) z := by
    simpa [VarianceReducedMirrorDescentSetup.componentOn,
      vrmdComponentGradientCore, SOptLib.carrierGradient] using
      VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i z.2
  simpa [VarianceReducedMirrorDescentSetup.componentOn, hgrad_mem_x, hgrad_mem_z]
    using
      carrierGradient_smooth_convex_gap_inequality
        (X := setup.X) (F := setup.f i) (f := setup.componentOn i)
        (L := setup.Li i) (setup.hLi_pos i) setup.hX_convex hconv_i
        (setup.hcomponent_differentiable i)
        (by intro y; rfl)
        (by
          intro a b
          simpa [VarianceReducedMirrorDescentSetup.componentOn,
            vrmdComponentGradientCore, SOptLib.carrierGradient] using
            setup.hcomponent_smooth i a.1 b.1 a.2 b.2)
        (by simpa [VarianceReducedMirrorDescentSetup.componentOn,
          vrmdComponentGradientCore] using setup.hcomponent_gradient_image_convex i)
        x z

/-- Componentwise Lan Lemma 5.8 using the Section 5.3 stated component
convexity assumption from the setup.

This is the source-facing specialization of
`component_lemma_5_8_of_component_convex`: the paper applies Lemma 5.8 with
`f = f_i` in the proof of Lemma 5.12, and the convexity premise is exactly
`setup.hcomponent_convex i`. -/
theorem component_lemma_5_8
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (i : ι) (x z : {x : E // x ∈ setup.X}) :
    (1 / (2 * setup.Li i : ℝ)) *
        SOptLib.dualNorm (setup.componentGrad i x.1 - setup.componentGrad i z.1) ^ 2 ≤
      setup.f i x.1 - setup.f i z.1 -
        ⟪setup.componentGrad i z.1, x.1 - z.1⟫_ℝ := by
  exact component_lemma_5_8_of_component_convex setup i
    (setup.hcomponent_convex i) x z

/-- Weighted component-gradient gap bound before the final composite-objective
optimality step.

This is Lan Lemma 5.12, proof step 1 after summing the componentwise Lemma 5.8
specializations and using `L_Q = (1/m) max_i L_i/q_i`.

The gradient here is `setup.componentGrad`, the intrinsic carrier-gradient
realization of the paper's `∇ f_i(x)` on `X`; the ordinary ambient gradient of
the extension `setup.f i : E → ℝ` is not a paper datum on lower-dimensional
carriers. -/
theorem lemma_5_12_linearized_f_gap_bound
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X}) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
      2 * setup.LQ *
        (setup.fAvg x.1 - setup.fAvg xStar.1 -
          ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_nonneg : 0 ≤ m⁻¹ := inv_nonneg.mpr (le_of_lt hm_pos)
  have hterm : ∀ i : ι,
      ((m * setup.q i)⁻¹ *
          SOptLib.dualNorm
            (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
        2 * setup.LQ *
          (setup.f i x.1 - setup.f i xStar.1 -
            ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ) := by
    intro i
    let n2 : ℝ :=
      SOptLib.dualNorm
        (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2
    let gap : ℝ :=
      setup.f i x.1 - setup.f i xStar.1 -
        ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ
    have hcomp : (1 / (2 * setup.Li i : ℝ)) * n2 ≤ gap := by
      simpa [n2, gap] using
        component_lemma_5_8 setup i x xStar
    have hLi_pos : 0 < setup.Li i := setup.hLi_pos i
    have hq_pos : 0 < setup.q i := setup.hq_pos i
    have hmqi_pos : 0 < m * setup.q i := mul_pos hm_pos hq_pos
    have hn2_nonneg : 0 ≤ n2 := by
      dsimp [n2]
      exact sq_nonneg _
    have hden_pos : 0 < (2 * setup.Li i : ℝ) := mul_pos (by norm_num) hLi_pos
    have hcomp_div : n2 / (2 * setup.Li i) ≤ gap := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcomp
    have hnorm_le' : n2 ≤ gap * (2 * setup.Li i) :=
      (div_le_iff₀ hden_pos).mp hcomp_div
    have hnorm_le : n2 ≤ 2 * setup.Li i * gap := by
      nlinarith
    have hgap_nonneg : 0 ≤ gap := by
      nlinarith
    have hLi_bound : setup.Li i ≤ m * setup.q i * setup.LQ := by
      simpa [m] using setup.Li_le_card_mul_q_mul_LQ i
    have hmul_bound :
        2 * setup.Li i * gap ≤ 2 * (m * setup.q i * setup.LQ) * gap := by
      nlinarith
    calc
      (m * setup.q i)⁻¹ * n2
          ≤ (m * setup.q i)⁻¹ * (2 * setup.Li i * gap) := by
            exact mul_le_mul_of_nonneg_left hnorm_le
              (inv_nonneg.mpr (le_of_lt hmqi_pos))
      _ ≤ (m * setup.q i)⁻¹ * (2 * (m * setup.q i * setup.LQ) * gap) := by
            exact mul_le_mul_of_nonneg_left hmul_bound
              (inv_nonneg.mpr (le_of_lt hmqi_pos))
      _ = 2 * setup.LQ * gap := by
            field_simp [ne_of_gt hmqi_pos]
  have hsum :
      Finset.sum Finset.univ
          (fun i : ι =>
            ((m * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2)) ≤
        Finset.sum Finset.univ
          (fun i : ι =>
            2 * setup.LQ *
              (setup.f i x.1 - setup.f i xStar.1 -
                ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ)) := by
    exact Finset.sum_le_sum (by intro i _hi; exact hterm i)
  have hscaled := mul_le_mul_of_nonneg_left hsum hm_nonneg
  have hgap_eq :
      m⁻¹ * Finset.sum Finset.univ
          (fun i : ι =>
            setup.f i x.1 - setup.f i xStar.1 -
              ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ) =
        setup.fAvg x.1 - setup.fAvg xStar.1 -
          ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ := by
    let d : E := x.1 - xStar.1
    let A : ℝ := Finset.sum Finset.univ (fun i : ι => setup.f i x.1)
    let B : ℝ := Finset.sum Finset.univ (fun i : ι => setup.f i xStar.1)
    let C : ℝ :=
      Finset.sum Finset.univ
        (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ)
    have hsum_gap :
        Finset.sum Finset.univ
            (fun i : ι =>
              setup.f i x.1 - setup.f i xStar.1 -
                ⟪setup.componentGrad i xStar.1, d⟫_ℝ) =
          A - B - C := by
      dsimp [A, B, C]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have hinner : ⟪setup.gradF xStar.1, d⟫_ℝ = m⁻¹ * C := by
      simp [VarianceReducedMirrorDescentSetup.gradF_def, m, C, inner_smul_left,
        sum_inner]
    calc
      m⁻¹ * Finset.sum Finset.univ
          (fun i : ι =>
            setup.f i x.1 - setup.f i xStar.1 -
              ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ)
          = m⁻¹ * (A - B - C) := by
              simp [d, hsum_gap]
      _ = m⁻¹ * A - m⁻¹ * B - m⁻¹ * C := by ring
      _ = setup.fAvg x.1 - setup.fAvg xStar.1 -
            ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ := by
              simp [VarianceReducedMirrorDescentSetup.fAvg, A, B, d, hinner, m]
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2)
        =
      m⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            ((m * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2)) := by
          simp [m]
    _ ≤
      m⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            2 * setup.LQ *
              (setup.f i x.1 - setup.f i xStar.1 -
                ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ)) := hscaled
    _ =
      2 * setup.LQ *
        (m⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι =>
              setup.f i x.1 - setup.f i xStar.1 -
                ⟪setup.componentGrad i xStar.1, x.1 - xStar.1⟫_ℝ)) := by
          rw [← Finset.mul_sum]
          ring
    _ =
      2 * setup.LQ *
        (setup.fAvg x.1 - setup.fAvg xStar.1 -
          ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ) := by
          rw [hgap_eq]

/-- Compatibility alias for downstream proof scripts that were already migrated
to the explicit carrier-gradient spelling. -/
theorem lemma_5_12_linearized_f_gap_bound_carrier
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X}) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
      2 * setup.LQ *
        (setup.fAvg x.1 - setup.fAvg xStar.1 -
          ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ) := by
  exact lemma_5_12_linearized_f_gap_bound setup x xStar

/-! Source step 2 of Lemma 5.12: composite optimality transport. -/

/-- Segment derivative of the finite-sum smooth part at an optimal comparison
point.

This aligns with Lan Lemma 5.12, proof step 2, where the quotient along the
segment from `x*` to `x` is sent to
`⟪∇f(x*), x - x*⟫`.  Considered
`hasFDerivWithinAt_of_contDiffOn_gradientWithin_comp`, which requires a
`ContDiffOn` premise not present in the VRMD setup, and
`Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`, which consumes a
derivative but does not construct the finite-sum `gradientWithin` identity. -/
private theorem fAvg_segment_hasDerivWithinAt_gradF
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X}) :
    HasDerivWithinAt
      (fun t : ℝ => setup.fAvg (xStar.1 + t • (x.1 - xStar.1)))
      ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  let d : E := x.1 - xStar.1
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => xStar.1 + t • d
  have hd_dir : d ∈ (affineSpan ℝ setup.X).direction := by
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ setup.X x.2)
      (subset_affineSpan ℝ setup.X xStar.2)
  have hline_eq : ∀ t : ℝ, line t = AffineMap.lineMap xStar.1 x.1 t := by
    intro t
    simp [line, d, AffineMap.lineMap_apply_module', add_comm, sub_eq_add_neg]
  have hmaps : Set.MapsTo line I setup.X := by
    intro t ht
    rw [hline_eq t]
    exact setup.hX_convex.lineMap_mem xStar.2 x.2 ht
  have hline_deriv : HasDerivWithinAt line d I 0 := by
    have hline_at : HasDerivAt (fun t : ℝ => xStar.1 + t • d) d 0 := by
      simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add xStar.1
    simpa [line] using hline_at.hasDerivWithinAt
  have hcomp : ∀ i : ι,
      HasDerivWithinAt (fun t : ℝ => setup.f i (line t))
        ⟪setup.componentGrad i xStar.1, d⟫_ℝ I 0 := by
    intro i
    have hF : HasFDerivWithinAt (setup.f i)
        (fderivWithin ℝ (setup.f i) setup.X xStar.1) setup.X xStar.1 :=
      (setup.hcomponent_differentiable i xStar.1 xStar.2).hasFDerivWithinAt
    have hchain : HasDerivWithinAt (fun t : ℝ => setup.f i (line t))
        ((fderivWithin ℝ (setup.f i) setup.X xStar.1) d) I 0 := by
      have h := hF.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line, d])
      simpa [line] using h
    have hcarrier : setup.componentGrad i xStar.1 =
        SOptLib.carrierGradient setup.X (setup.componentOn i) xStar := by
      simpa [VarianceReducedMirrorDescentSetup.componentOn,
        vrmdComponentGradientCore, SOptLib.carrierGradient] using
        VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i xStar.2
    let du : (affineSpan ℝ setup.X).direction := ⟨d, hd_dir⟩
    have hpair_carrier :=
      VarianceReducedMirrorDescentSetup.component_carrierGradient_inner_eq_fderivWithin_on_affine_direction
        (X := setup.X) (F := setup.f i) (f := setup.componentOn i)
        setup.hX_convex (setup.hcomponent_differentiable i) (by intro y; rfl) xStar du
    have hpair : (fderivWithin ℝ (setup.f i) setup.X xStar.1) d =
        ⟪setup.componentGrad i xStar.1, d⟫_ℝ := by
      simpa [du, hcarrier] using hpair_carrier.symm
    simpa [hpair] using hchain
  have hsum : HasDerivWithinAt
      (fun t : ℝ => Finset.sum Finset.univ (fun i : ι => setup.f i (line t)))
      (Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ))
      I 0 := by
    exact HasDerivWithinAt.fun_sum (fun i _hi => hcomp i)
  have havg : HasDerivWithinAt
      (fun t : ℝ => (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => setup.f i (line t)))
      ((Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ))
      I 0 := by
    simpa using hsum.const_mul (Fintype.card ι : ℝ)⁻¹
  have hgrad : ⟪setup.gradF xStar.1, d⟫_ℝ =
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i xStar.1, d⟫_ℝ) := by
    simp [VarianceReducedMirrorDescentSetup.gradF_def, inner_smul_left, sum_inner]
  simpa [VarianceReducedMirrorDescentSetup.fAvg, line, d, I, hgrad] using havg

/-- First-order transport from composite optimality to the `h`-gap.

This is Lan Lemma 5.12, proof step 2 in its intrinsic form.  Considered
`Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`, but the composite
objective includes the nonsmooth `h`; the source proof instead uses the
one-dimensional feasible segment, convexity of `h`, and the smooth derivative
of only `f`. -/
private theorem composite_optimality_inner_le_h_gap
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    -⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ ≤
      setup.hOn x - setup.hOn xStar := by
  classical
  let d : E := x.1 - xStar.1
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => xStar.1 + t • d
  let hgap : ℝ := setup.hOn x - setup.hOn xStar
  let φ : ℝ → ℝ := fun t => setup.fAvg (line t) + setup.hOn xStar + t * hgap
  have hline_eq : ∀ t : ℝ, line t = AffineMap.lineMap xStar.1 x.1 t := by
    intro t
    simp [line, d, AffineMap.lineMap_apply_module', add_comm, sub_eq_add_neg]
  have hline_mem : ∀ t ∈ I, line t ∈ setup.X := by
    intro t ht
    rw [hline_eq t]
    exact setup.hX_convex.lineMap_mem xStar.2 x.2 ht
  have hderiv_f :
      HasDerivWithinAt
        (fun t : ℝ => setup.fAvg (line t))
        ⟪setup.gradF xStar.1, d⟫_ℝ I 0 := by
    simpa [line, d, I] using fAvg_segment_hasDerivWithinAt_gradF setup x xStar
  have hderiv_lin :
      HasDerivWithinAt (fun t : ℝ => setup.hOn xStar + t * hgap) hgap I 0 := by
    have hid : HasDerivWithinAt (fun t : ℝ => t) 1 I 0 :=
      hasDerivWithinAt_id 0 I
    simpa [hgap] using (hid.mul_const hgap).const_add (setup.hOn xStar)
  have hderivφ :
      HasDerivWithinAt φ (⟪setup.gradF xStar.1, d⟫_ℝ + hgap) I 0 := by
    simpa [φ, line, hgap, add_assoc, add_comm, add_left_comm] using hderiv_f.add hderiv_lin
  have hmin : ∀ t ∈ I, φ 0 ≤ φ t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hseg_mem : line t ∈ setup.X := hline_mem t ht
    have hopt_seg := h_opt ⟨line t, hseg_mem⟩
    have hconv_h :
        setup.h (line t) - setup.h xStar.1 ≤
          t * (setup.h x.1 - setup.h xStar.1) := by
      have hconv_raw := setup.hh_convex.2 xStar.2 x.2
        (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = (1 : ℝ))
      have harg :
          (1 - t) • xStar.1 + t • x.1 = line t := by
        rw [hline_eq t]
        simp [AffineMap.lineMap_apply_module]
      have hconv_line :
          setup.h (line t) ≤ (1 - t) * setup.h xStar.1 + t * setup.h x.1 := by
        simpa [harg, smul_eq_mul] using hconv_raw
      linarith
    have hopt_unfold :
        setup.fAvg xStar.1 + setup.h xStar.1 ≤
          setup.fAvg (line t) + setup.h (line t) := by
      simpa [VarianceReducedMirrorDescentSetup.PsiOn,
        VarianceReducedMirrorDescentSetup.fOn,
        VarianceReducedMirrorDescentSetup.hOn,
        SOptLib.compositeObjective] using hopt_seg
    have hupper :
        setup.fAvg (line t) + setup.h (line t) ≤
          setup.fAvg (line t) + setup.h xStar.1 +
            t * (setup.h x.1 - setup.h xStar.1) := by
      linarith
    have hmain :
        setup.fAvg xStar.1 + setup.h xStar.1 ≤
          setup.fAvg (line t) + setup.h xStar.1 +
            t * (setup.h x.1 - setup.h xStar.1) :=
      le_trans hopt_unfold hupper
    simpa [φ, line, hgap, VarianceReducedMirrorDescentSetup.hOn] using hmain
  have hnonneg : 0 ≤ ⟪setup.gradF xStar.1, d⟫_ℝ + hgap :=
    right_derivative_nonneg_of_min_on_Icc (φ := φ) hderivφ hmin
  dsimp [hgap, d] at hnonneg ⊢
  linarith

/-- Optimality of `xStar` for `Ψ = f + h`, together with convexity of `h`,
turns the linearized smooth gap into the composite objective gap.

This aligns with Lan Lemma 5.12, proof step 2. -/
theorem linearized_f_gap_le_Psi_gap_of_opt
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    setup.fAvg x.1 - setup.fAvg xStar.1 -
        ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ ≤
      setup.PsiOn x - setup.PsiOn xStar := by
  have hinner := composite_optimality_inner_le_h_gap setup x xStar h_opt
  rw [setup.PsiOn_coe x, setup.PsiOn_coe xStar]
  unfold VarianceReducedMirrorDescentSetup.Psi
  rw [setup.hOn_coe x, setup.hOn_coe xStar] at hinner
  linarith

/-! Used in: `lemma_5_13` as the weighted component second-moment estimate
driving the variance bound for the corrected estimator.

The previous scaffold exposed a stronger deterministic bridge from the averaged
linearized smooth gap
`f(y) - f(x) - <∇f(x), y - x>` to two composite gaps.  That statement is not a
paper lemma and is false under the stated convex smooth composite setup.  Lemma
5.13 instead estimates the fixed-fiber estimator second moment directly by
splitting component-gradient differences through `x*`; the theorem
`weighted_component_grad_diff_between_le_two_Psi_gaps_of_opt` below records
that source-faithful deterministic endpoint. -/
/-! ### Lemma 5.12 soundness repair

The original scaffold exposed Lemma 5.12 with unrestricted ambient gradients
`gradient (setup.f i)`.  That is not a faithful object for a lower-dimensional
closed convex carrier: two ambient extensions agreeing on `X` can differ in
normal gradient components, while Algorithm 5.6 only uses the carrier gradient
on feasible points.  The small witness below records the concrete obstruction.
-/

private noncomputable def lemma_5_12_rawGradientCounterexampleF
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * x 1

private theorem lemma_5_12_rawGradientCounterexample_grad
    (a b : ℝ) :
    gradient lemma_5_12_rawGradientCounterexampleF
        (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 ![b, a] : EuclideanSpace ℝ (Fin 2)) := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  dsimp [lemma_5_12_rawGradientCounterexampleF]
  have h0 :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) => q 0)
        (PiLp.proj (2 : ENNReal) (𝕜 := ℝ) (fun _ : Fin 2 => ℝ) 0)
        (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) := by
    simpa using
      (PiLp.proj (2 : ENNReal) (𝕜 := ℝ) (fun _ : Fin 2 => ℝ) 0).hasFDerivAt
        (x := (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)))
  have h1 :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) => q 1)
        (PiLp.proj (2 : ENNReal) (𝕜 := ℝ) (fun _ : Fin 2 => ℝ) 1)
        (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) := by
    simpa using
      (PiLp.proj (2 : ENNReal) (𝕜 := ℝ) (fun _ : Fin 2 => ℝ) 1).hasFDerivAt
        (x := (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)))
  have hmul := h0.mul h1
  convert hmul using 1
  ext y
  simp [PiLp.inner_apply, InnerProductSpace.toDual_apply_apply]
  have hb : ⟪b, y.ofLp 0⟫_ℝ = b * y.ofLp 0 := by
    exact RCLike.inner_apply' b (y.ofLp 0)
  have ha : ⟪a, y.ofLp 1⟫_ℝ = a * y.ofLp 1 := by
    exact RCLike.inner_apply' a (y.ofLp 1)
  rw [hb, ha]
  ring

/-- Closed-form hyperplane projection used only in the raw-gradient
soundness witness.

For the concrete witness `X = {u | u 1 = 0}` and `v(u)=‖u‖²/2`, the prox
subproblem over `X` minimizes the one-dimensional quadratic in coordinate `0`.
This selector is the paper's argmin update specialized to that hyperplane, not
the false constant selector rejected in the prior iteration. -/
private noncomputable def lemma_5_12_hyperplaneProxPoint
    (x g : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  let X : Set (EuclideanSpace ℝ (Fin 2)) := {u | u 1 = 0}
  let v : EuclideanSpace ℝ (Fin 2) → ℝ := fun u => ‖u‖ ^ 2 / 2
  let a := gradientWithin v X x
  (WithLp.toLp 2
    ![a 0 - vrmdEtaCore (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ)) * g 0,
      (0 : ℝ)] : EuclideanSpace ℝ (Fin 2))

private theorem lemma_5_12_hyperplaneProxPoint_minimizes
    (x g y : EuclideanSpace ℝ (Fin 2)) (hy : y 1 = 0) :
    vrmdProxObjectiveCore
        ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0})
        (fun _ : EuclideanSpace ℝ (Fin 2) => 0)
        (fun u : EuclideanSpace ℝ (Fin 2) => ‖u‖ ^ 2 / 2)
        (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ))
        x g (lemma_5_12_hyperplaneProxPoint x g) ≤
      vrmdProxObjectiveCore
        ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0})
        (fun _ : EuclideanSpace ℝ (Fin 2) => 0)
        (fun u : EuclideanSpace ℝ (Fin 2) => ‖u‖ ^ 2 / 2)
        (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ))
        x g y := by
  classical
  let X : Set (EuclideanSpace ℝ (Fin 2)) := {u | u 1 = 0}
  let v : EuclideanSpace ℝ (Fin 2) → ℝ := fun u => ‖u‖ ^ 2 / 2
  let a : EuclideanSpace ℝ (Fin 2) := gradientWithin v X x
  let η : ℝ := vrmdEtaCore (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ))
  have hη : η = (1 / 16 : ℝ) := by
    norm_num [η, vrmdEtaCore, vrmdLQCore]
  have hsq : 0 ≤ (y 0 - (a 0 - η * g 0)) ^ 2 := sq_nonneg _
  simp only [vrmdProxObjectiveCore, vrmdBregmanCore]
  dsimp [lemma_5_12_hyperplaneProxPoint, X, v, a, η] at hsq ⊢
  norm_num [vrmdEtaCore, vrmdLQCore] at hsq ⊢
  simp [EuclideanSpace.norm_sq_eq, PiLp.inner_apply, hy]
  let b : EuclideanSpace ℝ (Fin 2) :=
    gradientWithin
      (fun u : EuclideanSpace ℝ (Fin 2) => (u 0 ^ 2 + u 1 ^ 2) / 2)
      ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0}) x
  have hsq' : 0 ≤ (y 0 - (b 0 - (1 / 16 : ℝ) * g 0)) ^ 2 := by
    simpa [b, EuclideanSpace.norm_sq_eq] using hsq
  have h_l1 : ⟪g 0, b 0 - 16⁻¹ * g 0⟫_ℝ =
      g 0 * (b 0 - 16⁻¹ * g 0) := by
    exact RCLike.inner_apply' (g 0) (b 0 - 16⁻¹ * g 0)
  have h_l2 : ⟪b 0, b 0 - 16⁻¹ * g 0 - x 0⟫_ℝ =
      b 0 * (b 0 - 16⁻¹ * g 0 - x 0) := by
    exact RCLike.inner_apply' (b 0) (b 0 - 16⁻¹ * g 0 - x 0)
  have h_l3 : ⟪b 1, x 1⟫_ℝ = b 1 * x 1 := by
    exact RCLike.inner_apply' (b 1) (x 1)
  have h_r1 : ⟪g 0, y 0⟫_ℝ = g 0 * y 0 := by
    exact RCLike.inner_apply' (g 0) (y 0)
  have h_r2 : ⟪b 0, y 0 - x 0⟫_ℝ = b 0 * (y 0 - x 0) := by
    exact RCLike.inner_apply' (b 0) (y 0 - x 0)
  change
    16⁻¹ * ⟪g 0, b 0 - 16⁻¹ * g 0⟫_ℝ +
        ((b 0 - 16⁻¹ * g 0) ^ 2 / 2 -
          (x 0 ^ 2 + x 1 ^ 2) / 2 -
            (⟪b 0, b 0 - 16⁻¹ * g 0 - x 0⟫_ℝ + -⟪b 1, x 1⟫_ℝ)) ≤
      16⁻¹ * ⟪g 0, y 0⟫_ℝ +
        (y 0 ^ 2 / 2 - (x 0 ^ 2 + x 1 ^ 2) / 2 -
          (⟪b 0, y 0 - x 0⟫_ℝ + -⟪b 1, x 1⟫_ℝ))
  rw [h_l1, h_l2, h_l3, h_r1, h_r2]
  nlinarith [hsq']

private theorem lemma_5_12_hyperplane_coord1_continuous :
    Continuous (fun u : EuclideanSpace ℝ (Fin 2) => u 1) := by
  exact (continuous_apply 1).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))

private theorem lemma_5_12_hyperplane_closed :
    IsClosed ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0}) := by
  simpa using
    isClosed_eq
      (f := fun u : EuclideanSpace ℝ (Fin 2) => u 1)
      (g := fun _ => (0 : ℝ))
      lemma_5_12_hyperplane_coord1_continuous continuous_const

private theorem lemma_5_12_hyperplane_convex :
    Convex ℝ ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0}) := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, hx, hy]
  simp

private theorem lemma_5_12_rawGradientCounterexample_differentiableOn :
    DifferentiableOn ℝ lemma_5_12_rawGradientCounterexampleF
      ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0}) := by
  unfold lemma_5_12_rawGradientCounterexampleF
  fun_prop

private theorem lemma_5_12_quadraticPotential_contDiffOn :
    ContDiffOn ℝ 1
      (fun u : EuclideanSpace ℝ (Fin 2) => ‖u‖ ^ 2 / 2)
      ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0}) := by
  exact ((contDiff_norm_sq ℝ).div_const 2).contDiffOn

private theorem lemma_5_12_quadraticPotential_strongConvexOn :
    StrongConvexOn ({u : EuclideanSpace ℝ (Fin 2) | u 1 = 0}) 1
      (fun u : EuclideanSpace ℝ (Fin 2) => ‖u‖ ^ 2 / 2) := by
  rw [strongConvexOn_iff_convex]
  convert convexOn_const (0 : ℝ) lemma_5_12_hyperplane_convex using 1
  funext x
  ring_nf

private theorem lemma_5_12_unit_sample_iIndep :
    iIndepFun (fun _ : ℕ => fun _ : Unit => ()) (Measure.dirac ()) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun _ => measurable_const)]
  ext s hs
  simp [hs]

/-- If a carrier-domain function vanishes on the carrier, its SOptLib
affine-span carrier gradient vanishes.

This is counterexample-local plumbing, not a paper assumption: it unfolds the
canonical `carrierGradientFrom` realization to Mathlib's `gradientWithin` of the
constant zero chart function. -/
private theorem carrierGradientFrom_eq_zero_of_forall_eq_zero
    {X : Set E} (f : {x : E // x ∈ X} → ℝ)
    (anchor x : {x : E // x ∈ X})
    (hf_zero : ∀ y, f y = 0) :
    SOptLib.carrierGradientFrom X f anchor x = 0 := by
  classical
  have hchart :
      SOptLib.carrierChartFunction X f anchor = fun _ => (0 : ℝ) := by
    funext u
    rw [SOptLib.carrierChartFunction_apply]
    by_cases hu : SOptLib.carrierChartToAmbient X anchor u ∈ X
    · rw [SOptLib.totalizeOn_of_mem X f hu]
      exact hf_zero _
    · rw [SOptLib.totalizeOn_of_not_mem X f hu]
  unfold SOptLib.carrierGradientFrom
  rw [hchart]
  simp [gradientWithin]

/-- Refutability witness for the legacy raw-gradient Lemma 5.12 surface.

On the carrier `{x | x 1 = 0}`, the function `x 0 * x 1` is identically zero,
so the carrier-gradient objective gap between `![1,0]` and `![0,0]` is zero.
Its unrestricted ambient gradient changes by the normal vector `![0,1]`,
making the raw-gradient squared norm positive.  Thus a raw ambient-gradient
Lemma 5.12 is not a theorem of the source setup without an additional bridge
equating ambient and carrier gradients. -/
theorem lemma_5_12_legacy_rawGradient_refutable :
    ¬ (SOptLib.dualNorm
          (gradient lemma_5_12_rawGradientCounterexampleF
              (WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)] : EuclideanSpace ℝ (Fin 2)) -
            gradient lemma_5_12_rawGradientCounterexampleF
              (WithLp.toLp 2 ![(0 : ℝ), (0 : ℝ)] : EuclideanSpace ℝ (Fin 2))) ^ 2 ≤
        (0 : ℝ)) := by
  rw [lemma_5_12_rawGradientCounterexample_grad,
    lemma_5_12_rawGradientCounterexample_grad]
  norm_num [SOptLib.dualNorm_eq_norm, EuclideanSpace.norm_sq_eq]

/-- Setup-level soundness witness for retiring the legacy raw-gradient Lemma 5.12
surface.

This instantiates the original VRMD setup fields on the lower-dimensional carrier
`{x | x 1 = 0}` with the component extension `(u,v) ↦ u*v`.  On the carrier the
objective is identically zero, so `x* = ![0,0]` is composite-optimal and the
right-hand side of the old raw-gradient Lemma 5.12 statement is zero.  The
unrestricted ambient gradients at `![1,0]` and `![0,0]` differ in the normal
direction, contradicting the old conclusion.  Some setup-field certificates are
routine feasibility plumbing for this concrete instance; the contradiction uses
`lemma_5_12_legacy_rawGradient_refutable` above. -/
theorem lemma_5_12_legacy_rawGradient_false_at_feasible_setup :
    ∃ (setup :
        VarianceReducedMirrorDescentSetup Unit (EuclideanSpace ℝ (Fin 2)) Unit)
      (x xStar : {x : EuclideanSpace ℝ (Fin 2) // x ∈ setup.X}),
      (∀ z : {x : EuclideanSpace ℝ (Fin 2) // x ∈ setup.X},
          setup.PsiOn xStar ≤ setup.PsiOn z) ∧
        ¬ ((Fintype.card Unit : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                (((Fintype.card Unit : ℝ) * setup.q i)⁻¹ *
                  SOptLib.dualNorm
                    (gradient (setup.f i) x.1 -
                      gradient (setup.f i) xStar.1) ^ 2)) ≤
              2 * setup.LQ * (setup.PsiOn x - setup.PsiOn xStar)) := by
  classical
  let p0 : EuclideanSpace ℝ (Fin 2) :=
    (WithLp.toLp 2 ![(0 : ℝ), (0 : ℝ)] : EuclideanSpace ℝ (Fin 2))
  let p1 : EuclideanSpace ℝ (Fin 2) :=
    (WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)] : EuclideanSpace ℝ (Fin 2))
  let X : Set (EuclideanSpace ℝ (Fin 2)) := {u | u 1 = 0}
  let setup :
      VarianceReducedMirrorDescentSetup Unit (EuclideanSpace ℝ (Fin 2)) Unit :=
    { X := X
      w₀ := p0
      Li := fun _ => 1
      q := fun _ => 1
      f := fun _ => lemma_5_12_rawGradientCounterexampleF
      h := fun _ => 0
      v := fun u => ‖u‖ ^ 2 / 2
      ξ := fun _ _ => ()
      P := Measure.dirac ()
      hP := by infer_instance
      proxMap := fun x g =>
        ⟨lemma_5_12_hyperplaneProxPoint x g, by
          constructor
          · simp [X, lemma_5_12_hyperplaneProxPoint]
          · intro y hy
            -- The selected point is the explicit minimizer of the one-dimensional
            -- quadratic obtained by restricting the prox objective to the
            -- hyperplane `u 1 = 0`.
            exact lemma_5_12_hyperplaneProxPoint_minimizes x g y hy⟩
      hX_closed := by
        exact lemma_5_12_hyperplane_closed
      hX_convex := by
        exact lemma_5_12_hyperplane_convex
      hw₀_mem := by
        simp [X, p0]
      hLi_pos := by
        intro i
        norm_num
      hq_pos := by
        intro i
        norm_num
      hq_sum := by
        simp
      hξ_meas := by
        intro n
        exact measurable_const
      hξ_indep := by
        exact lemma_5_12_unit_sample_iIndep
      hξ_law := by
        intro n i
        simp
      hh_convex := by
        exact convexOn_const 0 lemma_5_12_hyperplane_convex
      hcomponent_convex := by
        intro i
        rw [convexOn_iff_forall_pos]
        constructor
        · exact lemma_5_12_hyperplane_convex
        · intro x hx y hy a b ha hb hab
          have hx1 : x 1 = 0 := hx
          have hy1 : y 1 = 0 := hy
          have hx_zero : lemma_5_12_rawGradientCounterexampleF x = 0 := by
            simp [lemma_5_12_rawGradientCounterexampleF, hx1]
          have hy_zero : lemma_5_12_rawGradientCounterexampleF y = 0 := by
            simp [lemma_5_12_rawGradientCounterexampleF, hy1]
          have hxy :
              lemma_5_12_rawGradientCounterexampleF (a • x + b • y) = 0 := by
            have hmem := lemma_5_12_hyperplane_convex hx hy (le_of_lt ha) (le_of_lt hb) hab
            have hmem1 : (a • x + b • y) 1 = 0 := hmem
            simp [lemma_5_12_rawGradientCounterexampleF, hmem1]
          rw [hx_zero, hy_zero, hxy]
          simpa using (le_refl (0 : ℝ))
      hcomponent_differentiable := by
        intro i
        exact lemma_5_12_rawGradientCounterexample_differentiableOn
      hv_contDiff := by
        exact lemma_5_12_quadraticPotential_contDiffOn
      hv_strongConvex := by
        exact lemma_5_12_quadraticPotential_strongConvexOn
      hcomponent_smooth := by
        intro i x y hx hy
        have hxgrad :
            vrmdComponentGradientCore X
                (fun _ : Unit => lemma_5_12_rawGradientCounterexampleF) i
                ⟨x, hx⟩ = 0 := by
          unfold vrmdComponentGradientCore
          apply carrierGradientFrom_eq_zero_of_forall_eq_zero
          intro z
          have hz : z.1 1 = 0 := z.2
          simp [lemma_5_12_rawGradientCounterexampleF, hz]
        have hygrad :
            vrmdComponentGradientCore X
                (fun _ : Unit => lemma_5_12_rawGradientCounterexampleF) i
                ⟨y, hy⟩ = 0 := by
          unfold vrmdComponentGradientCore
          apply carrierGradientFrom_eq_zero_of_forall_eq_zero
          intro z
          have hz : z.1 1 = 0 := z.2
          simp [lemma_5_12_rawGradientCounterexampleF, hz]
        rw [hxgrad, hygrad]
        simp [SOptLib.dualNorm_eq_norm]
      hcomponent_gradient_image_convex := by
        intro i
        apply Set.Subsingleton.convex
        intro a ha b hb
        rcases ha with ⟨u, hu, rfl⟩
        rcases hb with ⟨w, hw, rfl⟩
        have hzero : ∀ z ∈ X,
            SOptLib.totalizeOn X
              (vrmdComponentGradientCore X
                (fun _ : Unit => lemma_5_12_rawGradientCounterexampleF) i) z = 0 := by
          intro z hz
          rw [SOptLib.totalizeOn_of_mem X _ hz]
          unfold vrmdComponentGradientCore
          apply carrierGradientFrom_eq_zero_of_forall_eq_zero
          intro y
          have hy : y.1 1 = 0 := y.2
          simp [lemma_5_12_rawGradientCounterexampleF, hy]
        rw [hzero u (intrinsicInterior_subset hu), hzero w (intrinsicInterior_subset hw)] }
  refine ⟨setup, ⟨p1, ?_⟩, ⟨p0, ?_⟩, ?_, ?_⟩
  · simp [setup, X, p1]
  · simp [setup, X, p0]
  · intro z
    -- On the carrier, both `f` and `h` vanish.
    have hz : z.1 1 = 0 := z.2
    simp [setup, VarianceReducedMirrorDescentSetup.PsiOn,
      VarianceReducedMirrorDescentSetup.fOn, VarianceReducedMirrorDescentSetup.fAvg,
      VarianceReducedMirrorDescentSetup.hOn, SOptLib.compositeObjective,
      lemma_5_12_rawGradientCounterexampleF, hz]
    norm_num [p0]
  · -- The old raw-gradient conclusion reduces to the standalone normal-gradient
    -- contradiction above.
    simpa [setup, p0, p1, VarianceReducedMirrorDescentSetup.PsiOn,
      VarianceReducedMirrorDescentSetup.fOn, VarianceReducedMirrorDescentSetup.fAvg,
      VarianceReducedMirrorDescentSetup.hOn, VarianceReducedMirrorDescentSetup.LQ,
      vrmdLQCore, SOptLib.compositeObjective, lemma_5_12_rawGradientCounterexampleF]
      using lemma_5_12_legacy_rawGradient_refutable

/-- Carrier-gradient Lemma 5.12 in the finite-sum form used by Algorithm 5.6.

The paper's `∇ f_i(x)` is represented on `X` by `setup.componentGrad`, the
intrinsic carrier gradient selected by `SOptLib.carrierGradient`; see
`lemma_5_12_legacy_rawGradient_refutable` for why the old unrestricted ambient
gradient surface is not source-faithful on lower-dimensional carriers.

This theorem carries the corrected object model.  The paper-facing name
`lemma_5_12` below now has the same carrier-gradient surface, so downstream
VRMD statements no longer route through the refuted ambient-gradient head. -/
theorem lemma_5_12_carrier_core
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
      2 * setup.LQ * (setup.PsiOn x - setup.PsiOn xStar) := by
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
        2 * setup.LQ *
          (setup.fAvg x.1 - setup.fAvg xStar.1 -
            ⟪setup.gradF xStar.1, x.1 - xStar.1⟫_ℝ) :=
      lemma_5_12_linearized_f_gap_bound setup x xStar
    _ ≤ 2 * setup.LQ * (setup.PsiOn x - setup.PsiOn xStar) := by
      have hcoef : 0 ≤ 2 * setup.LQ := by
        nlinarith [setup.LQ_pos]
      exact mul_le_mul_of_nonneg_left
        (linearized_f_gap_le_Psi_gap_of_opt setup x xStar h_opt) hcoef

/-- Lan Lemma 5.12 in the source-faithful carrier-gradient form.

The scaffold originally used unrestricted ambient gradients of the extensions
`setup.f i : E → ℝ`.  The closed witness
`lemma_5_12_legacy_rawGradient_false_at_feasible_setup` shows that surface is
formally false on a feasible lower-dimensional carrier, so the paper-facing name
is migrated to the canonical gradient object used by Algorithm 5.6:
`setup.componentGrad`. -/
theorem lemma_5_12
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
      2 * setup.LQ * (setup.PsiOn x - setup.PsiOn xStar) := by
  exact lemma_5_12_carrier_core setup x xStar h_opt

/-- Carrier-gradient version of Lemma 5.12 matching the canonical VRMD
estimator. -/
theorem lemma_5_12_carrier
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) ≤
      2 * setup.LQ * (setup.PsiOn x - setup.PsiOn xStar) := by
  exact lemma_5_12 setup x xStar h_opt

/-- Deterministic two-center component-gradient split for Lemma 5.13.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 3: insert and subtract `∇ f_i(x*)`, split the squared component
difference, then apply Lemma 5.12 at the two endpoints. Search audit:
pre-searched mirror-step/filtration candidates were checked and rejected because
they concern prox updates or stochastic conditioning, not this deterministic
finite component split; the applicable local candidate is `lemma_5_12`. -/
theorem weighted_component_grad_diff_between_le_two_Psi_gaps_of_opt
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x y xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2) ≤
      4 * setup.LQ *
        ((setup.PsiOn x - setup.PsiOn xStar) +
          (setup.PsiOn y - setup.PsiOn xStar)) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_nonneg : 0 ≤ m⁻¹ := inv_nonneg.mpr (le_of_lt hm_pos)
  have hsplit_term : ∀ i : ι,
      ((m * setup.q i)⁻¹ *
          SOptLib.dualNorm
            (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2) ≤
        2 * (((m * setup.q i)⁻¹) *
          SOptLib.dualNorm
            (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) +
        2 * (((m * setup.q i)⁻¹) *
          SOptLib.dualNorm
            (setup.componentGrad i y.1 - setup.componentGrad i xStar.1) ^ 2) := by
    intro i
    have hmq_pos : 0 < m * setup.q i := mul_pos hm_pos (setup.hq_pos i)
    have hcoef_nonneg : 0 ≤ (m * setup.q i)⁻¹ :=
      inv_nonneg.mpr (le_of_lt hmq_pos)
    let gx : E := setup.componentGrad i x.1
    let gy : E := setup.componentGrad i y.1
    let gs : E := setup.componentGrad i xStar.1
    have hnorm :
        ‖gy - gx‖ ≤ ‖gy - gs‖ + ‖gx - gs‖ := by
      calc
        ‖gy - gx‖ = ‖(gy - gs) - (gx - gs)‖ := by
            congr 1
            abel
        _ ≤ ‖gy - gs‖ + ‖gx - gs‖ := norm_sub_le (gy - gs) (gx - gs)
    have hnorm_sq :
        ‖gy - gx‖ ^ 2 ≤ 2 * ‖gx - gs‖ ^ 2 + 2 * ‖gy - gs‖ ^ 2 := by
      have hsq_mono :
          ‖gy - gx‖ ^ 2 ≤ (‖gy - gs‖ + ‖gx - gs‖) ^ 2 := by
        nlinarith [hnorm, norm_nonneg (gy - gx), norm_nonneg (gy - gs),
          norm_nonneg (gx - gs)]
      have hsq_expand :
          (‖gy - gs‖ + ‖gx - gs‖) ^ 2 ≤
            2 * ‖gx - gs‖ ^ 2 + 2 * ‖gy - gs‖ ^ 2 := by
        nlinarith [sq_nonneg (‖gy - gs‖ - ‖gx - gs‖)]
      exact le_trans hsq_mono hsq_expand
    have hdual_sq :
        SOptLib.dualNorm (gy - gx) ^ 2 ≤
          2 * SOptLib.dualNorm (gx - gs) ^ 2 +
            2 * SOptLib.dualNorm (gy - gs) ^ 2 := by
      simpa [SOptLib.dualNorm_eq_norm, add_comm, add_left_comm, add_assoc]
        using hnorm_sq
    calc
      (m * setup.q i)⁻¹ * SOptLib.dualNorm (gy - gx) ^ 2
          ≤ (m * setup.q i)⁻¹ *
              (2 * SOptLib.dualNorm (gx - gs) ^ 2 +
                2 * SOptLib.dualNorm (gy - gs) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hdual_sq hcoef_nonneg
      _ =
        2 * (((m * setup.q i)⁻¹) *
          SOptLib.dualNorm (gx - gs) ^ 2) +
        2 * (((m * setup.q i)⁻¹) *
          SOptLib.dualNorm (gy - gs) ^ 2) := by
            ring
  let Ax : ℝ :=
    m⁻¹ * Finset.sum Finset.univ
      (fun i : ι =>
        ((m * setup.q i)⁻¹ *
          SOptLib.dualNorm
            (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2))
  let Ay : ℝ :=
    m⁻¹ * Finset.sum Finset.univ
      (fun i : ι =>
        ((m * setup.q i)⁻¹ *
          SOptLib.dualNorm
            (setup.componentGrad i y.1 - setup.componentGrad i xStar.1) ^ 2))
  have hsplit :
      m⁻¹ * Finset.sum Finset.univ
          (fun i : ι =>
            ((m * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2)) ≤
        2 * Ax + 2 * Ay := by
    have hsum :
        Finset.sum Finset.univ
            (fun i : ι =>
              ((m * setup.q i)⁻¹ *
                SOptLib.dualNorm
                  (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2)) ≤
          Finset.sum Finset.univ
            (fun i : ι =>
              2 * (((m * setup.q i)⁻¹) *
                SOptLib.dualNorm
                  (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) +
              2 * (((m * setup.q i)⁻¹) *
                SOptLib.dualNorm
                  (setup.componentGrad i y.1 - setup.componentGrad i xStar.1) ^ 2)) := by
      exact Finset.sum_le_sum (fun i _hi => hsplit_term i)
    calc
      m⁻¹ * Finset.sum Finset.univ
          (fun i : ι =>
            ((m * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2))
          ≤
        m⁻¹ * Finset.sum Finset.univ
          (fun i : ι =>
            2 * (((m * setup.q i)⁻¹) *
              SOptLib.dualNorm
                (setup.componentGrad i x.1 - setup.componentGrad i xStar.1) ^ 2) +
            2 * (((m * setup.q i)⁻¹) *
              SOptLib.dualNorm
                (setup.componentGrad i y.1 - setup.componentGrad i xStar.1) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hsum hm_nonneg
      _ = 2 * Ax + 2 * Ay := by
          dsimp [Ax, Ay]
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
  have hx : Ax ≤ 2 * setup.LQ * (setup.PsiOn x - setup.PsiOn xStar) := by
    simpa [Ax, m] using lemma_5_12 setup x xStar h_opt
  have hy : Ay ≤ 2 * setup.LQ * (setup.PsiOn y - setup.PsiOn xStar) := by
    simpa [Ay, m] using lemma_5_12 setup y xStar h_opt
  calc
    (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2)
        =
      m⁻¹ * Finset.sum Finset.univ
          (fun i : ι =>
            ((m * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i y.1 - setup.componentGrad i x.1) ^ 2)) := by
          simp [m]
    _ ≤ 2 * Ax + 2 * Ay := hsplit
    _ ≤
      4 * setup.LQ *
        ((setup.PsiOn x - setup.PsiOn xStar) +
          (setup.PsiOn y - setup.PsiOn xStar)) := by
        nlinarith [hx, hy]

/-! Lemma 5.13 is split into three route-local stochastic control helpers.
The split mirrors the textbook proof: conditional unbiasedness, the linearized
smooth gap variance estimate, and the two-composite-gap variance estimate. -/

/-- Prefix-filtration form of the Lemma 5.13 mean-zero estimator identity.

This is the global sample-prefix version of Lan Lemma 5.13 proof step 1.  The
epoch-local theorem below follows from this statement by the conditional
expectation tower property and `epochIteratePast_le_globalSamplePrefix`.
Search audit: checked `condExp_oracle_noise_eq_zero_of_iid_adapted`,
`oracle_noise_setIntegral_eq_zero_of_past_measurable`,
`_root_.samplePrefixFiltration_indep_current`, and local
`delta_fixed_law_integral_eq_zero`; the remaining work is the VRMD-specific
transport from the deterministic prefix factorization of the iterates to the
generic independent fresh-sample conditional-centering lemma. -/
private theorem delta_condexp_eq_zero_globalSamplePrefix
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    ((setup.P[setup.deltaProcessAt s t |
        (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) =ᵐ[setup.P]
      fun _ => 0) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  have hY : Measurable (setup.sampledIndexAt s t) := by
    rw [setup.sampledIndexAt_eq]
    exact setup.hξ_meas _
  have hpast_indep_current :
      Indep ((setup.filtration).seq N)
        (MeasurableSpace.comap (setup.sampledIndexAt s t)
          (by infer_instance : MeasurableSpace ι)) setup.P := by
    simpa [VarianceReducedMirrorDescentSetup.filtration,
      VarianceReducedMirrorDescentSetup.sampledIndexAt_eq, N] using
      (_root_.samplePrefixFiltration_indep_current
        setup.ξ setup.hξ_meas setup.hξ_indep N)
  have hNepoch : setup.epochOffset (s - 1) ≤ N := by
    simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
  obtain ⟨decodeInner, hdecodeInner⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  have hinner_decode :
      setup.paperInnerIterAt s t = fun ω => decodeInner (prefixVec ω) := by
    simpa [prefixVec, N] using hdecodeInner
  let snapFeasible : (Fin N → ι) → {x : E // x ∈ setup.X} := fun xs =>
    if h : decodeSnap xs ∈ setup.X then ⟨decodeSnap xs, h⟩
    else ⟨setup.w₀, setup.hw₀_mem⟩
  let innerFeasible : (Fin N → ι) → {x : E // x ∈ setup.X} := fun xs =>
    if h : decodeInner xs ∈ setup.X then ⟨decodeInner xs, h⟩
    else ⟨setup.w₀, setup.hw₀_mem⟩
  let decodedDelta : (Fin N → ι) → ι → E := fun xs i =>
    setup.delta (snapFeasible xs).1 (innerFeasible xs).1 i
  have hGg_meas :
      Measurable (fun p : (Fin N → ι) × ι => decodedDelta p.1 p.2 - (0 : E)) := by
    exact Measurable.of_discrete
  have h_indep :
      ∀ A : Set Ω, MeasurableSet[(setup.filtration).seq N] A →
        IndepFun
          (fun ω => (A.indicator (fun _ => (1 : ℝ)) ω, prefixVec ω))
          (setup.sampledIndexAt s t) setup.P := by
    intro A hA
    have hAind : Measurable[(setup.filtration).seq N]
        (fun ω => A.indicator (fun _ => (1 : ℝ)) ω) := by
      exact measurable_const.indicator hA
    exact vrmd_indepFun_of_past_measurable_current_iid_sample
      (hAind.prodMk hprefix_past) hpast_indep_current
  have h_int :
      Integrable
        (fun ω => decodedDelta (prefixVec ω) (setup.sampledIndexAt s t ω) - (0 : E))
        setup.P := by
    have hmeas : Measurable
        (fun ω => decodedDelta (prefixVec ω) (setup.sampledIndexAt s t ω) - (0 : E)) := by
      simpa using hGg_meas.comp (hprefix_top.prodMk hY)
    let vals : Finset ℝ :=
      (Finset.univ.image
        (fun p : (Fin N → ι) × ι => ‖decodedDelta p.1 p.2 - (0 : E)‖))
    have hvals_nonempty : vals.Nonempty := by
      exact Finset.Nonempty.image (Finset.univ_nonempty :
        (Finset.univ : Finset ((Fin N → ι) × ι)).Nonempty) _
    let C : ℝ := vals.max' hvals_nonempty
    have hbound :
        ∀ ω, ‖decodedDelta (prefixVec ω) (setup.sampledIndexAt s t ω) - (0 : E)‖ ≤
          C := by
      intro ω
      dsimp [C, vals]
      exact Finset.le_max' _ _ (by
        refine Finset.mem_image.mpr ?_
        exact ⟨(prefixVec ω, setup.sampledIndexAt s t ω), by simp, rfl⟩)
    exact Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all setup.P hbound)
  have hfixed_zero :
      ∀ xs : Fin N → ι,
        ∫ y, decodedDelta xs y - (0 : E)
          ∂(Measure.map (setup.sampledIndexAt s t) setup.P) = 0 := by
    intro xs
    have hzero := setup.deltaFixedLawIntegralEqZero s t (snapFeasible xs) (innerFeasible xs)
    simpa [decodedDelta] using hzero
  have hcenter :
      setup.P[(fun ω => decodedDelta (prefixVec ω) (setup.sampledIndexAt s t ω) - (0 : E)) |
          (setup.filtration).seq N] =ᵐ[setup.P] 0 := by
    exact condExp_oracle_noise_eq_zero_of_iid_adapted
      setup.P ((setup.filtration).seq N) hm decodedDelta (fun _ => (0 : E))
      prefixVec (setup.sampledIndexAt s t)
      hGg_meas hprefix_past hprefix_top hY h_indep h_int hfixed_zero
  have hprocess_eq :
      setup.deltaProcessAt s t =ᵐ[setup.P]
        (fun ω => decodedDelta (prefixVec ω) (setup.sampledIndexAt s t ω) - (0 : E)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hsval : decodeSnap (prefixVec ω) = setup.snapshotIter (s - 1) ω :=
      (congrFun hsnap_decode ω).symm
    have hival : decodeInner (prefixVec ω) = setup.paperInnerIterAt s t ω :=
      (congrFun hinner_decode ω).symm
    have hsmem_actual : setup.snapshotIter (s - 1) ω ∈ setup.X :=
      setup.snapshotIter_mem (s - 1) ω
    have himem_actual : setup.paperInnerIterAt s t ω ∈ setup.X :=
      setup.paperInnerIterAt_mem s t ω
    have hsfeat : (snapFeasible (prefixVec ω)).1 = setup.snapshotIter (s - 1) ω := by
      dsimp [snapFeasible]
      simp [hsval, hsmem_actual]
    have hifeat : (innerFeasible (prefixVec ω)).1 = setup.paperInnerIterAt s t ω := by
      dsimp [innerFeasible]
      simp [hival, himem_actual]
    simp [VarianceReducedMirrorDescentSetup.deltaProcessAt, decodedDelta,
      hsfeat, hifeat]
  have hfinal :
      setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N] =ᵐ[setup.P] 0 := by
    calc
      setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N] =ᵐ[setup.P]
          setup.P[(fun ω => decodedDelta (prefixVec ω) (setup.sampledIndexAt s t ω) -
              (0 : E)) |
            (setup.filtration).seq N] :=
        MeasureTheory.condExp_congr_ae hprocess_eq
      _ =ᵐ[setup.P] 0 := hcenter
  simpa [N] using hfinal

/-- Conditional unbiasedness part of Lan Lemma 5.13.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 1: condition on `x_1, ..., x_t` and average only over the fresh
sampled component `i_t`.  Search audit: checked pre-searched candidates
`iIndepFun.indep_past_iSup_current`,
`fixedOracleDeviation_integral_law_eq_zero`, and
`condExp_oracle_noise_eq_zero_of_iid_adapted`; they provide generic fresh-sample
or fixed-oracle centering infrastructure, but this helper must also specialize
the paper's finite VR estimator `delta`, the epoch-local history
`epochIteratePast`, and `delta_finite_weighted_sum_eq_zero`. -/
theorem delta_condexp_eq_zero_at_epoch
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    ((setup.P[setup.deltaProcessAt s t |
        setup.epochIteratePast s t]) =ᵐ[setup.P]
      fun _ => 0) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  have hprefix :
      ((setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N]) =ᵐ[setup.P]
        fun _ => 0) := by
    simpa [N] using delta_condexp_eq_zero_globalSamplePrefix setup s t hs
  have htower :
      setup.P[setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N] |
          setup.epochIteratePast s t] =ᵐ[setup.P]
        setup.P[setup.deltaProcessAt s t | setup.epochIteratePast s t] := by
    simpa [N] using
      (MeasureTheory.condExp_condExp_of_le
        (μ := setup.P)
        (m₁ := setup.epochIteratePast s t)
        (m₂ := (setup.filtration).seq N)
        (m₀ := (by infer_instance : MeasurableSpace Ω))
        (f := setup.deltaProcessAt s t)
        (by simpa [N] using setup.epochIteratePast_le_globalSamplePrefix s t)
        (by simpa [N] using (setup.filtration).le N))
  calc
    setup.P[setup.deltaProcessAt s t | setup.epochIteratePast s t]
        =ᵐ[setup.P]
      setup.P[setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N] |
          setup.epochIteratePast s t] := htower.symm
    _ =ᵐ[setup.P]
      setup.P[(fun _ : Ω => (0 : E)) | setup.epochIteratePast s t] :=
        MeasureTheory.condExp_congr_ae hprefix
    _ =ᵐ[setup.P] fun _ => 0 := by
        change setup.P[(0 : Ω → E) | setup.epochIteratePast s t] =ᵐ[setup.P]
          (0 : Ω → E)
        rw [MeasureTheory.condExp_zero]

/-- Finite weighted centering can only decrease the second moment.

This is the deterministic Hilbert variance algebra used in Lan Lemma 5.13,
proof step 2. Search audit: checked `weighted_variance_sum_expectation_bound`,
`miniBatchResidual_sum_secondMoment_le_card_mul_variance`, and
`integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero`; those package
stochastic expectation/covariance transfers, while this proof needs the
pointwise finite identity
`∑ w_i ‖a_i - ∑ w_j a_j‖² = ∑ w_i ‖a_i‖² - ‖∑ w_i a_i‖²`. -/
private theorem finite_weighted_centered_sq_le_uncentered_sq
    (w : ι → ℝ) (a : ι → E)
    (hw_sum : Finset.sum Finset.univ w = 1) :
    Finset.sum Finset.univ
        (fun i : ι =>
          w i * ‖a i - Finset.sum Finset.univ (fun j : ι => w j • a j)‖ ^ 2) ≤
      Finset.sum Finset.univ (fun i : ι => w i * ‖a i‖ ^ 2) := by
  classical
  let μ : E := Finset.sum Finset.univ (fun i : ι => w i • a i)
  have hinner :
      Finset.sum Finset.univ (fun i : ι => w i * ⟪a i, μ⟫_ℝ) = ‖μ‖ ^ 2 := by
    calc
      Finset.sum Finset.univ (fun i : ι => w i * ⟪a i, μ⟫_ℝ)
          = ⟪Finset.sum Finset.univ (fun i : ι => w i • a i), μ⟫_ℝ := by
              rw [sum_inner]
              simp [real_inner_smul_left]
      _ = ‖μ‖ ^ 2 := by
              simp [μ, real_inner_self_eq_norm_sq]
  have hconst :
      Finset.sum Finset.univ (fun i : ι => w i * ‖μ‖ ^ 2) = ‖μ‖ ^ 2 := by
    rw [← Finset.sum_mul]
    simp [hw_sum]
  have hidentity :
      Finset.sum Finset.univ (fun i : ι => w i * ‖a i - μ‖ ^ 2) =
        Finset.sum Finset.univ (fun i : ι => w i * ‖a i‖ ^ 2) - ‖μ‖ ^ 2 := by
    calc
      Finset.sum Finset.univ (fun i : ι => w i * ‖a i - μ‖ ^ 2)
          =
        Finset.sum Finset.univ
          (fun i : ι =>
            w i * ‖a i‖ ^ 2 - 2 * (w i * ⟪a i, μ⟫_ℝ) + w i * ‖μ‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [norm_sub_sq_real]
            ring
      _ = Finset.sum Finset.univ (fun i : ι => w i * ‖a i‖ ^ 2) - ‖μ‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum]
            rw [hinner, hconst]
            ring
  simpa [μ, hidentity] using
    (sub_le_self
      (Finset.sum Finset.univ (fun i : ι => w i * ‖a i‖ ^ 2))
      (sq_nonneg ‖μ‖))

/-- Fixed-fiber second-moment bound for the VRMD noise term.

This is the deterministic finite-law part of Lan Lemma 5.13 proof step 2:
after freezing `(tilde{x}, x_t)`, expand the centered estimator variance, drop
the nonpositive centered-square term, normalize the `q_i (m q_i)^{-2}` factors,
and apply `lemma_5_12_linearized_f_gap_bound`. Search audit: checked
`randomIterate_variance_bound_of_fixed_variance`,
`weighted_variance_sum_expectation_bound`, and
`fixedOracleDeviation_integral_map_sq_le`; those transfer already-proved fixed
variance bounds through random queries, while this paper step first proves the
fixed bound from the explicit finite SVRG estimator algebra. -/
private theorem fixed_fiber_delta_sq_le_linearized_gap
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s)
    (xTilde x : {x : E // x ∈ setup.X}) :
    ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
        ∂Measure.map (setup.sampledIndexAt s t) setup.P ≤
      2 * setup.LQ *
        (setup.fOn xTilde - setup.fOn x -
          ⟪setup.gradF x.1, xTilde.1 - x.1⟫_ℝ) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure (Measure.map (setup.sampledIndexAt s t) setup.P) :=
    Measure.isFiniteMeasure_map setup.P (setup.sampledIndexAt s t)
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hq_ne : ∀ i : ι, setup.q i ≠ 0 := fun i => ne_of_gt (setup.hq_pos i)
  have h_law_sum :
      ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
          ∂Measure.map (setup.sampledIndexAt s t) setup.P =
        Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2) := by
    have hfin :
        Integrable
          (fun i : ι => SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2)
          (Measure.map (setup.sampledIndexAt s t) setup.P) := by
      exact Integrable.of_finite
    have hY : Measurable (setup.sampledIndexAt s t) := by
      rw [setup.sampledIndexAt_eq]
      exact setup.hξ_meas _
    rw [MeasureTheory.integral_fintype hfin]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hmass :
        (Measure.map (setup.sampledIndexAt s t) setup.P).real {i} =
          setup.q i := by
      rw [MeasureTheory.measureReal_def,
        Measure.map_apply hY (measurableSet_singleton i)]
      change (setup.P {ω | setup.sampledIndexAt s t ω = i}).toReal =
        setup.q i
      rw [setup.sampledIndexAt_law s t i]
      exact ENNReal.toReal_ofReal (le_of_lt (setup.hq_pos i))
    rw [hmass]
    simp
  let a : ι → E := fun i =>
    ((m * setup.q i)⁻¹) •
      (setup.componentGrad i x.1 - setup.componentGrad i xTilde.1)
  let mean : E := setup.gradF x.1 - setup.gradF xTilde.1
  have hdelta : ∀ i : ι, setup.delta xTilde.1 x.1 i = a i - mean := by
    intro i
    unfold VarianceReducedMirrorDescentSetup.delta
      VarianceReducedMirrorDescentSetup.estimator
    simp [a, mean]
    abel
  have hcoef :
      ∀ i : ι,
        setup.q i * ((m * setup.q i)⁻¹) = m⁻¹ := by
    intro i
    field_simp [hm_ne, hq_ne i]
  have hmean : Finset.sum Finset.univ (fun i : ι => setup.q i • a i) = mean := by
    calc
      Finset.sum Finset.univ (fun i : ι => setup.q i • a i)
          =
        Finset.sum Finset.univ
          (fun i : ι =>
            m⁻¹ • (setup.componentGrad i x.1 - setup.componentGrad i xTilde.1)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            dsimp [a]
            rw [smul_smul, hcoef i]
      _ = m⁻¹ •
          Finset.sum Finset.univ
            (fun i : ι => setup.componentGrad i x.1 - setup.componentGrad i xTilde.1) := by
            rw [Finset.smul_sum]
      _ = mean := by
            rw [Finset.sum_sub_distrib]
            simp [mean, VarianceReducedMirrorDescentSetup.gradF_def, smul_sub, m]
  have hvar :
      Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2) ≤
        Finset.sum Finset.univ
          (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) := by
    have hbase :=
      finite_weighted_centered_sq_le_uncentered_sq
        (w := setup.q) (a := a) setup.hq_sum
    calc
      Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2)
          =
        Finset.sum Finset.univ
          (fun i : ι => setup.q i * ‖a i - mean‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hdelta i, SOptLib.dualNorm_sq_eq_norm_sq]
      _ ≤ Finset.sum Finset.univ (fun i : ι => setup.q i * ‖a i‖ ^ 2) := by
            simpa [hmean] using hbase
      _ = Finset.sum Finset.univ
          (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [SOptLib.dualNorm_sq_eq_norm_sq]
  have hnormalize :
      Finset.sum Finset.univ
          (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) =
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι =>
              ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
                SOptLib.dualNorm
                  (setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) ^ 2) := by
    dsimp [m] at hm_pos hm_ne hcoef a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hmq_pos : 0 < (Fintype.card ι : ℝ) * setup.q i :=
      mul_pos hm_pos (setup.hq_pos i)
    have hmq_ne : (Fintype.card ι : ℝ) * setup.q i ≠ 0 := ne_of_gt hmq_pos
    have hscalar_nonneg : 0 ≤ (((Fintype.card ι : ℝ) * setup.q i)⁻¹) :=
      inv_nonneg.mpr (le_of_lt hmq_pos)
    have hnorm_rev :
        ‖setup.componentGrad i x.1 - setup.componentGrad i xTilde.1‖ =
          ‖setup.componentGrad i xTilde.1 - setup.componentGrad i x.1‖ := by
      have hneg :
          setup.componentGrad i x.1 - setup.componentGrad i xTilde.1 =
            -(setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) := by
        abel
      rw [hneg, norm_neg]
    dsimp [a]
    rw [SOptLib.dualNorm_sq_eq_norm_sq, SOptLib.dualNorm_sq_eq_norm_sq]
    rw [norm_smul, Real.norm_of_nonneg hscalar_nonneg, hnorm_rev]
    field_simp [hmq_ne]
  have h512 := lemma_5_12_linearized_f_gap_bound setup xTilde x
  calc
    ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
        ∂Measure.map (setup.sampledIndexAt s t) setup.P
        =
      Finset.sum Finset.univ
        (fun i : ι =>
          setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2) := h_law_sum
    _ ≤ Finset.sum Finset.univ
        (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) := hvar
    _ =
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) ^ 2) := hnormalize
    _ ≤
      2 * setup.LQ *
        (setup.fOn xTilde - setup.fOn x -
          ⟪setup.gradF x.1, xTilde.1 - x.1⟫_ℝ) := by
        simpa [VarianceReducedMirrorDescentSetup.fOn] using h512

/-- Fixed-fiber second-moment bound up to the weighted component-gradient
difference sum.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 3 before applying Lemma 5.12 at `x_t` and `\tilde{x}`. Search
audit: checked pre-searched conditioning/measurability candidates
`iIndepFun.indep_past_iSup_current`, `IdentDistrib.integral_comp_eq_of_measurable`,
`Measurable.of_measurableSpace_le`, `bregmanDivergence_eq_formula_of_interior_iterate`,
and `measurable_bregman_start_of_measurable_iterate`; those concern filtration,
map-integral, or Bregman measurability infrastructure, while this helper is the
VRMD-specific fixed finite-law centered-square algebra already isolated in
`fixed_fiber_delta_sq_le_linearized_gap`. -/
private theorem fixed_fiber_delta_sq_le_weighted_component_grad_diff
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s)
    (xTilde x : {x : E // x ∈ setup.X}) :
    ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
        ∂Measure.map (setup.sampledIndexAt s t) setup.P ≤
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) ^ 2) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure (Measure.map (setup.sampledIndexAt s t) setup.P) :=
    Measure.isFiniteMeasure_map setup.P (setup.sampledIndexAt s t)
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hq_ne : ∀ i : ι, setup.q i ≠ 0 := fun i => ne_of_gt (setup.hq_pos i)
  have h_law_sum :
      ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
          ∂Measure.map (setup.sampledIndexAt s t) setup.P =
        Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2) := by
    have hfin :
        Integrable
          (fun i : ι => SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2)
          (Measure.map (setup.sampledIndexAt s t) setup.P) := by
      exact Integrable.of_finite
    have hY : Measurable (setup.sampledIndexAt s t) := by
      rw [setup.sampledIndexAt_eq]
      exact setup.hξ_meas _
    rw [MeasureTheory.integral_fintype hfin]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hmass :
        (Measure.map (setup.sampledIndexAt s t) setup.P).real {i} =
          setup.q i := by
      rw [MeasureTheory.measureReal_def,
        Measure.map_apply hY (measurableSet_singleton i)]
      change (setup.P {ω | setup.sampledIndexAt s t ω = i}).toReal =
        setup.q i
      rw [setup.sampledIndexAt_law s t i]
      exact ENNReal.toReal_ofReal (le_of_lt (setup.hq_pos i))
    rw [hmass]
    simp
  let a : ι → E := fun i =>
    ((m * setup.q i)⁻¹) •
      (setup.componentGrad i x.1 - setup.componentGrad i xTilde.1)
  let mean : E := setup.gradF x.1 - setup.gradF xTilde.1
  have hdelta : ∀ i : ι, setup.delta xTilde.1 x.1 i = a i - mean := by
    intro i
    unfold VarianceReducedMirrorDescentSetup.delta
      VarianceReducedMirrorDescentSetup.estimator
    simp [a, mean]
    abel
  have hcoef :
      ∀ i : ι,
        setup.q i * ((m * setup.q i)⁻¹) = m⁻¹ := by
    intro i
    field_simp [hm_ne, hq_ne i]
  have hmean : Finset.sum Finset.univ (fun i : ι => setup.q i • a i) = mean := by
    calc
      Finset.sum Finset.univ (fun i : ι => setup.q i • a i)
          =
        Finset.sum Finset.univ
          (fun i : ι =>
            m⁻¹ • (setup.componentGrad i x.1 - setup.componentGrad i xTilde.1)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            dsimp [a]
            rw [smul_smul, hcoef i]
      _ = m⁻¹ •
          Finset.sum Finset.univ
            (fun i : ι => setup.componentGrad i x.1 - setup.componentGrad i xTilde.1) := by
            rw [Finset.smul_sum]
      _ = mean := by
            rw [Finset.sum_sub_distrib]
            simp [mean, VarianceReducedMirrorDescentSetup.gradF_def, smul_sub, m]
  have hvar :
      Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2) ≤
        Finset.sum Finset.univ
          (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) := by
    have hbase :=
      finite_weighted_centered_sq_le_uncentered_sq
        (w := setup.q) (a := a) setup.hq_sum
    calc
      Finset.sum Finset.univ
          (fun i : ι =>
            setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2)
          =
        Finset.sum Finset.univ
          (fun i : ι => setup.q i * ‖a i - mean‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hdelta i, SOptLib.dualNorm_sq_eq_norm_sq]
      _ ≤ Finset.sum Finset.univ (fun i : ι => setup.q i * ‖a i‖ ^ 2) := by
            simpa [hmean] using hbase
      _ = Finset.sum Finset.univ
          (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [SOptLib.dualNorm_sq_eq_norm_sq]
  have hnormalize :
      Finset.sum Finset.univ
          (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) =
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι =>
              ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
                SOptLib.dualNorm
                  (setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) ^ 2) := by
    dsimp [m] at hm_pos hm_ne hcoef a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hmq_pos : 0 < (Fintype.card ι : ℝ) * setup.q i :=
      mul_pos hm_pos (setup.hq_pos i)
    have hmq_ne : (Fintype.card ι : ℝ) * setup.q i ≠ 0 := ne_of_gt hmq_pos
    have hscalar_nonneg : 0 ≤ (((Fintype.card ι : ℝ) * setup.q i)⁻¹) :=
      inv_nonneg.mpr (le_of_lt hmq_pos)
    have hnorm_rev :
        ‖setup.componentGrad i x.1 - setup.componentGrad i xTilde.1‖ =
          ‖setup.componentGrad i xTilde.1 - setup.componentGrad i x.1‖ := by
      have hneg :
          setup.componentGrad i x.1 - setup.componentGrad i xTilde.1 =
            -(setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) := by
        abel
      rw [hneg, norm_neg]
    dsimp [a]
    rw [SOptLib.dualNorm_sq_eq_norm_sq, SOptLib.dualNorm_sq_eq_norm_sq]
    rw [norm_smul, Real.norm_of_nonneg hscalar_nonneg, hnorm_rev]
    field_simp [hmq_ne]
  calc
    ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
        ∂Measure.map (setup.sampledIndexAt s t) setup.P
        =
      Finset.sum Finset.univ
        (fun i : ι =>
          setup.q i * SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2) := h_law_sum
    _ ≤ Finset.sum Finset.univ
        (fun i : ι => setup.q i * SOptLib.dualNorm (a i) ^ 2) := hvar
    _ =
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) ^ 2) := hnormalize

/-- Fixed-fiber two-composite-gap version of Lan Lemma 5.13 step 3.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 3 after the finite centered-square expansion: the deterministic
endpoint is exactly the local
`weighted_component_grad_diff_between_le_two_Psi_gaps_of_opt`. Search audit:
checked generic variance-transfer candidates and the local linearized fixed
fiber helper; the source-faithful candidate is the component-gradient split,
not a scalar linearized-gap bridge. -/
private theorem fixed_fiber_delta_sq_le_two_Psi_gaps
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s)
    (xTilde x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
        ∂Measure.map (setup.sampledIndexAt s t) setup.P ≤
      4 * setup.LQ *
        ((setup.PsiOn x - setup.PsiOn xStar) +
          (setup.PsiOn xTilde - setup.PsiOn xStar)) := by
  calc
    ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
        ∂Measure.map (setup.sampledIndexAt s t) setup.P
        ≤
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            ((Fintype.card ι : ℝ) * setup.q i)⁻¹ *
              SOptLib.dualNorm
                (setup.componentGrad i xTilde.1 - setup.componentGrad i x.1) ^ 2) :=
        fixed_fiber_delta_sq_le_weighted_component_grad_diff setup s t xTilde x
    _ ≤ 4 * setup.LQ *
        ((setup.PsiOn x - setup.PsiOn xStar) +
          (setup.PsiOn xTilde - setup.PsiOn xStar)) := by
        simpa using
          weighted_component_grad_diff_between_le_two_Psi_gaps_of_opt
            setup x xTilde xStar h_opt

/-- Product-law transfer with a prefix-dependent scalar bound.

This is the conditional-expectation infrastructure needed for Lan Lemma 5.13
proof step 2 after freezing the finite sample prefix. Search audit: checked
SOptLib `integral_comp_le_of_indep_fixed_integral_bound`,
`integrable_comp_of_indep_fixed_integral_bound`, and Mathlib
`MeasureTheory.condExp_mono`; the SOptLib lemma has a constant bound `C`, while
this stochastic bridge needs the decoded-prefix-dependent bound `B (X ω)`. -/
private theorem integral_comp_le_of_indep_fixed_integral_bound_fun
    {W S : Type*} [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → S → ℝ} {B : W → ℝ} {X : Ω → W} {Y : Ω → S}
    (hφ : Measurable (Function.uncurry φ))
    (hB : Measurable B)
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hB_int : Integrable (fun ω => B (X ω)) P)
    (hfixed_bound :
      (fun w => ∫ y, φ w y ∂ν) ≤ᵐ[Measure.map X P] B) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ ∫ ω, B (X ω) ∂P := by
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_f_meas : Measurable (fun p : W × S => φ p.1 p.2) := hφ
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  have h_int_prod : Integrable (fun p : W × S => φ p.1 p.2) ((P.map X).prod ν) := by
    have h1 : Integrable (fun p : W × S => φ p.1 p.2)
        (P.map (fun ω => (X ω, Y ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  have hB_map_int : Integrable B (P.map X) :=
    (integrable_map_measure hB.aestronglyMeasurable hX.aemeasurable).mpr hB_int
  calc
    ∫ ω, φ (X ω) (Y ω) ∂P
        = ∫ p : W × S, φ p.1 p.2 ∂P.map (fun ω => (X ω, Y ω)) :=
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm
    _ = ∫ p : W × S, φ p.1 p.2 ∂(P.map X).prod ν := by rw [h_prod_eq]
    _ = ∫ w : W, ∫ y : S, φ w y ∂ν ∂P.map X := integral_prod _ h_int_prod
    _ ≤ ∫ w : W, B w ∂P.map X := by
      exact integral_mono_ae h_int_prod.integral_prod_left hB_map_int hfixed_bound
    _ = ∫ ω, B (X ω) ∂P := integral_map hX.aemeasurable hB.aestronglyMeasurable

/-- Set-integral characterization for an upper conditional-expectation bound.

This packages the Mathlib martingale pattern used in `submartingale_of_setIntegral_le`.
Search audit: checked Mathlib `MeasureTheory.condExp_mono`,
`MeasureTheory.ae_le_of_forall_setIntegral_le`, and
`MeasureTheory.setIntegral_condExp`; monotonicity is pointwise-before-conditioning,
whereas this route proves the conditional bound from all past-measurable
set-integral inequalities. -/
private theorem condExp_le_of_forall_setIntegral_le
    {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ}
    (hf : Integrable f P) (hg_int : Integrable g P)
    (hg_sm : StronglyMeasurable[m] g)
    (hsets :
      ∀ A : Set Ω, MeasurableSet[m] A →
        ∫ ω in A, f ω ∂P ≤ ∫ ω in A, g ω ∂P) :
    P[f | m] ≤ᵐ[P] g := by
  suffices P[f | m] ≤ᵐ[P.trim hm] g by
    exact ae_le_of_ae_le_trim this
  suffices 0 ≤ᵐ[P.trim hm] g - P[f | m] by
    filter_upwards [this] with ω hω
    exact sub_nonneg.mp (by simpa using hω)
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((hg_int.sub integrable_condExp).trim _ (hg_sm.sub stronglyMeasurable_condExp))
    fun A hA _ => ?_
  specialize hsets A hA
  rwa [← setIntegral_trim _ (hg_sm.sub stronglyMeasurable_condExp) hA,
    integral_sub' hg_int.integrableOn integrable_condExp.integrableOn, sub_nonneg,
    setIntegral_condExp hm hf hA]

set_option maxHeartbeats 800000

/-- Prefix-conditioning bridge for the fixed-fiber Lemma 5.13 square bound.

This isolates the stochastic part of Lan Lemma 5.13 proof step 2: the snapshot
and current iterate factor through the strict global sample prefix, the fresh
sampled index is independent of that prefix, and the conditional expectation is
therefore bounded by the fixed-fiber integral evaluated at the decoded prefix
values. Search audit: checked `integral_comp_le_of_indep_fixed_integral_bound`,
`condExp_oracle_noise_eq_zero_of_iid_adapted`, and Mathlib
`MeasureTheory.condExp_mono`; the available lemmas cover unconditional
product-law transfer or zero-mean conditional expectation, while this bridge
needs the prefix-dependent scalar upper bound. -/
private theorem delta_sq_condexp_le_linearized_gap_globalSamplePrefix_of_fixed_fiber
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (hfixed :
      ∀ xTilde x : {x : E // x ∈ setup.X},
        ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
            ∂Measure.map (setup.sampledIndexAt s t) setup.P ≤
          2 * setup.LQ *
            (setup.fOn xTilde - setup.fOn x -
              ⟪setup.gradF x.1, xTilde.1 - x.1⟫_ℝ)) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) ≤ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let Y : Ω → ι := setup.sampledIndexAt s t
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  have hY : Measurable Y := by
    change Measurable (setup.sampledIndexAt s t)
    rw [setup.sampledIndexAt_eq]
    exact setup.hξ_meas _
  haveI : IsProbabilityMeasure (Measure.map Y setup.P) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hpast_indep_current :
      Indep ((setup.filtration).seq N)
        (MeasurableSpace.comap Y (by infer_instance : MeasurableSpace ι)) setup.P := by
    simpa [VarianceReducedMirrorDescentSetup.filtration,
      VarianceReducedMirrorDescentSetup.sampledIndexAt_eq, Y, N] using
      (_root_.samplePrefixFiltration_indep_current
        setup.ξ setup.hξ_meas setup.hξ_indep N)
  have hNepoch : setup.epochOffset (s - 1) ≤ N := by
    simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
  obtain ⟨decodeInner, hdecodeInner⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  have hinner_decode :
      setup.paperInnerIterAt s t = fun ω => decodeInner (prefixVec ω) := by
    simpa [prefixVec, N] using hdecodeInner
  let snapFeasible : (Fin N → ι) → {x : E // x ∈ setup.X} := fun xs =>
    if h : decodeSnap xs ∈ setup.X then ⟨decodeSnap xs, h⟩
    else ⟨setup.w₀, setup.hw₀_mem⟩
  let innerFeasible : (Fin N → ι) → {x : E // x ∈ setup.X} := fun xs =>
    if h : decodeInner xs ∈ setup.X then ⟨decodeInner xs, h⟩
    else ⟨setup.w₀, setup.hw₀_mem⟩
  let φ : (Fin N → ι) → ι → ℝ := fun xs i =>
    SOptLib.dualNorm (setup.delta (snapFeasible xs).1 (innerFeasible xs).1 i) ^ 2
  let B : (Fin N → ι) → ℝ := fun xs =>
    2 * setup.LQ *
      (setup.fOn (snapFeasible xs) - setup.fOn (innerFeasible xs) -
        ⟪setup.gradF (innerFeasible xs).1,
          (snapFeasible xs).1 - (innerFeasible xs).1⟫_ℝ)
  have hφ_meas : Measurable (Function.uncurry φ) := Measurable.of_discrete
  have hB_meas : Measurable B := Measurable.of_discrete
  have hdecoded_meas : Measurable (fun ω => φ (prefixVec ω) (Y ω)) := by
    simpa [Function.uncurry] using hφ_meas.comp (hprefix_top.prodMk hY)
  have hdecoded_int :
      Integrable (fun ω => φ (prefixVec ω) (Y ω)) setup.P := by
    let vals : Finset ℝ :=
      Finset.univ.image (fun p : (Fin N → ι) × ι => ‖φ p.1 p.2‖)
    have hvals_nonempty : vals.Nonempty :=
      Finset.Nonempty.image
        (Finset.univ_nonempty : (Finset.univ : Finset ((Fin N → ι) × ι)).Nonempty) _
    let C : ℝ := vals.max' hvals_nonempty
    have hbound : ∀ ω, ‖φ (prefixVec ω) (Y ω)‖ ≤ C := by
      intro ω
      dsimp [C, vals]
      exact Finset.le_max' _ _ (by
        refine Finset.mem_image.mpr ?_
        exact ⟨(prefixVec ω, Y ω), by simp, rfl⟩)
    exact Integrable.of_bound hdecoded_meas.aestronglyMeasurable C
      (ae_of_all setup.P hbound)
  have hB_prefix_meas : Measurable (fun ω => B (prefixVec ω)) :=
    hB_meas.comp hprefix_top
  have hB_prefix_sm : StronglyMeasurable[(setup.filtration).seq N] (fun ω => B (prefixVec ω)) :=
    (hB_meas.comp hprefix_past).stronglyMeasurable
  have hB_prefix_int : Integrable (fun ω => B (prefixVec ω)) setup.P := by
    let vals : Finset ℝ := Finset.univ.image (fun xs : Fin N → ι => ‖B xs‖)
    have hvals_nonempty : vals.Nonempty :=
      Finset.Nonempty.image
        (Finset.univ_nonempty : (Finset.univ : Finset (Fin N → ι)).Nonempty) _
    let C : ℝ := vals.max' hvals_nonempty
    have hbound : ∀ ω, ‖B (prefixVec ω)‖ ≤ C := by
      intro ω
      dsimp [C, vals]
      exact Finset.le_max' _ _ (by
        refine Finset.mem_image.mpr ?_
        exact ⟨prefixVec ω, by simp, rfl⟩)
    exact Integrable.of_bound hB_prefix_meas.aestronglyMeasurable C
      (ae_of_all setup.P hbound)
  have hset_le :
      ∀ A : Set Ω, MeasurableSet[(setup.filtration).seq N] A →
        ∫ ω in A, φ (prefixVec ω) (Y ω) ∂setup.P ≤
          ∫ ω in A, B (prefixVec ω) ∂setup.P := by
    intro A hA
    let inA : Ω → Bool := fun ω => if ω ∈ A then true else false
    let XA : Ω → Bool × (Fin N → ι) := fun ω => (inA ω, prefixVec ω)
    let φA : (Bool × (Fin N → ι)) → ι → ℝ := fun z i =>
      if z.1 then φ z.2 i else 0
    let BA : Bool × (Fin N → ι) → ℝ := fun z =>
      if z.1 then B z.2 else 0
    have hA_top : MeasurableSet A := hm A hA
    have hinA_past : Measurable[(setup.filtration).seq N] inA := by
      apply measurable_to_bool
      convert hA using 1
      ext ω
      simp [inA]
    have hinA_top : Measurable inA := hinA_past.mono hm le_rfl
    have hXA_past : Measurable[(setup.filtration).seq N] XA :=
      hinA_past.prodMk hprefix_past
    have hXA_top : Measurable XA := hinA_top.prodMk hprefix_top
    have h_indep_XA : IndepFun XA Y setup.P :=
      vrmd_indepFun_of_past_measurable_current_iid_sample hXA_past hpast_indep_current
    have hφA_meas : Measurable (Function.uncurry φA) := Measurable.of_discrete
    have hBA_meas : Measurable BA := Measurable.of_discrete
    have hφA_eq :
        (fun ω => φA (XA ω) (Y ω)) =
          A.indicator (fun ω => φ (prefixVec ω) (Y ω)) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [XA, φA, inA, hω]
    have hBA_eq :
        (fun ω => BA (XA ω)) =
          A.indicator (fun ω => B (prefixVec ω)) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [XA, BA, inA, hω]
    have hφA_int : Integrable (fun ω => φA (XA ω) (Y ω)) setup.P := by
      simpa [hφA_eq] using hdecoded_int.indicator hA_top
    have hBA_int : Integrable (fun ω => BA (XA ω)) setup.P := by
      simpa [hBA_eq] using hB_prefix_int.indicator hA_top
    have hfixed_A :
        (fun z => ∫ i, φA z i ∂Measure.map Y setup.P) ≤ᵐ[Measure.map XA setup.P] BA := by
      refine Filter.Eventually.of_forall ?_
      intro z
      cases z with
      | mk b xs =>
          cases b
          · simp [φA, BA]
          · have hbase := hfixed (snapFeasible xs) (innerFeasible xs)
            simpa [φA, BA, Y, B, φ] using hbase
    have hfull_le :
        ∫ ω, φA (XA ω) (Y ω) ∂setup.P ≤ ∫ ω, BA (XA ω) ∂setup.P := by
      exact integral_comp_le_of_indep_fixed_integral_bound_fun
        (P := setup.P) (ν := Measure.map Y setup.P)
        (φ := φA) (B := BA) (X := XA) (Y := Y)
        hφA_meas hBA_meas hXA_top hY h_indep_XA rfl hφA_int hBA_int hfixed_A
    calc
      ∫ ω in A, φ (prefixVec ω) (Y ω) ∂setup.P
          = ∫ ω, φA (XA ω) (Y ω) ∂setup.P := by
            rw [← MeasureTheory.integral_indicator hA_top]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
              rw [hφA_eq])
      _ ≤ ∫ ω, BA (XA ω) ∂setup.P := hfull_le
      _ = ∫ ω in A, B (prefixVec ω) ∂setup.P := by
            rw [← MeasureTheory.integral_indicator hA_top]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
              rw [hBA_eq])
  have hdecoded_cond :
      setup.P[(fun ω => φ (prefixVec ω) (Y ω)) | (setup.filtration).seq N] ≤ᵐ[setup.P]
        fun ω => B (prefixVec ω) :=
    condExp_le_of_forall_setIntegral_le
      (P := setup.P) (m := (setup.filtration).seq N) hm
      hdecoded_int hB_prefix_int hB_prefix_sm hset_le
  have hprocess_eq :
      (fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) =ᵐ[setup.P]
        fun ω => φ (prefixVec ω) (Y ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hsval : decodeSnap (prefixVec ω) = setup.snapshotIter (s - 1) ω :=
      (congrFun hsnap_decode ω).symm
    have hival : decodeInner (prefixVec ω) = setup.paperInnerIterAt s t ω :=
      (congrFun hinner_decode ω).symm
    have hsmem_actual : setup.snapshotIter (s - 1) ω ∈ setup.X :=
      setup.snapshotIter_mem (s - 1) ω
    have himem_actual : setup.paperInnerIterAt s t ω ∈ setup.X :=
      setup.paperInnerIterAt_mem s t ω
    have hsfeat : (snapFeasible (prefixVec ω)).1 = setup.snapshotIter (s - 1) ω := by
      dsimp [snapFeasible]
      simp [hsval, hsmem_actual]
    have hifeat : (innerFeasible (prefixVec ω)).1 = setup.paperInnerIterAt s t ω := by
      dsimp [innerFeasible]
      simp [hival, himem_actual]
    simp [VarianceReducedMirrorDescentSetup.deltaProcessAt, φ, Y, hsfeat, hifeat]
  have hB_eq :
      (fun ω => B (prefixVec ω)) =
        fun ω =>
          2 * setup.LQ *
            (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.fOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              ⟪setup.gradF (setup.paperInnerIterAt s t ω),
                setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ) := by
    funext ω
    have hsval : decodeSnap (prefixVec ω) = setup.snapshotIter (s - 1) ω :=
      (congrFun hsnap_decode ω).symm
    have hival : decodeInner (prefixVec ω) = setup.paperInnerIterAt s t ω :=
      (congrFun hinner_decode ω).symm
    have hsmem_actual : setup.snapshotIter (s - 1) ω ∈ setup.X :=
      setup.snapshotIter_mem (s - 1) ω
    have himem_actual : setup.paperInnerIterAt s t ω ∈ setup.X :=
      setup.paperInnerIterAt_mem s t ω
    have hsfeat : (snapFeasible (prefixVec ω)).1 = setup.snapshotIter (s - 1) ω := by
      dsimp [snapFeasible]
      simp [hsval, hsmem_actual]
    have hifeat : (innerFeasible (prefixVec ω)).1 = setup.paperInnerIterAt s t ω := by
      dsimp [innerFeasible]
      simp [hival, himem_actual]
    have hs_sub :
        snapFeasible (prefixVec ω) =
          ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ :=
      Subtype.ext hsfeat
    have hi_sub :
        innerFeasible (prefixVec ω) =
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :=
      Subtype.ext hifeat
    simp [B, hsfeat, hifeat, hs_sub, hi_sub]
  calc
    setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        (setup.filtration).seq N]
        =ᵐ[setup.P]
      setup.P[(fun ω => φ (prefixVec ω) (Y ω)) | (setup.filtration).seq N] :=
        MeasureTheory.condExp_congr_ae hprocess_eq
    _ ≤ᵐ[setup.P] fun ω => B (prefixVec ω) := hdecoded_cond
    _ =ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ) :=
        Filter.EventuallyEq.of_eq hB_eq

/-- Prefix-filtration form of the Lemma 5.13 linearized second-moment bound.

This is the scaffold-aligned version of Lan Lemma 5.13 proof step 2: after
freezing the epoch snapshot and current iterate through the global sample
prefix, average only over the fresh component and apply the local
`lemma_5_12_linearized_f_gap_bound`. Search audit: checked the pre-searched
`randomIterate_variance_bound_of_fixed_variance`, `IdentDistrib.integral_comp_eq_of_measurable`,
and local `deltaFixedLawIntegralEqZero`; those provide the generic
fresh-sample variance-transfer pieces, while this helper packages the
VRMD-specific finite estimator algebra. -/
private theorem delta_sq_condexp_le_linearized_gap_globalSamplePrefix
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) ≤ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) := by
  exact delta_sq_condexp_le_linearized_gap_globalSamplePrefix_of_fixed_fiber
    setup s t hs (fun xTilde x =>
      fixed_fiber_delta_sq_le_linearized_gap setup s t xTilde x)

/-- Prefix-conditioning bridge for the two-composite-gap fixed-fiber Lemma 5.13
bound.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 3 under the global sample-prefix filtration: freeze
`(\tilde{x}, x_t)`, average over only the fresh component, and use the fixed
two-gap finite-law bound. Search audit: checked
`iIndepFun.indep_past_iSup_current`, `IdentDistrib.integral_comp_eq_of_measurable`,
`Measurable.of_measurableSpace_le`, and the existing linearized prefix bridge;
the generic candidates provide the independence/measurability ingredients, but
this helper must specialize the decoded VRMD prefix and the two-`Psi` scalar
bound. -/
private theorem delta_sq_condexp_le_two_Psi_gaps_globalSamplePrefix_of_fixed_fiber
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (hfixed :
      ∀ xTilde x : {x : E // x ∈ setup.X},
        ∫ i, SOptLib.dualNorm (setup.delta xTilde.1 x.1 i) ^ 2
            ∂Measure.map (setup.sampledIndexAt s t) setup.P ≤
          4 * setup.LQ *
            ((setup.PsiOn x - setup.PsiOn xStar) +
              (setup.PsiOn xTilde - setup.PsiOn xStar))) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar))) := by
  /-
  This is the same finite-prefix/product-law scaffold as
  `delta_sq_condexp_le_linearized_gap_globalSamplePrefix_of_fixed_fiber`, with
  only the scalar frozen-prefix bound changed from the linearized smooth gap to
  the source-faithful two-composite-gap expression.
  -/
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let Y : Ω → ι := setup.sampledIndexAt s t
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  have hY : Measurable Y := by
    change Measurable (setup.sampledIndexAt s t)
    rw [setup.sampledIndexAt_eq]
    exact setup.hξ_meas _
  haveI : IsProbabilityMeasure (Measure.map Y setup.P) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hpast_indep_current :
      Indep ((setup.filtration).seq N)
        (MeasurableSpace.comap Y (by infer_instance : MeasurableSpace ι)) setup.P := by
    simpa [VarianceReducedMirrorDescentSetup.filtration,
      VarianceReducedMirrorDescentSetup.sampledIndexAt_eq, Y, N] using
      (_root_.samplePrefixFiltration_indep_current
        setup.ξ setup.hξ_meas setup.hξ_indep N)
  have hNepoch : setup.epochOffset (s - 1) ≤ N := by
    simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
  obtain ⟨decodeInner, hdecodeInner⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  have hinner_decode :
      setup.paperInnerIterAt s t = fun ω => decodeInner (prefixVec ω) := by
    simpa [prefixVec, N] using hdecodeInner
  let snapFeasible : (Fin N → ι) → {x : E // x ∈ setup.X} := fun xs =>
    if h : decodeSnap xs ∈ setup.X then ⟨decodeSnap xs, h⟩
    else ⟨setup.w₀, setup.hw₀_mem⟩
  let innerFeasible : (Fin N → ι) → {x : E // x ∈ setup.X} := fun xs =>
    if h : decodeInner xs ∈ setup.X then ⟨decodeInner xs, h⟩
    else ⟨setup.w₀, setup.hw₀_mem⟩
  let φ : (Fin N → ι) → ι → ℝ := fun xs i =>
    SOptLib.dualNorm (setup.delta (snapFeasible xs).1 (innerFeasible xs).1 i) ^ 2
  let B : (Fin N → ι) → ℝ := fun xs =>
    4 * setup.LQ *
      ((setup.PsiOn (innerFeasible xs) - setup.PsiOn xStar) +
        (setup.PsiOn (snapFeasible xs) - setup.PsiOn xStar))
  have hφ_meas : Measurable (Function.uncurry φ) := Measurable.of_discrete
  have hB_meas : Measurable B := Measurable.of_discrete
  have hdecoded_meas : Measurable (fun ω => φ (prefixVec ω) (Y ω)) := by
    simpa [Function.uncurry] using hφ_meas.comp (hprefix_top.prodMk hY)
  have hdecoded_int :
      Integrable (fun ω => φ (prefixVec ω) (Y ω)) setup.P := by
    let vals : Finset ℝ :=
      Finset.univ.image (fun p : (Fin N → ι) × ι => ‖φ p.1 p.2‖)
    have hvals_nonempty : vals.Nonempty :=
      Finset.Nonempty.image
        (Finset.univ_nonempty : (Finset.univ : Finset ((Fin N → ι) × ι)).Nonempty) _
    let C : ℝ := vals.max' hvals_nonempty
    have hbound : ∀ ω, ‖φ (prefixVec ω) (Y ω)‖ ≤ C := by
      intro ω
      dsimp [C, vals]
      exact Finset.le_max' _ _ (by
        refine Finset.mem_image.mpr ?_
        exact ⟨(prefixVec ω, Y ω), by simp, rfl⟩)
    exact Integrable.of_bound hdecoded_meas.aestronglyMeasurable C
      (ae_of_all setup.P hbound)
  have hB_prefix_meas : Measurable (fun ω => B (prefixVec ω)) :=
    hB_meas.comp hprefix_top
  have hB_prefix_sm : StronglyMeasurable[(setup.filtration).seq N] (fun ω => B (prefixVec ω)) :=
    (hB_meas.comp hprefix_past).stronglyMeasurable
  have hB_prefix_int : Integrable (fun ω => B (prefixVec ω)) setup.P := by
    let vals : Finset ℝ := Finset.univ.image (fun xs : Fin N → ι => ‖B xs‖)
    have hvals_nonempty : vals.Nonempty :=
      Finset.Nonempty.image
        (Finset.univ_nonempty : (Finset.univ : Finset (Fin N → ι)).Nonempty) _
    let C : ℝ := vals.max' hvals_nonempty
    have hbound : ∀ ω, ‖B (prefixVec ω)‖ ≤ C := by
      intro ω
      dsimp [C, vals]
      exact Finset.le_max' _ _ (by
        refine Finset.mem_image.mpr ?_
        exact ⟨prefixVec ω, by simp, rfl⟩)
    exact Integrable.of_bound hB_prefix_meas.aestronglyMeasurable C
      (ae_of_all setup.P hbound)
  have hset_le :
      ∀ A : Set Ω, MeasurableSet[(setup.filtration).seq N] A →
        ∫ ω in A, φ (prefixVec ω) (Y ω) ∂setup.P ≤
          ∫ ω in A, B (prefixVec ω) ∂setup.P := by
    intro A hA
    let inA : Ω → Bool := fun ω => if ω ∈ A then true else false
    let XA : Ω → Bool × (Fin N → ι) := fun ω => (inA ω, prefixVec ω)
    let φA : (Bool × (Fin N → ι)) → ι → ℝ := fun z i =>
      if z.1 then φ z.2 i else 0
    let BA : Bool × (Fin N → ι) → ℝ := fun z =>
      if z.1 then B z.2 else 0
    have hA_top : MeasurableSet A := hm A hA
    have hinA_past : Measurable[(setup.filtration).seq N] inA := by
      apply measurable_to_bool
      convert hA using 1
      ext ω
      simp [inA]
    have hinA_top : Measurable inA := hinA_past.mono hm le_rfl
    have hXA_past : Measurable[(setup.filtration).seq N] XA :=
      hinA_past.prodMk hprefix_past
    have hXA_top : Measurable XA := hinA_top.prodMk hprefix_top
    have h_indep_XA : IndepFun XA Y setup.P :=
      vrmd_indepFun_of_past_measurable_current_iid_sample hXA_past hpast_indep_current
    have hφA_meas : Measurable (Function.uncurry φA) := Measurable.of_discrete
    have hBA_meas : Measurable BA := Measurable.of_discrete
    have hφA_eq :
        (fun ω => φA (XA ω) (Y ω)) =
          A.indicator (fun ω => φ (prefixVec ω) (Y ω)) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [XA, φA, inA, hω]
    have hBA_eq :
        (fun ω => BA (XA ω)) =
          A.indicator (fun ω => B (prefixVec ω)) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [XA, BA, inA, hω]
    have hφA_int : Integrable (fun ω => φA (XA ω) (Y ω)) setup.P := by
      simpa [hφA_eq] using hdecoded_int.indicator hA_top
    have hBA_int : Integrable (fun ω => BA (XA ω)) setup.P := by
      simpa [hBA_eq] using hB_prefix_int.indicator hA_top
    have hfixed_A :
        (fun z => ∫ i, φA z i ∂Measure.map Y setup.P) ≤ᵐ[Measure.map XA setup.P] BA := by
      refine Filter.Eventually.of_forall ?_
      intro z
      cases z with
      | mk b xs =>
          cases b
          · simp [φA, BA]
          · have hbase := hfixed (snapFeasible xs) (innerFeasible xs)
            simpa [φA, BA, Y, B, φ] using hbase
    have hfull_le :
        ∫ ω, φA (XA ω) (Y ω) ∂setup.P ≤ ∫ ω, BA (XA ω) ∂setup.P := by
      exact integral_comp_le_of_indep_fixed_integral_bound_fun
        (P := setup.P) (ν := Measure.map Y setup.P)
        (φ := φA) (B := BA) (X := XA) (Y := Y)
        hφA_meas hBA_meas hXA_top hY h_indep_XA rfl hφA_int hBA_int hfixed_A
    calc
      ∫ ω in A, φ (prefixVec ω) (Y ω) ∂setup.P
          = ∫ ω, φA (XA ω) (Y ω) ∂setup.P := by
            rw [← MeasureTheory.integral_indicator hA_top]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
              rw [hφA_eq])
      _ ≤ ∫ ω, BA (XA ω) ∂setup.P := hfull_le
      _ = ∫ ω in A, B (prefixVec ω) ∂setup.P := by
            rw [← MeasureTheory.integral_indicator hA_top]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
              rw [hBA_eq])
  have hdecoded_cond :
      setup.P[(fun ω => φ (prefixVec ω) (Y ω)) | (setup.filtration).seq N] ≤ᵐ[setup.P]
        fun ω => B (prefixVec ω) :=
    condExp_le_of_forall_setIntegral_le
      (P := setup.P) (m := (setup.filtration).seq N) hm
      hdecoded_int hB_prefix_int hB_prefix_sm hset_le
  have hprocess_eq :
      (fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) =ᵐ[setup.P]
        fun ω => φ (prefixVec ω) (Y ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hsval : decodeSnap (prefixVec ω) = setup.snapshotIter (s - 1) ω :=
      (congrFun hsnap_decode ω).symm
    have hival : decodeInner (prefixVec ω) = setup.paperInnerIterAt s t ω :=
      (congrFun hinner_decode ω).symm
    have hsmem_actual : setup.snapshotIter (s - 1) ω ∈ setup.X :=
      setup.snapshotIter_mem (s - 1) ω
    have himem_actual : setup.paperInnerIterAt s t ω ∈ setup.X :=
      setup.paperInnerIterAt_mem s t ω
    have hsfeat : (snapFeasible (prefixVec ω)).1 = setup.snapshotIter (s - 1) ω := by
      dsimp [snapFeasible]
      simp [hsval, hsmem_actual]
    have hifeat : (innerFeasible (prefixVec ω)).1 = setup.paperInnerIterAt s t ω := by
      dsimp [innerFeasible]
      simp [hival, himem_actual]
    simp [VarianceReducedMirrorDescentSetup.deltaProcessAt, φ, Y, hsfeat, hifeat]
  have hB_eq :
      (fun ω => B (prefixVec ω)) =
        fun ω =>
          4 * setup.LQ *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar)) := by
    funext ω
    have hsval : decodeSnap (prefixVec ω) = setup.snapshotIter (s - 1) ω :=
      (congrFun hsnap_decode ω).symm
    have hival : decodeInner (prefixVec ω) = setup.paperInnerIterAt s t ω :=
      (congrFun hinner_decode ω).symm
    have hsmem_actual : setup.snapshotIter (s - 1) ω ∈ setup.X :=
      setup.snapshotIter_mem (s - 1) ω
    have himem_actual : setup.paperInnerIterAt s t ω ∈ setup.X :=
      setup.paperInnerIterAt_mem s t ω
    have hsfeat : (snapFeasible (prefixVec ω)).1 = setup.snapshotIter (s - 1) ω := by
      dsimp [snapFeasible]
      simp [hsval, hsmem_actual]
    have hifeat : (innerFeasible (prefixVec ω)).1 = setup.paperInnerIterAt s t ω := by
      dsimp [innerFeasible]
      simp [hival, himem_actual]
    have hs_sub :
        snapFeasible (prefixVec ω) =
          ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ :=
      Subtype.ext hsfeat
    have hi_sub :
        innerFeasible (prefixVec ω) =
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :=
      Subtype.ext hifeat
    simp [B, hs_sub, hi_sub]
  calc
    setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        (setup.filtration).seq N]
        =ᵐ[setup.P]
      setup.P[(fun ω => φ (prefixVec ω) (Y ω)) | (setup.filtration).seq N] :=
        MeasureTheory.condExp_congr_ae hprocess_eq
    _ ≤ᵐ[setup.P] fun ω => B (prefixVec ω) := hdecoded_cond
    _ =ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar)) :=
        Filter.EventuallyEq.of_eq hB_eq

/-- Prefix-filtration form of Lan Lemma 5.13 step 3.

This packages the proved fixed-fiber two-gap component-gradient endpoint with
the prefix-conditioning scaffold. -/
private theorem delta_sq_condexp_le_two_Psi_gaps_globalSamplePrefix
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar))) := by
  exact
    delta_sq_condexp_le_two_Psi_gaps_globalSamplePrefix_of_fixed_fiber
      setup s t hs xStar
      (fun xTilde x => fixed_fiber_delta_sq_le_two_Psi_gaps setup s t xTilde x xStar h_opt)

/-- A function constant on the fibers of a finite-valued measurable factor is measurable.

This is a Lean measurability bridge for Lan Lemma 5.13's conditioning step:
after freezing the finite iterate-history factor, arbitrary scalar expressions
built from the frozen values are measurable without assuming global
measurability of every objective/gradient component. Search audit: checked
`measurable_of_finite`, `measurable_to_countable`, and the local finite-prefix
factorization lemmas; Mathlib covers arbitrary maps out of finite domains, while
this helper packages the fiber-constancy transfer needed here. -/
private theorem measurable_of_finite_range_factor
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] {m : MeasurableSpace Ω}
    {Y : Ω → α} {Z : Ω → β}
    (hY : @Measurable Ω α m _ Y)
    (hfin : (Set.range Y).Finite)
    (hconst : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    @Measurable Ω β m _ Z := by
  classical
  haveI : Fintype {y : α // y ∈ Set.range Y} := hfin.fintype
  let Yrange : Ω → {y : α // y ∈ Set.range Y} := fun ω => ⟨Y ω, ⟨ω, rfl⟩⟩
  let G : {y : α // y ∈ Set.range Y} → β := fun y =>
    Z (Classical.choose y.2)
  have hYrange : @Measurable Ω {y : α // y ∈ Set.range Y} m _ Yrange := by
    refine measurable_to_countable ?_
    intro ω
    have hset : MeasurableSet[m] (Y ⁻¹' {Y ω}) :=
      hY (measurableSet_singleton (Y ω))
    convert hset using 1
    ext ω'
    simp [Yrange]
  have hG : Measurable G := measurable_of_finite G
  have hZG : Z = G ∘ Yrange := by
    funext ω
    dsimp [Function.comp, G, Yrange]
    exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩)).symm
  rw [hZG]
  exact hG.comp hYrange

/-- Finite-valued measurable real random variables are integrable on finite measures.

This specializes the imported SOptLib bounded-real integrability lemma to
finite-range observables, the form needed for the Lemma 5.13 linearized gap. -/
private theorem integrable_real_of_finite_range
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → ℝ}
    (hZ : Measurable Z) (hfin : (Set.range Z).Finite) :
    Integrable Z μ := by
  classical
  let S : Finset ℝ := hfin.toFinset.image (fun z => ‖z‖)
  let C : ℝ := if hS : S.Nonempty then S.max' hS else 0
  have hC : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    have hmem : ‖Z ω‖ ∈ S := by
      simp [S, Set.Finite.mem_toFinset]
    have hS : S.Nonempty := ⟨‖Z ω‖, hmem⟩
    simpa [C, hS] using Finset.le_max' S (‖Z ω‖) hmem
  exact vrmd_integrable_of_measurable_bounded_real hZ hC

/-- Finite-factor real observables are integrable on finite measures.

This packages the finite-range route used by Lan Lemma 5.14 before applying
conditional-expectation monotonicity. Search audit: checked the pre-searched
helpers `measurable_of_finite_range_factor` and
`integrable_real_of_finite_range`; together they exactly match the required
finite-process observable form, while no SOptLib theorem provides this combined
paper-specific factor-constancy wrapper. -/
private theorem integrable_real_of_finite_range_factor
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → α} {Z : Ω → ℝ}
    (hY : Measurable Y) (hfin : (Set.range Y).Finite)
    (hconst : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    Integrable Z μ := by
  classical
  have hZ_meas : Measurable Z :=
    measurable_of_finite_range_factor hY hfin hconst
  have hZ_fin : (Set.range Z).Finite := by
    haveI : Fintype {y : α // y ∈ Set.range Y} := hfin.fintype
    let G : {y : α // y ∈ Set.range Y} → ℝ := fun y =>
      Z (Classical.choose y.2)
    have hsubset : Set.range Z ⊆ Set.range G := by
      rintro z ⟨ω, rfl⟩
      refine ⟨⟨Y ω, ⟨ω, rfl⟩⟩, ?_⟩
      dsimp [G]
      exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩))
    exact (Set.finite_range G).subset hsubset
  exact integrable_real_of_finite_range hZ_meas hZ_fin

/-- Integrability of the left observable in the raw conditioned descent step.

This aligns with Lan Lemma 5.14 proof step 3 before conditioning: the displayed
left side is a scalar function of the next finite iterate. Search audit: checked
`paperNextInnerIterAt_eq_internalCarrier`,
`innerCarrier_succ_factorizes_through_prefix`, and the finite-range helper
`integrable_real_of_finite_range_factor`; these provide the needed Lean
well-posedness, while the pre-searched descent lemmas concern the pathwise
inequality rather than this integrability side condition. -/
private theorem lemma_5_14_raw_left_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X}) :
    Integrable
      (fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar)
      setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) t.1
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let Z : Ω → ℝ := fun ω =>
    setup.η *
        (setup.PsiOn
            ⟨setup.paperNextInnerIterAt s t ω,
              setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
      setup.VOn
        ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
        xStar
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  obtain ⟨decodeNext, hdecodeNext_raw⟩ :
      ∃ decode : (Fin N → ι) → E,
        setup.paperNextInnerIterAt s t =
          fun ω => decode (prefixVec ω) := by
    simpa [N, prefixVec] using
      setup.paperNextInnerIter_factorizes_through_globalPrefix s t
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hnext : setup.paperNextInnerIterAt s t ω =
        setup.paperNextInnerIterAt s t ω' := by
      calc
        setup.paperNextInnerIterAt s t ω = decodeNext (prefixVec ω) :=
          congrFun hdecodeNext_raw ω
        _ = decodeNext (prefixVec ω') := by rw [hp]
        _ = setup.paperNextInnerIterAt s t ω' :=
          (congrFun hdecodeNext_raw ω').symm
    have hnext_sub :
        (⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperNextInnerIterAt s t ω', setup.paperNextInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hnext
    simpa [Z, hnext, hnext_sub]
  have hfin : (Set.range prefixVec).Finite := Set.toFinite _
  simpa [Z] using
    integrable_real_of_finite_range_factor (μ := setup.P) hprefix_top hfin hconst

/-- Integrability of the right observable in the raw conditioned descent step.

This aligns with Lan Lemma 5.14 proof step 3 before conditioning: the displayed
right side is a scalar function of the finite current iterate and fresh sampled
component. Search audit: checked `paperInnerIter_factorizes_through_globalPrefix`,
`sampledIndexAt_eq`, and `integrable_real_of_finite_range_factor`; no SOptLib
primitive packages this exact SVRG residual observable. -/
private theorem lemma_5_14_raw_right_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X}) :
    Integrable
      (fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2)
      setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) t.1
  let M := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let smallPrefixVec : Ω → (Fin M → ι) := fun ω j => setup.ξ j.1 ω
  let Z : Ω → ℝ := fun ω =>
    setup.VOn
      ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
      setup.η * ⟪setup.deltaProcessAt s t ω,
        xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
      setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  have hNepoch : setup.epochOffset (s - 1) ≤ N := by
    simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
  obtain ⟨decodeInner, hinner_decode⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hsmall : smallPrefixVec ω = smallPrefixVec ω' := by
      funext j
      have hcoord :=
        congrFun hp ⟨j.1, by
          have hj : j.1 < M := j.2
          simp [N, M, VarianceReducedMirrorDescentSetup.sampleIndex] at hj ⊢
          omega⟩
      simpa [prefixVec, smallPrefixVec] using hcoord
    have hsnap : setup.snapshotIter (s - 1) ω =
        setup.snapshotIter (s - 1) ω' := by
      calc
        setup.snapshotIter (s - 1) ω = decodeSnap (prefixVec ω) :=
          congrFun hsnap_decode ω
        _ = decodeSnap (prefixVec ω') := by rw [hp]
        _ = setup.snapshotIter (s - 1) ω' :=
          (congrFun hsnap_decode ω').symm
    have hinner : setup.paperInnerIterAt s t ω =
        setup.paperInnerIterAt s t ω' := by
      calc
        setup.paperInnerIterAt s t ω = decodeInner (smallPrefixVec ω) := by
          simpa [smallPrefixVec, M] using congrFun hinner_decode ω
        _ = decodeInner (smallPrefixVec ω') := by rw [hsmall]
        _ = setup.paperInnerIterAt s t ω' := by
          simpa [smallPrefixVec, M] using (congrFun hinner_decode ω').symm
    have hidx : setup.sampledIndexAt s t ω = setup.sampledIndexAt s t ω' := by
      have hcoord :=
        congrFun hp
          ⟨setup.sampleIndex (s - 1) (t.1 - 1), by
            simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
            omega⟩
      simpa [prefixVec, VarianceReducedMirrorDescentSetup.sampledIndexAt_eq]
        using hcoord
    have hinner_sub :
        (⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperInnerIterAt s t ω', setup.paperInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hinner
    have hdelta : setup.deltaProcessAt s t ω = setup.deltaProcessAt s t ω' := by
      simpa [VarianceReducedMirrorDescentSetup.deltaProcessAt, hsnap, hinner, hidx]
    simpa [Z, hinner, hinner_sub, hdelta]
  have hfin : (Set.range prefixVec).Finite := Set.toFinite _
  simpa [Z] using
    integrable_real_of_finite_range_factor (μ := setup.P) hprefix_top hfin hconst

/-- Adaptedness and integrability of the linearized-gap right-hand side used in
the Lemma 5.13 tower transport.

This aligns with Lan Lemma 5.13 proof step 2, where the snapshot and current
iterate are fixed under the epoch-history conditioning. Search audit: checked
the pre-searched conditional-expectation candidates
`MeasureTheory.condExp_of_stronglyMeasurable`, `MeasureTheory.condExp_mono`,
and the local finite-prefix factorization lemmas
`snapshotIter_factorizes_through_globalPrefix` /
`paperInnerIter_factorizes_through_globalPrefix`; the Mathlib API supplies the
conditional-expectation rewrite, while this helper isolates the paper-specific
finite-range measurability and boundedness of the linearized gap. -/
private theorem linearized_gap_epoch_past_measurable_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    StronglyMeasurable[setup.epochIteratePast s t]
      (fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) ∧
      Integrable
        (fun ω =>
          2 * setup.LQ *
            (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.fOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              ⟪setup.gradF (setup.paperInnerIterAt s t ω),
                setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ))
        setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let Z : Ω → ℝ := fun ω =>
    2 * setup.LQ *
      (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
        setup.fOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
        ⟪setup.gradF (setup.paperInnerIterAt s t ω),
          setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)
  let pair : Ω → E × E := fun ω =>
    (setup.snapshotIter (s - 1) ω, setup.paperInnerIterAt s t ω)
  have hsnap_meas :
      Measurable[setup.epochIteratePast s t] (setup.snapshotIter (s - 1)) := by
    refine Measurable.of_comap_le ?_
    rw [setup.epochIteratePast_eq]
    exact le_sup_left
  have hinner_meas :
      Measurable[setup.epochIteratePast s t] (setup.paperInnerIterAt s t) := by
    refine Measurable.of_comap_le ?_
    rw [setup.epochIteratePast_eq]
    refine le_trans ?_ le_sup_right
    let k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} := ⟨t.1, ⟨t.2.1, le_rfl⟩⟩
    have hle :
        MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E) ≤
          ⨆ k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1},
            MeasurableSpace.comap
              (setup.paperInnerIterAt s
                ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
              (by infer_instance : MeasurableSpace E) :=
      le_iSup
        (fun k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} =>
          MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E)) k
    simpa [k] using hle
  have hpair_meas : Measurable[setup.epochIteratePast s t] pair := by
    simpa [pair] using hsnap_meas.prod hinner_meas
  have hpair_fin : (Set.range pair).Finite := by
    let N := setup.sampleIndex (s - 1) (t.1 - 1)
    let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
    have hNepoch : setup.epochOffset (s - 1) ≤ N := by
      simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
    obtain ⟨decodeSnap, hsnap_decode⟩ :=
      setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
    obtain ⟨decodeInner, hinner_decode⟩ :=
      setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
    let pairDecode : (Fin N → ι) → E × E := fun xs => (decodeSnap xs, decodeInner xs)
    have hsubset : Set.range pair ⊆ Set.range pairDecode := by
      rintro y ⟨ω, rfl⟩
      refine ⟨prefixVec ω, ?_⟩
      have hsnapω :
          setup.snapshotIter (s - 1) ω = decodeSnap (prefixVec ω) := by
        simpa [prefixVec] using congrFun hsnap_decode ω
      have hinnerω :
          setup.paperInnerIterAt s t ω = decodeInner (prefixVec ω) := by
        simpa [prefixVec, N] using congrFun hinner_decode ω
      simp [pair, pairDecode, hsnapω, hinnerω]
    exact (Set.finite_range pairDecode).subset hsubset
  have hZ_const : ∀ ⦃ω ω' : Ω⦄, pair ω = pair ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hsnap :
        setup.snapshotIter (s - 1) ω = setup.snapshotIter (s - 1) ω' :=
      congrArg Prod.fst hp
    have hinner :
        setup.paperInnerIterAt s t ω = setup.paperInnerIterAt s t ω' :=
      congrArg Prod.snd hp
    have hsnap_sub :
        (⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.snapshotIter (s - 1) ω', setup.snapshotIter_mem (s - 1) ω'⟩ :=
      Subtype.ext hsnap
    have hinner_sub :
        (⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperInnerIterAt s t ω', setup.paperInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hinner
    simpa [Z, pair, hsnap, hinner, hsnap_sub, hinner_sub]
  have hZ_meas_epoch : Measurable[setup.epochIteratePast s t] Z :=
    measurable_of_finite_range_factor hpair_meas hpair_fin hZ_const
  have hZ_sm : StronglyMeasurable[setup.epochIteratePast s t] Z :=
    hZ_meas_epoch.stronglyMeasurable
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  have hEpoch_le_top :
      setup.epochIteratePast s t ≤ (by infer_instance : MeasurableSpace Ω) := by
    exact le_trans (setup.epochIteratePast_le_globalSamplePrefix s t)
      (by simpa [N] using (setup.filtration).le N)
  have hZ_meas : Measurable Z :=
    hZ_meas_epoch.mono hEpoch_le_top le_rfl
  have hZ_fin : (Set.range Z).Finite := by
    haveI : Fintype {p : E × E // p ∈ Set.range pair} := hpair_fin.fintype
    let G : {p : E × E // p ∈ Set.range pair} → ℝ := fun p =>
      Z (Classical.choose p.2)
    have hsubset : Set.range Z ⊆ Set.range G := by
      rintro z ⟨ω, rfl⟩
      refine ⟨⟨pair ω, ⟨ω, rfl⟩⟩, ?_⟩
      dsimp [G]
      exact hZ_const (Classical.choose_spec (show pair ω ∈ Set.range pair from ⟨ω, rfl⟩))
    exact (Set.finite_range G).subset hsubset
  have hZ_int : Integrable Z setup.P :=
    integrable_real_of_finite_range hZ_meas hZ_fin
  simpa [Z] using And.intro hZ_sm hZ_int

/-- Adaptedness and integrability of the two-composite-gap right-hand side used
in the Lemma 5.13 tower transport.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 3: after conditioning on the epoch history, both `x_t` and
`\tilde{x}` are fixed, so the two `Psi` gaps are finite-range functions of the
same iterate pair. Search audit: checked the pre-searched Bregman and generic
measurability candidates; no global measurability of `PsiOn` is needed because
the existing finite-range iterate factorization suffices. -/
private theorem two_Psi_gap_epoch_past_measurable_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X}) :
    StronglyMeasurable[setup.epochIteratePast s t]
      (fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar))) ∧
      Integrable
        (fun ω =>
          4 * setup.LQ *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar)))
        setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let Z : Ω → ℝ := fun ω =>
    4 * setup.LQ *
      ((setup.PsiOn
            ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
          setup.PsiOn xStar) +
        (setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar))
  let pair : Ω → E × E := fun ω =>
    (setup.snapshotIter (s - 1) ω, setup.paperInnerIterAt s t ω)
  have hsnap_meas :
      Measurable[setup.epochIteratePast s t] (setup.snapshotIter (s - 1)) := by
    refine Measurable.of_comap_le ?_
    rw [setup.epochIteratePast_eq]
    exact le_sup_left
  have hinner_meas :
      Measurable[setup.epochIteratePast s t] (setup.paperInnerIterAt s t) := by
    refine Measurable.of_comap_le ?_
    rw [setup.epochIteratePast_eq]
    refine le_trans ?_ le_sup_right
    let k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} := ⟨t.1, ⟨t.2.1, le_rfl⟩⟩
    have hle :
        MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E) ≤
          ⨆ k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1},
            MeasurableSpace.comap
              (setup.paperInnerIterAt s
                ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
              (by infer_instance : MeasurableSpace E) :=
      le_iSup
        (fun k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} =>
          MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E)) k
    simpa [k] using hle
  have hpair_meas : Measurable[setup.epochIteratePast s t] pair := by
    simpa [pair] using hsnap_meas.prod hinner_meas
  have hpair_fin : (Set.range pair).Finite := by
    let N := setup.sampleIndex (s - 1) (t.1 - 1)
    let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
    have hNepoch : setup.epochOffset (s - 1) ≤ N := by
      simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
    obtain ⟨decodeSnap, hsnap_decode⟩ :=
      setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
    obtain ⟨decodeInner, hinner_decode⟩ :=
      setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
    let pairDecode : (Fin N → ι) → E × E := fun xs => (decodeSnap xs, decodeInner xs)
    have hsubset : Set.range pair ⊆ Set.range pairDecode := by
      rintro y ⟨ω, rfl⟩
      refine ⟨prefixVec ω, ?_⟩
      have hsnapω :
          setup.snapshotIter (s - 1) ω = decodeSnap (prefixVec ω) := by
        simpa [prefixVec] using congrFun hsnap_decode ω
      have hinnerω :
          setup.paperInnerIterAt s t ω = decodeInner (prefixVec ω) := by
        simpa [prefixVec, N] using congrFun hinner_decode ω
      simp [pair, pairDecode, hsnapω, hinnerω]
    exact (Set.finite_range pairDecode).subset hsubset
  have hZ_const : ∀ ⦃ω ω' : Ω⦄, pair ω = pair ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hsnap :
        setup.snapshotIter (s - 1) ω = setup.snapshotIter (s - 1) ω' :=
      congrArg Prod.fst hp
    have hinner :
        setup.paperInnerIterAt s t ω = setup.paperInnerIterAt s t ω' :=
      congrArg Prod.snd hp
    have hsnap_sub :
        (⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.snapshotIter (s - 1) ω', setup.snapshotIter_mem (s - 1) ω'⟩ :=
      Subtype.ext hsnap
    have hinner_sub :
        (⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperInnerIterAt s t ω', setup.paperInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hinner
    simpa [Z, pair, hsnap, hinner, hsnap_sub, hinner_sub]
  have hZ_meas_epoch : Measurable[setup.epochIteratePast s t] Z :=
    measurable_of_finite_range_factor hpair_meas hpair_fin hZ_const
  have hZ_sm : StronglyMeasurable[setup.epochIteratePast s t] Z :=
    hZ_meas_epoch.stronglyMeasurable
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  have hEpoch_le_top :
      setup.epochIteratePast s t ≤ (by infer_instance : MeasurableSpace Ω) := by
    exact le_trans (setup.epochIteratePast_le_globalSamplePrefix s t)
      (by simpa [N] using (setup.filtration).le N)
  have hZ_meas : Measurable Z :=
    hZ_meas_epoch.mono hEpoch_le_top le_rfl
  have hZ_fin : (Set.range Z).Finite := by
    haveI : Fintype {p : E × E // p ∈ Set.range pair} := hpair_fin.fintype
    let G : {p : E × E // p ∈ Set.range pair} → ℝ := fun p =>
      Z (Classical.choose p.2)
    have hsubset : Set.range Z ⊆ Set.range G := by
      rintro z ⟨ω, rfl⟩
      refine ⟨⟨pair ω, ⟨ω, rfl⟩⟩, ?_⟩
      dsimp [G]
      exact hZ_const (Classical.choose_spec (show pair ω ∈ Set.range pair from ⟨ω, rfl⟩))
    exact (Set.finite_range G).subset hsubset
  have hZ_int : Integrable Z setup.P :=
    integrable_real_of_finite_range hZ_meas hZ_fin
  simpa [Z] using And.intro hZ_sm hZ_int

/-- Transport the prefix-filtration Lemma 5.13 variance bound to the
paper-facing epoch-history conditioning object.

This is the Lean tower-property step corresponding to the textbook convention
that the epoch snapshot `\tilde{x}` is fixed when conditioning on
`x_1, ..., x_t`. The local `epochIteratePast` scaffold includes that snapshot,
so the right-hand linearized gap is adapted to the smaller sigma-algebra and the
prefix bound can be towered down. -/
private theorem delta_sq_condexp_le_linearized_gap_epoch_of_globalSamplePrefix
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (hprefix :
      ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
          (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) ≤ᵐ[setup.P]
        fun ω =>
          2 * setup.LQ *
            (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.fOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              ⟪setup.gradF (setup.paperInnerIterAt s t ω),
                setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ))) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let Xsq : Ω → ℝ := fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  let Z : Ω → ℝ := fun ω =>
    2 * setup.LQ *
      (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
        setup.fOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
        ⟪setup.gradF (setup.paperInnerIterAt s t ω),
          setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)
  have hGleF : setup.epochIteratePast s t ≤ (setup.filtration).seq N := by
    simpa [N] using setup.epochIteratePast_le_globalSamplePrefix s t
  have hFleTop : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [N] using (setup.filtration).le N
  have hGleTop : setup.epochIteratePast s t ≤
      (by infer_instance : MeasurableSpace Ω) :=
    le_trans hGleF hFleTop
  have hZ :
      StronglyMeasurable[setup.epochIteratePast s t] Z ∧ Integrable Z setup.P := by
    simpa [Z] using linearized_gap_epoch_past_measurable_integrable setup s t hs
  have hprefixZ : (setup.P[Xsq | (setup.filtration).seq N]) ≤ᵐ[setup.P] Z := by
    simpa [Xsq, Z, N] using hprefix
  have hmono :
      (setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochIteratePast s t]) ≤ᵐ[setup.P]
        setup.P[Z | setup.epochIteratePast s t] := by
    exact MeasureTheory.condExp_mono
      (m := setup.epochIteratePast s t)
      (μ := setup.P)
      (f := setup.P[Xsq | (setup.filtration).seq N])
      (g := Z)
      (MeasureTheory.integrable_condExp) hZ.2 hprefixZ
  have htower :
      setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochIteratePast s t]
          =ᵐ[setup.P]
        setup.P[Xsq | setup.epochIteratePast s t] := by
    exact MeasureTheory.condExp_condExp_of_le
      (μ := setup.P)
      (m₁ := setup.epochIteratePast s t)
      (m₂ := (setup.filtration).seq N)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      (f := Xsq) hGleF hFleTop
  have hZcond_eq : setup.P[Z | setup.epochIteratePast s t] = Z := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (μ := setup.P)
      (m := setup.epochIteratePast s t)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      hGleTop hZ.1 hZ.2
  calc
    setup.P[Xsq | setup.epochIteratePast s t]
        =ᵐ[setup.P]
      setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochIteratePast s t] :=
        htower.symm
    _ ≤ᵐ[setup.P] setup.P[Z | setup.epochIteratePast s t] := hmono
    _ =ᵐ[setup.P] Z := Filter.EventuallyEq.of_eq hZcond_eq

/-- Transport the prefix-filtration two-composite-gap Lemma 5.13 variance
bound to the paper-facing epoch-history conditioning object.

This is the same tower-property step as the linearized-gap transport, with the
right-hand side replaced by the finite-range two-`Psi` expression from Lemma
5.13 proof step 3. -/
private theorem delta_sq_condexp_le_two_Psi_gaps_epoch_of_globalSamplePrefix
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (hprefix :
      ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
          (setup.filtration).seq (setup.sampleIndex (s - 1) (t.1 - 1))]) ≤ᵐ[setup.P]
        fun ω =>
          4 * setup.LQ *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar)))) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar))) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let Xsq : Ω → ℝ := fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  let Z : Ω → ℝ := fun ω =>
    4 * setup.LQ *
      ((setup.PsiOn
            ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
          setup.PsiOn xStar) +
        (setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar))
  have hGleF : setup.epochIteratePast s t ≤ (setup.filtration).seq N := by
    simpa [N] using setup.epochIteratePast_le_globalSamplePrefix s t
  have hFleTop : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [N] using (setup.filtration).le N
  have hGleTop : setup.epochIteratePast s t ≤
      (by infer_instance : MeasurableSpace Ω) :=
    le_trans hGleF hFleTop
  have hZ :
      StronglyMeasurable[setup.epochIteratePast s t] Z ∧ Integrable Z setup.P := by
    simpa [Z] using two_Psi_gap_epoch_past_measurable_integrable setup s t hs xStar
  have hprefixZ : (setup.P[Xsq | (setup.filtration).seq N]) ≤ᵐ[setup.P] Z := by
    simpa [Xsq, Z, N] using hprefix
  have hmono :
      (setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochIteratePast s t]) ≤ᵐ[setup.P]
        setup.P[Z | setup.epochIteratePast s t] := by
    exact MeasureTheory.condExp_mono
      (m := setup.epochIteratePast s t)
      (μ := setup.P)
      (f := setup.P[Xsq | (setup.filtration).seq N])
      (g := Z)
      (MeasureTheory.integrable_condExp) hZ.2 hprefixZ
  have htower :
      setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochIteratePast s t]
          =ᵐ[setup.P]
        setup.P[Xsq | setup.epochIteratePast s t] := by
    exact MeasureTheory.condExp_condExp_of_le
      (μ := setup.P)
      (m₁ := setup.epochIteratePast s t)
      (m₂ := (setup.filtration).seq N)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      (f := Xsq) hGleF hFleTop
  have hZcond_eq : setup.P[Z | setup.epochIteratePast s t] = Z := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (μ := setup.P)
      (m := setup.epochIteratePast s t)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      hGleTop hZ.1 hZ.2
  calc
    setup.P[Xsq | setup.epochIteratePast s t]
        =ᵐ[setup.P]
      setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochIteratePast s t] :=
        htower.symm
    _ ≤ᵐ[setup.P] setup.P[Z | setup.epochIteratePast s t] := hmono
    _ =ᵐ[setup.P] Z := Filter.EventuallyEq.of_eq hZcond_eq

/-- Linearized smooth-gap second-moment part of Lan Lemma 5.13.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 2: expand the centered estimator variance, drop the nonpositive
centering term, and apply the Lemma 5.12 linearized finite-sum bound with
`(x, x*) = (tilde{x}, x_t)`.  Search audit: checked
`randomIterate_variance_bound_of_fixed_variance`,
`weighted_variance_sum_expectation_bound`, and local
`lemma_5_12_linearized_f_gap_bound`; the SOptLib results handle generic
variance transfer/integration, while this helper packages the VRMD-specific
finite weighted square algebra and the source-facing linearized gap. -/
theorem delta_sq_condexp_le_linearized_gap_at_epoch
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) := by
  exact delta_sq_condexp_le_linearized_gap_epoch_of_globalSamplePrefix setup s t hs
    (delta_sq_condexp_le_linearized_gap_globalSamplePrefix setup s t hs)

/-- Two-composite-gap second-moment part of Lan Lemma 5.13.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` Lemma 5.13,
proof step 3: insert and subtract `∇ f_i(x*)`, split the squared component
difference, and apply Lemma 5.12 twice.  Search audit: checked
`randomIterate_variance_bound_of_fixed_variance`,
`weighted_variance_sum_expectation_bound`, and local `lemma_5_12_carrier`;
the imported variance-transfer lemmas do not contain the paper's two-center
component-gradient split, so this helper records the VRMD-specific endpoint
needed by Lemma 5.14. -/
theorem delta_sq_condexp_le_two_composite_gaps_at_epoch
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar)
          )) := by
  exact
    delta_sq_condexp_le_two_Psi_gaps_epoch_of_globalSamplePrefix setup s t hs xStar
      (delta_sq_condexp_le_two_Psi_gaps_globalSamplePrefix setup s t hs xStar h_opt)

/-- Mean-zero estimator identity under Lan Lemma 5.14's sample-past conditioner.

This is the same tower-property transport as `delta_condexp_eq_zero_at_epoch`,
but with the paper-local conditioner `epochSamplePastBefore` used in Lan Lemma
5.14 proof step 3.  Search audit: reused the verified prefix helper
`delta_condexp_eq_zero_globalSamplePrefix` after checking the listed SOptLib
conditional-expectation candidates; no new primitive is introduced. -/
private theorem delta_condexp_eq_zero_epochSamplePastBefore
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    ((setup.P[setup.deltaProcessAt s t |
        setup.epochSamplePastBefore s t]) =ᵐ[setup.P]
      fun _ => 0) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  have hprefix :
      ((setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N]) =ᵐ[setup.P]
        fun _ => 0) := by
    simpa [N] using delta_condexp_eq_zero_globalSamplePrefix setup s t hs
  have htower :
      setup.P[setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N] |
          setup.epochSamplePastBefore s t] =ᵐ[setup.P]
        setup.P[setup.deltaProcessAt s t | setup.epochSamplePastBefore s t] := by
    exact MeasureTheory.condExp_condExp_of_le
      (μ := setup.P)
      (m₁ := setup.epochSamplePastBefore s t)
      (m₂ := (setup.filtration).seq N)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      (f := setup.deltaProcessAt s t)
      (by simpa [N] using setup.epochSamplePastBefore_le_globalSamplePrefix s t)
      (by simpa [N] using (setup.filtration).le N)
  calc
    setup.P[setup.deltaProcessAt s t | setup.epochSamplePastBefore s t]
        =ᵐ[setup.P]
      setup.P[setup.P[setup.deltaProcessAt s t | (setup.filtration).seq N] |
          setup.epochSamplePastBefore s t] := htower.symm
    _ =ᵐ[setup.P]
      setup.P[(fun _ : Ω => (0 : E)) | setup.epochSamplePastBefore s t] := by
        exact MeasureTheory.condExp_congr_ae hprefix
    _ =ᵐ[setup.P] fun _ => 0 := by
        change setup.P[(0 : Ω → E) | setup.epochSamplePastBefore s t] =ᵐ[setup.P]
          (0 : Ω → E)
        exact Filter.EventuallyEq.of_eq
          (MeasureTheory.condExp_zero
            (μ := setup.P) (m := setup.epochSamplePastBefore s t) :
            setup.P[(0 : Ω → E) | setup.epochSamplePastBefore s t] = 0)

/-- Two-composite-gap second-moment bound under Lan Lemma 5.14's
sample-past conditioner.

This aligns with Lan Lemma 5.14 proof step 3 by transporting the proved prefix
Lemma 5.13 variance estimate through `epochSamplePastBefore_le_globalSamplePrefix`
and then identifying the two-gap right-hand side because it is already adapted
to `epochIteratePast ≤ epochSamplePastBefore`.  Search audit: reused
`delta_sq_condexp_le_two_Psi_gaps_globalSamplePrefix` and
`two_Psi_gap_epoch_past_measurable_integrable`; no SOptLib primitive matched this
paper-specific conditioner transport more directly. -/
private theorem delta_sq_condexp_le_two_Psi_gaps_epochSamplePastBefore
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar))) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let Xsq : Ω → ℝ := fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  let Z : Ω → ℝ := fun ω =>
    4 * setup.LQ *
      ((setup.PsiOn
            ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
          setup.PsiOn xStar) +
        (setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar))
  have hHleF : setup.epochSamplePastBefore s t ≤ (setup.filtration).seq N := by
    simpa [N] using setup.epochSamplePastBefore_le_globalSamplePrefix s t
  have hFleTop : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [N] using (setup.filtration).le N
  have hHleTop : setup.epochSamplePastBefore s t ≤
      (by infer_instance : MeasurableSpace Ω) := le_trans hHleF hFleTop
  have hEpoch_le_H : setup.epochIteratePast s t ≤ setup.epochSamplePastBefore s t := by
    rw [setup.epochSamplePastBefore_eq]
    exact le_sup_left
  have hZ_epoch :
      StronglyMeasurable[setup.epochIteratePast s t] Z ∧ Integrable Z setup.P := by
    simpa [Z] using two_Psi_gap_epoch_past_measurable_integrable setup s t hs xStar
  have hZ_H : StronglyMeasurable[setup.epochSamplePastBefore s t] Z :=
    hZ_epoch.1.mono hEpoch_le_H
  have hprefixZ : (setup.P[Xsq | (setup.filtration).seq N]) ≤ᵐ[setup.P] Z := by
    simpa [Xsq, Z, N] using
      delta_sq_condexp_le_two_Psi_gaps_globalSamplePrefix setup s t hs xStar h_opt
  have hmono :
      (setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochSamplePastBefore s t])
          ≤ᵐ[setup.P]
        setup.P[Z | setup.epochSamplePastBefore s t] := by
    exact MeasureTheory.condExp_mono
      (m := setup.epochSamplePastBefore s t)
      (μ := setup.P)
      (f := setup.P[Xsq | (setup.filtration).seq N])
      (g := Z)
      (MeasureTheory.integrable_condExp) hZ_epoch.2 hprefixZ
  have htower :
      setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochSamplePastBefore s t]
          =ᵐ[setup.P]
        setup.P[Xsq | setup.epochSamplePastBefore s t] := by
    exact MeasureTheory.condExp_condExp_of_le
      (μ := setup.P)
      (m₁ := setup.epochSamplePastBefore s t)
      (m₂ := (setup.filtration).seq N)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      (f := Xsq) hHleF hFleTop
  have hZcond_eq : setup.P[Z | setup.epochSamplePastBefore s t] = Z := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (μ := setup.P)
      (m := setup.epochSamplePastBefore s t)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      hHleTop hZ_H hZ_epoch.2
  calc
    setup.P[Xsq | setup.epochSamplePastBefore s t]
        =ᵐ[setup.P]
      setup.P[setup.P[Xsq | (setup.filtration).seq N] | setup.epochSamplePastBefore s t] :=
        htower.symm
    _ ≤ᵐ[setup.P] setup.P[Z | setup.epochSamplePastBefore s t] := hmono
    _ =ᵐ[setup.P] Z := Filter.EventuallyEq.of_eq hZcond_eq

/-- Conditioning the pathwise Lan Lemma 5.14 recursion before simplifying the RHS.

This aligns with Lan Lemma 5.14 proof step 3: apply conditional-expectation
monotonicity to the deterministic one-step recursion before using martingale
cancellation or Lemma 5.13. Search audit: checked SOptLib/Mathlib candidates
`MeasureTheory.condExp_mono`, `MeasureTheory.condExp_add`,
`MeasureTheory.condExp_smul`, and `MeasureTheory.condExp_of_stronglyMeasurable`;
`condExp_mono` is the exact abstract API, while this helper packages the
paper-specific finite-range integrability side conditions for the Lan observables. -/
private theorem lemma_5_14_conditional_descent_ce_raw
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (hpath : ∀ ω,
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar ≤
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) :
    ((setup.P[fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      setup.P[fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochSamplePastBefore s t]) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let LHS : Ω → ℝ := fun ω =>
    setup.η *
        (setup.PsiOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ -
          setup.PsiOn xStar) +
      setup.VOn
        ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ xStar
  let RHS : Ω → ℝ := fun ω =>
    setup.VOn
      ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
      setup.η * ⟪setup.deltaProcessAt s t ω,
        xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
      setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  have hL_int : Integrable LHS setup.P := by
    simpa [LHS] using lemma_5_14_raw_left_integrable setup s t hs xStar
  have hR_int : Integrable RHS setup.P := by
    simpa [RHS] using lemma_5_14_raw_right_integrable setup s t hs xStar
  have hpath_ae : LHS ≤ᵐ[setup.P] RHS :=
    Filter.Eventually.of_forall (fun ω => by
      simpa [LHS, RHS] using hpath ω)
  exact MeasureTheory.condExp_mono
    (m := setup.epochSamplePastBefore s t)
    (μ := setup.P)
    (f := LHS)
    (g := RHS)
    hL_int hR_int hpath_ae

/-- Adaptedness and integrability of the deterministic Bregman term in the
conditioned Lemma 5.14 right-hand side.

This aligns with Lan Lemma 5.14 proof step 3, where `x_t` is already fixed
under the sample-past conditioning. Search audit: checked the listed
`MeasureTheory.condExp_of_stronglyMeasurable` candidate and local finite-prefix
factorization helpers; no SOptLib primitive packages this paper-specific
`V(x_t,x*)` finite-range observable. -/
private theorem current_bregman_epochSamplePastBefore_measurable_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X}) :
    StronglyMeasurable[setup.epochSamplePastBefore s t]
      (fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar) ∧
      Integrable
        (fun ω =>
          setup.VOn
            ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar)
        setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let Vterm : Ω → ℝ := fun ω =>
    setup.VOn
      ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar
  have hEpoch_le_H : setup.epochIteratePast s t ≤ setup.epochSamplePastBefore s t := by
    rw [setup.epochSamplePastBefore_eq]
    exact le_sup_left
  have hinner_meas :
      Measurable[setup.epochIteratePast s t] (setup.paperInnerIterAt s t) := by
    refine Measurable.of_comap_le ?_
    rw [setup.epochIteratePast_eq]
    refine le_trans ?_ le_sup_right
    let k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} := ⟨t.1, ⟨t.2.1, le_rfl⟩⟩
    have hle :
        MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E) ≤
          ⨆ k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1},
            MeasurableSpace.comap
              (setup.paperInnerIterAt s
                ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
              (by infer_instance : MeasurableSpace E) :=
      le_iSup
        (fun k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} =>
          MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E)) k
    simpa [k] using hle
  have hinner_fin : (Set.range (setup.paperInnerIterAt s t)).Finite := by
    let N := setup.sampleIndex (s - 1) (t.1 - 1)
    let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
    obtain ⟨decodeInner, hinner_decode⟩ :=
      setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
    have hsubset : Set.range (setup.paperInnerIterAt s t) ⊆ Set.range decodeInner := by
      rintro y ⟨ω, rfl⟩
      refine ⟨prefixVec ω, ?_⟩
      simpa [prefixVec, N] using (congrFun hinner_decode ω).symm
    exact (Set.finite_range decodeInner).subset hsubset
  have hV_const :
      ∀ ⦃ω ω' : Ω⦄,
        setup.paperInnerIterAt s t ω = setup.paperInnerIterAt s t ω' →
          Vterm ω = Vterm ω' := by
    intro ω ω' hinner
    have hinner_sub :
        (⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperInnerIterAt s t ω', setup.paperInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hinner
    simpa [Vterm, hinner, hinner_sub]
  have hV_meas_epoch : Measurable[setup.epochIteratePast s t] Vterm :=
    measurable_of_finite_range_factor hinner_meas hinner_fin hV_const
  have hV_sm_H : StronglyMeasurable[setup.epochSamplePastBefore s t] Vterm :=
    hV_meas_epoch.stronglyMeasurable.mono hEpoch_le_H
  have hEpoch_le_top :
      setup.epochIteratePast s t ≤ (by infer_instance : MeasurableSpace Ω) :=
    le_trans (setup.epochIteratePast_le_globalSamplePrefix s t)
      (by
        let N := setup.sampleIndex (s - 1) (t.1 - 1)
        simpa [N] using (setup.filtration).le N)
  have hinner_top : Measurable (setup.paperInnerIterAt s t) :=
    hinner_meas.mono hEpoch_le_top le_rfl
  have hV_int : Integrable Vterm setup.P :=
    integrable_real_of_finite_range_factor (μ := setup.P)
      hinner_top hinner_fin hV_const
  simpa [Vterm] using And.intro hV_sm_H hV_int

/-- Integrability of the VRMD residual vector used by the Lemma 5.14 martingale
cancellation.

This aligns with Lan Lemma 5.14 proof step 3, `E[δ_t | past] = 0`. Search
audit: checked SOptLib `condExp_inner_sub_const_eq_zero_of_condExp_eq_zero` and
local `delta_condexp_eq_zero_epochSamplePastBefore`; this helper supplies only
the finite-range vector integrability side condition for that reusable theorem. -/
private theorem delta_process_integrable_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s) :
    Integrable (setup.deltaProcessAt s t) setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) t.1
  let M := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let smallPrefixVec : Ω → (Fin M → ι) := fun ω j => setup.ξ j.1 ω
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  have hNepoch : setup.epochOffset (s - 1) ≤ N := by
    simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
  obtain ⟨decodeInner, hinner_decode⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  let Z : Ω → E := setup.deltaProcessAt s t
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hsmall : smallPrefixVec ω = smallPrefixVec ω' := by
      funext j
      have hcoord :=
        congrFun hp ⟨j.1, by
          have hj : j.1 < M := j.2
          simp [N, M, VarianceReducedMirrorDescentSetup.sampleIndex] at hj ⊢
          omega⟩
      simpa [prefixVec, smallPrefixVec] using hcoord
    have hsnap : setup.snapshotIter (s - 1) ω =
        setup.snapshotIter (s - 1) ω' := by
      calc
        setup.snapshotIter (s - 1) ω = decodeSnap (prefixVec ω) :=
          congrFun hsnap_decode ω
        _ = decodeSnap (prefixVec ω') := by rw [hp]
        _ = setup.snapshotIter (s - 1) ω' :=
          (congrFun hsnap_decode ω').symm
    have hinner : setup.paperInnerIterAt s t ω =
        setup.paperInnerIterAt s t ω' := by
      calc
        setup.paperInnerIterAt s t ω = decodeInner (smallPrefixVec ω) := by
          simpa [smallPrefixVec, M] using congrFun hinner_decode ω
        _ = decodeInner (smallPrefixVec ω') := by rw [hsmall]
        _ = setup.paperInnerIterAt s t ω' := by
          simpa [smallPrefixVec, M] using (congrFun hinner_decode ω').symm
    have hidx : setup.sampledIndexAt s t ω = setup.sampledIndexAt s t ω' := by
      have hcoord :=
        congrFun hp
          ⟨setup.sampleIndex (s - 1) (t.1 - 1), by
            simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
            omega⟩
      simpa [prefixVec, VarianceReducedMirrorDescentSetup.sampledIndexAt_eq]
        using hcoord
    simpa [Z, VarianceReducedMirrorDescentSetup.deltaProcessAt, hsnap, hinner, hidx]
  have hZ_meas : Measurable Z :=
    measurable_of_finite_range_factor hprefix_top (Set.toFinite _) hconst
  have hZ_fin : (Set.range Z).Finite := by
    haveI : Fintype {p : Fin N → ι // p ∈ Set.range prefixVec} :=
      (Set.toFinite (Set.range prefixVec)).fintype
    let G : {p : Fin N → ι // p ∈ Set.range prefixVec} → E := fun p =>
      Z (Classical.choose p.2)
    have hsubset : Set.range Z ⊆ Set.range G := by
      rintro z ⟨ω, rfl⟩
      refine ⟨⟨prefixVec ω, ⟨ω, rfl⟩⟩, ?_⟩
      dsimp [G]
      exact hconst (Classical.choose_spec
        (show prefixVec ω ∈ Set.range prefixVec from ⟨ω, rfl⟩))
    exact (Set.finite_range G).subset hsubset
  let vals : Finset ℝ := hZ_fin.toFinset.image (fun z : E => ‖z‖)
  let C : ℝ := if hvals : vals.Nonempty then vals.max' hvals else 0
  have hbound : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    have hmem : ‖Z ω‖ ∈ vals := by
      simp [vals, Set.Finite.mem_toFinset]
    have hvals : vals.Nonempty := ⟨‖Z ω‖, hmem⟩
    simpa [C, hvals] using Finset.le_max' vals (‖Z ω‖) hmem
  exact Integrable.of_bound hZ_meas.aestronglyMeasurable C
    (ae_of_all setup.P hbound)

/-- Integrability of the scalar inner-product residual in Lan Lemma 5.14.

This is the finite-range side condition for the martingale-cancellation bridge.
Search audit: checked SOptLib `condExp_inner_sub_const_eq_zero_of_condExp_eq_zero`;
the reusable bridge needs this scalar integrability hypothesis, while the
paper-specific finite-prefix decoding is local to this file. -/
private theorem inner_noise_integrable_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X}) :
    Integrable
      (fun ω => ⟪setup.deltaProcessAt s t ω,
        xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ)
      setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) t.1
  let M := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let smallPrefixVec : Ω → (Fin M → ι) := fun ω j => setup.ξ j.1 ω
  let Z : Ω → ℝ := fun ω =>
    ⟪setup.deltaProcessAt s t ω, xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  have hNepoch : setup.epochOffset (s - 1) ≤ N := by
    simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix (s - 1) N hNepoch
  obtain ⟨decodeInner, hinner_decode⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hsmall : smallPrefixVec ω = smallPrefixVec ω' := by
      funext j
      have hcoord :=
        congrFun hp ⟨j.1, by
          have hj : j.1 < M := j.2
          simp [N, M, VarianceReducedMirrorDescentSetup.sampleIndex] at hj ⊢
          omega⟩
      simpa [prefixVec, smallPrefixVec] using hcoord
    have hsnap : setup.snapshotIter (s - 1) ω =
        setup.snapshotIter (s - 1) ω' := by
      calc
        setup.snapshotIter (s - 1) ω = decodeSnap (prefixVec ω) :=
          congrFun hsnap_decode ω
        _ = decodeSnap (prefixVec ω') := by rw [hp]
        _ = setup.snapshotIter (s - 1) ω' :=
          (congrFun hsnap_decode ω').symm
    have hinner : setup.paperInnerIterAt s t ω =
        setup.paperInnerIterAt s t ω' := by
      calc
        setup.paperInnerIterAt s t ω = decodeInner (smallPrefixVec ω) := by
          simpa [smallPrefixVec, M] using congrFun hinner_decode ω
        _ = decodeInner (smallPrefixVec ω') := by rw [hsmall]
        _ = setup.paperInnerIterAt s t ω' := by
          simpa [smallPrefixVec, M] using (congrFun hinner_decode ω').symm
    have hidx : setup.sampledIndexAt s t ω = setup.sampledIndexAt s t ω' := by
      have hcoord :=
        congrFun hp
          ⟨setup.sampleIndex (s - 1) (t.1 - 1), by
            simp [N, VarianceReducedMirrorDescentSetup.sampleIndex]
            omega⟩
      simpa [prefixVec, VarianceReducedMirrorDescentSetup.sampledIndexAt_eq]
        using hcoord
    have hdelta : setup.deltaProcessAt s t ω = setup.deltaProcessAt s t ω' := by
      simpa [VarianceReducedMirrorDescentSetup.deltaProcessAt, hsnap, hinner, hidx]
    simpa [Z, hinner, hdelta]
  have hfin : (Set.range prefixVec).Finite := Set.toFinite _
  simpa [Z] using
    integrable_real_of_finite_range_factor (μ := setup.P) hprefix_top hfin hconst

/-- Local conditional-expectation pullout bridge for adapted inner products.

This is the same Mathlib-level fact as SOptLib's
`condExp_inner_sub_const_eq_zero_of_condExp_eq_zero`; it is repeated here
because this target's full-file environment does not reliably expose that
imported name. It aligns with Lan Lemma 5.14 proof step 3. -/
private theorem condExp_inner_sub_const_eq_zero_of_condExp_eq_zero_local
    {δ x : Ω → E} {c : E} {P : Measure Ω} {m : MeasurableSpace Ω}
    (hx : @Measurable Ω E m _ x)
    (hδ_ce : P[δ | m] =ᵐ[P] 0)
    (hδ_int : Integrable δ P)
    (hinner_int : Integrable (fun ω => ⟪δ ω, x ω - c⟫_ℝ) P) :
    P[(fun ω => ⟪δ ω, x ω - c⟫_ℝ) | m] =ᵐ[P] 0 := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hx_asm : AEStronglyMeasurable[m] (fun ω => x ω - c) P := by
    exact (hx.sub measurable_const).aestronglyMeasurable
  have hpull := MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
    (μ := P) (m := m) (B := B) (f := δ) (g := fun ω => x ω - c)
    hx_asm hinner_int hδ_int
  refine hpull.trans ?_
  filter_upwards [hδ_ce] with ω hω
  simp [B, hω]

/-- Martingale cancellation for the scaled inner-product term in Lan Lemma 5.14.

This is exactly Lan Lemma 5.14 proof step 3, `E[δ_t | past] = 0`, after
pulling out the adapted multiplier `x* - x_t`. Search audit: selected SOptLib
`condExp_inner_sub_const_eq_zero_of_condExp_eq_zero` together with the local
`delta_condexp_eq_zero_epochSamplePastBefore`; no new stochastic primitive is
introduced. -/
private theorem inner_noise_condExp_zero_epochSamplePastBefore
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X}) :
    setup.P[(fun ω => setup.η *
        ⟪setup.deltaProcessAt s t ω,
          xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ) |
        setup.epochSamplePastBefore s t] =ᵐ[setup.P] 0 := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let Inner : Ω → ℝ := fun ω =>
    ⟪setup.deltaProcessAt s t ω, xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ
  let Xadapt : Ω → E := fun ω => xStar.1 - setup.paperInnerIterAt s t ω
  have hEpoch_le_H :
      setup.epochIteratePast s t ≤ setup.epochSamplePastBefore s t := by
    rw [VarianceReducedMirrorDescentSetup.epochSamplePastBefore_eq]
    exact le_sup_left
  have hinner_epoch :
      Measurable[setup.epochIteratePast s t] (setup.paperInnerIterAt s t) := by
    refine Measurable.of_comap_le ?_
    rw [setup.epochIteratePast_eq]
    refine le_trans ?_ le_sup_right
    let k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} := ⟨t.1, ⟨t.2.1, le_rfl⟩⟩
    have hle :
        MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E) ≤
          ⨆ k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1},
            MeasurableSpace.comap
              (setup.paperInnerIterAt s
                ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
              (by infer_instance : MeasurableSpace E) :=
      le_iSup
        (fun k : {k : ℕ // 1 ≤ k ∧ k ≤ t.1} =>
          MeasurableSpace.comap
            (setup.paperInnerIterAt s
              ⟨k.1, ⟨k.2.1, le_trans k.2.2 t.2.2⟩⟩)
            (by infer_instance : MeasurableSpace E)) k
    simpa [k] using hle
  have hX_meas : Measurable[setup.epochSamplePastBefore s t] Xadapt := by
    exact measurable_const.sub (hinner_epoch.mono hEpoch_le_H le_rfl)
  have hInner_ce0 :
      setup.P[Inner | setup.epochSamplePastBefore s t] =ᵐ[setup.P] 0 := by
    simpa [Inner, Xadapt, sub_zero] using
      condExp_inner_sub_const_eq_zero_of_condExp_eq_zero_local
        (P := setup.P) (m := setup.epochSamplePastBefore s t)
        (δ := setup.deltaProcessAt s t) (x := Xadapt) (c := 0)
        hX_meas
        (delta_condexp_eq_zero_epochSamplePastBefore setup s t hs)
        (delta_process_integrable_for_lemma_5_14 setup s t hs)
        (by
          simpa [Inner] using
            inner_noise_integrable_for_lemma_5_14 setup s t hs xStar)
  have hsmul :
      setup.P[(fun ω => setup.η * Inner ω) | setup.epochSamplePastBefore s t]
          =ᵐ[setup.P]
        fun ω => setup.η * setup.P[Inner | setup.epochSamplePastBefore s t] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := setup.P) (c := setup.η) (f := Inner)
        (m := setup.epochSamplePastBefore s t))
  filter_upwards [hsmul, hInner_ce0] with ω hη h0
  rw [hη, h0]
  simp

/-- Scaled form of the Lemma 5.13 two-gap second-moment bound under the
Lemma 5.14 conditioner.

This aligns with Lan Lemma 5.14 proof step 3 after applying Lemma 5.13.
Search audit: selected local
`delta_sq_condexp_le_two_Psi_gaps_epochSamplePastBefore` and Mathlib
`MeasureTheory.condExp_smul`; this helper only normalizes the scalar factor
`η^2`. -/
private theorem scaled_delta_sq_condExp_le_two_Psi_gaps_epochSamplePastBefore
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[fun ω =>
        setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ * setup.η ^ 2 *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar))) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let Sq : Ω → ℝ := fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  let Gap : Ω → ℝ := fun ω =>
    (setup.PsiOn
        ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
      setup.PsiOn xStar) +
    (setup.PsiOn
        ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
      setup.PsiOn xStar)
  have hbase :
      setup.P[Sq | setup.epochSamplePastBefore s t] ≤ᵐ[setup.P]
        fun ω => 4 * setup.LQ * Gap ω := by
    simpa [Sq, Gap] using
      delta_sq_condexp_le_two_Psi_gaps_epochSamplePastBefore
        setup s t hs xStar h_opt
  have hsmul :
      setup.P[(fun ω => setup.η ^ 2 * Sq ω) | setup.epochSamplePastBefore s t]
          =ᵐ[setup.P]
        fun ω =>
          setup.η ^ 2 * setup.P[Sq | setup.epochSamplePastBefore s t] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := setup.P) (c := setup.η ^ 2) (f := Sq)
        (m := setup.epochSamplePastBefore s t))
  have hη2_nonneg : 0 ≤ setup.η ^ 2 := sq_nonneg setup.η
  filter_upwards [hsmul, hbase] with ω hη hle
  calc
    setup.P[(fun ω => setup.η ^ 2 * Sq ω) | setup.epochSamplePastBefore s t] ω =
        setup.η ^ 2 * setup.P[Sq | setup.epochSamplePastBefore s t] ω := hη
    _ ≤ setup.η ^ 2 * (4 * setup.LQ * Gap ω) :=
        mul_le_mul_of_nonneg_left hle hη2_nonneg
    _ = 4 * setup.LQ * setup.η ^ 2 * Gap ω := by ring

/-- Simplification of the conditioned RHS in Lan Lemma 5.14.

This aligns with Lan Lemma 5.14 proof step 3 after conditioning: split the
conditional expectation of the affine RHS, identify the adapted Bregman term,
cancel the martingale residual, and insert Lemma 5.13's two-gap second-moment
bound. Search audit: checked SOptLib
`condExp_inner_sub_const_eq_zero_of_condExp_eq_zero`, local
`delta_condexp_eq_zero_epochSamplePastBefore`, local
`delta_sq_condexp_le_two_Psi_gaps_epochSamplePastBefore`, and Mathlib
`MeasureTheory.condExp_add`/`MeasureTheory.condExp_smul`; these are the intended
ingredients, while this helper isolates their syntactic assembly for the
paper-specific conditioner `epochSamplePastBefore`. -/
private theorem lemma_5_14_conditional_descent_ce_rhs_bound
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar))) := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let Vterm : Ω → ℝ := fun ω =>
    setup.VOn
      ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar
  let Inner : Ω → ℝ := fun ω =>
    ⟪setup.deltaProcessAt s t ω, xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ
  let Sq : Ω → ℝ := fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2
  let Gap : Ω → ℝ := fun ω =>
    (setup.PsiOn
        ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
      setup.PsiOn xStar) +
    (setup.PsiOn
        ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
      setup.PsiOn xStar)
  have hV :
      StronglyMeasurable[setup.epochSamplePastBefore s t] Vterm ∧
        Integrable Vterm setup.P := by
    simpa [Vterm] using
      current_bregman_epochSamplePastBefore_measurable_integrable setup s t hs xStar
  have hInner_int : Integrable Inner setup.P := by
    simpa [Inner] using inner_noise_integrable_for_lemma_5_14 setup s t hs xStar
  have hVInner_int : Integrable (fun ω => Vterm ω + setup.η * Inner ω) setup.P :=
    hV.2.add (hInner_int.const_mul setup.η)
  have hRaw_int :
      Integrable
        (fun ω => Vterm ω + setup.η * Inner ω + setup.η ^ 2 * Sq ω)
        setup.P := by
    simpa [Vterm, Inner, Sq] using lemma_5_14_raw_right_integrable setup s t hs xStar
  have hScaledSq_int : Integrable (fun ω => setup.η ^ 2 * Sq ω) setup.P := by
    have hdiff := hRaw_int.sub hVInner_int
    convert hdiff using 1
    funext ω
    dsimp
    ring
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  have hm_le_top :
      setup.epochSamplePastBefore s t ≤ (by infer_instance : MeasurableSpace Ω) := by
    exact le_trans (setup.epochSamplePastBefore_le_globalSamplePrefix s t)
      (by simpa [N] using (setup.filtration).le N)
  have hV_ce : setup.P[Vterm | setup.epochSamplePastBefore s t] = Vterm := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (μ := setup.P)
      (m := setup.epochSamplePastBefore s t)
      (m₀ := (by infer_instance : MeasurableSpace Ω))
      hm_le_top hV.1 hV.2
  have hInner_ce0 :
      setup.P[(fun ω => setup.η * Inner ω) | setup.epochSamplePastBefore s t]
          =ᵐ[setup.P] 0 := by
    simpa [Inner] using
      inner_noise_condExp_zero_epochSamplePastBefore setup s t hs xStar
  have hSq_bound :
      setup.P[(fun ω => setup.η ^ 2 * Sq ω) | setup.epochSamplePastBefore s t]
          ≤ᵐ[setup.P]
        fun ω => 4 * setup.LQ * setup.η ^ 2 * Gap ω := by
    simpa [Sq, Gap] using
      scaled_delta_sq_condExp_le_two_Psi_gaps_epochSamplePastBefore
        setup s t hs xStar h_opt
  have hAdd1 :
      setup.P[(fun ω => Vterm ω + setup.η * Inner ω) |
          setup.epochSamplePastBefore s t] =ᵐ[setup.P]
        setup.P[Vterm | setup.epochSamplePastBefore s t] +
          setup.P[(fun ω => setup.η * Inner ω) | setup.epochSamplePastBefore s t] := by
    exact MeasureTheory.condExp_add hV.2 (hInner_int.const_mul setup.η)
      (setup.epochSamplePastBefore s t)
  have hAdd2 :
      setup.P[(fun ω => (Vterm ω + setup.η * Inner ω) + setup.η ^ 2 * Sq ω) |
          setup.epochSamplePastBefore s t]
          =ᵐ[setup.P]
        setup.P[(fun ω => Vterm ω + setup.η * Inner ω) |
            setup.epochSamplePastBefore s t] +
          setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
            setup.epochSamplePastBefore s t] := by
    exact MeasureTheory.condExp_add hVInner_int hScaledSq_int
      (setup.epochSamplePastBefore s t)
  have hsplit :
      setup.P[(fun ω => Vterm ω + setup.η * Inner ω + setup.η ^ 2 * Sq ω) |
          setup.epochSamplePastBefore s t]
          =ᵐ[setup.P]
        fun ω =>
          (setup.P[Vterm | setup.epochSamplePastBefore s t] ω +
              setup.P[(fun ω => setup.η * Inner ω) |
                setup.epochSamplePastBefore s t] ω) +
            setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
              setup.epochSamplePastBefore s t] ω := by
    simpa [Pi.add_apply, add_assoc] using
      hAdd2.trans (hAdd1.add (Filter.EventuallyEq.rfl :
        setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
            setup.epochSamplePastBefore s t] =ᵐ[setup.P]
          setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
            setup.epochSamplePastBefore s t]))
  calc
    setup.P[(fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) |
        setup.epochSamplePastBefore s t]
        =ᵐ[setup.P]
      fun ω =>
        (setup.P[Vterm | setup.epochSamplePastBefore s t] ω +
            setup.P[(fun ω => setup.η * Inner ω) |
              setup.epochSamplePastBefore s t] ω) +
          setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
            setup.epochSamplePastBefore s t] ω := by
        simpa [Vterm, Inner, Sq] using hsplit
    _ ≤ᵐ[setup.P] fun ω => Vterm ω + 4 * setup.LQ * setup.η ^ 2 * Gap ω := by
        filter_upwards [Filter.EventuallyEq.of_eq hV_ce, hInner_ce0, hSq_bound]
          with ω hVω hInnerω hSqω
        calc
          (setup.P[Vterm | setup.epochSamplePastBefore s t] ω +
              setup.P[(fun ω => setup.η * Inner ω) |
                setup.epochSamplePastBefore s t] ω) +
            setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
              setup.epochSamplePastBefore s t] ω
              = (Vterm ω + 0) +
                  setup.P[(fun ω => setup.η ^ 2 * Sq ω) |
                    setup.epochSamplePastBefore s t] ω := by
                    rw [hVω, hInnerω]
                    simp
          _ ≤ Vterm ω + 4 * setup.LQ * setup.η ^ 2 * Gap ω := by
              linarith

/-- Lemma 5.13 variance-reduced estimator control, exposed only on the finite
Algorithm 5.6 inner-loop domain `t = 1, ..., T_s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/algorithm_spec/steps/1/math`.
Quote: `Pick i_t \in \{1, \ldots, m\} \text{ randomly according to } Q; \quad G_t = \frac{\nabla f_{i_t}(x_t) - \nabla f_{i_t}(\tilde{x})}{q_{i_t} m} + \tilde{g}`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/proof/0/description`.
Quote: `over t=1,...,T inside one epoch`. -/
theorem lemma_5_13
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[setup.deltaProcessAt s t |
        setup.epochIteratePast s t]) =ᵐ[setup.P]
      fun _ => 0) ∧
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) ∧
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar)
          )) := by
  exact ⟨delta_condexp_eq_zero_at_epoch setup s t hs,
    delta_sq_condexp_le_linearized_gap_at_epoch setup s t hs,
    delta_sq_condexp_le_two_composite_gaps_at_epoch setup s t hs xStar h_opt⟩

/-- Guarded compatibility route for proof experiments around Lemma 5.13.

Component convexity is now represented as the source-backed Setup field
`setup.hcomponent_convex`.  This suffixed helper is retained only as a
compatibility route for proof experiments that still pass the premise
explicitly. -/
theorem lemma_5_13_of_component_convex
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (hcomponent_convex : ∀ i, ConvexOn ℝ setup.X (setup.f i))
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ((setup.P[setup.deltaProcessAt s t |
        setup.epochIteratePast s t]) =ᵐ[setup.P]
      fun _ => 0) ∧
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        2 * setup.LQ *
          (setup.fOn ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
            setup.fOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
            ⟪setup.gradF (setup.paperInnerIterAt s t ω),
              setup.snapshotIter (s - 1) ω - setup.paperInnerIterAt s t ω⟫_ℝ)) ∧
    ((setup.P[fun ω => SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochIteratePast s t]) ≤ᵐ[setup.P]
      fun ω =>
        4 * setup.LQ *
          ((setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar) +
            (setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar)
          )) := by
  exact lemma_5_13 setup s t hs xStar h_opt

/-- First-order segment inequality for Lan Lemma 3.5 in the two-center carrier form.

This aligns with Lan Lemma 3.5 proof step 1: convexity of `p` controls the
nonsmooth part along the feasible segment, while
`carrierBregman_segment_difference_hasDerivWithinAt_zero` supplies the
one-sided derivatives of the two Bregman terms.  Considered the SOptLib
one-center prox helpers `prox_scaled_variational_inequality_of_argmin` and
`prox_majorant_hasDerivWithinAt_zero`; they give the derivative-sign pattern
but do not directly cover this two-center, unscaled Lemma 3.5 objective. -/
private theorem two_center_argmin_variational_inequality
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (p : E → ℝ)
    (xTilde yTilde uHat u : {x : E // x ∈ setup.X}) (μ₁ μ₂ : ℝ)
    (hp_convex : ConvexOn ℝ setup.X p)
    (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (huHat_opt :
      ∀ z : {x : E // x ∈ setup.X},
        p uHat.1 + μ₁ * setup.VOn xTilde uHat + μ₂ * setup.VOn yTilde uHat ≤
          p z.1 + μ₁ * setup.VOn xTilde z + μ₂ * setup.VOn yTilde z) :
    0 ≤ p u.1 - p uHat.1 +
      μ₁ * ⟪setup.vGradOn uHat - setup.vGradOn xTilde, u.1 - uHat.1⟫_ℝ +
      μ₂ * ⟪setup.vGradOn uHat - setup.vGradOn yTilde, u.1 - uHat.1⟫_ℝ := by
  classical
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let d : E := u.1 - uHat.1
  let segment : (t : ℝ) → t ∈ s → {x : E // x ∈ setup.X} :=
    fun t ht =>
      ⟨AffineMap.lineMap uHat.1 u.1 t,
        setup.hX_convex.lineMap_mem uHat.2 u.2 ht⟩
  let βx : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      setup.VOn xTilde (segment t ht) - setup.VOn xTilde uHat
    else 0
  let βy : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      setup.VOn yTilde (segment t ht) - setup.VOn yTilde uHat
    else 0
  let φ : ℝ → ℝ := fun t =>
    t * (p u.1 - p uHat.1) + μ₁ * βx t + μ₂ * βy t
  have hφ0 : φ 0 = 0 := by
    have h0 : (0 : ℝ) ∈ s := by norm_num [s]
    simp [φ, βx, βy, segment, s]
  have hφ_nonneg : ∀ t ∈ s, 0 ≤ φ t := by
    intro t ht
    let zt : {x : E // x ∈ setup.X} := segment t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : (1 - t) + t = 1 := by ring
    have hline :
        (1 - t) • uHat.1 + t • u.1 = zt.1 := by
      simp [zt, segment, AffineMap.lineMap_apply_module]
    have hp_raw := hp_convex.2 uHat.2 u.2 h1t ht0 hsum
    have hp_line :
        p zt.1 ≤ (1 - t) * p uHat.1 + t * p u.1 := by
      simpa [hline, smul_eq_mul] using hp_raw
    have hp_bound :
        p zt.1 - p uHat.1 ≤ t * (p u.1 - p uHat.1) := by
      linarith
    have hopt := huHat_opt zt
    have hopt_nonneg :
        0 ≤
          (p zt.1 - p uHat.1) +
            μ₁ * (setup.VOn xTilde zt - setup.VOn xTilde uHat) +
            μ₂ * (setup.VOn yTilde zt - setup.VOn yTilde uHat) := by
      linarith
    have hmain :
        0 ≤
          t * (p u.1 - p uHat.1) +
            μ₁ * (setup.VOn xTilde zt - setup.VOn xTilde uHat) +
            μ₂ * (setup.VOn yTilde zt - setup.VOn yTilde uHat) := by
      linarith
    have hβx_t : βx t = setup.VOn xTilde zt - setup.VOn xTilde uHat := by
      change
        (if ht' : t ∈ s then
          setup.VOn xTilde (segment t ht') - setup.VOn xTilde uHat
        else 0) =
          setup.VOn xTilde zt - setup.VOn xTilde uHat
      rw [dif_pos ht]
    have hβy_t : βy t = setup.VOn yTilde zt - setup.VOn yTilde uHat := by
      change
        (if ht' : t ∈ s then
          setup.VOn yTilde (segment t ht') - setup.VOn yTilde uHat
        else 0) =
          setup.VOn yTilde zt - setup.VOn yTilde uHat
      rw [dif_pos ht]
    change 0 ≤ t * (p u.1 - p uHat.1) + μ₁ * βx t + μ₂ * βy t
    rw [hβx_t, hβy_t]
    exact hmain
  have hv_diff : DifferentiableOn ℝ setup.v setup.X := by
    exact setup.hv_contDiff.differentiableOn (by norm_num)
  have hv_eq : ∀ y : {x : E // x ∈ setup.X}, setup.vOn y = setup.v y.1 := by
    intro y
    rfl
  have hgrad_apply :
      ∀ (y : {x : E // x ∈ setup.X}) (e : E),
        (fderivWithin ℝ setup.v setup.X y.1) e = ⟪setup.vGradOn y, e⟫_ℝ := by
    intro y e
    simp [VarianceReducedMirrorDescentSetup.vGradOn,
      VarianceReducedMirrorDescentSetup.vGradExtension, gradientWithin,
      InnerProductSpace.toDual_symm_apply]
  have hV :
      ∀ x z : {x : E // x ∈ setup.X},
        setup.VOn x z =
          setup.vOn z - setup.vOn x - ⟪setup.vGradOn x, z.1 - x.1⟫_ℝ := by
    intro x z
    rfl
  have hβx :
      HasDerivWithinAt βx
        ⟪setup.vGradOn uHat - setup.vGradOn xTilde, d⟫_ℝ s 0 := by
    have hraw :=
      carrierBregman_segment_difference_hasDerivWithinAt_zero
        setup.hX_convex setup.vOn setup.v setup.vGradOn setup.VOn
        hv_eq hv_diff hgrad_apply hV xTilde uHat u
    simpa [βx, segment, s, d] using hraw
  have hβy :
      HasDerivWithinAt βy
        ⟪setup.vGradOn uHat - setup.vGradOn yTilde, d⟫_ℝ s 0 := by
    have hraw :=
      carrierBregman_segment_difference_hasDerivWithinAt_zero
        setup.hX_convex setup.vOn setup.v setup.vGradOn setup.VOn
        hv_eq hv_diff hgrad_apply hV yTilde uHat u
    simpa [βy, segment, s, d] using hraw
  let C : ℝ := p u.1 - p uHat.1
  have hlin : HasDerivWithinAt (fun t : ℝ => t * C) C s 0 := by
    simpa [mul_comm] using
      (((hasDerivAt_id (0 : ℝ)).const_mul C).hasDerivWithinAt (s := s))
  have hderφ :
      HasDerivWithinAt φ
        (C + μ₁ * ⟪setup.vGradOn uHat - setup.vGradOn xTilde, d⟫_ℝ +
          μ₂ * ⟪setup.vGradOn uHat - setup.vGradOn yTilde, d⟫_ℝ) s 0 := by
    have hsum := (hlin.add (hβx.const_mul μ₁)).add (hβy.const_mul μ₂)
    simpa [φ, C, βx, βy, add_assoc, mul_assoc] using hsum
  have hnonneg :
      0 ≤
        C + μ₁ * ⟪setup.vGradOn uHat - setup.vGradOn xTilde, d⟫_ℝ +
          μ₂ * ⟪setup.vGradOn uHat - setup.vGradOn yTilde, d⟫_ℝ :=
    right_derivative_nonneg_of_min_on_Icc (φ := φ) hderφ (by
      intro t ht
      have hnon := hφ_nonneg t ht
      simpa [hφ0] using hnon)
  simpa [C, d, add_assoc] using hnonneg

/-- Three-point Bregman algebra for Lan Lemma 3.5.

This aligns with Lan Lemma 3.5 proof step 2 and specializes the existing
carrier identity `setup.VOn_three_point_identity` twice, once for each center. -/
private theorem two_center_three_point_rearrangement
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (p : E → ℝ)
    (xTilde yTilde uHat u : {x : E // x ∈ setup.X}) (μ₁ μ₂ : ℝ)
    (hvar :
      0 ≤ p u.1 - p uHat.1 +
        μ₁ * ⟪setup.vGradOn uHat - setup.vGradOn xTilde, u.1 - uHat.1⟫_ℝ +
        μ₂ * ⟪setup.vGradOn uHat - setup.vGradOn yTilde, u.1 - uHat.1⟫_ℝ) :
    p uHat.1 + μ₁ * setup.VOn xTilde uHat + μ₂ * setup.VOn yTilde uHat ≤
      p u.1 + μ₁ * setup.VOn xTilde u + μ₂ * setup.VOn yTilde u -
        (μ₁ + μ₂) * setup.VOn uHat u := by
  have h3x := setup.VOn_three_point_identity xTilde uHat u
  have h3y := setup.VOn_three_point_identity yTilde uHat u
  have hx_inner :
      ⟪setup.vGradOn uHat - setup.vGradOn xTilde, u.1 - uHat.1⟫_ℝ =
        setup.VOn xTilde u - setup.VOn xTilde uHat - setup.VOn uHat u := by
    linarith
  have hy_inner :
      ⟪setup.vGradOn uHat - setup.vGradOn yTilde, u.1 - uHat.1⟫_ℝ =
        setup.VOn yTilde u - setup.VOn yTilde uHat - setup.VOn uHat u := by
    linarith
  rw [hx_inner, hy_inner] at hvar
  linarith

/-- Lemma 3.5 specialized to this paper's feasible set and Bregman divergence.
The only local premise is the paper's own `Argmin` premise for `uHat`; `V` is
not a theorem-head parameter.

Considered `SOptLib.paperProxObjective`, `SOptLib.proxObjective`, and
`SOptLib.compositeProxPoint_isPaperProxPoint`; those model one-center prox
steps, while Lemma 3.5 is the two-center Bregman inequality from Lan §3. -/
theorem lemma_3_5
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (p : E → ℝ)
    (xTilde yTilde uHat u : {x : E // x ∈ setup.X}) (μ₁ μ₂ : ℝ)
    (hp_convex : ConvexOn ℝ setup.X p)
    (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (huHat_opt :
      ∀ z : {x : E // x ∈ setup.X},
        p uHat.1 + μ₁ * setup.VOn xTilde uHat + μ₂ * setup.VOn yTilde uHat ≤
          p z.1 + μ₁ * setup.VOn xTilde z + μ₂ * setup.VOn yTilde z) :
    p uHat.1 + μ₁ * setup.VOn xTilde uHat + μ₂ * setup.VOn yTilde uHat ≤
      p u.1 + μ₁ * setup.VOn xTilde u + μ₂ * setup.VOn yTilde u -
        (μ₁ + μ₂) * setup.VOn uHat u := by
  exact
    two_center_three_point_rearrangement setup p xTilde yTilde uHat u μ₁ μ₂
      (two_center_argmin_variational_inequality setup p xTilde yTilde uHat u μ₁ μ₂
        hp_convex hμ₁ hμ₂ huHat_opt)

/-- Carrier smoothness of the finite average in the exact Lan Lemma 5.14 form.

This aligns with Lan Lemma 5.14 proof step 1.  Considered the pre-searched
`Convex.carrier_smooth_quadratic_upper_bound` and the local
`carrierGradient_smooth_upper_bound_from_diff_lipschitz`; the latter is the
right differentiable-on bridge, but the paper-specific finite average still
requires transporting `setup.gradF` through the component-gradient average. -/
private theorem fOn_smooth_quadratic_upper_bound_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x y : {x : E // x ∈ setup.X}) :
    setup.fOn y ≤ setup.fOn x + ⟪setup.gradF x.1, y.1 - x.1⟫_ℝ +
      (setup.L / 2) * ‖y.1 - x.1‖ ^ 2 := by
  classical
  let d : E := y.1 - x.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap x.1 y.1 t
  let Fseg : ℝ → ℝ := fun t => setup.fAvg (line t)
  have hF0 : Fseg 0 = setup.fOn x := by
    simpa [Fseg, line] using (VarianceReducedMirrorDescentSetup.fOn_coe setup x).symm
  have hF1 : Fseg 1 = setup.fOn y := by
    simpa [Fseg, line] using (VarianceReducedMirrorDescentSetup.fOn_coe setup y).symm
  have hline_mem : ∀ t ∈ s, line t ∈ setup.X := by
    intro t ht
    exact setup.hX_convex.lineMap_mem x.2 y.2 ht
  have hmaps : Set.MapsTo line s setup.X := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg ⟪setup.gradF (line t), d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := x.1) (b := y.1)
          (s := s) (x := t))
    have hcomp : ∀ i : ι,
        HasDerivWithinAt (fun r : ℝ => setup.f i (line r))
          ⟪setup.componentGrad i (line t), d⟫_ℝ s t := by
      intro i
      have hF : HasFDerivWithinAt (setup.f i)
          (fderivWithin ℝ (setup.f i) setup.X (line t)) setup.X (line t) :=
        (setup.hcomponent_differentiable i (line t) (hline_mem t ht)).hasFDerivWithinAt
      have hchain : HasDerivWithinAt (fun r : ℝ => setup.f i (line r))
          ((fderivWithin ℝ (setup.f i) setup.X (line t)) d) s t := by
        simpa [line, Function.comp_def] using
          hF.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps (by simp [line])
      have hcarrier : setup.componentGrad i (line t) =
          SOptLib.carrierGradient setup.X (setup.componentOn i)
            ⟨line t, hline_mem t ht⟩ := by
        simpa [VarianceReducedMirrorDescentSetup.componentOn,
          vrmdComponentGradientCore, SOptLib.carrierGradient] using
          VarianceReducedMirrorDescentSetup.componentGrad_of_mem setup i (hline_mem t ht)
      have hd_dir : d ∈ (affineSpan ℝ setup.X).direction := by
        exact AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ setup.X y.2)
          (subset_affineSpan ℝ setup.X x.2)
      let du : (affineSpan ℝ setup.X).direction := ⟨d, hd_dir⟩
      have hpair_carrier :=
        VarianceReducedMirrorDescentSetup.component_carrierGradient_inner_eq_fderivWithin_on_affine_direction
          (X := setup.X) (F := setup.f i) (f := setup.componentOn i)
          setup.hX_convex (setup.hcomponent_differentiable i) (by intro z; rfl)
          ⟨line t, hline_mem t ht⟩ du
      have hpair : (fderivWithin ℝ (setup.f i) setup.X (line t)) d =
          ⟪setup.componentGrad i (line t), d⟫_ℝ := by
        simpa [du, hcarrier] using hpair_carrier.symm
      simpa [hpair] using hchain
    have hsum : HasDerivWithinAt
        (fun r : ℝ => Finset.sum Finset.univ (fun i : ι => setup.f i (line r)))
        (Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i (line t), d⟫_ℝ))
        s t := by
      exact HasDerivWithinAt.fun_sum (fun i _hi => hcomp i)
    have havg : HasDerivWithinAt
        (fun r : ℝ => (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => setup.f i (line r)))
        ((Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i (line t), d⟫_ℝ))
        s t := by
      simpa using hsum.const_mul (Fintype.card ι : ℝ)⁻¹
    have hgrad : ⟪setup.gradF (line t), d⟫_ℝ =
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => ⟪setup.componentGrad i (line t), d⟫_ℝ) := by
      simp [VarianceReducedMirrorDescentSetup.gradF_def, inner_smul_left, sum_inner]
    simpa [VarianceReducedMirrorDescentSetup.fAvg, Fseg, hgrad] using havg
  have hmodel := fAvg_carrier_smooth_convex_model setup
  have hsmooth : ∀ a b, a ∈ setup.X → b ∈ setup.X →
      SOptLib.dualNorm (setup.gradF a - setup.gradF b) ≤ setup.L * ‖a - b‖ :=
    hmodel.2.2
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪setup.gradF (line t), d⟫_ℝ ≤
        ⟪setup.gradF x.1, d⟫_ℝ + setup.L * t * ‖d‖ ^ 2 := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : line t - x.1 = t • d := by
      simp [line, d, AffineMap.lineMap_apply_module']
    have hnorm_line : ‖line t - x.1‖ = t * ‖d‖ := by
      rw [hseg_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hlip : ‖setup.gradF (line t) - setup.gradF x.1‖ ≤ setup.L * (t * ‖d‖) := by
      calc
        ‖setup.gradF (line t) - setup.gradF x.1‖
            = SOptLib.dualNorm (setup.gradF (line t) - setup.gradF x.1) := by
                rw [SOptLib.dualNorm_eq_norm]
        _ ≤ setup.L * ‖line t - x.1‖ := hsmooth (line t) x.1 (hline_mem t ht) x.2
        _ = setup.L * (t * ‖d‖) := by rw [hnorm_line]
    have hinner_diff :
        ⟪setup.gradF (line t), d⟫_ℝ - ⟪setup.gradF x.1, d⟫_ℝ =
          ⟪setup.gradF (line t) - setup.gradF x.1, d⟫_ℝ := by
      rw [inner_sub_left]
    have hcs :
        ⟪setup.gradF (line t) - setup.gradF x.1, d⟫_ℝ ≤
          ‖setup.gradF (line t) - setup.gradF x.1‖ * ‖d‖ := by
      calc
        ⟪setup.gradF (line t) - setup.gradF x.1, d⟫_ℝ
            ≤ |⟪setup.gradF (line t) - setup.gradF x.1, d⟫_ℝ| := le_abs_self _
        _ ≤ ‖setup.gradF (line t) - setup.gradF x.1‖ * ‖d‖ :=
          abs_real_inner_le_norm (setup.gradF (line t) - setup.gradF x.1) d
    have hmul :
        ‖setup.gradF (line t) - setup.gradF x.1‖ * ‖d‖ ≤
          setup.L * t * ‖d‖ ^ 2 := by
      have hmul' :
          ‖setup.gradF (line t) - setup.gradF x.1‖ * ‖d‖ ≤
            (setup.L * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
      calc
        ‖setup.gradF (line t) - setup.gradF x.1‖ * ‖d‖
            ≤ (setup.L * (t * ‖d‖)) * ‖d‖ := hmul'
        _ = setup.L * t * ‖d‖ ^ 2 := by ring
    have hdiff_le :
        ⟪setup.gradF (line t), d⟫_ℝ - ⟪setup.gradF x.1, d⟫_ℝ ≤
          setup.L * t * ‖d‖ ^ 2 := by
      calc
        ⟪setup.gradF (line t), d⟫_ℝ - ⟪setup.gradF x.1, d⟫_ℝ
            = ⟪setup.gradF (line t) - setup.gradF x.1, d⟫_ℝ := hinner_diff
        _ ≤ ‖setup.gradF (line t) - setup.gradF x.1‖ * ‖d‖ := hcs
        _ ≤ setup.L * t * ‖d‖ ^ 2 := hmul
    linarith
  let phi : ℝ → ℝ := fun t =>
    if _ht : t ∈ s then
      ⟪setup.gradF (line t), d⟫_ℝ
    else 0
  have hderiv_phi : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg (phi t) s t := by
    intro t ht
    simpa [phi, ht] using hderiv t ht
  have hbound_phi : ∀ (t : ℝ) (ht : t ∈ s),
      phi t ≤ ⟪setup.gradF x.1, d⟫_ℝ + (setup.L * ‖d‖ ^ 2) * t := by
    intro t ht
    have hb := hbound t ht
    simpa [phi, ht, mul_assoc, mul_comm, mul_left_comm] using hb
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪setup.gradF x.1, d⟫_ℝ +
        (setup.L * ‖d‖ ^ 2) / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg phi
      ⟪setup.gradF x.1, d⟫_ℝ (setup.L * ‖d‖ ^ 2) hderiv_phi hbound_phi
  rw [hF0, hF1] at hscalar
  change setup.fOn y ≤ setup.fOn x + ⟪setup.gradF x.1, y.1 - x.1⟫_ℝ +
    (setup.L / 2) * ‖y.1 - x.1‖ ^ 2
  rw [show d = y.1 - x.1 by rfl] at hscalar
  calc
    setup.fOn y ≤ setup.fOn x + ⟪setup.gradF x.1, y.1 - x.1⟫_ℝ +
        (setup.L * ‖y.1 - x.1‖ ^ 2) / 2 := hscalar
    _ = setup.fOn x + ⟪setup.gradF x.1, y.1 - x.1⟫_ℝ +
        (setup.L / 2) * ‖y.1 - x.1‖ ^ 2 := by ring

/-- Strong convexity on the full carrier gives the Bregman lower bound with
Mathlib's within-gradient.

This aligns with Lan Lemma 5.14 proof step 1.  Considered
`bregman_lower_bound_of_strongConvexOn_intrinsicInterior`,
`carrierBregmanDivergence_lower_bound_of_strongConvexOn_intrinsicInterior`, and
`bregmanDivergence_nonneg_of_strongConvexOn`; the first two are restricted to
intrinsic interiors and the last gives only nonnegativity, while this local
bridge is the same segment proof over the setup's closed convex carrier `X`. -/
private theorem bregman_lower_bound_of_strongConvexOn_withinGradient
    {X : Set E} {v : E → ℝ} {x z : E}
    (h_strong : StrongConvexOn X 1 v)
    (h_diff : DifferentiableOn ℝ v X)
    (hx : x ∈ X) (hz : z ∈ X) :
    (1 / 2 : ℝ) * ‖z - x‖ ^ 2 ≤
      v z - v x - ⟪gradientWithin v X x, z - x⟫_ℝ := by
  let φ : E → ℝ := fun y => v y - (1 / 2 : ℝ) * ‖y‖ ^ 2
  let line : ℝ → E := fun t => AffineMap.lineMap x z t
  have hφconv : ConvexOn ℝ X φ := by
    have hsc : StrongConvexOn X 1 v := h_strong
    rw [strongConvexOn_iff_convex] at hsc
    simpa [φ] using hsc
  have hline_mem : Set.Icc (0 : ℝ) 1 ⊆ line ⁻¹' X := by
    intro t ht
    exact hφconv.1.lineMap_mem hx hz ht
  have hφline_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => φ (line t)) := by
    simpa [line] using
      (hφconv.comp_affineMap (AffineMap.lineMap x z)).subset hline_mem (convex_Icc 0 1)
  have hmaps : Set.MapsTo line (Set.Icc (0 : ℝ) 1) X := by
    intro t ht
    exact hline_mem ht
  have hline_deriv :
      HasDerivWithinAt line (z - x) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [line] using
      (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := z)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hvdiff : DifferentiableWithinAt ℝ v X x := by
    exact h_diff x hx
  have hvline :
      HasDerivWithinAt (fun t => v (line t))
        ((fderivWithin ℝ v X x) (z - x)) (Set.Icc (0 : ℝ) 1) 0 :=
    hvdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line])
  have hnormline :
      HasDerivWithinAt (fun t => ‖line t‖ ^ 2)
        ((2 • innerSL ℝ x) (z - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    have hnormF :
        HasFDerivWithinAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) X x :=
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.hasFDerivWithinAt
    exact hnormF.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line])
  have hφderiv :
      HasDerivWithinAt (fun t => φ (line t))
        ((fderivWithin ℝ v X x) (z - x) -
          (1 / 2 : ℝ) * ((2 • innerSL ℝ x) (z - x)))
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ] using hvline.sub (HasDerivWithinAt.const_mul (1 / 2 : ℝ) hnormline)
  have hslope :
      (fderivWithin ℝ v X x) (z - x) -
          (1 / 2 : ℝ) * ((2 • innerSL ℝ x) (z - x)) ≤
        slope (fun t => φ (line t)) 0 1 := by
    exact convexOn_Icc_hasDerivWithinAt_left_le_slope hφline_conv hφderiv
  have hgrad_apply :
      (fderivWithin ℝ v X x) (z - x) =
        ⟪gradientWithin v X x, z - x⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hnorm_deriv :
      ((2 • innerSL ℝ x) (z - x)) =
        2 * ⟪x, z - x⟫_ℝ := by
    simp
  have hslope_expanded :
      ⟪gradientWithin v X x, z - x⟫_ℝ -
          ⟪x, z - x⟫_ℝ ≤
        v z - (1 / 2 : ℝ) * ‖z‖ ^ 2 -
          (v x - (1 / 2 : ℝ) * ‖x‖ ^ 2) := by
    have hs := hslope
    rw [hgrad_apply, hnorm_deriv] at hs
    simpa [slope_def_field, φ, line] using hs
  have hnorm_id :
      (1 / 2 : ℝ) * ‖z - x‖ ^ 2 =
        (1 / 2 : ℝ) * ‖z‖ ^ 2 - (1 / 2 : ℝ) * ‖x‖ ^ 2 -
          ⟪x, z - x⟫_ℝ := by
    rw [norm_sub_sq_real, inner_sub_right, real_inner_comm x z,
      real_inner_self_eq_norm_sq]
    ring_nf
  nlinarith [hslope_expanded, hnorm_id]

/-- Strong convexity of the distance generator gives the half-squared-distance
lower bound for the paper Bregman divergence.

This aligns with Lan Lemma 5.14 proof step 1.  Considered
`carrierBregmanDivergence_lower_bound_of_strongConvexOn_intrinsicInterior`,
`bregman_lower_bound_of_strongConvexOn_intrinsicInterior`, and
`carrierBregmanDivergence_lower_bound_all_carrier_from_dense`; those cover the
intrinsic-interior/dense-continuity route, while this file's setup has direct
`StrongConvexOn setup.X 1 setup.v` and the boundary-safe `gradientWithin`
realization on all feasible points. -/
private theorem VOn_half_sq_lower_of_strongConvex_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (x z : {x : E // x ∈ setup.X}) :
    (1 / 2 : ℝ) * ‖z.1 - x.1‖ ^ 2 ≤ setup.VOn x z := by
  have hdiff : DifferentiableOn ℝ setup.v setup.X :=
    setup.hv_contDiff.differentiableOn (by norm_num)
  have hraw :=
    bregman_lower_bound_of_strongConvexOn_withinGradient
      setup.hv_strongConvex hdiff x.2 z.2
  simpa [VarianceReducedMirrorDescentSetup.VOn, SOptLib.carrierBregmanDivergence,
    _root_.carrierBregmanDivergence,
    VarianceReducedMirrorDescentSetup.vOn,
    VarianceReducedMirrorDescentSetup.vGradOn,
    VarianceReducedMirrorDescentSetup.vGradExtension] using hraw

/-- Smoothness plus `L * η ≤ 1/2` absorbs the estimator residual into the
Bregman step and the squared dual norm.

This aligns with Lan Lemma 5.14 proof step 1.  The reusable atoms are
`fOn_smooth_quadratic_upper_bound_for_lemma_5_14`,
`VOn_half_sq_lower_of_strongConvex_for_lemma_5_14`,
`real_inner_le_norm`, and `SOptLib.dualNorm_eq_norm`; this helper packages only
the scalar Young-inequality algebra for the VR residual. -/
private theorem smooth_absorption_for_estimator_residual_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xt y : {x : E // x ∈ setup.X}) (G δ : E)
    (hηL : setup.L * setup.η ≤ 1 / 2)
    (hG : G = setup.gradF xt.1 + δ) :
    setup.η * setup.fOn y ≤
      setup.η * (setup.fOn xt + ⟪G, y.1 - xt.1⟫_ℝ) +
        setup.VOn xt y + setup.η ^ 2 * SOptLib.dualNorm δ ^ 2 := by
  classical
  let d : E := y.1 - xt.1
  have hη_nonneg : 0 ≤ setup.η := le_of_lt setup.eta_pos
  have hs0 := fOn_smooth_quadratic_upper_bound_for_lemma_5_14 setup xt y
  have hs : setup.fOn y ≤
      setup.fOn xt + ⟪setup.gradF xt.1, d⟫_ℝ +
        (setup.L / 2) * ‖d‖ ^ 2 := by
    simpa [d] using hs0
  have hsη : setup.η * setup.fOn y ≤
      setup.η * (setup.fOn xt + ⟪setup.gradF xt.1, d⟫_ℝ +
        (setup.L / 2) * ‖d‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hs hη_nonneg
  have hV : (1 / 2 : ℝ) * ‖d‖ ^ 2 ≤ setup.VOn xt y := by
    simpa [d] using VOn_half_sq_lower_of_strongConvex_for_lemma_5_14 setup xt y
  have hinner : -⟪δ, d⟫_ℝ ≤ ‖δ‖ * ‖d‖ := by
    have h := real_inner_le_norm (-δ) d
    simpa [inner_neg_left, norm_neg] using h
  have hcross0 : -setup.η * ⟪δ, d⟫_ℝ ≤ setup.η * (‖δ‖ * ‖d‖) := by
    have hmul := mul_le_mul_of_nonneg_left hinner hη_nonneg
    nlinarith
  have hyoung : setup.η * (‖δ‖ * ‖d‖) ≤
      setup.η ^ 2 * ‖δ‖ ^ 2 + (1 / 4 : ℝ) * ‖d‖ ^ 2 := by
    nlinarith [sq_nonneg (setup.η * ‖δ‖ - (1 / 2 : ℝ) * ‖d‖)]
  have hcross : -setup.η * ⟪δ, d⟫_ℝ ≤
      setup.η ^ 2 * ‖δ‖ ^ 2 + (1 / 4 : ℝ) * ‖d‖ ^ 2 :=
    le_trans hcross0 hyoung
  have hquad : setup.η * ((setup.L / 2) * ‖d‖ ^ 2) ≤
      (1 / 4 : ℝ) * ‖d‖ ^ 2 := by
    nlinarith [hηL, sq_nonneg ‖d‖]
  have habsorb :
      setup.η * ((setup.L / 2) * ‖d‖ ^ 2) - setup.η * ⟪δ, d⟫_ℝ ≤
        setup.VOn xt y + setup.η ^ 2 * ‖δ‖ ^ 2 := by
    nlinarith [hquad, hcross, hV]
  have hmain : setup.η * setup.fOn y ≤
      setup.η * (setup.fOn xt + ⟪G, d⟫_ℝ) +
        setup.VOn xt y + setup.η ^ 2 * ‖δ‖ ^ 2 := by
    rw [hG]
    simp only [inner_add_left]
    nlinarith [hsη, habsorb]
  simpa [d, SOptLib.dualNorm_eq_norm] using hmain

/-- Algorithm 5.6 prox update in the exact three-point form consumed by
Lan Lemma 5.14.

This aligns with Lan Lemma 5.14 proof step 2.  Considered the pre-searched
`paperNextInnerIterAt_eq_proxStep`, `proxPoint_isPaperProxPoint`,
`proxObjective_eq_eta_mul_paperProxObjective`, and local `lemma_3_5`; together
they provide the prox-minimizer route, but the conversion to the displayed
paper inner-product objective is specific to this theorem. -/
private theorem prox_three_point_for_paper_step_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (x : {x : E // x ∈ setup.X}) (ω : Ω) :
    let xt : {x : E // x ∈ setup.X} :=
      ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩
    let y : {x : E // x ∈ setup.X} :=
      ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
    let G : E := setup.estimatorProcessAt s t ω
    setup.η * (⟪G, y.1⟫_ℝ + setup.hOn y) + setup.VOn xt y + setup.VOn y x ≤
      setup.η * (⟪G, x.1⟫_ℝ + setup.hOn x) + setup.VOn xt x := by
  classical
  dsimp
  let xt : {x : E // x ∈ setup.X} :=
    ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩
  let y : {x : E // x ∈ setup.X} :=
    ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
  let G : E := setup.estimatorProcessAt s t ω
  let p : E → ℝ := fun z => setup.η * (⟪G, z⟫_ℝ + setup.h z)
  have hp_convex : ConvexOn ℝ setup.X p := by
    refine ⟨setup.hX_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh : setup.h (a • x + b • y) ≤ a * setup.h x + b * setup.h y := by
      simpa [smul_eq_mul] using setup.hh_convex.2 hx hy ha hb hab
    have hinner :
        ⟪G, a • x + b • y⟫_ℝ =
          a * ⟪G, x⟫_ℝ + b * ⟪G, y⟫_ℝ := by
      simp [inner_add_right, inner_smul_right]
    dsimp [p]
    rw [hinner]
    calc
      setup.η *
          (a * ⟪G, x⟫_ℝ + b * ⟪G, y⟫_ℝ +
            setup.h (a • x + b • y)) ≤
        setup.η *
          (a * ⟪G, x⟫_ℝ + b * ⟪G, y⟫_ℝ +
            (a * setup.h x + b * setup.h y)) := by
          have hsum :
              a * ⟪G, x⟫_ℝ + b * ⟪G, y⟫_ℝ +
                  setup.h (a • x + b • y) ≤
                a * ⟪G, x⟫_ℝ + b * ⟪G, y⟫_ℝ +
                  (a * setup.h x + b * setup.h y) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hh (a * ⟪G, x⟫_ℝ + b * ⟪G, y⟫_ℝ)
          exact mul_le_mul_of_nonneg_left hsum (le_of_lt setup.eta_pos)
      _ =
        a * (setup.η * (⟪G, x⟫_ℝ + setup.h x)) +
          b * (setup.η * (⟪G, y⟫_ℝ + setup.h y)) := by
          ring
  have hy_prox : y = setup.proxPoint xt G := by
    apply Subtype.ext
    have hnext := congrFun (setup.paperNextInnerIterAt_eq_proxStep s t hs) ω
    calc
      y.1 = setup.paperNextInnerIterAt s t ω := rfl
      _ =
          setup.proxStep (setup.paperInnerIterAt s t ω)
            (setup.estimatorProcessAt s t ω) := hnext
      _ = (setup.proxPoint xt G).1 := by
          simpa [xt, G] using setup.proxStep_eq_proxPoint xt G
  have hηne : setup.η ≠ 0 := ne_of_gt setup.eta_pos
  have hscaled_paper :
      ∀ z : {x : E // x ∈ setup.X},
        setup.η *
            SOptLib.paperProxObjective
              (eval := fun u : {x : E // x ∈ setup.X} => (u.1 : E))
              (V := setup.VOn) (h := setup.hOn) xt G setup.η z =
          p z.1 + setup.VOn xt z := by
    intro z
    simp only [p, SOptLib.paperProxObjective, VarianceReducedMirrorDescentSetup.hOn]
    field_simp [hηne]
    ring
  have hopt_simple :
      ∀ z : {x : E // x ∈ setup.X},
        p y.1 + setup.VOn xt y ≤ p z.1 + setup.VOn xt z := by
    intro z
    have hmin := setup.proxPoint_minimizes_literal xt G z
    rw [setup.proxObjective_eq_eta_mul_paperProxObjective xt
        (setup.proxPoint xt G) G,
      setup.proxObjective_eq_eta_mul_paperProxObjective xt z G] at hmin
    rw [hscaled_paper (setup.proxPoint xt G), hscaled_paper z] at hmin
    simpa [hy_prox] using hmin
  have h3raw :=
    lemma_3_5 setup p xt xt y x 1 0 hp_convex (by norm_num) (by norm_num)
      (by
        intro z
        simpa using hopt_simple z)
  have h3 :
      p y.1 + setup.VOn xt y ≤ p x.1 + setup.VOn xt x - setup.VOn y x := by
    simpa using h3raw
  simp only [p, VarianceReducedMirrorDescentSetup.hOn] at h3 ⊢
  linarith

/-- Final scalar algebra combining the smooth absorption, prox three-point
bound, and convexity support term in Lan Lemma 5.14.

This aligns with Lan Lemma 5.14 proof step 2 after all mathematical inputs have
already been specialized.  Search audit: checked `mirrorDescent_oneStep_pathwise_of_all_carrier_lower_bound`;
that reusable theorem packages a related one-step algebra but assumes a bounded
subgradient term and a different smooth/prox split, so this helper records the
VRMD-specific residual-sign normalization. -/
private theorem smooth_prox_convex_algebra_for_lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xt y x : {x : E // x ∈ setup.X}) (δ : E)
    (hsmooth :
      setup.η * setup.fOn y ≤
        setup.η *
            (setup.fOn xt +
              ⟪setup.gradF xt.1 + δ, y.1 - xt.1⟫_ℝ) +
          setup.VOn xt y + setup.η ^ 2 * SOptLib.dualNorm δ ^ 2)
    (hprox :
      setup.η * (⟪setup.gradF xt.1 + δ, y.1⟫_ℝ + setup.hOn y) +
          setup.VOn xt y + setup.VOn y x ≤
        setup.η * (⟪setup.gradF xt.1 + δ, x.1⟫_ℝ + setup.hOn x) +
          setup.VOn xt x)
    (hconv_scaled :
      setup.η *
          (setup.fOn xt - setup.fOn x +
            ⟪setup.gradF xt.1, x.1 - xt.1⟫_ℝ) ≤ 0) :
    setup.η * (setup.PsiOn y - setup.PsiOn x) + setup.VOn y x ≤
      setup.VOn xt x + setup.η * ⟪δ, x.1 - xt.1⟫_ℝ +
        setup.η ^ 2 * SOptLib.dualNorm δ ^ 2 := by
  unfold VarianceReducedMirrorDescentSetup.PsiOn
  have hinner_step :
      ⟪setup.gradF xt.1 + δ, y.1 - xt.1⟫_ℝ =
        ⟪setup.gradF xt.1 + δ, y.1⟫_ℝ -
          ⟪setup.gradF xt.1 + δ, xt.1⟫_ℝ := by
    rw [inner_sub_right]
  have hinner_delta :
      ⟪δ, x.1 - xt.1⟫_ℝ = ⟪δ, x.1⟫_ℝ - ⟪δ, xt.1⟫_ℝ := by
    rw [inner_sub_right]
  have hinner_grad :
      ⟪setup.gradF xt.1, x.1 - xt.1⟫_ℝ =
        ⟪setup.gradF xt.1, x.1⟫_ℝ - ⟪setup.gradF xt.1, xt.1⟫_ℝ := by
    rw [inner_sub_right]
  have hinner_sum_x :
      ⟪setup.gradF xt.1 + δ, x.1⟫_ℝ =
        ⟪setup.gradF xt.1, x.1⟫_ℝ + ⟪δ, x.1⟫_ℝ := by
    rw [inner_add_left]
  have hinner_sum_xt :
      ⟪setup.gradF xt.1 + δ, xt.1⟫_ℝ =
        ⟪setup.gradF xt.1, xt.1⟫_ℝ + ⟪δ, xt.1⟫_ℝ := by
    rw [inner_add_left]
  rw [hinner_step] at hsmooth
  rw [hinner_sum_xt] at hsmooth
  rw [hinner_sum_x] at hprox
  rw [hinner_grad] at hconv_scaled
  rw [hinner_delta]
  nlinarith [hsmooth, hprox, hconv_scaled]

/-- Pathwise deterministic half of Lan Lemma 5.14.

This aligns with Lan Lemma 5.14 proof steps 1-2: rewrite the Algorithm 5.6
update through `setup.paperNextInnerIterAt_eq_proxStep`, use the prox
minimality `setup.proxStep_is_argmin`/`lemma_3_5` three-point route, and absorb
the smooth quadratic term with `L * η ≤ 1 / 2`.  Search audit: checked
`mirrorDescent_oneStep_pathwise_of_all_carrier_lower_bound`,
`mirror_descent_three_point_of_variational_carrier`,
`Convex.carrier_smooth_quadratic_upper_bound`, and the local `lemma_3_5`; these
are the right reusable atoms, but the paper-specific composite smooth-plus-prox
algebra still needs to be assembled in this file. -/
private theorem lemma_5_14_pathwise_descent
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (x : {x : E // x ∈ setup.X})
    (hηL : setup.L * setup.η ≤ 1 / 2) :
    ∀ ω,
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn x) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ x ≤
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ x +
          setup.η *
            ⟪setup.deltaProcessAt s t ω,
              x.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 := by
  intro ω
  let xt : {x : E // x ∈ setup.X} :=
    ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩
  let y : {x : E // x ∈ setup.X} :=
    ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
  let G : E := setup.estimatorProcessAt s t ω
  let δ : E := setup.deltaProcessAt s t ω
  have hG : G = setup.gradF xt.1 + δ := by
    dsimp [G, δ, VarianceReducedMirrorDescentSetup.estimatorProcessAt,
      VarianceReducedMirrorDescentSetup.deltaProcessAt,
      VarianceReducedMirrorDescentSetup.delta]
    abel
  have hsmooth :=
    smooth_absorption_for_estimator_residual_for_lemma_5_14
      setup xt y G δ hηL hG
  have hprox :=
    prox_three_point_for_paper_step_for_lemma_5_14 setup s t hs x ω
  have hconv_raw := setup.f_convex_mu0 xt.1 x.1 xt.2 x.2
  have hconv :
      setup.fOn xt - setup.fOn x +
          ⟪setup.gradF xt.1, x.1 - xt.1⟫_ℝ ≤ 0 := by
    change setup.fAvg x.1 ≥
      setup.fAvg xt.1 + ⟪setup.gradF xt.1, x.1 - xt.1⟫_ℝ at hconv_raw
    change setup.fAvg xt.1 - setup.fAvg x.1 +
      ⟪setup.gradF xt.1, x.1 - xt.1⟫_ℝ ≤ 0
    linarith
  have hmain :
      setup.η * (setup.PsiOn y - setup.PsiOn x) + setup.VOn y x ≤
        setup.VOn xt x + setup.η * ⟪δ, x.1 - xt.1⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm δ ^ 2 := by
    have hη_nonneg : 0 ≤ setup.η := le_of_lt setup.eta_pos
    have hconv_scaled :
        setup.η *
            (setup.fOn xt - setup.fOn x +
              ⟪setup.gradF xt.1, x.1 - xt.1⟫_ℝ) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hη_nonneg hconv
    dsimp [G, δ] at hG hsmooth hprox
    rw [hG] at hsmooth
    rw [hG] at hprox
    exact
      smooth_prox_convex_algebra_for_lemma_5_14 setup xt y x δ
        (by simpa [δ] using hsmooth)
        (by simpa [xt, y, δ] using hprox)
        hconv_scaled
  simpa [xt, y, δ] using hmain

/-- Conditional-expectation assembly step for Lan Lemma 5.14.

This helper isolates the remaining measure-theoretic bookkeeping in Lemma 5.14
proof step 3: apply conditional-expectation monotonicity to the pathwise
descent recursion, split the conditional expectation of the affine right-hand
side, cancel the adapted inner-product noise term, and scale the Lemma 5.13
second-moment bound.  Search audit: checked the pre-searched candidates
`MeasureTheory.condExp_mono`, `MeasureTheory.condExp_add`,
`MeasureTheory.condExp_smul`, `MeasureTheory.condExp_of_stronglyMeasurable`,
and SOptLib `condExp_inner_sub_const_eq_zero_of_condExp_eq_zero`; these are the
right reusable APIs, while this helper packages the VRMD-specific finite-range
integrability/adaptedness side conditions around `epochSamplePastBefore`. -/
private theorem lemma_5_14_conditional_descent_ce_assembly
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hpath : ∀ ω,
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar ≤
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) :
    ((setup.P[fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar))) := by
  calc
    (setup.P[fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar |
        setup.epochSamplePastBefore s t])
        ≤ᵐ[setup.P]
      setup.P[fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          setup.η * ⟪setup.deltaProcessAt s t ω,
            xStar.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2 |
        setup.epochSamplePastBefore s t] := by
        exact lemma_5_14_conditional_descent_ce_raw setup s t hs xStar hpath
    _ ≤ᵐ[setup.P]
      fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar)) := by
        exact lemma_5_14_conditional_descent_ce_rhs_bound setup s t hs xStar h_opt

/-- Conditional-expectation half of Lan Lemma 5.14.

This aligns with Lan Lemma 5.14 proof step 3: condition the pathwise recursion
on the sample past, use the mean-zero residual and Lemma 5.13 second-moment
control, and identify sample-past-measurable terms with their conditional
expectations.  Search audit: checked the pre-searched probability candidates
`iIndepFun.indep_past_iSup_current`, `IdentDistrib.integral_comp_eq_of_measurable`,
`Measurable.of_measurableSpace_le`, plus Mathlib
`MeasureTheory.condExp_mono`, `MeasureTheory.condExp_of_stronglyMeasurable`,
and `MeasureTheory.condExp_condExp_of_le`; the reusable APIs cover the tower and
monotonicity pieces, while this helper packages the VRMD-specific
`epochSamplePastBefore` conditioning route. -/
private theorem lemma_5_14_conditional_descent
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hηL : setup.L * setup.η ≤ 1 / 2) :
    ((setup.P[fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar))
        ) := by
  refine lemma_5_14_conditional_descent_ce_assembly setup s t hs xStar h_opt ?_
  intro ω
  simpa [sub_eq_add_neg, inner_neg_right] using
    lemma_5_14_pathwise_descent setup s t hs xStar hηL ω

/-- Lemma 5.14 one-step VRMD recursion in the `μ = 0` smooth-convex regime,
exposed only on the finite Algorithm 5.6 inner-loop domain `t = 1, ..., T_s`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/key_lemmas/4/statement_math`.
Quote: `If L\gamma \le 1/2, \text{ then } \forall x \in X`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/proof/0/description`.
Quote: `over t=1,...,T inside one epoch`. -/
theorem lemma_5_14
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hηL : setup.L * setup.η ≤ 1 / 2) :
    (∀ ω,
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn x) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ x ≤
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ x +
          setup.η *
            ⟪setup.deltaProcessAt s t ω,
              x.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) ∧
    ((setup.P[fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar))
        ) := by
  exact
    ⟨lemma_5_14_pathwise_descent setup s t hs x hηL,
      lemma_5_14_conditional_descent setup s t hs xStar h_opt hηL⟩

/-- Guarded compatibility route for one-step VRMD proof experiments.

The deterministic pathwise part uses the canonical prox/Bregman objects already
realized in this file.  The explicit component-convexity premise is redundant
with `setup.hcomponent_convex` and remains only for suffixed-helper
compatibility. -/
theorem lemma_5_14_of_component_convex
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (hcomponent_convex : ∀ i, ConvexOn ℝ setup.X (setup.f i))
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (x xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hηL : setup.L * setup.η ≤ 1 / 2) :
    (∀ ω,
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn x) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ x ≤
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ x +
          setup.η *
            ⟪setup.deltaProcessAt s t ω,
              x.1 - setup.paperInnerIterAt s t ω⟫_ℝ +
          setup.η ^ 2 * SOptLib.dualNorm (setup.deltaProcessAt s t ω) ^ 2) ∧
    ((setup.P[fun ω =>
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar |
        setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P]
      fun ω =>
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar))
        ) := by
  exact lemma_5_14 setup s t hs x xStar h_opt hηL

/-- Integrability side condition for the selected-output objective in Theorem 5.6.

This is a derived finite-sample/process regularity obligation, not a setup
assumption.  It is isolated so the paper-facing theorem can consume the
canonical SOptLib expectation bridge after the epoch telescope is available. -/
private theorem theorem_5_6_output_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : ℕ) (hS : 1 ≤ S)
    (xStar : {x : E // x ∈ setup.X}) :
    Integrable (fun ω => setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω)) setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  let N := setup.epochOffset S
  let Y : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] Y := by
    simpa [Y] using setup.samplePrefixVector_measurable N
  have hY : Measurable Y := hprefix_past.mono hm le_rfl
  have hfin : (Set.range Y).Finite :=
    Set.finite_univ.subset (by intro y hy; exact Set.mem_univ y)
  refine integrable_real_of_finite_range_factor (μ := setup.P) hY hfin ?_
  intro ω ω' hYY
  apply congrArg setup.PsiOn
  apply Subtype.ext
  change setup.barX ⟨S, hS⟩ ω = setup.barX ⟨S, hS⟩ ω'
  have hsum :
      Finset.sum (setup.outputEpochs ⟨S, hS⟩)
          (fun s => setup.w s • setup.snapshotIter s ω) =
        Finset.sum (setup.outputEpochs ⟨S, hS⟩)
          (fun s => setup.w s • setup.snapshotIter s ω') := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hs_le : s ≤ S := by
      have hmem : s ∈ Finset.Icc 1 S := by
        simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
      exact (Finset.mem_Icc.mp hmem).2
    have hNepoch : setup.epochOffset s ≤ N := by
      dsimp [N]
      unfold VarianceReducedMirrorDescentSetup.epochOffset
      refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
      · intro k hk
        rcases Finset.mem_Icc.mp hk with ⟨hk1, hks⟩
        exact Finset.mem_Icc.mpr ⟨hk1, le_trans hks hs_le⟩
      · intro k hkS hknot
        exact Nat.zero_le _
    obtain ⟨decode, hdecode⟩ :=
      setup.snapshotIter_factorizes_through_globalPrefix s N hNepoch
    have hsnap : setup.snapshotIter s ω = setup.snapshotIter s ω' := by
      rw [hdecode]
      exact congrArg decode hYY
    exact congrArg (fun x => setup.w s • x) hsnap
  rw [setup.barX_def ⟨S, hS⟩ ω, setup.barX_def ⟨S, hS⟩ ω']
  exact congrArg (fun z : E => (setup.outputWeightSum ⟨S, hS⟩)⁻¹ • z) hsum

/-- Jensen/output-average gap bridge for Theorem 5.6.

This aligns with Lan Theorem 5.6 proof step 2: after the epoch inequalities are
summed, convexity of `Ψ` turns the weighted snapshot average `bar{x}^S` into the
normalized weighted sum of snapshot objective gaps.  Reuse audit: checked the
pre-searched candidates `Convex.normalized_weighted_sum_mem`,
`expectedOutput_eq_weighted_sum_div`, and SOptLib's
`weighted_average_sub_baseline_le_weighted_gap`; the last exactly packages the
baseline-shift algebra once the local Jensen lemma
`Psi_barXCarrier_le_weighted_sum` supplies the weighted objective bound. -/
private theorem theorem_5_6_weighted_output_jensen_gap
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X}) :
    ∀ ω,
      setup.PsiOn (setup.barXCarrier S ω) - setup.PsiOn xStar ≤
        (setup.outputWeightSum S)⁻¹ *
          Finset.sum (setup.outputEpochs S)
            (fun s =>
              setup.w s *
                (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar)) := by
  intro ω
  exact
    weighted_average_sub_baseline_le_weighted_gap
      (s := setup.outputEpochs S)
      (γ := setup.w)
      (F := fun s => setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩)
      (value := setup.PsiOn (setup.barXCarrier S ω))
      (baseline := setup.PsiOn xStar)
      (W := setup.outputWeightSum S)
      (setup.outputWeightSum_pos S)
      (by simpa [setup.outputWeightSum_eq S])
      (setup.Psi_barXCarrier_le_weighted_sum S ω)

/-- Expectation-level Jensen/output-average gap bridge for Theorem 5.6.

This aligns with Lan Theorem 5.6 proof step 2 after taking expectations: the
already-proved pointwise Jensen bridge is integrated under the finite weighted
snapshot-gap integrability side condition.  Reuse audit: considered
`integral_sum_telescope_bound_of_pointwise_lower_bound` and SOptLib finite-output
expectation helpers; those package telescope-to-expectation bounds, while this
local bridge is only the monotone integration of
`theorem_5_6_weighted_output_jensen_gap`. -/
private theorem theorem_5_6_expected_jensen_gap
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (hbar_int :
      Integrable (fun ω => setup.PsiOn (setup.barXCarrier S ω)) setup.P)
    (hweighted_int :
      Integrable
        (fun ω =>
          Finset.sum (setup.outputEpochs S)
            (fun s =>
              setup.w s *
                (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar))) setup.P) :
    ∫ ω, setup.PsiOn (setup.barXCarrier S ω) ∂setup.P - setup.PsiOn xStar ≤
      (setup.outputWeightSum S)⁻¹ *
        ∫ ω,
          Finset.sum (setup.outputEpochs S)
            (fun s =>
              setup.w s *
                (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar)) ∂setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  let gap : Ω → ℝ := fun ω => setup.PsiOn (setup.barXCarrier S ω)
  let weightedGap : Ω → ℝ := fun ω =>
    Finset.sum (setup.outputEpochs S)
      (fun s =>
        setup.w s *
          (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar))
  let baseline : ℝ := setup.PsiOn xStar
  let W : ℝ := setup.outputWeightSum S
  have hgap_int : Integrable gap setup.P := by
    simpa [gap] using hbar_int
  have hweightedGap_int : Integrable weightedGap setup.P := by
    simpa [weightedGap] using hweighted_int
  have hleft_int : Integrable (fun ω => gap ω - baseline) setup.P := by
    exact hgap_int.sub (integrable_const (c := baseline))
  have hright_int : Integrable (fun ω => W⁻¹ * weightedGap ω) setup.P := by
    exact hweightedGap_int.const_mul W⁻¹
  have hpoint : (fun ω => gap ω - baseline) ≤ᵐ[setup.P]
      fun ω => W⁻¹ * weightedGap ω := by
    exact Filter.Eventually.of_forall (fun ω => by
      simpa [gap, weightedGap, baseline, W] using
        theorem_5_6_weighted_output_jensen_gap setup S xStar ω)
  have hmono := MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hleft_eq :
      ∫ ω, gap ω - baseline ∂setup.P =
        ∫ ω, gap ω ∂setup.P - baseline := by
    rw [MeasureTheory.integral_sub hgap_int (integrable_const (c := baseline))]
    simp [baseline]
  have hright_eq :
      ∫ ω, W⁻¹ * weightedGap ω ∂setup.P =
        W⁻¹ * ∫ ω, weightedGap ω ∂setup.P := by
    rw [MeasureTheory.integral_const_mul]
  rw [hleft_eq, hright_eq] at hmono
  simpa [gap, weightedGap, baseline, W] using hmono

/-- Integrability of the finite weighted snapshot-gap process in Theorem 5.6.

This is a derived finite-prefix regularity fact, not a setup assumption.  It is
the expectation-level replacement for the older pathwise telescope route: the
epoch telescope now integrates the weighted snapshot gaps directly. -/
private theorem theorem_5_6_weighted_snapshot_gap_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X}) :
    Integrable
      (fun ω =>
        Finset.sum (setup.outputEpochs S)
          (fun s =>
            setup.w s *
              (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                setup.PsiOn xStar))) setup.P := by
  -- Each snapshot in the finite output window factorizes through the finite
  -- sample prefix up to `epochOffset S`; hence the weighted finite sum has
  -- finite range and is integrable under the probability measure.
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  let N := setup.epochOffset S.1
  let Y : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] Y := by
    simpa [Y] using setup.samplePrefixVector_measurable N
  have hY : Measurable Y := hprefix_past.mono hm le_rfl
  have hfin : (Set.range Y).Finite :=
    Set.finite_univ.subset (by intro y hy; exact Set.mem_univ y)
  refine integrable_real_of_finite_range_factor (μ := setup.P) hY hfin ?_
  intro ω ω' hYY
  refine Finset.sum_congr rfl ?_
  intro s hs
  have hs_le : s ≤ S.1 := by
    have hmem : s ∈ Finset.Icc 1 S.1 := by
      simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
    exact (Finset.mem_Icc.mp hmem).2
  have hNepoch : setup.epochOffset s ≤ N := by
    dsimp [N]
    unfold VarianceReducedMirrorDescentSetup.epochOffset
    refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hks⟩
      exact Finset.mem_Icc.mpr ⟨hk1, le_trans hks hs_le⟩
    · intro k hkS hknot
      exact Nat.zero_le _
  obtain ⟨decode, hdecode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix s N hNepoch
  have hsnap : setup.snapshotIter s ω = setup.snapshotIter s ω' := by
    rw [hdecode]
    exact congrArg decode hYY
  have hcarrier :
      (⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.snapshotIter s ω', setup.snapshotIter_mem s ω'⟩ := by
    exact Subtype.ext hsnap
  simp [hcarrier]

/-- Conditional-to-unconditional integral bridge for epoch-recursion steps.

This aligns with Lan Theorem 5.6 proof step 1: after Lemma 5.14 gives a
conditional one-step inequality, integrate the conditional expectation and use
the tower identity to obtain the unconditional expected one-step inequality.
Reuse audit: checked Mathlib `MeasureTheory.integral_condExp`,
`MeasureTheory.integral_mono_ae`, and SOptLib
`integral_eq_zero_of_condExp_ae_eq_zero`; the SOptLib lemma handles equality to
zero, while this theorem packages the inequality form needed here. -/
private theorem integral_le_of_condExp_le
    {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) [IsFiniteMeasure P] {f g : Ω → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hcond : P[f | m] ≤ᵐ[P] g) :
    ∫ ω, f ω ∂P ≤ ∫ ω, g ω ∂P := by
  haveI : SigmaFinite (P.trim hm) := by infer_instance
  have hce_int : Integrable (P[f | m]) P := integrable_condExp
  have hmono : ∫ ω, (P[f | m]) ω ∂P ≤ ∫ ω, g ω ∂P :=
    MeasureTheory.integral_mono_ae hce_int hg hcond
  have hce_eq : ∫ ω, (P[f | m]) ω ∂P = ∫ ω, f ω ∂P :=
    MeasureTheory.integral_condExp (μ := P) (m := m) (f := f) hm
  simpa [hce_eq] using hmono

/-- Unconditional one-step expectation form of Lemma 5.14.

This aligns with Lan Theorem 5.6 proof step 1: integrate the conditional
Lemma 5.14 descent inequality over the epoch sample-past sigma-algebra.  Reuse
audit: selected local `lemma_5_14`, `lemma_5_14_raw_left_integrable`,
`current_bregman_epochSamplePastBefore_measurable_integrable`,
`two_Psi_gap_epoch_past_measurable_integrable`, and
`integral_le_of_condExp_le`; searched SOptLib/Mathlib conditional-expectation
integral candidates, and no imported theorem packaged this exact inequality
with the VRMD right-hand observable. -/
private theorem lemma_5_14_unconditional_integral_step
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s) (hs : 1 ≤ s)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∫ ω,
        setup.η *
            (setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
            xStar ∂setup.P ≤
      ∫ ω,
        setup.VOn
          ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
          4 * setup.LQ * setup.η ^ 2 *
            ((setup.PsiOn
                  ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
                setup.PsiOn xStar) +
              (setup.PsiOn
                  ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
                setup.PsiOn xStar)) ∂setup.P := by
  classical
  let f : Ω → ℝ := fun ω =>
    setup.η *
        (setup.PsiOn
            ⟨setup.paperNextInnerIterAt s t ω,
              setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
      setup.VOn
        ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
        xStar
  let twoGap : Ω → ℝ := fun ω =>
    4 * setup.LQ *
      ((setup.PsiOn
            ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ -
          setup.PsiOn xStar) +
        (setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar))
  let g : Ω → ℝ := fun ω =>
    setup.VOn
      ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
      setup.η ^ 2 * twoGap ω
  have hm : setup.epochSamplePastBefore s t ≤ (by infer_instance : MeasurableSpace Ω) := by
    exact le_trans (setup.epochSamplePastBefore_le_globalSamplePrefix s t)
      (by
        let N := setup.sampleIndex (s - 1) (t.1 - 1)
        simpa [N] using (setup.filtration).le N)
  have hf : Integrable f setup.P := by
    simpa [f] using lemma_5_14_raw_left_integrable setup s t hs xStar
  have hV_int :
      Integrable
        (fun ω =>
          setup.VOn
            ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar)
        setup.P :=
    (current_bregman_epochSamplePastBefore_measurable_integrable setup s t hs xStar).2
  have htwoGap_int : Integrable twoGap setup.P := by
    simpa [twoGap] using
      (two_Psi_gap_epoch_past_measurable_integrable setup s t hs xStar).2
  have hg : Integrable g setup.P := by
    simpa [g] using hV_int.add (htwoGap_int.const_mul (setup.η ^ 2))
  have hcond :
      (setup.P[f | setup.epochSamplePastBefore s t]) ≤ᵐ[setup.P] g := by
    simpa [f, g, twoGap, mul_assoc, mul_left_comm, mul_comm] using
      (lemma_5_14 setup s t hs xStar xStar h_opt setup.L_eta_le_half).2
  haveI : IsProbabilityMeasure setup.P := setup.hP
  have hstep := integral_le_of_condExp_le
    (P := setup.P) (m := setup.epochSamplePastBefore s t)
    hm hf hg hcond
  simpa [f, g, twoGap, mul_assoc, mul_left_comm, mul_comm] using hstep

/-- Epoch endpoints are feasible, exposed for the fixed-epoch absorption step.

This is an endpoint feasibility bridge for Algorithm 5.6: at epoch zero the
endpoint is the initial point, and at positive epochs it is the last
paper-facing next-inner iterate.  Reuse audit: checked the local internal
process invariant, but it is private to the setup namespace; the public
`paperNextInnerIterAt_mem` theorem gives the needed endpoint membership without
adding a new assumption. -/
private theorem fixed_epoch_xEpochIter_mem
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) (s : ℕ) (ω : Ω) :
    setup.xEpochIter s ω ∈ setup.X := by
  cases s with
  | zero =>
      simp [VarianceReducedMirrorDescentSetup.xEpochIter,
        VarianceReducedMirrorDescentSetup.paperEpoch,
        VarianceReducedMirrorDescentSetup.internalProcess, setup.hw₀_mem]
  | succ s' =>
      have hTpos : 1 ≤ setup.T (s' + 1) := by
        simp [VarianceReducedMirrorDescentSetup.T]
        exact Nat.succ_le_of_lt
          (Nat.mul_pos (by norm_num) (pow_pos (by norm_num : 0 < 2) s'))
      let t : setup.InnerStep (s' + 1) :=
        ⟨setup.T (s' + 1), ⟨hTpos, le_rfl⟩⟩
      have hnext := setup.paperNextInnerIterAt_mem (s' + 1) t ω
      have hnot : ¬ t.1 < setup.T (s' + 1) := by
        dsimp [t]
        exact Nat.lt_irrefl _
      simpa [VarianceReducedMirrorDescentSetup.paperNextInnerIterAt,
        VarianceReducedMirrorDescentSetup.xEpochIter, t, hnot] using hnext

/-- Expected previous-epoch objective gaps are nonnegative by optimality of
`xStar` on the carrier.

This is the elementary absorption side condition in Lan Theorem 5.6 proof step
2.  Reuse audit: searched SOptLib/Mathlib for coefficient absorption and
nonnegative-integral helpers; `integral_nonneg` is the matching Mathlib atom,
while no SOptLib lemma packages this paper's `xEpochIter` feasibility bridge. -/
private theorem fixed_epoch_prev_gap_nonneg
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (s : ℕ) :
    0 ≤
      ∫ ω,
        setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P := by
  refine integral_nonneg ?_
  intro ω
  have hx : setup.xEpochIter (s - 1) ω ∈ setup.X :=
    fixed_epoch_xEpochIter_mem setup (s - 1) ω
  have hoptω := h_opt ⟨setup.xEpochIter (s - 1) ω, hx⟩
  have hcoe :
      setup.PsiOn ⟨setup.xEpochIter (s - 1) ω, hx⟩ =
        setup.Psi (setup.xEpochIter (s - 1) ω) := by
    simpa using setup.PsiOn_coe ⟨setup.xEpochIter (s - 1) ω, hx⟩
  change (0 : ℝ) ≤ setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar
  rw [← hcoe]
  exact sub_nonneg.mpr hoptω

/-- Coefficient absorption used after the fixed-epoch sum.

This aligns with Lan Theorem 5.6 proof step 2: `4 L_Q γ ≤ 1` implies
`4 L_Q γ^2 * gap ≤ γ * gap` for any nonnegative gap.  Reuse audit: searched for
SOptLib absorption helpers; the hits target quadratic/cross-term descent
absorption, so the needed scalar monotonicity is proved directly. -/
private theorem fixed_epoch_absorb_first_gap
    (setup : VarianceReducedMirrorDescentSetup ι E Ω) {gap : ℝ}
    (hgap_nonneg : 0 ≤ gap) :
    4 * setup.LQ * setup.η ^ 2 * gap ≤ setup.η * gap := by
  have hη_nonneg : 0 ≤ setup.η := le_of_lt setup.eta_pos
  have hcoeff_le_eta : 4 * setup.LQ * setup.η ^ 2 ≤ setup.η := by
    have hmul := mul_le_mul_of_nonneg_right setup.four_LQ_eta_le_one hη_nonneg
    nlinarith
  exact mul_le_mul_of_nonneg_right hcoeff_le_eta hgap_nonneg

/-- First inner iterate equals the previous epoch endpoint.

This is Lan Algorithm 5.6 step 0, `x_1 = x^{s-1}`. Reuse audit: checked the
pre-searched endpoint candidates `paperInnerIterInWindow_eq_at`,
`paperEpoch_inner_eq_internalCarrier`, and `xEpochIter_eq_paper_last`; they
provide adjacent local bridges but not this positive-epoch start identity, so
this helper specializes the local `internalProcess` recursion. -/
private theorem fixed_epoch_first_inner_eq_prev_epoch
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (hs : 1 ≤ s) (t : setup.InnerStep s) (ht : t.1 = 1) :
    setup.paperInnerIterAt s t = setup.xEpochIter (s - 1) := by
  cases s with
  | zero => omega
  | succ s' =>
      funext ω
      have ht0 : t.1 - 1 = 0 := by omega
      rw [setup.paperEpoch_inner_eq_internalCarrier (s' + 1) t]
      simp [VarianceReducedMirrorDescentSetup.internalInnerIter,
        VarianceReducedMirrorDescentSetup.internalProcess,
        VarianceReducedMirrorDescentSetup.xEpochIter,
        VarianceReducedMirrorDescentSetup.paperEpoch, ht0]

/-- Closed-interval telescope for predecessor-indexed current/next sums.

This is the pure finite-sum shape behind Lan Theorem 5.6 proof step 1 after
rewriting `x_t` as the zero-based carrier at `t-1` and `x_{t+1}` as the carrier
at `t`. Reuse audit: selected SOptLib `sum_Icc_sub_succ`; `outputWindow_sum_sub_succ`
has the same idea but is for positive-time subtype windows rather than this raw
`Finset.Icc 1 T` index. -/
private theorem fixed_epoch_sum_Icc_pred_telescope
    (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (Finset.sum (Finset.Icc 1 T) (fun n => A (n - 1))) -
        Finset.sum (Finset.Icc 1 T) (fun n => A n) =
      A 0 - A T := by
  rw [← Finset.sum_sub_distrib]
  have htel := sum_Icc_sub_succ (fun n => A (n - 1)) 1 T hT
  simpa using htel

/-- Split the predecessor-indexed epoch sum into its first term and the
remaining paper window.

This is the lower-end finite-sum split used in Lan Theorem 5.6 proof step 1.
Reuse audit: considered SOptLib `sum_Icc_sub_succ`, `outputWindow_sum_sub_succ`,
and Mathlib `Finset.sum_Icc_succ_top`; those telescope/split the upper endpoint,
so this local helper packages the raw `Finset.Icc 1 T` lower-end split. -/
private theorem sum_Icc_pred_split_first_tail
    (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    Finset.sum (Finset.Icc 1 T) (fun n => A (n - 1)) =
      A 0 + Finset.sum (Finset.Icc 2 T) (fun n => A (n - 1)) := by
  induction T with
  | zero => omega
  | succ T ih =>
      cases T with
      | zero =>
          simp
      | succ T =>
          have hT' : 1 ≤ T.succ := by omega
          have hih := ih hT'
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T.succ.succ)]
          rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ T.succ.succ)]
          rw [hih]
          ring

/-- Split the next-iterate epoch sum into the shifted middle window and terminal
endpoint.

This is the upper-end finite-sum reindexing used in Lan Theorem 5.6 proof step
1. Reuse audit: checked SOptLib `sum_Icc_sub_succ` and
`outputWindow_sum_sub_succ`; they give telescoping differences, not this
standalone paper-window split, while Mathlib `Finset.sum_Icc_succ_top` supplies
the endpoint step used in the proof below. -/
private theorem sum_Icc_self_split_tail_top
    (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    Finset.sum (Finset.Icc 1 T) A =
      Finset.sum (Finset.Icc 2 T) (fun n => A (n - 1)) + A T := by
  induction T with
  | zero => omega
  | succ T ih =>
      cases T with
      | zero =>
          simp
      | succ T =>
          have hT' : 1 ≤ T.succ := by omega
          have hih := ih hT'
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T.succ.succ)]
          rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ T.succ.succ)]
          rw [hih]
          have hidx : T + 1 + 1 - 1 = T + 1 := by omega
          rw [hidx]

/-- Raw fixed-epoch sum over the literal inner-step interval.

This is Lan Theorem 5.6 proof step 1 before any endpoint normalization:
sum the one-step recursion over `t = 1, ..., T_s`.  Reuse audit: selected
`Finset.sum_le_sum` as the exact finite-order atom after checking the supplied
SOptLib candidates `sum_Icc_sub_succ` and `outputWindow_sum_sub_succ`; those
are for the later telescope/reindexing phase, while this helper only packages
the `InnerStep` subtype coercion from `Finset.Icc 1 (T_s)`. -/
private theorem fixed_epoch_summed_step_raw_indexed
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (hstep :
      ∀ s, s ∈ setup.outputEpochs S → ∀ t : setup.InnerStep s,
        ∫ ω,
            setup.η *
                (setup.PsiOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
              setup.VOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P ≤
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
              4 * setup.LQ * setup.η ^ 2 *
                ((setup.PsiOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ -
                    setup.PsiOn xStar) +
                  (setup.PsiOn
                      ⟨setup.snapshotIter (s - 1) ω,
                        setup.snapshotIter_mem (s - 1) ω⟩ -
                    setup.PsiOn xStar)) ∂setup.P)
    (s : ℕ) (hs : s ∈ setup.outputEpochs S) :
    let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
              setup.η *
                  (setup.PsiOn
                      ⟨setup.paperNextInnerIterAt s t ω,
                        setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
                setup.VOn
                  ⟨setup.paperNextInnerIterAt s t ω,
                    setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0) ≤
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
              setup.VOn
                ⟨setup.paperInnerIterAt s t ω,
                  setup.paperInnerIterAt_mem s t ω⟩ xStar +
                coeff *
                  ((setup.PsiOn
                        ⟨setup.paperInnerIterAt s t ω,
                          setup.paperInnerIterAt_mem s t ω⟩ -
                      setup.PsiOn xStar) +
                    (setup.PsiOn
                        ⟨setup.snapshotIter (s - 1) ω,
                          setup.snapshotIter_mem (s - 1) ω⟩ -
                      setup.PsiOn xStar)) ∂setup.P
        else 0) := by
  classical
  let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
  refine Finset.sum_le_sum ?_
  intro n hn
  have h := hstep s hs ⟨n, Finset.mem_Icc.mp hn⟩
  simpa [hn, coeff] using h

/-- Integrability of any real observable of the next paper inner iterate.

This is route-local infrastructure for Lan Theorem 5.6 proof step 1. Reuse
audit: checked the pre-searched `lemma_5_14_raw_left_integrable` and
`paperNextInnerIter_factorizes_through_globalPrefix`; the former only gives the
combined left observable, while the latter plus `integrable_real_of_finite_range_factor`
gives each split component needed by `MeasureTheory.integral_add`. -/
private theorem paperNextInnerIter_observable_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s)
    (Φ : {x : E // x ∈ setup.X} → ℝ) :
    Integrable
      (fun ω =>
        Φ ⟨setup.paperNextInnerIterAt s t ω,
          setup.paperNextInnerIterAt_mem s t ω⟩) setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) t.1
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let Z : Ω → ℝ := fun ω =>
    Φ ⟨setup.paperNextInnerIterAt s t ω,
      setup.paperNextInnerIterAt_mem s t ω⟩
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  obtain ⟨decodeNext, hdecodeNext_raw⟩ :
      ∃ decode : (Fin N → ι) → E,
        setup.paperNextInnerIterAt s t =
          fun ω => decode (prefixVec ω) := by
    simpa [N, prefixVec] using
      setup.paperNextInnerIter_factorizes_through_globalPrefix s t
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hnext : setup.paperNextInnerIterAt s t ω =
        setup.paperNextInnerIterAt s t ω' := by
      calc
        setup.paperNextInnerIterAt s t ω = decodeNext (prefixVec ω) :=
          congrFun hdecodeNext_raw ω
        _ = decodeNext (prefixVec ω') := by rw [hp]
        _ = setup.paperNextInnerIterAt s t ω' :=
          (congrFun hdecodeNext_raw ω').symm
    have hnext_sub :
        (⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperNextInnerIterAt s t ω', setup.paperNextInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hnext
    simpa [Z, hnext_sub]
  have hfin : (Set.range prefixVec).Finite := Set.toFinite _
  simpa [Z] using
    integrable_real_of_finite_range_factor (μ := setup.P) hprefix_top hfin hconst

/-- Integrability of any real observable of the current paper inner iterate.

This is route-local infrastructure for Lan Theorem 5.6 proof step 1. Reuse
audit: checked `current_bregman_epochSamplePastBefore_measurable_integrable`
and `two_Psi_gap_epoch_past_measurable_integrable`; they cover particular
combined observables, while `paperInnerIter_factorizes_through_globalPrefix`
gives the individual split components needed here. -/
private theorem paperInnerIter_observable_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (s : ℕ) (t : setup.InnerStep s)
    (Φ : {x : E // x ∈ setup.X} → ℝ) :
    Integrable
      (fun ω =>
        Φ ⟨setup.paperInnerIterAt s t ω,
          setup.paperInnerIterAt_mem s t ω⟩) setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.sampleIndex (s - 1) (t.1 - 1)
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let Z : Ω → ℝ := fun ω =>
    Φ ⟨setup.paperInnerIterAt s t ω,
      setup.paperInnerIterAt_mem s t ω⟩
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  obtain ⟨decodeInner, hinner_decode⟩ :=
    setup.paperInnerIter_factorizes_through_globalPrefix s t t le_rfl
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hinner : setup.paperInnerIterAt s t ω =
        setup.paperInnerIterAt s t ω' := by
      calc
        setup.paperInnerIterAt s t ω = decodeInner (prefixVec ω) := by
          simpa [prefixVec, N] using congrFun hinner_decode ω
        _ = decodeInner (prefixVec ω') := by rw [hp]
        _ = setup.paperInnerIterAt s t ω' := by
          simpa [prefixVec, N] using (congrFun hinner_decode ω').symm
    have hinner_sub :
        (⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.paperInnerIterAt s t ω', setup.paperInnerIterAt_mem s t ω'⟩ :=
      Subtype.ext hinner
    simpa [Z, hinner_sub]
  have hfin : (Set.range prefixVec).Finite := Set.toFinite _
  simpa [Z] using
    integrable_real_of_finite_range_factor (μ := setup.P) hprefix_top hfin hconst

/-- Integrability of any real observable of a snapshot iterate.

This is route-local infrastructure for Lan Theorem 5.6 proof step 1. Reuse
audit: checked snapshot-specific finite-prefix helpers and the SOptLib finite-sum
integrability closures; no existing lemma stated the individual snapshot gap
observable needed to split the repeated epoch-constant integral term. -/
private theorem snapshotIter_observable_integrable
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (k : ℕ) (Φ : {x : E // x ∈ setup.X} → ℝ) :
    Integrable
      (fun ω =>
        Φ ⟨setup.snapshotIter k ω, setup.snapshotIter_mem k ω⟩) setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  haveI : IsFiniteMeasure setup.P := inferInstance
  let N := setup.epochOffset k
  let prefixVec : Ω → (Fin N → ι) := fun ω j => setup.ξ j.1 ω
  let Z : Ω → ℝ := fun ω =>
    Φ ⟨setup.snapshotIter k ω, setup.snapshotIter_mem k ω⟩
  have hm : (setup.filtration).seq N ≤ (by infer_instance : MeasurableSpace Ω) := by
    simpa [VarianceReducedMirrorDescentSetup.filtration] using (setup.filtration).le N
  have hprefix_past : Measurable[(setup.filtration).seq N] prefixVec := by
    simpa [prefixVec] using setup.samplePrefixVector_measurable N
  have hprefix_top : Measurable prefixVec := hprefix_past.mono hm le_rfl
  obtain ⟨decodeSnap, hsnap_decode⟩ :=
    setup.snapshotIter_factorizes_through_globalPrefix k N le_rfl
  have hconst : ∀ ⦃ω ω' : Ω⦄, prefixVec ω = prefixVec ω' → Z ω = Z ω' := by
    intro ω ω' hp
    have hsnap : setup.snapshotIter k ω = setup.snapshotIter k ω' := by
      calc
        setup.snapshotIter k ω = decodeSnap (prefixVec ω) := by
          simpa [prefixVec, N] using congrFun hsnap_decode ω
        _ = decodeSnap (prefixVec ω') := by rw [hp]
        _ = setup.snapshotIter k ω' := by
          simpa [prefixVec, N] using (congrFun hsnap_decode ω').symm
    have hsnap_sub :
        (⟨setup.snapshotIter k ω, setup.snapshotIter_mem k ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.snapshotIter k ω', setup.snapshotIter_mem k ω'⟩ :=
      Subtype.ext hsnap
    simpa [Z, hsnap_sub]
  have hfin : (Set.range prefixVec).Finite := Set.toFinite _
  simpa [Z] using
    integrable_real_of_finite_range_factor (μ := setup.P) hprefix_top hfin hconst

/-- Split the raw fixed-epoch integral sum into separate expected gap,
Bregman, and constant snapshot sums.

This is the measure-linearity part of Lan Theorem 5.6 proof step 1. Reuse
audit: checked `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul`,
`MeasureTheory.integral_finset_sum`, and SOptLib
`integrable_finset_sum_const_mul`; those are the generic atoms, but this helper
still has to specialize the existing `lemma_5_14_raw_left_integrable` and
`two_Psi_gap_epoch_past_measurable_integrable` side conditions to the local
`InnerStep` indexing. -/
private theorem fixed_epoch_raw_integral_sums_split
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) (hs_pos : 1 ≤ s)
    (hraw :
      let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.η *
                    (setup.PsiOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
                  setup.VOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
          else 0) ≤
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.VOn
                  ⟨setup.paperInnerIterAt s t ω,
                    setup.paperInnerIterAt_mem s t ω⟩ xStar +
                  coeff *
                    ((setup.PsiOn
                          ⟨setup.paperInnerIterAt s t ω,
                            setup.paperInnerIterAt_mem s t ω⟩ -
                        setup.PsiOn xStar) +
                      (setup.PsiOn
                          ⟨setup.snapshotIter (s - 1) ω,
                            setup.snapshotIter_mem (s - 1) ω⟩ -
                        setup.PsiOn xStar)) ∂setup.P
          else 0)) :
    let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
    let nextGapSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)
    let nextVSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)
    let currVSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)
    let currGapSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω,
                  setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)
    let prevSnapshotGap : ℝ :=
      ∫ ω,
        setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar ∂setup.P
    setup.η * nextGapSum + nextVSum ≤
      currVSum + coeff * currGapSum +
        coeff * (setup.T s : ℝ) * prevSnapshotGap := by
  classical
  let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
  let nextGapSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.PsiOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ -
            setup.PsiOn xStar ∂setup.P
      else 0)
  let nextVSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω,
              setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
      else 0)
  let currVSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.VOn
            ⟨setup.paperInnerIterAt s t ω,
              setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P
      else 0)
  let currGapSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.PsiOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ -
            setup.PsiOn xStar ∂setup.P
      else 0)
  let prevSnapshotGap : ℝ :=
    ∫ ω,
      setup.PsiOn
          ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
        setup.PsiOn xStar ∂setup.P
  let I : Finset ℕ := Finset.Icc 1 (setup.T s)
  have hT_pos : 1 ≤ setup.T s := by
    have hs0 : s ≠ 0 := by omega
    simp [VarianceReducedMirrorDescentSetup.T, hs0]
    exact Nat.succ_le_of_lt
      (Nat.mul_pos (by norm_num : 0 < 7) (pow_pos (by norm_num : (0 : ℕ) < 2) _))
  have hleft :
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.η *
                    (setup.PsiOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
                  setup.VOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
          else 0)) = setup.η * nextGapSum + nextVSum := by
    calc
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.η *
                    (setup.PsiOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
                  setup.VOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
          else 0))
          =
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            setup.η *
              (∫ ω,
                setup.PsiOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ -
                  setup.PsiOn xStar ∂setup.P) +
              ∫ ω,
                setup.VOn
                  ⟨setup.paperNextInnerIterAt s t ω,
                    setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hnmem
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hnmem⟩
            have hgap_int :
                Integrable
                  (fun ω =>
                    setup.PsiOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ -
                      setup.PsiOn xStar) setup.P := by
              simpa [t] using
                paperNextInnerIter_observable_integrable setup s t
                  (fun x => setup.PsiOn x - setup.PsiOn xStar)
            have hV_int :
                Integrable
                  (fun ω =>
                    setup.VOn
                      ⟨setup.paperNextInnerIterAt s t ω,
                        setup.paperNextInnerIterAt_mem s t ω⟩ xStar) setup.P := by
              simpa [t] using
                paperNextInnerIter_observable_integrable setup s t
                  (fun x => setup.VOn x xStar)
            have hterm :
                (∫ ω,
                    setup.η *
                        (setup.PsiOn
                            ⟨setup.paperNextInnerIterAt s t ω,
                              setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
                      setup.VOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P)
                  =
                setup.η *
                  (∫ ω,
                    setup.PsiOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ -
                      setup.PsiOn xStar ∂setup.P) +
                  ∫ ω,
                    setup.VOn
                      ⟨setup.paperNextInnerIterAt s t ω,
                        setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P := by
              rw [MeasureTheory.integral_add (hgap_int.const_mul setup.η) hV_int]
              rw [MeasureTheory.integral_const_mul]
            simpa [hnmem, t] using hterm
      _ = setup.η * nextGapSum + nextVSum := by
            simp only [nextGapSum, nextVSum]
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro n hnmem
            simp [hnmem]
  have hright :
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.VOn
                  ⟨setup.paperInnerIterAt s t ω,
                    setup.paperInnerIterAt_mem s t ω⟩ xStar +
                  coeff *
                    ((setup.PsiOn
                          ⟨setup.paperInnerIterAt s t ω,
                            setup.paperInnerIterAt_mem s t ω⟩ -
                        setup.PsiOn xStar) +
                      (setup.PsiOn
                          ⟨setup.snapshotIter (s - 1) ω,
                            setup.snapshotIter_mem (s - 1) ω⟩ -
                        setup.PsiOn xStar)) ∂setup.P
          else 0)) = currVSum + coeff * currGapSum +
            coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    have hsnap_int :
        Integrable
          (fun ω =>
            setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar) setup.P := by
      simpa using
        snapshotIter_observable_integrable setup (s - 1)
          (fun x => setup.PsiOn x - setup.PsiOn xStar)
    calc
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.VOn
                  ⟨setup.paperInnerIterAt s t ω,
                    setup.paperInnerIterAt_mem s t ω⟩ xStar +
                  coeff *
                    ((setup.PsiOn
                          ⟨setup.paperInnerIterAt s t ω,
                            setup.paperInnerIterAt_mem s t ω⟩ -
                        setup.PsiOn xStar) +
                      (setup.PsiOn
                          ⟨setup.snapshotIter (s - 1) ω,
                            setup.snapshotIter_mem (s - 1) ω⟩ -
                        setup.PsiOn xStar)) ∂setup.P
          else 0))
          =
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            (∫ ω,
              setup.VOn
                ⟨setup.paperInnerIterAt s t ω,
                  setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P) +
              coeff *
                (∫ ω,
                  setup.PsiOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ -
                    setup.PsiOn xStar ∂setup.P) +
              coeff * prevSnapshotGap
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hnmem
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hnmem⟩
            have hV_int :
                Integrable
                  (fun ω =>
                    setup.VOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ xStar) setup.P := by
              exact (current_bregman_epochSamplePastBefore_measurable_integrable
                setup s t hs_pos xStar).2
            have hgap_int :
                Integrable
                  (fun ω =>
                    setup.PsiOn
                        ⟨setup.paperInnerIterAt s t ω,
                          setup.paperInnerIterAt_mem s t ω⟩ -
                      setup.PsiOn xStar) setup.P := by
              simpa [t] using
                paperInnerIter_observable_integrable setup s t
                  (fun x => setup.PsiOn x - setup.PsiOn xStar)
            have hterm :
                (∫ ω,
                    setup.VOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ xStar +
                      coeff *
                        ((setup.PsiOn
                              ⟨setup.paperInnerIterAt s t ω,
                                setup.paperInnerIterAt_mem s t ω⟩ -
                            setup.PsiOn xStar) +
                          (setup.PsiOn
                              ⟨setup.snapshotIter (s - 1) ω,
                                setup.snapshotIter_mem (s - 1) ω⟩ -
                            setup.PsiOn xStar)) ∂setup.P)
                  =
                (∫ ω,
                  setup.VOn
                    ⟨setup.paperInnerIterAt s t ω,
                      setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P) +
                    coeff *
                      (∫ ω,
                        setup.PsiOn
                            ⟨setup.paperInnerIterAt s t ω,
                              setup.paperInnerIterAt_mem s t ω⟩ -
                          setup.PsiOn xStar ∂setup.P) +
                    coeff * prevSnapshotGap := by
              have hscaled_int :
                  Integrable
                    (fun ω =>
                      coeff *
                        ((setup.PsiOn
                              ⟨setup.paperInnerIterAt s t ω,
                                setup.paperInnerIterAt_mem s t ω⟩ -
                            setup.PsiOn xStar) +
                          (setup.PsiOn
                              ⟨setup.snapshotIter (s - 1) ω,
                                setup.snapshotIter_mem (s - 1) ω⟩ -
                            setup.PsiOn xStar))) setup.P := by
                simpa [smul_eq_mul] using (hgap_int.add hsnap_int).const_mul coeff
              rw [MeasureTheory.integral_add hV_int hscaled_int]
              rw [MeasureTheory.integral_const_mul]
              rw [MeasureTheory.integral_add hgap_int hsnap_int]
              simp [prevSnapshotGap, smul_eq_mul]
              ring
            simpa [hnmem, t] using hterm
      _ = currVSum + coeff * currGapSum +
            coeff * (setup.T s : ℝ) * prevSnapshotGap := by
            calc
              Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                  if hn : n ∈ Finset.Icc 1 (setup.T s) then
                    (∫ ω,
                      setup.VOn
                        ⟨setup.paperInnerIterAt s
                          ⟨n, Finset.mem_Icc.mp hn⟩ ω,
                          setup.paperInnerIterAt_mem s
                            ⟨n, Finset.mem_Icc.mp hn⟩ ω⟩ xStar ∂setup.P) +
                      coeff *
                        (∫ ω,
                          setup.PsiOn
                              ⟨setup.paperInnerIterAt s
                                ⟨n, Finset.mem_Icc.mp hn⟩ ω,
                                setup.paperInnerIterAt_mem s
                                  ⟨n, Finset.mem_Icc.mp hn⟩ ω⟩ -
                            setup.PsiOn xStar ∂setup.P) +
                      coeff * prevSnapshotGap
                  else 0)
                  =
                (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                  if hn : n ∈ Finset.Icc 1 (setup.T s) then
                    ∫ ω,
                      setup.VOn
                        ⟨setup.paperInnerIterAt s
                          ⟨n, Finset.mem_Icc.mp hn⟩ ω,
                          setup.paperInnerIterAt_mem s
                            ⟨n, Finset.mem_Icc.mp hn⟩ ω⟩ xStar ∂setup.P
                  else 0)) +
                (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                  if hn : n ∈ Finset.Icc 1 (setup.T s) then
                    coeff *
                      (∫ ω,
                        setup.PsiOn
                            ⟨setup.paperInnerIterAt s
                              ⟨n, Finset.mem_Icc.mp hn⟩ ω,
                              setup.paperInnerIterAt_mem s
                                ⟨n, Finset.mem_Icc.mp hn⟩ ω⟩ -
                          setup.PsiOn xStar ∂setup.P)
                  else 0)) +
                Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                  if _hn : n ∈ Finset.Icc 1 (setup.T s) then
                    coeff * prevSnapshotGap
                  else 0) := by
                    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl ?_
                    intro n hnmem
                    simp [hnmem]
              _ = currVSum + coeff * currGapSum +
                    coeff * (setup.T s : ℝ) * prevSnapshotGap := by
                    have hgapCoeff :
                        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                            if hn : n ∈ Finset.Icc 1 (setup.T s) then
                              coeff *
                                (∫ ω,
                                  setup.PsiOn
                                      ⟨setup.paperInnerIterAt s
                                        ⟨n, Finset.mem_Icc.mp hn⟩ ω,
                                        setup.paperInnerIterAt_mem s
                                          ⟨n, Finset.mem_Icc.mp hn⟩ ω⟩ -
                                    setup.PsiOn xStar ∂setup.P)
                            else 0) =
                          coeff *
                            Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                              if hn : n ∈ Finset.Icc 1 (setup.T s) then
                                ∫ ω,
                                  setup.PsiOn
                                      ⟨setup.paperInnerIterAt s
                                        ⟨n, Finset.mem_Icc.mp hn⟩ ω,
                                        setup.paperInnerIterAt_mem s
                                          ⟨n, Finset.mem_Icc.mp hn⟩ ω⟩ -
                                    setup.PsiOn xStar ∂setup.P
                              else 0) := by
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro n hnmem
                      simp [hnmem]
                    have hconst :
                        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                            if _hn : n ∈ Finset.Icc 1 (setup.T s) then
                              coeff * prevSnapshotGap
                            else 0) =
                          (setup.T s : ℝ) * (coeff * prevSnapshotGap) := by
                            calc
                              Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
                                  if _hn : n ∈ Finset.Icc 1 (setup.T s) then
                                    coeff * prevSnapshotGap
                                  else 0)
                                  =
                                Finset.sum (Finset.Icc 1 (setup.T s))
                                  (fun _ : ℕ => coeff * prevSnapshotGap) := by
                                    refine Finset.sum_congr rfl ?_
                                    intro n hnmem
                                    simp [hnmem]
                              _ = (setup.T s : ℝ) * (coeff * prevSnapshotGap) := by
                                    rw [Finset.sum_const]
                                    simp [Nat.card_Icc, hT_pos, nsmul_eq_mul]
                    rw [hgapCoeff]
                    rw [hconst]
                    simp only [currVSum, currGapSum]
                    ring
  have h := hraw
  dsimp only at h
  rw [hleft, hright] at h
  simpa [coeff, nextGapSum, nextVSum, currVSum, currGapSum, prevSnapshotGap,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Reindex the fixed-epoch objective-gap sums to the theorem's endpoint and
middle-window quantities.

This packages the Algorithm 5.6 identities `x_1 = x^{s-1}` and
`x_{T_s+1} = x^s` used in Lan Theorem 5.6 proof step 1. Reuse audit: checked
the local endpoint bridges `fixed_epoch_first_inner_eq_prev_epoch`,
`paperInnerIterInWindow_eq_at`, `paperNextInnerIterAt_eq_internalCarrier`, and
`xEpochIter_eq_paper_last`; the remaining work is the paper-specific Icc
off-by-one reindexing. -/
private theorem fixed_epoch_gap_sums_reindex
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) (hs_pos : 1 ≤ s) :
    let nextGapSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)
    let currGapSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω,
                  setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)
    let middleGap : ℝ :=
      Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        ∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
    let terminalGap : ℝ :=
      ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
    let prevGap : ℝ :=
      ∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P
    nextGapSum = middleGap + terminalGap ∧
      currGapSum = prevGap + middleGap := by
  classical
  have hT_pos : 1 ≤ setup.T s := by
    have hs0 : s ≠ 0 := by omega
    simp [VarianceReducedMirrorDescentSetup.T, hs0]
    exact Nat.succ_le_of_lt
      (Nat.mul_pos (by norm_num : 0 < 7) (pow_pos (by norm_num : (0 : ℕ) < 2) _))
  let A : ℕ → ℝ :=
    fun k => ∫ ω, setup.Psi (setup.internalInnerIter s k ω) - setup.PsiOn xStar ∂setup.P
  have hnext_norm :
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)) =
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n => A n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp only [hn, ↓reduceDIte]
    let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
    have hiter :
        setup.paperNextInnerIterAt s t = setup.internalInnerIter s n := by
      simpa [t] using setup.paperNextInnerIterAt_eq_internalCarrier s t
    change
      (∫ ω,
          setup.PsiOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ -
            setup.PsiOn xStar ∂setup.P) =
        (∫ ω, setup.Psi (setup.internalInnerIter s n ω) - setup.PsiOn xStar ∂setup.P)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hω := congrFun hiter ω
    simp [VarianceReducedMirrorDescentSetup.PsiOn_coe, hω]
  have hcurr_norm :
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω,
                  setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)) =
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n => A (n - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp only [hn, ↓reduceDIte]
    let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
    have hiter :
        setup.paperInnerIterAt s t = setup.internalInnerIter s (n - 1) := by
      simpa [t] using setup.paperEpoch_inner_eq_internalCarrier s t
    change
      (∫ ω,
          setup.PsiOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ -
            setup.PsiOn xStar ∂setup.P) =
        (∫ ω,
          setup.Psi (setup.internalInnerIter s (n - 1) ω) -
            setup.PsiOn xStar ∂setup.P)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hω := congrFun hiter ω
    simp [VarianceReducedMirrorDescentSetup.PsiOn_coe, hω]
  have hmiddle_norm :
      (Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        ∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)) =
        Finset.sum (Finset.Icc 2 (setup.T s)) (fun n => A (n - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    let t : setup.InnerStep s := ⟨n, ⟨by omega, hn_bounds.2⟩⟩
    have hwindow :
        setup.paperInnerIterInWindow s n = setup.paperInnerIterAt s t := by
      simpa [t] using setup.paperInnerIterInWindow_eq_at s t
    have hiter :
        setup.paperInnerIterAt s t = setup.internalInnerIter s (n - 1) := by
      simpa [t] using setup.paperEpoch_inner_eq_internalCarrier s t
    change
      (∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s n ω) -
            setup.PsiOn xStar ∂setup.P) =
        (∫ ω,
          setup.Psi (setup.internalInnerIter s (n - 1) ω) -
            setup.PsiOn xStar ∂setup.P)
    rw [hwindow, hiter]
  have hterminal :
      (∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P) =
        A (setup.T s) := by
    rw [setup.xEpochIter_eq_paper_last s]
  have hprev :
      (∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P) =
        A 0 := by
    let t : setup.InnerStep s := ⟨1, ⟨le_rfl, hT_pos⟩⟩
    have hfirst :
        setup.paperInnerIterAt s t = setup.xEpochIter (s - 1) :=
      fixed_epoch_first_inner_eq_prev_epoch setup s hs_pos t rfl
    have hcarrier :
        setup.internalInnerIter s 0 = setup.paperInnerIterAt s t := by
      simpa [t] using (setup.paperEpoch_inner_eq_internalCarrier s t).symm
    change
      (∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P) =
        (∫ ω, setup.Psi (setup.internalInnerIter s 0 ω) - setup.PsiOn xStar ∂setup.P)
    rw [← hfirst, ← hcarrier]
  change
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)) =
          (Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
            ∫ ω,
              setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)) +
            (∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P) ∧
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.PsiOn
                ⟨setup.paperInnerIterAt s t ω,
                  setup.paperInnerIterAt_mem s t ω⟩ -
              setup.PsiOn xStar ∂setup.P
        else 0)) =
          (∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P) +
            (Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
              ∫ ω,
                setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P))
  constructor
  · rw [hnext_norm, hmiddle_norm, hterminal]
    exact sum_Icc_self_split_tail_top A hT_pos
  · rw [hcurr_norm, hmiddle_norm, hprev]
    exact sum_Icc_pred_split_first_tail A hT_pos

/-- Telescope the fixed-epoch Bregman sums to the previous and terminal epoch
endpoints.

This is Lan Theorem 5.6 proof step 1 after rewriting `V(x_t, x*)` and
`V(x_{t+1}, x*)` through the zero-based internal carrier. Reuse audit: selected
the already-proved local `fixed_epoch_sum_Icc_pred_telescope`, which itself uses
SOptLib `sum_Icc_sub_succ`; this helper adds the VRMD endpoint coercions via
`paperEpoch_inner_eq_internalCarrier`, `paperNextInnerIterAt_eq_internalCarrier`,
`xEpochIter_eq_paper_last`, and `VOn_coe`. -/
private theorem fixed_epoch_v_sums_telescope
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) (hs_pos : 1 ≤ s) :
    let nextVSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)
    let currVSum : ℝ :=
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)
    let terminalV : ℝ :=
      ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
    let prevV : ℝ :=
      ∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P
    currVSum - nextVSum = prevV - terminalV := by
  classical
  have hT_pos : 1 ≤ setup.T s := by
    have hs0 : s ≠ 0 := by omega
    simp [VarianceReducedMirrorDescentSetup.T, hs0]
    exact Nat.succ_le_of_lt
      (Nat.mul_pos (by norm_num : 0 < 7) (pow_pos (by norm_num : (0 : ℕ) < 2) _))
  let A : ℕ → ℝ :=
    fun k => ∫ ω, setup.V (setup.internalInnerIter s k ω) xStar.1 ∂setup.P
  have hcurr :
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)) =
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n => A (n - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp only [hn, ↓reduceDIte]
    let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
    have hiter :
        setup.paperInnerIterAt s t = setup.internalInnerIter s (n - 1) := by
      simpa [t] using setup.paperEpoch_inner_eq_internalCarrier s t
    change
      (∫ ω, setup.VOn
        ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩
          xStar ∂setup.P) =
        (∫ ω, setup.V (setup.internalInnerIter s (n - 1) ω) xStar.1 ∂setup.P)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hω := congrFun hiter ω
    simp [VarianceReducedMirrorDescentSetup.VOn_coe, hω]
  have hnext :
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)) =
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n => A n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp only [hn, ↓reduceDIte]
    let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
    have hiter :
        setup.paperNextInnerIterAt s t = setup.internalInnerIter s n := by
      simpa [t] using setup.paperNextInnerIterAt_eq_internalCarrier s t
    change
      (∫ ω, setup.VOn
        ⟨setup.paperNextInnerIterAt s t ω, setup.paperNextInnerIterAt_mem s t ω⟩
          xStar ∂setup.P) =
        (∫ ω, setup.V (setup.internalInnerIter s n ω) xStar.1 ∂setup.P)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hω := congrFun hiter ω
    simp [VarianceReducedMirrorDescentSetup.VOn_coe, hω]
  have htel := fixed_epoch_sum_Icc_pred_telescope A hT_pos
  have hterminal :
      A (setup.T s) =
        (∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P) := by
    rw [setup.xEpochIter_eq_paper_last s]
  have hprev :
      A 0 =
        (∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P) := by
    let t : setup.InnerStep s := ⟨1, ⟨le_rfl, hT_pos⟩⟩
    have hfirst :
        setup.paperInnerIterAt s t = setup.xEpochIter (s - 1) :=
      fixed_epoch_first_inner_eq_prev_epoch setup s hs_pos t rfl
    have hcarrier :
        setup.internalInnerIter s 0 = setup.paperInnerIterAt s t := by
      simpa [t] using (setup.paperEpoch_inner_eq_internalCarrier s t).symm
    change
      (∫ ω, setup.V (setup.internalInnerIter s 0 ω) xStar.1 ∂setup.P) =
        (∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P)
    rw [hcarrier, hfirst]
  change
      (Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0) -
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
        if hn : n ∈ Finset.Icc 1 (setup.T s) then
          let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
          ∫ ω,
            setup.VOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
        else 0)) =
          (∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P) -
          (∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P)
  rw [hcurr, hnext]
  calc
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n => A (n - 1)) -
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n => A n) =
      A 0 - A (setup.T s) := htel
    _ =
        (∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P) -
          (∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P) := by
      rw [hprev, hterminal]

/-- Normalize the raw fixed-epoch sum into endpoint, middle-window, and
snapshot terms.

This is the remaining finite reindexing/telescope core of Lan Theorem 5.6
proof step 1 after `fixed_epoch_summed_step_raw_indexed`: split Bochner
integrals, use `paperInnerIterInWindow_eq_at`,
`paperNextInnerIterAt_eq_internalCarrier`, `xEpochIter_eq_paper_last`, and
telescope the Bregman differences.  Reuse audit: verified the signatures of
`sum_Icc_sub_succ`, `outputWindow_sum_sub_succ`,
`MeasureTheory.integral_finset_sum`, and `Finset.sum_Icc_succ_top`; they are
the generic atoms, but this local bridge still has to align the VRMD endpoints
and subtype proofs. -/
private theorem fixed_epoch_summed_step_normalized_from_raw_indexed
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) (hs_pos : 1 ≤ s)
    (hraw :
      let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
      Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.η *
                    (setup.PsiOn
                        ⟨setup.paperNextInnerIterAt s t ω,
                          setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
                  setup.VOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
          else 0) ≤
        Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
          if hn : n ∈ Finset.Icc 1 (setup.T s) then
            let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
            ∫ ω,
                setup.VOn
                  ⟨setup.paperInnerIterAt s t ω,
                    setup.paperInnerIterAt_mem s t ω⟩ xStar +
                  coeff *
                    ((setup.PsiOn
                          ⟨setup.paperInnerIterAt s t ω,
                            setup.paperInnerIterAt_mem s t ω⟩ -
                        setup.PsiOn xStar) +
                      (setup.PsiOn
                          ⟨setup.snapshotIter (s - 1) ω,
                            setup.snapshotIter_mem (s - 1) ω⟩ -
                        setup.PsiOn xStar)) ∂setup.P
          else 0)) :
    let middleGap : ℝ :=
      Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        ∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
    let terminalGap : ℝ :=
      ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
    let terminalV : ℝ :=
      ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
    let prevV : ℝ :=
      ∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P
    let prevGap : ℝ :=
      ∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P
    let prevSnapshotGap : ℝ :=
      ∫ ω,
        setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar ∂setup.P
    let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
    setup.η * terminalGap + setup.η * middleGap + terminalV ≤
      prevV + coeff * prevGap + coeff * middleGap +
        coeff * (setup.T s : ℝ) * prevSnapshotGap := by
  have hT_pos : 1 ≤ setup.T s := by
    simp [VarianceReducedMirrorDescentSetup.T]
    have hs_ne : s ≠ 0 := by omega
    simp [hs_ne]
    exact Nat.succ_le_of_lt
      (Nat.mul_pos (by norm_num) (pow_pos (by norm_num : 0 < 2) (s - 1)))
  let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
  let nextGapSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.PsiOn
              ⟨setup.paperNextInnerIterAt s t ω,
                setup.paperNextInnerIterAt_mem s t ω⟩ -
            setup.PsiOn xStar ∂setup.P
      else 0)
  let nextVSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.VOn
            ⟨setup.paperNextInnerIterAt s t ω,
              setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P
      else 0)
  let currVSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.VOn
            ⟨setup.paperInnerIterAt s t ω,
              setup.paperInnerIterAt_mem s t ω⟩ xStar ∂setup.P
      else 0)
  let currGapSum : ℝ :=
    Finset.sum (Finset.Icc 1 (setup.T s)) (fun n =>
      if hn : n ∈ Finset.Icc 1 (setup.T s) then
        let t : setup.InnerStep s := ⟨n, Finset.mem_Icc.mp hn⟩
        ∫ ω,
          setup.PsiOn
              ⟨setup.paperInnerIterAt s t ω,
                setup.paperInnerIterAt_mem s t ω⟩ -
            setup.PsiOn xStar ∂setup.P
      else 0)
  let middleGap : ℝ :=
    Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
      ∫ ω,
        setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
  let terminalGap : ℝ :=
    ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
  let terminalV : ℝ :=
    ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
  let prevV : ℝ :=
    ∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P
  let prevGap : ℝ :=
    ∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P
  let prevSnapshotGap : ℝ :=
    ∫ ω,
      setup.PsiOn
          ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
        setup.PsiOn xStar ∂setup.P
  have hsep :
      setup.η * nextGapSum + nextVSum ≤
        currVSum + coeff * currGapSum +
          coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    simpa [coeff, nextGapSum, nextVSum, currVSum, currGapSum, prevSnapshotGap] using
      fixed_epoch_raw_integral_sums_split setup xStar s hs_pos hraw
  have hgap := fixed_epoch_gap_sums_reindex setup xStar s hs_pos
  have hnext : nextGapSum = middleGap + terminalGap := by
    simpa [nextGapSum, currGapSum, middleGap, terminalGap, prevGap] using hgap.1
  have hcurr : currGapSum = prevGap + middleGap := by
    simpa [nextGapSum, currGapSum, middleGap, terminalGap, prevGap] using hgap.2
  have hv : currVSum - nextVSum = prevV - terminalV := by
    simpa [nextVSum, currVSum, terminalV, prevV] using
      fixed_epoch_v_sums_telescope setup xStar s hs_pos
  rw [hnext, hcurr] at hsep
  have hineq :
      setup.η * terminalGap + setup.η * middleGap + terminalV ≤
        prevV + coeff * prevGap + coeff * middleGap +
          coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    nlinarith [hsep, hv]
  simpa [middleGap, terminalGap, terminalV, prevV, prevGap, prevSnapshotGap, coeff,
    add_comm, add_left_comm, add_assoc] using hineq

/-- Normalized fixed-epoch sum before the first-current-gap absorption.

This is the finite reindexing/telescope core of Lan Theorem 5.6 proof step 1:
sum Lemma 5.14 over `t = 1, ..., T_s`, rewrite next/current iterates through
the internal carrier, split the objective-gap sums into endpoint and
`2..T_s` window pieces, make the repeated snapshot term constant, and telescope
the Bregman differences.  Reuse audit: checked
`summed_one_step_gap_bound_of_telescope`, `outputWindow_sum_sub_succ`,
`sum_Icc_sub_succ`, and `MeasureTheory.integral_finset_sum`; they are the right
generic atoms but do not directly cover this file's `InnerStep` subtype plus
VRMD endpoint identifications, so this helper isolates that specialization. -/
private theorem fixed_epoch_summed_step_normalized
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (hstep :
      ∀ s, s ∈ setup.outputEpochs S → ∀ t : setup.InnerStep s,
        ∫ ω,
            setup.η *
                (setup.PsiOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
              setup.VOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P ≤
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
              4 * setup.LQ * setup.η ^ 2 *
                ((setup.PsiOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ -
                    setup.PsiOn xStar) +
                  (setup.PsiOn
                      ⟨setup.snapshotIter (s - 1) ω,
                        setup.snapshotIter_mem (s - 1) ω⟩ -
                    setup.PsiOn xStar)) ∂setup.P)
    (s : ℕ) (hs : s ∈ setup.outputEpochs S) :
    let middleGap : ℝ :=
      Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        ∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
    let terminalGap : ℝ :=
      ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
    let terminalV : ℝ :=
      ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
    let prevV : ℝ :=
      ∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P
    let prevGap : ℝ :=
      ∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P
    let prevSnapshotGap : ℝ :=
      ∫ ω,
        setup.PsiOn
            ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
          setup.PsiOn xStar ∂setup.P
    let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
    setup.η * terminalGap + setup.η * middleGap + terminalV ≤
      prevV + coeff * prevGap + coeff * middleGap +
        coeff * (setup.T s : ℝ) * prevSnapshotGap := by
  classical
  have hs_pos : 1 ≤ s := by
    have hmem : s ∈ Finset.Icc 1 S.1 := by
      simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
    exact (Finset.mem_Icc.mp hmem).1
  have hraw := fixed_epoch_summed_step_raw_indexed setup S xStar hstep s hs
  simpa using
    fixed_epoch_summed_step_normalized_from_raw_indexed setup xStar s hs_pos hraw

/-- Summed fixed-epoch one-step recursion before the snapshot Jensen substitution.

This aligns with Lan Theorem 5.6 proof step 1 after summing Lemma 5.14 over
`t = 1, ..., T_s`: the Bregman terms telescope to the epoch endpoints, the
current-gap sum is split into the first inner point and the window `t = 2..T_s`,
and `4 L_Q γ ≤ 1` absorbs the first current gap into `γ(Ψ(x^{s-1})-Ψ*)`.
Reuse audit: checked `summed_one_step_gap_bound_of_telescope`,
`outputWindow_sum_sub_succ`, `sum_Icc_sub_succ`, and
`MeasureTheory.integral_finset_sum`; they provide generic finite-window
telescoping atoms, but this bridge packages the VRMD `InnerStep` subtype and
the paper endpoint identifications. -/
private theorem fixed_epoch_summed_step_core
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hstep :
      ∀ s, s ∈ setup.outputEpochs S → ∀ t : setup.InnerStep s,
        ∫ ω,
            setup.η *
                (setup.PsiOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
              setup.VOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P ≤
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
              4 * setup.LQ * setup.η ^ 2 *
                ((setup.PsiOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ -
                    setup.PsiOn xStar) +
                  (setup.PsiOn
                      ⟨setup.snapshotIter (s - 1) ω,
                        setup.snapshotIter_mem (s - 1) ω⟩ -
                    setup.PsiOn xStar)) ∂setup.P)
    (s : ℕ) (hs : s ∈ setup.outputEpochs S) :
    let middleGap : ℝ :=
      Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        ∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
    setup.η *
          ∫ ω,
            setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P +
        setup.η * middleGap +
        ∫ ω,
          setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P ≤
      ∫ ω,
          setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P +
        setup.η *
          ∫ ω,
            setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P +
        4 * setup.LQ * setup.η ^ 2 * middleGap +
        4 * setup.LQ * setup.η ^ 2 * (setup.T s : ℝ) *
          ∫ ω,
            setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω,
                  setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar ∂setup.P := by
  classical
  let middleGap : ℝ :=
    Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
      ∫ ω,
        setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
  let terminalGap : ℝ :=
    ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
  let terminalV : ℝ :=
    ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
  let prevV : ℝ :=
    ∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P
  let prevGap : ℝ :=
    ∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P
  let prevSnapshotGap : ℝ :=
    ∫ ω,
      setup.PsiOn
          ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
        setup.PsiOn xStar ∂setup.P
  let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
  have hnormalized :
      setup.η * terminalGap + setup.η * middleGap + terminalV ≤
        prevV + coeff * prevGap + coeff * middleGap +
          coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    simpa [middleGap, terminalGap, terminalV, prevV, prevGap, prevSnapshotGap, coeff]
      using fixed_epoch_summed_step_normalized setup S xStar hstep s hs
  have hprevGap_nonneg : 0 ≤ prevGap := by
    simpa [prevGap] using fixed_epoch_prev_gap_nonneg setup xStar h_opt s
  have habsorb : coeff * prevGap ≤ setup.η * prevGap := by
    simpa [coeff] using fixed_epoch_absorb_first_gap setup hprevGap_nonneg
  have htarget :
      setup.η * terminalGap + setup.η * middleGap + terminalV ≤
        prevV + setup.η * prevGap + coeff * middleGap +
          coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    nlinarith [hnormalized, habsorb]
  simpa [middleGap, terminalGap, terminalV, prevV, prevGap, prevSnapshotGap, coeff,
    mul_assoc, mul_left_comm, mul_comm] using htarget

/-- Pointwise Jensen bridge for one epoch snapshot.

This aligns with Lan Theorem 5.6 proof step 1: after Corollary 5.8 rewrites
`θ_t = 1`, the snapshot is the uniform average of the inner iterates over
`t = 2..T_s`, so convexity of `Ψ` bounds the snapshot gap by the unnormalized
sum of window gaps. Reuse audit: selected
`convexOn_weighted_average_le_weighted_sum` and
`weighted_average_sub_baseline_le_weighted_gap`; they provide the generic
Jensen and baseline algebra, while this helper specializes the paper snapshot
formula `snapshotIter_eq_paper_window`. -/
private theorem fixed_epoch_snapshot_jensen_pointwise
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) (hs : 1 ≤ s) (ω : Ω) :
    ((setup.T s : ℝ) - 1) *
        (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
          setup.PsiOn xStar) ≤
      Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar) := by
  classical
  let I : Finset ℕ := Finset.Icc 2 (setup.T s)
  have hT_two : 2 ≤ setup.T s := by
    have hs0 : s ≠ 0 := by omega
    simp [VarianceReducedMirrorDescentSetup.T, hs0]
    have hpow_pos : 0 < 2 ^ (s - 1) :=
      pow_pos (by norm_num : (0 : ℕ) < 2) (s - 1)
    omega
  have hinner_mem (t : ℕ) (ht : t ∈ I) :
      setup.paperInnerIterInWindow s t ω ∈ setup.X := by
    rcases Finset.mem_Icc.mp (by simpa [I] using ht) with ⟨ht2, htT⟩
    let τ : setup.InnerStep s := ⟨t, ⟨by omega, htT⟩⟩
    have hwindow :
        setup.paperInnerIterInWindow s t = setup.paperInnerIterAt s τ := by
      simpa [τ] using setup.paperInnerIterInWindow_eq_at s τ
    rw [hwindow]
    exact setup.paperInnerIterAt_mem s τ ω
  let W : ℝ := Finset.sum I setup.θ
  have hW_eq_T : W = (setup.T s : ℝ) - 1 := by
    have hT_one : 1 ≤ setup.T s := by omega
    calc
      W = ((setup.T s - 1 : ℕ) : ℝ) := by
        simp [W, I, setup.theta_corollary_5_8, Nat.card_Icc, nsmul_eq_mul]
      _ = (setup.T s : ℝ) - 1 := by
        have hcast : ((setup.T s - 1 : ℕ) : ℝ) =
            (setup.T s : ℝ) - ((1 : ℕ) : ℝ) :=
          Nat.cast_sub hT_one
        norm_num at hcast
        exact hcast
  have hW_pos : 0 < W := by
    rw [hW_eq_T]
    exact sub_pos.mpr (by exact_mod_cast hT_two)
  have hJ_value :
      setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ ≤
        W⁻¹ *
          Finset.sum I
            (fun t => setup.θ t * setup.Psi (setup.paperInnerIterInWindow s t ω)) := by
    have hsnap := congrFun (setup.snapshotIter_eq_paper_window s hs) ω
    have hJ :=
      _root_.convexOn_weighted_average_le_weighted_sum
        (hf := setup.Psi_convexOn)
        (s := I)
        (γ := setup.θ)
        (p := fun t => setup.paperInnerIterInWindow s t ω)
        (xbar := setup.snapshotIter s ω)
        (W := W)
        (hγ_nonneg := by
          intro t _ht
          rw [setup.theta_corollary_5_8 t]
          norm_num)
        (hp_mem := hinner_mem)
        (hW_pos := hW_pos)
        (hW_eq := by rfl)
        (hxbar := by
          simpa [I, W] using hsnap)
    simpa [VarianceReducedMirrorDescentSetup.PsiOn_coe] using hJ
  have hgap :
      setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
          setup.PsiOn xStar ≤
        W⁻¹ *
          Finset.sum I
            (fun t =>
              setup.θ t *
                (setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar)) := by
    exact
      weighted_average_sub_baseline_le_weighted_gap
        (s := I)
        (γ := setup.θ)
        (F := fun t => setup.Psi (setup.paperInnerIterInWindow s t ω))
        (value := setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩)
        (baseline := setup.PsiOn xStar)
        (W := W)
        hW_pos
        (by rfl)
        hJ_value
  have hscaled :
      W *
          (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar) ≤
        Finset.sum I
          (fun t =>
            setup.θ t *
              (setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar)) := by
    calc
      W *
          (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar)
          ≤ W *
              (W⁻¹ *
                Finset.sum I
                  (fun t =>
                    setup.θ t *
                      (setup.Psi (setup.paperInnerIterInWindow s t ω) -
                        setup.PsiOn xStar))) :=
            mul_le_mul_of_nonneg_left hgap (le_of_lt hW_pos)
      _ =
          Finset.sum I
            (fun t =>
              setup.θ t *
                (setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar)) := by
            field_simp [ne_of_gt hW_pos]
  calc
    ((setup.T s : ℝ) - 1) *
        (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
          setup.PsiOn xStar)
        =
      W *
        (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
          setup.PsiOn xStar) := by
        rw [hW_eq_T]
    _ ≤
        Finset.sum I
          (fun t =>
            setup.θ t *
              (setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar)) :=
        hscaled
    _ =
        Finset.sum I
          (fun t => setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar) := by
        refine Finset.sum_congr rfl ?_
        intro t _ht
        rw [setup.theta_corollary_5_8 t]
        ring

/-- Snapshot Jensen bridge for a single epoch at expectation level.

This aligns with Lan Theorem 5.6 proof step 1 and the epoch-averaged bound:
`\tilde x^s` is the uniform average of the inner iterates `x_t`, `t=2..T_s`,
because Corollary 5.8 has `θ_t = 1`; convexity of `Ψ` gives the window-average
gap bound after subtracting the same baseline and integrating. Reuse audit:
checked `convexOn_weighted_average_le_weighted_sum`,
`Convex.normalized_weighted_sum_mem`, and
`weighted_average_sub_baseline_le_weighted_gap`; the generic Jensen atoms do not
include this file's `snapshotIter_eq_paper_window` and finite-prefix
integrability bridges, so this helper isolates that specialization. -/
private theorem fixed_epoch_snapshot_jensen_integral
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) (hs : 1 ≤ s) :
    ((setup.T s : ℝ) - 1) *
        ∫ ω,
          setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar ∂setup.P ≤
      Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
        ∫ ω,
          setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P) := by
  classical
  let I : Finset ℕ := Finset.Icc 2 (setup.T s)
  have hsnap_int :
      Integrable
        (fun ω =>
          setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar) setup.P := by
    simpa using
      snapshotIter_observable_integrable setup s
        (fun x => setup.PsiOn x - setup.PsiOn xStar)
  have hleft_int :
      Integrable
        (fun ω =>
          ((setup.T s : ℝ) - 1) *
            (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
              setup.PsiOn xStar)) setup.P := by
    simpa [smul_eq_mul] using hsnap_int.const_mul ((setup.T s : ℝ) - 1)
  have hterm_int (t : ℕ) (ht : t ∈ I) :
      Integrable
        (fun ω => setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar)
        setup.P := by
    rcases Finset.mem_Icc.mp (by simpa [I] using ht) with ⟨ht2, htT⟩
    let τ : setup.InnerStep s := ⟨t, ⟨by omega, htT⟩⟩
    have hwindow :
        setup.paperInnerIterInWindow s t = setup.paperInnerIterAt s τ := by
      simpa [τ] using setup.paperInnerIterInWindow_eq_at s τ
    rw [hwindow]
    simpa [VarianceReducedMirrorDescentSetup.PsiOn_coe] using
      paperInnerIter_observable_integrable setup s τ
        (fun x => setup.PsiOn x - setup.PsiOn xStar)
  have hright_int :
      Integrable
        (fun ω =>
          Finset.sum I
            (fun t => setup.Psi (setup.paperInnerIterInWindow s t ω) -
              setup.PsiOn xStar)) setup.P := by
    exact integrable_finset_sum I hterm_int
  have hpoint :
      (fun ω =>
        ((setup.T s : ℝ) - 1) *
          (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar)) ≤ᵐ[setup.P]
      (fun ω =>
        Finset.sum I
          (fun t => setup.Psi (setup.paperInnerIterInWindow s t ω) -
            setup.PsiOn xStar)) := by
    exact Filter.Eventually.of_forall (fun ω => by
      simpa [I] using fixed_epoch_snapshot_jensen_pointwise setup xStar s hs ω)
  have hmono := MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hleft_eq :
      (∫ ω,
        ((setup.T s : ℝ) - 1) *
          (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar) ∂setup.P) =
        ((setup.T s : ℝ) - 1) *
          ∫ ω,
            setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
              setup.PsiOn xStar ∂setup.P := by
    rw [MeasureTheory.integral_const_mul]
  have hright_eq :
      (∫ ω,
        Finset.sum I
          (fun t => setup.Psi (setup.paperInnerIterInWindow s t ω) -
            setup.PsiOn xStar) ∂setup.P) =
        Finset.sum I
          (fun t =>
            ∫ ω,
              setup.Psi (setup.paperInnerIterInWindow s t ω) -
                setup.PsiOn xStar ∂setup.P) := by
    rw [MeasureTheory.integral_finset_sum]
    intro t ht
    exact hterm_int t ht
  rw [hleft_eq, hright_eq] at hmono
  simpa [I] using hmono

/-- Fixed-epoch recursion obtained by summing unconditional Lemma 5.14.

This aligns with Lan Theorem 5.6 proof step 1: sum the one-step recursion over
`t = 1, ..., T_s`, telescope the Bregman terms inside the epoch, use the
snapshot Jensen relation for `\tilde x^s`, and absorb the first-current-iterate
gap with `4 L_Q η ≤ 1`.  Reuse audit: selected the SOptLib candidates
`sum_Icc_sub_succ`, `summed_one_step_gap_bound_of_telescope`, and
`MeasureTheory.integral_finset_sum` as the right algebraic atoms; none directly
packages this paper's `InnerStep` subtype, endpoint bridges, and snapshot
coefficient, so this helper isolates that fixed-epoch assembly. -/
private theorem epoch_recursion_from_unconditional_steps
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hstep :
      ∀ s, s ∈ setup.outputEpochs S → ∀ t : setup.InnerStep s,
        ∫ ω,
            setup.η *
                (setup.PsiOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
              setup.VOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P ≤
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
              4 * setup.LQ * setup.η ^ 2 *
                ((setup.PsiOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ -
                    setup.PsiOn xStar) +
                  (setup.PsiOn
                      ⟨setup.snapshotIter (s - 1) ω,
                        setup.snapshotIter_mem (s - 1) ω⟩ -
                    setup.PsiOn xStar)) ∂setup.P)
    (s : ℕ) (hs : s ∈ setup.outputEpochs S) :
    setup.η *
          ∫ ω,
            setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P +
        setup.η * (1 - 4 * setup.LQ * setup.η) * ((setup.T s : ℝ) - 1) *
          ∫ ω,
            setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
              setup.PsiOn xStar ∂setup.P +
        ∫ ω,
          setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P ≤
      ∫ ω,
          setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P +
        setup.η *
          ∫ ω,
            setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P +
        4 * setup.LQ * setup.η ^ 2 * (setup.T s : ℝ) *
          ∫ ω,
            setup.PsiOn
                ⟨setup.snapshotIter (s - 1) ω,
                  setup.snapshotIter_mem (s - 1) ω⟩ -
              setup.PsiOn xStar ∂setup.P := by
  classical
  have hs_pos : 1 ≤ s := by
    have hmem : s ∈ Finset.Icc 1 S.1 := by
      simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
    exact (Finset.mem_Icc.mp hmem).1
  let middleGap : ℝ :=
    Finset.sum (Finset.Icc 2 (setup.T s)) (fun t =>
      ∫ ω,
        setup.Psi (setup.paperInnerIterInWindow s t ω) - setup.PsiOn xStar ∂setup.P)
  let terminalGap : ℝ :=
    ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
  let snapshotGap : ℝ :=
    ∫ ω,
      setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
        setup.PsiOn xStar ∂setup.P
  let terminalV : ℝ :=
    ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
  let prevV : ℝ :=
    ∫ ω, setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P
  let prevGap : ℝ :=
    ∫ ω, setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P
  let prevSnapshotGap : ℝ :=
    ∫ ω,
      setup.PsiOn
          ⟨setup.snapshotIter (s - 1) ω, setup.snapshotIter_mem (s - 1) ω⟩ -
        setup.PsiOn xStar ∂setup.P
  let coeff : ℝ := 4 * setup.LQ * setup.η ^ 2
  have hcore :
      setup.η * terminalGap + setup.η * middleGap + terminalV ≤
        prevV + setup.η * prevGap + coeff * middleGap +
          coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    simpa [middleGap, terminalGap, terminalV, prevV, prevGap, prevSnapshotGap, coeff]
      using fixed_epoch_summed_step_core setup S xStar h_opt hstep s hs
  have hJensen :
      ((setup.T s : ℝ) - 1) * snapshotGap ≤ middleGap := by
    simpa [middleGap, snapshotGap] using
      fixed_epoch_snapshot_jensen_integral setup xStar s hs_pos
  have hcoef_nonneg : 0 ≤ setup.η - coeff := by
    have hη_nonneg : 0 ≤ setup.η := le_of_lt setup.eta_pos
    have hmul := mul_le_mul_of_nonneg_right setup.four_LQ_eta_le_one hη_nonneg
    nlinarith [hmul]
  have hmiddle_sub :
      setup.η * terminalGap + (setup.η - coeff) * middleGap + terminalV ≤
        prevV + setup.η * prevGap + coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    nlinarith [hcore]
  have hsnap_scaled :
      (setup.η - coeff) * (((setup.T s : ℝ) - 1) * snapshotGap) ≤
        (setup.η - coeff) * middleGap := by
    exact mul_le_mul_of_nonneg_left hJensen hcoef_nonneg
  have htarget :
      setup.η * terminalGap + (setup.η - coeff) * (((setup.T s : ℝ) - 1) * snapshotGap) +
          terminalV ≤
        prevV + setup.η * prevGap + coeff * (setup.T s : ℝ) * prevSnapshotGap := by
    nlinarith [hmiddle_sub, hsnap_scaled]
  have htarget_final :
      setup.η * terminalGap +
          setup.η * (1 - 4 * setup.LQ * setup.η) * ((setup.T s : ℝ) - 1) *
            snapshotGap +
          terminalV ≤
        prevV + setup.η * prevGap +
          4 * setup.LQ * setup.η ^ 2 * (setup.T s : ℝ) * prevSnapshotGap := by
    nlinarith [htarget]
  simpa [terminalGap, snapshotGap, terminalV, prevV, prevGap, prevSnapshotGap,
    mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
    using htarget_final

/-- Commute the finite weighted snapshot-gap sum with expectation.

This aligns with Lan Theorem 5.6 proof step 2 before the scalar telescope:
the raw numerator is a finite weighted sum of expected snapshot gaps.  Reuse
audit: selected Mathlib `MeasureTheory.integral_finset_sum` and
`MeasureTheory.integral_const_mul`; SOptLib weighted-output lemmas normalize by
the output denominator, while this theorem needs the unnormalized numerator used
by the epoch telescope. -/
private theorem outer_weighted_snapshot_integral_sum_eq
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X}) :
    (∫ ω,
      Finset.sum (setup.outputEpochs S)
        (fun s =>
          setup.w s *
            (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
              setup.PsiOn xStar)) ∂setup.P) =
      Finset.sum (setup.outputEpochs S)
        (fun s =>
          setup.w s *
            ∫ ω,
              setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                setup.PsiOn xStar ∂setup.P) := by
  classical
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro s _hs
    rw [MeasureTheory.integral_const_mul]
  · intro s _hs
    have hsnap_int :
        Integrable
          (fun ω =>
            setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
              setup.PsiOn xStar) setup.P := by
      simpa using
        snapshotIter_observable_integrable setup s
          (fun x => setup.PsiOn x - setup.PsiOn xStar)
    simpa [smul_eq_mul] using hsnap_int.const_mul (setup.w s)

/-- Expected snapshot objective gaps are nonnegative by optimality of `xStar`.

This is the snapshot analogue of `fixed_epoch_prev_gap_nonneg` used in Lan
Theorem 5.6 proof step 2.  Reuse audit: checked the pre-searched telescope and
weighted-output candidates; none addresses this side condition, while Mathlib
`integral_nonneg` is exactly the needed positivity atom. -/
private theorem snapshot_gap_integral_nonneg
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (s : ℕ) :
    0 ≤
      ∫ ω,
        setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
          setup.PsiOn xStar ∂setup.P := by
  refine integral_nonneg ?_
  intro ω
  exact sub_nonneg.mpr
    (h_opt ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩)

/-- Expected endpoint Bregman terms are nonnegative.

This is the terminal-radius side condition in Lan Theorem 5.6 proof step 2.
Reuse audit: checked SOptLib telescope candidates and Mathlib finite-sum
nonnegativity; the needed bridge is direct `integral_nonneg` specialized through
the local feasibility theorem `fixed_epoch_xEpochIter_mem`. -/
private theorem xEpoch_v_integral_nonneg
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (s : ℕ) :
    0 ≤ ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P := by
  refine integral_nonneg ?_
  intro ω
  exact setup.V_nonneg (setup.xEpochIter s ω) xStar.1
    (fixed_epoch_xEpochIter_mem setup s ω) xStar.2

/-- Summed scalar epoch recursion after telescoping endpoint terms.

This is Lan Theorem 5.6 proof step 2 up to the remaining coefficient
comparison: sum the epoch recursion over `1..S`, telescope `A` and `B` with
`fixed_epoch_sum_Icc_pred_telescope`, split the predecessor sum with
`sum_Icc_pred_split_first_tail`, and drop the nonnegative terminal terms.  Reuse
audit: checked SOptLib `sum_Icc_sub_succ` plus the local wrappers
`fixed_epoch_sum_Icc_pred_telescope` and `sum_Icc_pred_split_first_tail`; no
existing lemma packages this exact two-sequence endpoint drop and shifted
snapshot predecessor coefficient. -/
private theorem outer_epoch_summed_recursion_bound
    (S : ℕ) (hS : 1 ≤ S)
    (η LQ : ℝ) (T : ℕ → ℕ) (A D B : ℕ → ℝ)
    (hη_pos : 0 < η)
    (hA_nonneg : ∀ s, 0 ≤ A s)
    (hB_nonneg : ∀ s, 0 ≤ B s)
    (hA0 : A 0 = D 0)
    (hEpoch :
      ∀ s ∈ Finset.Icc 1 S,
        η * A s + η * (1 - 4 * LQ * η) * ((T s : ℝ) - 1) * D s + B s ≤
          B (s - 1) + η * A (s - 1) +
            4 * LQ * η ^ 2 * (T s : ℝ) * D (s - 1)) :
    η *
        (Finset.sum (Finset.Icc 1 S)
            (fun s => (1 - 4 * LQ * η) * ((T s : ℝ) - 1) * D s) -
          Finset.sum (Finset.Icc 2 S)
            (fun s => (4 * LQ * η) * (T s : ℝ) * D (s - 1))) ≤
      η * (1 + (4 * LQ * η) * (T 1 : ℝ)) * D 0 + B 0 := by
  classical
  let β : ℝ := 4 * LQ * η
  let C : ℕ → ℝ := fun s => (1 - β) * ((T s : ℝ) - 1) * D s
  let R : ℕ → ℝ := fun s => β * (T s : ℝ) * D (s - 1)
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  change
    η *
        (Finset.sum (Finset.Icc 1 S) (fun s => C s) -
          Finset.sum (Finset.Icc 2 S) (fun s => R s)) ≤
      η * (1 + β * (T 1 : ℝ)) * D 0 + B 0
  have hsum_raw := Finset.sum_le_sum (fun s hs => hEpoch s hs)
  have hsum :
      η * Finset.sum (Finset.Icc 1 S) (fun s => A s) +
          η * Finset.sum (Finset.Icc 1 S) (fun s => C s) +
            Finset.sum (Finset.Icc 1 S) (fun s => B s) ≤
        Finset.sum (Finset.Icc 1 S) (fun s => B (s - 1)) +
          η * Finset.sum (Finset.Icc 1 S) (fun s => A (s - 1)) +
            η * Finset.sum (Finset.Icc 1 S) (fun s => R s) := by
    simpa [C, R, β, Finset.sum_add_distrib, Finset.mul_sum, pow_two,
      mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hsum_raw
  have htelA := fixed_epoch_sum_Icc_pred_telescope A hS
  have htelB := fixed_epoch_sum_Icc_pred_telescope B hS
  have hsplitR :
      Finset.sum (Finset.Icc 1 S) (fun s => R s) =
        R 1 + Finset.sum (Finset.Icc 2 S) (fun s => R s) := by
    have hsplit :=
      sum_Icc_pred_split_first_tail (fun k => R (k + 1)) hS
    have hleft :
        Finset.sum (Finset.Icc 1 S) (fun s => R s) =
          Finset.sum (Finset.Icc 1 S) (fun s => (fun k => R (k + 1)) (s - 1)) := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hidx : s - 1 + 1 = s := Nat.sub_add_cancel hs1
      simp [hidx]
    have hright :
        Finset.sum (Finset.Icc 2 S) (fun s => R s) =
          Finset.sum (Finset.Icc 2 S) (fun s => (fun k => R (k + 1)) (s - 1)) := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hs).1
      have hs1 : 1 ≤ s := by omega
      have hidx : s - 1 + 1 = s := Nat.sub_add_cancel hs1
      simp [hidx]
    calc
      Finset.sum (Finset.Icc 1 S) (fun s => R s)
          = Finset.sum (Finset.Icc 1 S)
              (fun s => (fun k => R (k + 1)) (s - 1)) := hleft
      _ = R 1 + Finset.sum (Finset.Icc 2 S)
              (fun s => (fun k => R (k + 1)) (s - 1)) := by
            simpa using hsplit
      _ = R 1 + Finset.sum (Finset.Icc 2 S) (fun s => R s) := by
            rw [← hright]
  have hR1 : R 1 = β * (T 1 : ℝ) * D 0 := by
    simp [R]
  have hterminal : 0 ≤ B S + η * A S :=
    add_nonneg (hB_nonneg S) (mul_nonneg hη_nonneg (hA_nonneg S))
  nlinarith [hsum, htelA, htelB, hsplitR, hR1, hA0, hterminal]

/-- Coefficient comparison for the Corollary 5.8 outer weights.

This is the scalar coefficient part of Lan Theorem 5.6 proof step 2.  The base
case uses the paper schedule fact `T_1 = 7`; middle coefficients use the
doubling recurrence twice, and the terminal coefficient uses nonnegativity of
the snapshot gap.  Reuse audit: checked the pre-searched finite telescope
candidates and Mathlib interval-sum APIs; none applies to this paper-specific
weight formula with the `s = 1` convention, so this local helper records the
remaining arithmetic obligation. -/
private theorem outer_epoch_weight_coeff_comparison
    (S : ℕ) (hS : 1 ≤ S)
    (η LQ : ℝ) (T : ℕ → ℕ) (w D : ℕ → ℝ)
    (hquarter : 4 * LQ * η = (1 / 4 : ℝ))
    (hT_one : T 1 = 7)
    (hTrec : ∀ s, 2 ≤ s → (T s : ℝ) = 2 * (T (s - 1) : ℝ))
    (hw_one : w 1 = (1 / 8 : ℝ))
    (hw :
      ∀ s, 2 ≤ s →
        w s =
          (1 - 4 * LQ * η) * ((T (s - 1) : ℝ) - 1) -
            4 * LQ * η * (T s : ℝ))
    (hD_nonneg : ∀ s, 0 ≤ D s) :
    Finset.sum (Finset.Icc 1 S) (fun s => w s * D s) ≤
      Finset.sum (Finset.Icc 1 S)
          (fun s => (1 - 4 * LQ * η) * ((T s : ℝ) - 1) * D s) -
        Finset.sum (Finset.Icc 2 S)
          (fun s => (4 * LQ * η) * (T s : ℝ) * D (s - 1)) := by
  classical
  let β : ℝ := 4 * LQ * η
  let c : ℝ := 1 - β
  have hβ : β = (1 / 4 : ℝ) := by
    simpa [β] using hquarter
  have hc : c = (3 / 4 : ℝ) := by
    dsimp [c]
    nlinarith
  change
    Finset.sum (Finset.Icc 1 S) (fun s => w s * D s) ≤
      Finset.sum (Finset.Icc 1 S) (fun s => c * ((T s : ℝ) - 1) * D s) -
        Finset.sum (Finset.Icc 2 S) (fun s => β * (T s : ℝ) * D (s - 1))
  have hw_closed : ∀ s, 1 ≤ s → w s = (1 / 8 : ℝ) * (T s : ℝ) - 3 / 4 := by
    intro s hs
    rcases lt_or_eq_of_le hs with hs_gt | rfl
    · have hs2 : 2 ≤ s := by omega
      have hrec := hTrec s hs2
      have hws := hw s hs2
      nlinarith [hβ, hc, hrec, hws]
    · have hT1 : (T 1 : ℝ) = 7 := by exact_mod_cast hT_one
      nlinarith [hw_one, hT1]
  have hmono_weight : ∀ s, 2 ≤ s → w (s - 1) ≤ w s := by
    intro s hs2
    have hs_prev : 1 ≤ s - 1 := by omega
    have hs_pos : 1 ≤ s := by omega
    have hrec := hTrec s hs2
    have hprev := hw_closed (s - 1) hs_prev
    have hcurr := hw_closed s hs_pos
    have hTprev_nonneg : 0 ≤ (T (s - 1) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    nlinarith
  have hmiddle :
      Finset.sum (Finset.Icc 2 S)
          (fun s => w (s - 1) * D (s - 1)) +
        Finset.sum (Finset.Icc 2 S)
          (fun s => β * (T s : ℝ) * D (s - 1)) ≤
        Finset.sum (Finset.Icc 2 S)
          (fun s => c * ((T (s - 1) : ℝ) - 1) * D (s - 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro s hs
    have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hs).1
    have hws := hw s hs2
    have hmono := hmono_weight s hs2
    have hcoeff :
        w (s - 1) + β * (T s : ℝ) ≤ c * ((T (s - 1) : ℝ) - 1) := by
      nlinarith [hws, hmono]
    calc
      w (s - 1) * D (s - 1) + β * (T s : ℝ) * D (s - 1)
          = (w (s - 1) + β * (T s : ℝ)) * D (s - 1) := by ring
      _ ≤ c * ((T (s - 1) : ℝ) - 1) * D (s - 1) :=
          mul_le_mul_of_nonneg_right hcoeff (hD_nonneg (s - 1))
  have hterminal_coeff : w S ≤ c * ((T S : ℝ) - 1) := by
    have hws := hw_closed S hS
    have hTS_nonneg : 0 ≤ (T S : ℝ) := by exact_mod_cast (Nat.zero_le _)
    nlinarith [hc, hws, hTS_nonneg]
  have hterminal :
      w S * D S ≤ c * ((T S : ℝ) - 1) * D S :=
    mul_le_mul_of_nonneg_right hterminal_coeff (hD_nonneg S)
  have hLsplit :=
    sum_Icc_self_split_tail_top (fun s => w s * D s) hS
  have hRsplit :=
    sum_Icc_self_split_tail_top (fun s => c * ((T s : ℝ) - 1) * D s) hS
  have hadd :
      Finset.sum (Finset.Icc 1 S) (fun s => w s * D s) +
        Finset.sum (Finset.Icc 2 S) (fun s => β * (T s : ℝ) * D (s - 1)) ≤
      Finset.sum (Finset.Icc 1 S) (fun s => c * ((T s : ℝ) - 1) * D s) := by
    nlinarith [hmiddle, hterminal, hLsplit, hRsplit]
  nlinarith

/-- Pure scalar epoch telescope for the Corollary 5.8 coefficient pattern.

This is the finite real-sequence algebra isolated from Lan Theorem 5.6 proof
step 2: sum the epoch recursion on `1..S`, telescope `A` and `B`, use the
Corollary 5.8 identities for `w_s` and `T_s`, and drop nonnegative terminal
terms.  Reuse audit: checked `sum_Icc_sub_succ`,
`fixed_epoch_sum_Icc_pred_telescope`, `sum_Icc_pred_split_first_tail`,
`sum_Icc_self_split_tail_top`, `integral_sum_telescope_bound_of_pointwise_lower_bound`,
and `summed_one_step_gap_bound_of_telescope`; they supply generic finite-window
atoms but do not package this shifted predecessor coefficient with Lan's
first-weight convention. -/
private theorem outer_epoch_scalar_algebra_core
    (S : ℕ) (hS : 1 ≤ S)
    (η LQ : ℝ) (T : ℕ → ℕ) (w A D B : ℕ → ℝ)
    (hη_pos : 0 < η)
    (hquarter : 4 * LQ * η = (1 / 4 : ℝ))
    (hT_one : T 1 = 7)
    (hTrec : ∀ s, 2 ≤ s → (T s : ℝ) = 2 * (T (s - 1) : ℝ))
    (hw_one : w 1 = (1 / 8 : ℝ))
    (hw :
      ∀ s, 2 ≤ s →
        w s =
          (1 - 4 * LQ * η) * ((T (s - 1) : ℝ) - 1) -
            4 * LQ * η * (T s : ℝ))
    (hA_nonneg : ∀ s, 0 ≤ A s)
    (hD_nonneg : ∀ s, 0 ≤ D s)
    (hB_nonneg : ∀ s, 0 ≤ B s)
    (hA0 : A 0 = D 0)
    (hEpoch :
      ∀ s ∈ Finset.Icc 1 S,
        η * A s + η * (1 - 4 * LQ * η) * ((T s : ℝ) - 1) * D s + B s ≤
          B (s - 1) + η * A (s - 1) +
            4 * LQ * η ^ 2 * (T s : ℝ) * D (s - 1)) :
    η * Finset.sum (Finset.Icc 1 S) (fun s => w s * D s) ≤
      η * (1 + 4 * LQ * η * (T 1 : ℝ)) * D 0 + B 0 := by
  classical
  let β : ℝ := 4 * LQ * η
  let c : ℝ := 1 - β
  have hβ : β = (1 / 4 : ℝ) := by
    simpa [β] using hquarter
  have hT1_real : (T 1 : ℝ) = 7 := by
    exact_mod_cast hT_one
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hrec_bound :
      η *
          (Finset.sum (Finset.Icc 1 S)
              (fun s => c * ((T s : ℝ) - 1) * D s) -
            Finset.sum (Finset.Icc 2 S)
              (fun s => β * (T s : ℝ) * D (s - 1))) ≤
        η * (1 + β * (T 1 : ℝ)) * D 0 + B 0 := by
    simpa [β, c, mul_assoc, mul_left_comm, mul_comm] using
      outer_epoch_summed_recursion_bound S hS η LQ T A D B hη_pos
        hA_nonneg hB_nonneg hA0 hEpoch
  have hcoeff :
      Finset.sum (Finset.Icc 1 S) (fun s => w s * D s) ≤
        Finset.sum (Finset.Icc 1 S)
            (fun s => c * ((T s : ℝ) - 1) * D s) -
          Finset.sum (Finset.Icc 2 S)
            (fun s => β * (T s : ℝ) * D (s - 1)) := by
    simpa [β, c, mul_assoc, mul_left_comm, mul_comm] using
      outer_epoch_weight_coeff_comparison S hS η LQ T w D hquarter hT_one
        hTrec hw_one hw hD_nonneg
  have hmain := mul_le_mul_of_nonneg_left hcoeff hη_nonneg
  have htrans := le_trans hmain hrec_bound
  simpa [β, c, mul_assoc, mul_left_comm, mul_comm] using htrans

/-- Scalar outer-epoch telescope for the Corollary 5.8 weights.

This is the finite algebra in Lan Theorem 5.6 proof step 2 after expectation has
already been pushed through the weighted snapshot numerator: sum the per-epoch
recursion over `s = 1, ..., S`, telescope the endpoint objective and Bregman
terms, use `w_one_corollary_5_8`, `w_corollary_5_8`, and
`T_rec_corollary_5_8` for the coefficient comparison, then drop nonnegative
terminal terms.  Reuse audit: checked `fixed_epoch_sum_Icc_pred_telescope`,
`integral_sum_telescope_bound_of_pointwise_lower_bound`, and
`summed_one_step_gap_bound_of_telescope`; they supply the generic telescope
atoms but do not package this paper's predecessor snapshot coefficient shift and
first-weight convention. -/
private theorem outer_epoch_weight_telescope_scalar
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hEpoch :
      ∀ s, s ∈ setup.outputEpochs S →
        setup.η *
              ∫ ω,
                setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P +
            setup.η * (1 - 4 * setup.LQ * setup.η) * ((setup.T s : ℝ) - 1) *
              ∫ ω,
                setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar ∂setup.P +
            ∫ ω,
              setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P ≤
          ∫ ω,
              setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P +
            setup.η *
              ∫ ω,
                setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P +
            4 * setup.LQ * setup.η ^ 2 * (setup.T s : ℝ) *
              ∫ ω,
                setup.PsiOn
                    ⟨setup.snapshotIter (s - 1) ω,
                      setup.snapshotIter_mem (s - 1) ω⟩ -
                  setup.PsiOn xStar ∂setup.P) :
    setup.η *
        Finset.sum (setup.outputEpochs S)
          (fun s =>
            setup.w s *
              ∫ ω,
                setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar ∂setup.P) ≤
      setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  let A : ℕ → ℝ := fun s =>
    ∫ ω, setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P
  let D : ℕ → ℝ := fun s =>
    ∫ ω,
      setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
        setup.PsiOn xStar ∂setup.P
  let B : ℕ → ℝ := fun s =>
    ∫ ω, setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P
  have hquarter : 4 * setup.LQ * setup.η = (1 / 4 : ℝ) := by
    rw [setup.eta_corollary_5_8]
    field_simp [ne_of_gt setup.LQ_pos]
    ring
  have hTrec : ∀ s, 2 ≤ s → (setup.T s : ℝ) = 2 * (setup.T (s - 1) : ℝ) := by
    intro s hs
    exact_mod_cast setup.T_rec_corollary_5_8 s hs
  have hA_nonneg : ∀ s, 0 ≤ A s := by
    intro s
    simpa [A, Nat.succ_sub_one] using
      fixed_epoch_prev_gap_nonneg setup xStar h_opt (s + 1)
  have hD_nonneg : ∀ s, 0 ≤ D s := by
    intro s
    simpa [D] using snapshot_gap_integral_nonneg setup xStar h_opt s
  have hB_nonneg : ∀ s, 0 ≤ B s := by
    intro s
    simpa [B] using xEpoch_v_integral_nonneg setup xStar s
  have hA0 : A 0 = D 0 := by
    simp [A, D, VarianceReducedMirrorDescentSetup.xEpochIter,
      VarianceReducedMirrorDescentSetup.snapshotIter,
      VarianceReducedMirrorDescentSetup.paperEpoch,
      VarianceReducedMirrorDescentSetup.internalProcess,
      VarianceReducedMirrorDescentSetup.PsiOn_coe, integral_const, probReal_univ]
  have hD0 :
      D 0 = setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar := by
    dsimp [D, VarianceReducedMirrorDescentSetup.snapshotIter,
      VarianceReducedMirrorDescentSetup.paperEpoch,
      VarianceReducedMirrorDescentSetup.internalProcess]
    let c : ℝ := setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar
    change (∫ _ : Ω, c ∂setup.P) = c
    rw [MeasureTheory.integral_const]
    simp [c, probReal_univ]
  have hB0 : B 0 = setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar := by
    dsimp [B, VarianceReducedMirrorDescentSetup.xEpochIter,
      VarianceReducedMirrorDescentSetup.paperEpoch,
      VarianceReducedMirrorDescentSetup.internalProcess,
      VarianceReducedMirrorDescentSetup.VOn_coe]
    let c : ℝ := setup.V setup.w₀ xStar.1
    change (∫ _ : Ω, c ∂setup.P) = setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar
    rw [MeasureTheory.integral_const]
    simp [c, probReal_univ, VarianceReducedMirrorDescentSetup.VOn_coe]
  have hEpoch' :
      ∀ s ∈ Finset.Icc 1 S.1,
        setup.η * A s +
              setup.η * (1 - 4 * setup.LQ * setup.η) * ((setup.T s : ℝ) - 1) *
                D s +
            B s ≤
          B (s - 1) + setup.η * A (s - 1) +
            4 * setup.LQ * setup.η ^ 2 * (setup.T s : ℝ) * D (s - 1) := by
    intro s hs
    have hs' : s ∈ setup.outputEpochs S := by
      simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
    simpa [A, D, B] using hEpoch s hs'
  have hscalar :
      setup.η * Finset.sum (Finset.Icc 1 S.1) (fun s => setup.w s * D s) ≤
        setup.η * (1 + 4 * setup.LQ * setup.η * (setup.T 1 : ℝ)) * D 0 + B 0 := by
    exact outer_epoch_scalar_algebra_core S.1 S.2 setup.η setup.LQ setup.T setup.w A D B
      setup.eta_pos hquarter setup.T_one_corollary_5_8 hTrec
      setup.w_one_corollary_5_8 setup.w_corollary_5_8
      hA_nonneg hD_nonneg hB_nonneg hA0 hEpoch'
  simpa [VarianceReducedMirrorDescentSetup.outputEpochs, D, hD0, hB0] using hscalar

/-- Outer epoch telescope and Corollary 5.8 coefficient comparison.

This aligns with Lan Theorem 5.6 proof step 2: sum the fixed-epoch recursion
over `s = 1, ..., S`, telescope the epoch endpoint gap/Bregman terms, compare
the remaining snapshot coefficients with the paper weights `w_s`, and drop the
terminal nonnegative Bregman divergence.  Reuse audit: checked
`outputWindow_sum_sub_succ`, `integral_sum_telescope_bound_of_pointwise_lower_bound`,
and `summed_one_step_gap_bound_of_telescope`; they provide generic telescope
atoms, while this helper packages Lan's first-weight convention and
Corollary 5.8 coefficient algebra. -/
private theorem outer_epoch_weight_telescope
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hEpoch :
      ∀ s, s ∈ setup.outputEpochs S →
        setup.η *
              ∫ ω,
                setup.Psi (setup.xEpochIter s ω) - setup.PsiOn xStar ∂setup.P +
            setup.η * (1 - 4 * setup.LQ * setup.η) * ((setup.T s : ℝ) - 1) *
              ∫ ω,
                setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar ∂setup.P +
            ∫ ω,
              setup.V (setup.xEpochIter s ω) xStar.1 ∂setup.P ≤
          ∫ ω,
              setup.V (setup.xEpochIter (s - 1) ω) xStar.1 ∂setup.P +
            setup.η *
              ∫ ω,
                setup.Psi (setup.xEpochIter (s - 1) ω) - setup.PsiOn xStar ∂setup.P +
            4 * setup.LQ * setup.η ^ 2 * (setup.T s : ℝ) *
              ∫ ω,
                setup.PsiOn
                    ⟨setup.snapshotIter (s - 1) ω,
                      setup.snapshotIter_mem (s - 1) ω⟩ -
                  setup.PsiOn xStar ∂setup.P) :
    setup.η *
        ∫ ω,
          Finset.sum (setup.outputEpochs S)
            (fun s =>
              setup.w s *
                (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar)) ∂setup.P ≤
      setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar := by
  classical
  rw [outer_weighted_snapshot_integral_sum_eq setup S xStar]
  exact outer_epoch_weight_telescope_scalar setup S xStar h_opt hEpoch

/-- Finite inner/outer telescope from unconditional Lemma 5.14 steps.

This aligns with Lan Theorem 5.6 proof steps 1-2 after the conditional
expectation has been eliminated: sum the unconditional one-step inequalities
over `t = 1..T_s` and `s = 1..S`, telescope Bregman endpoint terms, use the
snapshot Jensen bridge, compare the resulting coefficients with `w_s`, and drop
the terminal nonnegative Bregman divergence.  Reuse audit: checked the
pre-searched SOptLib candidates `summed_one_step_gap_bound_of_telescope`,
`integral_sum_telescope_bound_of_pointwise_lower_bound`, and
`outputWindow_sum_sub_succ`; their exposed names are unavailable in this target
session and their signatures do not combine the VRMD epoch indexing with Lan's
paper-specific weight algebra, so this helper isolates that remaining local
finite-sum argument. -/
private theorem theorem_5_6_epoch_telescope_from_unconditional_steps
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hstep :
      ∀ s, s ∈ setup.outputEpochs S → ∀ t : setup.InnerStep s,
        ∫ ω,
            setup.η *
                (setup.PsiOn
                    ⟨setup.paperNextInnerIterAt s t ω,
                      setup.paperNextInnerIterAt_mem s t ω⟩ - setup.PsiOn xStar) +
              setup.VOn
                ⟨setup.paperNextInnerIterAt s t ω,
                  setup.paperNextInnerIterAt_mem s t ω⟩ xStar ∂setup.P ≤
          ∫ ω,
            setup.VOn
              ⟨setup.paperInnerIterAt s t ω, setup.paperInnerIterAt_mem s t ω⟩ xStar +
              4 * setup.LQ * setup.η ^ 2 *
                ((setup.PsiOn
                      ⟨setup.paperInnerIterAt s t ω,
                        setup.paperInnerIterAt_mem s t ω⟩ -
                    setup.PsiOn xStar) +
                  (setup.PsiOn
                      ⟨setup.snapshotIter (s - 1) ω,
                        setup.snapshotIter_mem (s - 1) ω⟩ -
                    setup.PsiOn xStar)) ∂setup.P) :
    setup.η *
        ∫ ω,
          Finset.sum (setup.outputEpochs S)
            (fun s =>
              setup.w s *
                (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar)) ∂setup.P ≤
      setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar := by
  refine outer_epoch_weight_telescope setup S xStar h_opt ?_
  intro s hs
  exact epoch_recursion_from_unconditional_steps setup S xStar h_opt hstep s hs

/-- Expectation-level epoch telescope and weight simplification for Theorem 5.6.

This is the remaining Lan Theorem 5.6 proof step 2 after the Jensen bridge has
been isolated: sum the conditional Lemma 5.14 recursion over epochs, telescope
the Bregman terms, use `w_s = (1 - 4 L_Q η)(T_{s-1}-1) - 4 L_Q η T_s`, and drop
the nonnegative terminal expected divergence.  Reuse audit: checked
`outputWindow_sum_sub_succ` and `window_pathwise_bound_of_jensen_and_summed_one_step`;
they provide generic finite-window telescoping/composition, but the paper's
Theorem 5.6 uses conditional expectations, so this helper must package the VRMD
epoch recursion, `integral_le_of_condExp_le`, and paper-specific weight algebra. -/
private theorem theorem_5_6_epoch_telescope_bound
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : VarianceReducedMirrorDescentSetup.OutputHorizon)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    setup.η *
        ∫ ω,
          Finset.sum (setup.outputEpochs S)
            (fun s =>
              setup.w s *
                (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
                  setup.PsiOn xStar)) ∂setup.P ≤
      setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar := by
  -- This is the source-derived expected epoch recursion/telescope from Lan
  -- Theorem 5.6.  It is proved by summing the conditional Lemma 5.14 recursion,
  -- integrating conditional expectations with `integral_le_of_condExp_le`,
  -- applying the finite-output Jensen bridge for each epoch snapshot, and then
  -- simplifying the paper weights.
  refine theorem_5_6_epoch_telescope_from_unconditional_steps setup S xStar h_opt ?_
  intro s hs t
  have hs_pos : 1 ≤ s := by
    have hmem : s ∈ Finset.Icc 1 S.1 := by
      simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
    exact (Finset.mem_Icc.mp hmem).1
  exact lemma_5_14_unconditional_integral_step setup s t hs_pos xStar h_opt

theorem theorem_5_6
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : ℕ) (hS : 1 ≤ S)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P - setup.PsiOn xStar ≤
      (setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) /
        (setup.η * setup.outputWeightSum ⟨S, hS⟩) := by
  classical
  let Sout : VarianceReducedMirrorDescentSetup.OutputHorizon := ⟨S, hS⟩
  let weightedGap : Ω → ℝ := fun ω =>
    Finset.sum (setup.outputEpochs Sout)
      (fun s =>
        setup.w s *
          (setup.PsiOn ⟨setup.snapshotIter s ω, setup.snapshotIter_mem s ω⟩ -
            setup.PsiOn xStar))
  let W : ℝ := setup.outputWeightSum Sout
  let numerator : ℝ :=
    setup.η *
        (1 + 4 * setup.LQ * setup.η * setup.T 1) *
        (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
      setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar
  have hbar_int := theorem_5_6_output_integrable setup S hS xStar
  have hweighted_int :
      Integrable weightedGap setup.P := by
    simpa [weightedGap, Sout] using
      theorem_5_6_weighted_snapshot_gap_integrable setup Sout xStar
  have hjensen :
      ∫ ω, setup.PsiOn (setup.barXCarrier Sout ω) ∂setup.P - setup.PsiOn xStar ≤
        W⁻¹ * ∫ ω, weightedGap ω ∂setup.P := by
    simpa [weightedGap, W] using
      theorem_5_6_expected_jensen_gap setup Sout xStar
        (by simpa [Sout] using hbar_int) hweighted_int
  have htelescope :
      setup.η * ∫ ω, weightedGap ω ∂setup.P ≤ numerator := by
    simpa [weightedGap, numerator] using
      theorem_5_6_epoch_telescope_bound setup Sout xStar h_opt
  have hW_pos : 0 < W := by
    simpa [W] using setup.outputWeightSum_pos Sout
  have hη_pos : 0 < setup.η := setup.eta_pos
  have hηW_pos : 0 < setup.η * W := mul_pos hη_pos hW_pos
  calc
    ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P - setup.PsiOn xStar
        ≤ W⁻¹ * ∫ ω, weightedGap ω ∂setup.P := by
          simpa [Sout] using hjensen
    _ = (setup.η * W)⁻¹ * (setup.η * ∫ ω, weightedGap ω ∂setup.P) := by
          field_simp [ne_of_gt hη_pos, ne_of_gt hW_pos]
    _ ≤ (setup.η * W)⁻¹ * numerator := by
          exact mul_le_mul_of_nonneg_left htelescope
            (inv_nonneg.mpr (le_of_lt hηW_pos))
    _ = numerator / (setup.η * W) := by
          rw [div_eq_mul_inv]
          ring
    _ =
        (setup.η *
            (1 + 4 * setup.LQ * setup.η * setup.T 1) *
            (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
          setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) /
          (setup.η * setup.outputWeightSum ⟨S, hS⟩) := by
          simp [W, numerator, Sout]

/-- Guarded compatibility route for epoch-telescope proof experiments.

The paper-facing `theorem_5_6` keeps the source head.  This helper keeps the
older explicit component-convexity experiment under a suffixed name while the
canonical route consumes `setup.hcomponent_convex`. -/
theorem theorem_5_6_of_component_convex
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (hcomponent_convex : ∀ i, ConvexOn ℝ setup.X (setup.f i))
    (S : ℕ) (hS : 1 ≤ S)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P - setup.PsiOn xStar ≤
      (setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) /
        (setup.η * setup.outputWeightSum ⟨S, hS⟩) := by
  exact theorem_5_6 setup S hS xStar h_opt

/-- Scalar specialization from Theorem 5.6's denominator form to Corollary 5.8.

This aligns with `book/FOML/VarianceReducedMirrorDescent.json` main theorem
proof step 3.  Considered `SOptLib.outputWindow_sum_sub_succ`,
`SOptLib.expectedOutput_eq_weighted_sum_div`, and
`_root_.SOptLib.outputWeightDenominator_pos`; they cover generic output/telescope
machinery and positivity, but not the paper-specific Eq. (5.3.17) arithmetic
`γ = 1/(16 L_Q)`, `T₁ = 7`, and
`∑_{s=1}^S w_s ≥ (1/8)(2^S - 1)`. -/
private theorem corollary_5_8_rhs_specialization
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : ℕ) (hS : 1 ≤ S)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
      (setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) /
        (setup.η * setup.outputWeightSum ⟨S, hS⟩) ≤
      (8 / ((2 : ℝ) ^ S - 1)) *
        ((11 / 4 : ℝ) *
            (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
          16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) := by
  let A := setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar
  let B := setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar
  let D := (2 : ℝ) ^ S - 1
  let W := setup.outputWeightSum ⟨S, hS⟩
  have hA : 0 ≤ A := by
    dsimp [A]
    exact sub_nonneg.mpr (h_opt ⟨setup.w₀, setup.hw₀_mem⟩)
  have hB : 0 ≤ B := by
    dsimp [B]
    simpa [VarianceReducedMirrorDescentSetup.VOn_coe] using
      setup.V_nonneg setup.w₀ xStar.1 setup.hw₀_mem xStar.2
  have hLQ : 0 < setup.LQ := setup.LQ_pos
  have hη : 0 < setup.η := setup.eta_pos
  have hD : 0 < D := by
    dsimp [D]
    have hpow : (1 : ℝ) < (2 : ℝ) ^ S :=
      one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega : S ≠ 0)
    linarith
  have hWpos : 0 < W := by
    dsimp [W]
    exact setup.outputWeightSum_pos ⟨S, hS⟩
  have hWlower : (1 / 8 : ℝ) * D ≤ W := by
    dsimp [W, D]
    rw [setup.outputWeightSum_eq]
    have hpoint : ∀ s ∈ setup.outputEpochs ⟨S, hS⟩,
        (1 / 8 : ℝ) * (2 : ℝ) ^ (s - 1) ≤ setup.w s := by
      intro s hs
      have hmem : s ∈ Finset.Icc 1 S := by
        simpa [VarianceReducedMirrorDescentSetup.outputEpochs] using hs
      rcases Finset.mem_Icc.mp hmem with ⟨hs1, _hsS⟩
      have hs0 : s ≠ 0 := by omega
      have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (s - 1) := by
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      simp [VarianceReducedMirrorDescentSetup.w, VarianceReducedMirrorDescentSetup.T, hs0]
      nlinarith
    have hsum := Finset.sum_le_sum hpoint
    have hgeomAll : ∀ N : ℕ,
        Finset.sum (Finset.Icc 1 N)
          (fun s => (1 / 8 : ℝ) * (2 : ℝ) ^ (s - 1)) =
        (1 / 8 : ℝ) * ((2 : ℝ) ^ N - 1) := by
      intro N
      induction N with
      | zero => norm_num
      | succ n ih =>
          rw [Finset.sum_Icc_succ_top (a := 1) (b := n)
            (f := fun s => (1 / 8 : ℝ) * (2 : ℝ) ^ (s - 1))
            (by omega : 1 ≤ n + 1)]
          rw [ih]
          have hpowSucc : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
            rw [pow_succ]
            ring
          simp only [Nat.add_sub_cancel]
          rw [hpowSucc]
          ring
    calc
      (1 / 8 : ℝ) * ((2 : ℝ) ^ S - 1) =
          Finset.sum (Finset.Icc 1 S)
            (fun s => (1 / 8 : ℝ) * (2 : ℝ) ^ (s - 1)) := by
            rw [hgeomAll]
      _ ≤ Finset.sum (setup.outputEpochs ⟨S, hS⟩) setup.w := hsum
  have hη16 : 16 * setup.LQ * setup.η = 1 := by
    rw [setup.eta_corollary_5_8]
    field_simp [ne_of_gt hLQ]
  have hcoef : 1 + 4 * setup.LQ * setup.η * setup.T 1 = (11 / 4 : ℝ) := by
    rw [setup.T_one_corollary_5_8]
    nlinarith [hη16]
  let C := (11 / 4 : ℝ) * A + 16 * setup.LQ * B
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [hA, hB, hLQ]
  have hD8 : 0 < (1 / 8 : ℝ) * D := by
    nlinarith [hD]
  have hnum : setup.η * (11 / 4 : ℝ) *
        (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
      setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar = setup.η * C := by
    dsimp [A, B, C]
    nlinarith [hη16]
  calc
    (setup.η *
          (1 + 4 * setup.LQ * setup.η * setup.T 1) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) /
        (setup.η * setup.outputWeightSum ⟨S, hS⟩) = C / W := by
          rw [hcoef]
          rw [hnum]
          change (setup.η * C) / (setup.η * W) = C / W
          field_simp [ne_of_gt hη, ne_of_gt hWpos]
    _ ≤ C / ((1 / 8 : ℝ) * D) := by
          exact div_le_div_of_nonneg_left hC hD8 hWlower
    _ = (8 / D) * C := by
          ring_nf

/-- Corollary 5.8 compatibility route for experiments that explicitly pass
component convexity.

The paper-canonical `corollary_5_8` keeps the JSON head.  This suffixed theorem
is retained for older proof scripts; the source-backed canonical route uses
`setup.hcomponent_convex` directly. -/
theorem corollary_5_8_of_component_convex
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (hcomponent_convex : ∀ i, ConvexOn ℝ setup.X (setup.f i))
    (S : ℕ) (hS : 1 ≤ S)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P - setup.PsiOn xStar ≤
      (8 / ((2 : ℝ) ^ S - 1)) *
        ((11 / 4 : ℝ) *
            (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
          16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) := by
  exact le_trans (theorem_5_6 setup S hS xStar h_opt)
    (corollary_5_8_rhs_specialization setup S hS xStar h_opt)

/-! Used in: the final smooth-convex convergence statement corresponding to
Corollary 5.8. -/
theorem corollary_5_8
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : ℕ) (hS : 1 ≤ S)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P - setup.PsiOn xStar ≤
      (8 / ((2 : ℝ) ^ S - 1)) *
        ((11 / 4 : ℝ) *
            (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
          16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) := by
  exact corollary_5_8_of_component_convex setup setup.hcomponent_convex S hS xStar h_opt

/-- Nonnegativity of the initial radius in the Corollary 5.8 complexity rate.

This is derived from optimality of `x*`, Bregman nonnegativity, and `L_Q > 0`;
it is intentionally a theorem, not a setup field. -/
private theorem complexityRadius_nonneg_of_optimal
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    0 ≤ setup.complexityRadius xStar := by
  have hgap :
      0 ≤ setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar := by
    exact sub_nonneg.mpr (h_opt ⟨setup.w₀, setup.hw₀_mem⟩)
  have hV :
      0 ≤ setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar := by
    simpa [VarianceReducedMirrorDescentSetup.VOn_coe] using
      setup.V_nonneg setup.w₀ xStar.1 setup.hw₀_mem xStar.2
  have hLQ : 0 ≤ setup.LQ := le_of_lt setup.LQ_pos
  unfold VarianceReducedMirrorDescentSetup.complexityRadius
  nlinarith [mul_nonneg hLQ hV]

/-- In the zero-radius case, the scalar numerator in Corollary 5.8's displayed
RHS is zero.

This supplies the degenerate branch needed by the totalized SFO-rate theorem:
when the optimality gap plus `L_Q V(x⁰,x*)` vanishes, both nonnegative summands
vanish, so the stronger displayed RHS numerator also vanishes. -/
private theorem corollary_5_8_rhs_numerator_eq_zero_of_complexityRadius_eq_zero
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (hR : setup.complexityRadius xStar = 0) :
    (11 / 4 : ℝ) *
        (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
      16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar = 0 := by
  let A := setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar
  let B := setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar
  have hA : 0 ≤ A := by
    dsimp [A]
    exact sub_nonneg.mpr (h_opt ⟨setup.w₀, setup.hw₀_mem⟩)
  have hB : 0 ≤ B := by
    dsimp [B]
    simpa [VarianceReducedMirrorDescentSetup.VOn_coe] using
      setup.V_nonneg setup.w₀ xStar.1 setup.hw₀_mem xStar.2
  have hLQ_pos : 0 < setup.LQ := setup.LQ_pos
  have hLQ_nonneg : 0 ≤ setup.LQ := le_of_lt hLQ_pos
  have hR' : A + setup.LQ * B = 0 := by
    simpa [VarianceReducedMirrorDescentSetup.complexityRadius, A, B] using hR
  have hA_zero : A = 0 := by
    nlinarith [hA, mul_nonneg hLQ_nonneg hB, hR']
  have hB_zero : B = 0 := by
    have hmul_zero : setup.LQ * B = 0 := by
      nlinarith [hR', hA_zero]
    exact (mul_eq_zero.mp hmul_zero).resolve_left (ne_of_gt hLQ_pos)
  dsimp [A, B] at hA_zero hB_zero ⊢
  rw [hA_zero, hB_zero]
  ring

/-- Zero-radius branch of the Corollary 5.8 SFO complexity helper.

This branch uses the local totalized rate `sfoComplexityRate = 1`; the searched
SOptLib logarithmic/ceiling candidates (`ceil_log_two_div_le_three_log_one_div_over_log_two`,
`natCast_max_one_ceil_le_add_two`, and `twoPhaseSFOCallBound_bigO_rate`) address
positive-radius logarithmic accounting and are not needed in the degenerate
already-optimal case. -/
private theorem corollary_5_8_sfo_complexity_rate_zero_radius
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_bound :
      ∀ (S : ℕ) (hS : 1 ≤ S),
        ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P -
          setup.PsiOn xStar ≤
        (8 / ((2 : ℝ) ^ S - 1)) *
          ((11 / 4 : ℝ) *
              (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
            16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar))
    (hR : setup.complexityRadius xStar = 0)
    (hNumerator :
      (11 / 4 : ℝ) *
          (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
        16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar = 0) :
    ∃ callsForAccuracy : ℝ → ℝ,
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∃ S : {S : ℕ // 1 ≤ S},
          (∫ ω, setup.PsiOn (setup.barXCarrier S ω) ∂setup.P -
              setup.PsiOn xStar ≤ ε) ∧
            callsForAccuracy ε = (setup.cumulativeSFOCalls S.1 : ℝ)) ∧
      (callsForAccuracy =O[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ => setup.sfoComplexityRate xStar ε) := by
  refine ⟨fun _ => (setup.cumulativeSFOCalls 1 : ℝ), ?_, ?_⟩
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    refine ⟨⟨1, by norm_num⟩, ?_, rfl⟩
    have hfirst := h_bound 1 (by norm_num)
    have hnonneg : 0 ≤ ε := le_of_lt hε
    calc
      ∫ ω, setup.PsiOn (setup.barXCarrier ⟨1, by norm_num⟩ ω) ∂setup.P -
          setup.PsiOn xStar ≤
          (8 / ((2 : ℝ) ^ 1 - 1)) *
            ((11 / 4 : ℝ) *
                (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
              16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) := hfirst
      _ = 0 := by
        rw [hNumerator]
        ring
      _ ≤ ε := hnonneg
  · apply Asymptotics.IsBigO.of_bound (‖(setup.cumulativeSFOCalls 1 : ℝ)‖)
    filter_upwards with ε
    rw [setup.sfoComplexityRate_eq_one_of_radius_eq_zero xStar ε hR]
    simp

/-- The Corollary 5.8 displayed numerator is controlled by the paper's
positive-radius scale.

This aligns with Lan's proof step passing from the RHS numerator to the
complexity radius `Psi(x⁰)-Psi(x*) + L_Q V(x⁰,x*)`; the searched SOptLib
geometric/logarithmic candidates do not address this model-specific
optimization numerator comparison. -/
private theorem corollary_5_8_rhs_numerator_le_sixteen_radius
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    (11 / 4 : ℝ) *
        (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
      16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar ≤
        16 * setup.complexityRadius xStar := by
  let A := setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar
  let B := setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar
  have hA : 0 ≤ A := by
    dsimp [A]
    exact sub_nonneg.mpr (h_opt ⟨setup.w₀, setup.hw₀_mem⟩)
  have hB : 0 ≤ B := by
    dsimp [B]
    simpa [VarianceReducedMirrorDescentSetup.VOn_coe] using
      setup.V_nonneg setup.w₀ xStar.1 setup.hw₀_mem xStar.2
  have hLQ : 0 ≤ setup.LQ := le_of_lt setup.LQ_pos
  change (11 / 4 : ℝ) * A + 16 * setup.LQ * B ≤
    16 * (A + setup.LQ * B)
  nlinarith [hA, hB, hLQ, mul_nonneg hLQ hB]

/-- Geometric inversion for the positive-radius epoch selector.

This is the deterministic form of Lan Corollary 5.8 proof step 5: choose
`S = max 1 ⌈log₂(256 R / ε)⌉` so the geometric factor
`8 / (2^S - 1)` turns a numerator bounded by `16 R` into at most `ε`.
The candidates `le_positive_ceil_max_one` and `natCast_max_one_ceil_le_add_two`
were checked; this helper packages the additional logarithm/exponential
monotonicity and denominator arithmetic not supplied by a single SOptLib lemma. -/
private theorem geometric_error_bound_of_epoch_selector
    {R C ε : ℝ}
    (hRpos : 0 < R)
    (hCle : C ≤ 16 * R)
    (hε : 0 < ε) :
    (8 / ((2 : ℝ) ^
        (max 1 (Nat.ceil (Real.log (256 * R / ε) / Real.log 2)) : ℕ) - 1)) *
        C ≤ ε := by
  classical
  let S : ℕ := max 1 (Nat.ceil (Real.log (256 * R / ε) / Real.log 2))
  let A : ℝ := 256 * R / ε
  change (8 / ((2 : ℝ) ^ S - 1)) * C ≤ ε
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hS1 : 1 ≤ S := by
    dsimp [S]
    exact Nat.le_max_left 1 (Nat.ceil (Real.log (256 * R / ε) / Real.log 2))
  have hpow_ge_two : 2 ≤ (2 : ℝ) ^ S := by
    have hpow : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ S :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hS1
    simpa using hpow
  have hden_pos : 0 < (2 : ℝ) ^ S - 1 := by
    nlinarith
  have hden_ge_one : 1 ≤ (2 : ℝ) ^ S - 1 := by
    nlinarith
  have hcoeff_nonneg : 0 ≤ 8 / ((2 : ℝ) ^ S - 1) := by
    positivity
  have hCbound :
      (8 / ((2 : ℝ) ^ S - 1)) * C ≤
        (8 / ((2 : ℝ) ^ S - 1)) * (16 * R) := by
    exact mul_le_mul_of_nonneg_left hCle hcoeff_nonneg
  have hden_lower : 128 * R / ε ≤ (2 : ℝ) ^ S - 1 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hAhalf : 128 * R / ε = A / 2 := by
      dsimp [A]
      ring
    rw [hAhalf]
    by_cases hA2 : A ≤ 2
    · have hAhalf_le_one : A / 2 ≤ 1 := by
        nlinarith
      exact hAhalf_le_one.trans hden_ge_one
    · have hA2lt : 2 < A := lt_of_not_ge hA2
      have hy_le :
          Real.log A / Real.log 2 ≤ (S : ℝ) := by
        simpa [S, A] using le_positive_ceil_max_one
          (Real.log A / Real.log 2)
      have hlog_le : Real.log A ≤ (S : ℝ) * Real.log 2 := by
        have hmul := mul_le_mul_of_nonneg_right hy_le (le_of_lt hlog2_pos)
        have hleft :
            Real.log A / Real.log 2 * Real.log 2 = Real.log A := by
          field_simp [hlog2_pos.ne']
        nlinarith
      have hApow : A ≤ (2 : ℝ) ^ S := by
        exact Real.le_pow_of_log_le (x := A) (y := 2) (n := S)
          (by norm_num) hlog_le
      nlinarith
  have hmain :
      (8 / ((2 : ℝ) ^ S - 1)) * (16 * R) ≤ ε := by
    have hnum_le : 128 * R ≤ ε * ((2 : ℝ) ^ S - 1) := by
      have hmul := mul_le_mul_of_nonneg_right hden_lower (le_of_lt hε)
      have hleft : (128 * R / ε) * ε = 128 * R := by
        field_simp [hε.ne']
      nlinarith
    have hquot : 128 * R / ((2 : ℝ) ^ S - 1) ≤ ε := by
      exact (div_le_iff₀ hden_pos).2 (by nlinarith)
    calc
      (8 / ((2 : ℝ) ^ S - 1)) * (16 * R) =
          128 * R / ((2 : ℝ) ^ S - 1) := by
            ring
      _ ≤ ε := hquot
  exact hCbound.trans hmain

/-- Constant full-gradient costs summed over epochs `1, ..., S`.

This is the `m` part of Lan's proof step "each epoch costs `m + T_s`".
Searched `Finset sum Icc pow two geom_sum Nat.cast cumulativeSFOCalls` and
`sum constant Icc Nat.card_Icc Finset.sum_const`; SOptLib only supplies generic
Icc reindexing/telescoping lemmas, while this local helper is the direct
Mathlib cardinality normalization for this VRMD accounting sum. -/
private theorem sum_constant_card_Icc_real
    (S : ℕ) (_hS : 1 ≤ S) :
    ((Finset.sum (Finset.Icc 1 S) (fun _ : ℕ => Fintype.card ι) : ℕ) : ℝ) =
      (Fintype.card ι : ℝ) * (S : ℝ) := by
  classical
  rw [Finset.sum_const]
  simp [Nat.card_Icc, mul_comm]

/-- Geometric upper bound for the Corollary 5.8 epoch lengths.

This is the `T_s = 7 * 2^(s-1)` part of Lan's SFO count in (5.3.19).
Searched `geometric sum range pow two Nat sum geometric`; Mathlib has generic
geometric-sum identities such as `geom_sum_mul`, but no direct Icc/cast bound
for this totalized VRMD schedule, so the proof uses induction on the epoch
horizon and `Finset.sum_Icc_succ_top`. -/
private theorem sum_epoch_lengths_le_seven_pow
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : ℕ) :
    ((Finset.sum (Finset.Icc 1 S) setup.T : ℕ) : ℝ) ≤
      7 * (2 : ℝ) ^ S := by
  induction S with
  | zero =>
      norm_num
  | succ S ih =>
      have hsplit :
          Finset.sum (Finset.Icc 1 (S + 1)) setup.T =
            Finset.sum (Finset.Icc 1 S) setup.T + setup.T (S + 1) := by
        rw [Finset.sum_Icc_succ_top]
        omega
      have hT :
          ((setup.T (S + 1) : ℕ) : ℝ) = 7 * (2 : ℝ) ^ S := by
        simp [VarianceReducedMirrorDescentSetup.T]
      calc
        ((Finset.sum (Finset.Icc 1 (S + 1)) setup.T : ℕ) : ℝ) =
            ((Finset.sum (Finset.Icc 1 S) setup.T : ℕ) : ℝ) +
              ((setup.T (S + 1) : ℕ) : ℝ) := by
          rw [hsplit]
          norm_num
        _ ≤ 7 * (2 : ℝ) ^ S + 7 * (2 : ℝ) ^ S := by
          exact add_le_add ih (le_of_eq hT)
        _ = 7 * (2 : ℝ) ^ (S + 1) := by
          rw [pow_succ]
          ring

/-- Finite-sum SFO accounting for the VRMD epoch schedule.

This is the paper-specific sum `∑_{s=1}^S (m + T_s)` from Lan Corollary 5.8,
using `T_s = 7 * 2^(s-1)`. SOptLib's `twoPhaseSFOCallBound_bigO_rate` was
considered and rejected because it bounds a different two-phase SMD budget,
not this VRMD per-epoch full-gradient plus inner-loop count. -/
private theorem cumulativeSFOCalls_le_card_mul_add_pow
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (S : ℕ) (hS : 1 ≤ S) :
    (setup.cumulativeSFOCalls S : ℝ) ≤
      (Fintype.card ι : ℝ) * (S : ℝ) + 7 * (2 : ℝ) ^ S := by
  classical
  have hTsum := sum_epoch_lengths_le_seven_pow (setup := setup) S
  have hConst := sum_constant_card_Icc_real (ι := ι) S hS
  have hsplit :
      Finset.sum (Finset.Icc 1 S) (fun s => Fintype.card ι + setup.T s) =
        Finset.sum (Finset.Icc 1 S) (fun _ : ℕ => Fintype.card ι) +
          Finset.sum (Finset.Icc 1 S) setup.T := by
    rw [Finset.sum_add_distrib]
  rw [setup.cumulativeSFOCalls_eq S]
  calc
    ((Finset.sum (Finset.Icc 1 S) (fun s => Fintype.card ι + setup.T s) : ℕ) : ℝ) =
        ((Finset.sum (Finset.Icc 1 S) (fun _ : ℕ => Fintype.card ι) : ℕ) : ℝ) +
          ((Finset.sum (Finset.Icc 1 S) setup.T : ℕ) : ℝ) := by
      rw [hsplit]
      norm_num
    _ ≤ (Fintype.card ι : ℝ) * (S : ℝ) + 7 * (2 : ℝ) ^ S := by
      exact add_le_add (le_of_eq hConst) hTsum

/-- Pointwise SFO-count comparison for the positive-radius epoch selector.

This is Lan Corollary 5.8 proof step 5 after the finite SFO accounting
`∑_{s=1}^S (m + T_s)`: for sufficiently small positive `ε`, the selected
number of gradient calls is bounded by a constant multiple of the displayed
rate `m log(R / ε) + R / ε`.  Considered SOptLib candidates
`natCast_max_one_ceil_le_add_two`, `ceil_log_two_div_le_three_log_one_div_over_log_two`,
`le_positive_ceil_max_one`, and `twoPhaseSFOCallBound_bigO_rate`; the first
three are used as arithmetic components, while the two-phase SFO helper does
not match this VRMD per-epoch full-gradient plus inner-loop accounting. -/
private theorem selector_calls_le_const_mul_displayed_rate_near_zero
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (hRpos : 0 < setup.complexityRadius xStar) :
    ∃ C : ℝ,
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ‖(setup.cumulativeSFOCalls
          (max 1
            (Nat.ceil (Real.log (256 * setup.complexityRadius xStar / ε) /
              Real.log 2))) : ℝ)‖ ≤
          C * ‖setup.displayedSFOComplexityRate xStar ε‖ := by
  classical
  let R : ℝ := setup.complexityRadius xStar
  let m : ℝ := Fintype.card ι
  let α : ℝ := 1 / Real.log 2
  let β : ℝ := Real.log 256 / Real.log 2 + 2
  refine ⟨α + m * β + 7168, ?_⟩
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hRpos' : 0 < R := by simpa [R] using hRpos
  have hsmall :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), ε < min R (256 * R) := by
    have hδ : 0 < min R (256 * R) := by
      exact lt_min hRpos' (by positivity)
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with ε hε_pos_mem hε_small
  have hεpos : 0 < ε := by simpa using hε_pos_mem
  have hε_lt_R : ε < R := lt_of_lt_of_le hε_small (min_le_left R (256 * R))
  have hε_lt_256R : ε < 256 * R := lt_of_lt_of_le hε_small (min_le_right R (256 * R))
  let S : ℕ :=
    max 1 (Nat.ceil (Real.log (256 * R / ε) / Real.log 2))
  let L : ℝ := Real.log (R / ε)
  let Q : ℝ := R / ε
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hQge_one : 1 ≤ Q := by
    dsimp [Q]
    rw [le_div_iff₀ hεpos]
    linarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L, Q] at hQge_one ⊢
    exact Real.log_nonneg hQge_one
  have hApos : 0 < 256 * R / ε := by
    positivity
  have hAge_one : 1 ≤ 256 * R / ε := by
    rw [le_div_iff₀ hεpos]
    linarith
  have hy_nonneg : 0 ≤ Real.log (256 * R / ε) / Real.log 2 := by
    exact div_nonneg (Real.log_nonneg hAge_one) (le_of_lt hlog2_pos)
  have hS_le_y :
      (S : ℝ) ≤ Real.log (256 * R / ε) / Real.log 2 + 2 := by
    simpa [S] using
      natCast_max_one_ceil_le_add_two
        (Real.log (256 * R / ε) / Real.log 2) hy_nonneg
  have hlogA :
      Real.log (256 * R / ε) = Real.log 256 + L := by
    have hrewrite : 256 * R / ε = (256 : ℝ) * (R / ε) := by ring
    rw [hrewrite, Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) hQpos.ne']
  have hS_le :
      (S : ℝ) ≤ α * L + β := by
    calc
      (S : ℝ) ≤ Real.log (256 * R / ε) / Real.log 2 + 2 := hS_le_y
      _ = α * L + β := by
        dsimp [α, β]
        rw [hlogA]
        field_simp [hlog2_pos.ne']
        ring
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have hfour : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [hfour, Real.log_pow]
    norm_num
  have hlogB :
      Real.log (1024 * R / ε) = Real.log (256 * R / ε) + 2 * Real.log 2 := by
    have hrewrite : 1024 * R / ε = (4 : ℝ) * (256 * R / ε) := by ring
    rw [hrewrite, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hApos.ne', hlog_four]
    ring
  have hSlog_le :
      (S : ℝ) * Real.log 2 ≤ Real.log (1024 * R / ε) := by
    have hmul := mul_le_mul_of_nonneg_right hS_le_y (le_of_lt hlog2_pos)
    have hleft :
        (Real.log (256 * R / ε) / Real.log 2 + 2) * Real.log 2 =
          Real.log (256 * R / ε) + 2 * Real.log 2 := by
      field_simp [hlog2_pos.ne']
    nlinarith [hmul, hleft, hlogB]
  have hpow_le : (2 : ℝ) ^ S ≤ 1024 * R / ε := by
    have hBpos : 0 < 1024 * R / ε := by positivity
    exact (Real.pow_le_iff_le_log (by norm_num : (0 : ℝ) < 2) hBpos).2 hSlog_le
  have hS_one : 1 ≤ S := by
    dsimp [S]
    exact Nat.le_max_left 1 (Nat.ceil (Real.log (256 * R / ε) / Real.log 2))
  have hCalls :=
    cumulativeSFOCalls_le_card_mul_add_pow (setup := setup) S hS_one
  have hCalls_nonneg :
      0 ≤ (setup.cumulativeSFOCalls S : ℝ) := by exact_mod_cast Nat.zero_le _
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.zero_le (Fintype.card ι)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    have hlog256_nonneg : 0 ≤ Real.log (256 : ℝ) := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 256)
    positivity
  have hRate_nonneg :
      0 ≤ setup.displayedSFOComplexityRate xStar ε := by
    rw [setup.displayedSFOComplexityRate_eq]
    change 0 ≤ m * L + Q
    exact add_nonneg (mul_nonneg hm_nonneg hL_nonneg) (le_of_lt hQpos)
  have hCalls_bound :
      (setup.cumulativeSFOCalls S : ℝ) ≤
        (α + m * β + 7168) * setup.displayedSFOComplexityRate xStar ε := by
    have hPowTerm :
        7 * (2 : ℝ) ^ S ≤ 7168 * Q := by
      calc
        7 * (2 : ℝ) ^ S ≤ 7 * (1024 * R / ε) :=
          mul_le_mul_of_nonneg_left hpow_le (by norm_num : (0 : ℝ) ≤ 7)
        _ = 7168 * Q := by
          dsimp [Q]
          ring
    have hCardTerm :
        m * (S : ℝ) ≤ α * (m * L) + (m * β) * Q := by
      have hmul := mul_le_mul_of_nonneg_left hS_le hm_nonneg
      have hconst : m * β ≤ (m * β) * Q := by
        have hmβ_nonneg : 0 ≤ m * β := mul_nonneg hm_nonneg hβ_nonneg
        nlinarith
      calc
        m * (S : ℝ) ≤ m * (α * L + β) := hmul
        _ = α * (m * L) + m * β := by ring
        _ ≤ α * (m * L) + (m * β) * Q := by
          exact add_le_add_right hconst _
    have hAccounting :
        (setup.cumulativeSFOCalls S : ℝ) ≤
          α * (m * L) + (m * β) * Q + 7168 * Q := by
      have hCalls' :
          (setup.cumulativeSFOCalls S : ℝ) ≤
            m * (S : ℝ) + 7 * (2 : ℝ) ^ S := by
        simpa [m] using hCalls
      calc
        (setup.cumulativeSFOCalls S : ℝ) ≤
            m * (S : ℝ) + 7 * (2 : ℝ) ^ S := hCalls'
        _ ≤ (α * (m * L) + (m * β) * Q) + 7168 * Q :=
          add_le_add hCardTerm hPowTerm
        _ = α * (m * L) + (m * β) * Q + 7168 * Q := by ring
    rw [setup.displayedSFOComplexityRate_eq]
    change (setup.cumulativeSFOCalls S : ℝ) ≤
      (α + m * β + 7168) * (m * L + Q)
    have hC₁ : α * (m * L) ≤ (α + m * β + 7168) * (m * L) := by
      have hmL_nonneg : 0 ≤ m * L := mul_nonneg hm_nonneg hL_nonneg
      have hcoef : α ≤ α + m * β + 7168 := by
        calc
          α ≤ α + m * β := le_add_of_nonneg_right (mul_nonneg hm_nonneg hβ_nonneg)
          _ ≤ α + m * β + 7168 := le_add_of_nonneg_right (by norm_num)
      exact mul_le_mul_of_nonneg_right hcoef hmL_nonneg
    have hC₂ : (m * β) * Q + 7168 * Q ≤ (α + m * β + 7168) * Q := by
      calc
        (m * β) * Q + 7168 * Q = (m * β + 7168) * Q := by ring
        _ ≤ (α + (m * β + 7168)) * Q := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hα_nonneg) (le_of_lt hQpos)
        _ = (α + m * β + 7168) * Q := by ring
    calc
      (setup.cumulativeSFOCalls S : ℝ) ≤
          α * (m * L) + (m * β) * Q + 7168 * Q := hAccounting
      _ = α * (m * L) + ((m * β) * Q + 7168 * Q) := by ring
      _ ≤ (α + m * β + 7168) * (m * L) +
          (α + m * β + 7168) * Q := add_le_add hC₁ hC₂
      _ = (α + m * β + 7168) * (m * L + Q) := by ring
  simpa [R, S, Real.norm_of_nonneg hCalls_nonneg, Real.norm_of_nonneg hRate_nonneg] using
    hCalls_bound

/-- Big-O comparison for the positive-radius epoch selector's SFO count.

This isolates the asymptotic part of Lan Corollary 5.8 proof step 5: combine
the ceiling overshoot bound, the finite SFO-count sum, and the positive-radius
rewrite to the displayed rate
`m log(R / ε) + R / ε`. The checked helpers
`natCast_max_one_ceil_le_add_two`, `ceil_log_two_div_le_three_log_one_div_over_log_two`,
and `Asymptotics.IsBigO.of_bound` supply pieces of this argument, while the
remaining work is the local normalization from `256 R / ε` to `R / ε`. -/
private theorem positive_radius_selector_calls_bigO_displayed_rate
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (hRpos : 0 < setup.complexityRadius xStar) :
    (fun ε : ℝ =>
      (setup.cumulativeSFOCalls
        (max 1
          (Nat.ceil (Real.log (256 * setup.complexityRadius xStar / ε) /
            Real.log 2))) : ℝ)) =O[nhdsWithin 0 (Set.Ioi 0)]
      fun ε : ℝ => setup.sfoComplexityRate xStar ε := by
  obtain ⟨C, hC⟩ :=
    selector_calls_le_const_mul_displayed_rate_near_zero setup xStar hRpos
  have hRne : setup.complexityRadius xStar ≠ 0 := ne_of_gt hRpos
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with ε hε
  rw [setup.sfoComplexityRate_eq_displayed_of_radius_ne_zero xStar ε hRne]
  exact hε

/-- Positive-radius branch of the Corollary 5.8 SFO complexity helper.

This is the remaining deterministic arithmetic step: invert the geometric
Corollary 5.8 error bound with a ceiling epoch selector, sum the epoch SFO
costs, and compare the result to the displayed
`m log(R / ε) + R / ε` rate. SOptLib supplies the relevant ceiling/logarithm
building blocks (`le_positive_ceil_max_one`,
`ceil_log_two_div_le_three_log_one_div_over_log_two`,
`natCast_max_one_ceil_le_add_two`), while `twoPhaseSFOCallBound_bigO_rate`
was considered and rejected because it packages a different two-phase SMD
budget rather than this VRMD per-epoch finite-sum count. -/
private theorem corollary_5_8_sfo_complexity_rate_pos_radius
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (h_bound :
      ∀ (S : ℕ) (hS : 1 ≤ S),
        ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P -
          setup.PsiOn xStar ≤
        (8 / ((2 : ℝ) ^ S - 1)) *
          ((11 / 4 : ℝ) *
              (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
            16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar))
    (hRpos : 0 < setup.complexityRadius xStar) :
    ∃ callsForAccuracy : ℝ → ℝ,
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∃ S : {S : ℕ // 1 ≤ S},
          (∫ ω, setup.PsiOn (setup.barXCarrier S ω) ∂setup.P -
              setup.PsiOn xStar ≤ ε) ∧
            callsForAccuracy ε = (setup.cumulativeSFOCalls S.1 : ℝ)) ∧
      (callsForAccuracy =O[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ => setup.sfoComplexityRate xStar ε) := by
  let selector : ℝ → ℕ := fun ε =>
    max 1
      (Nat.ceil (Real.log (256 * setup.complexityRadius xStar / ε) /
        Real.log 2))
  refine ⟨fun ε => (setup.cumulativeSFOCalls (selector ε) : ℝ), ?_, ?_⟩
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hS : 1 ≤ selector ε := by
      dsimp [selector]
      exact Nat.le_max_left 1
        (Nat.ceil (Real.log (256 * setup.complexityRadius xStar / ε) /
          Real.log 2))
    refine ⟨⟨selector ε, hS⟩, ?_, rfl⟩
    have hNumerator :
        (11 / 4 : ℝ) *
            (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
          16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar ≤
            16 * setup.complexityRadius xStar :=
      corollary_5_8_rhs_numerator_le_sixteen_radius setup xStar h_opt
    calc
      ∫ ω, setup.PsiOn (setup.barXCarrier ⟨selector ε, hS⟩ ω) ∂setup.P -
          setup.PsiOn xStar ≤
          (8 / ((2 : ℝ) ^ selector ε - 1)) *
            ((11 / 4 : ℝ) *
                (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
              16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar) :=
        h_bound (selector ε) hS
      _ ≤ ε := by
        dsimp [selector]
        exact geometric_error_bound_of_epoch_selector hRpos hNumerator hε
  · simpa [selector] using
      positive_radius_selector_calls_bigO_displayed_rate setup xStar hRpos

/-- Deterministic epoch-selection and SFO-count arithmetic behind the
Corollary 5.8 displayed complexity rate.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/rate`.
Quote: `O{ m log ((Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon) + (Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon }`.

The rate object used in the conclusion totalizes the displayed logarithmic
formula at zero initial radius, where the already-optimal case needs only a
constant SFO-count envelope. -/
private theorem corollary_5_8_sfo_complexity_rate_from_bound
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z)
    (h_bound :
      ∀ (S : ℕ) (hS : 1 ≤ S),
        ∫ ω, setup.PsiOn (setup.barXCarrier ⟨S, hS⟩ ω) ∂setup.P -
          setup.PsiOn xStar ≤
        (8 / ((2 : ℝ) ^ S - 1)) *
          ((11 / 4 : ℝ) *
              (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
            16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar)) :
    ∃ callsForAccuracy : ℝ → ℝ,
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∃ S : {S : ℕ // 1 ≤ S},
          (∫ ω, setup.PsiOn (setup.barXCarrier S ω) ∂setup.P -
              setup.PsiOn xStar ≤ ε) ∧
            callsForAccuracy ε = (setup.cumulativeSFOCalls S.1 : ℝ)) ∧
      (callsForAccuracy =O[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ => setup.sfoComplexityRate xStar ε) := by
  have hRadius_nonneg := complexityRadius_nonneg_of_optimal setup xStar h_opt
  have hZeroNumerator :
      setup.complexityRadius xStar = 0 →
        (11 / 4 : ℝ) *
            (setup.PsiOn ⟨setup.w₀, setup.hw₀_mem⟩ - setup.PsiOn xStar) +
          16 * setup.LQ * setup.VOn ⟨setup.w₀, setup.hw₀_mem⟩ xStar = 0 :=
    corollary_5_8_rhs_numerator_eq_zero_of_complexityRadius_eq_zero setup xStar h_opt
  by_cases hR : setup.complexityRadius xStar = 0
  · exact corollary_5_8_sfo_complexity_rate_zero_radius setup xStar h_bound hR
      (hZeroNumerator hR)
  · have hRpos : 0 < setup.complexityRadius xStar :=
      lt_of_le_of_ne hRadius_nonneg (Ne.symm hR)
    exact corollary_5_8_sfo_complexity_rate_pos_radius setup xStar h_opt h_bound hRpos

/-- Corollary 5.8 SFO-complexity statement using the paper-facing SFO count and
rate objects.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/rate`.
Quote: `O{ m log ((Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon) + (Psi(x^0) - Psi(x^*) + L_Q V(x^0, x^*)) / epsilon }`.

Book citation: `book/FOML/VarianceReducedMirrorDescent.json#/main_theorem/proof/4/description`.
Quote: `Count total gradient evaluations: each epoch s costs m + T_s component gradient evaluations`.

The proof routes through the deterministic epoch-selection helper above; this
declaration fixes the object layer by exposing the cumulative SFO count and the
displayed rate expression as a genuine asymptotic `O` statement, not an exact
inequality with hidden constant one. -/
theorem corollary_5_8_sfo_complexity_rate
    (setup : VarianceReducedMirrorDescentSetup ι E Ω)
    (xStar : {x : E // x ∈ setup.X})
    (h_opt : ∀ z : {x : E // x ∈ setup.X}, setup.PsiOn xStar ≤ setup.PsiOn z) :
    ∃ callsForAccuracy : ℝ → ℝ,
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∃ S : {S : ℕ // 1 ≤ S},
          (∫ ω, setup.PsiOn (setup.barXCarrier S ω) ∂setup.P -
              setup.PsiOn xStar ≤ ε) ∧
            callsForAccuracy ε = (setup.cumulativeSFOCalls S.1 : ℝ)) ∧
      (callsForAccuracy =O[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ => setup.sfoComplexityRate xStar ε) := by
  exact corollary_5_8_sfo_complexity_rate_from_bound setup xStar h_opt
    (fun S hS => corollary_5_8 setup S hS xStar h_opt)

end VarianceReducedMirrorDescent
