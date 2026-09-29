import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.StochasticOracle
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Martingale
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Subgradient
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Telescope

open MeasureTheory ProbabilityTheory Topology
open scoped Gradient InnerProductSpace BigOperators

/-!
# Stochastic Mirror Descent (Convex, Variable Step Size)

Archetype B algorithm requiring novel Bregman divergence infrastructure.
NO Layer 1 meta-theorems used (explicit Archetype B enforcement).

Reference: Lan, First-order and Stochastic Optimization Methods for Machine Learning, Theorem 4.1
Used in: Final convergence rate theorem
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

-- ============================================================================
-- BREGMAN DIVERGENCE INFRASTRUCTURE
-- ============================================================================

/-- Bregman divergence canonically induced by the distance-generating function `v`.
Ref: Lan, Eq. (3.2.2). -/
noncomputable def V (v : E → ℝ) (x z : E) : ℝ :=
  _root_.bregmanDivergence v x z

/-- Non-negativity of Bregman divergence under 1-strong convexity.
Ref: Lan, Proposition 3.1. -/
theorem V_nonneg {v : E → ℝ} {X : Set E}
    (hv : StrongConvexOn X 1 v)
    (hx : x ∈ X) (hz : z ∈ X)
    (hgrad : HasGradientAt v (∇ v x) x) :
    0 ≤ V v x z := by
  simpa [V] using bregmanDivergence_nonneg_of_strongConvexOn hv hx hz hgrad

/-- Bregman three-point identity (Lan (3.2.6)). -/
theorem bregman_three_point_identity (v : E → ℝ) (x_t x_next x : E) :
    V v x_t x =
      V v x_t x_next + ⟪∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ + V v x_next x := by
  simpa [V] using
    bregmanDivergence_three_point_identity (v := v) (x := x_t) (y := x_next) (z := x)

/-- Helper three-point inequality from an explicit prox optimality witness. -/
theorem lemma_3_4_aux {v : E → ℝ} {X : Set E} {g : E} {x_t x_next x : E} {γ : ℝ}
    (hx_t : x_t ∈ X) (hx_next : x_next ∈ X) (hx : x ∈ X)
    (h_prox_opt : ∀ y ∈ X, ⟪γ • g + ∇ v x_next - ∇ v x_t, y - x_next⟫_ℝ ≥ 0) :
    γ * ⟪g, x_next - x⟫_ℝ + V v x_t x_next ≤ V v x_t x - V v x_next x := by
  simpa [V] using
    mirror_descent_three_point_of_variational
      (v := v) (g := g) (x_t := x_t) (x_next := x_next) (x := x) (γ := γ)
      (show 0 ≤ ⟪γ • g + ∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ from h_prox_opt x hx)

/-- Noise cancellation via martingale difference property.
Ref: Lan, proof of Theorem 4.1, Step 3. -/
theorem noise_inner_condExp_zero_of_vector_condExp_zero
    {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {δ : Ω → E} {x : Ω → E} {x_star : E}
    (h_adapted : Measurable[m] x)
    (h_noise_zero_mean : P[δ | m] =ᵐ[P] 0)
    (hδ_int : Integrable δ P)
    (h_int : Integrable (fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) P) :
    P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m] =ᵐ[P] 0 := by
  exact @condExp_inner_sub_const_eq_zero_of_condExp_eq_zero Ω E mΩ _ _ _ _ _ _ P m δ x x_star
    h_adapted h_noise_zero_mean hδ_int h_int

/-- Noise cancellation via martingale difference property.
Ref: Lan, proof of Theorem 4.1, Step 3. -/
theorem noise_cancellation_lemma
    {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → S} {δ : Ω → E} {x : Ω → E} {x_star : E}
    {t : ℕ}
    (hm_past : (⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›) ≤
      mΩ)
    [SigmaFinite (P.trim hm_past)]
    (h_adapted : Measurable[⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›] x)
    (h_noise_zero_mean : ∀ ω,
      (P[δ | ⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›]) ω = 0)
    (hδ_int : Integrable δ P)
    (h_int : Integrable (fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) P) :
    ∫ ω, ⟪δ ω, x ω - x_star⟫_ℝ ∂P = 0 := by
  let m : MeasurableSpace Ω :=
    ⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›
  have hscalar :
      P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m] =ᵐ[P] 0 := by
    refine noise_inner_condExp_zero_of_vector_condExp_zero
      (P := P) (m := m) hm_past h_adapted ?_ hδ_int h_int
    exact ae_of_all P h_noise_zero_mean
  have htotal :
      ∫ ω, (P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m]) ω ∂P =
        ∫ ω, ⟪δ ω, x ω - x_star⟫_ℝ ∂P :=
    MeasureTheory.integral_condExp (μ := P) (m := m)
      (f := fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) hm_past
  have hleft :
      ∫ ω, (P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m]) ω ∂P = 0 := by
    simpa using integral_congr_ae hscalar
  exact htotal ▸ hleft

/-- Mathlib-facing strengthened form of the martingale-difference cancellation.

This synonym keeps the descriptive side-condition name available for downstream proof
search while the blocker-facing `noise_cancellation_lemma` now exposes the same
Mathlib-required side conditions directly. -/
theorem noise_cancellation_lemma_with_side_conditions
    {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → S} {δ : Ω → E} {x : Ω → E} {x_star : E}
    {t : ℕ}
    (hm_past : (⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›) ≤
      mΩ)
    [SigmaFinite (P.trim hm_past)]
    (h_adapted : Measurable[⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›] x)
    (h_noise_zero_mean : ∀ ω,
      (P[δ | ⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›]) ω = 0)
    (hδ_int : Integrable δ P)
    (h_int : Integrable (fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) P) :
    ∫ ω, ⟪δ ω, x ω - x_star⟫_ℝ ∂P = 0 := by
  let m : MeasurableSpace Ω :=
    ⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›
  have hscalar :
      P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m] =ᵐ[P] 0 := by
    refine noise_inner_condExp_zero_of_vector_condExp_zero
      (P := P) (m := m) hm_past h_adapted ?_ hδ_int h_int
    exact ae_of_all P h_noise_zero_mean
  have htotal :
      ∫ ω, (P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m]) ω ∂P =
        ∫ ω, ⟪δ ω, x ω - x_star⟫_ℝ ∂P :=
    MeasureTheory.integral_condExp (μ := P) (m := m)
      (f := fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) hm_past
  have hleft :
      ∫ ω, (P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m]) ω ∂P = 0 := by
    simpa using integral_congr_ae hscalar
  exact htotal ▸ hleft

/-- Source-backed statement correction for the legacy martingale-cancellation head.

Lan's proof step uses the past sigma algebra, conditional expectation, and integrability
of the oracle noise before applying the unconditional expectation cancellation. This
name records the source-backed correction explicitly for proof search and audit trails. -/
theorem noise_cancellation_lemma_statement_correction
    {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → S} {δ : Ω → E} {x : Ω → E} {x_star : E}
    {t : ℕ}
    (hm_past : (⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›) ≤
      mΩ)
    [SigmaFinite (P.trim hm_past)]
    (h_adapted : Measurable[⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›] x)
    (h_noise_zero_mean : ∀ ω,
      (P[δ | ⨆ i < t, MeasurableSpace.comap (ξ i) ‹MeasurableSpace S›]) ω = 0)
    (hδ_int : Integrable δ P)
    (h_int : Integrable (fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) P) :
    ∫ ω, ⟪δ ω, x ω - x_star⟫_ℝ ∂P = 0 := by
  exact noise_cancellation_lemma_with_side_conditions
    (P := P) (ξ := ξ) (δ := δ) (x := x) (x_star := x_star)
    (t := t) hm_past h_adapted h_noise_zero_mean hδ_int h_int

/-- Mathlib-facing scalar conditional-expectation cancellation.

This is the tractable form of Lan's martingale step:
`E[⟪δ_t, x_t - x⟫ | ξ_[t-1]] = 0` a.e. implies the unconditional expectation is zero.
The vector pullout/adaptedness argument that establishes the scalar conditional expectation is
kept separate from this integration bridge. -/
theorem noise_cancellation_lemma_condExp_ae
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)]
    {Z : Ω → ℝ}
    (h_cond_zero : P[Z | m] =ᵐ[P] 0) :
    ∫ ω, Z ω ∂P = 0 := by
  exact integral_eq_zero_of_condExp_ae_eq_zero (P := P) (m := m) hm h_cond_zero

/-- Scalar martingale-difference cancellation with the adapted multiplier exposed.

This is the Mathlib-facing version of Lan's proof step
`E[⟪δ_t, x_t - x⟫] = 0`: once the inner-product random variable has conditional
expectation zero with respect to the past filtration, `MeasureTheory.integral_condExp`
gives the unconditional cancellation. The multiplier measurability hypothesis is kept
in the statement so the vector pull-out argument can target this theorem directly. -/
theorem noise_cancellation_lemma_scalar_condExp
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)]
    {δ : Ω → E} {x : Ω → E} {x_star : E}
    (h_multiplier_meas : Measurable[m] x)
    (h_int : Integrable (fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) P)
    (h_cond_zero :
      P[(fun ω => ⟪δ ω, x ω - x_star⟫_ℝ) | m] =ᵐ[P] 0) :
    ∫ ω, ⟪δ ω, x ω - x_star⟫_ℝ ∂P = 0 := by
  exact integral_inner_eq_zero_of_scalar_condExp_eq_zero
    (P := P) (m := m) (δ := δ) (x := x) (c := x_star) hm h_cond_zero

/-- Oracle magnitude bound via Young's inequality.
Ref: Lan (4.1.9). -/
theorem oracle_magnitude_bound (G_t g_t δ_t : E) (M : ℝ)
    (h_decomp : G_t = g_t + δ_t)
    (h_g_bound : ‖g_t‖ ≤ M) :
    ‖G_t‖ ^ 2 ≤ 2 * (M ^ 2 + ‖δ_t‖ ^ 2) := by
  exact norm_sq_le_two_mul_sq_add_sq_of_eq_add_of_norm_le G_t g_t δ_t M h_decomp h_g_bound

/-- Telescoping sum for Bregman divergences. -/
theorem telescoping_bregman_sum (v : E → ℝ) (x : ℕ → E) (x_star : E) (s k : ℕ)
    (hsk : s ≤ k) :
    Finset.sum (Finset.Icc s k) (fun t => V v (x t) x_star - V v (x (t + 1)) x_star) =
      V v (x s) x_star - V v (x (k + 1)) x_star := by
  let a : ℕ → ℝ := fun t => V v (x t) x_star
  change (∑ t ∈ Finset.Icc s k, (a t - a (t + 1))) = a s - a (k + 1)
  revert hsk
  refine Nat.le_induction ?base ?step k
  · simp [a]
  · intro n hsn ih
    have hIcc : Finset.Icc s (n + 1) = insert (n + 1) (Finset.Icc s n) := by
      ext t
      simp [Finset.mem_Icc]
      omega
    have hnot : n + 1 ∉ Finset.Icc s n := by
      simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnot]
    rw [ih]
    ring

-- ============================================================================
-- LOCAL SUBDIFFERENTIAL DEFINITION (Mathlib 4.28+ workaround)
-- ============================================================================

/-- Subdifferential of a convex function at a point.
`g ∈ ∂f(w)` iff `f(y) ≥ f(w) + ⟪g, y - w⟫` for all `y`. -/
def subdifferential (_ : Type*) (f : E → ℝ) (w : E) : Set E :=
  SOptLib.subdifferential f w

theorem mem_subdifferential_iff {f : E → ℝ} {w g : E} :
    g ∈ subdifferential ℝ f w ↔ ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ := by
  simpa [subdifferential] using (SOptLib.mem_subdifferential_iff (f := f) (w := w) (g := g))

-- ============================================================================
-- Mirror Descent Setup Structure
-- ============================================================================

/-- Internal ambient totalization of a function canonically defined on the paper carrier
`X`. This is scaffolding for analysis on the ambient space and is not the paper-facing
encoding of the object. -/
noncomputable def totalizeOn {α : Type*} [Zero α] (X : Set E)
    (f : {x : E // x ∈ X} → α) : E → α :=
  SOptLib.totalizeOn X f

/-- The ambient totalization agrees with the paper function on its carrier. -/
theorem totalizeOn_of_mem {α : Type*} [Zero α] (X : Set E)
    (f : {x : E // x ∈ X} → α) {x : E} (hx : x ∈ X) :
    totalizeOn X f x = f ⟨x, hx⟩ := by
  simpa [totalizeOn] using SOptLib.totalizeOn_of_mem X f hx

/-- Restriction of a paper function `f : X → α` to the intrinsic/relative interior
carrier `X^o`. -/
noncomputable def restrictToInterior {α : Type*} (X : Set E)
    (f : {x : E // x ∈ X} → α) : {x : E // x ∈ intrinsicInterior ℝ X} → α :=
  SOptLib.restrictToInterior X f

/-- Internal ambient realization of the paper object `f : X → α` on `X^o`. -/
noncomputable def totalizeOnInterior {α : Type*} [Zero α] (X : Set E)
    (f : {x : E // x ∈ X} → α) : E → α :=
  SOptLib.totalizeOnInterior X f

/-- The intrinsic-interior totalization agrees with the paper function on `Xᵒ`. -/
theorem totalizeOnInterior_of_mem {α : Type*} [Zero α] (X : Set E)
    (f : {x : E // x ∈ X} → α) {x : E} (hx : x ∈ intrinsicInterior ℝ X) :
    totalizeOnInterior X f x = f ⟨x, intrinsicInterior_subset hx⟩ := by
  exact SOptLib.totalizeOnInterior_of_mem X f hx

/-- Paper-facing convexity predicate for functions canonically defined on `X`. -/
def ConvexOnCarrier (X : Set E) (f : {x : E // x ∈ X} → ℝ) : Prop :=
  SOptLib.ConvexOnCarrier X f

/-- Paper-facing `C¹` regularity predicate for `v : X → ℝ`.

Lan states that the distance-generating function is continuously differentiable on `X`,
while the displayed strong-convexity inequality is used on `Xᵒ`.  The predicate records
exactly those two regularity realizations and does not bundle a separate
`UniqueDiffOn ℝ X` premise. -/
def ContDiffOnInterior (X : Set E) (v : {x : E // x ∈ X} → ℝ) : Prop :=
  SOptLib.ContDiffOnInterior X v

/-- Derived differentiability on `X^o` from the paper's `C¹` assumption. -/
def DifferentiableOnInterior (X : Set E) (v : {x : E // x ∈ X} → ℝ) : Prop :=
  SOptLib.DifferentiableOnInterior X v

/-- Lan's `C¹` hypothesis implies differentiability on `X^o`. -/
theorem ContDiffOnInterior.differentiableOn {X : Set E} {v : {x : E // x ∈ X} → ℝ}
    (hv : ContDiffOnInterior X v) :
    DifferentiableOnInterior X v := by
  exact SOptLib.ContDiffOnInterior.differentiableOnInterior hv

/-- Paper-facing strong-convexity predicate for `v : X → ℝ`.

Lan's JSON quote gives the displayed strong-convexity/gradient-monotonicity condition on
`Xᵒ`.  The Lean realization records exactly that Mathlib object, after restricting the
carrier function to the interior. -/
def StrongConvexOnInterior (X : Set E) (μ : ℝ) (v : {x : E // x ∈ X} → ℝ) : Prop :=
  SOptLib.StrongConvexOnInterior X μ v

/-- Affine span of a feasible carrier, used for the intrinsic gradient chart. -/
private abbrev carrierAffineSpan (X : Set E) : AffineSubspace ℝ E :=
  affineSpan ℝ X

/-- Fixed affine chart from the affine-span direction space to the carrier affine span. -/
private noncomputable def carrierChart (X : Set E)
    (anchor : {x : E // x ∈ X}) :
    (carrierAffineSpan X).direction ≃ₜ carrierAffineSpan X := by
  exact SOptLib.carrierAffineSpanChart X anchor

/-- Continuous affine map from the fixed affine-span direction chart back to the ambient
space.  This is the Mathlib object through which chart smoothness is transported. -/
private noncomputable def carrierChartToAmbient (X : Set E)
    (anchor : {x : E // x ∈ X}) :
    (carrierAffineSpan X).direction →ᴬ[ℝ] E := by
  exact SOptLib.carrierChartToAmbient X anchor

/-- The ambient chart map is the affine-span chart followed by the subtype inclusion. -/
private theorem carrierChartToAmbient_apply (X : Set E)
    (anchor : {x : E // x ∈ X}) (u : (carrierAffineSpan X).direction) :
    carrierChartToAmbient X anchor u = ((carrierChart X anchor u : carrierAffineSpan X) : E) := by
  exact SOptLib.carrierChartToAmbient_apply X anchor u

/-- The feasible carrier transported to the fixed affine-span direction chart. -/
private def carrierChartSet (X : Set E) (anchor : {x : E // x ∈ X}) :
    Set (carrierAffineSpan X).direction :=
  SOptLib.carrierChartSet X anchor

@[simp] private theorem mem_carrierChartSet_iff (X : Set E)
    (anchor : {x : E // x ∈ X}) (u : (carrierAffineSpan X).direction) :
    u ∈ carrierChartSet X anchor ↔ carrierChartToAmbient X anchor u ∈ X := by
  rfl

/-- The paper function `v : X → ℝ`, totalized and transported to the fixed carrier chart. -/
private noncomputable def carrierChartFunction (X : Set E)
    (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X}) :
    (carrierAffineSpan X).direction → ℝ :=
  SOptLib.carrierChartFunction X v anchor

/-- Coordinates of a feasible point in the fixed affine-span chart. -/
private noncomputable def carrierChartPoint (X : Set E) (anchor : {x : E // x ∈ X})
    (x : {x : E // x ∈ X}) : (carrierAffineSpan X).direction :=
  SOptLib.carrierChartPoint X anchor x

/-- The fixed affine-span chart transports convex feasible carriers to convex chart sets. -/
private theorem carrierChartSet_convex (X : Set E) (anchor : {x : E // x ∈ X})
    (hX : Convex ℝ X) :
    Convex ℝ (carrierChartSet X anchor) := by
  exact SOptLib.carrierChartSet_convex X anchor hX

/-- The charted feasible carrier has nonempty interior in its affine-span direction space. -/
private theorem carrierChartSet_interior_nonempty (X : Set E)
    (anchor : {x : E // x ∈ X}) (hX : Convex ℝ X) :
    (interior (carrierChartSet X anchor)).Nonempty := by
  simpa [carrierChartSet] using SOptLib.carrierChartSet_interior_nonempty X anchor hX

/-- The charted feasible carrier has unique tangent directions. -/
private theorem carrierChartSet_uniqueDiffOn (X : Set E)
    (anchor : {x : E // x ∈ X}) (hX : Convex ℝ X) :
    UniqueDiffOn ℝ (carrierChartSet X anchor) := by
  simpa [carrierChartSet] using SOptLib.carrierChartSet_uniqueDiffOn X anchor hX

/-- The paper `C¹` hypothesis on `v : X → ℝ`, transported to the fixed affine-span chart. -/
private theorem carrierChartFunction_contDiffOn (X : Set E)
    (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X})
    (hv : ContDiffOn ℝ 1 (totalizeOn X v) X) :
    ContDiffOn ℝ 1 (carrierChartFunction X v anchor) (carrierChartSet X anchor) := by
  simpa [carrierChartFunction, carrierChartSet] using
    SOptLib.carrierChartFunction_contDiffOn X v anchor hv

/-- Internal relative-gradient realization for a carrier function from a fixed chart anchor.

The paper's `∇v(x)` is a derivative along the feasible carrier.  For lower-dimensional
convex carriers, the ambient within-gradient is not canonical; the canonical Lean
realization differentiates in the direction space of `affineSpan ℝ X` and then includes
that relative gradient back into the ambient Euclidean space.  The chart anchor is fixed
for a setup by the paper's initial point `x₁`; this keeps the derivative selector a single
Mathlib `gradientWithin` over a fixed domain, so continuity is routed through
`ContDiffOn.continuousOn_fderivWithin`. -/
private noncomputable def carrierGradientFrom (X : Set E)
    (v : {x : E // x ∈ X} → ℝ) (anchor x : {x : E // x ∈ X}) : E :=
  SOptLib.carrierGradientFrom X v anchor x

/-- Backwards-compatible relative-gradient notation, anchored at the base point itself.
Setup-level objects use `carrierGradientFrom` with the paper initial point as fixed anchor. -/
private noncomputable def carrierGradient (X : Set E)
    (v : {x : E // x ∈ X} → ℝ) (x : {x : E // x ∈ X}) : E :=
  SOptLib.carrierGradient X v x

/-- Feasible displacements lie in the direction space of the carrier affine span. -/
private theorem feasible_difference_mem_carrier_direction (X : Set E)
    (x z : {x : E // x ∈ X}) :
    z.1 - x.1 ∈ (carrierAffineSpan X).direction := by
  exact SOptLib.vsub_mem_carrierAffineSpan_direction X x z

/-- The fixed chart sends the chart coordinate of a feasible point back to that point. -/
private theorem carrierChartToAmbient_chartPoint (X : Set E)
    (anchor x : {x : E // x ∈ X}) :
    carrierChartToAmbient X anchor (carrierChartPoint X anchor x) = x.1 := by
  exact SOptLib.carrierChartToAmbient_chartPoint X anchor x

/-- Intrinsic-interior feasible points are ordinary interior points after transporting the
carrier to the fixed affine-span direction chart. -/
private theorem carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior (X : Set E)
    (anchor x : {x : E // x ∈ X}) (hX : Convex ℝ X)
    (hx : x.1 ∈ intrinsicInterior ℝ X) :
    carrierChartPoint X anchor x ∈ interior (carrierChartSet X anchor) := by
  simpa [carrierChartPoint, carrierChartSet] using
    SOptLib.carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior X anchor x hx

/-- Chart-interior points correspond exactly to intrinsic-interior ambient points. -/
private theorem carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
    (X : Set E) (anchor : {x : E // x ∈ X})
    {u : (carrierAffineSpan X).direction}
    (hu : u ∈ interior (carrierChartSet X anchor)) :
    carrierChartToAmbient X anchor u ∈ intrinsicInterior ℝ X := by
  simpa [carrierChartSet, carrierChartToAmbient] using
    SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet X anchor hu

/-- The remaining local calculus bridge: chart and ambient within-derivatives agree on a
feasible affine-span displacement from an intrinsic-interior base point. -/
private theorem chart_fderiv_eq_ambient_fderivWithin_on_feasible_direction
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (anchor x z : {x : E // x ∈ X})
    (hX : Convex ℝ X)
    (hvX : ContDiffOn ℝ 1 (totalizeOn X v) X)
    (hvInt : ContDiffOn ℝ 1 (totalizeOnInterior X v) (intrinsicInterior ℝ X))
    (hx : x.1 ∈ intrinsicInterior ℝ X) :
    (fderivWithin ℝ (carrierChartFunction X v anchor) (carrierChartSet X anchor)
        (carrierChartPoint X anchor x))
      (⟨z.1 - x.1, feasible_difference_mem_carrier_direction X x z⟩ :
        (carrierAffineSpan X).direction) =
      (fderivWithin ℝ (totalizeOnInterior X v) (intrinsicInterior ℝ X) x.1) (z.1 - x.1) := by
  simpa [carrierAffineSpan, carrierChartFunction, carrierChartSet, carrierChartPoint,
    feasible_difference_mem_carrier_direction, totalizeOnInterior] using
    SOptLib.carrierChart_fderivWithin_eq_intrinsicInterior_fderivWithin_on_feasible_direction
      (X := X) (v := v) (anchor := anchor) (x := x) (z := z) hvInt hx

/-- The fixed affine-span coordinate of a feasible point lies in the charted carrier. -/
private theorem carrierChartPoint_mem (X : Set E) (anchor : {x : E // x ∈ X})
    (x : {x : E // x ∈ X}) :
    carrierChartPoint X anchor x ∈ carrierChartSet X anchor := by
  exact SOptLib.carrierChartPoint_mem X anchor x

/-- The fixed affine-span coordinate map is continuous on the feasible carrier subtype. -/
private theorem carrierChartPoint_continuous (X : Set E) (anchor : {x : E // x ∈ X}) :
    Continuous (fun x : {x : E // x ∈ X} => carrierChartPoint X anchor x) := by
  simpa [carrierChartPoint] using SOptLib.carrierChartPoint_continuous X anchor

/-- Continuity of the affine-span relative gradient selected by `carrierGradientFrom`. -/
private theorem carrierGradientFrom_continuous (X : Set E)
    (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X})
    (hX : Convex ℝ X) (hv : ContDiffOn ℝ 1 (totalizeOn X v) X) :
    Continuous (fun x : {x : E // x ∈ X} => carrierGradientFrom X v anchor x) := by
  simpa [carrierGradientFrom, totalizeOn] using
    SOptLib.carrierGradientFrom_continuous (X := X) (v := v) (anchor := anchor) hX hv

/-- Paper-facing subdifferential `∂f(x)` for `f : X → ℝ`, quantifying only over
the paper carrier `X`. -/
def carrierSubdifferential (X : Set E) (f : {x : E // x ∈ X} → ℝ)
    (w : {x : E // x ∈ X}) : Set E :=
  SOptLib.carrierSubdifferential f w

theorem mem_carrierSubdifferential_iff {X : Set E} {f : {x : E // x ∈ X} → ℝ}
    {w : {x : E // x ∈ X}} {g : E} :
    g ∈ carrierSubdifferential X f w ↔
      ∀ y : {x : E // x ∈ X}, f y ≥ f w + ⟪g, y.1 - w.1⟫_ℝ := by
  simpa [carrierSubdifferential] using
    (SOptLib.mem_carrierSubdifferential_iff (f := f) (w := w) (g := g))

/-- Paper-facing decision space `ℝ^m`. -/
abbrev DecisionSpace (m : ℕ) : Type :=
  EuclideanSpace ℝ (Fin m)

/-- Paper-facing sample space `ℝ^d`. -/
abbrev SampleSpace (d : ℕ) : Type :=
  EuclideanSpace ℝ (Fin d)

section AliasMeasurableSpaces

local instance instMeasurableSpaceDecisionSpace (m : ℕ) :
    MeasurableSpace (DecisionSpace m) :=
  borel (DecisionSpace m)

local instance instBorelSpaceDecisionSpace (m : ℕ) :
    BorelSpace (DecisionSpace m) :=
  ⟨rfl⟩

local instance instMeasurableSpaceSampleSpace (d : ℕ) :
    MeasurableSpace (SampleSpace d) :=
  borel (SampleSpace d)

local instance instBorelSpaceSampleSpace (d : ℕ) :
    BorelSpace (SampleSpace d) :=
  ⟨rfl⟩

/-- `book/FOML/StochasticMirrorDescent.json#/assumptions/4/math` and
`#/assumptions/6/math` use the dual norm `‖·‖_*` on oracle values.

In this formalization the paper space is specialized to the Euclidean model
`DecisionSpace m = ℝ^m`, so the source-facing dual norm is realized by the ambient
Euclidean norm via self-duality. -/
noncomputable def dualNorm {m : ℕ} (g : DecisionSpace m) : ℝ :=
  SOptLib.dualNorm g

/-- Bridge theorem documenting the Euclidean self-dual realization of the paper norm
`‖·‖_*`. -/
theorem dualNorm_eq_norm {m : ℕ} (g : DecisionSpace m) :
    dualNorm g = ‖g‖ :=
  rfl

/-- Squared dual norms are the squared Euclidean norms in this Euclidean
specialization. -/
theorem dualNorm_sq_eq_norm_sq {m : ℕ} (g : DecisionSpace m) :
    dualNorm g ^ 2 = ‖g‖ ^ 2 :=
  rfl

/-- Paper-facing deterministic data for stochastic mirror descent.

The canonical mathematical objects live directly on the feasible-domain carrier `X`:
the initial point `x₁`, the distance-generating function `v`, the loss kernel `F`,
the stochastic oracle kernel `G`, and the step-size sequence `γ_t`. -/
structure MirrorDescentSetup (m d : ℕ) where
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  X : Set (DecisionSpace m)
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  Ξ : Set (SampleSpace d)
  /-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization/math` ::
  `"x_1 ∈ X"`. -/
  x1 : {x : DecisionSpace m // x ∈ X}
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/math` ::
  `"v : X → ℝ is continuously differentiable and 1-strongly convex ..."` -/
  v : {x : DecisionSpace m // x ∈ X} → ℝ
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  F : {x : DecisionSpace m // x ∈ X} → {ξ : SampleSpace d // ξ ∈ Ξ} → ℝ
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. This records the measurable
  kernel structure needed to transport expectations along identically distributed
  samples. -/
  hF_measurable :
    ∀ x : {x : DecisionSpace m // x ∈ X}, Measurable (F x)
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"F : X × Ξ → ℝ"` and `#/setup/problem/math` ::
  `"f(x) := E[F(x, ξ)]"`. This is the stochastic-kernel measurability structure
  needed to view the objective integrand at random feasible decisions. -/
  hF_joint_measurable :
    Measurable (fun p : {x : DecisionSpace m // x ∈ X} × {ξ : SampleSpace d // ξ ∈ Ξ} =>
      F p.1 p.2)
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/2/math` ::
  `"∀ x ∈ X, ξ ∈ Ξ, the SFO returns G(x, ξ) such that g(x) := E[G(x, ξ)] is well defined"`. -/
  oracle : {x : DecisionSpace m // x ∈ X} → {ξ : SampleSpace d // ξ ∈ Ξ} → DecisionSpace m
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/2/math` ::
  `"∀ x ∈ X, ξ ∈ Ξ, the SFO returns G(x, ξ) such that g(x) := E[G(x, ξ)] is well defined"`.
  This records the measurable oracle kernel structure used by the expectation API. -/
  h_oracle_measurable :
    ∀ x : {x : DecisionSpace m // x ∈ X}, Measurable (oracle x)
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/2/math` ::
  `"∀ x ∈ X, ξ ∈ Ξ, the SFO returns G(x, ξ) such that g(x) := E[G(x, ξ)] is well defined"`.
  This records the joint stochastic-kernel measurability needed at random iterates. -/
  h_oracle_joint_measurable :
    Measurable
      (fun p : {x : DecisionSpace m // x ∈ X} × {ξ : SampleSpace d // ξ ∈ Ξ} =>
        oracle p.1 p.2)
  /-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters/0/math` ::
  `"γ_t > 0 (variable step sizes; optimal constant choice: γ_t = D_X / √(k(M^2 + σ^2)))"`. -/
  γ : {t : ℕ // 1 ≤ t} → ℝ
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  hX_bounded : Bornology.IsBounded X
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  hX_closed : IsClosed X
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  hX_convex : Convex ℝ X
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/math` ::
  `"v : X → ℝ is continuously differentiable ... ∀ x', x ∈ X^o"` -/
  hv_contDiff_on_interior : ContDiffOnInterior X v
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/math` ::
  `"v : X → ℝ ... is 1-strongly convex ... ∀ x', x ∈ X^o"` -/
  hv_strong_convex_on_interior : StrongConvexOnInterior X 1 v
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/math` ::
  `"v : X → ℝ is continuously differentiable"` and
  `#/algorithm_spec/parameters/2/math` ::
  `"V(x, z) = v(z) - [v(x) + ⟨∇v(x), z - x⟩]"`. -/
  hv_measurable : Measurable v
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/0/math` ::
  `"F(·, ξ) is convex on X for every ξ ∈ Ξ"` -/
  hF_convex : ∀ s, ConvexOnCarrier X (fun x => F x s)
  /-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters/0/math` ::
  `"γ_t > 0 (variable step sizes; optimal constant choice: γ_t = D_X / √(k(M^2 + σ^2)))"`. -/
  hγ_pos : ∀ t : {t : ℕ // 1 ≤ t}, 0 < γ t
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/parameters/0` ::
  `"D_X^2 := max_{x_1, x ∈ X} V(x_1, x)"`.

  This records the maximizing pair named by the paper's `max` notation. The displayed formula is
  the same boundary-safe relative-interior gradient Bregman realization exported below as
  `MirrorDescentSetup.V`. -/
  DXSqMaximizer : ({x : DecisionSpace m // x ∈ X} × {x : DecisionSpace m // x ∈ X})
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/parameters/0` ::
  `"D_X^2 := max_{x_1, x ∈ X} V(x_1, x)"`. -/
  hDXSqMaximizer_max :
    ∀ q : ({x : DecisionSpace m // x ∈ X} × {x : DecisionSpace m // x ∈ X}),
      v q.2 - v q.1 -
          ⟪carrierGradientFrom X v x1 q.1, q.2.1 - q.1.1⟫_ℝ ≤
        v DXSqMaximizer.2 - v DXSqMaximizer.1 -
          ⟪carrierGradientFrom X v x1 DXSqMaximizer.1,
            DXSqMaximizer.2.1 - DXSqMaximizer.1.1⟫_ℝ

/-- Internal kernel realizing the paper integrand `F(x, ξ)` along the random vector `ξ`. -/
def objectiveKernel {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : Ω → ℝ :=
  fun ω => setup.F x (ξ ω)

/-- Paper-level well-definedness predicate for `f(x) := E[F(x, ξ)]`. -/
def objectiveWellDefined {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : Prop :=
  Integrable (objectiveKernel setup ξ x)

/-- The paper objective `f(x) := E[F(x, ξ)]`. -/
noncomputable def objectiveExpectation {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : ℝ :=
  SOptLib.objectiveExpectation volume setup.F ξ x

/-- Internal kernel realizing the paper oracle output `G(x, ξ)` along `ξ`. -/
def oracleKernel {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : Ω → DecisionSpace m :=
  fun ω => setup.oracle x (ξ ω)

/-- Paper-level well-definedness predicate for `g(x) := E[G(x, ξ)]`. -/
def oracleWellDefined {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : Prop :=
  Integrable (oracleKernel setup ξ x)

/-- The paper mean oracle `g(x) := E[G(x, ξ)]`. -/
noncomputable def oracleMean {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : DecisionSpace m :=
  SOptLib.oracleMean volume setup.oracle ξ x

/-- Internal kernel realizing the squared oracle deviation around the paper mean `g(x)`. -/
noncomputable def oracleVarianceKernel {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : Ω → ℝ :=
  SOptLib.oracleVarianceKernel volume setup.oracle ξ dualNorm x

/-- Paper-level well-definedness predicate for the bounded-variance expectation. -/
def oracleVarianceWellDefined {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : Prop :=
  SOptLib.oracleVarianceWellDefined volume setup.oracle ξ dualNorm x

/-- The paper variance expression `E[‖G(x, ξ) - g(x)‖_*²]`. -/
noncomputable def oracleVariance {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) : ℝ :=
  SOptLib.oracleVariance volume setup.oracle ξ dualNorm x

/-- Internal kernel realizing Assumption 3b on the sampled random vector `ξ_t`. -/
noncomputable def oracleSampleVarianceKernel {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) (t : {t : ℕ // 1 ≤ t}) : Ω → ℝ :=
  SOptLib.oracleSampleVarianceKernel volume setup.oracle ξ ξt dualNorm x t

/-- Paper-level well-definedness predicate for the sampled bounded-variance expectation. -/
def oracleSampleVarianceWellDefined {m d : ℕ} (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) (t : {t : ℕ // 1 ≤ t}) : Prop :=
  SOptLib.oracleSampleVarianceWellDefined volume setup.oracle ξ ξt dualNorm x t

/-- Assumption 3b's sampled expectation `E[‖G(x, ξ_t) - f'(x)‖_*²]`. -/
noncomputable def oracleSampleVariance {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (x : {x : DecisionSpace m // x ∈ setup.X}) (t : {t : ℕ // 1 ≤ t}) : ℝ :=
  SOptLib.oracleSampleVariance volume setup.oracle ξ ξt dualNorm x t

/-- Internal kernel for the random-iterate version of Lan's variance term
`‖G(x_t, ξ_t) - g(x_t)‖_*²`. -/
noncomputable def oracleRandomIterateVarianceKernel {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (xProcess : {t : ℕ // 1 ≤ t} → Ω → {x : DecisionSpace m // x ∈ setup.X})
    (t : {t : ℕ // 1 ≤ t}) : Ω → ℝ :=
  SOptLib.oracleRandomIterateVarianceKernel volume setup.oracle ξ ξt xProcess dualNorm t

/-- Paper-level well-definedness predicate for the random-iterate variance expectation. -/
def oracleRandomIterateVarianceWellDefined {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (xProcess : {t : ℕ // 1 ≤ t} → Ω → {x : DecisionSpace m // x ∈ setup.X})
    (t : {t : ℕ // 1 ≤ t}) : Prop :=
  SOptLib.oracleRandomIterateVarianceWellDefined volume setup.oracle ξ ξt xProcess dualNorm t

/-- Source-facing realization of Lan's random-iterate variance bound
`E[‖δ_t‖_*²] ≤ σ²`, with the expectation well-defined. -/
noncomputable def oracleRandomIterateVarianceBound {m d : ℕ}
    (setup : MirrorDescentSetup m d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ})
    (xProcess : {t : ℕ // 1 ≤ t} → Ω → {x : DecisionSpace m // x ∈ setup.X})
    (sigmaSq : ℝ) (t : {t : ℕ // 1 ≤ t}) : Prop :=
  SOptLib.oracleRandomIterateVarianceBound volume setup.oracle
    (oracleMean setup ξ) xProcess ξt dualNorm sigmaSq t

namespace MirrorDescentSetup

variable {m d : ℕ}
variable (setup : MirrorDescentSetup m d)

/-- The paper carrier `X`. -/
abbrev Point : Type _ :=
  {x : DecisionSpace m // x ∈ setup.X}

/-- Paper time indices `t = 1, 2, ...`. -/
abbrev Time : Type _ :=
  {t : ℕ // 1 ≤ t}

/-- Paper sample carrier `Ξ`. -/
abbrev Sample : Type _ :=
  {ξ : SampleSpace d // ξ ∈ setup.Ξ}

/-- The topological interior carrier used by theorem heads that state explicit
ambient-interior hypotheses. The regularity predicates above use Mathlib's
`intrinsicInterior`; topological interior points are routed into that intrinsic carrier
by `interior_subset_intrinsicInterior` when needed. -/
abbrev InteriorPoint : Type _ :=
  SOptLib.InteriorCarrierPoint setup.X

/-- The relative/interior carrier `X^o` used by Lan's differentiability and
strong-convexity assumptions, realized as Mathlib's `intrinsicInterior`. -/
abbrev IntrinsicInteriorPoint : Type _ :=
  SOptLib.IntrinsicInteriorCarrierPoint setup.X

/-- A paper output window `[s, k]` with `1 ≤ s ≤ k`. -/
abbrev OutputWindow : Type :=
  SOptLib.PositiveOutputWindow

namespace OutputWindow

abbrev mk (start stop : ℕ) (start_pos : 1 ≤ start) (le_stop : start ≤ stop) :
    OutputWindow :=
  SOptLib.PositiveOutputWindow.mk start stop start_pos le_stop

abbrev start (w : OutputWindow) : ℕ :=
  SOptLib.PositiveOutputWindow.start w

abbrev stop (w : OutputWindow) : ℕ :=
  SOptLib.PositiveOutputWindow.stop w

abbrev start_pos (w : OutputWindow) : 1 ≤ w.start :=
  SOptLib.PositiveOutputWindow.start_pos w

abbrev le_stop (w : OutputWindow) : w.start ≤ w.stop :=
  SOptLib.PositiveOutputWindow.le_stop w

end OutputWindow

/-- The first paper time index. -/
def timeOne : Time :=
  SOptLib.positiveTimeOne

/-- The successor paper time index. -/
def nextTime (t : Time) : Time :=
  SOptLib.positiveTimeSucc t

/-- Internal bridge from zero-based recursion counters to paper times. -/
def natSuccTime (t : ℕ) : Time :=
  SOptLib.natSuccPositiveTime t

/-- Forgetful map from `X^o` to the feasible carrier `X`. -/
def InteriorPoint.toPoint (x : setup.InteriorPoint) : setup.Point :=
  ⟨x.1, interior_subset x.2⟩

/-- Forgetful map from the relative/interior carrier to the feasible carrier `X`. -/
def IntrinsicInteriorPoint.toPoint (x : setup.IntrinsicInteriorPoint) : setup.Point :=
  ⟨x.1, intrinsicInterior_subset x.2⟩

/-- The initial time of an output window. -/
def OutputWindow.startTime (w : OutputWindow) : Time :=
  SOptLib.PositiveOutputWindow.startTime w

/-- The paper times appearing in an output window. -/
def outputTimes (w : OutputWindow) : Finset Time :=
  SOptLib.PositiveOutputWindow.times w

/-- Reindex a finite sum over a paper output window back to the underlying natural
interval. The conditional proof term keeps the statement independent of any
particular proof of membership in the interval. -/
theorem outputTimes_sum_eq_Icc {α : Type*} [AddCommMonoid α]
    (w : OutputWindow) (φ : Time → α) :
    Finset.sum (outputTimes w) φ =
      Finset.sum (Finset.Icc w.start w.stop) (fun n =>
        if hn : n ∈ Finset.Icc w.start w.stop then
          φ ⟨n, le_trans w.start_pos (Finset.mem_Icc.mp hn).1⟩
        else 0) := by
  simpa [outputTimes] using SOptLib.PositiveOutputWindow.sum_times_eq_Icc w φ

/-- Internal ambient extension of the paper distance-generating function. -/
private noncomputable def vAmbient : DecisionSpace m → ℝ :=
  SOptLib.carrierPotentialAmbient setup.X setup.v

/-- Internal ambient realization of the paper distance-generating function on `X^o`. -/
private noncomputable def vInteriorAmbient : DecisionSpace m → ℝ :=
  SOptLib.carrierPotentialInteriorAmbient setup.X setup.v

/-- Internal ambient extension of the paper loss kernel. -/
noncomputable def FAmbient (s : setup.Sample) : DecisionSpace m → ℝ :=
  SOptLib.totalizeOn setup.X (fun x => setup.F x s)

/-- Internal ambient extension of the paper oracle kernel. -/
noncomputable def oracleAmbient (s : setup.Sample) : DecisionSpace m → DecisionSpace m :=
  SOptLib.totalizeOn setup.X (fun x => setup.oracle x s)

/-- Internal Lean-only boundary extension of Lan's gradient notation.

Lan justifies `∇v(x)` on `Xᵒ`, interpreted here as the relative/intrinsic interior.
The all-carrier public `V` therefore extends that relative-interior within-gradient
to boundary points. On ambient topological interior points it agrees with the literal
ambient gradient by local equality of the carrier totalization. -/
private noncomputable def vGradExtension (x : setup.Point) : DecisionSpace m :=
  SOptLib.carrierGradientFrom setup.X setup.v setup.x1 x

/-- Literal relative gradient on `Xᵒ`.

Lan's `∇v(x)` in the Bregman formula is the gradient intrinsic to the feasible carrier.
For lower-dimensional feasible sets this is not Mathlib's ambient `gradientWithin`
selector; it is the affine-span relative gradient used by `vGradExtension`. -/
private noncomputable def vIntrinsicGradient (x : setup.IntrinsicInteriorPoint) :
    DecisionSpace m :=
  SOptLib.carrierIntrinsicGradient setup.X setup.v setup.x1 x

/-- Internal Lean realization of the Bregman formula on all of `X × X`.

The public object is `V`; this private definition keeps the paper formula centralized
behind the paper-facing name and bridge theorems. -/
private noncomputable def extendedV (x z : setup.Point) : ℝ :=
  carrierBregmanFormula setup.v (fun y : setup.Point => y.1)
    (fun y : setup.Point => setup.vGradExtension y) x z

/-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters/2/math` ::
`"V(x, z) = v(z) - [v(x) + ⟨∇v(x), z - x⟩] (Bregman divergence associated with v)"`.

The public paper object lives on `X × X`. Lean uses the boundary-safe Mathlib
relative-interior within-gradient on all feasible base points; literal formulas are
exported on both the ambient topological interior and the intrinsic-interior carrier. -/
noncomputable def V (x z : setup.Point) : ℝ :=
  carrierBregmanDivergence setup.v (fun x => setup.vGradExtension x) x z

/-- Internal expansion of the ambient realization used to define the public divergence. -/
private theorem extendedV_def (x z : setup.Point) :
    setup.extendedV x z =
      setup.v z - setup.v x - ⟪setup.vGradExtension x, z.1 - x.1⟫_ℝ := by
  exact carrierBregmanFormula_def setup.v (fun y : setup.Point => y.1)
    (fun y : setup.Point => setup.vGradExtension y) x z

/-- Literal Bregman formula on interior base points, where Lan's `∇v(x)` notation is
directly justified. -/
noncomputable def literalV (x : setup.InteriorPoint) (z : setup.Point) : ℝ :=
  setup.v z - setup.v x.toPoint - ⟪∇ setup.vInteriorAmbient x.1, z.1 - x.1⟫_ℝ

/-- Literal Bregman formula on the relative/interior carrier, using Mathlib's
intrinsic affine-span gradient on `intrinsicInterior ℝ X`. -/
noncomputable def literalVIntrinsic (x : setup.IntrinsicInteriorPoint) (z : setup.Point) : ℝ :=
  setup.v z - setup.v x.toPoint -
    ⟪setup.vIntrinsicGradient x, z.1 - x.1⟫_ℝ

/-- Interior `C¹` regularity of the paper distance-generating function. -/
theorem v_c1_on_interior :
    ContDiffOn ℝ 1 setup.vInteriorAmbient (intrinsicInterior ℝ setup.X) := by
  simpa [vInteriorAmbient] using
    SOptLib.carrierPotential_contDiffOn_intrinsicInterior setup.hv_contDiff_on_interior

/-- Interior differentiability of the paper distance-generating function. -/
theorem v_differentiableOn_interior :
    DifferentiableOn ℝ setup.vInteriorAmbient (intrinsicInterior ℝ setup.X) := by
  exact DifferentiableOn.of_contDiffOn_one_intrinsicInterior setup.X setup.vInteriorAmbient
    setup.v_c1_on_interior

/-- Interior strong convexity of the paper distance-generating function. -/
theorem v_strong_convex_on_interior :
    StrongConvexOn (intrinsicInterior ℝ setup.X) 1 setup.vInteriorAmbient := by
  simpa [vInteriorAmbient] using
    (SOptLib.carrierPotential_strongConvexOn_intrinsicInterior
      (X := setup.X) (v := setup.v) (μ := (1 : ℝ))
      setup.hv_strong_convex_on_interior)

/-- On interior base points, the within-gradient extension agrees with Lan's literal ambient
gradient. This theorem bridges the public `X × X` divergence back to the literal paper
formula on `X^o × X`. -/
theorem vGradExtension_eq_literal_of_interior (x : setup.InteriorPoint) :
    setup.vGradExtension x.toPoint = ∇ setup.vInteriorAmbient x.1 := by
  apply ext_inner_right ℝ
  intro y
  refine
    (inner_eq_of_eq_on_displacements_of_mem_interior
      (X := setup.X) (x := x.1) (a := setup.vGradExtension x.toPoint)
      (b := ∇ setup.vInteriorAmbient x.1) x.2 ?_ y)
  intro z hz
  have hinner :
      ⟪setup.vGradExtension x.toPoint, z - x.1⟫_ℝ =
        ⟪gradientWithin setup.vInteriorAmbient (intrinsicInterior ℝ setup.X) x.1, z - x.1⟫_ℝ := by
    simpa [vGradExtension, InteriorPoint.toPoint] using
      SOptLib.carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior
        (X := setup.X) (v := setup.v) (vInterior := setup.vInteriorAmbient)
        (anchor := setup.x1) (x := x.toPoint) (z := ⟨z, hz⟩)
        setup.hX_convex setup.hv_contDiff_on_interior.1
        (by
          intro w hw
          simpa [vInteriorAmbient] using totalizeOnInterior_of_mem setup.X setup.v hw)
        (interior_subset_intrinsicInterior x.2)
  have hgrad :
      gradientWithin setup.vInteriorAmbient (intrinsicInterior ℝ setup.X) x.1 =
        ∇ setup.vInteriorAmbient x.1 := by
    have hmem : intrinsicInterior ℝ setup.X ∈ 𝓝 x.1 := by
      exact Filter.mem_of_superset
        (IsOpen.mem_nhds isOpen_interior x.2)
        (fun w hw => interior_subset_intrinsicInterior hw)
    rw [gradientWithin, gradient, fderivWithin_of_mem_nhds hmem]
  simpa [hgrad] using hinner

/-- On relative-interior base points, the all-carrier extension agrees with the
literal relative gradient used for Lan's `∇v(x)` notation on `Xᵒ`.

This is the semantic bridge from the all-carrier boundary extension back to Lan's
relative-interior formula. -/
theorem vGradExtension_eq_literal_of_intrinsicInterior
    (x : setup.IntrinsicInteriorPoint) :
    setup.vGradExtension x.toPoint = setup.vIntrinsicGradient x := by
  simpa [vGradExtension, vIntrinsicGradient] using
    (SOptLib.carrierGradientFrom_eq_intrinsicGradient
      (X := setup.X) (v := setup.v) (anchor := setup.x1) (x := x))

/-- Directional bridge between the intrinsic affine-span gradient and Mathlib's ambient
`gradientWithin` selector.

The vector equality is not available for lower-dimensional carriers, but feasible
directions only see the affine-span component. This is the exact bridge needed by the
`StrongConvexOn` lower-bound route below. -/
theorem vGradExtension_inner_eq_gradientWithin_intrinsicInterior
    (x z : setup.Point) (hx : x.1 ∈ intrinsicInterior ℝ setup.X) :
    ⟪setup.vGradExtension x, z.1 - x.1⟫_ℝ =
      ⟪gradientWithin setup.vInteriorAmbient (intrinsicInterior ℝ setup.X) x.1,
        z.1 - x.1⟫_ℝ := by
  simpa [vGradExtension] using
    SOptLib.carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior
      (X := setup.X) (v := setup.v) (vInterior := setup.vInteriorAmbient)
      setup.x1 x z setup.hX_convex setup.hv_contDiff_on_interior.1
      (by
        intro y hy
        simpa [vInteriorAmbient] using totalizeOnInterior_of_mem setup.X setup.v hy)
      hx

/-- The paper initial point `x₁ ∈ X`. -/
abbrev x1Point : setup.Point := setup.x1

/-- The paper step size sequence `γ_t`, indexed on the paper times `t = 1, 2, ...`. -/
def stepSize (setup : MirrorDescentSetup m d) (t : Time) : ℝ :=
  SOptLib.stepSize setup.γ t

/-- On paper indices, the public step size object is exactly the primitive field `γ_t`. -/
theorem stepSize_eq_gamma (t : Time) :
    setup.stepSize t = setup.γ t := by
  simpa [MirrorDescentSetup.stepSize] using
    (SOptLib.stepSize_eq_gamma (γ := setup.γ) (t := t))

/-- Positivity of the paper step sizes. -/
theorem stepSize_pos (t : Time) :
    0 < setup.stepSize t := by
  simpa [MirrorDescentSetup.stepSize] using
    (SOptLib.stepSize_pos (γ := setup.γ) (t := t) (hγ_pos := setup.hγ_pos))

/-- The paper feasible set `X` is compact by Heine-Borel from Lan's closed and bounded
hypotheses in the finite-dimensional Euclidean realization. -/
theorem X_isCompact : IsCompact setup.X := by
  exact Metric.isCompact_iff_isClosed_bounded.2 ⟨setup.hX_closed, setup.hX_bounded⟩

/-- The feasible-carrier subtype is compact. -/
theorem point_univ_isCompact : IsCompact (Set.univ : Set setup.Point) := by
  haveI : CompactSpace setup.Point := isCompact_iff_compactSpace.mp setup.X_isCompact
  exact isCompact_univ

/-- The product carrier `X × X` is compact. -/
theorem pointProd_univ_isCompact :
    IsCompact (Set.univ : Set (setup.Point × setup.Point)) := by
  haveI : CompactSpace setup.Point := isCompact_iff_compactSpace.mp setup.X_isCompact
  exact isCompact_univ

/-- Mathlib route to continuity of the boundary-safe gradient extension when the carrier
has unique tangent directions.

This is not a setup assumption: it isolates the exact extra geometric premise needed to use
`ContDiffOn.continuousOn_fderivWithin` for the within-gradient on a possibly-boundary
carrier. -/
theorem vGradExtension_continuous_of_uniqueDiffOn
    (huniq : UniqueDiffOn ℝ setup.X) :
    Continuous (fun x : setup.Point => setup.vGradExtension x) := by
  exact carrierGradientFrom_continuous setup.X setup.v setup.x1
    setup.hX_convex setup.hv_contDiff_on_interior.2

/-- Continuity of the paper gradient extension on the feasible carrier. -/
theorem vGradExtension_continuous :
    Continuous (fun x : setup.Point => setup.vGradExtension x) := by
  exact carrierGradientFrom_continuous setup.X setup.v setup.x1
    setup.hX_convex setup.hv_contDiff_on_interior.2

/-- The paper distance-generating function is continuous on the feasible carrier. -/
theorem v_continuous_carrier :
    Continuous setup.v := by
  exact continuous_subtype_of_continuousOn_ambient setup.v setup.vAmbient
    setup.hv_contDiff_on_interior.2.continuousOn
    (by intro x; simp [vAmbient])

/-- Source-backed continuity bridge for the boundary-safe Bregman divergence when the
carrier has unique tangent directions.

The extra `UniqueDiffOn` premise is intentionally explicit: Lan's JSON assumptions give
closed bounded convex `X`, but do not state full-dimensionality.  Mathlib's canonical
route for continuity of `gradientWithin` is `ContDiffOn.continuousOn_fderivWithin`,
which needs `UniqueDiffOn ℝ X`. -/
theorem V_continuousOn_carrier_of_uniqueDiffOn
    (huniq : UniqueDiffOn ℝ setup.X) :
    ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ := by
  have hv : Continuous setup.v := setup.v_continuous_carrier
  have hg : Continuous (fun x : setup.Point => setup.vGradExtension x) :=
    setup.vGradExtension_continuous_of_uniqueDiffOn huniq
  have hleft : Continuous (fun p : setup.Point × setup.Point => setup.v p.2) :=
    hv.comp continuous_snd
  have hbase : Continuous (fun p : setup.Point × setup.Point => setup.v p.1) :=
    hv.comp continuous_fst
  have hinner : Continuous (fun p : setup.Point × setup.Point =>
      ⟪setup.vGradExtension p.1, p.2.1 - p.1.1⟫_ℝ) :=
    (hg.comp continuous_fst).inner
      ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst))
  have hV : Continuous (fun p : setup.Point × setup.Point =>
      setup.v p.2 - setup.v p.1 -
        ⟪setup.vGradExtension p.1, p.2.1 - p.1.1⟫_ℝ) :=
    (hleft.sub hbase).sub hinner
  change ContinuousOn (fun p : setup.Point × setup.Point =>
      setup.v p.2 - setup.v p.1 -
        ⟪setup.vGradExtension p.1, p.2.1 - p.1.1⟫_ℝ) Set.univ
  exact hV.continuousOn

/-- Carrier-continuity bridge for the boundary-safe Bregman divergence, with the
relative affine-span gradient extension. -/
theorem V_continuousOn_carrier :
    ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ := by
  have hv : Continuous setup.v := setup.v_continuous_carrier
  have hg : Continuous (fun x : setup.Point => setup.vGradExtension x) :=
    setup.vGradExtension_continuous
  have hleft : Continuous (fun p : setup.Point × setup.Point => setup.v p.2) :=
    hv.comp continuous_snd
  have hbase : Continuous (fun p : setup.Point × setup.Point => setup.v p.1) :=
    hv.comp continuous_fst
  have hinner : Continuous (fun p : setup.Point × setup.Point =>
      ⟪setup.vGradExtension p.1, p.2.1 - p.1.1⟫_ℝ) :=
    (hg.comp continuous_fst).inner
      ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst))
  have hV : Continuous (fun p : setup.Point × setup.Point =>
      setup.v p.2 - setup.v p.1 -
        ⟪setup.vGradExtension p.1, p.2.1 - p.1.1⟫_ℝ) :=
    (hleft.sub hbase).sub hinner
  change ContinuousOn (fun p : setup.Point × setup.Point =>
      setup.v p.2 - setup.v p.1 -
        ⟪setup.vGradExtension p.1, p.2.1 - p.1.1⟫_ℝ) Set.univ
  exact hV.continuousOn

/-- Interior feasible points are dense in the feasible-carrier subtype, provided the
ambient topological interior is dense in `X`.

The JSON states that `X` is nonempty, bounded, closed, and convex; it does not separately state
that `X` is full-dimensional.  Therefore the density premise is explicit here rather than
hidden as a paper assumption. -/
theorem interiorPointSet_dense_of_subset_closure_interior
    (hXdense : setup.X ⊆ closure (interior setup.X)) :
    Dense {x : setup.Point | x.1 ∈ interior setup.X} := by
  exact dense_subtype_of_subset_closure (X := setup.X) (U := interior setup.X)
    interior_subset hXdense

/-- Mathlib's relative/intrinsic closure of the finite-dimensional feasible set is the
usual topological closure. -/
theorem intrinsicClosure_eq_topological_closure :
    intrinsicClosure ℝ setup.X = closure setup.X := by
  exact intrinsicClosure_eq_closure ℝ setup.X

/-- Every feasible point lies in Mathlib's relative/intrinsic closure of the feasible set.

This is the source-backed relative-geometry route available from Lan's nonempty convex
carrier; unlike `X ⊆ closure (interior X)`, it does not require an unstated
full-dimensionality assumption. -/
theorem subset_intrinsicClosure_carrier :
    setup.X ⊆ intrinsicClosure ℝ setup.X := by
  exact subset_intrinsicClosure

/-- Relative-interior density in the feasible-carrier subtype from an ambient closure
statement.

This is the intrinsic analogue of `interiorPointSet_dense_of_subset_closure_interior`:
the dense subset is now `intrinsicInterior ℝ X`, not the generally-too-small
topological interior. -/
theorem intrinsicInteriorPointSet_dense_of_subset_closure_intrinsicInterior
    (hXdense : setup.X ⊆ closure (intrinsicInterior ℝ setup.X)) :
    Dense {x : setup.Point | x.1 ∈ intrinsicInterior ℝ setup.X} := by
  exact dense_subtype_of_subset_closure
    (X := setup.X) (U := intrinsicInterior ℝ setup.X) intrinsicInterior_subset hXdense

/-- Source-backed relative-interior density for a nonempty closed convex feasible set.

For a finite-dimensional convex set, the closure of the relative interior is the closure of
the set.  Lan supplies nonemptiness through `x₁ ∈ X` and closed convexity through the
feasible-set assumptions, so every feasible point lies in `closure (intrinsicInterior ℝ X)`.
This is the boundary bridge needed for lower-dimensional feasible carriers. -/
theorem X_subset_closure_intrinsicInterior :
    setup.X ⊆ closure (intrinsicInterior ℝ setup.X) := by
  have hclosure_intrinsic :
      closure (intrinsicInterior ℝ setup.X) = intrinsicClosure ℝ setup.X :=
    closure_intrinsicInterior_eq_intrinsicClosure_of_nonempty_convex
      (X := setup.X) setup.hX_convex ⟨setup.x1.1, setup.x1.2⟩
  simpa [hclosure_intrinsic] using
    (subset_intrinsicClosure (𝕜 := ℝ) (s := setup.X))

/-- The feasible carrier is nonempty because the paper initialization supplies `x₁ ∈ X`. -/
theorem X_nonempty : setup.X.Nonempty :=
  ⟨setup.x1.1, setup.x1.2⟩

/-- Mathlib's full-dimensional convex-set route to unique differentiability.

This is not a setup assumption. It packages the exact geometric premise needed by
`ContDiffOn.continuousOn_fderivWithin`: a convex feasible set with nonempty topological interior. -/
theorem X_uniqueDiffOn_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) :
    UniqueDiffOn ℝ setup.X := by
  exact uniqueDiffOn_convex setup.hX_convex hXint

/-- Source-backed topological-density bridge for full-dimensional convex feasible sets.

For a closed convex `X` with nonempty topological interior, Mathlib identifies
`closure (interior X)` with `closure X`; Lan's closed-carrier hypothesis then gives
`X ⊆ closure (interior X)`. -/
theorem X_subset_closure_interior_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) :
    setup.X ⊆ closure (interior setup.X) := by
  exact subset_closure_interior_of_closed_convex_nonempty_interior
    setup.hX_closed setup.hX_convex hXint

/-- All-carrier continuity of the boundary-safe Bregman divergence under the standard
full-dimensional convex-set bridge. -/
theorem V_continuousOn_carrier_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) :
    ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ := by
  exact carrierBregmanDivergence_continuousOn_of_nonempty_interior
    setup.hX_convex setup.V_continuousOn_carrier_of_uniqueDiffOn hXint

/-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math` ::
`"\\bar{x}_s^k = (\\sum_{t=s}^{k} \\gamma_t)^{-1} \\sum_{t=s}^{k} \\gamma_t x_t"`. -/
def outputWeightSum (setup : MirrorDescentSetup m d) (w : OutputWindow) : ℝ :=
  SOptLib.outputWeightSum outputTimes setup.stepSize w

/-- `book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math` ::
`"E[f(\\bar{x}_s^k)] - f^* ≤ (\\sum_{t=s}^{k} \\gamma_t)^{-1}[E[V(x_s, x^*)] + (M^2 + σ^2)\\sum_{t=s}^{k} \\gamma_t^2]"`. -/
def outputSquaredStepSum (setup : MirrorDescentSetup m d) (w : OutputWindow) : ℝ :=
  SOptLib.outputSquaredStepSum outputTimes setup.stepSize w

/-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/parameters/0` ::
`"D_X^2 := max_{x_1, x ∈ X} V(x_1, x)"`. -/
theorem DXSq_exists :
    ∃ p : setup.Point × setup.Point,
      ∀ q : setup.Point × setup.Point, setup.V q.1 q.2 ≤ setup.V p.1 p.2 := by
  exact exists_max_pair_of_declared_maximizer setup.V setup.DXSqMaximizer (by
    intro q
    simpa [MirrorDescentSetup.V, carrierBregmanDivergence, vGradExtension, vInteriorAmbient] using
      setup.hDXSqMaximizer_max q)

/-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/parameters/0` ::
`"D_X^2 := max_{x_1, x ∈ X} V(x_1, x)"`, realized on the paper carrier `X × X`. -/
private def bregmanValueSet : Set ℝ :=
  _root_.bregmanValueSet setup.V

/- The set `{V(x₁, x) | x₁, x ∈ X}` is nonempty. -/
private theorem bregmanValueSet_nonempty :
    (setup.bregmanValueSet).Nonempty := by
  simpa [bregmanValueSet] using _root_.bregmanValueSet_nonempty setup.V setup.DXSq_exists

/- The set `{V(x₁, x) | x₁, x ∈ X}` is bounded above by a maximizing value. -/
private theorem bregmanValueSet_bddAbove :
    BddAbove setup.bregmanValueSet := by
  simpa [bregmanValueSet] using _root_.bregmanValueSet_bddAbove setup.V setup.DXSq_exists

/-- `book/FOML/StochasticMirrorDescent.json#/assumptions/5/parameters/0` ::
`"D_X^2 := max_{x_1, x ∈ X} V(x_1, x)"`, realized on `X × X`. -/
noncomputable def D_X_sq : ℝ :=
  bregmanDiameterSq setup.V

/- The canonical diameter value is attained by a maximizing pair in `X × X`. -/
theorem D_X_sq_eq_max :
    ∃ p : setup.Point × setup.Point,
      setup.D_X_sq = setup.V p.1 p.2 ∧
        ∀ q : setup.Point × setup.Point, setup.V q.1 q.2 ≤ setup.D_X_sq := by
  simpa [D_X_sq] using
    bregmanDiameterSq_eq_declared_max setup.V setup.DXSqMaximizer (by
      intro q
      simpa [MirrorDescentSetup.V, carrierBregmanDivergence, vGradExtension, vInteriorAmbient] using
        setup.hDXSqMaximizer_max q)

/-- The paper Bregman divergence is controlled by `D_X²`. -/
theorem V_le_D_X_sq (x z : setup.Point) :
    setup.V x z ≤ setup.D_X_sq := by
  simpa [D_X_sq, bregmanValueSet] using
    carrierBregmanDivergence_le_diameterSq
      (X := setup.X) (V := setup.V) setup.bregmanValueSet_bddAbove x z

/-- The public divergence is Lan's literal formula on interior base points. -/
theorem V_eq_formula_of_interior (x : setup.InteriorPoint) (z : setup.Point) :
    setup.V x.toPoint z = setup.literalV x z := by
  simpa [V, literalV, InteriorPoint.toPoint] using
    carrierBregmanDivergence_eq_interior_formula
      (v := setup.v) (vInterior := setup.vInteriorAmbient)
      (grad := fun y : setup.Point => setup.vGradExtension y)
      (x := x) (z := z)
      (setup.vGradExtension_eq_literal_of_interior x)

/-- The public divergence is Lan's relative-interior Bregman formula on the
intrinsic-interior carrier used by the paper regularity assumptions. -/
theorem V_eq_formula_of_intrinsicInterior
    (x : setup.IntrinsicInteriorPoint) (z : setup.Point) :
    setup.V x.toPoint z = setup.literalVIntrinsic x z := by
  simpa [V, literalVIntrinsic] using
    (literalIntrinsicCarrierBregmanDivergence
      (X := setup.X) (v := setup.v) (grad := fun y : setup.Point => setup.vGradExtension y)
      (gradI := fun y => setup.vIntrinsicGradient y) (x := x) (z := z)
      (setup.vGradExtension_eq_literal_of_intrinsicInterior x))

/-- Core strong-convexity lower bound on the relative-interior carrier.

This is placed before the topological-interior wrapper so that the latter can
specialize it through `interior_subset_intrinsicInterior`. -/
theorem V_lower_bound_of_intrinsicInterior_core (x z : setup.Point)
    (hx : x.1 ∈ intrinsicInterior ℝ setup.X)
    (hz : z.1 ∈ intrinsicInterior ℝ setup.X) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  simpa [MirrorDescentSetup.V, carrierBregmanDivergence, vInteriorAmbient,
    totalizeOnInterior_of_mem, hx, hz]
    using
      (bregman_lower_bound_of_strongConvexOn_intrinsicInterior
        (X := setup.X) (v := setup.vInteriorAmbient)
        (grad := fun _ : DecisionSpace m => setup.vGradExtension x)
        (V := fun y w : DecisionSpace m =>
          setup.vInteriorAmbient w - setup.vInteriorAmbient y -
            ⟪setup.vGradExtension x, w - y⟫_ℝ)
        (x := x.1) (z := z.1) rfl setup.v_strong_convex_on_interior
        setup.v_differentiableOn_interior
        (by
          simpa [vInteriorAmbient] using
            setup.vGradExtension_inner_eq_gradientWithin_intrinsicInterior x z hx)
        hx hz)

/-- Strong-convexity lower bound for the Bregman divergence on interior base and
target points.

This is Lan's proof step `V(x_t,x_{t+1}) ≥ (1/2)‖x_t-x_{t+1}‖²`, routed through
the Mathlib `StrongConvexOn` realization of the distance generator on `Xᵒ`. -/
theorem V_lower_bound_of_interior (x z : setup.Point)
    (hx : x.1 ∈ interior setup.X) (hz : z.1 ∈ interior setup.X) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_of_intrinsicInterior_core x z
    (interior_subset_intrinsicInterior hx) (interior_subset_intrinsicInterior hz)

/-- Interior nonnegativity of the paper Bregman divergence, matching Lan's
interior-only differentiability and strong-convexity assumptions. -/
theorem V_nonneg_of_interior (x z : setup.Point)
    (hx : x.1 ∈ interior setup.X) (hz : z.1 ∈ interior setup.X) :
    0 ≤ setup.V x z := by
  have h := setup.V_lower_bound_of_interior x z hx hz
  nlinarith [sq_nonneg ‖x.1 - z.1‖]

/-- Boundary extension of the interior Bregman lower bound under an explicit
topological-interior density premise.

This is the real Mathlib route for the all-carrier estimate: prove the inequality on the
dense interior carrier using `StrongConvexOn`, then close it under `ContinuousOn` of
`(x,z) ↦ V(x,z) - (1/2)‖x-z‖²` and density of `Xᵒ` in `X`. -/
theorem V_lower_bound_all_carrier_from_density
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X))
    (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  let f : setup.Point × setup.Point → ℝ := fun p => setup.V p.1 p.2
  let g : setup.Point × setup.Point → ℝ :=
    fun p => (1 / 2 : ℝ) * ‖p.1.1 - p.2.1‖ ^ 2
  let s : Set (setup.Point × setup.Point) :=
    {y : setup.Point | y.1 ∈ interior setup.X} ×ˢ
      {y : setup.Point | y.1 ∈ interior setup.X}
  have hres_cont : ContinuousOn (fun p => f p - g p) Set.univ := by
    have hnorm : Continuous g := by
      exact continuous_const.mul
        (((continuous_subtype_val.comp continuous_fst).sub
          (continuous_subtype_val.comp continuous_snd)).norm.pow 2)
    exact hcont.sub hnorm.continuousOn
  have hdense_pair : Dense s := by
    have hI : Dense {y : setup.Point | y.1 ∈ interior setup.X} :=
      setup.interiorPointSet_dense_of_subset_closure_interior hXdense
    rw [dense_iff_closure_eq] at hI ⊢
    rw [closure_prod_eq, hI]
    simp
  have hres_nonneg_interior : ∀ p ∈ s, g p ≤ f p := by
    rintro p ⟨hp1, hp2⟩
    exact setup.V_lower_bound_of_interior p.1 p.2 hp1 hp2
  simpa [f, g] using
    le_of_continuousOn_of_dense_le f g s hres_cont hdense_pair hres_nonneg_interior (x, z)

/-- Carrier-level lower bound for the paper Bregman divergence on the feasible carrier,
with the extra topological boundary bridge stated explicitly.

The source JSON directly supplies the lower-bound argument on `Xᵒ`.  Extending it to all
of `X` requires a density/continuity boundary argument; this theorem exposes the density
premise instead of hiding it inside the setup strong-convexity field. -/
theorem V_lower_bound_on_carrier
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X)) (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_all_carrier_from_density hcont hXdense x z

/-- Carrier-level lower bound for the paper Bregman divergence with both boundary
extension premises explicit. -/
theorem V_lower_bound_on_carrier_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X)) (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_all_carrier_from_density hcont hXdense x z

/-- All-carrier lower bound for the paper Bregman divergence under an explicit
topological-interior density premise.

The JSON assumptions directly justify `V_lower_bound_on_carrier` on `Xᵒ`; this lemma makes
the additional boundary-density obligation visible to callers instead of treating it as a
primitive setup fact. -/
theorem V_lower_bound_all_carrier_of_subset_closure_interior
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X)) (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_on_carrier hcont hXdense x z

/-- All-carrier nonnegativity of the boundary-safe Bregman divergence under an explicit
topological-interior density premise. -/
theorem V_nonneg_all_carrier_of_subset_closure_interior
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X)) (x z : setup.Point) :
    0 ≤ setup.V x z := by
  have h := setup.V_lower_bound_on_carrier hcont hXdense x z
  nlinarith [sq_nonneg ‖x.1 - z.1‖]

/-- All-carrier nonnegativity from the explicit continuity/density boundary bridge. -/
theorem V_nonneg_all_carrier_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X)) (x z : setup.Point) :
    0 ≤ setup.V x z := by
  have h := setup.V_lower_bound_on_carrier_of_continuousOn hcont hXdense x z
  nlinarith [sq_nonneg ‖x.1 - z.1‖]

/-- Strong-convexity lower bound on the relative interior carrier.

This is the direct Lean realization of Lan's lower-bound step on `Xᵒ`, with
`Xᵒ` interpreted as Mathlib's `intrinsicInterior ℝ X`. -/
theorem V_lower_bound_of_intrinsicInterior (x z : setup.Point)
    (hx : x.1 ∈ intrinsicInterior ℝ setup.X)
    (hz : z.1 ∈ intrinsicInterior ℝ setup.X) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_of_intrinsicInterior_core x z hx hz

/-- Boundary extension of the relative-interior Bregman lower bound.

The dense set is `intrinsicInterior ℝ X`, so this route remains meaningful for
lower-dimensional closed convex feasible carriers. -/
theorem V_lower_bound_all_carrier_from_intrinsicClosure
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (intrinsicInterior ℝ setup.X))
    (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact sub_nonneg.mp (nonneg_of_continuousOn_of_dense_nonneg
    (D := fun p : setup.Point × setup.Point =>
      setup.V p.1 p.2 - (1 / 2 : ℝ) * ‖p.1.1 - p.2.1‖ ^ 2)
    (s := {x : setup.Point | x.1 ∈ intrinsicInterior ℝ setup.X} ×ˢ
      {x : setup.Point | x.1 ∈ intrinsicInterior ℝ setup.X})
    (by
      have hnorm :
          Continuous (fun p : setup.Point × setup.Point =>
            (1 / 2 : ℝ) * ‖p.1.1 - p.2.1‖ ^ 2) :=
        continuous_const.mul
          (((continuous_subtype_val.comp continuous_fst).sub
            (continuous_subtype_val.comp continuous_snd)).norm.pow 2)
      exact hcont.sub hnorm.continuousOn)
    (by
      have hI : Dense {x : setup.Point | x.1 ∈ intrinsicInterior ℝ setup.X} :=
        setup.intrinsicInteriorPointSet_dense_of_subset_closure_intrinsicInterior hXdense
      rw [dense_iff_closure_eq] at hI ⊢
      rw [closure_prod_eq, hI]
      simp)
    (by
      rintro p ⟨hp1, hp2⟩
      change 0 ≤ setup.V p.1 p.2 - (1 / 2 : ℝ) * ‖p.1.1 - p.2.1‖ ^ 2
      have h := setup.V_lower_bound_of_intrinsicInterior p.1 p.2 hp1 hp2
      linarith)
    (x, z))

/-- All-carrier lower bound from the source-backed relative-interior boundary bridge. -/
theorem V_lower_bound_all_carrier_of_intrinsicClosure
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_all_carrier_from_intrinsicClosure hcont
    setup.X_subset_closure_intrinsicInterior x z

/-- All-carrier nonnegativity from the source-backed relative-interior boundary bridge. -/
theorem V_nonneg_all_carrier_of_intrinsicClosure
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (x z : setup.Point) :
    0 ≤ setup.V x z := by
  have h := setup.V_lower_bound_all_carrier_of_intrinsicClosure hcont x z
  nlinarith [sq_nonneg ‖x.1 - z.1‖]

/-- All-carrier lower bound from the source-backed full-dimensional convex-set bridge. -/
theorem V_lower_bound_on_carrier_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) (x z : setup.Point) :
    (1 / 2 : ℝ) * ‖x.1 - z.1‖ ^ 2 ≤ setup.V x z := by
  exact setup.V_lower_bound_all_carrier_from_density
    (setup.V_continuousOn_carrier_of_nonempty_interior hXint)
    (setup.X_subset_closure_interior_of_nonempty_interior hXint) x z

/-- All-carrier nonnegativity from the source-backed full-dimensional convex-set bridge. -/
theorem V_nonneg_all_carrier_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) (x z : setup.Point) :
    0 ≤ setup.V x z := by
  have h := setup.V_lower_bound_on_carrier_of_nonempty_interior hXint x z
  nlinarith [sq_nonneg ‖x.1 - z.1‖]

/-- Compact-continuity route to a finite absolute bound for the paper Bregman term.

This is the valid Mathlib path for an all-carrier absolute bound: once the boundary-safe
divergence is genuinely continuous on compact `X × X`, the extreme-value theorem applied
to `p ↦ ‖V(p.1,p.2)‖` gives a uniform bound. -/
theorem V_abs_bound_exists_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : setup.Point, ‖setup.V x z‖ ≤ C := by
  simpa [Prod.forall] using
    (exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (s := Set.univ)
      (f := fun p : setup.Point × setup.Point => setup.V p.1 p.2)
      setup.pointProd_univ_isCompact hcont)

/-- The paper Bregman divergence has a finite absolute bound on `X × X`.

This is routed through the compact-continuity extreme-value theorem, not through
an all-carrier nonnegativity claim.  Lan's strong-convexity hypothesis is stated on
`Xᵒ`, so the absolute-bound path must not depend on a hidden all-carrier
nonnegativity assertion. -/
theorem V_abs_bound_exists :
    ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : setup.Point, ‖setup.V x z‖ ≤ C := by
  intro hcont
  exact setup.V_abs_bound_exists_of_continuousOn hcont

/-- Absolute boundedness from Mathlib's `UniqueDiffOn` route to continuity. -/
theorem V_abs_bound_exists_of_uniqueDiffOn
    (huniq : UniqueDiffOn ℝ setup.X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : setup.Point, ‖setup.V x z‖ ≤ C := by
  exact setup.V_abs_bound_exists setup.V_continuousOn_carrier

/-- Absolute boundedness from the source-backed full-dimensional convex-set bridge. -/
theorem V_abs_bound_exists_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : setup.Point, ‖setup.V x z‖ ≤ C := by
  exact exists_abs_bound_on_compact_product_of_continuousOn (P := setup.Point) setup.V
    setup.pointProd_univ_isCompact (setup.V_continuousOn_carrier_of_nonempty_interior hXint)

/-- Interior nonnegativity of the boundary-safe Bregman divergence on carrier points. -/
theorem V_nonneg_on_carrier (x z : setup.Point)
    (hx : x.1 ∈ interior setup.X) (hz : z.1 ∈ interior setup.X) :
    0 ≤ setup.V x z := by
  simpa [MirrorDescentSetup.V] using
    (carrierBregmanDivergence_nonneg_of_interior
      (X := setup.X) (v := setup.v) (vInterior := setup.vInteriorAmbient)
      (grad := fun x => setup.vGradExtension x) (x := x) (z := z)
      (by
        simpa [vInteriorAmbient] using
          (totalizeOnInterior_of_mem setup.X setup.v
            (interior_subset_intrinsicInterior hx)).symm)
      (by
        simpa [vInteriorAmbient] using
          (totalizeOnInterior_of_mem setup.X setup.v
            (interior_subset_intrinsicInterior hz)).symm)
      setup.v_strong_convex_on_interior setup.v_differentiableOn_interior
      (setup.vGradExtension_inner_eq_gradientWithin_intrinsicInterior x z
        (interior_subset_intrinsicInterior hx))
      hx hz)

/-- Expanded literal formula for `V` on interior base points. -/
theorem literalV_def (x : setup.InteriorPoint) (z : setup.Point) :
    setup.literalV x z =
      setup.v z - setup.v x.toPoint -
        ⟪∇ setup.vInteriorAmbient x.1, z.1 - x.1⟫_ℝ := by
  simpa [InteriorPoint.toPoint] using
    literalCarrierBregmanDivergence
      (v := setup.v) (vInterior := setup.vInteriorAmbient) (V := setup.literalV)
      (by intro y w; rfl) x z

/-- Paper prox objective realizing Eq. (3.2.5) on the paper carrier `X × X`. -/
noncomputable def paperMirrorObjective
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) : ℝ :=
  SOptLib.paperMirrorObjective setup.V (fun y : setup.Point => y.1) x g γ y

/-- Expanded paper prox objective formula. -/
theorem paperMirrorObjective_def
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    setup.paperMirrorObjective x g γ y =
      γ * ⟪g, y.1⟫_ℝ + setup.V x y := by
  rfl

/-- Continuity of the paper prox objective in the candidate point.

This is the compact-argmin route for Lan's prox update: the linear oracle term is
continuous and the Bregman term is continuous on the feasible carrier. -/
theorem paperMirrorObjective_continuous
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    Continuous (setup.paperMirrorObjective x g γ) := by
  have hinner : Continuous (fun y : setup.Point => ⟪g, y.1⟫_ℝ) :=
    continuous_const.inner continuous_subtype_val
  have hlin : Continuous (fun y : setup.Point => γ * ⟪g, y.1⟫_ℝ) :=
    continuous_const.mul hinner
  have hVpair : Continuous (fun p : setup.Point × setup.Point => setup.V p.1 p.2) :=
    continuousOn_univ.mp setup.V_continuousOn_carrier
  have hV : Continuous (fun y : setup.Point => setup.V x y) :=
    hVpair.comp (continuous_const.prodMk continuous_id)
  simpa [paperMirrorObjective] using hlin.add hV

/-- Backward-compatible name for the literal paper prox objective on interior base points. -/
noncomputable def literalMirrorObjective
    (x : setup.InteriorPoint) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) : ℝ :=
  _root_.literalMirrorObjective setup.literalV (fun y : setup.Point => y.1) x g γ y

/-- On interior bases, the paper prox objective agrees with Lan's literal formula. -/
theorem literalMirrorObjective_eq_paperMirrorObjective
    (x : setup.InteriorPoint) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    setup.literalMirrorObjective x g γ y =
      setup.paperMirrorObjective x.toPoint g γ y := by
  exact _root_.literalMirrorObjective_eq_paperMirrorObjective setup.V setup.literalV
    (fun x : setup.InteriorPoint => x.toPoint) (fun y : setup.Point => y.1)
    setup.V_eq_formula_of_interior x g γ y

/-- Paper-facing argmin specification for the mirror descent prox step on `X`. -/
def IsMirrorStep (x : setup.Point) (g : DecisionSpace m) (γ : ℝ)
    (z : setup.Point) : Prop :=
  IsMinOn (setup.paperMirrorObjective x g γ) Set.univ z

/-- Literal paper-facing argmin condition for interior base points. -/
def IsLiteralMirrorStep (x : setup.InteriorPoint) (g : DecisionSpace m) (γ : ℝ)
    (z : setup.Point) : Prop :=
  SOptLib.IsLiteralMirrorStep setup.literalMirrorObjective x g γ z

/-- Expanded paper-facing argmin condition for the prox step. -/
theorem isMirrorStep_iff
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (z : setup.Point) :
    setup.IsMirrorStep x g γ z ↔
      ∀ y : setup.Point,
        setup.paperMirrorObjective x g γ z ≤ setup.paperMirrorObjective x g γ y := by
  rw [MirrorDescentSetup.IsMirrorStep, isMinOn_univ_iff]

/-- Expanded literal argmin condition on interior base points. -/
theorem isLiteralMirrorStep_iff
    (x : setup.InteriorPoint) (g : DecisionSpace m) (γ : ℝ) (z : setup.Point) :
    setup.IsLiteralMirrorStep x g γ z ↔
      ∀ y : setup.Point,
        setup.literalMirrorObjective x g γ z ≤ setup.literalMirrorObjective x g γ y := by
  simpa [MirrorDescentSetup.IsLiteralMirrorStep, SOptLib.IsLiteralMirrorStep] using
    (SOptLib.isLiteralMirrorStep_iff setup.literalMirrorObjective x g γ z)

/-- Compactness/continuity existence route for the paper prox argmin.

The terminal existence theorem is Mathlib's `IsCompact.exists_isMinOn`, applied to the
compact feasible-carrier subtype and the continuous paper mirror objective. -/
theorem mirrorStep_exists_compact
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    ∃ z : setup.Point, setup.IsMirrorStep x g γ z := by
  rcases setup.point_univ_isCompact.exists_isMinOn
      (⟨x, trivial⟩ : (Set.univ : Set setup.Point).Nonempty)
      (setup.paperMirrorObjective_continuous x g γ).continuousOn with
    ⟨z, _hz, hzmin⟩
  exact ⟨z, hzmin⟩

/-- Canonical realization of the paper prox step
`book/FOML/StochasticMirrorDescent.json#/algorithm_spec/steps/0/math` ::
`"x_{t+1} = argmin_{x ∈ X} {γ_t ⟨G_t, x⟩ + V(x_t, x)}, t = 1, 2, ..."` on the
paper carrier `X`. -/
private theorem mirrorStep_exists_aux
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    ∃ z : setup.Point, setup.IsMirrorStep x g γ z := by
  exact setup.mirrorStep_exists_compact x g γ

/-- Canonical realization of the paper prox step. -/
theorem mirrorStep_exists
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    ∃ z : setup.Point, setup.IsMirrorStep x g γ z := by
  exact setup.mirrorStep_exists_compact x g γ

private noncomputable def proxStepArgmin (setup : MirrorDescentSetup m d)
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    {z : setup.Point // setup.IsMirrorStep x g γ z} :=
  let h :=
    setup.point_univ_isCompact.exists_isMinOn
      (⟨x, trivial⟩ : (Set.univ : Set setup.Point).Nonempty)
      (setup.paperMirrorObjective_continuous x g γ).continuousOn
  ⟨Classical.choose h, (Classical.choose_spec h).2⟩

/-- Canonical realization of the paper prox step used by the recursive iterate sequence.

This is the paper update `argmin_{x ∈ X} {γ ⟨g, x⟩ + V(x_t, x)}` selected from the
compact feasible carrier by Mathlib's extreme-value theorem. It replaces the earlier
source-level arbitrary selector field, so the update used by the process and the
argmin object used by the prox lemmas are the same definition. -/
noncomputable def proxStep
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) : setup.Point :=
  SOptLib.proxStep (V := setup.V) (eval := fun y : setup.Point => y.1)
    setup.point_univ_isCompact (continuousOn_univ.mp setup.V_continuousOn_carrier)
    continuous_subtype_val x g γ

/-- The canonical prox-map output realizes the paper argmin semantics. -/
theorem proxStep_isMirrorStep
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    setup.IsMirrorStep x g γ (setup.proxStep x g γ) := by
  simpa [MirrorDescentSetup.IsMirrorStep, MirrorDescentSetup.paperMirrorObjective,
    MirrorDescentSetup.proxStep, SOptLib.IsMirrorStep] using
    (SOptLib.proxStep_isMirrorStep (V := setup.V) (eval := fun y : setup.Point => y.1)
      setup.point_univ_isCompact (continuousOn_univ.mp setup.V_continuousOn_carrier)
      continuous_subtype_val x g γ)

/-- The canonical prox map minimizes the paper prox objective over `X`. -/
theorem proxStep_minimizes
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    setup.paperMirrorObjective x g γ (setup.proxStep x g γ) ≤
      setup.paperMirrorObjective x g γ y := by
  exact (setup.isMirrorStep_iff x g γ (setup.proxStep x g γ)).1
    (setup.proxStep_isMirrorStep x g γ) y

/-- Joint continuity of the compact-argmin objective in parameters and candidate point. -/
private theorem paperMirrorObjective_joint_continuous :
    Continuous (fun q : (setup.Point × DecisionSpace m × ℝ) × setup.Point =>
      setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  simpa [paperMirrorObjective] using
    (SOptLib.paperMirrorObjective_joint_continuous
      (P := setup.Point) (E := DecisionSpace m) (V := setup.V)
      (eval := fun y : setup.Point => y.1)
      (continuousOn_univ.mp setup.V_continuousOn_carrier)
      continuous_subtype_val)

private theorem mapClusterPt_graph_of_tendsto_of_mapClusterPt
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {l : Filter α} {a : α} {f : α → β} {b : β}
    (ha : Filter.Tendsto id l (𝓝 a)) (hb : MapClusterPt b l f) :
    MapClusterPt (a, b) l (fun x => (x, f x)) := by
  rw [((𝓝 a).basis_sets.prod_nhds (𝓝 b).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  have hs_eventually : ∀ᶠ x in l, x ∈ s := ha hs
  have ht_frequently : ∃ᶠ x in l, f x ∈ t := by
    rw [mapClusterPt_iff_frequently] at hb
    exact hb t ht
  exact (ht_frequently.and_eventually hs_eventually).mono fun x hx => ⟨hx.2, hx.1⟩

/-- Scalar one-sided first-order condition at a minimum on `[0,1]`, staged before the
uniqueness bridge. -/
private theorem right_derivative_nonneg_of_min_on_Icc_for_unique
    {φ : ℝ → ℝ} {D : ℝ}
    (hderiv : HasDerivWithinAt φ D (Set.Icc (0 : ℝ) 1) 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t) :
    0 ≤ D := by
  have hderivIoc : HasDerivWithinAt φ D (Set.Ioc (0 : ℝ) 1) 0 :=
    hderiv.mono Set.Ioc_subset_Icc_self
  have htendIoc :
      Filter.Tendsto (slope φ 0) (𝓝[Set.Ioc (0 : ℝ) 1] (0 : ℝ)) (𝓝 D) := by
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hderivIoc
  have htend : Filter.Tendsto (slope φ 0) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    simpa [nhdsWithin_Ioc_eq_nhdsGT (show (0 : ℝ) < 1 by norm_num)] using htendIoc
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot (0 : ℝ)
  apply ge_of_tendsto htend
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hdiff : 0 ≤ φ t - φ 0 :=
    sub_nonneg.mpr (hmin t ⟨ht.1.le, ht.2⟩)
  have hden : 0 ≤ t - 0 := sub_nonneg.mpr ht.1.le
  have hslope : 0 ≤ (φ t - φ 0) / (t - 0) := div_nonneg hdiff hden
  simpa [slope_def_field] using hslope

/-- First-order condition for a constrained minimizer in a Hilbert chart, staged before
the uniqueness bridge. -/
private theorem constrained_first_order_condition_chart_for_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : Set H} {Φ : H → ℝ} {z y : H} {F' : H →L[ℝ] ℝ}
    (hTconv : Convex ℝ T) (hz : z ∈ T) (hy : y ∈ T)
    (hmin : ∀ u ∈ T, Φ z ≤ Φ u)
    (hderiv : HasFDerivWithinAt Φ F' T z) :
    0 ≤ F' (y - z) := by
  exact Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt
    hTconv hz hy hmin hderiv

/-- Difference of two feasible chart coordinates, included back into ambient space, staged
before the uniqueness bridge. -/
private theorem carrierChartPoint_sub_subtypeL_for_unique
    (X : Set E) (anchor x y : {x : E // x ∈ X}) :
    let A : AffineSubspace ℝ E := carrierAffineSpan X
    (A.direction.subtypeL)
      (carrierChartPoint X anchor y - carrierChartPoint X anchor x) = y.1 - x.1 := by
  classical
  let A : AffineSubspace ℝ E := carrierAffineSpan X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let L : A.direction →ᴬ[ℝ] E := carrierChartToAmbient X anchor
  let uy : A.direction := carrierChartPoint X anchor y
  let ux : A.direction := carrierChartPoint X anchor x
  have hlin : L.contLinear (uy - ux) = L uy - L ux := by
    simpa [vsub_eq_sub] using L.contLinear_map_vsub uy ux
  have hy : L uy = y.1 := by
    simpa [A, L, uy] using carrierChartToAmbient_chartPoint X anchor y
  have hx : L ux = x.1 := by
    simpa [A, L, ux] using carrierChartToAmbient_chartPoint X anchor x
  have hLlin_apply : L.contLinear (uy - ux) = (A.direction.subtypeL) (uy - ux) := by
    let du : A.direction := uy - ux
    have hLdu : L.contLinear du = L du - L 0 := by
      simpa [vsub_eq_sub] using L.contLinear_map_vsub du 0
    have hLdu_apply : L du = (du : E) + anchor.1 := by
      let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
      change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
          du : A) : E) = (du : E) + anchor.1
      simp [a]
    have hLzero : L 0 = anchor.1 := by
      let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
      change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
          (0 : A.direction) : A) : E) = anchor.1
      simp [a]
    calc
      L.contLinear (uy - ux) = L.contLinear du := by simp [du]
      _ = (du : E) := by
        rw [hLdu, hLdu_apply, hLzero]
        simp
      _ = (A.direction.subtypeL) (uy - ux) := by simp [du]
  change (A.direction.subtypeL) (uy - ux) = y.1 - x.1
  rw [← hLlin_apply, hlin, hy, hx]

/-- Derivative of the charted paper mirror objective at a feasible minimizer, staged before
the uniqueness bridge. -/
private theorem paperMirrorObjective_chart_hasFDerivWithinAt_for_unique
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (z : setup.Point) :
    let A : AffineSubspace ℝ (DecisionSpace m) := carrierAffineSpan setup.X
    let T : Set A.direction := carrierChartSet setup.X setup.x1
    let Φ : A.direction → ℝ := fun u =>
      γ * ⟪g, carrierChartToAmbient setup.X setup.x1 u⟫_ℝ +
        (carrierChartFunction setup.X setup.v setup.x1 u - setup.v x -
          ⟪carrierGradientFrom setup.X setup.v setup.x1 x,
            carrierChartToAmbient setup.X setup.x1 u - x.1⟫_ℝ)
    let F' : A.direction →L[ℝ] ℝ :=
      (innerSL ℝ
        (γ • g +
          carrierGradientFrom setup.X setup.v setup.x1 z -
          carrierGradientFrom setup.X setup.v setup.x1 x)).comp
        (A.direction.subtypeL)
    HasFDerivWithinAt Φ F' T (carrierChartPoint setup.X setup.x1 z) := by
  classical
  let A : AffineSubspace ℝ (DecisionSpace m) := carrierAffineSpan setup.X
  haveI : Nonempty A := ⟨⟨setup.x1.1, subset_affineSpan ℝ setup.X setup.x1.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ (DecisionSpace m)) : Set (DecisionSpace m)) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := carrierChartSet setup.X setup.x1
  let L : A.direction →ᴬ[ℝ] DecisionSpace m := carrierChartToAmbient setup.X setup.x1
  let f : A.direction → ℝ := carrierChartFunction setup.X setup.v setup.x1
  let uz : A.direction := carrierChartPoint setup.X setup.x1 z
  let gradz : DecisionSpace m := carrierGradientFrom setup.X setup.v setup.x1 z
  let gradx : DecisionSpace m := carrierGradientFrom setup.X setup.v setup.x1 x
  have huz : uz ∈ T := by
    simpa [T, uz] using carrierChartPoint_mem setup.X setup.x1 z
  have hLlin_eq : L.contLinear = A.direction.subtypeL := by
    let a : A := ⟨setup.x1.1, subset_affineSpan ℝ setup.X setup.x1.2⟩
    have hL_apply : ∀ du : A.direction, L du = (du : DecisionSpace m) + a := by
      intro du
      change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
          du : A) : DecisionSpace m) = (du : DecisionSpace m) + a
      simp [L, a]
    simpa using (AffineSubspace.vaddConst_contLinear_eq_subtypeL (A := A) (a := a) (L := L) hL_apply)
  have hLder :
      HasFDerivWithinAt (fun u : A.direction => L u) A.direction.subtypeL T uz := by
    have hLhas : HasFDerivWithinAt (fun u : A.direction => L u) L.contLinear T uz := by
      rw [L.decomp]
      exact L.contLinear.hasFDerivWithinAt.add_const (L 0)
    simpa [hLlin_eq] using hLhas
  have hvder :
      HasFDerivWithinAt f (((innerSL ℝ) gradz).comp A.direction.subtypeL) T uz := by
    have hfcont : ContDiffOn ℝ 1 f T := by
      simpa [T, f] using
        carrierChartFunction_contDiffOn setup.X setup.v setup.x1
          setup.hv_contDiff_on_interior.2
    have hfdiff : DifferentiableWithinAt ℝ f T uz :=
      hfcont.differentiableOn_one uz huz
    have hbase : HasFDerivWithinAt f (fderivWithin ℝ f T uz) T uz :=
      hfdiff.hasFDerivWithinAt
    have hgrad :
        fderivWithin ℝ f T uz =
          (((innerSL ℝ) gradz).comp A.direction.subtypeL) := by
      ext du
      dsimp [gradz]
      unfold carrierGradientFrom
      change (fderivWithin ℝ f T uz) du =
        ⟪((@gradientWithin ℝ A.direction _ _ _ instComplete f T uz : A.direction) :
            DecisionSpace m),
          (du : DecisionSpace m)⟫_ℝ
      rw [← A.direction.coe_inner
        (@gradientWithin ℝ A.direction _ _ _ instComplete f T uz) du]
      simp [gradientWithin]
      rfl
    simpa [hgrad] using hbase
  have hgder :
      HasFDerivWithinAt (fun u : A.direction => γ * ⟪g, L u⟫_ℝ)
        (γ • (((innerSL ℝ) g).comp A.direction.subtypeL)) T uz := by
    have hinner : HasFDerivWithinAt (fun u : A.direction => ⟪g, L u⟫_ℝ)
        (((innerSL ℝ) g).comp A.direction.subtypeL) T uz := by
      simpa using ((innerSL ℝ g).hasFDerivAt.comp_hasFDerivWithinAt uz hLder)
    simpa using hinner.const_mul γ
  have hxder :
      HasFDerivWithinAt (fun u : A.direction => ⟪gradx, L u - x.1⟫_ℝ)
        (((innerSL ℝ) gradx).comp A.direction.subtypeL) T uz := by
    simpa using
      ((innerSL ℝ gradx).hasFDerivAt.comp_hasFDerivWithinAt uz (hLder.sub_const x.1))
  have hsum := hgder.add ((hvder.sub_const (setup.v x)).sub hxder)
  have hF :
      (γ • (((innerSL ℝ) g).comp A.direction.subtypeL) +
          ((((innerSL ℝ) gradz).comp A.direction.subtypeL) -
            (((innerSL ℝ) gradx).comp A.direction.subtypeL))) =
        ((innerSL ℝ) (γ • g + gradz - gradx)).comp A.direction.subtypeL := by
    ext du
    simp [ContinuousLinearMap.comp_apply]
    ring
  change HasFDerivWithinAt
    (fun u : A.direction =>
      γ * ⟪g, L u⟫_ℝ +
        (f u - setup.v x - ⟪gradx, L u - x.1⟫_ℝ))
    (((innerSL ℝ) (γ • g + gradz - gradx)).comp A.direction.subtypeL) T uz
  rw [← hF]
  convert hsum using 1

/-- Symmetric Bregman divergence equals the gradient-monotonicity pairing. -/
private theorem V_symm_eq_gradient_monotonicity_inner
    (z z' : setup.Point) :
    setup.V z z' + setup.V z' z =
      ⟪setup.vGradExtension z' - setup.vGradExtension z, z'.1 - z.1⟫_ℝ := by
  exact carrierBregmanDivergence_add_swap_eq_inner_grad_sub setup.v
    (fun x : setup.Point => setup.vGradExtension x) z z'

/-- Symmetric all-carrier Bregman lower bound from the source-backed strong convexity
bridge. -/
private theorem V_symm_lower_bound_all_carrier
    (z z' : setup.Point) :
    ‖z.1 - z'.1‖ ^ 2 ≤ setup.V z z' + setup.V z' z := by
  exact sq_norm_le_bregman_add_swap_of_half_lower_bound
    (V := setup.V) (eval := fun p : setup.Point => p.1) z z'
    (setup.V_lower_bound_all_carrier_of_intrinsicClosure setup.V_continuousOn_carrier z z')
    (setup.V_lower_bound_all_carrier_of_intrinsicClosure setup.V_continuousOn_carrier z' z)

/-- First-order variational inequality for a carrier minimizer of the paper mirror
objective, staged before the uniqueness bridge. -/
private theorem paperMirrorObjective_argmin_variational_for_unique
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (z y : setup.Point)
    (hzmin : ∀ u : setup.Point,
      setup.paperMirrorObjective x g γ z ≤ setup.paperMirrorObjective x g γ u) :
    0 ≤
      ⟪γ • g +
          carrierGradientFrom setup.X setup.v setup.x1 z -
          carrierGradientFrom setup.X setup.v setup.x1 x,
        y.1 - z.1⟫_ℝ := by
  classical
  let A : AffineSubspace ℝ (DecisionSpace m) := carrierAffineSpan setup.X
  haveI : Nonempty A := ⟨⟨setup.x1.1, subset_affineSpan ℝ setup.X setup.x1.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ (DecisionSpace m)) : Set (DecisionSpace m)) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let T : Set A.direction := carrierChartSet setup.X setup.x1
  let Φ : A.direction → ℝ := fun u =>
    γ * ⟪g, carrierChartToAmbient setup.X setup.x1 u⟫_ℝ +
      (carrierChartFunction setup.X setup.v setup.x1 u - setup.v x -
        ⟪carrierGradientFrom setup.X setup.v setup.x1 x,
          carrierChartToAmbient setup.X setup.x1 u - x.1⟫_ℝ)
  let F' : A.direction →L[ℝ] ℝ :=
    (innerSL ℝ
      (γ • g +
        carrierGradientFrom setup.X setup.v setup.x1 z -
        carrierGradientFrom setup.X setup.v setup.x1 x)).comp
      (A.direction.subtypeL)
  let pointOfChart : ∀ u : A.direction, u ∈ T → setup.Point := fun u hu =>
    ⟨carrierChartToAmbient setup.X setup.x1 u, by simpa [T] using hu⟩
  have hTconv : Convex ℝ T := by
    simpa [T] using carrierChartSet_convex setup.X setup.x1 setup.hX_convex
  have hz_chart : carrierChartPoint setup.X setup.x1 z ∈ T := by
    simpa [T] using carrierChartPoint_mem setup.X setup.x1 z
  have hy_chart : carrierChartPoint setup.X setup.x1 y ∈ T := by
    simpa [T] using carrierChartPoint_mem setup.X setup.x1 y
  have hpointOfChart : ∀ u (hu : u ∈ T),
      Φ u = setup.paperMirrorObjective x g γ (pointOfChart u hu) := by
    intro u hu
    simp [pointOfChart, Φ, paperMirrorObjective, SOptLib.paperMirrorObjective,
      MirrorDescentSetup.V, carrierBregmanDivergence, vGradExtension, carrierGradientFrom,
      carrierChartFunction]
    exact SOptLib.totalizeOn_of_mem setup.X setup.v (by simpa [T] using hu)
  have hchart_z :
      Φ (carrierChartPoint setup.X setup.x1 z) =
        setup.paperMirrorObjective x g γ z := by
    have hz_total :
        SOptLib.totalizeOn setup.X setup.v
            (((SOptLib.carrierAffineSpanChart setup.X setup.x1)
              (carrierChartPoint setup.X setup.x1 z) : affineSpan ℝ setup.X) :
                DecisionSpace m) =
          setup.v z := by
      rw [← SOptLib.carrierChartToAmbient_apply setup.X setup.x1
        (carrierChartPoint setup.X setup.x1 z)]
      change SOptLib.totalizeOn setup.X setup.v
          (carrierChartToAmbient setup.X setup.x1 (carrierChartPoint setup.X setup.x1 z)) =
        setup.v z
      rw [carrierChartToAmbient_chartPoint]
      exact SOptLib.totalizeOn_of_mem setup.X setup.v z.2
    simp [Φ, paperMirrorObjective, SOptLib.paperMirrorObjective, MirrorDescentSetup.V,
      carrierBregmanDivergence, vGradExtension, carrierGradientFrom, carrierChartFunction,
      carrierChartToAmbient_chartPoint, hz_total]
  have hmin_chart : ∀ u ∈ T, Φ (carrierChartPoint setup.X setup.x1 z) ≤ Φ u := by
    intro u hu
    rw [hchart_z, hpointOfChart u hu]
    exact hzmin (pointOfChart u hu)
  have hfoc : 0 ≤ F' (carrierChartPoint setup.X setup.x1 y -
      carrierChartPoint setup.X setup.x1 z) := by
    exact Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt
      hTconv hz_chart hy_chart hmin_chart
      (paperMirrorObjective_chart_hasFDerivWithinAt_for_unique (setup := setup) x g γ z)
  have hF_apply :
      F' (carrierChartPoint setup.X setup.x1 y -
          carrierChartPoint setup.X setup.x1 z) =
        ⟪γ • g +
            carrierGradientFrom setup.X setup.v setup.x1 z -
            carrierGradientFrom setup.X setup.v setup.x1 x,
          y.1 - z.1⟫_ℝ := by
    have hcoord :
        ((carrierChartPoint setup.X setup.x1 y : A.direction) : DecisionSpace m) -
            ((carrierChartPoint setup.X setup.x1 z : A.direction) : DecisionSpace m) =
          y.1 - z.1 := by
      simpa [A] using carrierChartPoint_sub_subtypeL_for_unique setup.X setup.x1 z y
    dsimp [F']
    simp [hcoord]
  simpa [hF_apply] using hfoc

/-- Uniqueness of the paper mirror objective minimizer.

This is the mathematical strong-convexity bridge: the objective is linear plus the
strongly convex Bregman term in the candidate point, so two global minimizers on the
compact feasible carrier must coincide. -/
private theorem paperMirrorObjective_argmin_unique
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (z z' : setup.Point)
    (hzmin : ∀ y : setup.Point,
      setup.paperMirrorObjective x g γ z ≤ setup.paperMirrorObjective x g γ y)
    (hz'min : ∀ y : setup.Point,
      setup.paperMirrorObjective x g γ z' ≤ setup.paperMirrorObjective x g γ y) :
    z = z' := by
  exact SOptLib.paperMirrorObjective_argmin_unique_of_strict_bregman
    (V := setup.V) (eval := fun y : setup.Point => y.1)
    (grad := fun y : setup.Point => carrierGradientFrom setup.X setup.v setup.x1 y)
    (obj := setup.paperMirrorObjective x g γ) (fun _ _ h => Subtype.ext h) x g γ z z'
    (by
      intro a b hmin
      exact setup.paperMirrorObjective_argmin_variational_for_unique x g γ a b hmin)
    (by
      intro a b
      simpa [vGradExtension, carrierGradientFrom] using
        setup.V_symm_eq_gradient_monotonicity_inner a b)
    (by
      intro a b
      exact setup.V_symm_lower_bound_all_carrier a b)
    hzmin hz'min

/-- Closed-graph part of the compact argmin selector argument.

Any cluster point of selected prox steps along parameters converging to `p0` still
minimizes the limiting objective, by joint continuity and closedness of `≤` in `ℝ`. -/
private theorem proxStep_mapClusterPt_minimizes
    (hjoint : Continuous (fun q : (setup.Point × DecisionSpace m × ℝ) × setup.Point =>
      setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 q.2))
    (p0 : setup.Point × DecisionSpace m × ℝ) (z : setup.Point)
    (hzcluster : MapClusterPt z (𝓝 p0)
      (fun p : setup.Point × DecisionSpace m × ℝ =>
        setup.proxStep p.1 p.2.1 p.2.2)) :
    ∀ y : setup.Point,
      setup.paperMirrorObjective p0.1 p0.2.1 p0.2.2 z ≤
        setup.paperMirrorObjective p0.1 p0.2.1 p0.2.2 y := by
  intro y
  let P : Type _ := setup.Point × DecisionSpace m × ℝ
  let step : P → setup.Point := fun p => setup.proxStep p.1 p.2.1 p.2.2
  let graph : P → P × setup.Point := fun p => (p, step p)
  let C : Set (P × setup.Point) := {q |
    setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 q.2 ≤
      setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 y}
  have hCclosed : IsClosed C := by
    have hleft : Continuous (fun q : P × setup.Point =>
        setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 q.2) := by
      simpa [P] using hjoint
    have hright : Continuous (fun q : P × setup.Point =>
        setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 y) := by
      simpa [P] using hjoint.comp (continuous_fst.prodMk continuous_const)
    simpa [C] using isClosed_le hleft hright
  have hgraph_cluster : MapClusterPt (p0, z) (𝓝 p0) graph := by
    exact mapClusterPt_graph_of_tendsto_of_mapClusterPt
      (f := step) (a := p0) (b := z)
      (continuous_id.continuousAt : Filter.Tendsto id (𝓝 p0) (𝓝 p0))
      (by simpa [step] using hzcluster)
  have hevent : ∀ᶠ p in 𝓝 p0, graph p ∈ C := by
    exact Filter.Eventually.of_forall fun p => by
      dsimp [graph, step, C, P]
      exact setup.proxStep_minimizes p.1 p.2.1 p.2.2 y
  have hmem : (p0, z) ∈ C :=
    hCclosed.mem_of_mapClusterPt hgraph_cluster hevent
  simpa [C] using hmem

/-- Compact unique-argmin continuity bridge for the canonical prox selector.

This is the remaining topological selection theorem: joint continuity of the objective,
compactness of the candidate carrier, and uniqueness of minimizers force the `Classical.choose`
argmin selector to vary continuously with the parameter. -/
private theorem proxStep_continuous_of_joint_continuous
    (hjoint : Continuous (fun q : (setup.Point × DecisionSpace m × ℝ) × setup.Point =>
      setup.paperMirrorObjective q.1.1 q.1.2.1 q.1.2.2 q.2)) :
    Continuous (fun p : setup.Point × DecisionSpace m × ℝ =>
      setup.proxStep p.1 p.2.1 p.2.2) := by
  classical
  let P : Type _ := setup.Point × DecisionSpace m × ℝ
  let step : P → setup.Point := fun p => setup.proxStep p.1 p.2.1 p.2.2
  change Continuous step
  haveI : CompactSpace setup.Point := isCompact_iff_compactSpace.mp setup.X_isCompact
  exact continuous_argmin_of_compact_unique
    (F := fun p : P => fun z : setup.Point =>
      setup.paperMirrorObjective p.1 p.2.1 p.2.2 z)
    (sel := step)
    (by simpa [P] using hjoint)
    (by
      intro p y
      exact setup.proxStep_minimizes p.1 p.2.1 p.2.2 y)
    (by
      intro p z z' hzmin hz'min
      exact setup.paperMirrorObjective_argmin_unique p.1 p.2.1 p.2.2 z z' hzmin hz'min)

/-- Continuity of the canonical compact-argmin prox selector. -/
private theorem proxStep_continuous :
    Continuous (fun p : setup.Point × DecisionSpace m × ℝ =>
      setup.proxStep p.1 p.2.1 p.2.2) := by
  exact setup.proxStep_continuous_of_joint_continuous
    setup.paperMirrorObjective_joint_continuous

/-- Expanded source-facing argmin semantics of the canonical prox step.

This replaces the former `MirrorDescentSetup` field with a derived theorem from the
compact argmin realization. -/
theorem h_proxStep_minimizes
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
        γ * ⟪g, (setup.proxStep x g γ).1⟫_ℝ +
        (setup.v (setup.proxStep x g γ) - setup.v x -
          ⟪carrierGradientFrom setup.X setup.v setup.x1 x,
            (setup.proxStep x g γ).1 - x.1⟫_ℝ) ≤
      γ * ⟪g, y.1⟫_ℝ +
        (setup.v y - setup.v x -
          ⟪carrierGradientFrom setup.X setup.v setup.x1 x, y.1 - x.1⟫_ℝ) := by
  simpa [MirrorDescentSetup.proxStep, MirrorDescentSetup.V, carrierBregmanDivergence,
    vGradExtension, vInteriorAmbient] using
    (SOptLib.proxStep_minimizes_expanded (V := setup.V) (eval := fun y : setup.Point => y.1)
      setup.point_univ_isCompact (continuousOn_univ.mp setup.V_continuousOn_carrier)
      continuous_subtype_val x g γ y)

/-- Backward-compatible name for the canonical paper prox step. -/
noncomputable def mirrorStep
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) : setup.Point :=
  _root_.mirrorStep setup.proxStep x g γ

/-- The canonical mirror-step output realizes the paper argmin semantics. -/
theorem mirrorStep_isMirrorStep
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    setup.IsMirrorStep x g γ (setup.mirrorStep x g γ) := by
  simpa [MirrorDescentSetup.IsMirrorStep, MirrorDescentSetup.paperMirrorObjective,
    MirrorDescentSetup.mirrorStep] using
    (_root_.mirrorStep_isMirrorStep (V := setup.V) (eval := fun y : setup.Point => y.1)
      setup.proxStep (fun x g γ => setup.proxStep_isMirrorStep x g γ) x g γ)

/-- The backward-compatible mirror-step name is definitionally the canonical prox selector. -/
theorem mirrorStep_eq_proxStep
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    setup.mirrorStep x g γ = setup.proxStep x g γ := by
  exact SOptLib.mirrorStep_eq_proxStep setup.proxStep x g γ

/-- Measurability of the canonical compact-argmin prox selector.

The proof route is the measurable maximum theorem for a compact feasible carrier and a
continuous, uniquely minimizing strongly convex mirror objective. It is kept as a derived
theorem rather than a setup field, so adaptiveness of the iterate process is no longer
primitive stochastic data. -/
theorem proxStep_measurable :
    Measurable (fun p : setup.Point × DecisionSpace m × ℝ =>
      setup.proxStep p.1 p.2.1 p.2.2) := by
  letI : CompactSpace setup.Point := isCompact_iff_compactSpace.mp setup.X_isCompact
  exact proxStep_measurable_of_joint_continuous_unique
    (F := fun x g γ y => setup.paperMirrorObjective x g γ y)
    (sel := fun x g γ => setup.proxStep x g γ)
    setup.paperMirrorObjective_joint_continuous
    (by intro x g γ y; exact setup.proxStep_minimizes x g γ y)
    (by
      intro x g γ z z' hzmin hz'min
      exact setup.paperMirrorObjective_argmin_unique x g γ z z' hzmin hz'min)

/-- Measurability of the backward-compatible `mirrorStep` name. -/
theorem mirrorStep_measurable :
    Measurable (fun p : setup.Point × DecisionSpace m × ℝ =>
      setup.mirrorStep p.1 p.2.1 p.2.2) := by
  exact _root_.mirrorStep_measurable_of_eq_proxStep setup.proxStep_measurable
    (fun x g γ => setup.mirrorStep_eq_proxStep x g γ)

/-- Composition form of prox-step measurability for recursive stochastic iterates. -/
theorem proxStep_comp_measurable
    {Ω' : Type*} [MeasurableSpace Ω']
    {x : Ω' → setup.Point} {g : Ω' → DecisionSpace m} {γ : Ω' → ℝ}
    (hx : Measurable x) (hg : Measurable g) (hγ : Measurable γ) :
    Measurable (fun ω => setup.proxStep (x ω) (g ω) (γ ω)) := by
  exact Measurable.proxStep_comp setup.proxStep_measurable hx hg hγ

/-- The public prox step satisfies the literal paper argmin semantics. -/
theorem mirrorStep_isLiteralMirrorStep
    (x : setup.InteriorPoint) (g : DecisionSpace m) (γ : ℝ) :
    setup.IsLiteralMirrorStep x g γ (setup.mirrorStep x.toPoint g γ) := by
  exact SOptLib.isLiteralMirrorStep_of_isMirrorStep
    (paper := setup.paperMirrorObjective)
    (literal := setup.literalMirrorObjective)
    (toPoint := fun x : setup.InteriorPoint => x.toPoint)
    (step := setup.mirrorStep)
    (fun x g γ => by
      simpa [MirrorDescentSetup.IsMirrorStep] using setup.mirrorStep_isMirrorStep x g γ)
    (fun x g γ y => by
      simpa using setup.literalMirrorObjective_eq_paperMirrorObjective x g γ y)
    x g γ

/-- The canonical mirror step is an `X`-valued paper point. -/
theorem mirrorStep_mem
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) :
    (setup.mirrorStep x g γ).1 ∈ setup.X := by
  exact (setup.mirrorStep x g γ).2

/-- The canonical mirror step minimizes the paper prox objective over `X`. -/
theorem mirrorStep_minimizes
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    setup.paperMirrorObjective x g γ (setup.mirrorStep x g γ) ≤
      setup.paperMirrorObjective x g γ y := by
  have h_mirrorStep_isMirrorStep :
      ∀ x' g' γ', SOptLib.IsMirrorStep setup.V (fun y : setup.Point => y.1) x' g' γ'
        (setup.mirrorStep x' g' γ') := by
    intro x' g' γ'
    change setup.IsMirrorStep x' g' γ' (setup.mirrorStep x' g' γ')
    exact setup.mirrorStep_isMirrorStep (x := x') (g := g') (γ := γ')
  exact _root_.mirrorStep_minimizes
    (V := setup.V) (eval := fun y : setup.Point => y.1)
    (mirrorStep := fun x g γ => setup.mirrorStep x g γ)
    (h_mirrorStep_isMirrorStep := h_mirrorStep_isMirrorStep)
    x g γ y

/-- Scalar one-sided first-order condition at a minimum on `[0,1]`. -/
private theorem right_derivative_nonneg_of_min_on_Icc
    {φ : ℝ → ℝ} {D : ℝ}
    (hderiv : HasDerivWithinAt φ D (Set.Icc (0 : ℝ) 1) 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t) :
    0 ≤ D := by
  exact _root_.right_derivative_nonneg_of_min_on_Icc hderiv hmin

/-- First-order condition for a constrained minimizer in a Hilbert chart. -/
private theorem constrained_first_order_condition_chart
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : Set H} {Φ : H → ℝ} {z y : H} {F' : H →L[ℝ] ℝ}
    (hTconv : Convex ℝ T) (hz : z ∈ T) (hy : y ∈ T)
    (hmin : ∀ u ∈ T, Φ z ≤ Φ u)
    (hderiv : HasFDerivWithinAt Φ F' T z) :
    0 ≤ F' (y - z) := by
  exact Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt hTconv hz hy hmin hderiv

/-- Difference of two feasible chart coordinates, included back into ambient space. -/
private theorem carrierChartPoint_sub_subtypeL
    (X : Set E) (anchor x y : {x : E // x ∈ X}) :
    let A : AffineSubspace ℝ E := carrierAffineSpan X
    (A.direction.subtypeL)
      (carrierChartPoint X anchor y - carrierChartPoint X anchor x) = y.1 - x.1 := by
  classical
  let A : AffineSubspace ℝ E := carrierAffineSpan X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let L : A.direction →ᴬ[ℝ] E := carrierChartToAmbient X anchor
  let uy : A.direction := carrierChartPoint X anchor y
  let ux : A.direction := carrierChartPoint X anchor x
  have hlin : L.contLinear (uy - ux) = L uy - L ux := by
    simpa [vsub_eq_sub] using L.contLinear_map_vsub uy ux
  have hy : L uy = y.1 := by
    simpa [A, L, uy] using carrierChartToAmbient_chartPoint X anchor y
  have hx : L ux = x.1 := by
    simpa [A, L, ux] using carrierChartToAmbient_chartPoint X anchor x
  have hLlin_apply : L.contLinear (uy - ux) = (A.direction.subtypeL) (uy - ux) := by
    let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
    let xA : A := ⟨x.1, subset_affineSpan ℝ X x.2⟩
    let yA : A := ⟨y.1, subset_affineSpan ℝ X y.2⟩
    have hamb : L.contLinear (uy - ux) = y.1 - x.1 := by
      rw [hlin, hy, hx]
    have hchart₀ :
        (A.direction.subtypeL)
          ((AffineIsometryEquiv.vaddConst ℝ a).symm yA -
            (AffineIsometryEquiv.vaddConst ℝ a).symm xA) =
            (yA : E) - (xA : E) :=
      affineSpan_chartPoint_sub_subtypeL A a xA yA
    have hchart :
        (A.direction.subtypeL) (uy - ux) = y.1 - x.1 := by
      convert hchart₀ using 1
    exact hamb.trans hchart.symm
  change (A.direction.subtypeL) (uy - ux) = y.1 - x.1
  rw [← hLlin_apply, hlin, hy, hx]

/-- Derivative of the charted paper mirror objective at a feasible minimizer. -/
private theorem paperMirrorObjective_chart_hasFDerivWithinAt
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (z : setup.Point) :
    let A : AffineSubspace ℝ (DecisionSpace m) := carrierAffineSpan setup.X
    let T : Set A.direction := carrierChartSet setup.X setup.x1
    let Φ : A.direction → ℝ := fun u =>
      γ * ⟪g, carrierChartToAmbient setup.X setup.x1 u⟫_ℝ +
        (carrierChartFunction setup.X setup.v setup.x1 u - setup.v x -
          ⟪carrierGradientFrom setup.X setup.v setup.x1 x,
            carrierChartToAmbient setup.X setup.x1 u - x.1⟫_ℝ)
    let F' : A.direction →L[ℝ] ℝ :=
      (innerSL ℝ
        (γ • g +
          carrierGradientFrom setup.X setup.v setup.x1 z -
          carrierGradientFrom setup.X setup.v setup.x1 x)).comp
        (A.direction.subtypeL)
    HasFDerivWithinAt Φ F' T (carrierChartPoint setup.X setup.x1 z) := by
  classical
  let A : AffineSubspace ℝ (DecisionSpace m) := carrierAffineSpan setup.X
  haveI : Nonempty A := ⟨⟨setup.x1.1, subset_affineSpan ℝ setup.X setup.x1.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ (DecisionSpace m)) : Set (DecisionSpace m)) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := carrierChartSet setup.X setup.x1
  let L : A.direction →ᴬ[ℝ] DecisionSpace m := carrierChartToAmbient setup.X setup.x1
  let f : A.direction → ℝ := carrierChartFunction setup.X setup.v setup.x1
  let uz : A.direction := carrierChartPoint setup.X setup.x1 z
  let gradz : DecisionSpace m := carrierGradientFrom setup.X setup.v setup.x1 z
  let gradx : DecisionSpace m := carrierGradientFrom setup.X setup.v setup.x1 x
  have huz : uz ∈ T := by
    simpa [T, uz] using carrierChartPoint_mem setup.X setup.x1 z
  have hLlin_eq : L.contLinear = A.direction.subtypeL := by
    let a : A := ⟨setup.x1.1, subset_affineSpan ℝ setup.X setup.x1.2⟩
    have hL_apply : ∀ du : A.direction, L du = (du : DecisionSpace m) + a := by
      intro du
      change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
          du : A) : DecisionSpace m) = (du : DecisionSpace m) + a
      simp [L, a]
    simpa using (AffineSubspace.vaddConst_contLinear_eq_subtypeL (A := A) (a := a) (L := L) hL_apply)
  have hLder :
      HasFDerivWithinAt (fun u : A.direction => L u) A.direction.subtypeL T uz := by
    have hLhas : HasFDerivWithinAt (fun u : A.direction => L u) L.contLinear T uz := by
      rw [L.decomp]
      exact L.contLinear.hasFDerivWithinAt.add_const (L 0)
    simpa [hLlin_eq] using hLhas
  have hvder :
      HasFDerivWithinAt f (((innerSL ℝ) gradz).comp A.direction.subtypeL) T uz := by
    have hfcont : ContDiffOn ℝ 1 f T := by
      simpa [T, f] using
        carrierChartFunction_contDiffOn setup.X setup.v setup.x1
          setup.hv_contDiff_on_interior.2
    have hgrad :
        fderivWithin ℝ f T uz =
          (((innerSL ℝ) gradz).comp A.direction.subtypeL) := by
      ext du
      dsimp [gradz]
      unfold carrierGradientFrom
      change (fderivWithin ℝ f T uz) du =
        ⟪((@gradientWithin ℝ A.direction _ _ _ instComplete f T uz : A.direction) :
            DecisionSpace m),
          (du : DecisionSpace m)⟫_ℝ
      rw [← A.direction.coe_inner
        (@gradientWithin ℝ A.direction _ _ _ instComplete f T uz) du]
      simp [gradientWithin]
      rfl
    exact
      hasFDerivWithinAt_of_contDiffOn_gradientWithin_comp
        (T := T) (f := f) (L' := A.direction.subtypeL)
        (u := uz) (grad := gradz) hfcont huz hgrad
  exact carrier_charted_mirrorObjective_hasFDerivWithinAt
    (T := T) (chart := carrierChartPoint setup.X setup.x1)
    (L := fun u : A.direction => L u) (L' := A.direction.subtypeL)
    (f := f) (eval := fun p => p.1) (v := setup.v)
    (grad := carrierGradientFrom setup.X setup.v setup.x1)
    (x := x) (z := z) (g := g) (γ := γ) hLder hvder

/-- First-order variational inequality for a carrier minimizer of the paper mirror
objective.

This is the route-local calculus bridge behind Lan Lemma 3.4, proof step 1.  The
intended proof differentiates the one-sided feasible segment from `z` to `y`, uses
`hzmin` to show the endpoint derivative is nonnegative, and identifies the derivative
through the affine-span carrier gradient `carrierGradientFrom`. -/
private theorem paperMirrorObjective_argmin_variational
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (z y : setup.Point)
    (hzmin : ∀ u : setup.Point,
      setup.paperMirrorObjective x g γ z ≤ setup.paperMirrorObjective x g γ u) :
    0 ≤
      ⟪γ • g +
          carrierGradientFrom setup.X setup.v setup.x1 z -
          carrierGradientFrom setup.X setup.v setup.x1 x,
        y.1 - z.1⟫_ℝ := by
  exact setup.paperMirrorObjective_argmin_variational_for_unique x g γ z y hzmin

/-- Derived first-order variational inequality for the selected prox step.

This is Lan Lemma 3.4's first proof step, derived from the stated argmin semantics
`h_proxStep_minimizes` rather than stored as setup data. The proof route is the standard
Mathlib convex first-order optimality path for an `IsMinOn` objective over the feasible
carrier, specialized to the Bregman objective. -/
theorem h_proxStep_variational
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    0 ≤
      ⟪γ • g +
          carrierGradientFrom setup.X setup.v setup.x1 (setup.proxStep x g γ) -
          carrierGradientFrom setup.X setup.v setup.x1 x,
        y.1 - (setup.proxStep x g γ).1⟫_ℝ := by
  exact mirrorStep_variational
    (mirrorStep := setup.proxStep)
    (objective := fun x' g' γ' y' => setup.paperMirrorObjective x' g' γ' y')
    (grad := fun y' => carrierGradientFrom setup.X setup.v setup.x1 y')
    (eval := fun y' : setup.Point => y'.1)
    (h_mirrorStep_minimizes := setup.proxStep_minimizes)
    (h_variational := setup.paperMirrorObjective_argmin_variational)
    x g γ y

/-- The source-backed first-order variational inequality for the selected mirror step. -/
theorem mirrorStep_variational
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    0 ≤
      ⟪γ • g + setup.vGradExtension (setup.mirrorStep x g γ) - setup.vGradExtension x,
        y.1 - (setup.mirrorStep x g γ).1⟫_ℝ := by
  exact
    _root_.mirrorStep_variational
      (mirrorStep := setup.mirrorStep)
      (grad := fun x : setup.Point => setup.vGradExtension x)
      (eval := fun x : setup.Point => x.1)
      (objective := setup.paperMirrorObjective)
      (h_mirrorStep_minimizes := setup.mirrorStep_minimizes)
      (h_variational :=
        by
          intro x g γ z y hzmin
          simpa [vGradExtension] using setup.paperMirrorObjective_argmin_variational x g γ z y hzmin)
      x g γ y

/-- Carrier-level Bregman three-point identity for the within-gradient realization of `V`. -/
private theorem V_three_point_identity
    (x z y : setup.Point) :
    setup.V x y =
      setup.V x z + ⟪setup.vGradExtension z - setup.vGradExtension x, y.1 - z.1⟫_ℝ +
        setup.V z y := by
  exact carrierBregmanDivergence_three_point_identity setup.v
    (fun x : setup.Point => x.1) (fun x : setup.Point => setup.vGradExtension x)
    setup.V (by intro x z; rfl) x z y

/-- Lemma 3.4 specialized to the canonical mirror step. -/
theorem mirrorStep_three_point
    (x : setup.Point) (g : DecisionSpace m) (γ : ℝ) (y : setup.Point) :
    γ * ⟪g, (setup.mirrorStep x g γ).1 - y.1⟫_ℝ +
      setup.V x (setup.mirrorStep x g γ) ≤
        setup.V x y -
          setup.V (setup.mirrorStep x g γ) y := by
  simpa using
    (mirror_descent_three_point_of_variational_carrier
      (V := setup.V)
      (eval := fun x' : setup.Point => x'.1)
      (grad := setup.vGradExtension)
      (x := x)
      (z := setup.mirrorStep x g γ)
      (y := y)
      (g := g)
      (γ := γ)
      (h_variational := setup.mirrorStep_variational x g γ y)
      (h_three_point := setup.V_three_point_identity x (setup.mirrorStep x g γ) y))

end MirrorDescentSetup

/-- Internal stochastic realization of the paper random vector `ξ` and the i.i.d. sample
stream `ξ₁, ξ₂, ...` together with the expectation-level assumptions. -/
structure MirrorDescentProcess
    {m d : ℕ} (setup : MirrorDescentSetup m d)
    (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] where
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"X ⊂ ℝ^m nonempty bounded closed convex; ξ random vector on Ξ ⊂ ℝ^d; F : X × Ξ → ℝ"`. -/
  ξ : Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ}
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math` ::
  `"ξ random vector on Ξ ⊂ ℝ^d"`. -/
  hξ_measurable : Measurable ξ
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math` ::
  `"It is possible to generate i.i.d. samples ξ_1, ξ_2, ... of realizations of ξ"`. -/
  ξt : {t : ℕ // 1 ≤ t} → Ω → {ξ : SampleSpace d // ξ ∈ setup.Ξ}
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math` ::
  `"i.i.d. samples ξ_1, ξ_2, ... of realizations of ξ"`, modeled as measurable
  sample random variables. -/
  hξt_measurable : ∀ t, Measurable (ξt t)
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math` ::
  `"It is possible to generate i.i.d. samples ξ_1, ξ_2, ... of realizations of ξ"`. -/
  hξt_iIndep : iIndepFun ξt volume
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math` ::
  `"It is possible to generate i.i.d. samples ξ_1, ξ_2, ... of realizations of ξ"`. -/
  hξt_identDistrib : ∀ t, IdentDistrib (ξt t) ξ volume volume
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/2/math` ::
  `"∀ x ∈ X, ξ ∈ Ξ, the SFO returns G(x, ξ) such that g(x) := E[G(x, ξ)] is well defined"`. -/
  h_oracle_wellDefined :
    ∀ x : {x : DecisionSpace m // x ∈ setup.X},
      oracleWellDefined setup ξ x
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/problem/math` ::
  `"f(x) := E[F(x, ξ)]"`, recording that the objective expectation is well defined
  for every feasible decision. -/
  h_objective_wellDefined :
    ∀ x : {x : DecisionSpace m // x ∈ setup.X},
      objectiveWellDefined setup ξ x
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/3/math` ::
  `"E[G(x, ξ)] = f'(x) ∈ ∂f(x), ∀ x ∈ X"` -/
  h_meanOracle_subgradient :
    ∀ x : {x : DecisionSpace m // x ∈ setup.X},
      oracleMean setup ξ x ∈
        carrierSubdifferential setup.X (objectiveExpectation setup ξ) x
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/6/math` ::
  `"‖g(x)‖_* ≤ M, ∀ x ∈ X"`. -/
  M : ℝ
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/6/parameters/0` ::
  `"M > 0"`. -/
  hM_pos : 0 < M
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/6/math` ::
  `"‖g(x)‖_* ≤ M, ∀ x ∈ X"`. -/
  h_meanOracle_norm :
    ∀ x : {x : DecisionSpace m // x ∈ setup.X}, dualNorm (oracleMean setup ξ x) ≤ M
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/4/math` ::
  `"E[‖G(x, ξ_t) - f'(x)‖_*^2] ≤ σ^2, ∀ x ∈ X"`. -/
  sigmaSq : ℝ
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/4/parameters/0` ::
  `"σ^2 ≥ 0"`. -/
  h_sigmaSq_nonneg : 0 ≤ sigmaSq
  /-- `book/FOML/StochasticMirrorDescent.json#/assumptions/4/math` ::
  `"E[‖G(x, ξ_t) - f'(x)‖_*^2] ≤ σ^2, ∀ x ∈ X"`.

  The paper's expectation notation entails that the sampled fixed-point variance
  expectation is well-defined; this field records that source-backed fixed-`x`
  fact together with the stated bound. -/
  h_oracle_variance :
    ∀ x : {x : DecisionSpace m // x ∈ setup.X},
      ∀ t : {t : ℕ // 1 ≤ t},
        oracleSampleVarianceWellDefined setup ξ ξt x t ∧
          oracleSampleVariance setup ξ ξt x t ≤ sigmaSq
  /-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization/math` ::
  `"x_1 ∈ X"`.
  `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/steps/0/math` ::
  `"x_{t+1} = argmin_{x ∈ X} {γ_t ⟨G_t, x⟩ + V(x_t, x)}, t = 1, 2, ..."`.
  This is the paper iterate process on the feasible carrier. -/
  xProcess : {t : ℕ // 1 ≤ t} → Ω → {x : DecisionSpace m // x ∈ setup.X}
  /-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/initialization/math` ::
  `"x_1 ∈ X"`. -/
  h_xProcess_init :
    xProcess ⟨1, le_rfl⟩ = fun _ => setup.x1
  /-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/steps/0/math` ::
  `"x_{t+1} = argmin_{x ∈ X} {γ_t ⟨G_t, x⟩ + V(x_t, x)}, t = 1, 2, ..."`.

  The update is routed through the canonical compact-argmin prox selector defined in
  `MirrorDescentSetup.proxStep`, not through an arbitrary process-local selector. -/
  h_xProcess_update :
    ∀ t : {t : ℕ // 1 ≤ t},
      xProcess ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩ = fun ω =>
        setup.proxStep (xProcess t ω) (setup.oracle (xProcess t ω) (ξt t ω)) (setup.γ t)
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/problem/math` ::
  `"f^* ≡ min_{x ∈ X} { f(x) := E[F(x, ξ)] }"`.

  The source theorem uses a paper optimizer `x^*`; this field records the selected minimizer
  named by that `min` statement, on the already-defined objective expectation. -/
  xStarSource : {x : DecisionSpace m // x ∈ setup.X}
  /-- `book/FOML/StochasticMirrorDescent.json#/setup/problem/math` ::
  `"f^* ≡ min_{x ∈ X} { f(x) := E[F(x, ξ)] }"`. -/
  h_xStarSource_minimizes :
    ∀ z : {z : DecisionSpace m // z ∈ setup.X},
      objectiveExpectation setup ξ xStarSource ≤ objectiveExpectation setup ξ z

namespace MirrorDescentProcess

variable {m d : ℕ}
variable {setup : MirrorDescentSetup m d}
variable (proc : MirrorDescentProcess setup Ω)

/-- Paper-level well-definedness predicate for a scalar expectation `E[Z]`.

Lean realizes the paper expectation by the Bochner integral `∫ ω, Z ω`; this predicate
records the source-facing condition under which that realization is a genuine paper
expectation rather than merely Lean's totalized surrogate. -/
def ExpectationWellDefined (proc : MirrorDescentProcess setup Ω) (Z : Ω → ℝ) : Prop :=
  let _ := proc
  SOptLib.expectationWellDefined volume Z

/-- The paper expectation operator `E[Z]`.

This is implemented by Lean's Bochner integral `∫ ω, Z ω`; the public predicate
`ExpectationWellDefined` is the paper-facing bridge asserting when the integrand is
well defined. -/
noncomputable def expectation (proc : MirrorDescentProcess setup Ω) (Z : Ω → ℝ) : ℝ :=
  let _ := proc
  SOptLib.expectation volume Z

/-- Lean realizes the paper expectation by the Bochner integral. -/
theorem expectation_def (Z : Ω → ℝ) :
    proc.expectation Z = ∫ ω, Z ω := by
  simpa [MirrorDescentProcess.expectation, SOptLib.expectation] using
    (SOptLib.expectation_def (μ := volume) (Z := Z))

/-- `ExpectationWellDefined` is exactly integrability of the paper random variable. -/
theorem expectationWellDefined_iff (Z : Ω → ℝ) :
    proc.ExpectationWellDefined Z ↔ Integrable Z := by
  simpa [MirrorDescentProcess.ExpectationWellDefined, SOptLib.expectationWellDefined] using
    (SOptLib.expectationWellDefined_iff_integrable (μ := volume) (Z := Z))

/-- `book/FOML/StochasticMirrorDescent.json#/setup/problem/math` ::
`"f^* ≡ min_{x ∈ X} { f(x) := E[F(x, ξ)] }"`. -/
noncomputable def f (x : setup.Point) : ℝ :=
  SOptLib.paperObjective (μ := volume) (F := setup.F) (ξ := proc.ξ) x

/-- `book/FOML/StochasticMirrorDescent.json#/assumptions/2/math` ::
`"∀ x ∈ X, ξ ∈ Ξ, the SFO returns G(x, ξ) such that g(x) := E[G(x, ξ)] is well defined"`. -/
noncomputable def g (x : setup.Point) : DecisionSpace m :=
  SOptLib.paperMeanOracle (μ := volume) (G := setup.oracle) (ξ := proc.ξ) x

/-- The paper objective `f(x) := E[F(x, ξ)]` is well defined for every `x ∈ X`. -/
theorem f_wellDefined (x : setup.Point) :
    objectiveWellDefined setup proc.ξ x := by
  simpa [objectiveWellDefined, objectiveKernel, SOptLib.objectiveWellDefined] using
    (SOptLib.paperObjective_wellDefined
      (μ := (volume : Measure Ω)) (F := setup.F)
      (ξ := proc.ξ) (x := x)
      (by simpa [objectiveWellDefined, objectiveKernel] using proc.h_objective_wellDefined x))

/-- The random variable `ω ↦ F(x, ξ(ω))` is a well-defined paper expectation. -/
theorem f_expectationWellDefined (x : setup.Point) :
    proc.ExpectationWellDefined (fun ω => setup.F x (proc.ξ ω)) := by
  simpa [MirrorDescentProcess.ExpectationWellDefined] using
    SOptLib.expectationWellDefined_objectiveKernel_of_objectiveWellDefined
      (μ := (volume : Measure Ω)) (F := setup.F) (ξ := proc.ξ) (x := x) (by
        simpa [objectiveWellDefined, objectiveKernel, SOptLib.objectiveKernel] using
          proc.f_wellDefined x)

/-- The paper mean oracle is well defined for every `x ∈ X`. -/
theorem g_wellDefined (x : setup.Point) :
    oracleWellDefined setup proc.ξ x := by
  simpa [oracleWellDefined, SOptLib.oracleWellDefined, oracleKernel, SOptLib.oracleKernel] using
    (SOptLib.paperMeanOracle_wellDefined
      (μ := (volume : Measure Ω)) (G := setup.oracle) (ξ := proc.ξ) (x := x)
      (by simpa [oracleWellDefined, SOptLib.oracleWellDefined, oracleKernel, SOptLib.oracleKernel] using
        proc.h_oracle_wellDefined x))

/-- The objective kernel bridge `f(x) = E[F(x, ξ)]`. -/
theorem f_def (x : setup.Point) :
    proc.f x = proc.expectation (fun ω => setup.F x (proc.ξ ω)) := by
  simpa [MirrorDescentProcess.f, MirrorDescentProcess.expectation, SOptLib.paperObjective] using
    (SOptLib.paperObjective_def (μ := volume) (F := setup.F) (ξ := proc.ξ) (x := x))

/-- The sample process realizes the same one-sample expectation as the paper random
vector `ξ`. -/
theorem f_eq_sample_expectation (x : setup.Point) (t : {t : ℕ // 1 ≤ t}) :
    proc.expectation (fun ω => setup.F x (proc.ξt t ω)) = proc.f x := by
  have hdist : IdentDistrib (proc.ξt t) (proc.ξ) volume volume := proc.hξt_identDistrib t
  have hcomp :
      ∫ ω, setup.F x (proc.ξt t ω) ∂volume = ∫ ω, setup.F x (proc.ξ ω) ∂volume :=
    hdist.integral_comp_eq_of_measurable (setup.hF_measurable x)
  calc
    proc.expectation (fun ω => setup.F x (proc.ξt t ω)) =
        ∫ ω, setup.F x (proc.ξt t ω) := rfl
    _ = ∫ ω, setup.F x (proc.ξ ω) := hcomp
    _ = proc.f x := rfl

/-- The oracle mean bridge `g(x) = E[G(x, ξ)]`. -/
theorem g_def (x : setup.Point) :
    proc.g x = ∫ ω, setup.oracle x (proc.ξ ω) := by
  simpa [MirrorDescentProcess.g, SOptLib.paperMeanOracle] using
    (SOptLib.paperMeanOracle_def (μ := volume) (G := setup.oracle) (ξ := proc.ξ) (x := x))

/-- The base random vector `ξ` induces the corresponding oracle deviation integral around
the paper mean oracle `g(x)`. This is internal scaffolding; Eq. (4.1.4) is exported
below on the sampled realizations `ξ_t`. -/
theorem oracle_variance_def (x : setup.Point) :
    oracleVariance setup proc.ξ x =
      proc.expectation (fun ω => dualNorm (setup.oracle x (proc.ξ ω) - proc.g x) ^ 2) := by
  rfl

/-- The sampled oracle process has the same one-sample expectation as the base oracle
kernel. -/
theorem g_eq_sample_expectation (x : setup.Point) (t : {t : ℕ // 1 ≤ t}) :
    ∫ ω, setup.oracle x (proc.ξt t ω) = proc.g x := by
  have hdist :
      IdentDistrib (fun ω => setup.oracle x (proc.ξt t ω))
        (fun ω => setup.oracle x (proc.ξ ω)) volume volume :=
    (proc.hξt_identDistrib t).comp (setup.h_oracle_measurable x)
  calc
    ∫ ω, setup.oracle x (proc.ξt t ω) =
        ∫ ω, setup.oracle x (proc.ξ ω) := hdist.integral_eq
    _ = proc.g x := rfl

/-- The sampled oracle variance expression is centered at the same paper mean oracle
`g(x) = f'(x)` as in Eq. (4.1.4). -/
theorem oracle_variance_eq_sample_expectation (x : setup.Point) (t : {t : ℕ // 1 ≤ t}) :
    proc.expectation (fun ω => dualNorm (setup.oracle x (proc.ξt t ω) - proc.g x) ^ 2) =
      ∫ ω, dualNorm (setup.oracle x (proc.ξt t ω) - oracleMean setup proc.ξ x) ^ 2 := by
  rfl

/-- Assumption 3b's sampled variance is the public paper expectation of its random
variable. -/
theorem oracle_sample_variance_def (x : setup.Point) (t : {t : ℕ // 1 ≤ t}) :
    oracleSampleVariance setup proc.ξ proc.ξt x t =
      proc.expectation (fun ω => dualNorm (setup.oracle x (proc.ξt t ω) - proc.g x) ^ 2) := by
  rfl

/-- Assumption 3b's fixed-`x` sampled variance expectation is well-defined. -/
theorem oracle_sample_variance_wellDefined (x : setup.Point) (t : {t : ℕ // 1 ≤ t}) :
    oracleSampleVarianceWellDefined setup proc.ξ proc.ξt x t := by
  exact (proc.h_oracle_variance x t).1

/-- `book/FOML/StochasticMirrorDescent.json#/assumptions/3/math` ::
`"E[G(x, ξ)] = f'(x) ∈ ∂f(x), ∀ x ∈ X"` in paper-facing carrier form. -/
theorem g_subgradient (x : setup.Point) :
    proc.g x ∈ carrierSubdifferential setup.X proc.f x := by
  exact meanOracle_mem_carrierSubdifferential
    (X := setup.X) (f := proc.f) (g := proc.g) proc.h_meanOracle_subgradient x

/-- Eq. (4.1.7) in paper-facing form: `‖g(x)‖_* ≤ M` on `X`. -/
theorem g_bound (x : setup.Point) :
    dualNorm (proc.g x) ≤ proc.M := by
  simpa [MirrorDescentProcess.g] using proc.h_meanOracle_norm x

/-- Eq. (4.1.4) in paper-facing form: the sampled oracle variance is bounded by `σ²`
for every sample index `t` and every `x ∈ X`. -/
theorem oracle_variance_bound (x : setup.Point) (t : {t : ℕ // 1 ≤ t}) :
    proc.expectation (fun ω => dualNorm (setup.oracle x (proc.ξt t ω) - proc.g x) ^ 2) ≤
      proc.sigmaSq := by
  simpa [MirrorDescentProcess.g, MirrorDescentProcess.expectation] using
    (sample_oracle_variance_bound
      (P := volume) (G := setup.oracle) (g := proc.g) (β := proc.ξt)
      (normDual := dualNorm) (σ2 := proc.sigmaSq) (x := x) (t := t)
      (h_fixed := fun z => by
        simpa [oracleSampleVarianceWellDefined, oracleSampleVariance, oracleSampleVarianceKernel] using
          (proc.h_oracle_variance z t)))

/-- Convexity of the paper objective `f : X → ℝ`, inherited from
`book/FOML/StochasticMirrorDescent.json#/assumptions/0/math` ::
`"F(·, ξ) is convex on X for every ξ ∈ Ξ"`. -/
theorem f_convex : ConvexOnCarrier setup.X proc.f := by
  unfold ConvexOnCarrier
  refine ⟨setup.hX_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ setup.X := setup.hX_convex hx hy ha hb hab
  let xp : setup.Point := ⟨x, hx⟩
  let yp : setup.Point := ⟨y, hy⟩
  let zp : setup.Point := ⟨a • x + b • y, hxy⟩
  have hleft : Integrable (fun ω => setup.F zp (proc.ξ ω)) := by
    simpa [objectiveWellDefined, objectiveKernel, zp] using proc.f_wellDefined zp
  have hxp : Integrable (fun ω => setup.F xp (proc.ξ ω)) := by
    simpa [objectiveWellDefined, objectiveKernel, xp] using proc.f_wellDefined xp
  have hyp : Integrable (fun ω => setup.F yp (proc.ξ ω)) := by
    simpa [objectiveWellDefined, objectiveKernel, yp] using proc.f_wellDefined yp
  let A : Ω → ℝ :=
    fun ω => totalizeOn setup.X (fun x => setup.F x (proc.ξ ω)) (a • x + b • y)
  let B : Ω → ℝ := fun ω => totalizeOn setup.X (fun x => setup.F x (proc.ξ ω)) x
  let C : Ω → ℝ := fun ω => totalizeOn setup.X (fun x => setup.F x (proc.ξ ω)) y
  have hleft : Integrable A := by
    simpa [A, zp, totalizeOn_of_mem, hxy] using hleft
  have hright : Integrable B := by
    simpa [B, xp, totalizeOn_of_mem, hx] using hxp
  have hC : Integrable C := by
    simpa [C, yp, totalizeOn_of_mem, hy] using hyp
  have hpoint :
      A ≤ fun ω => a * B ω + b * C ω := by
    intro ω
    have hc := (setup.hF_convex (proc.ξ ω)).2 hx hy ha hb hab
    simpa [A, B, C, hxy, hx, hy] using hc
  have hle :=
    integral_le_integral_affine_combination (μ := (volume : Measure Ω))
      (A := A) (B := B) (C := C) (a := a) (b := b) hleft hright hC hpoint
  have hL :
      SOptLib.carrierTotalizeOn setup.X proc.f (a • x + b • y) =
        ∫ ω, setup.F ⟨a • x + b • y, hxy⟩ (proc.ξ ω) := by
    change SOptLib.totalizeOn setup.X proc.f (a • x + b • y) =
      ∫ ω, setup.F ⟨a • x + b • y, hxy⟩ (proc.ξ ω)
    calc
      SOptLib.totalizeOn setup.X proc.f (a • x + b • y) = proc.f ⟨a • x + b • y, hxy⟩ := by
        exact SOptLib.totalizeOn_of_mem (X := setup.X) (f := proc.f) hxy
      _ = ∫ ω, setup.F ⟨a • x + b • y, hxy⟩ (proc.ξ ω) := by
        simp [MirrorDescentProcess.f, SOptLib.paperObjective_def,
          SOptLib.objectiveExpectation_def]
  have hLx :
      SOptLib.carrierTotalizeOn setup.X proc.f x =
        ∫ ω, setup.F ⟨x, hx⟩ (proc.ξ ω) := by
    change SOptLib.totalizeOn setup.X proc.f x = ∫ ω, setup.F ⟨x, hx⟩ (proc.ξ ω)
    calc
      SOptLib.totalizeOn setup.X proc.f x = proc.f ⟨x, hx⟩ := by
        exact SOptLib.totalizeOn_of_mem (X := setup.X) (f := proc.f) hx
      _ = ∫ ω, setup.F ⟨x, hx⟩ (proc.ξ ω) := by
        simp [MirrorDescentProcess.f, SOptLib.paperObjective_def,
          SOptLib.objectiveExpectation_def]
  have hLy :
      SOptLib.carrierTotalizeOn setup.X proc.f y =
        ∫ ω, setup.F ⟨y, hy⟩ (proc.ξ ω) := by
    change SOptLib.totalizeOn setup.X proc.f y = ∫ ω, setup.F ⟨y, hy⟩ (proc.ξ ω)
    calc
      SOptLib.totalizeOn setup.X proc.f y = proc.f ⟨y, hy⟩ := by
        exact SOptLib.totalizeOn_of_mem (X := setup.X) (f := proc.f) hy
      _ = ∫ ω, setup.F ⟨y, hy⟩ (proc.ξ ω) := by
        simp [MirrorDescentProcess.f, SOptLib.paperObjective_def,
          SOptLib.objectiveExpectation_def]
  have hle' : ∫ (ω : Ω), setup.F ⟨a • x + b • y, hxy⟩ (proc.ξ ω) ≤
      (a * ∫ (ω : Ω), setup.F ⟨x, hx⟩ (proc.ξ ω)) +
        b * ∫ (ω : Ω), setup.F ⟨y, hy⟩ (proc.ξ ω) := by
    simpa [A, B, C, totalizeOn_of_mem, totalizeOn, xp, yp, zp, hxy, hx, hy] using hle
  calc
    SOptLib.carrierTotalizeOn setup.X proc.f (a • x + b • y)
        = ∫ ω, setup.F ⟨a • x + b • y, hxy⟩ (proc.ξ ω) := hL
    _ ≤ (a * ∫ ω, setup.F ⟨x, hx⟩ (proc.ξ ω)) +
        b * ∫ ω, setup.F ⟨y, hy⟩ (proc.ξ ω) := hle'
    _ = (a * ∫ (ω : Ω), setup.F ⟨x, hx⟩ (proc.ξ ω)) +
        b * ∫ (ω : Ω), setup.F ⟨y, hy⟩ (proc.ξ ω) := by
      rfl
    _ = a * SOptLib.carrierTotalizeOn setup.X proc.f x +
        b * SOptLib.carrierTotalizeOn setup.X proc.f y := by
      rw [← hLx, ← hLy]

/-- The paper optimum value
`f^* = min_{x ∈ X} f(x)` from Eq. (4.1.1). -/
theorem minimizer_exists :
    ∃ x : setup.Point, ∀ z : setup.Point, proc.f x ≤ proc.f z := by
  refine ⟨proc.xStarSource, ?_⟩
  intro z
  simpa [MirrorDescentProcess.f] using proc.h_xStarSource_minimizes z

/-- Source-backed selector for the canonical paper optimizer `x^*`. -/
private noncomputable def xStarArgmin :
    {x : setup.Point // ∀ z : setup.Point, proc.f x ≤ proc.f z} :=
  SOptLib.argminSelectorOfSource (f := proc.f) (source := proc.xStarSource)
    (hsource := fun z => by
      simpa [MirrorDescentProcess.f] using proc.h_xStarSource_minimizes z)

/-- `book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math` ::
`"E[f(\\bar{x}_s^k)] - f^* ≤ ... E[V(x_s, x^*)] ..."` exposes a canonical
paper optimal point `x^*`. -/
noncomputable def xStar : setup.Point :=
  SOptLib.selectedOptimizer (argmin := proc.xStarArgmin)

/-- `book/FOML/StochasticMirrorDescent.json#/setup/problem/math` ::
`"f^* ≡ min_{x ∈ X} { f(x) := E[F(x, ξ)] }"`. -/
noncomputable def fStar : ℝ :=
  proc.f proc.xStar

/-- The canonical paper point `x^*` is optimal. -/
theorem xStar_minimizes (z : setup.Point) :
    proc.f proc.xStar ≤ proc.f z := by
  exact proc.xStarArgmin.2 z

/-- `f^*` lower-bounds every objective value on `X`. -/
theorem fStar_le (z : setup.Point) :
    proc.fStar ≤ proc.f z := by
  simpa [MirrorDescentProcess.fStar] using proc.xStar_minimizes z

/-- Paper-facing optimality predicate: `f(x) = f^*`. -/
def IsOptimal (x : setup.Point) : Prop :=
  SOptLib.IsOptimalValue (f := proc.f) (fStar := proc.fStar) x

/-- The canonical paper point `x^*` realizes the optimum value `f^*`. -/
theorem xStar_isOptimal : proc.IsOptimal proc.xStar := by
  exact (SOptLib.optimizerValueModel (f := proc.f) (xStar := proc.xStar) (fStar := proc.fStar)
    (IsOptimal := proc.IsOptimal) (hfStar := rfl) (hIsOptimal := fun _ => Iff.rfl)
    (hmin := proc.xStar_minimizes)).2

/-- Any paper minimizer realizes the paper optimum value `f^*`. -/
theorem f_eq_fStar_of_minimizer (x : setup.Point)
    (hmin : ∀ z : setup.Point, proc.f x ≤ proc.f z) :
    proc.f x = proc.fStar := by
  exact SOptLib.eq_optimizerValue_of_minimizer (f := proc.f) (xStar := proc.xStar) (x := x)
    (fStar := proc.fStar) rfl hmin proc.fStar_le

/-- Internal measurability bridge for the sample process. -/
theorem ξt_measurable (t : {t : ℕ // 1 ≤ t}) : Measurable (proc.ξt t) := by
  exact proc.hξt_measurable t

/-- The paper initial point lies in `X`, exactly as stated in the algorithm. -/
theorem x1_mem :
    setup.x1.1 ∈ setup.X := by
  exact setup.x1.2

/-- Natural filtration generated by the sample process `ξ₁, ξ₂, ...`. -/
noncomputable def filtration : Filtration ℕ (by infer_instance : MeasurableSpace Ω) :=
  SOptLib.filtration
    (fun j => proc.ξt ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
    (fun j => proc.hξt_measurable ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)

/-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/steps/0/math` ::
`"x_{t+1} = argmin_{x ∈ X} {γ_t ⟨G_t, x⟩ + V(x_t, x)}, t = 1, 2, ..."` induces the paper iterate sequence `x_t`. -/
noncomputable def x (t : MirrorDescentSetup.Time) : Ω → setup.Point :=
  SOptLib.iterateProcessView proc.xProcess t

/-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters/1/math` ::
`"G_t := G(x_t, ξ_t) (stochastic subgradient from SFO)"`. -/
noncomputable def G (t : MirrorDescentSetup.Time) : Ω → DecisionSpace m :=
  fun ω => setup.oracle (proc.x t ω) (proc.ξt t ω)

/-- The paper iterate recursion starts from `x₁`. -/
theorem x_init :
    proc.x MirrorDescentSetup.timeOne = fun _ => setup.x1 := by
  simpa [MirrorDescentProcess.x, MirrorDescentSetup.timeOne] using
    SOptLib.iterateProcess_init (x := proc.xProcess) (t0 := MirrorDescentSetup.timeOne)
      (x0 := setup.x1) proc.h_xProcess_init

/-- The sampled oracle process is the oracle kernel evaluated along the paper iterates. -/
theorem G_def (t : MirrorDescentSetup.Time) :
    proc.G t = fun ω => setup.oracle (proc.x t ω) (proc.ξt t ω) := by
  exact SOptLib.sampledOracleProcess_def setup.oracle proc.x proc.ξt t

/-- Every paper iterate is an `X`-valued point because the recursion is built on
`setup.Point`. -/
theorem x_mem (t : MirrorDescentSetup.Time) (ω : Ω) :
    (proc.x t ω).1 ∈ setup.X := by
  exact SOptLib.iterateProcess_mem (x := proc.x) t ω

/-- The paper iterate recursion follows Eq. (4.1.6). -/
theorem x_update (t : MirrorDescentSetup.Time) :
    proc.x (MirrorDescentSetup.nextTime t) = fun ω =>
      setup.mirrorStep (proc.x t ω) (proc.G t ω) (setup.stepSize t) := by
  simpa [MirrorDescentProcess.x, MirrorDescentProcess.G, MirrorDescentSetup.stepSize,
    setup.mirrorStep_eq_proxStep] using
    SOptLib.iterateProcess
      (next := MirrorDescentSetup.nextTime)
      (xProcess := proc.xProcess)
      (update := setup.proxStep)
      (oracle := setup.oracle)
      (ξ := proc.ξt)
      (γ := setup.γ)
      (x := proc.x)
      (G := proc.G)
      (stepSize := setup.stepSize)
      (h_x := fun _ => rfl)
      (h_G := fun _ => rfl)
      (h_stepSize := fun _ => rfl)
      (h_update := proc.h_xProcess_update)
      t

/-- Pointwise paper argmin semantics of the update rule
`x_{t+1} = argmin_{x ∈ X} {γ_t ⟨G_t, x⟩ + V(x_t, x)}`. -/
theorem x_update_argmin (t : MirrorDescentSetup.Time) (ω : Ω) :
    ∀ y : setup.Point,
      setup.paperMirrorObjective (proc.x t ω) (proc.G t ω) (setup.stepSize t)
          (proc.x (MirrorDescentSetup.nextTime t) ω) ≤
        setup.paperMirrorObjective (proc.x t ω) (proc.G t ω) (setup.stepSize t) y := by
  exact mirrorStep_minimizes_of_update
    (objective := setup.paperMirrorObjective)
    (mirrorStep := setup.mirrorStep)
    (x := proc.x t)
    (xNext := proc.x (MirrorDescentSetup.nextTime t))
    (oracle := proc.G t)
    (stepSize := fun _ => setup.stepSize t)
    (h_update := fun ω => congrFun (proc.x_update t) ω)
    (h_mirrorStep_minimizes := fun x g γ y =>
      (setup.isMirrorStep_iff x g γ (setup.mirrorStep x g γ)).1
        (setup.mirrorStep_isMirrorStep x g γ) y)
    ω

/-- Once the current iterate is known to be interior, the recursive update also realizes
the literal paper argmin semantics. -/
theorem x_update_argmin_of_interior
    (t : MirrorDescentSetup.Time) (ω : Ω)
    (hx : (proc.x t ω).1 ∈ interior setup.X) :
    setup.IsLiteralMirrorStep ⟨(proc.x t ω).1, hx⟩ (proc.G t ω) (setup.stepSize t)
      (proc.x (MirrorDescentSetup.nextTime t) ω) := by
  exact literalMirrorStep_of_update_of_interior
    (toP := fun y : setup.InteriorPoint => y.toPoint)
    (mirrorStep := setup.mirrorStep)
    (IsLiteralMirrorStep := setup.IsLiteralMirrorStep)
    (x := proc.x t)
    (xNext := proc.x (MirrorDescentSetup.nextTime t))
    (d := proc.G t)
    (stepSize := fun _ => setup.stepSize t)
    (h_update := fun ω => congrFun (proc.x_update t) ω)
    (h_mirrorStep_literal := setup.mirrorStep_isLiteralMirrorStep)
    (ω := ω) ⟨(proc.x t ω).1, hx⟩ (by ext; rfl)

/-- Lemma 3.4 along the paper update rule. -/
theorem lemma_3_4 (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point) :
    setup.stepSize t * ⟪proc.G t ω, (proc.x (MirrorDescentSetup.nextTime t) ω).1 - x.1⟫_ℝ +
      setup.V (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω) ≤
        setup.V (proc.x t ω) x -
          setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x := by
  exact
    mirrorDescent_three_point_of_update
      (V := setup.V) (eval := fun y : setup.Point => y.1) (step := setup.mirrorStep)
      (x := proc.x t) (xNext := proc.x (MirrorDescentSetup.nextTime t))
      (g := proc.G t) (γ := setup.stepSize t) (y := x)
      (h_update := fun ω => congrFun (proc.x_update t) ω)
      (h_step_three_point := setup.mirrorStep_three_point) ω

/-- If a later proof establishes that a recursive next iterate is an interior base
point, then the public divergence expands to Lan's literal gradient formula there. -/
theorem V_x_next_eq_formula_of_interior
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point)
    (hx_next : (proc.x (MirrorDescentSetup.nextTime t) ω).1 ∈ interior setup.X) :
    setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x =
      setup.v x - setup.v (proc.x (MirrorDescentSetup.nextTime t) ω) -
        ⟪∇ setup.vInteriorAmbient (proc.x (MirrorDescentSetup.nextTime t) ω).1,
          x.1 - (proc.x (MirrorDescentSetup.nextTime t) ω).1⟫_ℝ := by
  exact
    bregmanDivergence_eq_formula_of_interior_iterate
      (V := setup.V) (toP := fun y : setup.InteriorPoint => y.toPoint)
      (v := setup.v) (grad := fun y : setup.InteriorPoint => ∇ setup.vInteriorAmbient y.1)
      (eval := fun y : setup.Point => y.1)
      (xnextI := ⟨(proc.x (MirrorDescentSetup.nextTime t) ω).1, hx_next⟩)
      (hnext := by ext; rfl)
      (h_formula := fun y z => by
        simpa [MirrorDescentSetup.literalV_def] using setup.V_eq_formula_of_interior y z)

/-- Positivity of the weighted-output denominator. -/
theorem outputWeightSum_pos (w : MirrorDescentSetup.OutputWindow) :
    0 < setup.outputWeightSum w := by
  simpa [MirrorDescentSetup.outputWeightSum, MirrorDescentSetup.outputTimes] using
    (SOptLib.PositiveOutputWindow.weight_sum_pos (γ := setup.stepSize) setup.stepSize_pos w)

/-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math` ::
`"\\bar{x}_s^k = (\\sum_{t=s}^{k} \\gamma_t)^{-1} \\sum_{t=s}^{k} \\gamma_t x_t"`. -/
theorem xBar_weightedSum_mem (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    (setup.outputWeightSum w)⁻¹ •
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t => setup.stepSize t • (proc.x t ω).1) ∈
      setup.X := by
  simpa [MirrorDescentSetup.outputWeightSum] using
    (Convex.normalized_weighted_sum_mem setup.hX_convex
      (MirrorDescentSetup.outputTimes w) setup.stepSize (fun t => (proc.x t ω).1)
      (by simpa [MirrorDescentSetup.outputWeightSum] using outputWeightSum_pos w)
      (fun t _ => le_of_lt (setup.stepSize_pos t))
      (fun t _ => proc.x_mem t ω))

/-- `book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math` ::
`"\\bar{x}_s^k = (\\sum_{t=s}^{k} \\gamma_t)^{-1} \\sum_{t=s}^{k} \\gamma_t x_t"`. -/
noncomputable def xBar (w : MirrorDescentSetup.OutputWindow) : Ω → setup.Point :=
  SOptLib.weightedOutputAverage setup.X MirrorDescentSetup.outputTimes setup.stepSize
    (fun t ω => (proc.x t ω).1) setup.outputWeightSum setup.hX_convex
    (fun _ t _ => le_of_lt (setup.stepSize_pos t))
    (fun _ t _ ω => proc.x_mem t ω)
    (fun w => outputWeightSum_pos w)
    (fun _ => rfl) w

/-- Defining weighted-average formula for `\bar x_s^k`. -/
theorem xBar_def (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    (proc.xBar w ω).1 =
      (setup.outputWeightSum w)⁻¹ •
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t => setup.stepSize t • (proc.x t ω).1) := by
  exact SOptLib.weightedAverageOutput_def setup.X MirrorDescentSetup.outputTimes setup.stepSize
    (fun t ω => (proc.x t ω).1) setup.outputWeightSum setup.hX_convex
    (fun _ t _ => le_of_lt (setup.stepSize_pos t))
    (fun _ t _ ω => proc.x_mem t ω) (fun w => outputWeightSum_pos w) (fun _ => rfl) w ω

/-- The paper weighted output lies in `X`. -/
theorem xBar_mem (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    (proc.xBar w ω).1 ∈ setup.X := by
  exact SOptLib.weightedAverageOutput_mem (proc.xBar w) ω

/-- Bounded measurable real random variables are integrable under the probability
measure used for the paper expectation. -/
theorem integrable_of_measurable_bounded_real {Z : Ω → ℝ}
    (hZ : Measurable Z) {C : ℝ} (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    Integrable Z := by
  exact Integrable.of_bound hZ.aestronglyMeasurable C (ae_of_all volume hC)

/-- Derived adaptiveness bridge for the paper iterates, exposed against the generated
sample filtration.

This is a theorem, not process data: Lan uses `x_t is ξ_[t-1]-measurable` inside the
martingale proof step, and it must be derived from the deterministic initialization,
the recursive update, and measurability of the sampled oracle/prox composition. -/
theorem x_past_measurable (t : MirrorDescentSetup.Time) :
    Measurable[proc.filtration.seq (t.1 - 1)] (proc.x t) := by
  simpa [MirrorDescentProcess.x, MirrorDescentProcess.filtration, SOptLib.filtration] using
    (adapted_iterate_of_recursive_sample_update
      (x := proc.xProcess) (ξ := proc.ξt) (oracle := setup.oracle)
      (update := setup.proxStep) (γ := setup.γ) (x₁ := setup.x1)
      setup.h_oracle_joint_measurable setup.proxStep_measurable proc.hξt_measurable
      proc.h_xProcess_init proc.h_xProcess_update t)

/-- The paper iterates are measurable random feasible points. This is the ambient
measurability consequence of `x_t` being measurable with respect to the past
filtration in Lan's martingale step. -/
theorem x_measurable (t : MirrorDescentSetup.Time) :
    Measurable (proc.x t) := by
  exact Measurable.of_measurableSpace_le (m := proc.filtration.seq (t.1 - 1))
    (proc.x_past_measurable t) (proc.filtration.le (t.1 - 1))

/-- The weighted output `\bar x_s^k` is a measurable random feasible point because it is
a finite weighted sum of measurable iterates. -/
theorem xBar_measurable (w : MirrorDescentSetup.OutputWindow) :
    Measurable (proc.xBar w) := by
  simpa [MirrorDescentProcess.xBar] using
    (SOptLib.weightedAverageOutput_measurable setup.X MirrorDescentSetup.outputTimes setup.stepSize
      (fun t ω => (proc.x t ω).1) setup.outputWeightSum setup.hX_convex
      (fun _ t _ => le_of_lt (setup.stepSize_pos t))
      (fun _ t _ ω => proc.x_mem t ω) (fun w => outputWeightSum_pos w) (fun _ => rfl)
      (fun t => (proc.x_measurable t).subtype_val) w)

/-- The sampled oracle process is measurable along each paper time. -/
theorem G_measurable (t : MirrorDescentSetup.Time) :
    Measurable (proc.G t) := by
  simpa [MirrorDescentProcess.G] using
    SOptLib.sampledOracle_measurable setup.h_oracle_joint_measurable
      (proc.x_measurable t) (proc.ξt_measurable t)

  /-- The paper mean oracle `g(x) = E[G(x, ξ)]` is measurable as a parameterized
  Bochner integral of the jointly measurable oracle kernel. -/
  theorem g_measurable :
      Measurable proc.g := by
  simpa [MirrorDescentProcess.g, SOptLib.paperMeanOracle, SOptLib.oracleMean,
    SOptLib.oracleKernel] using
    (oracleMean_measurable_of_joint_measurable
      (μ := volume) (oracle := setup.oracle) (ξ := proc.ξ)
      setup.h_oracle_joint_measurable proc.hξ_measurable)

/-- The sampled oracle deviation is a measurable Euclidean random vector. -/
theorem sampled_oracle_deviation_measurable
    (t : MirrorDescentSetup.Time) :
    Measurable (fun ω => proc.G t ω - proc.g (proc.x t ω)) := by
  exact oracleDeviation_measurable (proc.G t) proc.g (proc.x t)
    (proc.G_measurable t) proc.g_measurable (proc.x_measurable t)

/-- The sampled oracle deviation is almost everywhere strongly measurable. -/
theorem sampled_oracle_deviation_aestronglyMeasurable
    (t : MirrorDescentSetup.Time) :
    AEStronglyMeasurable (fun ω => proc.G t ω - proc.g (proc.x t ω)) volume := by
  exact Measurable.aestronglyMeasurable_measure
    (proc.sampled_oracle_deviation_measurable t)

/-- Measure-theoretic transfer of fixed-parameter integrability to a random parameter.

This is the reusable Fubini/independence part of the random-iterate variance bridge:
if `Y` has law `ν`, `X` is independent of `Y`, and each fiber `φ w ·` is integrable
with uniformly bounded nonnegative expectation, then the composed random kernel is
integrable. -/
theorem random_parameter_integrable_of_indep_fixed_bound
    {W S : Type*} [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → S → ℝ} {X : Ω → W} {Y : Ω → S} {C : ℝ}
    (hφ : Measurable (Function.uncurry φ))
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hφ_nonneg : ∀ w s, 0 ≤ φ w s)
    (hC_nonneg : 0 ≤ C)
    (hfixed_int : ∀ w, Integrable (fun s => φ w s) ν)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ C) :
    Integrable (fun ω => φ (X ω) (Y ω)) P := by
  exact integrable_comp_of_indep_fixed_integral_bound hφ hX hY h_indep h_dist
    hφ_nonneg hC_nonneg hfixed_int hfixed_bound

/-- Measure-theoretic transfer of a fixed-parameter integral bound to a random parameter.

This is the reusable product-law/Fubini calculation used after integrability has been
established. -/
theorem random_parameter_integral_bound_of_indep_fixed_bound
    {W S : Type*} [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → S → ℝ} {X : Ω → W} {Y : Ω → S} {C : ℝ}
    (hφ : Measurable (Function.uncurry φ))
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ C)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ C := by
  exact integral_comp_le_of_indep_fixed_integral_bound hφ hX hY h_indep h_dist h_int
    hfixed_bound

/-- Vector-valued product-law/Fubini cancellation for a random parameter independent of
the current sample. -/
private theorem random_parameter_integral_zero_of_indep_fixed_zero
    {W S V : Type*} [MeasurableSpace W] [MeasurableSpace S]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → S → V} {X : Ω → W} {Y : Ω → S}
    (hφ : Measurable (Function.uncurry φ))
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hfixed_zero : ∀ w, ∫ s, φ w s ∂ν = 0) :
    ∫ ω, φ (X ω) (Y ω) ∂P = 0 := by
  exact integral_comp_eq_zero_of_indep_fixed_integral_zero
    hφ hX hY h_indep h_dist h_int hfixed_zero

/-- The current sample is independent of the sigma-algebra generated by the earlier
sample stream. -/
private theorem current_sample_independent_of_past_filtration
    (t : MirrorDescentSetup.Time) :
    ProbabilityTheory.Indep (proc.filtration.seq (t.1 - 1))
      (MeasurableSpace.comap (proc.ξt t)
        (by infer_instance : MeasurableSpace setup.Sample)) volume := by
  simpa [MirrorDescentProcess.filtration, Nat.sub_add_cancel t.2] using
    (samplePrefixFiltration_indep_current
      (ξ := fun j => proc.ξt ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
      (μ := volume)
      (hξ_measurable := fun j =>
        proc.ξt_measurable ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
      (hξ_iIndep := proc.hξt_iIndep.precomp (by
        intro i j hij
        have hval := congrArg Subtype.val hij
        simp at hval
        omega))
      (t := t.1 - 1))

/-- The current paper iterate is independent of the current sample once it is known to
be measurable with respect to the past sample filtration. -/
theorem indepFun_x_currentSample_of_past_measurable
    (t : MirrorDescentSetup.Time)
    (hx_adapted : Measurable[proc.filtration.seq (t.1 - 1)] (proc.x t)) :
    IndepFun (proc.x t) (proc.ξt t) volume := by
  exact indepFun_of_past_measurable_current_iid_sample hx_adapted
    (current_sample_independent_of_past_filtration (proc := proc) t)

/-- Any past-measurable random parameter is independent of the current sample. -/
private theorem indepFun_past_measurable_currentSample
    {W : Type*} [MeasurableSpace W]
    (t : MirrorDescentSetup.Time) {Z : Ω → W}
    (hZ : Measurable[proc.filtration.seq (t.1 - 1)] Z) :
    IndepFun Z (proc.ξt t) volume := by
  exact indepFun_of_measurable_left_of_indep_comap hZ
    (current_sample_independent_of_past_filtration (proc := proc) t)

/-- Concrete specialization of the product-law variance transfer to the SMD oracle
deviation kernel. -/
theorem oracleRandomIterateVarianceBound_of_fixed_variance
    (t : MirrorDescentSetup.Time)
    (hx_meas : Measurable (proc.x t))
    (h_indep : IndepFun (proc.x t) (proc.ξt t) volume)
    (hfixed :
      ∀ x : setup.Point,
        oracleSampleVarianceWellDefined setup proc.ξ proc.ξt x t ∧
          oracleSampleVariance setup proc.ξ proc.ξt x t ≤ proc.sigmaSq) :
    oracleRandomIterateVarianceBound setup proc.ξ proc.ξt proc.xProcess proc.sigmaSq t := by
  classical
  have hdev_meas : Measurable
      (fun p : setup.Point × setup.Sample => setup.oracle p.1 p.2 - proc.g p.1) :=
    setup.h_oracle_joint_measurable.sub (proc.g_measurable.comp measurable_fst)
  haveI : IsProbabilityMeasure (Measure.map (proc.ξt t) volume) :=
    Measure.isProbabilityMeasure_map (proc.ξt_measurable t).aemeasurable
  simpa [oracleRandomIterateVarianceBound, oracleRandomIterateVarianceWellDefined,
    oracleRandomIterateVarianceKernel, oracleSampleVarianceWellDefined,
    oracleSampleVarianceKernel, oracleSampleVariance, MirrorDescentProcess.x,
    MirrorDescentProcess.g, dualNorm] using
    (randomIterate_variance_bound_of_fixed_variance
      (P := volume) (ν := Measure.map (proc.ξt t) volume)
      (G := setup.oracle) (g := proc.g) (x := proc.x t) (Y := proc.ξt t)
      (σ2 := proc.sigmaSq)
      hdev_meas hx_meas (proc.ξt_measurable t) h_indep rfl proc.h_sigmaSq_nonneg
      (fun x => by
        simpa [oracleSampleVarianceWellDefined, oracleSampleVarianceKernel,
          MirrorDescentProcess.g, dualNorm] using (hfixed x).1)
      (fun x => by
        simpa [oracleSampleVariance, oracleSampleVarianceKernel,
          MirrorDescentProcess.g, dualNorm] using (hfixed x).2))

/-- The random-iterate oracle noise is integrable once the fixed-iterate variance
bound is transferred through the past/current-sample independence bridge. -/
private theorem random_iterate_oracle_noise_integrable
    (t : MirrorDescentSetup.Time)
    (hx_adapted : Measurable[proc.filtration.seq (t.1 - 1)] (proc.x t))
    (hx_meas : Measurable (proc.x t)) :
    Integrable (fun ω => proc.G t ω - proc.g (proc.x t ω)) := by
  exact oracleNoise_integrable_of_sq_integrable
    (μ := volume) (G := setup.oracle) (g := proc.g)
    (x := proc.x t) (Y := proc.ξt t) (normNoise := dualNorm)
    (by intro z; rfl)
    (proc.sampled_oracle_deviation_aestronglyMeasurable t)
    (by
      simpa [oracleRandomIterateVarianceWellDefined, oracleRandomIterateVarianceKernel,
        MirrorDescentProcess.G, MirrorDescentProcess.g, MirrorDescentProcess.x] using
        (proc.oracleRandomIterateVarianceBound_of_fixed_variance t hx_meas
          (proc.indepFun_x_currentSample_of_past_measurable t hx_adapted)
          (fun x => proc.h_oracle_variance x t)).1)

/-- For a fixed feasible decision, the current-sample oracle deviation has zero
integral under the current sample law. -/
private theorem fixed_oracle_deviation_current_sample_law_integral_zero
    (x : setup.Point) (t : MirrorDescentSetup.Time) :
    ∫ y, setup.oracle x y - proc.g x ∂Measure.map (proc.ξt t) volume = 0 := by
  exact fixedOracleDeviation_integral_law_eq_zero
    (μ := volume) (G := setup.oracle) (g := proc.g) (x := x)
    (ξ := proc.ξ) (Y := proc.ξt t)
    (proc.ξt_measurable t) (setup.h_oracle_measurable x)
    (proc.hξt_identDistrib t)
    (by simpa [oracleKernel] using proc.g_wellDefined x)
    (by rfl)

/-- Set-integral form of the martingale-difference property for a past-measurable
event. This is the remaining product-law/Fubini packaging: the event and iterate are
past-measurable, the current sample is independent of the past, and each fixed
oracle fiber is centered at `oracleMean`. -/
private theorem oracle_noise_setIntegral_zero_of_past_measurable_set
    (t : MirrorDescentSetup.Time)
    (s : Set Ω)
    (hs : MeasurableSet[proc.filtration.seq (t.1 - 1)] s) :
    ∫ ω in s, proc.G t ω - proc.g (proc.x t ω) = 0 := by
  classical
  simpa [MirrorDescentProcess.G] using
    (oracle_noise_setIntegral_eq_zero_of_past_measurable
      (μ := volume) (m := proc.filtration.seq (t.1 - 1))
      (G := setup.oracle) (g := proc.g) (x := proc.x t) (Y := proc.ξt t)
      (s := s) (proc.filtration.le (t.1 - 1)) hs
      (setup.h_oracle_joint_measurable.sub (proc.g_measurable.comp measurable_fst))
      (proc.x_past_measurable t) (proc.x_measurable t) (proc.ξt_measurable t)
      (by
        simpa using
          proc.indepFun_past_measurable_currentSample t
            ((measurable_const.indicator hs).prodMk (proc.x_past_measurable t)))
      (by
        simpa [MirrorDescentProcess.G] using
          proc.random_iterate_oracle_noise_integrable t
            (proc.x_past_measurable t) (proc.x_measurable t))
      (fun x => by
        simpa using proc.fixed_oracle_deviation_current_sample_law_integral_zero x t))

/-- Derived conditional-unbiasedness bridge for the random-iterate oracle noise.

This is the martingale consequence used in Lan Theorem 4.1, proof step 6. It is derived
from the fixed-point oracle expectation, i.i.d. sample stream, and past measurability of
the iterate; it is intentionally not a primitive `MirrorDescentProcess` field. Placing it
after `x_past_measurable` exposes the canonical adaptiveness route to fill-only proofs. -/
theorem h_oracle_noise_condExp_zero
    (t : {t : ℕ // 1 ≤ t}) :
      volume[
        (fun ω => setup.oracle (proc.xProcess t ω) (proc.ξt t ω) -
          oracleMean setup proc.ξ (proc.xProcess t ω)) |
          ⨆ j < t.1 - 1,
            MeasurableSpace.comap
              (proc.ξt ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩)
              (by infer_instance : MeasurableSpace {ξ : SampleSpace d // ξ ∈ setup.Ξ})] =ᵐ[volume] 0 := by
  classical
  simpa [MirrorDescentProcess.G, MirrorDescentProcess.g,
    MirrorDescentProcess.x, MirrorDescentProcess.filtration] using
    (condExp_oracle_noise_eq_zero_of_setIntegral_zero
      (μ := volume) (m := proc.filtration.seq (t.1 - 1))
      (G := setup.oracle) (g := proc.g) (x := proc.x t) (Y := proc.ξt t)
      (proc.filtration.le (t.1 - 1))
      (proc.random_iterate_oracle_noise_integrable t
        (proc.x_past_measurable t) (proc.x_measurable t))
      (fun s hs => proc.oracle_noise_setIntegral_zero_of_past_measurable_set t s hs))

/-- Derived random-iterate variance bridge.

Assumption 3b bounds the sampled oracle variance for each fixed feasible `x`. The
random-iterate form used in the convergence proof is derived from that fixed-point
bound together with the i.i.d. sample stream and past measurability of `x_t`, rather
than assumed as process data. Placing it after `x_past_measurable` exposes the random
iterate as a measurable kernel parameter. -/
theorem h_oracle_random_iterate_variance
    (t : {t : ℕ // 1 ≤ t}) :
      oracleRandomIterateVarianceBound setup proc.ξ proc.ξt proc.xProcess proc.sigmaSq t := by
  simpa [oracleRandomIterateVarianceBound, MirrorDescentProcess.g, dualNorm] using
    (oracleRandomIterateVarianceBound_of_fixedVariance
      (P := volume) (G := setup.oracle) (g := proc.g)
      (x := proc.xProcess) (Y := proc.ξt) (normDual := dualNorm)
      (σ2 := proc.sigmaSq) (t := t)
      (by intro e; simp [dualNorm])
      (setup.h_oracle_joint_measurable.sub (proc.g_measurable.comp measurable_fst))
      (proc.x_measurable t) (proc.ξt_measurable t)
      (proc.indepFun_x_currentSample_of_past_measurable t (proc.x_past_measurable t))
      proc.h_sigmaSq_nonneg
      (fun x => by
        simpa [oracleSampleVarianceWellDefined, oracleSampleVarianceKernel,
          oracleSampleVariance, MirrorDescentProcess.g, dualNorm] using
          proc.h_oracle_variance x t))

/-- Bounded-subgradient convexity gives the objective a Lipschitz bound on the feasible
carrier. This is the paper's Eq. (4.1.7) routed through the carrier subdifferential
API. -/
theorem f_lipschitzOn_carrier :
    ∀ x y : setup.Point, ‖proc.f x - proc.f y‖ ≤ proc.M * ‖x.1 - y.1‖ := by
  intro x y
  exact SOptLib.abs_sub_le_of_subgradient_norm_bound
    (f := proc.f) (eval := fun x : setup.Point => x.1) (g := proc.g) (M := proc.M)
    (x := x) (y := y)
    (by
      have hg := proc.g_subgradient x
      rw [mem_carrierSubdifferential_iff] at hg
      exact hg y)
    (by
      have hg := proc.g_subgradient y
      rw [mem_carrierSubdifferential_iff] at hg
      exact hg x)
    (by simpa [dualNorm] using proc.g_bound x)
    (by simpa [dualNorm] using proc.g_bound y)

/-- The carrier objective is a genuine Lipschitz map on the feasible subtype. -/
theorem f_lipschitzWith_carrier :
    LipschitzWith (Real.toNNReal proc.M) proc.f := by
  exact lipschitzWith_of_norm_sub_le_mul proc.f proc.M proc.f_lipschitzOn_carrier

/-- Since `X` is bounded and `f` is Lipschitz on `X`, the paper objective is bounded
on the feasible carrier. -/
theorem f_boundedOn_carrier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : setup.Point, ‖proc.f x‖ ≤ C := by
  exact exists_bound_of_bounded_lipschitzOn_real
    (f := proc.f) (eval := fun x : setup.Point => x.1) (x0 := setup.x1)
    (M := proc.M) (le_of_lt proc.hM_pos)
    (Bornology.IsBounded.subset setup.hX_bounded (by rintro _ ⟨x, rfl⟩; exact x.2))
    proc.f_lipschitzOn_carrier

/-- Interior-safe nonnegativity for the paper Bregman divergence.

Lan's distance-generator assumption justifies the lower-bound argument on `Xᵒ`. This
keeps the old helper name available for proof search, but exposes the required
interior obligations instead of asserting an all-carrier fact that does not follow
from the current object model. -/
theorem V_nonneg_carrier (x z : setup.Point)
    (hx : x.1 ∈ interior setup.X) (hz : z.1 ∈ interior setup.X) :
    0 ≤ setup.V x z := by
  exact carrierBregman_nonneg_of_interior
    (V := setup.V) (eval := fun x : setup.Point => x.1)
    (interiorPred := fun x : setup.Point => x.1 ∈ interior setup.X)
    setup.V_lower_bound_of_interior hx hz

/-- The theorem-head random variable `ω ↦ f(\bar x_s^k(ω))` is measurable. -/
theorem f_measurable :
    Measurable proc.f := by
  exact LipschitzWith.measurable proc.f_lipschitzWith_carrier

/-- The left section of the paper Bregman divergence is measurable on the carrier once
the boundary-safe divergence has a genuine continuity bridge. -/
theorem V_measurable_left_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (z : setup.Point) :
    Measurable (fun x : setup.Point => setup.V x z) := by
  exact measurable_left_section_of_continuousOn_univ (V := setup.V) hcont z

/-- The left section of `V` is measurable under the source-backed full-dimensional
convex-set bridge. -/
theorem V_measurable_left_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty) (z : setup.Point) :
    Measurable (fun x : setup.Point => setup.V x z) := by
  exact carrierBregman_measurable_left_of_nonemptyInterior
    setup.hX_convex setup.V_continuousOn_carrier_of_uniqueDiffOn hXint z

/-- The left section of `V` is measurable once the boundary-safe within-gradient extension
is known to be measurable.

This is a bookkeeping decomposition of the all-carrier measurability problem. The remaining
non-source-backed obligation is exactly the regularity of Mathlib's `gradientWithin` selector on
possibly lower-dimensional feasible carriers. -/
theorem V_measurable_left_of_vGradExtension_measurable
    (hgrad : Measurable (fun x : setup.Point => setup.vGradExtension x))
    (z : setup.Point) :
    Measurable (fun x : setup.Point => setup.V x z) := by
  simpa [MirrorDescentSetup.V, carrierBregmanDivergence] using
    Measurable.bregmanFormula_left
      (P := setup.Point) (E := DecisionSpace m) (v := setup.v)
      (eval := fun x : setup.Point => x.1)
      (grad := fun x : setup.Point => setup.vGradExtension x)
      setup.hv_measurable continuous_subtype_val.measurable hgrad z

/-- The left section of the paper Bregman divergence is measurable on the carrier. -/
theorem V_measurable_left (z : setup.Point) :
    Measurable (fun x : setup.Point => setup.V x z) := by
  exact carrierBregman_measurable_left setup.V setup.V_continuousOn_carrier z

/-- The theorem-head random variable `ω ↦ f(\bar x_s^k(ω))` is measurable. -/
theorem xBar_objective_measurable (w : MirrorDescentSetup.OutputWindow) :
    Measurable (fun ω => proc.f (proc.xBar w ω)) := by
  exact measurable_comp_real proc.f (proc.xBar w) proc.f_measurable (proc.xBar_measurable w)

/-- The theorem-head random variable `ω ↦ V(x_s(ω), x^*)` is measurable from an explicit
Bregman continuity bridge. -/
theorem start_bregman_measurable_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (w : MirrorDescentSetup.OutputWindow) :
  Measurable (fun ω =>
      setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar) := by
  exact measurable_bregman_start_of_measurable_iterate
    (V := setup.V) (X := proc.x (MirrorDescentSetup.OutputWindow.startTime w))
    proc.xStar hcont (proc.x_measurable (MirrorDescentSetup.OutputWindow.startTime w))

/-- Start-Bregman measurability under the source-backed full-dimensional convex-set bridge. -/
theorem start_bregman_measurable_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty)
    (w : MirrorDescentSetup.OutputWindow) :
  Measurable (fun ω =>
      setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar) := by
  exact SOptLib.startBregman_measurable_of_nonemptyInterior
    (V := setup.V)
    (X := proc.x (MirrorDescentSetup.OutputWindow.startTime w))
    (z := proc.xStar)
    (proc.x_measurable (MirrorDescentSetup.OutputWindow.startTime w))
    setup.hX_convex setup.V_continuousOn_carrier_of_uniqueDiffOn hXint

/-- The theorem-head random variable `ω ↦ V(x_s(ω), x^*)` is measurable. -/
theorem start_bregman_measurable (w : MirrorDescentSetup.OutputWindow) :
  Measurable (fun ω =>
      setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar) := by
  exact startBregman_measurable setup.V
    (proc.x (MirrorDescentSetup.OutputWindow.startTime w)) proc.xStar
    (V_measurable_left (setup := setup) proc.xStar)
    (proc.x_measurable (MirrorDescentSetup.OutputWindow.startTime w))

/-- Integrability bridge for the output objective appearing in the main theorem. -/
theorem xBar_objective_integrable (w : MirrorDescentSetup.OutputWindow) :
    Integrable (fun ω => proc.f (proc.xBar w ω)) := by
  rcases proc.f_boundedOn_carrier with ⟨C, _hC_nonneg, hC⟩
  exact _root_.integrable_of_measurable_bounded_real (proc.xBar_objective_measurable w)
    (fun ω => hC (proc.xBar w ω))

/-- Integrability bridge for the initial Bregman term from an explicit Bregman
continuity bridge. -/
theorem start_bregman_integrable_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (w : MirrorDescentSetup.OutputWindow) :
    Integrable
      (fun ω => setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar) := by
  rcases setup.V_abs_bound_exists hcont with ⟨C, _hC_nonneg, hC⟩
  exact integrable_bregman_of_measurable_bounded
    (V := setup.V)
    (X := proc.x (MirrorDescentSetup.OutputWindow.startTime w))
    (z := proc.xStar)
    (V_measurable_left_of_continuousOn (setup := setup) hcont proc.xStar)
    (proc.x_measurable (MirrorDescentSetup.OutputWindow.startTime w))
    (fun ω => hC (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar)

/-- Start-Bregman integrability under the source-backed full-dimensional convex-set bridge. -/
theorem start_bregman_integrable_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty)
    (w : MirrorDescentSetup.OutputWindow) :
    Integrable
      (fun ω => setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar) := by
  exact SOptLib.startBregman_integrable_of_nonemptyInterior
    (V := setup.V)
    (X := proc.x (MirrorDescentSetup.OutputWindow.startTime w))
    (z := proc.xStar)
    (μ := volume)
    (proc.x_measurable (MirrorDescentSetup.OutputWindow.startTime w))
    setup.hX_convex setup.V_continuousOn_carrier_of_uniqueDiffOn hXint
    setup.pointProd_univ_isCompact

/-- Integrability bridge for the initial Bregman term appearing in the main theorem. -/
theorem start_bregman_integrable (w : MirrorDescentSetup.OutputWindow) :
    Integrable
      (fun ω => setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar) := by
  exact SOptLib.startBregman_integrable setup.V
    (proc.x (MirrorDescentSetup.OutputWindow.startTime w)) proc.xStar
    (proc.x_measurable (MirrorDescentSetup.OutputWindow.startTime w))
    setup.V_continuousOn_carrier setup.pointProd_univ_isCompact

/-- Backward-compatible alias for the paper oracle mean. -/
noncomputable abbrev meanOracle (x : setup.Point) : DecisionSpace m := proc.g x

/-- Backward-compatible alias for the paper iterate sequence. -/
noncomputable abbrev iterate (t : MirrorDescentSetup.Time) : Ω → setup.Point := proc.x t

/-- Backward-compatible alias for the sampled oracle sequence. -/
noncomputable abbrev sampledOracle (t : MirrorDescentSetup.Time) : Ω → DecisionSpace m := proc.G t

/-- Backward-compatible alias for the weighted output. -/
noncomputable abbrev cesaroAverage (w : MirrorDescentSetup.OutputWindow) : Ω → setup.Point :=
  proc.xBar w

/-- The theorem-head random variable `f(\bar x_s^k)` is a well-defined paper expectation. -/
theorem xBar_objective_expectationWellDefined (w : MirrorDescentSetup.OutputWindow) :
    proc.ExpectationWellDefined (fun ω => proc.f (proc.xBar w ω)) := by
  simpa [MirrorDescentProcess.ExpectationWellDefined] using
    proc.xBar_objective_integrable w

/-- The theorem-head random variable `V(x_s, x^*)` is a well-defined paper expectation. -/
theorem start_bregman_expectationWellDefined_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (w : MirrorDescentSetup.OutputWindow) :
    proc.ExpectationWellDefined
      (fun ω => setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar) := by
  simpa [MirrorDescentProcess.ExpectationWellDefined] using
    proc.start_bregman_integrable_of_continuousOn hcont w

/-- Start-Bregman expectation well-definedness under the source-backed full-dimensional
convex-set bridge. -/
theorem start_bregman_expectationWellDefined_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty)
    (w : MirrorDescentSetup.OutputWindow) :
    proc.ExpectationWellDefined
      (fun ω => setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar) := by
  simpa [MirrorDescentProcess.ExpectationWellDefined] using
    proc.start_bregman_integrable_of_nonempty_interior hXint w

/-- The theorem-head random variable `V(x_s, x^*)` is a well-defined paper expectation. -/
theorem start_bregman_expectationWellDefined (w : MirrorDescentSetup.OutputWindow) :
    proc.ExpectationWellDefined
      (fun ω => setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar) := by
  simpa [MirrorDescentProcess.ExpectationWellDefined] using
    proc.start_bregman_integrable w

-- ============================================================================
-- Convergence Theorem (Lan, Theorem 4.1)
-- ============================================================================

/-- Algebraic one-step pathwise inequality from the residual Bregman lower bound.

This isolates the only geometric input in Lan's residual estimate:
`V(x_t,x_{t+1}) ≥ (1/2)‖x_t-x_{t+1}‖²`.  Interior and all-carrier callers must
produce that lower bound from the appropriate Bregman realization, rather than
burying the boundary obligation inside the stochastic algebra. -/
theorem stochasticMirrorDescent_oneStep_pathwise_of_residual_lower_bound
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point)
    (hVlower :
      (1 / 2 : ℝ) *
          ‖(proc.x t ω).1 - (proc.x (MirrorDescentSetup.nextTime t) ω).1‖ ^ 2 ≤
        setup.V (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω)) :
    setup.stepSize t * (proc.f (proc.x t ω) - proc.f x) ≤
      setup.V (proc.x t ω) x - setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x +
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) -
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ := by
  simpa [dualNorm] using
    mirrorDescent_oneStep_pathwise_of_residual_lower_bound
      (f := proc.f) (V := setup.V) (point := fun y : setup.Point => y.1)
      (x := proc.x t ω) (xNext := proc.x (MirrorDescentSetup.nextTime t) ω)
      (xRef := x) (G := proc.G t ω) (g := proc.g (proc.x t ω))
      (δ := proc.G t ω - proc.g (proc.x t ω)) (γ := setup.stepSize t)
      (M := proc.M) (by simpa using setup.stepSize_pos t)
      (by
        have hg := proc.g_subgradient (proc.x t ω)
        rw [mem_carrierSubdifferential_iff] at hg
        simpa using hg x)
      (by simpa using proc.lemma_3_4 t ω x) hVlower
      (by abel) (by simpa [dualNorm] using proc.g_bound (proc.x t ω))

/-- One-step pathwise inequality before taking expectations. It exposes the exact
descent term, variance term, and martingale-difference term used in Lan's proof of
Theorem 4.1, with the residual lower bound discharged on `Xᵒ`. -/
theorem stochasticMirrorDescent_oneStep_pathwise_of_interior
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point)
    (hxt : (proc.x t ω).1 ∈ interior setup.X)
    (hxnext : (proc.x (MirrorDescentSetup.nextTime t) ω).1 ∈ interior setup.X) :
    setup.stepSize t * (proc.f (proc.x t ω) - proc.f x) ≤
      setup.V (proc.x t ω) x - setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x +
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) -
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ := by
  exact proc.stochasticMirrorDescent_oneStep_pathwise_of_residual_lower_bound t ω x
    (setup.V_lower_bound_of_interior
      (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω) hxt hxnext)

/-- One-step pathwise inequality with the residual lower bound discharged by the
source-backed full-dimensional convex-set bridge. -/
theorem stochasticMirrorDescent_oneStep_pathwise_of_nonempty_interior
    (hXint : (interior setup.X).Nonempty)
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point) :
    setup.stepSize t * (proc.f (proc.x t ω) - proc.f x) ≤
      setup.V (proc.x t ω) x - setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x +
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) -
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ := by
  exact proc.stochasticMirrorDescent_oneStep_pathwise_of_residual_lower_bound t ω x
    (setup.V_lower_bound_on_carrier_of_nonempty_interior hXint
      (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω))

/-- One-step pathwise inequality with the residual lower bound discharged by an explicit
continuity/density boundary bridge for the feasible carrier. -/
theorem stochasticMirrorDescent_oneStep_pathwise_of_continuousOn
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (hXdense : setup.X ⊆ closure (interior setup.X))
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point) :
    setup.stepSize t * (proc.f (proc.x t ω) - proc.f x) ≤
      setup.V (proc.x t ω) x - setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x +
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) -
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ := by
  exact proc.stochasticMirrorDescent_oneStep_pathwise_of_residual_lower_bound t ω x
    (setup.V_lower_bound_on_carrier hcont hXdense
      (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω))

/-- One-step pathwise inequality with the residual lower bound discharged by the
relative-interior boundary bridge.

This is the lower-dimensional replacement for the older topological-interior density route:
the only remaining analytic input is continuity of the boundary-safe `V` on `X × X`. -/
theorem stochasticMirrorDescent_oneStep_pathwise_of_intrinsicClosure
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point) :
    setup.stepSize t * (proc.f (proc.x t ω) - proc.f x) ≤
      setup.V (proc.x t ω) x - setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x +
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) -
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ := by
  simpa [dualNorm] using
    mirrorDescent_oneStep_pathwise_of_all_carrier_lower_bound
      (f := proc.f) (V := setup.V) (point := fun y : setup.Point => y.1)
      (x := proc.x t ω) (xNext := proc.x (MirrorDescentSetup.nextTime t) ω)
      (xRef := x) (G := proc.G t ω) (g := proc.g (proc.x t ω))
      (δ := proc.G t ω - proc.g (proc.x t ω)) (γ := setup.stepSize t)
      (M := proc.M) (by simpa using setup.stepSize_pos t)
      (by
        have hg := proc.g_subgradient (proc.x t ω)
        rw [mem_carrierSubdifferential_iff] at hg
        simpa using hg x)
      (by simpa using proc.lemma_3_4 t ω x)
      (setup.V_lower_bound_all_carrier_of_intrinsicClosure hcont)
      (by abel) (by simpa [dualNorm] using proc.g_bound (proc.x t ω))

/-- One-step pathwise inequality before taking expectations. It exposes the exact
descent term, variance term, and martingale-difference term used in Lan's proof of
Theorem 4.1.

The source-backed all-carrier route is
`stochasticMirrorDescent_oneStep_pathwise_of_intrinsicClosure`, using the carrier
continuity bridge for the source gradient realization of `V`. -/
theorem stochasticMirrorDescent_oneStep_pathwise
    (t : MirrorDescentSetup.Time) (ω : Ω) (x : setup.Point) :
    setup.stepSize t * (proc.f (proc.x t ω) - proc.f x) ≤
      setup.V (proc.x t ω) x - setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) x +
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) -
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ := by
  exact proc.stochasticMirrorDescent_oneStep_pathwise_of_intrinsicClosure
    setup.V_continuousOn_carrier t ω x

/-- Mathlib-facing conditional-unbiasedness bridge for the random iterate.

This is the explicit version of Lan's proof step
`E[δ_t | ξ_[t-1]] = 0`, where
`δ_t = G(x_t, ξ_t) - g(x_t)` and `x_t` is measurable with respect to the past
sample filtration. Its proof is expected to use the derived `x_past_measurable`
bridge, `hξt_iIndep`, `hξt_identDistrib`, and the oracle expectation kernel. -/
theorem oracle_noise_condExp_zero_of_iid_adapted
    (t : MirrorDescentSetup.Time) :
    volume[(fun ω => proc.G t ω - proc.g (proc.x t ω)) |
        proc.filtration.seq (t.1 - 1)] =ᵐ[volume] 0 := by
  classical
  simpa [MirrorDescentProcess.G, MirrorDescentProcess.g, MirrorDescentProcess.x,
    MirrorDescentProcess.filtration] using
    (condExp_oracle_noise_eq_zero_of_iid_adapted
      (μ := volume) (m := proc.filtration.seq (t.1 - 1))
      (G := setup.oracle) (g := proc.g) (x := proc.x t) (Y := proc.ξt t)
      (proc.filtration.le (t.1 - 1))
      (setup.h_oracle_joint_measurable.sub (proc.g_measurable.comp measurable_fst))
      (proc.x_past_measurable t) (proc.x_measurable t) (proc.ξt_measurable t)
      (fun s hs => by
        simpa using
          proc.indepFun_past_measurable_currentSample t
            ((measurable_const.indicator hs).prodMk (proc.x_past_measurable t)))
      (by
        simpa [MirrorDescentProcess.G] using
          proc.random_iterate_oracle_noise_integrable t
            (proc.x_past_measurable t) (proc.x_measurable t))
      (fun x => by
        simpa using proc.fixed_oracle_deviation_current_sample_law_integral_zero x t))

/-- Mathlib-facing martingale cancellation with all analytic side conditions exposed.

This is the process-level version of Lan's martingale cancellation once the conditional
unbiasedness statement and integrability obligations have been established. The proof
is intentionally only a composition of the canonical conditional-expectation pullout
lemma and `MeasureTheory.integral_condExp`. -/
theorem martingale_term_integral_zero_of_condExp
    (t : MirrorDescentSetup.Time) (x : setup.Point)
    (hδ_int : Integrable (fun ω => proc.G t ω - proc.g (proc.x t ω)))
    (h_int :
      Integrable (fun ω =>
        ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ))
    (h_cond_zero :
      volume[(fun ω => proc.G t ω - proc.g (proc.x t ω)) |
          proc.filtration.seq (t.1 - 1)] =ᵐ[volume] 0) :
    ∫ ω,
      ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ = 0 := by
  exact integral_inner_sub_const_eq_zero_of_condExp_eq_zero
    (P := volume) (m := proc.filtration.seq (t.1 - 1))
    (hm := proc.filtration.le (t.1 - 1))
    (δ := fun ω => proc.G t ω - proc.g (proc.x t ω))
    (x := fun ω => (proc.x t ω).1) (c := x.1)
    (proc.x_past_measurable t).subtype_val h_cond_zero hδ_int h_int

/-- Integrability of the random oracle deviation `δ_t = G_t - g(x_t)`.

This is the vector side condition needed by the conditional-expectation pullout in
Lan's martingale cancellation step. It is separated from the cancellation theorem so
the proof can be routed through the square-deviation expectation hypothesis and
finite-dimensional `L² -> L¹` estimates. -/
theorem sampled_oracle_deviation_integrable
    (t : MirrorDescentSetup.Time) :
    Integrable (fun ω => proc.G t ω - proc.g (proc.x t ω)) := by
  let δ : Ω → DecisionSpace m := fun ω => proc.G t ω - proc.g (proc.x t ω)
  have hδ_meas : AEStronglyMeasurable δ volume := by
    simpa [δ] using proc.sampled_oracle_deviation_aestronglyMeasurable t
  have hsq : Integrable (fun ω => ‖δ ω‖ ^ 2) := by
    simpa [δ, dualNorm, oracleRandomIterateVarianceWellDefined,
      oracleRandomIterateVarianceKernel, MirrorDescentProcess.G, MirrorDescentProcess.g,
      MirrorDescentProcess.x] using (proc.h_oracle_random_iterate_variance t).1
  exact integrable_of_integrable_norm_sq hδ_meas hsq

/-- Integrability of the scalar martingale product
`⟪δ_t, x_t - x⟫`.

This is the scalar side condition needed by the conditional-expectation cancellation
bridge. It is the place where boundedness of `X` and integrability of `δ_t` combine. -/
theorem martingale_inner_integrable
    (t : MirrorDescentSetup.Time) (x : setup.Point) :
    Integrable (fun ω =>
      ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ) := by
  rcases (Metric.isBounded_iff_subset_closedBall x.1).1 setup.hX_bounded with ⟨R, hR⟩
  exact Integrable.inner_sub_const_of_bounded
    (μ := volume)
    (δ := fun ω => proc.G t ω - proc.g (proc.x t ω))
    (x := fun ω => (proc.x t ω).1) (c := x.1) (R := R)
    ((proc.x_measurable t).subtype_val.aestronglyMeasurable)
    (proc.sampled_oracle_deviation_integrable t)
    (ae_of_all volume (fun ω => by
      simpa [dist_eq_norm, norm_sub_rev] using hR (proc.x_mem t ω)))

/-- Integral cancellation for the martingale inner-product term from the conditional
unbiasedness bridge and adaptedness of `x_t`. -/
theorem martingale_term_integral_zero_from_conditional_unbiasedness
    (t : MirrorDescentSetup.Time) (x : setup.Point) :
    ∫ ω,
      ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ = 0 := by
  exact proc.martingale_term_integral_zero_of_condExp t x
    (proc.sampled_oracle_deviation_integrable t)
    (proc.martingale_inner_integrable t x)
    (proc.oracle_noise_condExp_zero_of_iid_adapted t)

/-- Conditional-expectation cancellation for the martingale term appearing in the
summed SMD bound. -/
theorem stochasticMirrorDescent_martingale_term_integral_zero
    (t : MirrorDescentSetup.Time) (x : setup.Point) :
    ∫ ω,
      ⟪proc.G t ω - proc.g (proc.x t ω), (proc.x t ω).1 - x.1⟫_ℝ = 0 := by
  exact proc.martingale_term_integral_zero_from_conditional_unbiasedness t x

/-- Jensen/convexity bridge for the weighted output `\bar x_s^k`. -/
theorem xBar_jensen_objective (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    proc.f (proc.xBar w ω) ≤
      (setup.outputWeightSum w)⁻¹ *
        Finset.sum (MirrorDescentSetup.outputTimes w)
          (fun t => setup.stepSize t * proc.f (proc.x t ω)) := by
  classical
  have hJ :=
    (convexOn_weighted_average_le_weighted_sum
      (hf := (by simpa [ConvexOnCarrier] using proc.f_convex))
      (s := MirrorDescentSetup.outputTimes w)
      (γ := setup.stepSize)
      (p := fun t => (proc.x t ω).1)
      (xbar := (proc.xBar w ω).1)
      (W := setup.outputWeightSum w)
      (hγ_nonneg := fun t _ht => le_of_lt (setup.stepSize_pos t))
      (hp_mem := fun t _ht => proc.x_mem t ω)
      (hW_pos := outputWeightSum_pos w)
      (hW_eq := rfl)
      (hxbar := rfl))
  have hleft :
      SOptLib.carrierTotalizeOn setup.X proc.f (proc.xBar w ω).1 =
        proc.f (proc.xBar w ω) := by
    simpa [SOptLib.totalizeOn] using
      SOptLib.totalizeOn_of_mem setup.X proc.f (proc.xBar_mem w ω)
  have hright :
      Finset.sum (MirrorDescentSetup.outputTimes w)
          (fun t => setup.stepSize t * SOptLib.carrierTotalizeOn setup.X proc.f (proc.x t ω).1) =
        Finset.sum (MirrorDescentSetup.outputTimes w)
          (fun t => setup.stepSize t * proc.f (proc.x t ω)) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    rw [show SOptLib.carrierTotalizeOn setup.X proc.f (proc.x t ω).1 =
        proc.f (proc.x t ω) by
      simpa [SOptLib.totalizeOn] using
        SOptLib.totalizeOn_of_mem setup.X proc.f (proc.x_mem t ω)]
  rw [hleft, hright] at hJ
  exact hJ

/-- Jensen/convexity bridge for the weighted output, stated directly as an
objective gap against `fStar`. -/
theorem xBar_jensen_gap (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    proc.f (proc.xBar w ω) - proc.fStar ≤
      (setup.outputWeightSum w)⁻¹ *
        Finset.sum (MirrorDescentSetup.outputTimes w)
          (fun t => setup.stepSize t * (proc.f (proc.x t ω) - proc.fStar)) := by
  exact
    weighted_average_sub_baseline_le_weighted_gap
      (s := MirrorDescentSetup.outputTimes w)
      (γ := setup.stepSize)
      (F := fun t => proc.f (proc.x t ω))
      (value := proc.f (proc.xBar w ω))
      (baseline := proc.fStar)
      (W := setup.outputWeightSum w)
      (hW_pos := outputWeightSum_pos w)
      (hW_eq := by simp [MirrorDescentSetup.outputWeightSum])
      (hvalue_le := proc.xBar_jensen_objective w ω)

/-- Variance bridge for the sampled oracle deviation along the random iterate. -/
theorem sampled_oracle_deviation_sq_integrable
    (t : MirrorDescentSetup.Time) :
    Integrable (fun ω => dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) := by
  simpa [oracleRandomIterateVarianceWellDefined, oracleRandomIterateVarianceKernel,
    MirrorDescentProcess.G, MirrorDescentProcess.g, MirrorDescentProcess.x] using
    (proc.h_oracle_random_iterate_variance t).1

/-- Variance bridge for the sampled oracle deviation along the random iterate. -/
theorem sampled_oracle_deviation_expectation_bound_from_fixed_variance
    (t : MirrorDescentSetup.Time) :
    proc.expectation
        (fun ω => dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) ≤
      proc.sigmaSq := by
  simpa [MirrorDescentProcess.expectation, oracleRandomIterateVarianceKernel,
    MirrorDescentProcess.G, MirrorDescentProcess.g, MirrorDescentProcess.x] using
    (proc.h_oracle_random_iterate_variance t).2

/-- Variance bridge for the sampled oracle deviation along the random iterate. -/
theorem sampled_oracle_deviation_expectation_bound (t : MirrorDescentSetup.Time) :
    proc.expectation
        (fun ω => dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2) ≤
      proc.sigmaSq := by
  exact proc.sampled_oracle_deviation_expectation_bound_from_fixed_variance t

/-- Telescope successive differences over an arbitrary natural-number interval. -/
theorem sum_Icc_sub_succ {α : Type*} [AddCommGroup α] (a : ℕ → α) (s k : ℕ)
    (hsk : s ≤ k) :
    Finset.sum (Finset.Icc s k) (fun n => a n - a (n + 1)) = a s - a (k + 1) := by
  exact _root_.sum_Icc_sub_succ a s k hsk

/-- Bregman telescope over the paper output window. -/
theorem output_times_bregman_telescope
    (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
        setup.V (proc.x t ω) proc.xStar -
          setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) proc.xStar) =
      setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar -
        setup.V
          (proc.x ⟨w.stop + 1, Nat.succ_le_succ (Nat.zero_le w.stop)⟩ ω)
          proc.xStar := by
  simpa [MirrorDescentSetup.nextTime, MirrorDescentSetup.OutputWindow.startTime] using
    outputWindow_sum_sub_succ
      (times := MirrorDescentSetup.outputTimes w)
      (a := fun t => setup.V (proc.x t ω) proc.xStar)
      w.start_pos w.le_stop
      (fun φ => MirrorDescentSetup.outputTimes_sum_eq_Icc w φ)

/-- Finite summation of the one-step inequalities, after telescoping the Bregman
terms and dropping the nonnegative terminal divergence. -/
theorem summed_one_step_gap_bound
    (hVlower :
      ∀ t : MirrorDescentSetup.Time, ∀ ω : Ω,
        (1 / 2 : ℝ) *
            ‖(proc.x t ω).1 - (proc.x (MirrorDescentSetup.nextTime t) ω).1‖ ^ 2 ≤
          setup.V (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω))
    (hVtail_nonneg :
      ∀ t : MirrorDescentSetup.Time, ∀ ω : Ω,
        0 ≤ setup.V (proc.x t ω) proc.xStar)
    (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    Finset.sum (MirrorDescentSetup.outputTimes w)
        (fun t => setup.stepSize t * (proc.f (proc.x t ω) - proc.fStar)) ≤
      setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar +
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
          (setup.stepSize t) ^ 2 *
            (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) -
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
          setup.stepSize t *
            ⟪proc.G t ω - proc.g (proc.x t ω),
              (proc.x t ω).1 - proc.xStar.1⟫_ℝ) := by
  classical
  exact
    summed_one_step_gap_bound_of_telescope
      (s := MirrorDescentSetup.outputTimes w)
      (gap := fun t => setup.stepSize t * (proc.f (proc.x t ω) - proc.fStar))
      (descent := fun t =>
        setup.V (proc.x t ω) proc.xStar -
          setup.V (proc.x (MirrorDescentSetup.nextTime t) ω) proc.xStar)
      (variance := fun t =>
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2))
      (correction := fun t =>
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω),
            (proc.x t ω).1 - proc.xStar.1⟫_ℝ)
      (initial := setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
        proc.xStar)
      (terminal := setup.V
        (proc.x ⟨w.stop + 1, Nat.succ_le_succ (Nat.zero_le w.stop)⟩ ω)
        proc.xStar)
      (by
        intro t _ht
        have hstep := proc.stochasticMirrorDescent_oneStep_pathwise_of_residual_lower_bound
          t ω proc.xStar (hVlower t ω)
        simpa [MirrorDescentProcess.fStar] using hstep)
      (by simpa using proc.output_times_bregman_telescope w ω)
      (hVtail_nonneg ⟨w.stop + 1, Nat.succ_le_succ (Nat.zero_le w.stop)⟩ ω)

/-- Deterministic finite-window summation of Lan's one-step SMD inequality.

This packages the Jensen step, the one-step inequality summed over the output
window, telescoping of the Bregman terms, and dropping the nonnegative terminal
Bregman divergence. -/
theorem summed_oneStep_pathwise_window_bound
    (hVlower :
      ∀ t : MirrorDescentSetup.Time, ∀ ω : Ω,
        (1 / 2 : ℝ) *
            ‖(proc.x t ω).1 - (proc.x (MirrorDescentSetup.nextTime t) ω).1‖ ^ 2 ≤
          setup.V (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω))
    (hVtail_nonneg :
      ∀ t : MirrorDescentSetup.Time, ∀ ω : Ω,
        0 ≤ setup.V (proc.x t ω) proc.xStar)
    (w : MirrorDescentSetup.OutputWindow) (ω : Ω) :
    proc.f (proc.xBar w ω) - proc.fStar ≤
      (setup.outputWeightSum w)⁻¹ *
        (setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar +
          Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
            (setup.stepSize t) ^ 2 *
              (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) -
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
          setup.stepSize t *
            ⟪proc.G t ω - proc.g (proc.x t ω),
              (proc.x t ω).1 - proc.xStar.1⟫_ℝ)) := by
  classical
  exact
    window_pathwise_bound_of_jensen_and_summed_one_step
      (s := MirrorDescentSetup.outputTimes w)
      (gap := fun ω => proc.f (proc.xBar w ω) - proc.fStar)
      (oneStepGap := fun t ω => setup.stepSize t * (proc.f (proc.x t ω) - proc.fStar))
      (initial := fun ω =>
        setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar)
      (error := fun ω =>
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
          (setup.stepSize t) ^ 2 *
            (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)))
      (correction := fun ω =>
        Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
          setup.stepSize t *
            ⟪proc.G t ω - proc.g (proc.x t ω),
              (proc.x t ω).1 - proc.xStar.1⟫_ℝ))
      (W := setup.outputWeightSum w)
      (outputWeightSum_pos w)
      (fun ω => proc.xBar_jensen_gap w ω)
      (fun ω => proc.summed_one_step_gap_bound hVlower hVtail_nonneg w ω)
      ω

/-- Finite-window cancellation of the martingale inner-product terms. -/
theorem window_martingale_sum_integral_zero
    (w : MirrorDescentSetup.OutputWindow) :
    ∫ ω,
      Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω),
            (proc.x t ω).1 - proc.xStar.1⟫_ℝ) = 0 := by
  exact integral_finset_sum_const_mul_eq_zero
    (μ := (volume : Measure Ω))
    (s := MirrorDescentSetup.outputTimes w)
    (c := fun t => setup.stepSize t)
    (Z := fun t ω =>
      ⟪proc.G t ω - proc.g (proc.x t ω),
        (proc.x t ω).1 - proc.xStar.1⟫_ℝ)
    (fun t _ht => proc.martingale_inner_integrable t proc.xStar)
    (fun t _ht => proc.stochasticMirrorDescent_martingale_term_integral_zero t proc.xStar)

/-- Finite-window expectation bound for the sampled-oracle squared deviation terms. -/
theorem window_variance_sum_expectation_bound
    (w : MirrorDescentSetup.OutputWindow) :
    ∫ ω,
      Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) ≤
      (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w := by
  simpa [MirrorDescentSetup.outputSquaredStepSum] using
    weighted_variance_sum_expectation_bound
      (μ := (volume : Measure Ω))
      (s := MirrorDescentSetup.outputTimes w)
      (γ := fun t => setup.stepSize t)
      (M2 := proc.M ^ 2)
      (σ2 := proc.sigmaSq)
      (Z := fun t ω => dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)
      (fun t _ht => proc.sampled_oracle_deviation_sq_integrable t)
      (fun t _ht => by
        simpa [MirrorDescentProcess.expectation] using
          proc.sampled_oracle_deviation_expectation_bound t)

/-- Integrability of the right-hand side in the integrated finite-window pathwise bound. -/
theorem window_pathwise_rhs_integrable
    (w : MirrorDescentSetup.OutputWindow) :
    Integrable (fun ω =>
      (setup.outputWeightSum w)⁻¹ *
        (setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar +
          Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
            (setup.stepSize t) ^ 2 *
              (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) -
          Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
            setup.stepSize t *
              ⟪proc.G t ω - proc.g (proc.x t ω),
                (proc.x t ω).1 - proc.xStar.1⟫_ℝ))) := by
  classical
  exact
    integrable_const_mul_add_finset_sum_sub_finset_sum
      (μ := (volume : Measure Ω))
      (s := MirrorDescentSetup.outputTimes w)
      (W := setup.outputWeightSum w)
      (A := fun ω =>
        setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar)
      (B := fun t ω =>
        (setup.stepSize t) ^ 2 *
          (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2))
      (C := fun t ω =>
        setup.stepSize t *
          ⟪proc.G t ω - proc.g (proc.x t ω),
            (proc.x t ω).1 - proc.xStar.1⟫_ℝ)
      (proc.start_bregman_integrable w)
      (fun t _ht =>
        ((integrable_const (c := proc.M ^ 2)).add
          (proc.sampled_oracle_deviation_sq_integrable t)).const_mul
            ((setup.stepSize t) ^ 2))
      (fun t _ht =>
        (proc.martingale_inner_integrable t proc.xStar).const_mul (setup.stepSize t))

/-- Expectation bridge for the already-summed pathwise SMD window bound.

This consumes the deterministic finite-window inequality, cancels the martingale
sum termwise, and uses the sampled-oracle variance bound on the weighted squared
deviation sum. -/
theorem stochasticMirrorDescent_expectation_of_window_pathwise_bound
    (w : MirrorDescentSetup.OutputWindow)
    (hpath :
      ∀ ω : Ω,
        proc.f (proc.xBar w ω) - proc.fStar ≤
          (setup.outputWeightSum w)⁻¹ *
            (setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar +
              Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
                (setup.stepSize t) ^ 2 *
                  (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) -
              Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
                setup.stepSize t *
                  ⟪proc.G t ω - proc.g (proc.x t ω),
                    (proc.x t ω).1 - proc.xStar.1⟫_ℝ))) :
    MirrorDescentProcess.expectation proc (fun ω => proc.f (proc.xBar w ω)) - proc.fStar ≤
      (setup.outputWeightSum w)⁻¹ *
        (MirrorDescentProcess.expectation proc (fun ω =>
          setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
            proc.xStar) +
         (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w) := by
  classical
  let s := MirrorDescentSetup.outputTimes w
  let A : Ω → ℝ := fun ω =>
    setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar
  let B : Ω → ℝ := fun ω =>
    Finset.sum s (fun t =>
      (setup.stepSize t) ^ 2 *
        (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2))
  let C : Ω → ℝ := fun ω =>
    Finset.sum s (fun t =>
      setup.stepSize t *
        ⟪proc.G t ω - proc.g (proc.x t ω),
          (proc.x t ω).1 - proc.xStar.1⟫_ℝ)
  have hAint : Integrable A := by
    simpa [A] using proc.start_bregman_integrable w
  have hBint : Integrable B := by
    simpa [B, s] using
      (integrable_finset_sum_const_mul (μ := (volume : Measure Ω)) (s := s)
        (c := fun t => (setup.stepSize t) ^ 2)
        (Z := fun t ω =>
          proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)
        (fun t _ht =>
          ((integrable_const (c := proc.M ^ 2)).add
            (proc.sampled_oracle_deviation_sq_integrable t))))
  have hCint : Integrable C := by
    simpa [C, s] using
      (integrable_finset_sum_const_mul (μ := (volume : Measure Ω)) (s := s)
        (c := fun t => setup.stepSize t)
        (Z := fun t ω =>
          ⟪proc.G t ω - proc.g (proc.x t ω),
            (proc.x t ω).1 - proc.xStar.1⟫_ℝ)
        (fun t _ht =>
          proc.martingale_inner_integrable t proc.xStar))
  have hbound := expectation_bound_of_window_pathwise_bound
    (μ := (volume : Measure Ω))
    (gap := fun ω => proc.f (proc.xBar w ω))
    (A := A) (B := B) (C := C)
    (baseline := proc.fStar)
    (W := setup.outputWeightSum w)
    (R := (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w)
    (proc.xBar_objective_integrable w)
    hAint hBint hCint
    (outputWeightSum_pos w)
    (by
      intro ω
      simpa [A, B, C, s] using hpath ω)
    (by
      simpa [B, s] using proc.window_variance_sum_expectation_bound w)
    (by
      simpa [C, s] using proc.window_martingale_sum_integral_zero w)
  simpa [A, MirrorDescentProcess.expectation] using hbound

/-- Convergence from the exact Bregman boundary facts needed by Lan's summation proof.

This non-paper helper isolates the geometric obligations from the stochastic summation:
the residual lower bound controls `x_t - x_{t+1}`, and tail nonnegativity is what permits
dropping the final Bregman term after telescoping. -/
theorem stochasticMirrorDescent_convergence_of_V_boundary_bridge
    (hVlower :
      ∀ t : MirrorDescentSetup.Time, ∀ ω : Ω,
        (1 / 2 : ℝ) *
            ‖(proc.x t ω).1 - (proc.x (MirrorDescentSetup.nextTime t) ω).1‖ ^ 2 ≤
          setup.V (proc.x t ω) (proc.x (MirrorDescentSetup.nextTime t) ω))
    (hVtail_nonneg :
      ∀ t : MirrorDescentSetup.Time, ∀ ω : Ω,
        0 ≤ setup.V (proc.x t ω) proc.xStar)
    (w : MirrorDescentSetup.OutputWindow) :
    MirrorDescentProcess.expectation proc (fun ω => proc.f (proc.xBar w ω)) - proc.fStar ≤
      (setup.outputWeightSum w)⁻¹ *
        (MirrorDescentProcess.expectation proc (fun ω =>
          setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
            proc.xStar) +
         (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w) := by
  exact _root_.stochasticMirrorDescent_convergence_of_V_boundary_bridge
    (μ := (volume : Measure Ω))
    (point := fun x : setup.Point => x.1)
    (V := setup.V)
    (x := proc.x)
    (xStar := proc.xStar)
    (nextTime := MirrorDescentSetup.nextTime)
    (pathwiseBound := fun w =>
      ∀ ω : Ω,
        proc.f (proc.xBar w ω) - proc.fStar ≤
          (setup.outputWeightSum w)⁻¹ *
            (setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar +
              Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
                (setup.stepSize t) ^ 2 *
                  (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) -
              Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
                setup.stepSize t *
                  ⟪proc.G t ω - proc.g (proc.x t ω),
                    (proc.x t ω).1 - proc.xStar.1⟫_ℝ)))
    (convergenceBound := fun _ w =>
      MirrorDescentProcess.expectation proc (fun ω => proc.f (proc.xBar w ω)) - proc.fStar ≤
        (setup.outputWeightSum w)⁻¹ *
          (MirrorDescentProcess.expectation proc (fun ω =>
            setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
              proc.xStar) +
           (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w))
    (h_expectation_of_pathwise := fun w hpath =>
      proc.stochasticMirrorDescent_expectation_of_window_pathwise_bound w hpath)
    (h_summed_oneStep_of_V_boundary := fun hVlower hVtail_nonneg w =>
      proc.summed_oneStep_pathwise_window_bound hVlower hVtail_nonneg w)
    (hVlower := hVlower)
    (hVtail_nonneg := hVtail_nonneg)
    (w := w)

/-- Convergence from relative-interior boundary geometry plus continuity of the
boundary-safe Bregman divergence on `X × X`. -/
theorem stochasticMirrorDescent_convergence_of_intrinsicClosure
    (hcont : ContinuousOn (fun p : setup.Point × setup.Point => setup.V p.1 p.2) Set.univ)
    (w : MirrorDescentSetup.OutputWindow) :
    MirrorDescentProcess.expectation proc (fun ω => proc.f (proc.xBar w ω)) - proc.fStar ≤
      (setup.outputWeightSum w)⁻¹ *
        (MirrorDescentProcess.expectation proc (fun ω =>
          setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
            proc.xStar) +
         (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w) := by
  exact mirror_descent_convergence_of_intrinsicClosure
    (μ := (volume : Measure Ω))
    (point := fun x : setup.Point => x.1)
    (V := setup.V)
    (x := proc.x)
    (xStar := proc.xStar)
    (nextTime := MirrorDescentSetup.nextTime)
    (pathwiseBound := fun w =>
      ∀ ω : Ω,
        proc.f (proc.xBar w ω) - proc.fStar ≤
          (setup.outputWeightSum w)⁻¹ *
            (setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω) proc.xStar +
              Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
                (setup.stepSize t) ^ 2 *
                  (proc.M ^ 2 + dualNorm (proc.G t ω - proc.g (proc.x t ω)) ^ 2)) -
              Finset.sum (MirrorDescentSetup.outputTimes w) (fun t =>
                setup.stepSize t *
                  ⟪proc.G t ω - proc.g (proc.x t ω),
                    (proc.x t ω).1 - proc.xStar.1⟫_ℝ)))
    (convergenceBound := fun _ w =>
      MirrorDescentProcess.expectation proc (fun ω => proc.f (proc.xBar w ω)) - proc.fStar ≤
        (setup.outputWeightSum w)⁻¹ *
          (MirrorDescentProcess.expectation proc (fun ω =>
            setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
              proc.xStar) +
           (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w))
    (h_expectation_of_pathwise := fun w hpath =>
      proc.stochasticMirrorDescent_expectation_of_window_pathwise_bound w hpath)
    (h_summed_oneStep_of_V_boundary := fun hVlower hVtail_nonneg w =>
      proc.summed_oneStep_pathwise_window_bound hVlower hVtail_nonneg w)
    (hcont := hcont)
    (hVlower_of_intrinsicClosure := fun hcont x z =>
      setup.V_lower_bound_all_carrier_of_intrinsicClosure hcont x z)
    (hVtail_nonneg_of_intrinsicClosure := fun hcont x z =>
      setup.V_nonneg_all_carrier_of_intrinsicClosure hcont x z)
    (w := w)

/-- `book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math` ::
`"E[f(\\bar{x}_s^k)] - f^* ≤ (\\sum_{t=s}^{k} \\gamma_t)^{-1}[E[V(x_s, x^*)] + (M^2 + σ^2)\\sum_{t=s}^{k} \\gamma_t^2]"`.
The formal statement uses the public paper expectation layer `expectation`; the theorem-head
random variables are certified by `xBar_objective_expectationWellDefined` and
`start_bregman_expectationWellDefined` rather than relying silently on raw totalized `∫`. -/
theorem stochasticMirrorDescent_convergence
    (w : MirrorDescentSetup.OutputWindow) :
    MirrorDescentProcess.expectation proc (fun ω => proc.f (proc.xBar w ω)) - proc.fStar ≤
      (setup.outputWeightSum w)⁻¹ *
        (MirrorDescentProcess.expectation proc (fun ω =>
          setup.V (proc.x (MirrorDescentSetup.OutputWindow.startTime w) ω)
            proc.xStar) +
         (proc.M ^ 2 + proc.sigmaSq) * setup.outputSquaredStepSum w) := by
  exact proc.stochasticMirrorDescent_convergence_of_intrinsicClosure
    setup.V_continuousOn_carrier w

end MirrorDescentProcess
end AliasMeasurableSpaces
