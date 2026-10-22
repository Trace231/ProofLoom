import Mathlib.MeasureTheory.Integral.Bochner.Basic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Selection
import SOptLib.Model.Stationarity
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.ConvexFOC
import SOptLib.Axioms.BaillonHaddad

open MeasureTheory Topology
open scoped Gradient InnerProductSpace

namespace SOptLib

/-- The start-point Bregman observable is integrable under compact continuous
kernel control.

If the Bregman kernel is continuous on the compact product carrier and the
random start point is measurable, then the scalar observable `ω ↦ V (X ω) z` is
integrable for every fixed comparison point `z`.

Layer: Glue | Gap: Level 1 (canonical start Bregman integrability)
Proof: compactness and continuity give a uniform absolute bound for the
  Bregman kernel on the product carrier. Measurability of the left section and
  finite-measure boundedness then discharge integrability.
Source: Mathlib compactness, continuous functions, and finite-measure
  integrability APIs
Used in: stochastic mirror descent start-distance Bregman integrability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem startBregman_integrable
    {Ω P : Type*} [MeasurableSpace Ω] [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] {μ : Measure Ω} [IsFiniteMeasure μ]
    (V : P → P → ℝ) (X : Ω → P) (z : P)
    (hX : Measurable X)
    (hV_cont : ContinuousOn (fun p : P × P => V p.1 p.2) Set.univ)
    (hcompact : IsCompact (Set.univ : Set (P × P))) :
    Integrable (fun ω => V (X ω) z) μ := by
  rcases exists_abs_bound_on_compact_product_of_continuousOn
      (D := V) hcompact hV_cont with
    ⟨_C, _hC_nonneg, hC⟩
  exact integrable_bregman_of_measurable_bounded
    (V := V) (X := X) (z := z)
    (measurable_left_section_of_continuousOn_univ V hV_cont z)
    hX
    (fun ω => hC (X ω) z)

/-- Start-point Bregman observables are measurable from a nonempty-interior carrier.

If the iterate `X` is measurable and a convex carrier has nonempty interior, the
continuity bridge for the carrier Bregman map makes `ω ↦ V (X ω) z`
measurable.

Layer: Model | Gap: Level 1 (start-point Bregman measurability from nonempty interior)
Proof: Apply the carrier Bregman continuity lemma supplied by convexity and
  nonempty interior, then use measurable composition for the fixed-start
  observable.
Source: Mathlib topology of continuous-on maps, convex nonempty-interior APIs,
  and Borel measurability composition
Used in: stochastic mirror descent initialization of Bregman-distance observables
  for prox-step measurability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem startBregman_measurable_of_nonemptyInterior
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {C : Set E} (V : {x : E // x ∈ C} → {x : E // x ∈ C} → ℝ)
    (X : Ω → {x : E // x ∈ C}) (z : {x : E // x ∈ C})
    (hX : Measurable X)
    (hC_convex : Convex ℝ C)
    (hV_uniqueDiffOn : UniqueDiffOn ℝ C →
      ContinuousOn
        (fun p : {x : E // x ∈ C} × {x : E // x ∈ C} => V p.1 p.2) Set.univ)
    (hCint : (interior C).Nonempty) :
    Measurable (fun ω => V (X ω) z) := by
  exact measurable_bregman_start_of_measurable_iterate
    (V := V) (X := X) (z := z)
    (carrierBregmanDivergence_continuousOn_of_nonempty_interior
      hC_convex hV_uniqueDiffOn hCint)
    hX

/-- The start-point Bregman observable is integrable from nonempty carrier interior.

For a convex carrier with nonempty interior, continuity of the carrier Bregman
divergence on the compact carrier product gives a uniform bound, so a measurable
left section along the random start point is integrable under a finite measure.

Layer: Model | Gap: Level 1 (Bregman integrability from nonempty interior)
Proof: use nonempty interior to obtain carrier Bregman continuity, then compact
  boundedness gives an absolute bound on the product. Measurability of the left
  section and boundedness under a finite measure finish integrability.
Source: Mathlib convex topology, compactness, and MeasureTheory integrability APIs
Used in: stochastic mirror descent initialization of Bregman integrability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem startBregman_integrable_of_nonemptyInterior
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {C : Set E} (V : {x : E // x ∈ C} → {x : E // x ∈ C} → ℝ)
    (X : Ω → {x : E // x ∈ C}) (z : {x : E // x ∈ C})
    (hX : Measurable X)
    (hC_convex : Convex ℝ C)
    (hV_uniqueDiffOn : UniqueDiffOn ℝ C →
      ContinuousOn
        (fun p : {x : E // x ∈ C} × {x : E // x ∈ C} => V p.1 p.2) Set.univ)
    (hCint : (interior C).Nonempty)
    (hcompact : IsCompact (Set.univ : Set ({x : E // x ∈ C} × {x : E // x ∈ C}))) :
    Integrable (fun ω => V (X ω) z) μ := by
  have hcont :
      ContinuousOn
        (fun p : {x : E // x ∈ C} × {x : E // x ∈ C} => V p.1 p.2) Set.univ :=
    carrierBregmanDivergence_continuousOn_of_nonempty_interior
      hC_convex hV_uniqueDiffOn hCint
  rcases exists_abs_bound_on_compact_product_of_continuousOn
      (D := V) hcompact hcont with
    ⟨_K, _hK_nonneg, hK⟩
  exact integrable_bregman_of_measurable_bounded
    (V := V) (X := X) (z := z)
    (measurable_left_section_of_continuousOn_univ V hcont z) hX
    (fun ω => hK (X ω) z)

/-- Convexity of a stochastic objective is preserved by Bochner integration.

If a carrier `X` is convex, every sample objective `F · ω` is convex on that
carrier, and every carrier point has an integrable sample value, then the
expected objective `x ↦ ∫ ω, F x ω ∂ μ` is convex on the same carrier.

Layer: Glue | Gap: Level 1 (convex stochastic kernel expectation)
Proof: apply pointwise convexity under the integral, use integrability under
  scalar multiplication and addition, and conclude with `MeasureTheory.integral_mono`,
  `integral_add`, and `integral_const_mul`.
Source: Mathlib measure theory Bochner integral and convex analysis APIs
Used in: stochastic mirror descent expected objective convexity
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem ConvexOnCarrier.integral
    {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]
    (X : Set E) (F : {x : E // x ∈ X} → Ω → ℝ) (μ : Measure Ω)
    (hX_convex : Convex ℝ X)
    (hF_convex : ∀ ω, ConvexOnCarrier X (fun x => F x ω))
    (h_integrable : ∀ x : {x : E // x ∈ X}, Integrable (fun ω => F x ω) μ) :
    ConvexOnCarrier X (fun x : {x : E // x ∈ X} => ∫ ω, F x ω ∂ μ) := by
  unfold ConvexOnCarrier
  refine ⟨hX_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ X := hX_convex hx hy ha hb hab
  let xp : {x : E // x ∈ X} := ⟨x, hx⟩
  let yp : {x : E // x ∈ X} := ⟨y, hy⟩
  let zp : {x : E // x ∈ X} := ⟨a • x + b • y, hxy⟩
  have hxp : Integrable (fun ω => F xp ω) μ := h_integrable xp
  have hyp : Integrable (fun ω => F yp ω) μ := h_integrable yp
  have hleft : Integrable (fun ω => F zp ω) μ := h_integrable zp
  have hAx : Integrable (fun ω => a * F xp ω) μ := by
    simpa only [smul_eq_mul] using hxp.const_mul a
  have hBy : Integrable (fun ω => b * F yp ω) μ := by
    simpa only [smul_eq_mul] using hyp.const_mul b
  have hright : Integrable (fun ω => a * F xp ω + b * F yp ω) μ := hAx.add hBy
  have hpoint :
      (fun ω => F zp ω) ≤ fun ω => a * F xp ω + b * F yp ω := by
    intro ω
    have hc := (hF_convex ω).2 hx hy ha hb hab
    simpa [carrierTotalizeOn, xp, yp, zp, hxy, hx, hy] using hc
  have hle := MeasureTheory.integral_mono hleft hright hpoint
  have hright_eq :
      (∫ ω, a * F xp ω + b * F yp ω ∂ μ) =
        a * (∫ ω, F xp ω ∂ μ) + b * (∫ ω, F yp ω ∂ μ) := by
    rw [integral_add hAx hBy]
    simp [integral_const_mul]
  rw [hright_eq] at hle
  simpa [carrierTotalizeOn, hxy, hx, hy, xp, yp, zp] using hle

end SOptLib

-- Batch 5 promoted staging declarations

-- From Staging/smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
--   (orig was: finite_smooth_quadratic_upper_bound_of_hasGradientAt)
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E];
--      inner products support the gradient pairing and Cauchy-Schwarz, and
--      CompleteSpace is required by Mathlib's HasGradientAt.
--   measure: none; this is deterministic segment calculus.
--   convexity: explicit Convex ℝ X hypothesis, matching Mathlib convex-set API.
-- G0.3 reusability — could instantiate:
--   1. finite-sum stochastic conditional gradient, smooth objective decrease on
--      the LMO affine update segment.
--   2. stochastic mirror descent / variance-reduced mirror descent, smooth
--      objective upper bound before prox or estimator-error absorption.
-- G0.4 search trace:
--   queries: ["smooth quadratic upper bound",
--     "HasGradientAt Lipschitz gradient convex segment"]
--   top hits: ["Convex.carrier_smooth_quadratic_upper_bound",
--     "le_value_add_of_hasDerivWithinAt_le_affine_on_Icc",
--     "hasFDerivWithinAt_of_contDiffOn_gradientWithin_comp",
--     "carrierGradient_lipschitz_of_assumption"]
--   coverage: partial — Convex.carrier_smooth_quadratic_upper_bound assumes a
--     carrier-subtype ambient C¹/fderivWithin package, while this theorem uses
--     pointwise HasGradientAt on feasible points plus a direct Lipschitz-gradient
--     hypothesis.
-- G0.4 not-a-thin-wrapper rationale: packages segment feasibility, pointwise
--   gradient chain rule, Lipschitz-gradient error control, Cauchy-Schwarz, and
--   scalar derivative integration into the standard descent lemma.
-- G0.5 structural-content rationale: the theorem exposes the reusable smooth
--   descent invariant directly over ambient feasible points, not through a
--   carrier realization or paper setup fields.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step new content beyond
--   one Mathlib/SOptLib call.
-- G0.5d minimal-hypothesis check: pointwise HasGradientAt on X is used only at
--   segment points; global ContDiffOn/DifferentiableOn hypotheses were avoided.

/-- Pointwise gradients with Lipschitz gradient give the smooth quadratic upper
bound on a convex feasible segment.

If every feasible point has the prescribed gradient and the gradient map is
`L`-Lipschitz on the feasible set, then the usual descent lemma holds between
any two feasible points.

Layer: Layer0 | Gap: Level 1 (smooth objective descent from pointwise gradients)
Proof: restrict the objective to the affine segment, identify the scalar
  derivative by the `HasGradientAt` chain rule, bound the derivative error by
  Lipschitz continuity and Cauchy-Schwarz, then integrate the affine derivative
  bound on `[0, 1]`.
Source: Mathlib convex segments, `HasGradientAt` chain rule, and Hilbert-space
  Cauchy-Schwarz APIs
Used in: stochastic conditional gradient and mirror-descent smooth objective
  decrease before oracle-error or prox-descent absorption
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (f : E → ℝ) (grad : E → E) (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hgrad : ∀ z ∈ X, HasGradientAt f (grad z) z)
    (hgrad_lipschitz :
      ∀ z ∈ X, ∀ w ∈ X, ‖grad z - grad w‖ ≤ L * ‖z - w‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2 := by
  let d : E := y - x
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap x y t
  let Fseg : ℝ → ℝ := fun t => f (line t)
  have hF0 : Fseg 0 = f x := by
    simp [Fseg, line]
  have hF1 : Fseg 1 = f y := by
    simp [Fseg, line]
  have hline_mem : ∀ t ∈ s, line t ∈ X := by
    intro t ht
    exact hX_convex.lineMap_mem hx hy ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg ⟪grad (line t), d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := y)
          (s := s) (x := t))
    have hfderiv :
        HasFDerivAt f (InnerProductSpace.toDual ℝ E (grad (line t))) (line t) :=
      (hgrad (line t) (hline_mem t ht)).hasFDerivAt
    have hfseg : HasDerivWithinAt Fseg
        ((InnerProductSpace.toDual ℝ E (grad (line t))) d) s t := by
      simpa [Fseg, Function.comp_def] using
        hfderiv.comp_hasDerivWithinAt t hline_deriv
    simpa using hfseg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪grad (line t), d⟫_ℝ ≤
        ⟪grad x, d⟫_ℝ + L * t * ‖d‖ ^ 2 := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : line t - x = t • d := by
      simp [line, d, AffineMap.lineMap_apply_module']
    have hnorm_line : ‖line t - x‖ = t * ‖d‖ := by
      rw [hseg_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hlip : ‖grad (line t) - grad x‖ ≤ L * (t * ‖d‖) := by
      calc
        ‖grad (line t) - grad x‖
            ≤ L * ‖line t - x‖ :=
          hgrad_lipschitz (line t) (hline_mem t ht) x hx
        _ = L * (t * ‖d‖) := by rw [hnorm_line]
    have hinner_diff :
        ⟪grad (line t), d⟫_ℝ - ⟪grad x, d⟫_ℝ =
          ⟪grad (line t) - grad x, d⟫_ℝ := by
      rw [inner_sub_left]
    have hcs :
        ⟪grad (line t) - grad x, d⟫_ℝ ≤
          ‖grad (line t) - grad x‖ * ‖d‖ := by
      calc
        ⟪grad (line t) - grad x, d⟫_ℝ
            ≤ |⟪grad (line t) - grad x, d⟫_ℝ| := le_abs_self _
        _ ≤ ‖grad (line t) - grad x‖ * ‖d‖ :=
          abs_real_inner_le_norm (grad (line t) - grad x) d
    have hmul :
        ‖grad (line t) - grad x‖ * ‖d‖ ≤ L * t * ‖d‖ ^ 2 := by
      have hmul' :
          ‖grad (line t) - grad x‖ * ‖d‖ ≤
            (L * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
      calc
        ‖grad (line t) - grad x‖ * ‖d‖
            ≤ (L * (t * ‖d‖)) * ‖d‖ := hmul'
        _ = L * t * ‖d‖ ^ 2 := by ring
    have hdiff_le :
        ⟪grad (line t), d⟫_ℝ - ⟪grad x, d⟫_ℝ ≤
          L * t * ‖d‖ ^ 2 := by
      calc
        ⟪grad (line t), d⟫_ℝ - ⟪grad x, d⟫_ℝ
            = ⟪grad (line t) - grad x, d⟫_ℝ := hinner_diff
        _ ≤ ‖grad (line t) - grad x‖ * ‖d‖ := hcs
        _ ≤ L * t * ‖d‖ ^ 2 := hmul
    linarith
  let phi : ℝ → ℝ := fun t =>
    if ht : t ∈ s then ⟪grad (line t), d⟫_ℝ else 0
  have hderiv_phi : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg (phi t) s t := by
    intro t ht
    rw [show phi t = ⟪grad (line t), d⟫_ℝ by
      dsimp [phi]
      rw [if_pos ht]]
    exact hderiv t ht
  have hbound_phi : ∀ (t : ℝ) (ht : t ∈ s),
      phi t ≤ ⟪grad x, d⟫_ℝ + (L * ‖d‖ ^ 2) * t := by
    intro t ht
    have hb := hbound t ht
    rw [show phi t = ⟪grad (line t), d⟫_ℝ by
      dsimp [phi]
      rw [if_pos ht]]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hb
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪grad x, d⟫_ℝ + (L * ‖d‖ ^ 2) / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg phi
      ⟪grad x, d⟫_ℝ (L * ‖d‖ ^ 2) hderiv_phi hbound_phi
  rw [hF0, hF1] at hscalar
  change f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2
  rw [show d = y - x by rfl] at hscalar
  calc
    f y ≤ f x + ⟪grad x, y - x⟫_ℝ +
        (L * ‖y - x‖ ^ 2) / 2 := hscalar
    _ = f x + ⟪grad x, y - x⟫_ℝ +
        (L / 2) * ‖y - x‖ ^ 2 := by ring

-- From Staging/measurable_of_norm_sub_le_mul_on_subtype.lean
-- Generalization plan (G0):
-- G0.1 naming: measurable_of_norm_sub_le_mul_on_subtype
-- G0.2 typeclass level used:
--   E: SeminormedAddCommGroup plus MeasurableSpace/OpensMeasurableSpace, because the proof rewrites
--      subtype distance to the ambient norm distance and uses continuity-to-measurability.
--   F: SeminormedAddCommGroup plus MeasurableSpace/BorelSpace, because the codomain only
--      needs subtraction, norm distance, and continuity-to-measurability.
--   measure: none; the conclusion is plain Borel measurability.
--   convexity: none; feasibility is represented only by an arbitrary carrier subtype.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient component-gradient measurability on the
--      feasible carrier.
--   2. finite-sum variance-reduced conditional gradient component-oracle measurability
--      after restricting smooth components to a compact feasible set.
-- G0.4 search trace:
--   queries: ["measurable lipschitz subtype", "continuous_of_dist_le lipschitz measurable"]
--   top hits: ["SOptLib.LipschitzWith.measurable",
--     "SOptLib.lipschitzWith_of_norm_sub_le_mul",
--     "SOptLib.measurable_of_supporting_inequality_and_abs_inner_bound",
--     "SOptLib.proxPoint_measurable_oracle_of_continuous"]
--   coverage: partial — lipschitzWith_of_norm_sub_le_mul packages a metric bound, and
--     LipschitzWith.measurable is real-valued only; neither states vector-valued carrier
--     measurability from an ambient-norm subtype estimate.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the recurring carrier-subtype
--   invariant that an ambient norm Lipschitz estimate is enough for Borel measurability
--   of a vector-valued restricted field.
-- G0.5 structural-content rationale: the statement exposes the carrier restriction and
--   ambient norm estimate directly, avoiding repeated local conversion through subtype
--   distances and Lipschitz constants.
-- G0.5c thin-wrapper self-detect: clean — body has a two-step construction, first
--   converting the ambient subtype estimate into a LipschitzWith proof and then applying
--   continuity-to-measurability.
-- G0.5d minimal-hypothesis check: all already minimal; no global differentiability,
--   convexity, compactness, probability, or finite-dimensional hypotheses are used.

/-- An ambient norm Lipschitz estimate on a carrier subtype gives measurability.

If a vector-valued field on `{x // x ∈ s}` has pointwise differences bounded by
`L` times the ambient norm distance of the underlying points, then the field is
Borel measurable on the carrier subtype.

Layer: Glue | Gap: Level 0 (carrier Lipschitz field measurability)
Proof: rewrite subtype distance as ambient norm distance, package the estimate
  as a `LipschitzWith` map, and use Lipschitz continuity to obtain Borel
  measurability.
Source: Mathlib metric Lipschitz maps, subtype metric topology, and Borel
  measurability APIs
Used in: stochastic nonconvex conditional gradient component-gradient
  measurability on the feasible carrier
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem measurable_of_norm_sub_le_mul_on_subtype
    {E F : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeminormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    {s : Set E} (g : {x : E // x ∈ s} → F) (L : ℝ)
    (h : ∀ x y : {x : E // x ∈ s}, ‖g x - g y‖ ≤ L * ‖(x : E) - (y : E)‖) :
    Measurable g := by
  have hLip : LipschitzWith (Real.toNNReal L) g := by
    refine lipschitzWith_of_norm_sub_le_mul g L ?_
    intro x y
    rw [Subtype.dist_eq, dist_eq_norm]
    exact h x y
  exact hLip.continuous.measurable

-- From Staging/norm_le_ref_norm_add_lipschitz_mul_diam.lean
-- Generalization plan (G0):
-- G0.1 naming: norm_le_ref_norm_add_lipschitz_mul_diam (orig was: gradf_norm_bound_on_X)
-- G0.2 typeclass level used:
--   E: SeminormedAddGroup; only subtraction and norms of domain differences are used.
--   F: SeminormedAddGroup; only subtraction and norms of image differences are used.
--   measure: none; this is a deterministic pointwise norm estimate.
--   convexity: none; feasibility and convexity are consumed upstream to provide the two pointwise bounds.
-- G0.3 reusability — could instantiate:
--   1. stochastic conditional gradient, bounding the mean-gradient norm on a bounded feasible carrier
--   2. finite-sum conditional gradient, bounding averaged component gradients by a start-gradient plus diameter budget
-- G0.4 search trace:
--   queries: ["norm Lipschitz diameter", "norm bound reference Lipschitz distance"]
--   top hits: ["lipschitzWith_of_norm_sub_le_mul", "exists_bound_of_bounded_lipschitzOn_real", "LipschitzWith.norm_sub_le_of_le", "norm_le_norm_add_norm_sub'"]
--   coverage: partial — hits provide Lipschitz packaging or the triangle component, but not the combined reference-norm plus diameter-budget estimate
-- G0.4 not-a-thin-wrapper rationale: the signature packages the reusable three-part invariant `norm at x <= norm at base + Lipschitz constant * diameter`, combining a pointwise image-difference bound, a domain-diameter bound, and the norm triangle estimate.
-- G0.5 structural-content rationale: no new def or structure is introduced; the theorem exposes the exact deterministic estimate reused by carrier-bounded gradient arguments.
-- G0.5c thin-wrapper self-detect: clean — body combines triangle, monotone scalar multiplication, and arithmetic rather than aliasing a single Mathlib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; the Lipschitz and diameter hypotheses are pointwise at the pair used.

/-- A map value norm is bounded by a reference value plus a Lipschitz-diameter budget.

If `g x` differs from `g x₀` by at most `L * ‖x - x₀‖`, and the two domain
points are at distance at most `D`, then the norm at `x` is bounded by the
reference norm at `x₀` plus `L * D`.

Layer: Layer0 | Gap: Level 0 (reference-point Lipschitz diameter norm bound)
Proof: combine `norm_le_norm_add_norm_sub'` with monotonicity of multiplication
  by the nonnegative Lipschitz constant, then close the scalar inequalities by
  linear arithmetic.
Source: Mathlib normed additive group triangle estimates and ordered real
  arithmetic
Used in: stochastic and finite-sum conditional-gradient bounded-gradient
  estimates on a bounded feasible carrier
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem norm_le_ref_norm_add_lipschitz_mul_diam
    {E F : Type*} [SeminormedAddGroup E] [SeminormedAddGroup F]
    (g : E → F) (x x₀ : E) (L D : ℝ)
    (h_lipschitz : ‖g x - g x₀‖ ≤ L * ‖x - x₀‖)
    (h_diam : ‖x - x₀‖ ≤ D)
    (hL_nonneg : 0 ≤ L) :
    ‖g x‖ ≤ ‖g x₀‖ + L * D := by
  have hdist : L * ‖x - x₀‖ ≤ L * D :=
    mul_le_mul_of_nonneg_left h_diam hL_nonneg
  have hbase : ‖g x‖ ≤ ‖g x₀‖ + ‖g x - g x₀‖ :=
    norm_le_norm_add_norm_sub' (g x) (g x₀)
  linarith

-- From Staging/integrable_stationarity_of_measurable_bounded_on_feasible_process.lean
open MeasureTheory
open scoped InnerProductSpace

namespace SOptLib.ConditionalGradient

-- Generalization plan (G0):
-- G0.1 naming: integrable_stationarity_of_measurable_bounded_on_feasible_process
--   (concept is the conditional-gradient Wolfe stationarity certificate).
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E] plus measurability
--      classes needed by the existing LMO-based Wolfe-gap measurability bridge;
--      no finite dimensionality or completeness is used.
--   measure: arbitrary finite measure μ via [IsFiniteMeasure μ], since the
--      proof only needs finite-measure bounded integrability.
--   convexity: none; feasibility enters through pointwise LMO membership,
--      argmin certificates, and a diameter bound, not through global convexity.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, proving expected Wolfe-gap
--      well-definedness along generated feasible iterates.
--   2. finite-sum nonconvex conditional gradient, reusing the same LMO-based
--      Wolfe-gap bound for generated finite-sum iterates.
-- G0.4 search trace:
--   queries: ["Wolfe gap integrable measurable bounded",
--     "conditional gradient wolfeGap linearMinimizer norm bound",
--     "bounded measurable real random variable integrable"]
--   top hits: ["SOptLib.integrable_of_measurable_bounded_real",
--     "SOptLib.ConditionalGradient.wolfeGap_measurable_of_lmo",
--     "SOptLib.ConditionalGradient.wolfeGap_eq_linearMinimizer",
--     "SOptLib.integrable_bregman_of_measurable_bounded",
--     "SOptLib.inner_sub_const_of_bounded"]
--   coverage: partial — existing hits provide the final finite-measure
--      bounded-integrability bridge and the Wolfe-gap measurability/equality
--      components, but none subsumes the combined conditional-gradient process
--      theorem with gradient and diameter bounds.
-- G0.4 not-a-thin-wrapper rationale: the theorem combines LMO-realized
--   Wolfe-gap measurability, the selected Wolfe-gap/LMO equality, Cauchy-Schwarz
--   control, and finite-measure bounded integrability.
-- G0.5 structural-content rationale: the statement is about the concrete
--   conditional-gradient `wolfeGap` certificate and exposes the reusable
--   process-level norm and diameter invariants needed for integrability.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step measurable
--   construction plus inner-product bound, not a direct single-lemma alias.
-- G0.5d minimal-hypothesis check: all already minimal; measurability is only
--   required for the parameter process, evaluation, gradient, and LMO selector,
--   while the norm and diameter controls are pointwise along the process.

/-- A bounded conditional-gradient Wolfe stationarity certificate is integrable
along a measurable feasible process.

If a measurable process is evaluated in a Hilbert space, the gradient and LMO
selectors are measurable, the selected Wolfe-gap certificate is realized by the
LMO, and the process has pointwise gradient and LMO-displacement bounds, then
the Wolfe-gap random variable is integrable under any finite measure.

Layer: Layer0 | Gap: Level 1 (conditional-gradient stationarity integrability)
Proof: use the LMO Wolfe-gap measurability theorem, rewrite the gap through the
  LMO selector, bound the inner product by the gradient and diameter controls,
  and apply bounded measurable real integrability.
Source: Frank-Wolfe conditional-gradient stationarity certificates, Hilbert-space
  Cauchy-Schwarz bounds, and Mathlib finite-measure integrability APIs
Used in: stochastic and finite-sum conditional-gradient expected Wolfe-gap
  well-definedness along generated feasible iterates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integrable_stationarity_of_measurable_bounded_on_feasible_process
    {Ω P E : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [MeasurableSub₂ E] [OpensMeasurableSpace (E × E)]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Set E}
    (eval : P → E) (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (linearMinimizer : E → E)
    (process : Ω → P) (G D : ℝ)
    (heval : Measurable eval)
    (hgrad : Measurable (fun p : P => grad (eval p)))
    (hlmo : Measurable linearMinimizer)
    (hprocess : Measurable process)
    (linearMinimizer_mem : ∀ g : E, linearMinimizer g ∈ X)
    (linearMinimizer_is_argmin :
      ∀ g z : E, z ∈ X → ⟪g, linearMinimizer g⟫_ℝ ≤ ⟪g, z⟫_ℝ)
    (hmax : ∀ x : E, ∀ z : {z : E // z ∈ X},
      ⟪grad x, x - (z : E)⟫_ℝ ≤
        ⟪grad x, x - (maximizer x : E)⟫_ℝ)
    (hgrad_bound : ∀ ω, ‖grad (eval (process ω))‖ ≤ G)
    (hdiam : ∀ ω,
      ‖eval (process ω) - linearMinimizer (grad (eval (process ω)))‖ ≤ D)
    (hG_nonneg : 0 ≤ G) :
    Integrable (fun ω =>
      wolfeGap grad maximizer (eval (process ω))) μ := by
  classical
  have hgap_meas :
      Measurable (fun p : P => wolfeGap grad maximizer (eval p)) :=
    wolfeGap_measurable_of_lmo
      (eval := eval) (grad := grad) (maximizer := maximizer)
      (linearMinimizer := linearMinimizer)
      (heval := heval) (hgrad := hgrad) (hlmo := hlmo)
      (linearMinimizer_mem := linearMinimizer_mem)
      (linearMinimizer_is_argmin := linearMinimizer_is_argmin)
      (hmax := hmax)
  have hmeas :
      Measurable (fun ω => wolfeGap grad maximizer (eval (process ω))) :=
    hgap_meas.comp hprocess
  have hbound :
      ∀ ω, ‖wolfeGap grad maximizer (eval (process ω))‖ ≤ G * D := by
    intro ω
    let y : E := linearMinimizer (grad (eval (process ω)))
    have hgap_eq :
        wolfeGap grad maximizer (eval (process ω)) =
          ⟪grad (eval (process ω)), eval (process ω) - y⟫_ℝ := by
      simpa [y] using
        (wolfeGap_eq_linearMinimizer
          (grad := grad) (maximizer := maximizer)
          (linearMinimizer := linearMinimizer)
          (linearMinimizer_mem := linearMinimizer_mem)
          (linearMinimizer_is_argmin := linearMinimizer_is_argmin)
          (hmax := hmax) (eval (process ω)))
    calc
      ‖wolfeGap grad maximizer (eval (process ω))‖ =
          |⟪grad (eval (process ω)), eval (process ω) - y⟫_ℝ| := by
        rw [hgap_eq]
        simp [Real.norm_eq_abs]
      _ ≤ ‖grad (eval (process ω))‖ * ‖eval (process ω) - y‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ G * D := by
        exact mul_le_mul (hgrad_bound ω) (by simpa [y] using hdiam ω)
          (norm_nonneg _) hG_nonneg
  exact integrable_of_measurable_bounded_real hmeas hbound

end SOptLib.ConditionalGradient

namespace SOptLib

-- Generalization plan (G0):
-- G0.1 naming: lowerModel_le_compositeObjective_of_curvature_lower
--   (orig was: lPsi_le_Psi); the name states the optimization model comparison
--   rather than the paper-local `lPsi`/`Psi` notation.
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the named lower model
--     uses subtraction and the real inner product, with no completeness,
--     finite-dimensionality, topology, or measurability.
--   measure: none; this is a deterministic pointwise model comparison.
--   convexity: none; the proof consumes only the pointwise curvature-lower
--     inequality already produced by smoothness/strong-convexity assumptions.
-- G0.3 reusability — could instantiate:
--   1. accelerated stochastic gradient descent lower-model summation at the
--      selected optimizer.
--   2. stochastic composite mirror/proximal-gradient descent, replacing a
--      base-point first-order lower model by the composite objective value.
-- G0.4 search trace:
--   queries: ["linearized lower model composite objective",
--     "curvature lower linearization plus convex term"]
--   top hits: ["SOptLib.compositeLinearizedModel",
--     "SOptLib.compositeLinearizedModel_def", "SOptLib.compositeObjective",
--     "SOptLib.compositeObjectiveAmbient_of_mem",
--     "SOptLib.prox_segment_majorized_lower_bound"]
--   coverage: partial — the hits name the linearized model and composite
--     objective separately, or prove prox/segment bounds, but none turns the
--     pointwise curvature-lower inequality into the lower-model objective bound.
-- G0.4 not-a-thin-wrapper rationale: packages the reusable invariant that a
--   curvature lower model for the smooth term survives adding the same simple
--   term and becomes a composite objective lower bound.
-- G0.5 structural-content rationale: the theorem links the named
--   `compositeLinearizedModel` and `compositeObjective` APIs through the exact
--   pointwise curvature hypothesis future algorithms already derive.
-- G0.5b name-body alignment: the name promises a lower-model-to-composite
--   objective inequality from a curvature lower bound, and the theorem proves
--   exactly that property.
-- G0.5c thin-wrapper self-detect: clean — body is not a direct single-call
--   alias; it unfolds two named optimization objects and performs the ordered
--   real algebra connecting them.
-- G0.5d minimal-hypothesis check: all already minimal; the only mathematical
--   hypothesis is pointwise at the two model endpoints.

/-- A curvature lower bound makes the composite linearized model a lower bound
for the composite objective.

If the regularized curvature term at base point `y` is bounded by the smooth
objective residual from `y` to `x`, then adding the same simple term `h x`
turns the composite first-order model into a lower bound on `f x + h x`.

Layer: Layer0 | Gap: Level 0 (composite lower-model objective comparison)
Proof: unfold the named composite linearized model and composite objective,
  then rearrange the supplied pointwise curvature lower inequality by ordered
  real arithmetic.
Source: convex optimization first-order lower models and Mathlib ordered real
  arithmetic for inner-product expressions
Used in: accelerated stochastic gradient descent lower-model summation and
  stochastic composite mirror/proximal-gradient objective comparison
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem lowerModel_le_compositeObjective_of_curvature_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f h : E → ℝ) (gradF : E → E) (mu : ℝ) (V : E → E → ℝ)
    (y x : E)
    (hcurv :
      mu * V y x ≤ f x - f y - ⟪gradF y, x - y⟫_ℝ) :
    f y + ⟪gradF y, x - y⟫_ℝ + h x + mu * V y x ≤
      compositeObjective f h x := by
  unfold compositeObjective
  linarith

-- Generalization plan (G0):
-- G0.1 naming: composite_upper_model_at_convex_average
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses inner
--      products, norms, affine combinations, and no finite-dimensional facts.
--   measure: none; this is a deterministic one-step objective-model estimate.
--   convexity: Mathlib `ConvexOn ℝ X h`, which also supplies carrier convexity.
-- G0.3 reusability — could instantiate:
--   1. accelerated composite stochastic gradient, upper-model step before the
--      prox/Bregman descent inequality.
--   2. proximal stochastic gradient and variance-reduced mirror descent,
--      composite-objective model assembly after a smooth upper bound and
--      convex nonsmooth averaging.
-- G0.4 search trace:
--   queries: ["composite upper model convex average",
--     "convex support smooth upper bound composite objective"]
--   top hits: ["Convex.carrier_smooth_quadratic_upper_bound",
--     "smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex",
--     "convexOn_weighted_average_le_weighted_sum",
--     "ConvexOn", "ConvexOn.le_on_segment'"]
--   coverage: partial — smooth upper-bound hits provide only the `f` curvature
--     estimate, and Jensen hits provide only convex averaging; none combines
--     curvature, support, and nonsmooth convexity into a composite objective
--     model at an accelerated average.
-- G0.4 not-a-thin-wrapper rationale: packages the pointwise curvature model,
--   supporting-hyperplane inequality, convex nonsmooth Jensen step, and inner
--   product affine expansion into the reusable composite upper-model estimate.
-- G0.5 structural-content rationale: the theorem exposes the composite
--   objective estimate over abstract objectives and a convex carrier, rather
--   than forwarding through an algorithm setup record.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step algebraic and
--   convexity assembly beyond one Mathlib/SOptLib call.
-- G0.5d minimal-hypothesis check: curvature and support are pointwise at the
--   points used; `ConvexOn ℝ X h` is retained as the canonical hypothesis for
--   the nonsmooth composite term and carrier convexity.

/-- A curvature upper model and a support inequality give a composite upper
model at a convex average.

If `h` is convex on the feasible carrier, `f` has a pointwise upper model from
`z` to the averaged point, and the same linear model supports `f` at the
previous average point, then the composite objective `f + h` at the convex
average is bounded by the standard accelerated composite model.

Layer: Layer0 | Gap: Level 1 (composite objective upper model at convex average)
Proof: use convexity to keep the averaged point feasible and bound `h`; expand
  the affine inner product, scale the support inequality by `1 - alpha`, and
  collect the scalar inequalities.
Source: Mathlib convex analysis, Hilbert-space inner-product algebra, and
  SOptLib composite objective notation
Used in: accelerated composite stochastic gradient one-step upper-model
  recursion before the prox/Bregman descent inequality
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/key_lemmas/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem composite_upper_model_at_convex_average
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h : E → ℝ) (gradF : E → E) (L M alpha : ℝ)
    {xBarPrev xNext z : E}
    (hhconv : ConvexOn ℝ X h)
    (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hxBarPrev : xBarPrev ∈ X)
    (hxNext : xNext ∈ X)
    (hcurv :
      f ((1 - alpha) • xBarPrev + alpha • xNext) ≤
        f z + ⟪gradF z, ((1 - alpha) • xBarPrev + alpha • xNext) - z⟫_ℝ +
          (L / 2) *
            ‖((1 - alpha) • xBarPrev + alpha • xNext) - z‖ ^ 2 +
          M * ‖((1 - alpha) • xBarPrev + alpha • xNext) - z‖)
    (hsupport :
      f z + ⟪gradF z, xBarPrev - z⟫_ℝ ≤ f xBarPrev) :
    compositeObjective f h
        ((1 - alpha) • xBarPrev + alpha • xNext) ≤
      (1 - alpha) * compositeObjective f h xBarPrev +
        alpha * (f z + ⟪gradF z, xNext - z⟫_ℝ + h xNext) +
        (L / 2) *
          ‖((1 - alpha) • xBarPrev + alpha • xNext) - z‖ ^ 2 +
        M * ‖((1 - alpha) • xBarPrev + alpha • xNext) - z‖ := by
  let y : E := (1 - alpha) • xBarPrev + alpha • xNext
  rcases Set.mem_Icc.mp halpha with ⟨ha0, ha1⟩
  have h1ma : 0 ≤ 1 - alpha := sub_nonneg.mpr ha1
  have hsum : (1 - alpha) + alpha = 1 := by ring
  have hy : y ∈ X := by
    simpa [y] using hhconv.1 hxBarPrev hxNext h1ma ha0 hsum
  have hfcurv :
      f y ≤ f z + ⟪gradF z, y - z⟫_ℝ +
        (L / 2) * ‖y - z‖ ^ 2 + M * ‖y - z‖ := by
    simpa [y] using hcurv
  have hh :
      h y ≤ (1 - alpha) * h xBarPrev + alpha * h xNext := by
    have hconv := hhconv.2 hxBarPrev hxNext h1ma ha0 hsum
    simpa [y, smul_eq_mul] using hconv
  have hinner :
      ⟪gradF z, y - z⟫_ℝ =
        (1 - alpha) * ⟪gradF z, xBarPrev - z⟫_ℝ +
          alpha * ⟪gradF z, xNext - z⟫_ℝ := by
    simp [y, inner_add_right, inner_smul_right, sub_eq_add_neg]
    ring
  have hsupport_scaled :
      (1 - alpha) * (f z + ⟪gradF z, xBarPrev - z⟫_ℝ) ≤
        (1 - alpha) * f xBarPrev := by
    exact mul_le_mul_of_nonneg_left hsupport h1ma
  unfold compositeObjective
  change f y + h y ≤
      (1 - alpha) * (f xBarPrev + h xBarPrev) +
        alpha * (f z + ⟪gradF z, xNext - z⟫_ℝ + h xNext) +
        (L / 2) * ‖y - z‖ ^ 2 + M * ‖y - z‖
  rw [hinner] at hfcurv
  nlinarith

end SOptLib

open scoped BigOperators

/-- A finite average of one-sided lower-bounded components plus a positive
quadratic regularizer has a coercive lower tail.

Each component is bounded below at `x` by its base value at `x0`, a linear
norm term, and a negative quadratic error.  Adding a positive centered
quadratic shift to the finite average eventually dominates any real target
outside large balls centered at `z`.

Layer: Layer0 | Gap: Level 1 (finite-average quadratic lower-tail coercivity)
Proof: use the triangle inequality to transfer each component lower model from
  the base point to the regularization center, average the component
  inequalities, and reduce the resulting bound to a scalar positive-leading
  quadratic tail radius.
Source: Mathlib finite sums, normed-group inequalities, and ordered real
  quadratic tail arithmetic
Used in: randomized accelerated proximal-point exact finite-sum proximal
  subproblem compact truncation
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem finite_average_quadratic_regularized_coercive_lower_tail
    {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E]
    {X : Set E} (x0 z : E) (μ : ℝ)
    (f : ι → {x : E // x ∈ X} → ℝ) (grad0 : ι → E) (F : E → ℝ)
    (hx0 : x0 ∈ X) (hμ : 0 < μ)
    (hcomp_lower : ∀ i : ι, ∀ x : E, ∀ hx : x ∈ X,
      f i ⟨x0, hx0⟩ - ‖grad0 i‖ * ‖x - x0‖ -
          (μ / 2) * ‖x - x0‖ ^ 2 ≤ f i ⟨x, hx⟩)
    (hF_lower : ∀ x : E, ∀ hx : x ∈ X,
      (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i : ι => f i ⟨x, hx⟩) +
          μ * ‖x - z‖ ^ 2 + (μ / 2) * ‖x - z‖ ^ 2 ≤ F x) :
    ∀ B : ℝ, ∃ R : ℝ, ‖x0 - z‖ ≤ R ∧
      ∀ x : E, x ∈ X → R ≤ ‖x - z‖ → B ≤ F x := by
  classical
  intro B
  let xBase : {x : E // x ∈ X} := ⟨x0, hx0⟩
  let G : ℝ := (Fintype.card ι : ℝ)⁻¹ *
    Finset.sum Finset.univ (fun i : ι => ‖grad0 i‖)
  let cdist : ℝ := ‖x0 - z‖
  have hlower : ∃ b c : ℝ, ∀ x : E, x ∈ X →
      μ * ‖x - z‖ ^ 2 - b * ‖x - z‖ + c ≤ F x := by
    refine ⟨G + μ * cdist,
      (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => f i xBase) -
        G * cdist - (μ / 2) * cdist ^ 2, ?_⟩
    intro x hx
    have hdist : ‖x - x0‖ ≤ ‖x - z‖ + cdist := by
      have h := norm_add_le (x - z) (z - x0)
      have hdecomp : x - x0 = (x - z) + (z - x0) := by abel
      dsimp [cdist]
      rwa [← hdecomp, norm_sub_rev z x0] at h
    have hdist_sq : ‖x - x0‖ ^ 2 ≤ (‖x - z‖ + cdist) ^ 2 := by
      have habs : |‖x - x0‖| ≤ |‖x - z‖ + cdist| := by
        rw [abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact hdist
      exact sq_le_sq.mpr habs
    have hcomp_tail : ∀ i : ι,
        f i xBase - ‖grad0 i‖ * (‖x - z‖ + cdist) -
            (μ / 2) * (‖x - z‖ + cdist) ^ 2 ≤ f i ⟨x, hx⟩ := by
      intro i
      have hgnonneg : 0 ≤ ‖grad0 i‖ := norm_nonneg _
      have hmu_half_nonneg : 0 ≤ μ / 2 := le_of_lt (div_pos hμ two_pos)
      have hbase := hcomp_lower i x hx
      nlinarith
    let r : ℝ := ‖x - z‖
    have hcard_nat : 0 < Fintype.card ι := Fintype.card_pos
    have hcard_real_pos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast hcard_nat
    have hcard_real_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_real_pos
    have hinv_nonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
      inv_nonneg.mpr (le_of_lt hcard_real_pos)
    have hsum_tail :
        Finset.sum Finset.univ
            (fun i : ι =>
              f i xBase - ‖grad0 i‖ * (r + cdist) -
                (μ / 2) * (r + cdist) ^ 2) ≤
          Finset.sum Finset.univ (fun i : ι => f i ⟨x, hx⟩) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      simpa [r] using hcomp_tail i
    have hscaled_tail :
        (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i : ι =>
                f i xBase - ‖grad0 i‖ * (r + cdist) -
                  (μ / 2) * (r + cdist) ^ 2) ≤
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i : ι => f i ⟨x, hx⟩) :=
      mul_le_mul_of_nonneg_left hsum_tail hinv_nonneg
    have htail_norm :
        (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i : ι =>
                f i xBase - ‖grad0 i‖ * (r + cdist) -
                  (μ / 2) * (r + cdist) ^ 2) =
          (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ
              (fun i : ι => f i xBase) -
            G * (r + cdist) - (μ / 2) * (r + cdist) ^ 2 := by
      have hsplit :
          Finset.sum Finset.univ
              (fun i : ι =>
                f i xBase - ‖grad0 i‖ * (r + cdist) -
                  (μ / 2) * (r + cdist) ^ 2) =
            Finset.sum Finset.univ (fun i : ι => f i xBase) -
              Finset.sum Finset.univ (fun i : ι => ‖grad0 i‖) * (r + cdist) -
              (Fintype.card ι : ℝ) * ((μ / 2) * (r + cdist) ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_mul,
          Finset.sum_const, nsmul_eq_mul]
        simp
      rw [hsplit]
      rw [mul_sub, mul_sub]
      dsimp [G]
      rw [← mul_assoc (Fintype.card ι : ℝ)⁻¹ (Fintype.card ι)
        ((μ / 2) * (r + cdist) ^ 2)]
      rw [inv_mul_cancel₀ hcard_real_ne, one_mul]
      ring
    have havg_tail :
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ
              (fun i : ι => f i xBase) -
            G * (r + cdist) - (μ / 2) * (r + cdist) ^ 2 ≤
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i : ι => f i ⟨x, hx⟩) := by
      rw [← htail_norm]
      exact hscaled_tail
    have hF_tail := hF_lower x hx
    calc
      μ * ‖x - z‖ ^ 2 - (G + μ * cdist) * ‖x - z‖ +
            ((Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ (fun i : ι => f i xBase) -
              G * cdist - μ / 2 * cdist ^ 2)
          =
            ((Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ (fun i : ι => f i xBase) -
              G * (r + cdist) - (μ / 2) * (r + cdist) ^ 2) +
              μ * r ^ 2 + (μ / 2) * r ^ 2 := by
        dsimp [r]
        ring
      _ ≤
            (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ (fun i : ι => f i ⟨x, hx⟩) +
              μ * r ^ 2 + (μ / 2) * r ^ 2 := by
        nlinarith
      _ ≤ F x := by
        simpa [r] using hF_tail
  obtain ⟨b, c, hlower_tail⟩ := hlower
  obtain ⟨R0, _hR0_nonneg, hR0_tail⟩ :=
    exists_nonneg_forall_le_quadratic_sub_linear_of_pos (a := μ) hμ b c B
  let R : ℝ := max R0 ‖x0 - z‖
  refine ⟨R, ?_, ?_⟩
  · dsimp [R]
    exact le_max_right _ _
  · intro x hx hfar
    have hR0_le_R : R0 ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    have hR0_le_norm : R0 ≤ ‖x - z‖ := le_trans hR0_le_R hfar
    exact le_trans (hR0_tail ‖x - z‖ hR0_le_norm) (hlower_tail x hx)

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Layer0/linearModel_eq_compare_add_estimator_inner_add_residual_inner.lean
/-!
-- Generalization plan (G0):
-- concept/name: linearModel_eq_compare_add_estimator_inner_add_residual_inner
--   exposes the affine linear-model decomposition obtained by replacing a
--   target gradient with an estimator plus residual; orig was
--   linearModel_x_eq_linearModel_compare_add_batch_delta, renamed away from
--   mini-batch and Algorithm 7.8 state fields.
-- generality used: arbitrary real inner-product normed additive group `E`, a
--   scalar objective value function `f : E → ℝ`, a target vector, an estimator
--   vector, a model base point, a chosen point, and a comparison point; no
--   measure, independence, integrability, convexity, smoothness, compactness,
--   filtration, or oracle hypotheses are used.
-- portable call pattern: stochastic conditional-gradient, stochastic gradient,
--   mirror-descent, and proximal-gradient descent proofs can rewrite an exact
--   affine model at a selected point into the comparison-point model plus the
--   estimator projection term and residual correction while `f`, `target`,
--   `g`, and the three points vary.
-- counterargument checked: not paper-local traceability because the statement
--   is independent of Lan notation and mini-batch construction; not a pure
--   caller-side expression because it packages a recurring estimator/residual
--   split at the exact comparison-model boundary used before projection or
--   descent inequalities.
-- coverage search: searched catalog/symbols for `linear model estimator
--   residual inner`, `inner sub add residual estimator target`, and LeanSearch
--   for inner-product affine model estimator residual decomposition. Hits
--   covered conditional-gradient max-linear models, stochastic residual
--   processes, and orthogonal-projection residual lemmas, but none states this
--   affine model decomposition.
-- minimal hypotheses: all already minimal for the chosen Hilbert-space
--   formulation; the proof uses only real inner-product bilinearity and
--   additive-group algebra.
-/

open scoped InnerProductSpace

/-- An affine linear model splits through an estimator and its residual.

For the model `y ↦ f z + ⟪target, y - z⟫`, the value at `xi` equals the value
at a comparison point `x`, plus the estimator term `⟪g, xi - x⟫` and the
residual correction `⟪g - target, x - xi⟫`.

Layer: Layer0 | Gap: Level 0 (estimator residual affine-model decomposition)
Proof: expand the residual `g - target`, distribute inner products over sums
  and differences, and normalize the resulting additive expression.
Source: Mathlib real inner-product bilinearity and additive-group algebra
Used in: stochastic first-order descent proofs replacing an exact target
  gradient in an affine model by a gradient estimator plus residual correction
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem linearModel_eq_compare_add_estimator_inner_add_residual_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (target g z xi x : E) :
    f z + ⟪target, xi - z⟫_ℝ =
      f z + ⟪target, x - z⟫_ℝ +
        ⟪g, xi - x⟫_ℝ +
          ⟪g - target, x - xi⟫_ℝ := by
  simp [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, sub_eq_add_neg]
  ring

theorem linear_model_eq_compare_add_estimator_inner_add_residual_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (target g z xi x : E) :
    f z + ⟪target, xi - z⟫_ℝ =
      f z + ⟪target, x - z⟫_ℝ +
        ⟪g, xi - x⟫_ℝ +
          ⟪g - target, x - xi⟫_ℝ :=
  linearModel_eq_compare_add_estimator_inner_add_residual_inner f target g z xi x

-- Batch 2 promoted from Staging/finiteAverageGradient_lipschitzOn_of_component_lipschitz.lean
open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finiteAverageGradient_lipschitzOn_of_component_lipschitz
--   exposes the standard finite-sum smoothness transfer from component
--   Lipschitz gradients to the normalized full finite-average gradient; orig
--   was fullGradient_lipschitz_on_X, renamed away from setup-field wording.
-- generality used: arbitrary finite index type `ι`, normed real vector-space
--   target `E`, feasible set `X`, component-gradient family `gradF`,
--   component Lipschitz constants `Lcomp`, and average constant `L`; no
--   measure, independence, integrability, convexity, differentiability,
--   inner-product, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum SGD, variance-reduced gradient estimators,
--   proximal finite-sum methods, and conditional-gradient sliding proofs can
--   vary the component gradients, feasible set, and smoothness constants while
--   using the same conclusion that the deterministic finite-average gradient
--   is Lipschitz on feasible point pairs.
-- counterargument checked: not paper-local traceability because the statement
--   is exactly the reusable finite-average Lipschitz transfer used before
--   applying smooth descent lemmas; not a caller-side expression because it
--   packages triangle inequality, finite-sum monotonicity, scalar
--   normalization, and the average-constant identity over the named
--   `finiteUniformAverage`. The inner formula is already named, so no new def
--   is warranted.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `finiteUniformAverage`, `component Lipschitz`, `average gradient
--   Lipschitz`, and `finiteAverageGradient_lipschitzOn`; relevant hits were
--   the existing `finiteUniformAverage` def and finite-average gradient
--   calculus, but no theorem transferring component Lipschitz constants to
--   the finite-average gradient. LeanSearch for "finite average of Lipschitz
--   maps is Lipschitz with average Lipschitz constants" returned only generic
--   Lipschitz APIs, not this finite-sum normalized-gradient statement.
-- minimal hypotheses: pointwise Lipschitz hypotheses only at feasible pairs
--   are used; no nonempty or positive-cardinality assumption is needed because
--   the inverse cardinal scalar is nonnegative even for an empty finite type.

/-- Componentwise Lipschitz gradients make the finite-average gradient Lipschitz.

If every component gradient `gradF i` is Lipschitz on feasible pairs with
constant `Lcomp i`, and `L` is the normalized average of those constants, then
the finite-average gradient is `L`-Lipschitz on the same feasible pairs.

Layer: Layer0 | Gap: Level 1 (finite-average component Lipschitz transfer)
Proof: unfold the finite-average gradient, use the triangle inequality for the
  finite sum, bound each component difference, and rewrite the normalized sum
  of component constants as `L`.
Source: Mathlib finite sums, real normed-space scalar norms, and ordered
  additive monoid inequalities
Used in: finite-sum stochastic nonconvex conditional-gradient sliding smooth
  descent for the deterministic full finite-sum gradient
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem finiteAverageGradient_lipschitzOn_of_component_lipschitz
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (gradF : ι → E → E) (Lcomp : ι → ℝ) (L : ℝ)
    (hL_eq_average : L = (Fintype.card ι : ℝ)⁻¹ *
      Finset.sum Finset.univ (fun i : ι => Lcomp i))
    (hcomponent_lipschitz :
      ∀ i : ι, ∀ x y : E, x ∈ X → y ∈ X →
        ‖gradF i x - gradF i y‖ ≤ Lcomp i * ‖x - y‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    ‖finiteUniformAverage (fun i : ι => gradF i x) -
        finiteUniformAverage (fun i : ι => gradF i y)‖ ≤
      L * ‖x - y‖ := by
  classical
  have hcard_nonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card ι))
  have hdiff :
      finiteUniformAverage (fun i : ι => gradF i x) -
          finiteUniformAverage (fun i : ι => gradF i y) =
        (Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i : ι => gradF i x - gradF i y) := by
    simp [finiteUniformAverage, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  calc
    ‖finiteUniformAverage (fun i : ι => gradF i x) -
        finiteUniformAverage (fun i : ι => gradF i y)‖
        =
      (Fintype.card ι : ℝ)⁻¹ *
        ‖Finset.sum Finset.univ (fun i : ι => gradF i x - gradF i y)‖ := by
      rw [hdiff, norm_smul, Real.norm_of_nonneg hcard_nonneg]
    _ ≤
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι => ‖gradF i x - gradF i y‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hcard_nonneg
    _ ≤
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι => Lcomp i * ‖x - y‖) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _hi => hcomponent_lipschitz i x y hx hy))
        hcard_nonneg
    _ = L * ‖x - y‖ := by
      rw [hL_eq_average]
      rw [← Finset.sum_mul]
      ring

end SOptLib


-- Batch 2 promoted from Staging/finiteAverageObjective_smooth_quadratic_upper_bound_of_component_lipschitz.lean
open scoped BigOperators
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
--   exposes the finite-sum descent lemma: component gradient calculus and
--   component Lipschitz constants imply the smooth quadratic upper model for
--   the normalized finite-average objective; orig was
--   finiteSumObjective_smooth_quadratic_upper_bound.
-- generality used: arbitrary finite index type `ι`, Hilbert decision space
--   `E`, convex feasible set `X`, component objectives `F`, component
--   gradients `gradF`, component constants `Lcomp`, and average constant `L`;
--   no measure, independence, integrability, oracle, filtration, compactness,
--   or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum SGD, variance-reduced mirror descent,
--   proximal finite-sum, and conditional-gradient sliding proofs can vary the
--   components, gradients, feasible carrier, and component smoothness constants
--   while reusing the same finite-average smooth descent conclusion.
-- counterargument checked: not paper-local traceability because the theorem is
--   the standard deterministic finite-sum smoothness transfer used before
--   stochastic estimator-error absorption; not a duplicate of the generic
--   smooth descent lemma because this statement composes finite-average
--   gradient calculus and componentwise Lipschitz transfer into the finite-sum
--   call shape. The objective and gradient averages are expressed directly by
--   `finiteUniformAverage`, so no extra finite-average wrapper is warranted.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `finiteUniformAverage`, `smooth quadratic upper bound`, `component
--   Lipschitz`, and `finiteUniformAverage`; relevant hits were
--   `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`,
--   `finiteAverageObjective_hasGradientAt`, and finite-uniform average APIs,
--   all partial.
--   LeanSearch for "finite average objective smooth quadratic upper bound
--   component Lipschitz gradients" returned only generic gradient/Lipschitz
--   APIs, not this normalized finite-sum descent statement.
-- minimal hypotheses: pointwise component `HasGradientAt` and component
--   Lipschitz hypotheses only at feasible points are used; compactness,
--   closedness, component positivity, schedules, sampling laws, and algorithm
--   update rules are unnecessary.

/-- Component smoothness gives the smooth quadratic upper model for a finite-average
objective.

If each component objective has the named component gradient on a convex
feasible set and those component gradients are Lipschitz with constants whose
normalized average is `L`, then the finite-average objective satisfies the
usual `L`-smooth descent upper bound.

Layer: Layer0 | Gap: Level 1 (finite-average smooth descent from component smoothness)
Proof: use finite-average gradient calculus for the normalized objective,
  transfer component Lipschitz bounds to the finite-average gradient, and apply
  the generic smooth quadratic upper-bound theorem on a convex feasible segment.
Source: SOptLib finite-average objective calculus, finite-sum Lipschitz
  transfer, and Mathlib Hilbert-space smooth descent APIs
Used in: finite-sum stochastic nonconvex conditional-gradient sliding smooth
  objective decrease before estimator-error and conditional-gradient gap
  absorption
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (F : ι → E → ℝ) (gradF : ι → E → E)
    (Lcomp : ι → ℝ) (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hL_eq_average : L = (Fintype.card ι : ℝ)⁻¹ *
      Finset.sum Finset.univ (fun i : ι => Lcomp i))
    (hcomponent_hasGradientAt :
      ∀ i : ι, ∀ z : E, z ∈ X → HasGradientAt (F i) (gradF i z) z)
    (hcomponent_lipschitz :
      ∀ i : ι, ∀ z w : E, z ∈ X → w ∈ X →
        ‖gradF i z - gradF i w‖ ≤ Lcomp i * ‖z - w‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    finiteUniformAverage F y ≤
      finiteUniformAverage F x + ⟪finiteUniformAverage gradF x, y - x⟫_ℝ +
        (L / 2) * ‖y - x‖ ^ 2 := by
  exact
    smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
      X (finiteUniformAverage F) (finiteUniformAverage gradF) L
      hX_convex
      (fun z hz => by
        rw [show finiteUniformAverage F =
            (fun u : E => (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ (fun i : ι => F i u)) by
          funext u
          simp [finiteUniformAverage]]
        simpa [finiteUniformAverage] using
          finiteAverageObjective_hasGradientAt F gradF z
            (fun i => hcomponent_hasGradientAt i z hz))
      (fun z hz w hw => by
        have hcard_nonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
          inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card ι))
        have hdiff :
            finiteUniformAverage gradF z - finiteUniformAverage gradF w =
              (Fintype.card ι : ℝ)⁻¹ •
                Finset.sum Finset.univ (fun i : ι => gradF i z - gradF i w) := by
          simp [finiteUniformAverage, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
        calc
          ‖finiteUniformAverage gradF z - finiteUniformAverage gradF w‖
              =
            (Fintype.card ι : ℝ)⁻¹ *
              ‖Finset.sum Finset.univ (fun i : ι => gradF i z - gradF i w)‖ := by
            rw [hdiff, norm_smul, Real.norm_of_nonneg hcard_nonneg]
          _ ≤
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i : ι => ‖gradF i z - gradF i w‖) := by
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hcard_nonneg
          _ ≤
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i : ι => Lcomp i * ‖z - w‖) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun i _hi => hcomponent_lipschitz i z w hz hw))
              hcard_nonneg
          _ = L * ‖z - w‖ := by
            rw [hL_eq_average]
            rw [← Finset.sum_mul]
            ring)
      hx hy

end SOptLib


-- Batch 6 promoted from Staging/finite_importance_weighted_gradient_gap_le_linearization_gap_of_component_smoothness.lean
noncomputable section

open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite importance-weighted gradient-gap bound by the
--   finite-average linearization gap; orig was
--   eq535_carrier_finite_sum_gradient_gap_relation, renamed away from equation
--   numbering, carrier implementation details, and theorem-local constants.
-- generality used: arbitrary finite component index type, Hilbert decision
--   space, component objectives, selected component gradients, positive
--   component smoothness constants, positive sampling weights, a scalar
--   finite-average normalizer, and pointwise component smoothness-gap
--   hypotheses; no measure, filtration, oracle, convexity, completeness, or
--   finite-dimensional assumptions are used by this summation step.
-- portable call pattern: nonuniform SVRG/SAGA/SARAH/SPIDER and
--   variance-reduced accelerated finite-sum proofs can vary component
--   objectives, component gradients, sampling probabilities, and the average
--   smoothness scale while reusing the same reduction from an
--   inverse-probability quadratic gradient gap to a finite-average
--   linearization gap.
-- counterargument checked: not paper-local traceability because this composes
--   standard component co-coercivity with smoothness-proportional importance
--   weights; not a pure wrapper around `importance_weighted_gradient_gap_quadratic`
--   because the proof performs the component scaling, summation, and
--   finite-average linearization rewrite. No inner def is extracted: the only
--   recurring formulas are already named by `importance_weighted_gradient_gap_quadratic`
--   and `finiteUniformAverage`.
-- coverage search: searched CATALOG.md/SOptLib/Staging for `importance weighted
--   gradient gap quadratic`, `linearization gap`, `co-coercive smoothness gap`,
--   and `finiteUniformAverage component smoothness`; relevant partial hits were
--   `importance_weighted_gradient_gap_quadratic`,
--   `projectedWithinGradient_smoothness_gap_of_convex_lipschitz`, and
--   `finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitzWithin`.
--   None states this finite-sum importance-weighted summation and
--   linearization-gap composition.
-- minimal hypotheses: component smoothness enters only through the pointwise
--   lower-gap inequality; the normalizer equality to `Fintype.card` is used
--   exactly to express the right side as `finiteUniformAverage`.

/-- Component smoothness gaps control the finite importance-weighted quadratic
gradient gap by the finite-average linearization gap.

If each component gradient gap is bounded by its component first-order
linearization gap, and the sampling weights satisfy `L_i / q_i = n * Lbar`
with `n` the finite component count, then the normalized
inverse-probability quadratic gradient gap is bounded by `2 * Lbar` times the
linearization gap of the finite uniform average.

Layer: Layer0 | Gap: Level 1 (finite-sum importance-weighted gradient-gap summation)
Proof: scale the component smoothness-gap inequality by the positive
  inverse-probability coefficient, use the smoothness-proportional ratio to
  replace every component coefficient by `2 * Lbar`, then sum and unfold the
  finite uniform averages.
Source: finite-sum smooth convex optimization co-coercivity, importance
  sampling algebra, and Mathlib finite-sum/inner-product APIs
Used in: finite-sum variance-reduced accelerated-gradient residual
  second-moment reduction before converting a quadratic gradient gap into a
  finite-average objective gap
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finite_importance_weighted_gradient_gap_le_linearization_gap_of_component_smoothness
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ι → E → ℝ) (gradF : ι → E → E)
    (q Lcomp : ι → ℝ) (Lbar n : ℝ) {x z : E}
    (hn_pos : 0 < n)
    (hn_card : n = (Fintype.card ι : ℝ))
    (hq_pos : ∀ i : ι, 0 < q i)
    (hLcomp_pos : ∀ i : ι, 0 < Lcomp i)
    (hratio : ∀ i : ι, Lcomp i / q i = n * Lbar)
    (hcomponent_gap :
      ∀ i : ι,
        (1 / (2 * Lcomp i)) * ‖gradF i x - gradF i z‖ ^ 2 ≤
          F i x - F i z - ⟪gradF i z, x - z⟫_ℝ) :
    SOptLib.importance_weighted_gradient_gap_quadratic q n gradF x z ≤
      2 * Lbar *
        (SOptLib.finiteUniformAverage (fun i : ι => F i x) -
          SOptLib.finiteUniformAverage (fun i : ι => F i z) -
          ⟪SOptLib.finiteUniformAverage (fun i : ι => gradF i z), x - z⟫_ℝ) := by
  classical
  subst n
  let gap : ι → ℝ := fun i =>
    F i x - F i z - ⟪gradF i z, x - z⟫_ℝ
  have hterm :
      ∀ i : ι,
        (1 / ((Fintype.card ι : ℝ) * q i)) *
            ‖gradF i x - gradF i z‖ ^ 2 ≤
          2 * Lbar * gap i := by
    intro i
    have hgap_i := hcomponent_gap i
    let N : ℝ := ‖gradF i x - gradF i z‖ ^ 2
    let G : ℝ := gap i
    have htwoL_pos : 0 < 2 * Lcomp i := by
      exact mul_pos (by norm_num) (hLcomp_pos i)
    have hN_le : N ≤ 2 * Lcomp i * G := by
      have hmul := mul_le_mul_of_nonneg_left hgap_i (le_of_lt htwoL_pos)
      have hleft :
          N = (2 * Lcomp i) * ((1 / (2 * Lcomp i)) * N) := by
        field_simp [ne_of_gt htwoL_pos]
        field_simp [ne_of_gt (hLcomp_pos i)]
      calc
        N = (2 * Lcomp i) * ((1 / (2 * Lcomp i)) * N) := hleft
        _ ≤ 2 * Lcomp i * G := by
          simpa [N, G, gap, mul_assoc] using hmul
    have hq_i_pos : 0 < q i := hq_pos i
    have hcoeff_pos :
        0 < 1 / ((Fintype.card ι : ℝ) * q i) := by
      exact one_div_pos.mpr (mul_pos hn_pos hq_i_pos)
    have hscaled :=
      mul_le_mul_of_nonneg_left hN_le (le_of_lt hcoeff_pos)
    have hcoeff :
        (1 / ((Fintype.card ι : ℝ) * q i)) *
            (2 * Lcomp i * G) =
          2 * Lbar * G := by
      have hratio_i := hratio i
      field_simp [ne_of_gt hn_pos, ne_of_gt hq_i_pos] at hratio_i ⊢
      ring_nf at hratio_i ⊢
      rw [hratio_i]
    calc
      (1 / ((Fintype.card ι : ℝ) * q i)) *
          ‖gradF i x - gradF i z‖ ^ 2
          ≤
        (1 / ((Fintype.card ι : ℝ) * q i)) *
          (2 * Lcomp i * G) := by
          simpa [N] using hscaled
      _ = 2 * Lbar * gap i := by
          simpa [G] using hcoeff
  have hsum :
      Finset.univ.sum (fun i : ι =>
          (1 / ((Fintype.card ι : ℝ) * q i)) *
            ‖gradF i x - gradF i z‖ ^ 2) ≤
        Finset.univ.sum (fun i : ι => 2 * Lbar * gap i) :=
    Finset.sum_le_sum (fun i _hi => hterm i)
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hn_pos))
  have hleft :
      ((Fintype.card ι : ℝ)⁻¹ *
        Finset.univ.sum (fun i : ι =>
          (1 / ((Fintype.card ι : ℝ) * q i)) *
            ‖gradF i x - gradF i z‖ ^ 2)) =
      SOptLib.importance_weighted_gradient_gap_quadratic
        q (Fintype.card ι : ℝ) gradF x z := by
    rfl
  have hright :
      ((Fintype.card ι : ℝ)⁻¹ *
        Finset.univ.sum (fun i : ι => 2 * Lbar * gap i)) =
      2 * Lbar *
        (SOptLib.finiteUniformAverage (fun i : ι => F i x) -
          SOptLib.finiteUniformAverage (fun i : ι => F i z) -
          ⟪SOptLib.finiteUniformAverage (fun i : ι => gradF i z), x - z⟫_ℝ) := by
    dsimp [gap]
    rw [inner_smul_left, sum_inner]
    simp only [map_inv₀]
    rw [show ((starRingEnd ℝ) (Fintype.card ι : ℝ))⁻¹ =
        (Fintype.card ι : ℝ)⁻¹ by simp]
    ring_nf
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    repeat rw [← Finset.sum_mul]
    repeat rw [← Finset.mul_sum]
    ring_nf
  rw [hleft, hright] at hscaled
  exact hscaled


-- Batch 6 promoted from Staging/finiteUniformAverage_convexOn.lean
open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finiteUniformAverage_convexOn exposes convexity preservation
--   for the normalized uniform finite average of component objectives; orig was
--   finiteSumObjective_convexOn, renamed away from the VRAGD setup field.
-- generality used: arbitrary finite index type `ι`, real module carrier `E`,
--   feasible set `X`, and component family `F`; no measure, independence,
--   integrability, smoothness, oracle, norm, inner product, topology,
--   completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum SGD, variance-reduced gradient methods,
--   proximal finite-sum methods, and conditional-gradient sliding can vary the
--   index type, carrier, component objectives, and feasible set while reusing
--   the same conclusion that the deterministic uniform finite-average
--   objective is convex on the carrier.
-- counterargument checked: not paper-local traceability because this is the
--   standard deterministic finite-sum convexity transfer used before Jensen or
--   composite-objective convexity steps; not a caller-side expression because
--   it packages the finite component sum and nonnegative normalized scaling
--   over the named `finiteUniformAverage`. No inner def is needed because
--   `finiteUniformAverage` already names the recurring formula.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `finiteUniformAverage`, `average convex`, `ConvexOn sum`, and
--   `convexOn_weighted_average_le_weighted_sum`; relevant hits were
--   `SOptLib.finiteUniformAverage`, smooth finite-average transfer lemmas, and
--   the downstream Jensen value theorem `convexOn_weighted_average_le_weighted_sum`.
--   LeanSearch for "finite sum of convex functions is convex ConvexOn Finset
--   sum smul nonnegative" returned Mathlib ingredients `ConvexOn.add`,
--   `ConvexOn.smul`, and `ConvexOn.map_sum_le`, but no theorem for the named
--   normalized finite-uniform-average objective.
-- minimal hypotheses: explicit `Convex ℝ X` is needed for empty finite index
--   types because component convexity is then vacuous while `ConvexOn` includes
--   carrier convexity; component hypotheses are otherwise pointwise and
--   minimal.

/-- The uniform finite average of convex component objectives is convex.

If `X` is convex and every component objective `F i` is convex on `X`, then the
named normalized finite-uniform average `finiteUniformAverage F` is convex on
the same carrier.

Layer: Layer0 | Gap: Level 0 (finite-average objective convexity)
Proof: sum the component convexity inequalities over the finite index type, then
  multiply the resulting convex sum by the nonnegative inverse-cardinality
  scalar from `finiteUniformAverage`.
Source: Mathlib convex-function finite sums and nonnegative scalar
  multiplication APIs
Used in: variance-reduced accelerated gradient finite-sum objective convexity
  before composite-objective Jensen steps
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finiteUniformAverage_convexOn
    {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E]
    (X : Set E) (F : ι → E → ℝ)
    (hX_convex : Convex ℝ X)
    (hF_convex : ∀ i : ι, ConvexOn ℝ X (F i)) :
    ConvexOn ℝ X (finiteUniformAverage F) := by
  classical
  have hsum :
      ConvexOn ℝ X (fun y : E => Finset.univ.sum (fun i : ι => F i y)) := by
    refine ⟨hX_convex, ?_⟩
    intro u hu v hv a b ha hb hab
    calc
      Finset.univ.sum (fun i : ι => F i (a • u + b • v))
          ≤ Finset.univ.sum (fun i : ι => a • F i u + b • F i v) := by
            exact Finset.sum_le_sum
              (fun i _hi => (hF_convex i).2 hu hv ha hb hab)
      _ = a • Finset.univ.sum (fun i : ι => F i u) +
            b • Finset.univ.sum (fun i : ι => F i v) := by
            rw [Finset.sum_add_distrib]
            simp [Finset.mul_sum]
  rw [finiteUniformAverage_def]
  have hfun :
      (fun y : E =>
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.univ.sum (fun i : ι => F i y)) =
        ((Fintype.card ι : ℝ)⁻¹ • Finset.univ.sum F) := by
    funext y
    simp
  rw [← hfun]
  exact
    ConvexOn.smul
      (show 0 ≤ ((Fintype.card ι : ℝ)⁻¹) by positivity) hsum

-- Batch 7 promoted from Staging/finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitzWithin.lean
-- Generalization plan (G0):
-- concept/name: finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitzWithin
--   exposes the carrier-constrained finite-sum descent lemma: component
--   within-gradient calculus and component Lipschitz constants imply the
--   smooth quadratic upper model for the normalized finite-average objective;
--   orig was finiteSumObjective_smooth_upper_bound_from_component_smooth.
-- generality used: arbitrary finite index type `ι`, Hilbert decision space
--   `E`, convex feasible carrier `X`, component objectives `F`, selected
--   within-gradients `gradF`, component constants `Lcomp`, and average
--   constant `L`; no measure, independence, integrability, oracle,
--   filtration, compactness, closedness, or finite-dimensional hypotheses are
--   used.
-- portable call pattern: carrier-constrained finite-sum SGD,
--   variance-reduced mirror descent, proximal-gradient, mirror-descent, and
--   conditional-gradient proofs can vary components, carrier, within-gradient
--   selectors, and smoothness constants while reusing the same finite-average
--   smooth descent conclusion.
-- counterargument checked: not paper-local traceability because this is the
--   standard deterministic finite-sum smoothness transfer used before
--   stochastic estimator-error or prox-descent absorption. It is not a
--   duplicate of the existing ambient-gradient theorem
--   `finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz`
--   because the component calculus hypothesis is `HasGradientWithinAt` on a
--   carrier rather than global `HasGradientAt`. The objective and gradient
--   averages are already named by `finiteUniformAverage`, so no inner def is
--   warranted.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `finiteUniformAverage`, `smooth quadratic upper bound`, `component
--   Lipschitz`, `HasGradientWithinAt`, and `finiteAverageGradient_lipschitzOn`;
--   relevant hits were `finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz`,
--   `HasGradientWithinAt.fintype_average`,
--   `finiteAverageGradient_lipschitzOn_of_component_lipschitz`, and
--   `Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz`.
--   Coverage is partial: those hits provide the ambient finite-average theorem
--   or the within-gradient ingredients, but not the carrier-constrained
--   finite-average descent statement itself.
-- minimal hypotheses: pointwise component `HasGradientWithinAt` and component
--   Lipschitz hypotheses only at feasible pairs are used; component positivity,
--   nonempty carrier, closedness, schedules, sampling laws, and algorithm
--   update rules are unnecessary.

/-- Component within-smoothness gives the smooth quadratic upper model for a
finite-average objective on a carrier.

If each component objective has the selected within-gradient on a convex
feasible set and those selected gradients are Lipschitz with constants whose
normalized average is `L`, then the finite-average objective satisfies the
usual `L`-smooth descent upper bound between feasible points.

Layer: Layer0 | Gap: Level 1 (carrier finite-average smooth descent from component smoothness)
Proof: use finite-average within-gradient calculus for the normalized
  objective, transfer component Lipschitz bounds to the finite-average
  gradient, and apply the carrier smooth quadratic upper-bound theorem.
Source: SOptLib finite-average within-gradient calculus, finite-sum Lipschitz
  transfer, and Mathlib Hilbert-space smooth descent APIs
Used in: variance-reduced accelerated gradient finite-sum objective decrease on
  the feasible carrier before estimator-error and prox-descent absorption
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitzWithin
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (F : ι → E → ℝ) (gradF : ι → E → E)
    (Lcomp : ι → ℝ) (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hL_eq_average : L = (Fintype.card ι : ℝ)⁻¹ *
      Finset.sum Finset.univ (fun i : ι => Lcomp i))
    (hcomponent_hasGradientWithinAt :
      ∀ i : ι, ∀ z : E, z ∈ X → HasGradientWithinAt (F i) (gradF i z) X z)
    (hcomponent_lipschitz :
      ∀ i : ι, ∀ z w : E, z ∈ X → w ∈ X →
        ‖gradF i z - gradF i w‖ ≤ Lcomp i * ‖z - w‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    finiteUniformAverage F y ≤
      finiteUniformAverage F x + ⟪finiteUniformAverage gradF x, y - x⟫_ℝ +
        (L / 2) * ‖y - x‖ ^ 2 := by
  classical
  have hgrad :
      ∀ z : {u : E // u ∈ X},
        HasGradientWithinAt (finiteUniformAverage F)
          (finiteUniformAverage (fun i : ι => gradF i z.1)) X z.1 := by
    intro z
    have havg :=
      HasGradientWithinAt.fintype_average
        (F := F) (G := gradF) (X := X) (x := z.1)
        (fun i => hcomponent_hasGradientWithinAt i z.1 z.2)
    rw [show finiteUniformAverage F =
        (fun u : E => (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F i u)) by
      funext u
      simp [finiteUniformAverage]]
    simpa [finiteUniformAverage] using havg
  have hlip :
      ∀ a b : {u : E // u ∈ X},
        ‖finiteUniformAverage (fun i : ι => gradF i b.1) -
            finiteUniformAverage (fun i : ι => gradF i a.1)‖ ≤
          L * ‖b.1 - a.1‖ := by
    intro a b
    exact
      finiteAverageGradient_lipschitzOn_of_component_lipschitz
        (X := X) (gradF := gradF) (Lcomp := Lcomp) (L := L)
        hL_eq_average hcomponent_lipschitz b.2 a.2
  have hsmooth :=
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (X := X)
      (f := fun z : {u : E // u ∈ X} => finiteUniformAverage F z.1)
      (F := finiteUniformAverage F)
      (grad := fun z : {u : E // u ∈ X} =>
        finiteUniformAverage (fun i : ι => gradF i z.1))
      (L := L)
      hX_convex
      (by intro z hz; rfl)
      hgrad hlip
      ⟨y, hy⟩ ⟨x, hx⟩
  dsimp at hsmooth
  have hsmooth' :
      finiteUniformAverage F y - finiteUniformAverage F x -
          ⟪finiteUniformAverage gradF x, y - x⟫_ℝ ≤
        (L / 2) * ‖y - x‖ ^ 2 := by
    simpa [finiteUniformAverage] using hsmooth
  nlinarith

-- Batch 7 promoted from Staging/finite_importance_weighted_gradient_gap_le_composite_gap_of_optimum.lean
-- Generalization plan (G0):
-- concept/name: finite importance-weighted component-gradient gap controlled
--   by a composite objective optimum; orig was
--   `lemma512_weighted_component_gradient_gap_bound`, renamed away from theorem
--   numbering and variance-reduced algorithm labels.
-- generality used: arbitrary finite component index type, Hilbert decision
--   space, feasible carrier, component objectives and selected component
--   gradients, positive component smoothness constants, positive sampling
--   weights, a finite-average smoothness scale, a convex simple term, and
--   pointwise component smoothness and composite-minimizer hypotheses; no
--   measure, filtration, oracle, independence, integrability, completeness, or
--   finite-dimensional assumptions are used.
-- portable call pattern: finite-sum composite SVRG/SAGA/SARAH/SPIDER and
--   accelerated variance-reduced proofs instantiate different component
--   objectives, importance weights, smoothness constants, nonsmooth composite
--   term, and reference optimum while reusing the same step from a
--   weighted component-gradient quadratic gap to a composite objective gap.
-- counterargument checked: this is a short composition of two staged Layer0
--   facts, but not paper-local traceability: the final composite-gap boundary is
--   the recurring proof step used after Eq.-style finite-sum co-coercivity and
--   before variance/noise absorption. It is not a new formula wrapper; the
--   recurring formulas are already named by `importance_weighted_gradient_gap_quadratic`,
--   `finiteUniformAverage`, and `compositeObjective`.
-- coverage search: searched CATALOG.md/SOptLib/Staging and local sources for
--   `finite importance weighted gradient gap composite gap`,
--   `linearization gap composite minimizer`, and
--   `importance_weighted_gradient_gap_quadratic finiteUniformAverage compositeObjective`.
--   Relevant partial hits were
--   `finite_importance_weighted_gradient_gap_le_linearization_gap_of_component_smoothness`,
--   `smooth_part_linearization_gap_le_composite_gap_of_minimizer`, and
--   `finite_sum_control_variate_residual_second_moment_le_composite_gap`; none
--   states this finite component-gradient quadratic gap to composite optimum
--   inequality.
-- minimal hypotheses: component smoothness is pointwise through
--   `hcomponent_gap`; optimum information is pointwise through `hmin`; convexity
--   is needed only for the simple term in the minimizer bridge; `hLbar_nonneg`
--   is retained exactly for smooth-model validity and multiplication
--   monotonicity.

/-- Component smoothness and a composite optimum control the finite
importance-weighted component-gradient gap by the composite objective gap.

The theorem composes the finite-sum importance-weighted smoothness summation
with the standard bridge from a smooth-part linearization gap to a composite
objective gap at an optimum.

Layer: Layer0 | Gap: Level 1 (finite-sum importance-weighted gradient gap to composite optimum gap)
Proof: first bound the inverse-probability quadratic gradient gap by the
  finite-average smooth linearization gap using component smoothness and the
  importance-weight ratio. Then use the composite-minimizer bridge and multiply
  by the nonnegative coefficient `2 * Lbar`.
Source: finite-sum smooth composite optimization, importance sampling algebra,
  and Mathlib finite-sum/ordered-real APIs
Used in: finite-sum variance-reduced accelerated-gradient residual
  second-moment reduction before absorbing the stochastic error into a
  composite objective gap
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finite_importance_weighted_gradient_gap_le_composite_gap_of_optimum
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (F : ι → E → ℝ) (gradF : ι → E → E) (h : E → ℝ)
    (q Lcomp : ι → ℝ) (Lbar n : ℝ) {x xStar : E}
    (hn_pos : 0 < n)
    (hn_card : n = (Fintype.card ι : ℝ))
    (hq_pos : ∀ i : ι, 0 < q i)
    (hLcomp_pos : ∀ i : ι, 0 < Lcomp i)
    (hratio : ∀ i : ι, Lcomp i / q i = n * Lbar)
    (hcomponent_gap :
      ∀ i : ι,
        (1 / (2 * Lcomp i)) * ‖gradF i x - gradF i xStar‖ ^ 2 ≤
          F i x - F i xStar - ⟪gradF i xStar, x - xStar⟫_ℝ)
    (hx : x ∈ X) (hxStar : xStar ∈ X)
    (hhconv : ConvexOn ℝ X h)
    (hmin :
      ∀ y, y ∈ X →
        SOptLib.compositeObjective
            (fun u => SOptLib.finiteUniformAverage (fun i : ι => F i u)) h xStar ≤
          SOptLib.compositeObjective
            (fun u => SOptLib.finiteUniformAverage (fun i : ι => F i u)) h y)
    (hLbar_nonneg : 0 ≤ Lbar)
    (hsmooth :
      ∀ y, y ∈ X →
        SOptLib.finiteUniformAverage (fun i : ι => F i y) -
            SOptLib.finiteUniformAverage (fun i : ι => F i xStar) ≤
          ⟪SOptLib.finiteUniformAverage (fun i : ι => gradF i xStar),
              y - xStar⟫_ℝ +
            (Lbar / 2) * ‖y - xStar‖ ^ 2) :
    SOptLib.importance_weighted_gradient_gap_quadratic q n gradF x xStar ≤
      2 * Lbar *
        (SOptLib.compositeObjective
            (fun u => SOptLib.finiteUniformAverage (fun i : ι => F i u)) h x -
          SOptLib.compositeObjective
            (fun u => SOptLib.finiteUniformAverage (fun i : ι => F i u)) h xStar) := by
  classical
  let f : E → ℝ := fun u => SOptLib.finiteUniformAverage (fun i : ι => F i u)
  let g : E := SOptLib.finiteUniformAverage (fun i : ι => gradF i xStar)
  have hgap :
      SOptLib.importance_weighted_gradient_gap_quadratic q n gradF x xStar ≤
        2 * Lbar *
          (f x - f xStar - ⟪g, x - xStar⟫_ℝ) := by
    simpa [f, g] using
      (finite_importance_weighted_gradient_gap_le_linearization_gap_of_component_smoothness
        (F := F) (gradF := gradF) (q := q) (Lcomp := Lcomp)
        (Lbar := Lbar) (n := n) (x := x) (z := xStar)
        hn_pos hn_card hq_pos hLcomp_pos hratio hcomponent_gap)
  have hbridge :
      f x - f xStar - ⟪g, x - xStar⟫_ℝ ≤
        SOptLib.compositeObjective f h x -
          SOptLib.compositeObjective f h xStar := by
    have hbridge_raw :=
      smooth_part_linearization_gap_le_composite_gap_of_minimizer
        (X := X) (f := f) (h := h) (g := g) (L := Lbar)
        (x := x) (xStar := xStar)
        hx hxStar hhconv
        (by
          intro y hy
          simpa [f] using hmin y hy)
        hLbar_nonneg
        (by
          intro y hy
          simpa [f, g] using hsmooth y hy)
    unfold SOptLib.first_order_linear_model at hbridge_raw
    linarith
  exact hgap.trans
    (mul_le_mul_of_nonneg_left hbridge
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLbar_nonneg))

-- Batch 7 promoted from Staging/projectedWithinGradient_smoothness_gap_of_convex_lipschitz.lean
-- Generalization plan (G0):
-- concept/name: projectedWithinGradient_smoothness_gap_of_convex_lipschitz
--   exposes the co-coercive smoothness-gap lower bound for the carrier-projected
--   within-gradient; orig was lemma58_smoothness_gap_projected.
-- generality used: arbitrary convex carrier `X : Set E`, ambient objective
--   `f : E -> Real`, positive smoothness constant `L`, convexity,
--   differentiability on the carrier, and pointwise Lipschitzness of
--   Mathlib's `gradientWithin`; no measure, oracle, finite-sum index, or
--   algorithm setup fields are used.
-- portable call pattern: finite-sum SVRG/VRAGD component-gradient estimates,
--   projected-gradient descent, and proximal-gradient smoothness proofs change
--   the component objective, carrier, and Lipschitz constant while reusing the
--   same projected-gradient gap conclusion.
-- counterargument checked: not paper-local traceability and not a one-line
--   wrapper; the theorem derives the first-order support gap and quadratic
--   upper model before applying the carrier Baillon-Haddad boundary. Existing
--   `SOptLib.carrier_baillon_haddad_of_convex_lipschitz_gradient` is partial
--   coverage only because it requires those model-gap hypotheses as inputs and
--   does not specialize them to `projectedWithinGradient`.
-- coverage search: searched `projectedWithinGradient smoothness gap`,
--   `carrier baillon haddad convex lipschitz gradient`, `co-coercive
--   smoothness gap`, and catalog entries around Baillon-Haddad. Hits were the
--   carrier Baillon-Haddad axiom, the carrier quadratic upper-bound theorem,
--   and projected-gradient staging lemmas; none state this convex/Lipschitz
--   projected-gradient endpoint inequality directly.
-- minimal hypotheses: global smoothness is reduced to pointwise feasible
--   `gradientWithin` Lipschitzness; differentiability is carrier-only; finite
--   dimensionality remains because the current SOptLib carrier Baillon-Haddad
--   boundary requires it, and `CompleteSpace`/`HasOrthogonalProjection` are
--   inherited from `projectedWithinGradient`.

/-- Convex carrier smoothness gives a projected-gradient co-coercive gap bound.

For a convex carrier, if `f` is convex, differentiable on the carrier, and its
selected within-gradient is `L`-Lipschitz on feasible points, then the
affine-span projected within-gradient satisfies the usual smoothness-gap lower
bound between any two feasible points.

Layer: Layer0 | Gap: Level 1 (projected-gradient smoothness gap)
Proof: derive projected-gradient derivative semantics and Lipschitzness from
  the existing projected-gradient API, use convex first-order support and the
  carrier quadratic upper model, then apply the carrier Baillon-Haddad boundary.
Source: Mathlib convex analysis, within-gradient calculus, Hilbert-space
  projection APIs, and SOptLib carrier Baillon-Haddad boundary
Used in: finite-sum variance-reduced accelerated gradient component smoothness
  before estimator second-moment absorption
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem projectedWithinGradient_smoothness_gap_of_convex_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (X : Set E) [((affineSpan ℝ X).direction).HasOrthogonalProjection]
    (f : E → ℝ) (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hf_convex : ConvexOn ℝ X f)
    (hf_diff : DifferentiableOn ℝ f X)
    (hL_pos : 0 < L)
    (hgradientWithin_lipschitz :
      ∀ x z : {u : E // u ∈ X},
        ‖gradientWithin f X x.1 - gradientWithin f X z.1‖ ≤ L * ‖x.1 - z.1‖)
    (x z : {u : E // u ∈ X}) :
    (1 / (2 * L)) *
        ‖projectedWithinGradient X f x.1 -
          projectedWithinGradient X f z.1‖ ^ 2 ≤
      f x.1 - f z.1 -
        ⟪projectedWithinGradient X f z.1, x.1 - z.1⟫_ℝ := by
  let v : {u : E // u ∈ X} → ℝ := fun w => f w.1
  let grad : {u : E // u ∈ X} → E := fun w => projectedWithinGradient X f w.1
  have hgrad :
      ∀ w : {u : E // u ∈ X}, HasGradientWithinAt f (grad w) X w.1 := by
    intro w
    exact projectedWithinGradient_hasGradientWithinAt X f w (hf_diff w.1 w.2)
  have hgrad_lipschitz :
      ∀ a b : {u : E // u ∈ X},
        ‖grad a - grad b‖ ≤ L * ‖a.1 - b.1‖ := by
    intro a b
    simpa [grad] using
      projectedWithinGradient_lipschitz_of_gradientWithin_lipschitz
        (X := X) (f := f) (L := L) hgradientWithin_lipschitz a b
  have hsupport :
      ∀ a b : {u : E // u ∈ X},
        0 ≤ v a - v b - ⟪grad b, a.1 - b.1⟫_ℝ := by
    intro a b
    have h :=
      ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
        hX_convex hf_convex b.2 a.2 (hgrad b)
    dsimp [v, grad] at h ⊢
    linarith
  have hupper :
      ∀ a b : {u : E // u ∈ X},
        v a - v b - ⟪grad b, a.1 - b.1⟫_ℝ ≤
          L / 2 * ‖a.1 - b.1‖ ^ 2 := by
    intro a b
    exact
      Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
        (X := X) (f := v) (F := f) (grad := grad)
        (L := L) hX_convex (by intro w hw; rfl) hgrad
        (fun x y => hgrad_lipschitz y x) a b
  have hBH :=
    SOptLib.carrier_baillon_haddad_of_convex_lipschitz_gradient
      (X := X) (v := v) (F := f) (grad := grad)
      (L := L) hX_convex hL_pos (by intro w hw; rfl) hgrad
      (by
        intro w
        simp [grad])
      hsupport hupper hgrad_lipschitz x z
  simpa [v, grad] using hBH


end SOptLib


-- Promoted from Staging/sum_Icc_weighted_half_norm_sq_le_bregman_budget.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted finite-window aggregation of a pointwise
--   half-norm-square lower bound.
-- generality used: an arbitrary carrier type with an evaluation map into a
--   seminormed additive commutative group for the displayed norm, real-valued
--   weights, scales, residuals, and an arbitrary real-valued upper expression
--   on successive carrier points.
-- portable call pattern: once a proof supplies a pointwise lower bound for
--   one half of a squared step norm, this lemma lifts it through nonnegative
--   finite-window weights and scales while preserving an additive residual.
-- minimal hypotheses: pointwise nonnegativity of weights and scales on
--   `Finset.Icc 1 k`, plus the pointwise half-norm-square lower bound on the
--   same window.

/-- Aggregate a pointwise half-norm-square lower bound over a weighted window.

If every index in `Finset.Icc 1 k` has nonnegative weight and scale, and
`upper (xPrev t) (xCur t)` dominates one half of the squared step norm, then the
weighted residual sum with `(eta_t / 2) * ‖xPrev_t - xCur_t‖ ^ 2` is bounded by
the same residual sum with `eta_t * upper (xPrev_t) (xCur_t)`.

Layer: Glue | Gap: Level 0 (weighted finite-sum lower-bound aggregation)
Proof: apply `Finset.sum_le_sum`; each summand follows by scaling the pointwise
  lower bound by the nonnegative scale, adding the residual, and scaling by the
  nonnegative weight.
Source: Mathlib finite sums over ordered rings and seminormed additive-group
  norm-square algebra
Used in: pathwise conversion of weighted step-norm sums into weighted sums of
  an available pointwise upper expression
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_Icc_weighted_half_norm_sq_le_of_pointwise_half_norm_sq_le
    {P E : Type*} [SeminormedAddCommGroup E]
    (toNorm : P → E) (upper : P → P → ℝ) (xPrev xCur : ℕ → P)
    (θ η R : ℕ → ℝ) (k : ℕ)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (hη : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ η t)
    (hhalf_norm_sq_le_upper : ∀ t, 1 ≤ t → t ≤ k →
      (1 / 2 : ℝ) * ‖toNorm (xCur t) - toNorm (xPrev t)‖ ^ 2 ≤
        upper (xPrev t) (xCur t)) :
    (∑ t ∈ Finset.Icc 1 k, θ t *
      (η t / 2 * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2 + R t)) ≤
      ∑ t ∈ Finset.Icc 1 k, θ t *
        (η t * upper (xPrev t) (xCur t) + R t) := by
  classical
  refine Finset.sum_le_sum ?_
  intro t htmem
  rcases Finset.mem_Icc.mp htmem with ⟨ht1, htk⟩
  have hupper :
      (1 / 2 : ℝ) * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2 ≤
        upper (xPrev t) (xCur t) := by
    rw [norm_sub_rev]
    exact hhalf_norm_sq_le_upper t ht1 htk
  have hscaled :
      η t * ((1 / 2 : ℝ) * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2) ≤
        η t * upper (xPrev t) (xCur t) :=
    mul_le_mul_of_nonneg_left hupper (hη t ht1 htk)
  have hbudget :
      η t / 2 * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2 ≤
        η t * upper (xPrev t) (xCur t) := by
    calc
      η t / 2 * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2 =
          η t * ((1 / 2 : ℝ) * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2) := by
            ring
      _ ≤ η t * upper (xPrev t) (xCur t) := hscaled
  have hadd :
      η t / 2 * ‖toNorm (xPrev t) - toNorm (xCur t)‖ ^ 2 + R t ≤
        η t * upper (xPrev t) (xCur t) + R t := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hbudget (R t)
  exact mul_le_mul_of_nonneg_left hadd (hθ t ht1 htk)


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: carrier smooth quadratic upper bound from affine-direction dual-norm Lipschitz gradient; orig was component_smooth_quadratic_upper_bound.
-- generality used: real Hilbert carrier with a separating primal seminorm, pointwise HasGradientWithinAt on carrier points, convex carrier, and Lipschitz control through the concrete affineDirectionDualNorm; no measure, filtration, oracle, finite-sum index, or paper setup fields.
-- portable call pattern: carrier-based finite-sum, prox-gradient, mirror-descent, and variance-reduced methods use the same smooth upper model while changing the objective, selected gradient, carrier, primal seminorm, and smoothness constant.
-- counterargument checked: not paper-local traceability because it packages the standard descent lemma for a named affine-direction dual gauge; not a duplicate of Mathlib/SOptLib norm descent because existing carrier_smooth_quadratic_upper_bound lemmas require ambient norm Lipschitz gradients, not seminorm support-dual Lipschitz gradients.
-- coverage search: searched CATALOG/SOptLib/Staging for carrier_smooth_quadratic_upper_bound, smooth quadratic upper, affineDirectionDualNorm, and abs_inner; relevant hits were Convex.carrier_smooth_quadratic_upper_bound, Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz, affineDirectionDualNorm, and abs_inner_le_affineDirectionDualNorm_mul; coverage partial because the existing smooth upper bounds use ambient norm/Cauchy-Schwarz rather than affine-direction seminorm support.
-- minimal hypotheses: global smoothness is reduced to the pointwise affineDirectionDualNorm Lipschitz condition actually used along the segment; finite-dimensionality plus separating seminorm are used only to bound the support set for the affine-direction dual support inequality.

/-- A carrier smoothness upper model from affine-direction dual-norm Lipschitz gradients.

If the selected gradient has a `HasGradientWithinAt` certificate at every
carrier point and the gradient difference is Lipschitz in the support dual of a
separating primal seminorm over the carrier affine directions, then the usual
quadratic upper model holds with that primal seminorm.

Layer: Layer0 | Gap: Level 1 (carrier smooth upper model for affine-direction dual seminorms)
Proof: restrict the objective to the segment between carrier points, identify
  the scalar derivative by the within-gradient chain rule, bound its excess
  using the affine-direction primal-dual support inequality and the Lipschitz
  hypothesis, then integrate the affine derivative bound on `[0, 1]`.
Source: Convex segment calculus, within-gradient chain rule, support functions
  of seminorm unit balls, and one-dimensional derivative-bound integration
Used in: randomized gradient extrapolation component smoothness and carrier
  smooth upper-model steps in finite-sum and mirror/prox methods
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem carrier_smooth_quadratic_upper_bound_of_affineDirectionDualNorm_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (F : E → ℝ) (grad : E → E) (p : Seminorm ℝ E) (L : ℝ)
    (hp : p.IsSeparating)
    (hX_convex : Convex ℝ X)
    (hgrad : ∀ z ∈ X, HasGradientWithinAt F (grad z) X z)
    (hgrad_lipschitz :
      ∀ x ∈ X, ∀ y ∈ X,
        affineDirectionDualNorm X p (grad x - grad y) ≤ L * p (x - y))
    {base y : E} (hbase : base ∈ X) (hy : y ∈ X) :
    F y ≤ F base + ⟪grad base, y - base⟫_ℝ + (L / 2) * p (y - base) ^ 2 := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating p hp with
    ⟨C, hCnonneg, hC⟩
  let d : E := y - base
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap base y t
  let Fseg : ℝ → ℝ := fun t => F (line t)
  have hF0 : Fseg 0 = F base := by
    simp [Fseg, line]
  have hF1 : Fseg 1 = F y := by
    simp [Fseg, line]
  have hline_mem : ∀ t ∈ s, line t ∈ X := by
    intro t ht
    exact hX_convex.lineMap_mem hbase hy ht
  have hmaps : Set.MapsTo line s X := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg ⟪grad (line t), d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := base) (b := y)
          (s := s) (x := t))
    have hfseg : HasDerivWithinAt Fseg
        ((InnerProductSpace.toDual ℝ E (grad (line t))) d) s t := by
      simpa [Fseg, Function.comp_def] using
        (hgrad (line t) (hline_mem t ht)).hasFDerivWithinAt
          |>.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps (by simp [line])
    simpa using hfseg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪grad (line t), d⟫_ℝ ≤
        ⟪grad base, d⟫_ℝ + (L * p d ^ 2) * t := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : line t - base = t • d := by
      simp [line, d, AffineMap.lineMap_apply_module']
    have hprimal_line : p (line t - base) = t * p d := by
      rw [hseg_sub]
      simp [map_smul_eq_mul, Real.norm_of_nonneg ht_nonneg]
    have hd_dir : d ∈ (affineSpan ℝ X).direction :=
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ X hy) (subset_affineSpan ℝ X hbase)
    let delta : E := grad (line t) - grad base
    have h_bdd :
        BddAbove {r : ℝ |
          ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
            p u ≤ 1 ∧ r = |inner ℝ delta u|} := by
      refine ⟨‖delta‖ * C, ?_⟩
      intro r hr
      rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
      have hinner : |inner ℝ delta u| ≤ ‖delta‖ * ‖u‖ := by
        simpa using (norm_inner_le_norm (𝕜 := ℝ) delta u)
      have hu_norm : ‖u‖ ≤ C := by
        calc
          ‖u‖ ≤ C * p u := hC u
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
          _ = C := by simp
      exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg delta))
    have hinner_diff :
        ⟪grad (line t), d⟫_ℝ - ⟪grad base, d⟫_ℝ = ⟪delta, d⟫_ℝ := by
      simp [delta, inner_sub_left]
    have hdual_smooth :
        affineDirectionDualNorm X p delta ≤ L * p (line t - base) := by
      simpa [delta] using hgrad_lipschitz (line t) (hline_mem t ht) base hbase
    have habs :
        |⟪delta, d⟫_ℝ| ≤ affineDirectionDualNorm X p delta * p d :=
      abs_inner_le_affineDirectionDualNorm_mul
        (X := X) p hp (zeta := delta) (d := d) h_bdd hd_dir
    have hinner_le :
        ⟪delta, d⟫_ℝ ≤ affineDirectionDualNorm X p delta * p d :=
      (le_abs_self _).trans habs
    have hmul_le :
        affineDirectionDualNorm X p delta * p d ≤
          (L * p (line t - base)) * p d :=
      mul_le_mul_of_nonneg_right hdual_smooth (apply_nonneg p d)
    have hquad :
        (L * p (line t - base)) * p d = (L * p d ^ 2) * t := by
      rw [hprimal_line]
      ring
    have hdiff :
        ⟪grad (line t), d⟫_ℝ - ⟪grad base, d⟫_ℝ ≤
          (L * p d ^ 2) * t := by
      calc
        ⟪grad (line t), d⟫_ℝ - ⟪grad base, d⟫_ℝ = ⟪delta, d⟫_ℝ := hinner_diff
        _ ≤ affineDirectionDualNorm X p delta * p d := hinner_le
        _ ≤ (L * p (line t - base)) * p d := hmul_le
        _ = (L * p d ^ 2) * t := hquad
    linarith
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪grad base, d⟫_ℝ + (L * p d ^ 2) / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg
      (fun t => ⟪grad (line t), d⟫_ℝ)
      ⟪grad base, d⟫_ℝ (L * p d ^ 2) hderiv hbound
  rw [hF0, hF1] at hscalar
  change F y ≤ F base + ⟪grad base, y - base⟫_ℝ + (L / 2) * p (y - base) ^ 2
  nlinarith

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: carrier Baillon-Haddad smoothness gap from affine-direction dual-norm Lipschitz gradients; orig was component_carrier_baillon_haddad_gap.
-- generality used: finite-dimensional complete real Hilbert carrier, closed convex feasible set, convex ambient objective, pointwise HasGradientWithinAt certificates, affine-span selected-gradient representatives, separating primal seminorm, positive smoothness constant, and affineDirectionDualNorm Lipschitzness; no measure, filtration, oracle, finite-sum index, or algorithm setup fields.
-- portable call pattern: carrier-based finite-sum, variance-reduced, proximal-gradient, and mirror-descent component proofs call the same co-coercive smoothness-gap endpoint while changing the component objective, selected carrier gradient, feasible carrier, primal seminorm, and smoothness constant.
-- counterargument checked: not paper-local traceability because it packages the reusable route from convex first-order support plus smooth upper model to a Baillon-Haddad gap; not a duplicate of SOptLib.carrier_baillon_haddad_of_separating_seminorm_affine_support, which assumes the Bregman nonnegativity and upper-model hypotheses directly rather than deriving them from convexity and Lipschitz gradient data.
-- coverage search: searched CATALOG/SOptLib/Staging for baillon, haddad, cocoercivity, smoothness gap, affineDirectionDualNorm, and carrier smooth upper; relevant hits were SOptLib.carrier_baillon_haddad_of_separating_seminorm_affine_support, projectedWithinGradient_smoothness_gap_of_convex_lipschitz, and carrier_smooth_quadratic_upper_bound_of_affineDirectionDualNorm_lipschitz; LeanSearch for Baillon-Haddad/cocoercivity found no Mathlib theorem with this constrained seminorm support-dual shape; coverage is partial, not full.
-- minimal hypotheses: Bregman nonnegativity is reduced to ConvexOn plus pointwise HasGradientWithinAt, the upper model is reduced to the staged affineDirectionDualNorm smoothness theorem, closedness and finite-dimensional completeness remain because the current carrier Baillon-Haddad boundary requires them, and affine-span gradient membership is needed to avoid arbitrary normal components of within-gradients.

/-- A carrier Baillon-Haddad gap bound from affine-direction dual-norm Lipschitz gradients.

For a convex objective on a closed convex carrier, if the selected within-gradient
lives in the carrier affine direction and is Lipschitz in the support dual of a
separating primal seminorm, then the affine-direction dual gradient difference
is controlled by the first-order convexity gap.

Layer: Layer0 | Gap: Level 1 (carrier Baillon-Haddad gap for affine-direction dual seminorms)
Proof: derive the nonnegative first-order convex gap from `ConvexOn`, derive
  the quadratic smooth upper model from the affine-direction dual Lipschitz
  theorem, then apply the carrier Baillon-Haddad support-dual boundary.
Source: Convex first-order support inequalities, carrier smooth upper models,
  and constrained Baillon-Haddad/co-coercivity boundaries
Used in: randomized gradient extrapolation component smoothness and carrier
  co-coercivity steps in finite-sum variance-reduced and mirror/prox methods
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem carrier_baillon_haddad_gap_of_affineDirectionDualNorm_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {X : Set E} (F : E → ℝ) (grad : E → E) (p : Seminorm ℝ E) (L : ℝ)
    (hp : p.IsSeparating)
    (hX_closed : IsClosed X)
    (hX_convex : Convex ℝ X)
    (hF_convex : ConvexOn ℝ X F)
    (hL_pos : 0 < L)
    (hgrad : ∀ z ∈ X, HasGradientWithinAt F (grad z) X z)
    (hgrad_mem_direction :
      ∀ z ∈ X, grad z ∈ (affineSpan ℝ X).direction)
    (hgrad_lipschitz :
      ∀ x ∈ X, ∀ y ∈ X,
        affineDirectionDualNorm X p (grad x - grad y) ≤ L * p (x - y))
    {x z : E} (hx : x ∈ X) (hz : z ∈ X) :
    (1 / (2 * L)) * affineDirectionDualNorm X p (grad x - grad z) ^ 2 ≤
      F x - F z - ⟪grad z, x - z⟫_ℝ := by
  classical
  let v : {u : E // u ∈ X} → ℝ := fun u => F u.1
  let carrierGrad : {u : E // u ∈ X} → E := fun u => grad u.1
  have hF_eval : ∀ (u : E) (hu : u ∈ X), F u = v ⟨u, hu⟩ := by
    intro u hu
    rfl
  have hgrad_sub :
      ∀ u : {w : E // w ∈ X},
        HasGradientWithinAt F (carrierGrad u) X u.1 := by
    intro u
    exact hgrad u.1 u.2
  have hgrad_mem_direction_sub :
      ∀ u : {w : E // w ∈ X},
        carrierGrad u ∈ (affineSpan ℝ X).direction := by
    intro u
    exact hgrad_mem_direction u.1 u.2
  have hBreg_nonneg :
      ∀ a b : {w : E // w ∈ X},
        0 ≤ v a - v b - ⟪carrierGrad b, a.1 - b.1⟫_ℝ := by
    intro a b
    have hsupport :=
      ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
        hX_convex hF_convex b.2 a.2 (hgrad b.1 b.2)
    dsimp [v, carrierGrad] at hsupport ⊢
    linarith
  have hBreg_upper :
      ∀ a b : {w : E // w ∈ X},
        v a - v b - ⟪carrierGrad b, a.1 - b.1⟫_ℝ ≤
          L / 2 * p (a.1 - b.1) ^ 2 := by
    intro a b
    have hupper :=
      carrier_smooth_quadratic_upper_bound_of_affineDirectionDualNorm_lipschitz
        (X := X) (F := F) (grad := grad) (p := p) (L := L)
        hp hX_convex hgrad hgrad_lipschitz b.2 a.2
    dsimp [v, carrierGrad] at hupper ⊢
    linarith
  have hgrad_lipschitz_sub :
      ∀ a b : {w : E // w ∈ X},
        affineDirectionDualNorm X p (carrierGrad a - carrierGrad b) ≤
          L * p (a.1 - b.1) := by
    intro a b
    exact hgrad_lipschitz a.1 a.2 b.1 b.2
  have hmain :=
    carrier_baillon_haddad_of_separating_seminorm_affine_support
      (X := X) (v := v) (F := F) (grad := carrierGrad)
      (p := p) (L := L) hp hX_closed hX_convex hL_pos hF_eval hgrad_sub
      hgrad_mem_direction_sub hBreg_nonneg hBreg_upper hgrad_lipschitz_sub
      ⟨x, hx⟩ ⟨z, hz⟩
  simpa [v, carrierGrad] using hmain

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: carrier Baillon-Haddad smoothness gap with nonnegative totalized Lipschitz constant; orig was component_smoothness_bound_of_nonnegative_L.
-- generality used: finite-dimensional complete real Hilbert carrier, closed convex feasible set, convex ambient objective, separating primal seminorm, selected within-gradients in the carrier affine direction, affine-direction support-dual Lipschitzness, and a nonnegative smoothness constant; no measure, filtration, oracle, finite-sum index, or paper setup fields.
-- portable call pattern: finite-sum, block-coordinate, variance-reduced, proximal-gradient, and mirror-descent component proofs can call the same totalized co-coercive gradient-gap endpoint while changing the carrier, component objective, selected gradient, primal seminorm, support dual, and smoothness constant.
-- counterargument checked: not merely paper-local traceability because the strict-positive Baillon-Haddad theorem is a common smooth convex optimization boundary while this lemma adds the reusable nonnegative-constant totalization needed when component smoothness constants may be zero; not a pure duplicate because existing SOptLib/staged carrier Baillon-Haddad entries require `0 < L`.
-- coverage search: searched CATALOG/SOptLib/Staging/algorithm sources for baillon_haddad, nonnegative_L, smoothness gap, affineDirectionDualNorm, and `1 / (2 * L)`; relevant hits were carrier_baillon_haddad_of_separating_seminorm_affine_support, projectedWithinGradient_smoothness_gap_of_convex_lipschitz, and carrier_baillon_haddad_gap_of_affineDirectionDualNorm_lipschitz; LeanSearch for Baillon-Haddad/cocoercivity with nonnegative Lipschitz constants found no Mathlib theorem covering the carrier seminorm support-dual zero branch.
-- minimal hypotheses: strict positivity is weakened to `0 ≤ L`; the zero branch uses only convexity and the pointwise gradient certificate at the base point, while the positive branch keeps exactly the hypotheses required by the staged carrier Baillon-Haddad theorem.

/-- A carrier Baillon-Haddad gap bound for nonnegative totalized Lipschitz constants.

When `L > 0`, this is the carrier Baillon-Haddad/co-coercivity bound from
affine-direction dual-norm Lipschitz gradients. When `L = 0`, Lean's totalized
division makes the quadratic left side vanish, and convex first-order support
gives the nonnegative linearization gap.

Layer: Layer0 | Gap: Level 1 (carrier Baillon-Haddad nonnegative-L totalization)
Proof: split on `0 < L`; the positive branch applies the affine-direction
  carrier Baillon-Haddad theorem, and the zero branch rewrites totalized
  division by zero before applying convex first-order support.
Source: constrained Baillon-Haddad/co-coercivity, convex first-order support
  inequalities, and affine-direction seminorm support duals
Used in: randomized gradient extrapolation component smoothness and future
  finite-sum or block-coordinate analyses with possibly zero component
  smoothness constants
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem carrier_baillon_haddad_gap_of_nonneg_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {X : Set E} (F : E → ℝ) (grad : E → E) (p : Seminorm ℝ E) (L : ℝ)
    (hp : p.IsSeparating)
    (hX_closed : IsClosed X)
    (hX_convex : Convex ℝ X)
    (hF_convex : ConvexOn ℝ X F)
    (hL_nonneg : 0 ≤ L)
    (hgrad : ∀ z ∈ X, HasGradientWithinAt F (grad z) X z)
    (hgrad_mem_direction :
      ∀ z ∈ X, grad z ∈ (affineSpan ℝ X).direction)
    (hgrad_lipschitz :
      ∀ x ∈ X, ∀ y ∈ X,
        affineDirectionDualNorm X p (grad x - grad y) ≤ L * p (x - y))
    {x z : E} (hx : x ∈ X) (hz : z ∈ X) :
    (1 / (2 * L)) * affineDirectionDualNorm X p (grad x - grad z) ^ 2 ≤
      F x - F z - ⟪grad z, x - z⟫_ℝ := by
  classical
  by_cases hL_pos : 0 < L
  · exact
      carrier_baillon_haddad_gap_of_affineDirectionDualNorm_lipschitz
        (X := X) (F := F) (grad := grad) (p := p) (L := L)
        hp hX_closed hX_convex hF_convex hL_pos hgrad hgrad_mem_direction
        hgrad_lipschitz hx hz
  · have hL_nonpos : L ≤ 0 := le_of_not_gt hL_pos
    have hL_eq : L = 0 := le_antisymm hL_nonpos hL_nonneg
    have hgap_nonneg :
        0 ≤ F x - F z - ⟪grad z, x - z⟫_ℝ := by
      have hsupport :=
        ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
          hX_convex hF_convex hz hx (hgrad z hz)
      linarith
    simpa [hL_eq] using hgap_nonneg

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: zero-Lipschitz gradient residual dual-size collapse; orig was
--   `proposition56_zero_L_sampled_current_residual_sq_eq_zero`, renamed away
--   from proposition numbering and sampled-table notation.
-- generality used: arbitrary type with subtraction, an arbitrary real-valued
--   dual-size functional, an arbitrary gradient map, a selected-value equality,
--   and a pointwise Lipschitz-style bound at scale `L`; no measure,
--   independence, convexity, oracle, topology, inner-product, or
--   finite-dimensional hypotheses are used by the proof.
-- portable call pattern: zero-smoothness branches in stochastic finite-sum,
--   block-coordinate, variance-reduced, and proximal-gradient analyses where a
--   selected gradient memory value is rewritten to the current gradient and
--   Lipschitz continuity with `L = 0` forces the current/stale residual square
--   to vanish.
-- counterargument checked: the theorem is short, but not paper-local
--   traceability because it isolates the recurring degenerate smoothness branch
--   with no algorithm fields; Mathlib supplies generic `sq_eq_zero_iff` and
--   order lemmas, but not this selected-gradient residual rewrite boundary.
-- coverage search: searched SOptLib/catalog/staging for `zero Lipschitz`,
--   `residual dualNorm sq`, `dualNorm bounded by zero`, and LeanSearch for
--   nonnegative bounded-above-by-zero square; closest hits were
--   `eq_zero_of_pos_mul_norm_sq_le_zero`, `sq_nonpos_iff`,
--   `norm_le_zero_iff`, and `dualNorm_sq_eq_norm_sq`, all partial rather than
--   covering a Lipschitz-gradient residual with a selected `y = grad x` rewrite.
-- minimal hypotheses: the proof uses exactly `hy`, `L = 0`, the pointwise
--   bound `dualNorm (grad x - grad z) ≤ L * radius`, and nonnegativity of that
--   same dual-size value.

/-- A zero Lipschitz scale forces the selected gradient residual square to vanish.

If the selected value `y` is the current gradient, the residual dual size is
nonnegative, and a Lipschitz-style gradient bound has scale `L = 0`, then the
dual-size square of the current/stale gradient residual is zero.

Layer: Layer0 | Gap: Level 0 (zero-Lipschitz gradient residual collapse)
Proof: rewrite the selected value to the current gradient, reduce the
  Lipschitz bound to an upper bound by zero, and combine it with nonnegativity.
Source: Mathlib ordered real arithmetic and square simplification APIs
Used in: randomized gradient extrapolation zero-smoothness sampled gradient
  memory residual branch; reusable for finite-sum and block-coordinate methods
  with zero component smoothness constants
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem zero_lipschitz_gradient_residual_dualNorm_sq_eq_zero
    {E : Type*} [Sub E]
    (dualNorm : E → ℝ) (grad : E → E) {y x z : E} {L radius : ℝ}
    (hy : y = grad x)
    (hLzero : L = 0)
    (hgrad_bound : dualNorm (grad x - grad z) ≤ L * radius)
    (hnonneg : 0 ≤ dualNorm (grad x - grad z)) :
    dualNorm (y - grad z) ^ 2 = 0 := by
  have hdual_le_zero : dualNorm (grad x - grad z) ≤ 0 := by
    simpa [hLzero] using hgrad_bound
  have hdual : dualNorm (grad x - grad z) = 0 :=
    le_antisymm hdual_le_zero hnonneg
  rw [hy]
  simp [hdual]

end SOptLib

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
--   exposes L2 transport through a Lipschitz gradient-like field from a
--   centered square-integrable random point; orig was
--   grad_sq_integrable_of_centered_l2, renamed away from the local setup.
-- generality used: arbitrary finite measure space, a normed additive group
--   domain, a normed additive group codomain, one base point, one map, and a
--   pointwise global Lipschitz bound; no convexity, differentiability,
--   filtration, oracle, Hilbert, probability, or finite-dimensional structure
--   is used.
-- portable call pattern: stochastic smooth optimization proofs use this after
--   proving iterates or search points are square-integrable about a reference
--   point; the base point, gradient field, Lipschitz constant, iterate process,
--   and measure vary while the gradient second-moment conclusion is unchanged.
-- counterargument checked: not merely paper-local traceability because it
--   packages translation to a zero-preserving Lipschitz map, Mathlib Lp
--   composition, and add-back of the base gradient; not a pure wrapper around
--   a single existing SOptLib theorem.
-- coverage search: searched `Integrable squared norm gradient Lipschitz
--   centered L2`, `LipschitzWith comp MemLp zero integrable sq norm`, and
--   Mathlib semantic search for Lipschitz maps sending Lp random variables to
--   Lp. Top hits were Mathlib `LipschitzWith.comp_memLp` and SOptLib L2
--   affine/mini-batch closure lemmas; these are proof components but do not
--   cover the nonzero-base Lipschitz-gradient composition contract.
-- minimal hypotheses: the source proof only needs finite measure, a.e. strong
--   measurability of `z`, centered squared-norm integrability, and a pointwise
--   Lipschitz estimate for `grad`; the suggested Hilbert and finite-dimensional
--   assumptions are unnecessary.

/-- A Lipschitz gradient-like field has integrable squared norm along a centered
L2 random point.

If `z` is square-integrable about `base` and `grad` is globally Lipschitz, then
the scalar process `omega |-> ‖grad (z omega)‖ ^ 2` is integrable.

Layer: Layer0 | Gap: Level 1 (Lipschitz gradient L2 transport from a center)
Proof: translate the map to `d |-> grad (d + base) - grad base`, apply
  Mathlib's `LipschitzWith.comp_memLp` to the centered displacement, add back
  the constant base value, and convert `MemLp` at exponent two to squared-norm
  integrability.
Source: Mathlib Lp-space composition for Lipschitz maps and Bochner
  squared-norm integrability APIs
Used in: randomized stochastic accelerated-gradient proofs when
  square-integrability of iterates or search points about the initial point is
  converted into square-integrability of objective gradients
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (base : E) (grad : E → F) (L : ℝ) (z : Ω → E)
    (hz_meas : AEStronglyMeasurable z μ)
    (hz_sq : Integrable (fun ω => ‖base - z ω‖ ^ 2) μ)
    (hgrad_lipschitz : ∀ x y : E, ‖grad y - grad x‖ ≤ L * ‖y - x‖) :
    Integrable (fun ω => ‖grad (z ω)‖ ^ 2) μ := by
  have hdisp_meas : AEStronglyMeasurable (fun ω => base - z ω) μ :=
    aestronglyMeasurable_const.sub hz_meas
  have hdisp_l2 : MemLp (fun ω => base - z ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hdisp_meas).2 hz_sq
  have hdisp_rev_l2 : MemLp (fun ω => z ω - base) 2 μ := by
    refine MemLp.ae_eq ?_ hdisp_l2.neg
    filter_upwards with ω
    change -(base - z ω) = z ω - base
    rw [neg_sub]
  let centeredGrad : E → F := fun d => grad (d + base) - grad base
  have hcentered_lip : LipschitzWith (Real.toNNReal L) centeredGrad := by
    refine lipschitzWith_of_norm_sub_le_mul centeredGrad L ?_
    intro d e
    have h := hgrad_lipschitz (e + base) (d + base)
    have hdiff :
        centeredGrad d - centeredGrad e = grad (d + base) - grad (e + base) := by
      dsimp [centeredGrad]
      abel
    rw [hdiff]
    have hdist : ‖(d + base) - (e + base)‖ = ‖d - e‖ := by
      congr 1
      abel
    calc
      ‖grad (d + base) - grad (e + base)‖
          ≤ L * ‖(d + base) - (e + base)‖ := h
      _ = L * dist d e := by
        rw [hdist]
        simp [dist_eq_norm]
  have hcentered_zero : centeredGrad 0 = 0 := by
    simp [centeredGrad]
  have hcentered_l2 : MemLp (fun ω => grad (z ω) - grad base) 2 μ := by
    have hcomp := hcentered_lip.comp_memLp hcentered_zero hdisp_rev_l2
    simpa [centeredGrad, Function.comp_def] using hcomp
  have hgrad_l2 : MemLp (fun ω => grad (z ω)) 2 μ := by
    have hconst : MemLp (fun _ : Ω => grad base) 2 μ := memLp_const _
    have hsum : MemLp
        (fun ω => (grad (z ω) - grad base) + grad base) 2 μ :=
      hcentered_l2.add hconst
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  exact (memLp_two_iff_integrable_sq_norm hgrad_l2.aestronglyMeasurable).1 hgrad_l2


-- Generalization plan (G0):
-- concept/name: absolute first-order Taylor remainder bound for a smooth
--   function on a convex set; orig was smoothUpper, renamed away from the
--   paper-local smoothness-model label.
-- generality used: deterministic real Hilbert space with
--   [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E], an
--   arbitrary convex feasible set X, a scalar objective f, a selected gradient
--   field grad, pointwise HasGradientAt certificates on X, and a pointwise
--   Lipschitz-gradient estimate on X; no measure, oracle, filtration,
--   probability, bounded-below, or finite-dimensional hypotheses are used.
-- portable call pattern: smooth stochastic-gradient, variance-reduced,
--   conditional-gradient, and proximal-descent proofs call the same absolute
--   Taylor-remainder estimate before absorbing oracle error or prox algebra;
--   E, X, f, grad, L, x, and y vary while the conclusion stays unchanged.
-- counterargument checked: not paper-local traceability because the statement
--   is the standard two-sided smooth Taylor remainder contract; not a pure
--   wrapper because existing SOptLib gives only the one-sided descent lemma,
--   and this theorem packages the lower bound by applying that lemma to -f.
-- coverage search: searched `absolute Taylor remainder bound HasGradientAt
--   Lipschitz gradient convex`, `smooth quadratic upper bound HasGradientAt
--   lipschitzOn convex`, and Mathlib semantic search for absolute Taylor
--   remainder from Lipschitz gradient. Top hits were
--   `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`,
--   carrier smooth upper-bound variants, and Mathlib one-dimensional Taylor
--   remainder theorems; these are partial but none states this Hilbert-space
--   absolute first-order remainder contract.
-- minimal hypotheses: all already minimal for this proof route; convexity is
--   only used for segment feasibility in the one-sided lemma, while pointwise
--   HasGradientAt and Lipschitz-gradient hypotheses are needed for both f and
--   -f.

/-- Lipschitz gradients bound the absolute first-order Taylor remainder on a
convex feasible set.

If every feasible point has the prescribed gradient and the gradient field is
`L`-Lipschitz on a convex feasible set, then the first-order Taylor remainder
between two feasible points has absolute value at most `L / 2` times the
squared displacement norm.

Layer: Layer0 | Gap: Level 1 (absolute smooth Taylor remainder from pointwise gradients)
Proof: apply the one-sided smooth quadratic upper bound to `f` and to `-f`,
  using negated gradient certificates and the same Lipschitz constant, then
  combine the resulting upper and lower scalar remainder inequalities.
Source: SOptLib smooth quadratic upper-bound lemma, Mathlib Hilbert-space
  gradient negation calculus, and ordered real absolute-value inequalities
Used in: randomized stochastic accelerated-gradient smoothness model before
  stochastic gradient-step and accelerated-step error decomposition
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (f : E → ℝ) (grad : E → E) (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hgrad : ∀ z ∈ X, HasGradientAt f (grad z) z)
    (hgrad_lipschitz :
      ∀ z ∈ X, ∀ w ∈ X, ‖grad z - grad w‖ ≤ L * ‖z - w‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    |f y - f x - ⟪grad x, y - x⟫_ℝ| ≤ (L / 2) * ‖y - x‖ ^ 2 := by
  have hupper :
      f y ≤ f x + ⟪grad x, y - x⟫_ℝ +
        (L / 2) * ‖y - x‖ ^ 2 := by
    exact smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
      (X := X) (f := f) (grad := grad) (L := L)
      hX_convex hgrad hgrad_lipschitz hx hy
  have hgrad_neg : ∀ z ∈ X, HasGradientAt (fun u : E => - f u) (-grad z) z := by
    intro z hz
    simpa using (hgrad z hz).hasFDerivAt.neg.hasGradientAt
  have hgrad_lipschitz_neg :
      ∀ z ∈ X, ∀ w ∈ X, ‖(-grad z) - (-grad w)‖ ≤ L * ‖z - w‖ := by
    intro z hz w hw
    have hnorm : ‖(-grad z) - (-grad w)‖ = ‖grad z - grad w‖ := by
      rw [← norm_neg (grad z - grad w)]
      congr 1
      abel
    calc
      ‖(-grad z) - (-grad w)‖ = ‖grad z - grad w‖ := hnorm
      _ ≤ L * ‖z - w‖ := hgrad_lipschitz z hz w hw
  have hlower_raw :
      (fun u : E => - f u) y ≤
        (fun u : E => - f u) x + ⟪-grad x, y - x⟫_ℝ +
          (L / 2) * ‖y - x‖ ^ 2 := by
    exact smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
      (X := X) (f := fun u : E => - f u) (grad := fun z : E => -grad z) (L := L)
      hX_convex hgrad_neg hgrad_lipschitz_neg hx hy
  have hupper_rem :
      f y - f x - ⟪grad x, y - x⟫_ℝ ≤ (L / 2) * ‖y - x‖ ^ 2 := by
    linarith
  have hlower_rem :
      -((L / 2) * ‖y - x‖ ^ 2) ≤ f y - f x - ⟪grad x, y - x⟫_ℝ := by
    have hraw :
        - f y ≤ - f x - ⟪grad x, y - x⟫_ℝ +
          (L / 2) * ‖y - x‖ ^ 2 := by
      simpa using hlower_raw
    linarith
  exact abs_le.mpr ⟨hlower_rem, hupper_rem⟩


-- Generalization plan (G0):
-- concept/name: integrable_smooth_value_of_centered_l2 exposes L1
--   integrability of a smooth objective value along a centered L2 random
--   point; orig was smooth_value_integrable_of_centered_l2, renamed away from
--   the local setup field order while keeping the smooth-value concept.
-- generality used: arbitrary finite measure space, a real Hilbert-space
--   domain, a.e.-strong measurability of the scalar objective along the
--   random point, a selected gradient vector at a base point, and an a.e.
--   first-order quadratic Taylor-remainder bound along the sampled points;
--   no oracle, filtration, probability, convexity, global differentiability,
--   global Lipschitz-gradient, or finite-dimensional structure is used.
-- portable call pattern: stochastic smooth-gradient, variance-reduced, and
--   accelerated proofs call this after proving an iterate/search point is
--   square-integrable about a reference point and after deriving the local
--   smooth upper model; the objective, gradient vector, base point, smoothness
--   constant, random point, and measure vary while value integrability is the
--   unchanged conclusion.
-- counterargument checked: not paper-local traceability because it packages
--   the reusable affine Taylor-part integrability plus quadratic-remainder
--   domination step; not a pure wrapper around Mathlib because existing hits
--   cover only Lp/L2 components or gradient L2 transport, not scalar smooth
--   value integrability from a centered L2 input.
-- coverage search: searched `integrable smooth value quadratic remainder
--   centered L2`, `Integrable function bounded by square norm affine plus
--   remainder`, and Mathlib semantic search for smooth function composition
--   with an L2 random variable. Top hits were SOptLib
--   `integrable_sq_norm_grad_of_lipschitz_grad_centered_l2`, SOptLib
--   affine L2 transport lemmas, and Mathlib `LipschitzWith.comp_memLp`;
--   these are partial proof components and do not cover this value statement.
-- minimal hypotheses: global smoothness was weakened to the exact pointwise
--   Taylor-remainder bound at the base, plus direct a.e.-strong measurability
--   of `f ∘ z`; finite dimension and probability are unnecessary.

/-- A smooth scalar value is integrable along a centered L2 random point.

If `z` is square-integrable about `base` and the first-order Taylor remainder
of `f` at `base` is a.e. bounded along `z` by a quadratic model, then
`omega |-> f (z omega)` is integrable under any finite measure.

Layer: Layer0 | Gap: Level 1 (smooth value integrability from centered L2)
Proof: split `f (z omega)` into its affine Taylor model at `base` plus the
  Taylor remainder. The affine model is integrable by L2-to-L1 and Hilbert
  inner-product integrability, while the remainder is dominated by the
  integrable centered squared norm.
Source: Mathlib Bochner integrability APIs, real Hilbert-space inner products,
  and smooth first-order quadratic remainder calculus
Used in: randomized stochastic accelerated-gradient proofs when centered L2
  control of generated iterates is converted into integrability of smooth
  objective values before expectation recurrences
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem integrable_smooth_value_of_centered_l2
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : E → ℝ) (g : E) (base : E) (L : ℝ) (z : Ω → E)
    (hz_meas : AEStronglyMeasurable z μ)
    (hfz_aesm : AEStronglyMeasurable (fun ω => f (z ω)) μ)
    (hz_sq : Integrable (fun ω => ‖base - z ω‖ ^ 2) μ)
    (hrem_bound :
      ∀ᵐ ω ∂ μ,
        |f (z ω) - f base - ⟪g, z ω - base⟫_ℝ| ≤
          (L / 2) * ‖z ω - base‖ ^ 2) :
    Integrable (fun ω => f (z ω)) μ := by
  let disp : Ω → E := fun ω => z ω - base
  have hdisp_meas : AEStronglyMeasurable disp μ :=
    hz_meas.sub aestronglyMeasurable_const
  have hdisp_sq : Integrable (fun ω => ‖disp ω‖ ^ 2) μ := by
    simpa [disp, norm_sub_rev] using hz_sq
  have hinner_int :
      Integrable (fun ω => ⟪g, disp ω⟫_ℝ) μ := by
    have hconst_sq :
        Integrable (fun _ : Ω => ‖g‖ ^ 2) μ :=
      integrable_const _
    exact integrable_inner_of_integrable_sq_norm
      (P := μ) (u := fun _ : Ω => g) (v := disp)
      aestronglyMeasurable_const hdisp_meas hconst_sq hdisp_sq
  have hbase_int :
      Integrable (fun ω => f base + ⟪g, disp ω⟫_ℝ) μ :=
    (integrable_const (f base)).add hinner_int
  have hrem_aesm :
      AEStronglyMeasurable
        (fun ω => f (z ω) - (f base + ⟪g, disp ω⟫_ℝ)) μ :=
    hfz_aesm.sub hbase_int.aestronglyMeasurable
  have hrem_int :
      Integrable
        (fun ω => f (z ω) - (f base + ⟪g, disp ω⟫_ℝ)) μ := by
    refine Integrable.mono' (hdisp_sq.const_mul (L / 2)) hrem_aesm ?_
    filter_upwards [hrem_bound] with ω hbound
    have hquad_nonneg : 0 ≤ (L / 2) * ‖disp ω‖ ^ 2 := by
      have hnonneg :
          0 ≤ |f (z ω) - f base - ⟪g, z ω - base⟫_ℝ| :=
        abs_nonneg _
      simpa [disp] using le_trans hnonneg hbound
    simpa [Real.norm_eq_abs, abs_of_nonneg hquad_nonneg, disp, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using hbound
  have hsum :
      Integrable
        (fun ω =>
          (f base + ⟪g, disp ω⟫_ℝ) +
            (f (z ω) - (f base + ⟪g, disp ω⟫_ℝ))) μ :=
    hbase_int.add hrem_int
  refine hsum.congr ?_
  filter_upwards with ω
  ring

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: block smooth upper bound from coordinate gradient Lipschitz;
--   orig was block_descent_model.
-- generality used: arbitrary dependent block family over a decidable index type;
--   each selected block is a complete real Hilbert space.  No measure,
--   filtration, convexity, oracle, finite index, or finite-dimensional
--   assumptions are used.  Smoothness is represented by pointwise coordinate
--   `HasGradientAt` certificates and coordinate-slice Lipschitz bounds.
-- portable call pattern: block-coordinate descent, randomized coordinate
--   descent, and block mirror-descent proofs instantiate the objective, exact
--   coordinate gradient, selected block, and local displacement to get the
--   one-block smooth descent model; only the gradient object and coordinate
--   Lipschitz hypotheses vary.
-- counterargument checked: not a duplicate of the ambient smooth quadratic
--   upper bound because this packages the dependent-product coordinate update
--   specialization and normalization of `Function.update x i (x i) = x`;
--   not paper-local because the same one-block model is a standard reusable
--   proof step in randomized block methods.
-- coverage search: queried "block coordinate quadratic upper bound Lipschitz
--   gradient coordinate replacement", "coordinate slice smooth quadratic upper
--   model HasGradientAt Lipschitz gradient", and LeanSearch "smooth descent
--   lemma Lipschitz gradient quadratic upper bound Hilbert space"; hits included
--   `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`,
--   `Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz`,
--   the staged coordinate-slice gradient bridges, and local private block
--   wrappers, but no public dependent-coordinate upper-model bridge.
-- minimal hypotheses: the source finite index and finite-dimensional assumptions
--   were dropped; `DecidableEq` is needed for `Function.update`;
--   `CompleteSpace` is inherited from the existing `HasGradientAt` smooth
--   descent lemma; and the smoothness assumptions are local to the selected
--   base point, coordinate, and Lipschitz constant.

/-- A coordinate-slice Lipschitz gradient gives the one-block smooth quadratic
upper model.

For an objective on dependent block coordinates, if the selected
one-coordinate slice has the selected coordinate of `grad` as its gradient and
that selected gradient is `L`-Lipschitz along the slice, then replacing block
`i` by `x i + rho`
satisfies the standard smooth descent upper bound.

Layer: Layer0 | Gap: Level 1 (block-coordinate smooth upper model)
Proof: apply the ambient SOptLib smooth quadratic upper-bound theorem to the
  selected coordinate slice on `Set.univ`, then simplify the basepoint update
  and displacement.
Source: SOptLib smooth descent from pointwise `HasGradientAt` and Lipschitz
  gradient, plus Mathlib `Function.update` coordinate APIs
Used in: randomized block mirror-descent and block-coordinate proofs when the
  sampled block update needs a smooth objective upper model before prox or
  oracle-error algebra
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem block_smooth_upper_bound_of_coordinate_gradient_lipschitz
    {ι : Type*} [DecidableEq ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (grad : (∀ i, Block i) → ∀ i, Block i)
    (x : ∀ i, Block i) (i : ι) (L : ℝ)
    (hgrad : ∀ u : Block i,
      HasGradientAt (fun z : Block i => f (Function.update x i z))
        (grad (Function.update x i u) i) u)
    (hgrad_lipschitz : ∀ u v : Block i,
      ‖grad (Function.update x i u) i - grad (Function.update x i v) i‖ ≤
        L * ‖u - v‖)
    (rho : Block i) :
    f (Function.update x i (x i + rho)) ≤
      f x + ⟪grad x i, rho⟫_ℝ + (L / 2) * ‖rho‖ ^ 2 := by
  have hslice :=
    smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
      (X := Set.univ)
      (f := fun z : Block i => f (Function.update x i z))
      (grad := fun z : Block i => grad (Function.update x i z) i)
      (L := L)
      convex_univ
      (by
        intro z _hz
        exact hgrad z)
      (by
        intro z _hz w _hw
        exact hgrad_lipschitz z w)
      (x := x i) (y := x i + rho) (by simp) (by simp)
  simpa [sub_eq_add_neg] using hslice

end SOptLib

namespace SOptLib

namespace AbsTaylorRemainderBound

/-- A Lipschitz-gradient objective satisfies the global absolute Taylor-remainder bound.

Layer: Layer0 | Gap: Level 1 (absolute Taylor-remainder bound from Lipschitz gradient)
Proof: convert differentiability into pointwise `HasGradientAt` certificates on
  `Set.univ`, specialize the Lipschitz-gradient bound, and apply the existing
  SOptLib convex-set absolute Taylor-remainder theorem.
Source: SOptLib absolute Taylor remainder theorem for pointwise gradients on
  convex sets and Mathlib Hilbert-space gradient calculus
Used in: randomized stochastic gradient-free proofs when the source
  `C_L^{1,1}` smoothness class is converted into the displayed smooth-descent
  inequality before Gaussian finite-difference estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem of_lipschitzGradientObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hf : LipschitzGradientObjective f L) :
    AbsTaylorRemainderBound f L := by
  intro x y
  have hgrad : ∀ z ∈ (Set.univ : Set E), HasGradientAt f (∇ f z) z := by
    intro z _hz
    exact (LipschitzGradientObjective.differentiable hf z).hasGradientAt
  have hgrad_lipschitz :
      ∀ z ∈ (Set.univ : Set E), ∀ w ∈ (Set.univ : Set E),
        ‖(fun t : E => ∇ f t) z - (fun t : E => ∇ f t) w‖ ≤
          L * ‖z - w‖ := by
    intro z _hz w _hw
    exact LipschitzGradientObjective.gradient_lipschitz hf w z
  exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
    (X := Set.univ) (f := f) (grad := fun z : E => ∇ f z) (L := L)
    (by simpa using (convex_univ : Convex ℝ (Set.univ : Set E)))
    hgrad hgrad_lipschitz (by simp) (by simp)

end AbsTaylorRemainderBound


end SOptLib

open MeasureTheory ProbabilityTheory
open scoped Gradient InnerProductSpace

-- Generalization plan (G0):
-- concept/name: absolute Gaussian smoothing error from a smooth descent bound
--   (orig was gaussianSmoothing_abs_sub_objective_le).
-- generality used: finite-dimensional real inner-product normed space with its
--   Borel, second-countable measurable structure; arbitrary real objective,
--   smoothing scale, and smoothness constant; explicit shifted-value
--   integrability and pointwise absolute Taylor-remainder hypotheses.
-- portable call pattern: Gaussian smoothing, random-direction, and zeroth-order
--   descent proofs call this to turn a smooth objective bound into a uniform
--   two-sided smoothing error; the objective, radius, law-induced integrability,
--   and ambient dimension vary between algorithms.
-- counterargument checked: this is not paper-local traceability or a caller-side
--   wrapper: it packages the nontrivial two-sided Bochner comparison, centered
--   Gaussian cancellation, and dimension second moment. Mathlib and SOptLib
--   provide the component moment and integral lemmas but no combined bound.
-- coverage search: searched "absolute Gaussian smoothing difference self smooth
--   descent bound", "standard Gaussian smoothing Taylor remainder", and
--   "Gaussian norm squared expectation finrank"; hits were the named smoothing
--   definition, `stdGaussianMoment_two`, and affine-shift integral scaling,
--   all partial rather than this complete inequality.
-- minimal hypotheses: no positivity of the radius or smoothness constant is
--   used; the shifted-value integrability is retained as the exact Bochner
--   side condition needed by `integral_sub` and `integral_mono`.

/-- Gaussian smoothing differs from a smooth objective by at most its quadratic
Taylor remainder averaged under the standard Gaussian.

If the shifted objective is integrable and its absolute first-order Taylor
remainder is bounded by `L / 2` times squared displacement, then the smoothing
error at `x` is bounded by `mu² L dim(E) / 2`.

Layer: Layer0 | Gap: Level 1 (Gaussian smoothing Taylor-error bound)
Proof: compare the shifted objective pointwise above and below by affine Taylor
models plus a quadratic remainder, integrate both inequalities, cancel the
centered Gaussian linear term, and evaluate the squared Gaussian norm moment.
Source: Mathlib Bochner integration and finite-dimensional Gaussian moments;
SOptLib centered affine-shift moment scaling and absolute Taylor bounds
Used in: randomized zeroth-order descent proofs when replacing the smoothed
objective by the original objective at an iterate or endpoint
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
Machine Learning, randomized stochastic gradient-free method -/
theorem abs_gaussianSmoothing_sub_self_le_of_smoothDescentBound
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hshift_int : Integrable (fun u : E => f (x + μ • u)) (stdGaussian E))
    (hdes : SOptLib.AbsTaylorRemainderBound f L) :
    |SOptLib.gaussianSmoothing f μ x - f x| ≤
      μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2 := by
  let g : E := ∇ f x
  let lin : E → ℝ := fun u => ⟪g, μ • u⟫_ℝ
  let quad : E → ℝ := fun u => (L / 2) * ‖x - (x + μ • u)‖ ^ (2 : ℕ)
  have hdiff_int :
      Integrable (fun u : E => f (x + μ • u) - f x) (stdGaussian E) :=
    hshift_int.sub (integrable_const _)
  have hlin_int : Integrable lin (stdGaussian E) := by
    have hid_int : Integrable (fun u : E => u) (stdGaussian E) := by
      simpa using (IsGaussian.integrable_id (μ := stdGaussian E))
    let Lmap : E →L[ℝ] ℝ := (innerSL ℝ g).smulRight μ
    simpa [lin, Lmap, real_inner_smul_right, mul_comm] using
      Lmap.integrable_comp hid_int
  have hquad_sq_int :
      Integrable (fun u : E => ‖x - (x + μ • u)‖ ^ (2 : ℕ)) (stdGaussian E) := by
    have hmem : MemLp (fun u : E => μ • u) 2 (stdGaussian E) :=
      (IsGaussian.memLp_two_id (μ := stdGaussian E)).const_smul μ
    have hsq : Integrable (fun u : E => ‖μ • u‖ ^ (2 : ℕ)) (stdGaussian E) := by
      simpa using
        (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
  have hquad_int : Integrable quad (stdGaussian E) :=
    hquad_sq_int.const_mul (L / 2)
  have hpoint_upper :
      ∀ u : E, f (x + μ • u) - f x ≤ lin u + quad u := by
    intro u
    have hrem := hdes x (x + μ • u)
    have hdisp : (x + μ • u) - x = μ • u := by abel
    have hup :
        f (x + μ • u) - f x - ⟪∇ f x, (x + μ • u) - x⟫_ℝ ≤
          (L / 2) * ‖(x + μ • u) - x‖ ^ (2 : ℕ) :=
      (le_abs_self _).trans hrem
    have hnorm :
        ‖(x + μ • u) - x‖ ^ (2 : ℕ) = ‖x - (x + μ • u)‖ ^ (2 : ℕ) := by
      rw [← norm_neg ((x + μ • u) - x)]
      congr 2
      abel
    calc
      f (x + μ • u) - f x
          ≤ ⟪∇ f x, (x + μ • u) - x⟫_ℝ +
              (L / 2) * ‖(x + μ • u) - x‖ ^ (2 : ℕ) := by linarith
      _ = lin u + quad u := by simp [lin, quad, g, hdisp, hnorm]
  have hpoint_lower :
      ∀ u : E, -(quad u) + lin u ≤ f (x + μ • u) - f x := by
    intro u
    have hrem := hdes x (x + μ • u)
    have hdisp : (x + μ • u) - x = μ • u := by abel
    have hlow :
        -((L / 2) * ‖(x + μ • u) - x‖ ^ (2 : ℕ)) ≤
          f (x + μ • u) - f x - ⟪∇ f x, (x + μ • u) - x⟫_ℝ :=
      (abs_le.mp hrem).1
    have hnorm :
        ‖(x + μ • u) - x‖ ^ (2 : ℕ) = ‖x - (x + μ • u)‖ ^ (2 : ℕ) := by
      rw [← norm_neg ((x + μ • u) - x)]
      congr 2
      abel
    calc
      -(quad u) + lin u =
          -((L / 2) * ‖(x + μ • u) - x‖ ^ (2 : ℕ)) +
            ⟪∇ f x, (x + μ • u) - x⟫_ℝ := by
              simp [lin, quad, g, hdisp, hnorm]
      _ ≤ f (x + μ • u) - f x := by linarith
  have hlin_zero : (∫ u : E, lin u ∂stdGaussian E) = 0 := by
    have hid_int : Integrable (fun u : E => u) (stdGaussian E) := by
      simpa using (IsGaussian.integrable_id (μ := stdGaussian E))
    let Lmap : E →L[ℝ] ℝ := (innerSL ℝ g).smulRight μ
    have hcomm := (ContinuousLinearMap.integral_comp_comm Lmap hid_int).symm
    simpa [lin, Lmap, ProbabilityTheory.integral_id_stdGaussian,
      real_inner_smul_right, mul_comm] using hcomm.symm
  have hquad_eval :
      (∫ u : E, quad u ∂stdGaussian E) =
        μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2 := by
    have hshift_sq :
        (∫ u : E, ‖x - (x + μ • u)‖ ^ (2 : ℕ) ∂stdGaussian E) =
          μ ^ (2 : ℕ) * (∫ u : E, ‖u‖ ^ (2 : ℕ) ∂stdGaussian E) :=
      integral_norm_sub_self_add_const_smul_sq_eq_const_mul
        (ν := stdGaussian E) (μ := μ) (x := x)
    have hmoment :
        (∫ u : E, ‖u‖ ^ (2 : ℕ) ∂stdGaussian E) =
          (Module.finrank ℝ E : ℝ) := by
      simpa [Real.rpow_natCast] using (stdGaussianMoment_two (E := E))
    calc
      (∫ u : E, quad u ∂stdGaussian E) =
          (L / 2) * (∫ u : E, ‖x - (x + μ • u)‖ ^ (2 : ℕ) ∂stdGaussian E) := by
            rw [integral_const_mul]
      _ = (L / 2) * (μ ^ (2 : ℕ) * (Module.finrank ℝ E : ℝ)) := by
            rw [hshift_sq, hmoment]
      _ = μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2 := by ring
  have hdiff_eval :
      SOptLib.gaussianSmoothing f μ x - f x =
        ∫ u : E, f (x + μ • u) - f x ∂stdGaussian E := by
    rw [SOptLib.gaussianSmoothing_apply, integral_sub hshift_int (integrable_const _)]
    simp
  have hupper :
      SOptLib.gaussianSmoothing f μ x - f x ≤
        μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2 := by
    have hmono :
        (∫ u : E, f (x + μ • u) - f x ∂stdGaussian E) ≤
          ∫ u : E, lin u + quad u ∂stdGaussian E :=
      integral_mono_ae hdiff_int (hlin_int.add hquad_int)
        (Filter.Eventually.of_forall hpoint_upper)
    calc
      SOptLib.gaussianSmoothing f μ x - f x =
          ∫ u : E, f (x + μ • u) - f x ∂stdGaussian E := hdiff_eval
      _ ≤ ∫ u : E, lin u + quad u ∂stdGaussian E := hmono
      _ = (∫ u : E, lin u ∂stdGaussian E) +
            ∫ u : E, quad u ∂stdGaussian E := by rw [integral_add hlin_int hquad_int]
      _ = μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2 := by
            rw [hlin_zero, hquad_eval]
            ring
  have hlower :
      -(μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2) ≤
        SOptLib.gaussianSmoothing f μ x - f x := by
    have hmono :
        (∫ u : E, -(quad u) + lin u ∂stdGaussian E) ≤
          ∫ u : E, f (x + μ • u) - f x ∂stdGaussian E :=
      integral_mono_ae (hquad_int.neg.add hlin_int) hdiff_int
        (Filter.Eventually.of_forall hpoint_lower)
    have hleft_eval :
        (∫ u : E, -(quad u) + lin u ∂stdGaussian E) =
          -(μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2) := by
      calc
        (∫ u : E, -(quad u) + lin u ∂stdGaussian E) =
            (∫ u : E, -(quad u) ∂stdGaussian E) +
              ∫ u : E, lin u ∂stdGaussian E := by
                change (∫ u : E, (-quad) u + lin u ∂stdGaussian E) =
                  (∫ u : E, (-quad) u ∂stdGaussian E) +
                    ∫ u : E, lin u ∂stdGaussian E
                rw [integral_add hquad_int.neg hlin_int]
        _ = -(μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2) := by
              have hneg_eval :
                  (∫ u : E, (-quad) u ∂stdGaussian E) =
                    -(∫ u : E, quad u ∂stdGaussian E) := by
                change (∫ u : E, -quad u ∂stdGaussian E) =
                  -(∫ u : E, quad u ∂stdGaussian E)
                rw [integral_neg]
              change (∫ u : E, (-quad) u ∂stdGaussian E) +
                  ∫ u : E, lin u ∂stdGaussian E =
                -(μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2)
              rw [hneg_eval, hlin_zero, hquad_eval]
              ring
    calc
      -(μ ^ (2 : ℕ) * L * (Module.finrank ℝ E : ℝ) / 2) =
          (∫ u : E, -(quad u) + lin u ∂stdGaussian E) := hleft_eval.symm
      _ ≤ ∫ u : E, f (x + μ • u) - f x ∂stdGaussian E := hmono
      _ = SOptLib.gaussianSmoothing f μ x - f x := hdiff_eval.symm
  exact abs_le.mpr ⟨hlower, hupper⟩


open scoped Gradient InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: derivative of a forward finite difference along an affine line;
--   orig was `cl11_forward_line_hasDerivAt`.
-- generality used: a complete real inner-product normed additive group `E`, a
--   real objective `f` differentiable at the evaluation point, and a nonzero
--   finite-difference scale; no global smoothness, measure, convexity, or finite
--   dimension.
-- portable call pattern: Gaussian and random-direction zeroth-order proofs
--   differentiate the scalar forward-difference fiber `s ↦ (f (x + μ •
--   (z + s • d)) - f x) / μ`; only the objective, points, and scale change.
-- counterargument checked: this is more than a caller-side expression because
--   it packages the affine-line chain rule and denominator cancellation; no
--   existing Mathlib or SOptLib declaration covers this combined contract.
-- coverage search: searched for the derivative of a forward finite difference
--   along an affine line from pointwise differentiability and a nonzero scale;
--   hits were proof components, not this complete statement.
-- minimal hypotheses: only pointwise differentiability at the composed
--   evaluation point and nonvanishing of the finite-difference scale are used.

/-- The scalar forward finite difference of an objective differentiable at the
evaluation point has the expected derivative along an affine direction, with
the nonzero scale factor canceled.

Layer: Layer0 | Gap: Level 1 (affine-line forward-difference derivative)
Proof: apply the gradient-to-Fréchet derivative conversion, compose it with
the affine-line derivative, then subtract the constant and divide by the
nonzero finite-difference scale; simplify the inner-product scalar action.
Source: Mathlib Hilbert-space gradient calculus and one-variable derivative
composition rules.
Used in: Gaussian Stein and random-direction zeroth-order proofs when reducing
a vector finite-difference identity to a one-dimensional scalar fiber.
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
Machine Learning, randomized stochastic gradient-free method -/
theorem hasDerivAt_forwardDifference_affineLine_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (μ : ℝ) (x z d : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x + μ • (z + t • d))) (hμ : μ ≠ 0) :
    HasDerivAt
      (fun s : ℝ => (f (x + μ • (z + s • d)) - f x) / μ)
      ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ t := by
  have hbase :
      HasFDerivAt f
        (InnerProductSpace.toDual ℝ E
          (∇ f (x + μ • (z + t • d))))
        (x + μ • (z + t • d)) :=
    hf.hasGradientAt.hasFDerivAt
  have hline_inner :
      HasDerivAt (fun s : ℝ => z + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add z
  have hline :
      HasDerivAt (fun s : ℝ => x + μ • (z + s • d)) (μ • d) t := by
    simpa [smul_add, add_comm, add_left_comm, add_assoc] using
      (hline_inner.const_smul μ).const_add x
  have hcomp :
      HasDerivAt (fun s : ℝ => f (x + μ • (z + s • d)))
        ((InnerProductSpace.toDual ℝ E
          (∇ f (x + μ • (z + t • d)))) (μ • d)) t := by
    simpa [Function.comp_def] using hbase.comp_hasDerivAt t hline
  have hdiv :
      HasDerivAt
        (fun s : ℝ => (f (x + μ • (z + s • d)) - f x) / μ)
        (((InnerProductSpace.toDual ℝ E
          (∇ f (x + μ • (z + t • d)))) (μ • d)) / μ) t :=
    (hcomp.sub_const (f x)).div_const μ
  convert hdiv using 1
  rw [InnerProductSpace.toDual_apply_apply, real_inner_smul_right, real_inner_comm]
  field_simp [hμ]

end SOptLib


open MeasureTheory ProbabilityTheory
open scoped Gradient InnerProductSpace

namespace SOptLib

noncomputable section

-- Generalization plan (G0):
-- concept/name: Gaussian Stein identity for a forward finite difference along
--   an affine line; orig was `cl11_forward_line_gaussianReal_stein_of_integrable`.
-- generality used: a complete real inner-product normed additive group `E`, a
--   real objective differentiable at every point of the selected affine line,
--   a nonzero finite-difference scale, and three ordinary standard-Gaussian
--   integrability hypotheses; no smoothness constant or finite dimension.
-- portable call pattern: Gaussian smoothing and random-direction zeroth-order
--   proofs replace a scalar forward-difference coordinate moment by the
--   corresponding shifted-gradient fiber integral; the objective, base point,
--   offset, direction, scale, and integrability arguments may all change.
-- counterargument checked: the statement is not paper-local or a pure wrapper;
--   it composes affine-line differentiation, Gaussian Stein integration by
--   parts, and two Gaussian-law-to-density integrability transports into the
--   complete fiber identity required by coordinate/Fubini arguments.
-- coverage search: queried `forward difference affine line Gaussian integral
--   equals shifted gradient inner product from integrability` and `Gaussian
--   Stein integral forward difference line inner gradient`; Mathlib search
--   returned generic line-derivative and integration-by-parts results, while
--   SOptLib hits were the three strict proof components, not this contract.
-- minimal hypotheses: global `CL11 f L` and `0 < μ` are weakened to linewise
--   pointwise differentiability and `μ ≠ 0`; all three integrability hypotheses
--   are consumed by the Gaussian Stein bridge.

/-- The standard-Gaussian first moment of a forward finite difference along an
affine line equals the integral of the shifted gradient in that direction.

Layer: Layer0 | Gap: Level 1 (forward-difference Gaussian affine-line Stein identity)
Proof: Differentiate the forward-difference fiber using the affine-line chain
rule, transport the three Gaussian-law integrability hypotheses to density
form, and apply the scalar standard-Gaussian Stein identity.
Source: Mathlib Hilbert-space gradient calculus, real Gaussian density
representation, and improper real-line integration by parts.
Used in: Gaussian smoothing and random-direction zeroth-order proofs when a
product-coordinate/Fubini reduction leaves a one-dimensional Gaussian fiber.
Book citation: book/FOML/StochasticZerothOrder.json#/key_lemmas/0
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for
Machine Learning, randomized stochastic gradient-free method -/
theorem integral_forwardDifference_line_mul_id_gaussianReal_eq_integral_inner_gradient_line
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (μ : ℝ) (x z d : E)
    (hf : ∀ t : ℝ, DifferentiableAt ℝ f (x + μ • (z + t • d)))
    (hμ : μ ≠ 0)
    (hleft :
      Integrable
        (fun t : ℝ =>
          ((f (x + μ • (z + t • d)) - f x) / μ) * t)
        (gaussianReal 0 1))
    (hright :
      Integrable
        (fun t : ℝ =>
          ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ)
        (gaussianReal 0 1))
    (hprod :
      Integrable
        (fun t : ℝ =>
          (f (x + μ • (z + t • d)) - f x) / μ)
        (gaussianReal 0 1)) :
    (∫ t : ℝ,
        ((f (x + μ • (z + t • d)) - f x) / μ) * t
          ∂gaussianReal 0 1) =
      ∫ t : ℝ, ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ
        ∂gaussianReal 0 1 := by
  exact integral_mul_id_gaussianReal_eq_integral_deriv
    (fun t : ℝ => (f (x + μ • (z + t • d)) - f x) / μ)
    (fun t : ℝ => ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ)
    (fun t => hasDerivAt_forwardDifference_affineLine_of_differentiableAt
      f μ x z d t (hf t) hμ)
    (integrable_mul_neg_id_mul_gaussianPDFReal_of_integrable_mul_id_gaussianReal
      (fun t : ℝ => (f (x + μ • (z + t • d)) - f x) / μ) hleft)
    (by
      simpa [mul_comm] using
        integrable_mul_gaussianPDFReal_of_integrable_gaussianReal
          (mu := 0) (v := 1) (by norm_num : (1 : NNReal) ≠ 0) hright)
    (by
      simpa [mul_comm] using
        integrable_mul_gaussianPDFReal_of_integrable_gaussianReal
          (mu := 0) (v := 1) (by norm_num : (1 : NNReal) ≠ 0) hprod)

end

end SOptLib


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: convexity of an additive-translation integral (orig was gaussianSmoothing_convexOn_of_objective_convex)
-- generality used: arbitrary real additive module E with a measurable space, arbitrary measure nu on E, scalar shift mu, and a pointwise ConvexOn objective; no norm, inner-product, probability, or finite-dimensional assumptions are needed.
-- portable call pattern: Gaussian smoothing, randomized search, and other additive-noise expected objectives use this to turn convexity of the base objective plus shifted-value integrability into convexity of the smoothed objective; f, nu, mu, and the integrability proof vary.
-- counterargument checked: this is not paper-local traceability or a caller-side wrapper; it packages translation convexity and Bochner integral convexity into a reusable expectation-preservation step. Mathlib supplies the integral theorem but not this translated-integrand specialization.
-- coverage search: searched "integral of translated convex function is convex", "convexity integral translation gaussian smoothing", and SOptLib ConvexOn/integral; Mathlib's MeasureTheory.integral_convexOn_of_integrand_ae and ConvexOn.translate_left cover the components, while no complete translated-integral theorem was found.
-- minimal hypotheses: probability, Borel, completeness, norm, inner-product, and finite-dimensional assumptions are unnecessary; only the additive real module, measurable space, measure, pointwise shifted integrability, and base ConvexOn remain.

namespace SOptLib

/-- Integrating additive translates of a convex objective preserves convexity.

For any measure on the perturbation space, if every shifted value is
integrable, then the Bochner integral `x ↦ ∫ u, f (x + mu • u) ∂nu` is convex
on the whole space whenever `f` is convex there.

Layer: Layer0 | Gap: Level 1 (convexity preservation under translated expectation)
Proof: apply `ConvexOn.translate_left` to each shifted integrand and then
  Mathlib's `MeasureTheory.integral_convexOn_of_integrand_ae` theorem.
Source: Mathlib convex-function translation and Bochner integral convexity APIs
Used in: Gaussian smoothing and additive-noise zeroth-order proofs when the
  expected shifted objective must inherit convexity from the original objective
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem convexOn_gaussianSmoothing_of_convexOn
    {E : Type*} [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
    (nu : Measure E) (f : E → ℝ) (mu : ℝ)
    (hconvex : ConvexOn ℝ Set.univ f)
    (h_integrable : ∀ x : E, Integrable (fun u : E => f (x + mu • u)) nu) :
    ConvexOn ℝ Set.univ (fun x : E => ∫ u : E, f (x + mu • u) ∂nu) := by
  apply MeasureTheory.integral_convexOn_of_integrand_ae (s := (Set.univ : Set E))
    (f := fun u x => f (x + mu • u)) (μ := nu)
  · exact convex_univ
  · filter_upwards [] with u
    simpa [Function.comp_def] using hconvex.translate_left (mu • u)
  · intro x hx
    exact h_integrable x

end SOptLib



-- Phase 4 batch 3 merge from Staging/norm_sq_forwardDifference_smul_le_of_lipschitzGradient.lean

open scoped Gradient InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: squared norm bound for a forward finite-difference vector; orig was gaussian_forward_oracle_norm_sq_pointwise_bound_CL11.
-- generality used: arbitrary complete real inner-product normed additive group E, objective f : E -> Real, smoothness constant L, base point x, and positive smoothing scale mu; no measure, Gaussian law, finite-dimensionality, or convexity assumptions are used.
-- portable call pattern: derivative-free, Gaussian-smoothing, random-direction, and coordinate finite-difference analyses call this after a pointwise Taylor split; E, f, x, L, and mu vary while the linear-plus-cubic norm bound remains unchanged.
-- counterargument checked: this is not paper-local traceability or a caller-side wrapper; it packages the nontrivial Taylor-remainder, norm-square splitting, and power algebra. Existing smooth quadratic and Taylor lemmas provide components but no complete forward-difference squared-norm contract.
-- coverage search: searched "squared norm forward difference Lipschitz gradient bound" and "squared norm of forward difference under Lipschitz gradient bound"; Mathlib and SOptLib hits were Lipschitz norm bounds, smooth quadratic upper models, and Taylor remainder components, with no matching complete declaration.
-- minimal hypotheses: CompleteSpace is required by the existing Lipschitz-gradient objective and Taylor-remainder APIs; nonnegativity of L and positivity of mu are used for the remainder coefficient and division, respectively.

/-- A smooth forward finite-difference vector is bounded by its linear gradient term
and a sixth-power Taylor-remainder term.

Layer: Layer0 | Gap: Level 1 (forward-difference squared-norm Taylor bound)
Proof: obtain the absolute Taylor remainder from the Lipschitz-gradient objective,
split the scaled difference into linear and residual parts, apply the two-term
norm-square inequality, and simplify the residual power bound.
Source: smooth first-order Taylor remainder calculus and Mathlib inner-product,
norm, scalar-action, and ordered-field APIs
Used in: Gaussian and random-direction zeroth-order oracle second-moment estimates
when a forward finite difference is decomposed before integrating its linear and
remainder terms
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem norm_sq_forward_difference_smul_le_of_lipschitz_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 < μ) :
    ∀ u : E,
      ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ) ≤
        2 * ‖((⟪∇ f x, u⟫_ℝ) • u : E)‖ ^ (2 : ℕ) +
          (μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2) * ‖u‖ ^ (6 : ℕ) := by
  intro u
  let a : ℝ := (f (x + μ • u) - f x) / μ
  let b : ℝ := ⟪∇ f x, u⟫_ℝ
  let r : ℝ := a - b
  have hdes := (AbsTaylorRemainderBound.of_lipschitzGradientObjective hf) x (x + μ • u)
  have hsub : (x + μ • u) - x = μ • u := by
    abel
  have hdes' :
      |f (x + μ • u) - f x - μ * b| ≤
        L / 2 * (μ * ‖u‖) ^ (2 : ℕ) := by
    simpa [b, hsub, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hμ.le]
      using hdes
  have hr_abs : |r| ≤ (μ * L / 2) * ‖u‖ ^ (2 : ℕ) := by
    have ha :
        r = (f (x + μ • u) - f x - μ * b) / μ := by
      dsimp [r, a]
      field_simp [hμ.ne']
    rw [ha, abs_div]
    calc
      |f (x + μ • u) - f x - μ * b| / |μ|
          ≤ (L / 2 * (μ * ‖u‖) ^ (2 : ℕ)) / |μ| := by
              exact div_le_div_of_nonneg_right hdes' (abs_nonneg μ)
      _ = (μ * L / 2) * ‖u‖ ^ (2 : ℕ) := by
              rw [abs_of_pos hμ]
              field_simp [hμ.ne']
  have hsplit :
      (((f (x + μ • u) - f x) / μ) • u : E) =
        (r • u : E) + (b • u : E) := by
    have ha : (f (x + μ • u) - f x) / μ = r + b := by
      dsimp [r, a]
      ring
    rw [ha, add_smul]
  have hsq_split :
      ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ) ≤
        2 * ‖(r • u : E)‖ ^ (2 : ℕ) +
          2 * ‖(b • u : E)‖ ^ (2 : ℕ) := by
    rw [hsplit]
    exact SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
      (r • u : E) (b • u : E)
  have hr_sq :
      2 * ‖(r • u : E)‖ ^ (2 : ℕ) ≤
        (μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2) * ‖u‖ ^ (6 : ℕ) := by
    have hbound_nonneg : 0 ≤ (μ * L / 2) * ‖u‖ ^ (2 : ℕ) := by
      positivity
    have hnorm_r :
        ‖(r • u : E)‖ ≤ ((μ * L / 2) * ‖u‖ ^ (2 : ℕ)) * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hr_abs (norm_nonneg u)
    have hnorm_r_sq :
        ‖(r • u : E)‖ ^ (2 : ℕ) ≤
          (((μ * L / 2) * ‖u‖ ^ (2 : ℕ)) * ‖u‖) ^ (2 : ℕ) := by
      nlinarith [hnorm_r, norm_nonneg (r • u : E), hbound_nonneg, norm_nonneg u]
    calc
      2 * ‖(r • u : E)‖ ^ (2 : ℕ)
          ≤ 2 * ((((μ * L / 2) * ‖u‖ ^ (2 : ℕ)) * ‖u‖) ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hnorm_r_sq (by norm_num)
      _ = (μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2) * ‖u‖ ^ (6 : ℕ) := by
              ring
  calc
    ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ)
        ≤ 2 * ‖(r • u : E)‖ ^ (2 : ℕ) +
            2 * ‖(b • u : E)‖ ^ (2 : ℕ) := hsq_split
    _ ≤ (μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2) * ‖u‖ ^ (6 : ℕ) +
          2 * ‖(b • u : E)‖ ^ (2 : ℕ) := by
            exact add_le_add hr_sq (le_refl _)
    _ = 2 * ‖((⟪∇ f x, u⟫_ℝ) • u : E)‖ ^ (2 : ℕ) +
          (μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2) * ‖u‖ ^ (6 : ℕ) := by
            simp [b, add_comm]

end SOptLib

-- Phase 4 batch 3 merge from Staging/forwardDifference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitzGradient.lean

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Gradient

-- Generalization plan (G0):
-- concept/name: Gaussian forward finite-difference squared-moment integrability and bound; orig was gaussian_forward_oracle_norm_sq_integrable_and_integral_le_CL11.
-- generality used: finite-dimensional real inner-product normed space E with Borel and second-countable measurable structure, standard Gaussian measure, objective f, Lipschitz-gradient constant L, positive smoothing scale mu, and base point x.
-- portable call pattern: Gaussian smoothing and random-direction zeroth-order analyses call this after forming a forward finite-difference estimator; E, f, L, mu, and x vary while the integrability and dimension-dependent second-moment conclusion stays fixed.
-- counterargument checked: this is not paper-local traceability or a caller-side wrapper; it composes a pointwise Taylor remainder estimate with Gaussian rank-one and sixth-moment integration to provide a reusable compound contract. Existing entries provide only the pointwise or individual moment components.
-- coverage search: searched "forward difference Gaussian norm squared integrable Lipschitz gradient" and "standard Gaussian forward finite difference second moment"; SOptLib hits were the pointwise forward-difference bound, rank-one integrability/equality, and Gaussian moment bound, with no complete integrability-plus-bound declaration.
-- minimal hypotheses: finite-dimensionality is required by stdGaussian and the rank-one fourth-moment identity; Borel and second-countable structure support continuity-based measurability; positivity of L and mu supplies the pointwise Taylor estimate and division.

/-- A Lipschitz-gradient forward finite-difference vector is square-integrable under a
standard Gaussian direction, with an explicit dimension-dependent second-moment bound.

Layer: Layer0 | Gap: Level 2 (Gaussian forward-difference second-moment composition)
Proof: dominate the squared estimator by twice its Gaussian rank-one linear term plus a sixth-power remainder, transport integrability through the affine combination, and integrate the pointwise bound using standard Gaussian moment estimates.
Source: Lipschitz-gradient Taylor remainder calculus, Gaussian rank-one fourth moments, standard Gaussian norm moments, and Bochner integral monotonicity
Used in: zeroth-order Gaussian smoothing proofs when establishing the finite second moment of the deterministic forward oracle before combining it with sample-gradient variance bounds
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : SOptLib.LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 < μ) :
    Integrable
        (fun u : E => ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
        (stdGaussian E) ∧
      (∫ u : E,
          ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ)
            ∂stdGaussian E) ≤
        2 * ((Module.finrank ℝ E : ℝ) + 4) * ‖∇ f x‖ ^ (2 : ℕ) +
          μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2 *
            ((Module.finrank ℝ E : ℝ) + 6) ^ (3 : ℕ) := by
  let lin : E → ℝ :=
    fun u => ‖((⟪∇ f x, u⟫_ℝ) • u : E)‖ ^ (2 : ℕ)
  let rem : E → ℝ := fun u => ‖u‖ ^ (6 : ℕ)
  let c : ℝ := μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2
  have hpt :
      ∀ u : E,
        ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ) ≤
          2 * lin u + c * rem u := by
    intro u
    simpa [lin, rem, c] using
      (SOptLib.norm_sq_forward_difference_smul_le_of_lipschitz_gradient
        (f := f) (L := L) (μ := μ) (x := x) hf hL hμ u)
  have hlin_int : Integrable lin (stdGaussian E) := by
    simpa [lin] using
      (integrable_norm_inner_smul_sq_stdGaussian (E := E) (∇ f x))
  have hrem_int : Integrable rem (stdGaussian E) := by
    have hmem : MemLp id 6 (stdGaussian E) :=
      IsGaussian.memLp_id (stdGaussian E) 6 (by norm_num)
    simpa [rem, Real.rpow_natCast] using
      (hmem.integrable_norm_rpow (by norm_num) (by norm_num))
  have hdom_int :
      Integrable (fun u : E => 2 * lin u + c * rem u) (stdGaussian E) :=
    (hlin_int.const_mul 2).add (hrem_int.const_mul c)
  have horacle_aesm :
      AEStronglyMeasurable
        (fun u : E =>
          ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
        (stdGaussian E) := by
    have hcont_f : Continuous f := hf.1.continuous
    have hplus : Continuous (fun u : E => f (x + μ • u)) :=
      hcont_f.comp (continuous_const.add (continuous_const.smul continuous_id))
    have horacle_cont :
        Continuous (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E)) :=
      (((hplus.sub continuous_const).div_const μ).smul continuous_id)
    exact (horacle_cont.norm.pow 2).aestronglyMeasurable
  have horacle_int :
      Integrable
        (fun u : E =>
          ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
        (stdGaussian E) := by
    refine Integrable.mono' hdom_int horacle_aesm ?_
    exact Filter.Eventually.of_forall fun u => by
      have hnonneg :
          0 ≤ ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ) := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hpt u
  refine ⟨horacle_int, ?_⟩
  have hlin_bound :
      (∫ u : E, lin u ∂stdGaussian E) ≤
        ((Module.finrank ℝ E : ℝ) + 4) * ‖∇ f x‖ ^ (2 : ℕ) := by
    have heq := integral_norm_inner_smul_sq_stdGaussian (E := E) (∇ f x)
    have hsq : 0 ≤ ‖∇ f x‖ ^ (2 : ℕ) := by positivity
    rw [show (∫ u : E, lin u ∂stdGaussian E) =
        ((Module.finrank ℝ E : ℝ) + 2) * ‖∇ f x‖ ^ (2 : ℕ) by
      simpa [lin] using heq]
    nlinarith
  have hrem_bound :
      (∫ u : E, rem u ∂stdGaussian E) ≤
        ((Module.finrank ℝ E : ℝ) + 6) ^ (3 : ℕ) := by
    have h := stdGaussianMoment_le_add_finrank_rpow_of_two_le
      (E := E) 6 (by norm_num : (2 : ℝ) ≤ 6)
    rw [show (6 : ℝ) + (Module.finrank ℝ E : ℝ) =
        (Module.finrank ℝ E : ℝ) + 6 by ring,
      show (6 : ℝ) / 2 = (3 : ℝ) by norm_num,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast] at h
    simpa only [rem, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast] using h
  have hmono :
      (∫ u : E,
        ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ)
          ∂stdGaussian E) ≤
        2 * (∫ u : E, lin u ∂stdGaussian E) +
          c * (∫ u : E, rem u ∂stdGaussian E) := by
    exact integral_le_integral_affine_combination
      (stdGaussian E)
      (fun u : E =>
        ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
      lin rem 2 c horacle_int hlin_int hrem_int (fun u => hpt u)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  calc
    (∫ u : E,
        ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ)
          ∂stdGaussian E)
        ≤ 2 * (∫ u : E, lin u ∂stdGaussian E) +
            c * (∫ u : E, rem u ∂stdGaussian E) := hmono
    _ ≤ 2 * (((Module.finrank ℝ E : ℝ) + 4) * ‖∇ f x‖ ^ (2 : ℕ)) +
          c * (((Module.finrank ℝ E : ℝ) + 6) ^ (3 : ℕ)) := by
          nlinarith [hlin_bound, hrem_bound, hc]
    _ = 2 * ((Module.finrank ℝ E : ℝ) + 4) * ‖∇ f x‖ ^ (2 : ℕ) +
          μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2 *
            ((Module.finrank ℝ E : ℝ) + 6) ^ (3 : ℕ) := by
          dsimp [c]
          ring

-- Phase 4 batch 3 merge from Staging/integrable_forwardDifference_gaussian_of_lipschitzGradient.lean

open MeasureTheory ProbabilityTheory
open scoped Gradient InnerProductSpace

-- Generalization plan (G0):
-- concept/name: Bochner integrability of a Gaussian forward finite-difference
--   vector under a Lipschitz-gradient objective; orig was
--   gaussian_forward_oracle_integrable_CL11.
-- generality used: an arbitrary finite-dimensional real inner-product normed
--   space with its Borel, second-countable measurable structure, the standard
--   Gaussian measure, a Lipschitz-gradient objective, a nonnegative smoothness
--   constant, a positive smoothing scale, and an arbitrary base point.
-- portable call pattern: Gaussian smoothing, evolution-strategy, and
--   random-direction zeroth-order proofs need the forward-difference search
--   direction to be Bochner integrable before applying Stein identities or
--   integral norm bounds; the space, objective, base point, and smoothing
--   parameters vary while this conclusion remains unchanged.
-- counterargument checked: the theorem is a short projection from the stronger
--   staged second-moment estimate, but its vector-valued Integrable conclusion
--   is the stable API consumed directly by integral identities; neither
--   Mathlib nor SOptLib exposes this specialized Gaussian contract already.
-- coverage search: queried "forward difference Gaussian Bochner integrable
--   Lipschitz gradient", "integrable vector of integrable norm squared finite
--   measure", and the corresponding Mathlib semantic query; the closest hits
--   were the generic integrable_of_integrable_norm_sq bridge and the stronger
--   forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient,
--   so coverage is compositional rather than alpha-equivalent.
-- minimal hypotheses: L > 0 is weakened to 0 <= L; finite dimensionality is
--   retained because stdGaussian and the Gaussian moment theorem require it,
--   while positivity of mu is required by the forward quotient estimate.

/-- A Lipschitz-gradient forward finite-difference vector is Bochner integrable
under the standard Gaussian direction law.

Layer: Layer0 | Gap: Level 0 (Gaussian forward-difference Bochner integrability)
Proof: continuity of the objective makes the vector-valued forward difference strongly measurable; the Gaussian squared-moment estimate and the finite-measure L2-to-L1 bridge then give Bochner integrability.
Source: Mathlib multivariate standard Gaussian measures and Bochner integrability; SOptLib Gaussian forward-difference second-moment and finite-measure L2-to-L1 APIs
Used in: Gaussian-smoothed zeroth-order and evolution-strategy proofs before applying vector-valued Stein identities, commuting linear functionals with expectation, or bounding smoothing-gradient errors
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem integrable_forwardDifference_gaussian_of_lipschitzGradient
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : SOptLib.LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 < μ) :
    Integrable
      (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
      (stdGaussian E) := by
  have hsq :
      Integrable
        (fun u : E =>
          ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
        (stdGaussian E) :=
    (forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient
      f L μ x hf hL hμ).1
  have hplus : Continuous (fun u : E => f (x + μ • u)) :=
    hf.1.continuous.comp
      (continuous_const.add (continuous_const.smul continuous_id))
  have hmeas :
      AEStronglyMeasurable
        (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
        (stdGaussian E) :=
    (((hplus.sub continuous_const).div_const μ).smul continuous_id).aestronglyMeasurable
  exact integrable_of_integrable_norm_sq hmeas hsq

-- Phase 4 batch 3 merge from Staging/integrable_gradient_gaussianShift_of_lipschitzGradient.lean

open MeasureTheory ProbabilityTheory Topology
open scoped Gradient InnerProductSpace

-- Generalization plan (G0):
-- concept/name: Bochner integrability of a Lipschitz objective gradient after
--   an affine standard-Gaussian shift; orig was
--   gaussian_gradient_shift_integrable_CL11.
-- generality used: arbitrary finite-dimensional real inner-product normed
--   space with Borel measurable structure, the standard Gaussian measure, and
--   a bundled Lipschitz-gradient objective; no convexity, oracle, filtration,
--   positivity of the Lipschitz constant, or sign condition on the shift scale
--   is used.
-- portable call pattern: Gaussian smoothing and random-search proofs call this
--   before integrating shifted gradients or differentiating an expected
--   objective; the space, objective, Lipschitz constant, scale, and base point
--   vary while shifted-gradient integrability remains unchanged.
-- counterargument checked: the generic centered-L2 Lipschitz-field theorem is
--   stronger at the second-moment level but does not directly expose the
--   standard-Gaussian shifted-gradient Integrable contract consumed by
--   smoothing proofs; this theorem composes that result with Gaussian L2 and
--   the finite-measure L2-to-L1 bridge rather than duplicating its proof.
-- coverage search: queried "integrable gradient Gaussian affine shift
--   Lipschitz gradient linear growth", "Integrable composition Lipschitz map
--   integrable random variable finite measure", and "integrable vector of
--   integrable squared norm finite measure"; the closest hits were SOptLib
--   integrable_sq_norm_grad_of_lipschitz_grad_centered_l2 and
--   integrable_of_integrable_norm_sq, which are compositional ingredients, not
--   this Gaussian specialization, while Mathlib has only lower-level MemLp
--   composition APIs.
-- minimal hypotheses: source differentiability is retained through the
--   reusable LipschitzGradientObjective contract even though this proof uses
--   only its gradient bound; positivity of L and mu is dropped,
--   SecondCountableTopology is inferred in finite dimension, and finite
--   dimensionality is retained for standard-Gaussian L2 integrability.

/-- The gradient of a Lipschitz-gradient objective is Bochner integrable after
an affine shift by a standard Gaussian vector.

Layer: Layer0 | Gap: Level 1 (Gaussian-shifted gradient integrability)
Proof: standard-Gaussian second moments make the affine shift centered L2;
  SOptLib Lipschitz-field L2 transport gives an integrable squared gradient
  norm, and the finite-measure L2-to-L1 bridge gives Bochner integrability.
Source: Mathlib multivariate Gaussian moments and Bochner integrability;
  SOptLib centered-L2 Lipschitz-gradient transport
Used in: Gaussian smoothing and randomized zeroth-order proofs before taking
  expectations of objective gradients evaluated at Gaussian-shifted queries
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem integrable_gradient_gaussianShift_of_lipschitzGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : SOptLib.LipschitzGradientObjective f L) :
    Integrable (fun u : E => ∇ f (x + μ • u)) (stdGaussian E) := by
  have hshift_meas :
      AEStronglyMeasurable (fun u : E => x + μ • u) (stdGaussian E) :=
    (continuous_const.add (continuous_const.smul continuous_id)).aestronglyMeasurable
  have hshift_sq :
      Integrable (fun u : E => ‖x - (x + μ • u)‖ ^ (2 : ℕ)) (stdGaussian E) := by
    have hmem : MemLp (fun u : E => μ • u) 2 (stdGaussian E) :=
      (IsGaussian.memLp_two_id (μ := stdGaussian E)).const_smul μ
    have hsq : Integrable (fun u : E => ‖μ • u‖ ^ (2 : ℕ)) (stdGaussian E) := by
      simpa using (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
  have hgrad_sq :
      Integrable (fun u : E => ‖∇ f (x + μ • u)‖ ^ (2 : ℕ)) (stdGaussian E) :=
    SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x (fun y : E => ∇ f y) L (fun u : E => x + μ • u)
      hshift_meas hshift_sq
      (SOptLib.LipschitzGradientObjective.gradient_lipschitz hf)
  have hgrad_lipschitz :
      LipschitzWith (Real.toNNReal L) (fun y : E => ∇ f y) := by
    refine lipschitzWith_of_norm_sub_le_mul (fun y : E => ∇ f y) L ?_
    intro a b
    simpa [dist_eq_norm] using
      SOptLib.LipschitzGradientObjective.gradient_lipschitz hf b a
  have hgrad_meas :
      AEStronglyMeasurable (fun u : E => ∇ f (x + μ • u)) (stdGaussian E) :=
    (hgrad_lipschitz.continuous.comp
      (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  exact integrable_of_integrable_norm_sq hgrad_meas hgrad_sq

-- Phase 4 batch 3 merge from Staging/integral_pi_gaussian_forwardDifference_basis_coord_eq_gradient_basis_coord_of_lipschitzGradient.lean

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Gradient InnerProductSpace

namespace SOptLib

noncomputable section

-- Generalization plan (G0):
-- concept/name: basis-coordinate product-Gaussian Stein identity for a forward difference; orig was gaussian_forward_difference_pi_coordinate_integral_eq_gradient_coordinate_CL11.
-- generality used: arbitrary finite-dimensional real Hilbert space with Borel and second-countable measurable structure, a supplied finite orthonormal basis, a Lipschitz-gradient objective, nonnegative smoothness, and positive smoothing scale; no algorithm setup, oracle, or paper-specific Euclidean alias remains.
-- portable call pattern: Gaussian-smoothed zeroth-order and evolution-strategy proofs isolate any selected basis coordinate of a forward-difference estimator and replace its product-Gaussian expectation by the matching shifted-gradient coordinate; the space, basis, coordinate, objective, smoothness constant, scale, and base point may all change.
-- counterargument checked: this is not paper-local traceability or a one-line wrapper, because it packages product-law integrability, selected-coordinate Fubini, basis reconstruction, and one-dimensional Stein integration; the existing staged declarations cover only those separate components.
-- coverage search: queried `product standard Gaussian integral forward difference coordinate equals directional derivative Stein identity` and `integral product Gaussian forward difference basis coordinate equals gradient coordinate Lipschitz gradient`; Mathlib returned generic Schwartz and Haar integration-by-parts results, while SOptLib/project hits were the one-dimensional affine-line Stein theorem and the finite product coordinate-fiber split, so coverage is partial rather than full.
-- minimal hypotheses: `L > 0` is weakened to `0 <= L`; finite-dimensional, Borel, and second-countable assumptions are used for `stdGaussian` moments and measurability, while positivity of `mu` is used for the forward-difference denominator.

/-- Under a product standard Gaussian in orthonormal-basis coordinates, the
selected coordinate moment of a forward difference equals the corresponding
coordinate of the averaged shifted gradient.

Layer: Layer0 | Gap: Level 2 (basis-coordinate product-Gaussian forward-difference Stein identity)
Proof: transport the required integrability facts from the standard Gaussian through the orthonormal-basis coordinate map, split off the selected product coordinate by Fubini, and apply the one-dimensional affine-line Gaussian Stein identity on almost every fiber.
Source: Mathlib multivariate Gaussian basis representation, finite product measures, Bochner Fubini, and Hilbert-space gradient calculus; SOptLib Gaussian moment and affine-line Stein APIs
Used in: Gaussian-smoothed zeroth-order and evolution-strategy gradient proofs when each basis coordinate of the expected forward-difference estimator is identified with the same coordinate of the expected shifted gradient
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem integral_pi_gaussian_forwardDifference_basis_coord_eq_gradient_basis_coord_of_lipschitzGradient
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n)
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 < μ) :
    (∫ z : Fin n → ℝ,
        ((f (x + μ • (∑ j, z j • (b j : E))) - f x) / μ) * z i
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) =
      ∫ z : Fin n → ℝ,
        ⟪b i, ∇ f (x + μ • (∑ j, z j • (b j : E)))⟫_ℝ
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      let μfull : Measure (Fin (m + 1) → ℝ) :=
        Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1
      let assemble : (Fin (m + 1) → ℝ) → E :=
        fun z => ∑ j, z j • (b j : E)
      let leftΦ : (Fin (m + 1) → ℝ) → ℝ :=
        fun z => ((f (x + μ • assemble z) - f x) / μ) * z i
      let rightΦ : (Fin (m + 1) → ℝ) → ℝ :=
        fun z => ⟪b i, ∇ f (x + μ • assemble z)⟫_ℝ
      have hassemble_aem : AEMeasurable assemble μfull :=
        Continuous.aemeasurable (by
          dsimp [assemble]
          continuity)
      have hbasis_coord : ∀ z : Fin (m + 1) → ℝ, ⟪b i, assemble z⟫_ℝ = z i := by
        intro z
        have hz_repr : b.repr (assemble z) = z := by
          dsimp [assemble]
          rw [OrthonormalBasis.sum_repr_symm]
          simp
        have hi := congrFun hz_repr i
        simpa [OrthonormalBasis.repr_apply_apply] using hi
      have hforward_sq :
          Integrable
            (fun u : E =>
              ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
            (stdGaussian E) :=
        (forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient
          f L μ x hf hL hμ).1
      have hforward_aesm :
          AEStronglyMeasurable
            (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
            (stdGaussian E) := by
        have hcont_f : Continuous f := hf.1.continuous
        have hplus : Continuous (fun u : E => f (x + μ • u)) :=
          hcont_f.comp (continuous_const.add (continuous_const.smul continuous_id))
        exact (((hplus.sub continuous_const).div_const μ).smul continuous_id).aestronglyMeasurable
      have hforward_int :
          Integrable
            (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
            (stdGaussian E) :=
        integrable_of_integrable_norm_sq hforward_aesm hforward_sq
      have hgrad_int :
          Integrable (fun u : E => ∇ f (x + μ • u)) (stdGaussian E) := by
        rcases hf with ⟨_hdiff, hlip⟩
        have hcont_grad : Continuous (fun y : E => ∇ f y) := by
          have hlip_with : LipschitzWith ⟨L, hL⟩ (fun y : E => ∇ f y) := by
            rw [lipschitzWith_iff_norm_sub_le]
            intro a c
            simpa using hlip c a
          exact hlip_with.continuous
        have hnorm1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := by
          simpa using (IsGaussian.integrable_id (μ := stdGaussian E)).norm
        have hbound_int :
            Integrable (fun u : E => ‖∇ f x‖ + (L * μ) * ‖u‖) (stdGaussian E) :=
          (integrable_const ‖∇ f x‖).add (hnorm1.const_mul (L * μ))
        refine Integrable.mono' hbound_int ?_ ?_
        · exact
            (hcont_grad.comp
              (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
        · exact Filter.Eventually.of_forall fun u => by
            have hsub : (x + μ • u) - x = μ • u := by abel
            calc
              ‖∇ f (x + μ • u)‖
                  ≤ ‖∇ f (x + μ • u) - ∇ f x‖ + ‖∇ f x‖ := by
                    simpa using norm_add_le (∇ f (x + μ • u) - ∇ f x) (∇ f x)
              _ ≤ L * ‖(x + μ • u) - x‖ + ‖∇ f x‖ := by
                    simpa [add_comm, add_left_comm, add_assoc] using
                      add_le_add_right (hlip x (x + μ • u)) ‖∇ f x‖
              _ = ‖∇ f x‖ + (L * μ) * ‖u‖ := by
                    rw [hsub, norm_smul, Real.norm_of_nonneg hμ.le]
                    ring
      have hleft_space_int :
          Integrable
            (fun u : E => ((f (x + μ • u) - f x) / μ) * ⟪b i, u⟫_ℝ)
            (stdGaussian E) := by
        let T : E →L[ℝ] ℝ := innerSL ℝ (b i)
        simpa [T, real_inner_smul_right] using T.integrable_comp hforward_int
      have hright_space_int :
          Integrable (fun u : E => ⟪b i, ∇ f (x + μ • u)⟫_ℝ)
            (stdGaussian E) := by
        let T : E →L[ℝ] ℝ := innerSL ℝ (b i)
        simpa [T] using T.integrable_comp hgrad_int
      rw [stdGaussian_eq_map_pi_orthonormalBasis b] at hleft_space_int hright_space_int
      have hleft_int : Integrable leftΦ μfull := by
        have hcomp :=
          (MeasureTheory.integrable_map_measure
            hleft_space_int.aestronglyMeasurable hassemble_aem).1 hleft_space_int
        simpa [leftΦ, assemble, Function.comp_def, hbasis_coord] using hcomp
      have hright_int : Integrable rightΦ μfull := by
        have hcomp :=
          (MeasureTheory.integrable_map_measure
            hright_space_int.aestronglyMeasurable hassemble_aem).1 hright_space_int
        simpa [rightΦ, assemble, Function.comp_def] using hcomp
      rw [integral_pi_eq_integral_coordinate_fiber_piFinSuccAbove
            (μ := fun _ : Fin (m + 1) => gaussianReal 0 1) i leftΦ hleft_int,
          integral_pi_eq_integral_coordinate_fiber_piFinSuccAbove
            (μ := fun _ : Fin (m + 1) => gaussianReal 0 1) i rightΦ hright_int]
      let μcoord : Measure ℝ := gaussianReal 0 1
      let μrest : Measure (Fin m → ℝ) :=
        Measure.pi fun _ : Fin m => gaussianReal 0 1
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
      let prodΦ : (Fin (m + 1) → ℝ) → ℝ :=
        fun z => (f (x + μ • assemble z) - f x) / μ
      have hvalue_space_int : Integrable (fun u : E => f (x + μ • u)) (stdGaussian E) := by
        refine integrable_smooth_value_of_centered_l2
          (f := f) (g := ∇ f x) (base := x) (L := L)
          (z := fun u : E => x + μ • u) ?_ ?_ ?_ ?_
        · exact (continuous_const.add (continuous_const.smul continuous_id)).aestronglyMeasurable
        · exact
            (hf.1.continuous.comp
              (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
        · exact integrable_norm_sub_self_add_const_smul_sq_stdGaussian μ x
        · exact Filter.Eventually.of_forall fun u => by
            simpa using (AbsTaylorRemainderBound.of_lipschitzGradientObjective hf)
              x (x + μ • u)
      have hprod_space_int :
          Integrable (fun u : E => (f (x + μ • u) - f x) / μ) (stdGaussian E) :=
        (hvalue_space_int.sub (integrable_const (f x))).div_const μ
      rw [stdGaussian_eq_map_pi_orthonormalBasis b] at hprod_space_int
      have hprod_int : Integrable prodΦ μfull := by
        have hcomp :=
          (MeasureTheory.integrable_map_measure
            hprod_space_int.aestronglyMeasurable hassemble_aem).1 hprod_space_int
        simpa [prodΦ, assemble, Function.comp_def] using hcomp
      have hmp : MeasurePreserving e μfull (μcoord.prod μrest) := by
        simpa [e, μfull, μcoord, μrest] using
          (MeasureTheory.measurePreserving_piFinSuccAbove
            (fun _ : Fin (m + 1) => gaussianReal 0 1) i)
      have hround : ∀ z : Fin (m + 1) → ℝ, e.symm (e z) = z := by
        intro z
        change (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) i)
          (z i, i.removeNth z) = z
        exact Fin.insertNth_self_removeNth i z
      have hleft_prod_int :
          Integrable (fun p : ℝ × (Fin m → ℝ) => leftΦ (e.symm p))
            (μcoord.prod μrest) := by
        rw [← hmp.integrable_comp_emb e.measurableEmbedding]
        refine hleft_int.congr ?_
        exact Filter.Eventually.of_forall fun z => by simp [hround z]
      have hright_prod_int :
          Integrable (fun p : ℝ × (Fin m → ℝ) => rightΦ (e.symm p))
            (μcoord.prod μrest) := by
        rw [← hmp.integrable_comp_emb e.measurableEmbedding]
        refine hright_int.congr ?_
        exact Filter.Eventually.of_forall fun z => by simp [hround z]
      have hprod_prod_int :
          Integrable (fun p : ℝ × (Fin m → ℝ) => prodΦ (e.symm p))
            (μcoord.prod μrest) := by
        rw [← hmp.integrable_comp_emb e.measurableEmbedding]
        refine hprod_int.congr ?_
        exact Filter.Eventually.of_forall fun z => by simp [hround z]
      have hfiber_int :
          ∀ᵐ η ∂μrest,
            Integrable (fun t : ℝ => leftΦ (e.symm (t, η))) μcoord ∧
            Integrable (fun t : ℝ => rightΦ (e.symm (t, η))) μcoord ∧
            Integrable (fun t : ℝ => prodΦ (e.symm (t, η))) μcoord := by
        filter_upwards [hleft_prod_int.prod_left_ae, hright_prod_int.prod_left_ae,
          hprod_prod_int.prod_left_ae] with η hleftη hrightη hprodη
        exact ⟨hleftη, hrightη, hprodη⟩
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hfiber_int] with η hη
      rcases hη with ⟨hleftη, hrightη, hprodη⟩
      change
        (∫ t : ℝ, leftΦ (e.symm (t, η)) ∂gaussianReal 0 1) =
          ∫ t : ℝ, rightΦ (e.symm (t, η)) ∂gaussianReal 0 1
      let rest : E := ∑ k : Fin m, η k • (b (i.succAbove k) : E)
      have hcoord_i : ∀ t : ℝ, (e.symm (t, η)) i = t := by
        intro t
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_apply_same]
      have hcoord_rest :
          ∀ (t : ℝ) (k : Fin m), (e.symm (t, η)) (i.succAbove k) = η k := by
        intro t k
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_apply_succAbove]
      have hassemble :
          ∀ t : ℝ, assemble (e.symm (t, η)) = rest + t • (b i : E) := by
        intro t
        dsimp [assemble, rest]
        rw [Fin.sum_univ_succAbove
          (fun j : Fin (m + 1) => (e.symm (t, η)) j • (b j : E)) i]
        simp [hcoord_i, hcoord_rest, add_comm]
      have hleft_line :
          Integrable
            (fun t : ℝ =>
              ((f (x + μ • (rest + t • (b i : E))) - f x) / μ) * t)
            (gaussianReal 0 1) := by
        simpa [μcoord, leftΦ, hassemble, hcoord_i] using hleftη
      have hright_line :
          Integrable
            (fun t : ℝ =>
              ⟪(b i : E), ∇ f (x + μ • (rest + t • (b i : E)))⟫_ℝ)
            (gaussianReal 0 1) := by
        simpa [μcoord, rightΦ, hassemble] using hrightη
      have hprod_line :
          Integrable
            (fun t : ℝ => (f (x + μ • (rest + t • (b i : E))) - f x) / μ)
            (gaussianReal 0 1) := by
        simpa [μcoord, prodΦ, hassemble] using hprodη
      have hstein :=
        integral_forwardDifference_line_mul_id_gaussianReal_eq_integral_inner_gradient_line
          (f := f) (μ := μ) (x := x) (z := rest) (d := (b i : E))
          (fun t => hf.1 (x + μ • (rest + t • (b i : E)))) hμ.ne'
          hleft_line hright_line hprod_line
      simpa [μcoord, leftΦ, rightΦ, hassemble, hcoord_i,
        smul_add, smul_smul, mul_assoc] using hstein

end

end SOptLib

-- Phase 4 batch 3 merge from Staging/integral_forwardDifference_mul_inner_stdGaussian_eq_integral_inner_gradient_shift_of_lipschitzGradient.lean

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Gradient InnerProductSpace

namespace SOptLib

noncomputable section

-- Generalization plan (G0):
-- concept/name: scalarized multivariate Gaussian Stein identity for a smooth
--   forward difference; orig was
--   gaussian_forward_difference_inner_integral_eq_gradient_inner_CL11.
-- generality used: arbitrary finite-dimensional real Hilbert space with Borel
--   measurable structure, a Lipschitz-gradient objective,
--   nonnegative smoothness, and positive smoothing scale; the Gaussian law is
--   Mathlib's canonical `stdGaussian`, with no algorithm setup or Euclidean
--   coordinate alias.
-- portable call pattern: Gaussian-smoothed zeroth-order and evolution-strategy
--   analyses test a forward-difference estimator against an arbitrary direction
--   and replace its expectation by the same direction paired with the averaged
--   shifted gradient; the objective, space, base point, direction, smoothness,
--   and smoothing scale may all change.
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it packages forward-estimator and shifted-gradient integrability,
--   standard-Gaussian basis transport, every-coordinate Stein identities, and
--   finite-dimensional lifting to an arbitrary test direction.
-- coverage search: queried `forward difference Gaussian integral inner product
--   equals shifted gradient integral Lipschitz gradient` with project symbol
--   search and `Gaussian integration by parts forward finite difference inner
--   product equals expected shifted gradient inner product` with Mathlib
--   LeanSearch; Mathlib returned generic Haar/Schwartz integration by parts,
--   while project hits covered only the product-Gaussian basis-coordinate
--   identity and generic orthonormal-basis lifting, so coverage is partial.
-- minimal hypotheses: `L > 0` is weakened to `0 <= L`; finite-dimensional,
--   Borel assumptions support the standard Gaussian and its basis
--   representation, while `0 < mu` makes the forward quotient valid.

/-- The standard-Gaussian moment of a smooth forward difference tested against
an arbitrary direction equals the averaged shifted gradient tested against that
direction.

Layer: Layer0 | Gap: Level 1 (scalarized multivariate Gaussian forward-difference Stein identity)
Proof: obtain integrability from the Gaussian forward-difference moment bound and Lipschitz gradient growth, prove the identity on every coordinate through product-Gaussian Stein integration, and lift the coordinate identities along a finite orthonormal basis.
Source: Mathlib multivariate standard Gaussian basis representation, Gaussian first moments, Bochner integral transport, and Hilbert-space gradient calculus; SOptLib product-coordinate Stein and finite-basis integral APIs
Used in: Gaussian-smoothed zeroth-order and evolution-strategy proofs when identifying a forward-difference average with the averaged shifted gradient after testing against a descent or comparison direction
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem integral_forwardDifference_mul_inner_stdGaussian_eq_integral_inner_gradient_shift_of_lipschitzGradient
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L μ : ℝ) (x v : E)
    (hf : LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 < μ) :
    (∫ u : E,
        ((f (x + μ • u) - f x) / μ) * ⟪v, u⟫_ℝ ∂stdGaussian E) =
      ∫ u : E, ⟪v, ∇ f (x + μ • u)⟫_ℝ ∂stdGaussian E := by
  have hforward_sq :
      Integrable
        (fun u : E =>
          ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
        (stdGaussian E) :=
    (forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient
      f L μ x hf hL hμ).1
  have hforward_aesm :
      AEStronglyMeasurable
        (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
        (stdGaussian E) := by
    have hplus : Continuous (fun u : E => f (x + μ • u)) :=
      hf.1.continuous.comp
        (continuous_const.add (continuous_const.smul continuous_id))
    exact (((hplus.sub continuous_const).div_const μ).smul continuous_id).aestronglyMeasurable
  have hforward_int :
      Integrable
        (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
        (stdGaussian E) :=
    integrable_of_integrable_norm_sq hforward_aesm hforward_sq
  have hgrad_int :
      Integrable (fun u : E => ∇ f (x + μ • u)) (stdGaussian E) := by
    have hcont_grad : Continuous (fun y : E => ∇ f y) := by
      have hlip_with : LipschitzWith ⟨L, hL⟩ (fun y : E => ∇ f y) := by
        rw [lipschitzWith_iff_norm_sub_le]
        intro a c
        simpa using hf.2 c a
      exact hlip_with.continuous
    have hnorm1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := by
      simpa using (IsGaussian.integrable_id (μ := stdGaussian E)).norm
    have hbound_int :
        Integrable (fun u : E => ‖∇ f x‖ + (L * μ) * ‖u‖) (stdGaussian E) :=
      (integrable_const ‖∇ f x‖).add (hnorm1.const_mul (L * μ))
    refine Integrable.mono' hbound_int ?_ ?_
    · exact
        (hcont_grad.comp
          (continuous_const.add
            (continuous_const.smul continuous_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        have hsub : (x + μ • u) - x = μ • u := by abel
        calc
          ‖∇ f (x + μ • u)‖
              ≤ ‖∇ f (x + μ • u) - ∇ f x‖ + ‖∇ f x‖ := by
                simpa using norm_add_le (∇ f (x + μ • u) - ∇ f x) (∇ f x)
          _ ≤ L * ‖(x + μ • u) - x‖ + ‖∇ f x‖ := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right (hf.2 x (x + μ • u)) ‖∇ f x‖
          _ = ‖∇ f x‖ + (L * μ) * ‖u‖ := by
                rw [hsub, norm_smul, Real.norm_of_nonneg hμ.le]
                ring
  classical
  let n := Module.finrank ℝ E
  let b : OrthonormalBasis (Fin n) ℝ E := stdOrthonormalBasis ℝ E
  have hcoord :
      ∀ i : Fin n,
        (∫ u : E,
          ((f (x + μ • u) - f x) / μ) * ⟪b i, u⟫_ℝ ∂stdGaussian E) =
          ∫ u : E, ⟪b i, ∇ f (x + μ • u)⟫_ℝ ∂stdGaussian E := by
    intro i
    have hleft_int :
        Integrable
          (fun u : E => ((f (x + μ • u) - f x) / μ) * ⟪b i, u⟫_ℝ)
          (stdGaussian E) := by
      let T : E →L[ℝ] ℝ := innerSL ℝ (b i)
      simpa [T, real_inner_smul_right] using T.integrable_comp hforward_int
    have hright_int :
        Integrable (fun u : E => ⟪b i, ∇ f (x + μ • u)⟫_ℝ)
          (stdGaussian E) := by
      let T : E →L[ℝ] ℝ := innerSL ℝ (b i)
      simpa [T] using T.integrable_comp hgrad_int
    let assemble : (Fin n → ℝ) → E := fun z => ∑ j, z j • (b j : E)
    have hassemble_aem :
        AEMeasurable assemble (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      Continuous.aemeasurable (by
        dsimp [assemble]
        continuity)
    rw [stdGaussian_eq_map_pi_orthonormalBasis b] at hleft_int hright_int ⊢
    rw [MeasureTheory.integral_map hassemble_aem hleft_int.aestronglyMeasurable]
    rw [MeasureTheory.integral_map hassemble_aem hright_int.aestronglyMeasurable]
    have hbasis_coord : ∀ z : Fin n → ℝ, ⟪b i, assemble z⟫_ℝ = z i := by
      intro z
      have hz_repr : b.repr (assemble z) = z := by
        dsimp [assemble]
        rw [OrthonormalBasis.sum_repr_symm]
        simp
      have hi := congrFun hz_repr i
      simpa [OrthonormalBasis.repr_apply_apply] using hi
    simpa [assemble, hbasis_coord] using
      integral_pi_gaussian_forwardDifference_basis_coord_eq_gradient_basis_coord_of_lipschitzGradient
        b i f L μ x hf hL hμ
  exact
    integral_inner_identity_of_orthonormalBasis_coordinates
      (ν := stdGaussian E) (b := b)
      (a := fun u : E => (f (x + μ • u) - f x) / μ)
      (G := fun u : E => ∇ f (x + μ • u)) (v := v)
      hforward_int hgrad_int hcoord

end

end SOptLib

-- Phase 4 batch 3 merge from Staging/integral_forwardDifference_smul_stdGaussian_eq_integral_gradient_shift_of_lipschitzGradient.lean

open MeasureTheory ProbabilityTheory
open scoped Gradient InnerProductSpace

namespace SOptLib

noncomputable section

-- Generalization plan (G0):
-- concept/name: vector-valued standard-Gaussian Stein identity for a smooth
--   forward difference; orig was
--   gaussian_forward_difference_integral_eq_gradient_average_CL11.
-- generality used: arbitrary finite-dimensional real Hilbert space with its
--   Borel measurable structure, a Lipschitz-gradient objective, nonnegative
--   smoothness, and positive smoothing scale; no algorithm setup, coordinate
--   type, or paper notation remains.
-- portable call pattern: Gaussian-smoothed zeroth-order and evolution-strategy
--   analyses replace the mean forward-difference search direction by the mean
--   shifted gradient; the objective, Hilbert space, base point, smoothness, and
--   smoothing scale may all change while the vector equality is unchanged.
-- counterargument checked: this is stronger than the already staged scalarized
--   identity and is the direct vector rewrite needed by downstream algorithms;
--   it is not paper traceability or a pure rename because it packages the two
--   vector integrability obligations and reconstructs equality from every
--   inner-product test.
-- coverage search: queried `integral forward difference smul standard Gaussian
--   equals integral shifted gradient Lipschitz gradient` and `vector integral
--   equality from all inner products finite dimensional`; the closest SOptLib
--   hit was the scalarized forward-difference Stein identity, while Mathlib
--   supplied only generic `integral_inner` and inner-product extensionality, so
--   coverage is partial rather than duplicative.
-- minimal hypotheses: `L > 0` is weakened to `0 <= L`; finite dimensionality
--   and the Borel structure are required by `stdGaussian` and the scalar Stein
--   theorem, while `0 < mu` is required for the forward quotient.

/-- The standard-Gaussian average of a smooth forward-difference vector equals
the average gradient at the corresponding shifted points.

Layer: Layer0 | Gap: Level 1 (vector-valued multivariate Gaussian forward-difference Stein identity)
Proof: establish Bochner integrability of the forward-difference vector from its Gaussian second moment and of the shifted gradient from Lipschitz growth, then commute every inner-product functional through both integrals and apply the scalarized Gaussian Stein identity.
Source: Mathlib multivariate standard Gaussian moments, Bochner integral transport by continuous linear maps, and Hilbert-space extensionality; SOptLib scalarized forward-difference Stein identity
Used in: Gaussian-smoothed zeroth-order and evolution-strategy proofs when the expected forward-difference search direction is rewritten as the expected shifted gradient before proving unbiasedness or descent
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem integral_forwardDifference_smul_stdGaussian_eq_integral_gradient_shift_of_lipschitzGradient
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 < μ) :
    (∫ u : E, (((f (x + μ • u) - f x) / μ) • u : E) ∂stdGaussian E) =
      ∫ u : E, ∇ f (x + μ • u) ∂stdGaussian E := by
  have hforward_sq :
      Integrable
        (fun u : E =>
          ‖(((f (x + μ • u) - f x) / μ) • u : E)‖ ^ (2 : ℕ))
        (stdGaussian E) :=
    (forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient
      f L μ x hf hL hμ).1
  have hforward_aesm :
      AEStronglyMeasurable
        (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
        (stdGaussian E) := by
    have hplus : Continuous (fun u : E => f (x + μ • u)) :=
      hf.1.continuous.comp
        (continuous_const.add (continuous_const.smul continuous_id))
    exact
      (((hplus.sub continuous_const).div_const μ).smul continuous_id).aestronglyMeasurable
  have hforward_int :
      Integrable
        (fun u : E => (((f (x + μ • u) - f x) / μ) • u : E))
        (stdGaussian E) :=
    integrable_of_integrable_norm_sq hforward_aesm hforward_sq
  have hgrad_int :
      Integrable (fun u : E => ∇ f (x + μ • u)) (stdGaussian E) := by
    have hcont_grad : Continuous (fun y : E => ∇ f y) := by
      have hlip_with : LipschitzWith ⟨L, hL⟩ (fun y : E => ∇ f y) := by
        rw [lipschitzWith_iff_norm_sub_le]
        intro a c
        simpa using hf.2 c a
      exact hlip_with.continuous
    have hnorm1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := by
      simpa using (IsGaussian.integrable_id (μ := stdGaussian E)).norm
    have hbound_int :
        Integrable (fun u : E => ‖∇ f x‖ + (L * μ) * ‖u‖) (stdGaussian E) :=
      (integrable_const ‖∇ f x‖).add (hnorm1.const_mul (L * μ))
    refine Integrable.mono' hbound_int ?_ ?_
    · exact
        (hcont_grad.comp
          (continuous_const.add
            (continuous_const.smul continuous_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        have hsub : (x + μ • u) - x = μ • u := by abel
        calc
          ‖∇ f (x + μ • u)‖
              ≤ ‖∇ f (x + μ • u) - ∇ f x‖ + ‖∇ f x‖ := by
                simpa using norm_add_le (∇ f (x + μ • u) - ∇ f x) (∇ f x)
          _ ≤ L * ‖(x + μ • u) - x‖ + ‖∇ f x‖ := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right (hf.2 x (x + μ • u)) ‖∇ f x‖
          _ = ‖∇ f x‖ + (L * μ) * ‖u‖ := by
                rw [hsub, norm_smul, Real.norm_of_nonneg hμ.le]
                ring
  apply ext_inner_left ℝ
  intro v
  have hleft :
      ⟪v,
        ∫ u : E, (((f (x + μ • u) - f x) / μ) • u : E)
          ∂stdGaussian E⟫_ℝ =
        ∫ u : E, ((f (x + μ • u) - f x) / μ) * ⟪v, u⟫_ℝ
          ∂stdGaussian E := by
    let T : E →L[ℝ] ℝ := innerSL ℝ v
    simpa [T, real_inner_smul_right] using
      (ContinuousLinearMap.integral_comp_comm T hforward_int).symm
  have hright :
      ⟪v, ∫ u : E, ∇ f (x + μ • u) ∂stdGaussian E⟫_ℝ =
        ∫ u : E, ⟪v, ∇ f (x + μ • u)⟫_ℝ ∂stdGaussian E := by
    let T : E →L[ℝ] ℝ := innerSL ℝ v
    simpa [T] using
      (ContinuousLinearMap.integral_comp_comm T hgrad_int).symm
  rw [hleft, hright]
  exact
    integral_forwardDifference_mul_inner_stdGaussian_eq_integral_inner_gradient_shift_of_lipschitzGradient
      f L μ x v hf hL hμ

end

end SOptLib

-- Phase 4 batch 3 merge from Staging/hasGradientAt_gaussianSmoothing_eq_integral_gradient_shift_of_lipschitzGradient.lean

open MeasureTheory ProbabilityTheory Topology
open scoped Gradient InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: differentiability of Gaussian smoothing with averaged shifted gradient; orig was gaussianSmoothing_hasGradientAt_average
-- generality used: finite-dimensional real inner-product normed space with Borel measurable structure, a Lipschitz-gradient objective, and nonnegative smoothing and Lipschitz parameters
-- portable call pattern: randomized zeroth-order and Gaussian random-search proofs identify the gradient of a Gaussian-smoothed objective by replacing the objective, radius, smoothness constant, and evaluation point while retaining the averaged shifted-gradient conclusion
-- counterargument checked: not paper-local or a pure wrapper because it packages the nontrivial Gaussian integrability and dominated differentiation obligations; the lower-level dominated integral theorem does not supply this Gaussian-smoothing specialization
-- coverage search: searched "gradient Gaussian smoothing integral shifted gradient Lipschitz gradient" and "HasGradientAt integral gradient"; SOptLib has hasGradientAt_integral_of_dominated_of_gradient_le, which is a lower-level partial result, but no Gaussian smoothing theorem with the required contract
-- minimal hypotheses: finite-dimensionality is needed for stdGaussian; completeness is supplied by finite-dimensionality, while nonnegativity of L and mu is used for the Lipschitz and affine domination bounds

/-- A Lipschitz-gradient objective is differentiable after Gaussian smoothing, with
gradient equal to the standard-Gaussian average of shifted objective gradients.

Layer: Layer0 | Gap: Level 1 (Gaussian smoothing gradient differentiation)
Proof: establish integrability and an affine Gaussian domination bound for the
shifted objective and gradient, then apply the dominated Bochner-integral
gradient theorem and identify the named smoothing definition.
Source: Mathlib Gaussian measures, Bochner integration, and Fréchet/gradient
calculus; SOptLib dominated differentiation and Taylor-remainder APIs
Used in: randomized zeroth-order descent proofs when replacing the smoothed
objective gradient by the expected gradient at Gaussian-shifted points
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem hasGradientAt_gaussianSmoothing_eq_integral_gradient_shift_of_lipschitzGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L μ : ℝ) (x : E)
    (hf : LipschitzGradientObjective f L) (hL : 0 ≤ L) (hμ : 0 ≤ μ) :
    HasGradientAt (gaussianSmoothing f μ)
      (∫ u : E, ∇ f (x + μ • u) ∂(stdGaussian E)) x := by
  haveI : IsProbabilityMeasure (stdGaussian E) := by infer_instance
  have hcont_f : Continuous f := (LipschitzGradientObjective.differentiable hf).continuous
  have hcont_grad : Continuous (fun y : E => ∇ f y) := by
    have hlip_with : LipschitzWith ⟨L, hL⟩ (fun y : E => ∇ f y) := by
      rw [lipschitzWith_iff_norm_sub_le]
      intro a b
      simpa using LipschitzGradientObjective.gradient_lipschitz hf b a
    exact hlip_with.continuous
  have hnorm1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := by
    simpa using (IsGaussian.integrable_id (μ := stdGaussian E)).norm
  have hshift_sq :
      Integrable (fun u : E => ‖x - (x + μ • u)‖ ^ (2 : ℕ)) (stdGaussian E) := by
    have hmem : MemLp (fun u : E => μ • u) 2 (stdGaussian E) :=
      (IsGaussian.memLp_two_id (μ := stdGaussian E)).const_smul μ
    have hsq : Integrable (fun u : E => ‖μ • u‖ ^ (2 : ℕ)) (stdGaussian E) := by
      simpa using (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
  have hshift_int :
      Integrable (fun u : E => f (x + μ • u)) (stdGaussian E) := by
    refine integrable_smooth_value_of_centered_l2
      (f := f) (g := ∇ f x) (base := x) (L := L)
      (z := fun u : E => x + μ • u) ?_ ?_ hshift_sq ?_
    · exact (continuous_const.add (continuous_const.smul continuous_id)).aestronglyMeasurable
    · exact (hcont_f.comp
        (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        simpa using (AbsTaylorRemainderBound.of_lipschitzGradientObjective hf x (x + μ • u))
  have hgrad_shift_int :
      Integrable (fun u : E => ∇ f (x + μ • u)) (stdGaussian E) := by
    have hbound_int :
        Integrable (fun u : E => ‖∇ f x‖ + (L * μ) * ‖u‖) (stdGaussian E) :=
      (integrable_const ‖∇ f x‖).add (hnorm1.const_mul (L * μ))
    refine Integrable.mono' hbound_int ?_ ?_
    · exact (hcont_grad.comp
        (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        have hsub : (x + μ • u) - x = μ • u := by abel
        calc
          ‖∇ f (x + μ • u)‖
              ≤ ‖∇ f (x + μ • u) - ∇ f x‖ + ‖∇ f x‖ := by
                simpa using norm_add_le (∇ f (x + μ • u) - ∇ f x) (∇ f x)
          _ ≤ L * ‖(x + μ • u) - x‖ + ‖∇ f x‖ := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right (LipschitzGradientObjective.gradient_lipschitz hf x (x + μ • u)) ‖∇ f x‖
          _ = ‖∇ f x‖ + (L * μ) * ‖u‖ := by
                rw [hsub, norm_smul, Real.norm_of_nonneg hμ]
                ring
  let bound : E → ℝ := fun u => ‖∇ f x‖ + L * (1 + μ * ‖u‖)
  have hbound_int : Integrable bound (stdGaussian E) := by
    have hlin : Integrable (fun u : E => L * (1 + μ * ‖u‖)) (stdGaussian E) := by
      have hinner : Integrable (fun u : E => 1 + μ * ‖u‖) (stdGaussian E) :=
        (integrable_const (1 : ℝ)).add (hnorm1.const_mul μ)
      simpa [mul_add, mul_assoc] using hinner.const_mul L
    exact (integrable_const ‖∇ f x‖).add hlin
  have hdom : ∀ᵐ u ∂(stdGaussian E), ∀ z ∈ Metric.closedBall x 1,
      ‖∇ f (z + μ • u)‖ ≤ bound u := by
    filter_upwards [] with u
    intro z hz
    have hzx : ‖z - x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hdist : ‖(z + μ • u) - x‖ ≤ 1 + μ * ‖u‖ := by
      have hsplit : (z + μ • u) - x = (z - x) + μ • u := by abel
      calc
        ‖(z + μ • u) - x‖ = ‖(z - x) + μ • u‖ := by rw [hsplit]
        _ ≤ ‖z - x‖ + ‖μ • u‖ := norm_add_le _ _
        _ ≤ 1 + μ * ‖u‖ := by
          rw [norm_smul, Real.norm_of_nonneg hμ]
          exact add_le_add hzx le_rfl
    calc
      ‖∇ f (z + μ • u)‖
          ≤ ‖∇ f (z + μ • u) - ∇ f x‖ + ‖∇ f x‖ := by
            simpa using norm_add_le (∇ f (z + μ • u) - ∇ f x) (∇ f x)
      _ ≤ L * ‖(z + μ • u) - x‖ + ‖∇ f x‖ := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (LipschitzGradientObjective.gradient_lipschitz hf x (z + μ • u)) ‖∇ f x‖
      _ ≤ bound u := by
            dsimp [bound]
            nlinarith [mul_le_mul_of_nonneg_left hdist hL]
  have hgrad : ∀ᵐ u ∂(stdGaussian E), ∀ z ∈ Metric.closedBall x 1,
      HasGradientAt (fun y : E => f (y + μ • u)) (∇ f (z + μ • u)) z := by
    filter_upwards [] with u
    intro z hz
    have hbase := (LipschitzGradientObjective.differentiable hf (z + μ • u)).hasGradientAt
    have haff : HasFDerivAt (fun y : E => y + μ • u)
        (1 : E →L[ℝ] E) z := by
      simpa using (hasFDerivAt_id z).add_const (μ • u)
    have hcomp := hbase.hasFDerivAt.comp z haff
    convert hcomp.hasGradientAt using 1
    apply (InnerProductSpace.toDual ℝ E).injective
    ext v
    simp [ContinuousLinearMap.comp_apply]
  have hmain := hasGradientAt_integral_of_dominated_of_gradient_le
    (μ := stdGaussian E) (F := fun z u : E => f (z + μ • u))
    (gradF := fun z u : E => ∇ f (z + μ • u)) (x := x)
    (s := Metric.closedBall x 1) (bound := bound)
    (Metric.closedBall_mem_nhds x zero_lt_one)
    (Filter.Eventually.of_forall fun z =>
      (hcont_f.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    hshift_int hgrad_shift_int.aestronglyMeasurable hdom hbound_int hgrad
  simpa [gaussianSmoothing] using hmain

end SOptLib

-- Phase 4 batch 3 merge from Staging/objective_gap_le_mul_sq_dist_of_global_minimizer.lean

open scoped Gradient InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: quadratic objective-gap upper bound at a global minimizer;
--   orig was objective_gap_le_sq_distance_from_global_optimal.
-- generality used: arbitrary complete real inner-product normed additive group
--   E, a Lipschitz-gradient objective f with smoothness scale L, an attained
--   optimum value fStar, and two points; no measure, convexity, oracle, or
--   finite-dimensional assumptions are used.
-- portable call pattern: smooth stochastic-gradient, variance-reduced, and
--   zeroth-order analyses can dominate an objective gap by an iterate's squared
--   distance to any attained unconstrained minimizer, changing f, L, fStar,
--   xStar, and x while retaining the same conclusion.
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes minimizer stationarity, the smooth Taylor model, and
--   attained optimum-value identification into the reusable quadratic gap
--   bound needed by L2-to-objective-gap arguments.
-- coverage search: symbol searches for "smooth objective value gap upper bound
--   squared distance global minimizer" and "AbsTaylorRemainderBound global
--   minimizer objective gap squared distance", plus Mathlib semantic searches
--   for the smooth minimizer bound, found Mathlib IsLocalMin Fermat lemmas,
--   SOptLib.eq_gradient_of_hasGradientAt_of_affine_minorant_touch, and
--   SOptLib.AbsTaylorRemainderBound.of_lipschitzGradientObjective as proof
--   components, but no declaration with this complete objective-gap contract.
-- minimal hypotheses: global convexity, positivity of L, probability data, and
--   finite dimensionality are removed; the optimum-value equality is retained
--   explicitly because the conclusion is stated relative to fStar.

/-- A smooth objective's gap above an attained global minimum is bounded by
half its smoothness scale times the squared distance to the minimizer.

Layer: Layer0 | Gap: Level 1 (quadratic smooth objective gap at a global minimizer)
Proof: identify the gradient at the unconstrained global minimizer with zero
  using a touching constant affine minorant, then apply the absolute smooth
  Taylor-remainder bound and rewrite the attained optimum value.
Source: Mathlib Hilbert-space gradient calculus and SOptLib absolute Taylor
  remainder and touching affine-support APIs
Used in: smooth stochastic and zeroth-order convergence proofs that turn
  squared-distance integrability or moment bounds into objective-gap control
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/0/math
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient free method -/
theorem objective_gap_le_mul_sq_dist_of_global_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L fStar : ℝ) (xStar x : E)
    (hf : LipschitzGradientObjective f L)
    (hmin : ∀ y : E, f xStar ≤ f y)
    (hfStar : fStar = f xStar) :
    f x - fStar ≤ (L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hgrad_star : ∇ f xStar = 0 := by
    have hgrad : HasGradientAt f (∇ f xStar) xStar :=
      (LipschitzGradientObjective.differentiable hf xStar).hasGradientAt
    have hminor :
        ∀ y : E, ⟪y, (0 : E)⟫_ℝ - (-f xStar) ≤ f y := by
      intro y
      simpa using hmin y
    have htouch :
        ⟪xStar, (0 : E)⟫_ℝ - (-f xStar) = f xStar := by
      simp
    exact (eq_gradient_of_hasGradientAt_of_affine_minorant_touch
      hgrad hminor htouch).symm
  have hdes := AbsTaylorRemainderBound.of_lipschitzGradientObjective hf xStar x
  have hmodel :
      f x ≤ f xStar + ⟪∇ f xStar, x - xStar⟫_ℝ +
        (L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    have h :=
      (le_abs_self (f x - f xStar - ⟪∇ f xStar, x - xStar⟫_ℝ)).trans hdes
    linarith
  rw [hfStar]
  simpa [hgrad_star, add_comm] using hmodel

end SOptLib

-- Phase 4 batch 3 merge from Staging/integrable_objective_gap_of_integrable_sq_dist_to_minimizer.lean

open MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: objective-gap integrability from L2 distance to an attained
--   global minimizer; orig was
--   objective_gap_integrable_of_sq_distance_integrable.
-- generality used: arbitrary complete real Hilbert space E, arbitrary measure
--   nu, a Lipschitz-gradient objective f, an attained optimum value fStar, and
--   an a.e.-strongly measurable E-valued process; no probability, convexity,
--   oracle, or finite-dimensional assumptions are used.
-- portable call pattern: smooth stochastic-gradient, variance-reduced, and
--   zeroth-order analyses can convert an iterate's L2 distance invariant into
--   objective-gap integrability while changing the objective, measure,
--   minimizer, process, smoothness scale, and attained optimum value.
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes smooth minimizer growth, objective composition
--   measurability, nonnegativity of the attained gap, and integrability by
--   domination into the recurring L2-to-objective-gap proof step.
-- coverage search: searched "objective gap integrable squared distance global
--   minimizer", "integrable function composition dominated by integrable
--   nonnegative upper bound squared norm distance", and Mathlib semantic
--   variants; the closest hits were Integrable.mono',
--   integrable_smooth_value_of_centered_l2, and
--   objective_gap_le_mul_sq_dist_of_global_minimizer, which provide proof
--   components or require a finite measure but do not state this contract.
-- minimal hypotheses: the source's Euclidean finite-dimensional space and
--   probability law are removed; global convexity is replaced by the actually
--   used global-minimizer property, and no sign assumption on L is needed.

/-- A smooth objective gap is integrable when squared distance to an attained
global minimizer is integrable.

Layer: Layer0 | Gap: Level 1 (objective-gap integrability from minimizer-centered L2 control)
Proof: continuity of a Lipschitz-gradient objective gives a.e. strong
  measurability of the composed gap. The attained-minimum nonnegativity and
  quadratic smooth objective-gap bound provide domination by the integrable
  squared-distance process.
Source: Mathlib `Integrable.mono'` and continuous-composition measurability,
  together with SOptLib's smooth objective-gap bound at a global minimizer
Used in: convex stochastic zeroth-order prefix inductions that propagate
  squared-distance integrability and then require objective-gap expectations
Book citation: book/FOML/StochasticZerothOrder.json#/main_theorem/proof/13
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient free method -/
theorem integrable_objective_gap_of_integrable_sq_dist_to_minimizer
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ν : Measure Ω}
    (f : E → ℝ) (L fStar : ℝ) (xStar : E) (X : Ω → E)
    (hf : LipschitzGradientObjective f L)
    (hmin : ∀ y : E, f xStar ≤ f y)
    (hfStar : fStar = f xStar)
    (hX_aesm : AEStronglyMeasurable X ν)
    (hX_l2 : Integrable (fun ω : Ω => ‖X ω - xStar‖ ^ (2 : ℕ)) ν) :
    Integrable (fun ω : Ω => f (X ω) - fStar) ν := by
  have hgap_aesm :
      AEStronglyMeasurable (fun ω : Ω => f (X ω) - fStar) ν :=
    ((LipschitzGradientObjective.differentiable hf).continuous.comp_aestronglyMeasurable
      hX_aesm).sub aestronglyMeasurable_const
  have hbound_int :
      Integrable (fun ω : Ω => (L / 2) * ‖X ω - xStar‖ ^ (2 : ℕ)) ν :=
    hX_l2.const_mul (L / 2)
  refine Integrable.mono' hbound_int hgap_aesm ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hgap_nonneg : 0 ≤ f (X ω) - fStar := by
    rw [hfStar]
    exact sub_nonneg.mpr (hmin (X ω))
  rw [Real.norm_eq_abs, abs_of_nonneg hgap_nonneg]
  exact objective_gap_le_mul_sq_dist_of_global_minimizer
    f L fStar xStar (X ω) hf hmin hfStar

end SOptLib

-- Phase 4 batch 3 merge from Staging/norm_sq_gradient_le_two_mul_smoothness_mul_sub_inf.lean

open scoped Gradient InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: norm_sq_gradient_le_two_mul_smoothness_mul_sub_inf exposes the
--   standard gradient-norm-to-objective-gap conversion for a smooth function;
--   orig was objective_gradient_norm_sq_le_two_mul_L_gap.
-- generality used: arbitrary complete real inner-product normed additive group,
--   objective f, positive smoothness constant L, reference lower bound fInf,
--   the global absolute Taylor-remainder property, and a pointwise certificate
--   that fInf lower-bounds f; no measure, convexity, oracle, probability, or
--   finite-dimensional assumptions are used.
-- portable call pattern: stochastic-gradient, variance-reduced, zeroth-order,
--   and nonconvex proximal analyses call this when converting a true-gradient
--   second moment into an objective gap; f, L, fInf, and x vary while the
--   gradient-gap conclusion keeps the same form.
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper because it combines the smooth upper model at an inverse-L gradient
--   step with a global lower bound and nontrivial Hilbert-space scalar algebra.
-- coverage search: queried "squared norm gradient upper bound smoothness
--   objective gap lower bound", "norm squared gradient less than two times L
--   times function sub infimum", and Mathlib semantic search for the standard
--   smooth lower-bounded gradient-gap inequality. SOptLib hits only provide the
--   smooth quadratic upper model, and Mathlib hits concern derivative norms of
--   Lipschitz functions; none states this gradient-gap conclusion.
-- minimal hypotheses: global differentiability and Lipschitz-gradient data are
--   reduced to AbsTaylorRemainderBound, and bounded-below is reduced to the
--   pointwise lower-bound certificate actually used at the gradient step.

/-- A smooth objective's squared gradient norm is bounded by its gap above any
global lower bound.

For positive `L`, take one inverse-`L` gradient step in the smooth quadratic
upper model and compare its value with the supplied lower bound `fInf`.

Layer: Layer0 | Gap: Level 1 (smooth gradient norm to objective gap conversion)
Proof: specialize the absolute Taylor-remainder bound at the inverse-smoothness
  gradient step, simplify its inner product and norm terms, then combine the
  resulting descent estimate with the objective lower bound.
Source: smooth nonconvex optimization descent lemma and Mathlib Hilbert-space
  gradient, inner-product, norm, and ordered-field APIs
Used in: randomized stochastic gradient-free oracle second-moment control when
  replacing a true-gradient square by a lower-bounded objective gap
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/0/math
Origin algorithm: Lan, First-Order and Stochastic Optimization Methods for
  Machine Learning, Randomized Stochastic Gradient Free Method -/
theorem norm_sq_gradient_le_two_mul_smoothness_mul_sub_inf
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L fInf : ℝ) (x : E)
    (hL_pos : 0 < L)
    (hsmooth : AbsTaylorRemainderBound f L)
    (hfInf : ∀ y, fInf ≤ f y) :
    ‖∇ f x‖ ^ (2 : ℕ) ≤ 2 * L * (f x - fInf) := by
  let g : E := ∇ f x
  let eta : ℝ := L⁻¹
  let y : E := x - eta • g
  have hmodel :
      f y ≤ f x + ⟪∇ f x, y - x⟫_ℝ +
        (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    have h := (le_abs_self (f y - f x - ⟪∇ f x, y - x⟫_ℝ)).trans
      (hsmooth x y)
    linarith
  have heta_nonneg : 0 ≤ eta := by
    exact inv_nonneg.mpr hL_pos.le
  have hy_sub : y - x = -(eta • g) := by
    dsimp [y]
    abel
  have hinner :
      ⟪∇ f x, y - x⟫_ℝ = -eta * ‖g‖ ^ (2 : ℕ) := by
    rw [hy_sub, inner_neg_right, inner_smul_right]
    simp [g]
  have hnorm :
      ‖y - x‖ ^ (2 : ℕ) = eta ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := by
    rw [hy_sub, norm_neg, norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg heta_nonneg]
    ring
  have hdescent :
      f y ≤ f x - (1 / (2 * L)) * ‖g‖ ^ (2 : ℕ) := by
    calc
      f y ≤ f x + ⟪∇ f x, y - x⟫_ℝ +
          (L / 2) * ‖y - x‖ ^ (2 : ℕ) := hmodel
      _ = f x - (1 / (2 * L)) * ‖g‖ ^ (2 : ℕ) := by
        have hL_ne : L ≠ 0 := ne_of_gt hL_pos
        rw [hinner, hnorm]
        dsimp [eta]
        field_simp [hL_ne]
        ring
  have hgap :
      (1 / (2 * L)) * ‖g‖ ^ (2 : ℕ) ≤ f x - fInf := by
    linarith [hfInf y]
  calc
    ‖∇ f x‖ ^ (2 : ℕ) =
        (2 * L) * ((1 / (2 * L)) * ‖g‖ ^ (2 : ℕ)) := by
      have hL_ne : L ≠ 0 := ne_of_gt hL_pos
      dsimp [g]
      field_simp [hL_ne]
    _ ≤ (2 * L) * (f x - fInf) := by
      exact mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = 2 * L * (f x - fInf) := by ring

end SOptLib

-- Phase 4 batch 3 merge from Staging/objective_sub_inf_sub_error_le_inner_gradient_smoothing.lean

open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: convex smoothed-objective gap lower bound from a gradient inner product;
--   orig was gaussianSmoothing_gradient_inner_ge_objective_gap_sub_error.
-- generality used: complete real inner-product normed additive group `E`, original
--   objective `f`, comparison objective `g`, gradient map `grad`, scalar infimum
--   value `fStar`, error budget `eps`, and two points; no measure, oracle,
--   smoothing law, or finite-dimensional assumption is used.
-- portable call pattern: zeroth-order Gaussian smoothing and other approximate-
--   objective convex analyses use the convex first-order support inequality and
--   endpoint approximation errors to lower-bound an original objective gap by a
--   smoothed-gradient pairing; objectives, approximations, and error budgets vary.
-- counterargument checked: this is not paper-local traceability or a caller-side
--   wrapper: it composes convex support, inner-product sign conversion, two-sided
--   approximation bounds, and an attained-infimum equality into a reusable gap
--   estimate. Existing SOptLib support lemmas provide only the first-order model,
--   while no existing entry combines the endpoint-error conclusion.
-- coverage search: searched "convex objective gap infimum smoothing error inner
--   gradient lower bound" and "first order convex support gradient inner product";
--   `ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt` was a partial
--   support hit, with no matching combined objective-gap theorem.
-- minimal hypotheses: endpoint approximation is stated only at `x` and `xStar`,
--   and the optimizer information is reduced to the equality `fStar = f xStar`.

/-- A convex comparison objective transfers an endpoint approximation bound to an
original objective-gap lower bound for its gradient pairing.

If `g` is convex and has gradient `grad x` at `x`, while `g` approximates `f` at
the two endpoints within `eps / 2`, then the gap to the attained value `fStar`
is bounded by the inner product with the displacement toward `xStar`.

Layer: Layer0 | Gap: Level 1 (convex approximate-objective gradient gap)
Proof: apply the convex first-order support inequality at `x`, rewrite the
reversed displacement inner product, and combine the two endpoint absolute-error
bounds with the attained-value equality by ordered real arithmetic.
Source: Mathlib convex first-order support, real inner-product bilinearity, and
absolute-value order identities
Used in: zeroth-order Gaussian smoothing convex convergence, where a smoothed
gradient pairing is converted into the original objective gap before telescoping
the iterate recursion
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec
Origin algorithm: Lan, First-Order and Stochastic Optimization Methods for
Machine Learning, randomized stochastic gradient-free method -/
theorem objective_gap_sub_error_le_inner_gradient_of_convex_approximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → ℝ) (grad : E → E) (fStar eps : ℝ) (xStar x : E)
    (hconvex : ConvexOn ℝ Set.univ g)
    (hgrad : HasGradientWithinAt g (grad x) Set.univ x)
    (herr_x : |g x - f x| ≤ eps / 2)
    (herr_xStar : |g xStar - f xStar| ≤ eps / 2)
    (hfstar : fStar = f xStar) :
    f x - fStar - eps ≤ ⟪grad x, x - xStar⟫_ℝ := by
  have hsupport :
      g x + ⟪grad x, xStar - x⟫_ℝ ≤ g xStar :=
    ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      hconvex (by simp) (by simp) hgrad
  have hinner_lower :
      g x - g xStar ≤ ⟪grad x, x - xStar⟫_ℝ := by
    have hinner :
        ⟪grad x, xStar - x⟫_ℝ = -⟪grad x, x - xStar⟫_ℝ := by
      rw [← inner_neg_right]
      congr 1
      abel
    linarith
  have hx_lower : f x - eps / 2 ≤ g x := by
    have h := (abs_le.mp herr_x).1
    linarith
  have hxStar_upper : g xStar ≤ f xStar + eps / 2 := by
    have h := (abs_le.mp herr_xStar).2
    linarith
  linarith

end SOptLib
