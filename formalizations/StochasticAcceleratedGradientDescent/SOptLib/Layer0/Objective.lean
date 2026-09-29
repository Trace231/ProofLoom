import Mathlib.MeasureTheory.Integral.Bochner.Basic
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.Objective
import SOptLib.Model.Stationarity

open MeasureTheory Topology
open scoped InnerProductSpace

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
