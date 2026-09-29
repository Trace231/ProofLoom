import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Bounds.Basic
import Mathlib.Topology.Semicontinuity.Basic
import SOptLib.Model.Objective

open scoped InnerProductSpace

namespace SOptLib

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGap.lean
-- Generalization plan (G0):
-- G0.1 naming: saddleGap (orig was: gap)
-- G0.2 typeclass level used:
--   E: none; the carrier is an arbitrary comparison type `Z`.
--   measure: none; this is a deterministic value-level saddle-gap construction.
--   convexity: none; convexity and compactness support later attainment or
--     measurability results, not the definition of the gap value.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual gap maximization
--      `g(zt) = sup_z Q(zt,z)` over feasible comparison points.
--   2. stochastic mirror-prox and extragradient saddle-point analyses that
--      evaluate a primal-dual gap by optimizing a comparison kernel over a
--      feasible carrier.
-- G0.4 search trace:
--   queries: ["saddle gap value", "supremum over comparison points saddle gap value",
--     "indexed supremum feasible comparison"]
--   top hits: ["gapValue", "gapValueSet", "gap",
--     "gap_measurable_of_compact_value_function", "saddle_gap_comparison",
--     "gapValue_eq_gapMaximizer_value",
--     "saddle_gap_comparison_left_lowerSemicontinuous", "SupSet.sSup", "iSup"]
--   coverage: partial - Mathlib provides the order-theoretic indexed supremum,
--     and the target file has the paper-local `gapValue`; no importable
--     project declaration gives the paper-independent saddle-gap functional.
-- G0.4 not-a-thin-wrapper rationale: the declaration fixes the reusable
--   saddle-point quantifier orientation `zTilde ↦ sup_z Q zTilde z`, separating
--   the gap functional from paper-local feasible-set notation and argmax
--   certificates.
-- G0.5 structural-content rationale: the construction exposes the stable
--   optimization object consumed by attainment, lower-semicontinuity,
--   measurability, and expected-gap arguments.
-- G0.5c thin-wrapper self-detect: clean - this is a canonical saddle-gap value
--   construction with a companion unfolding theorem, not a theorem alias or
--   projection accessor.
-- G0.5d minimal-hypothesis check: all already minimal; no global hypotheses are
--   present.

/-- Fixed-base saddle gap over feasible comparison points.

For a two-point comparison kernel `Q`, `saddleGap Q zTilde` is the value-level
gap obtained by taking the supremum of the section `z ↦ Q zTilde z`.

Layer: Model | Concept: Objective
Proof: (definitional construction; indexed supremum of a fixed-base saddle-gap
  comparison section)
Source: convex-concave saddle-point gap functions and Mathlib complete-lattice
  indexed supremum API
Used in: stochastic accelerated primal-dual value-level gap maximization over
  feasible comparison points
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def saddleGap {Z : Type*} (Q : Z → Z → ℝ) (zTilde : Z) : ℝ :=
  ⨆ z : Z, Q zTilde z

/-- The fixed-base saddle gap unfolds to the indexed supremum of the comparison
section.

Layer: Model | Gap: Level 0 (saddle-gap value unfolding)
Proof: by rfl after unfolding `saddleGap`.
Source: convex-concave saddle-point gap functions and Mathlib complete-lattice
  indexed supremum API
Used in: stochastic accelerated primal-dual normalization of the value-level
  saddle gap
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem saddleGap_def {Z : Type*} (Q : Z → Z → ℝ) (zTilde : Z) :
    saddleGap Q zTilde = ⨆ z : Z, Q zTilde z := by
  rfl

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGapValue.lean
/-- Fixed-base saddle-gap value over feasible comparison points.

For a two-point comparison kernel `Q`, `saddleGapValue Q zTilde` is the
value-level gap obtained by taking the supremum of the section
`z ↦ Q zTilde z`.

Layer: Model | Concept: Objective
Proof: (definitional construction; indexed supremum of a fixed-base
  saddle-gap comparison section)
Source: convex-concave saddle-point gap functions and Mathlib complete-lattice
  indexed supremum API
Used in: stochastic accelerated primal-dual value-level gap maximization over
  feasible comparison points
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def saddleGapValue {Z : Type*} (Q : Z → Z → ℝ) (zTilde : Z) : ℝ :=
  ⨆ z : Z, Q zTilde z

/-- The fixed-base saddle-gap value unfolds to the indexed supremum of the
comparison section.

Layer: Model | Gap: Level 0 (saddle-gap value unfolding)
Proof: by rfl after unfolding `saddleGapValue`.
Source: convex-concave saddle-point gap functions and Mathlib complete-lattice
  indexed supremum API
Used in: stochastic accelerated primal-dual normalization of the value-level
  saddle gap
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem saddleGapValue_def {Z : Type*} (Q : Z → Z → ℝ) (zTilde : Z) :
    saddleGapValue Q zTilde = ⨆ z : Z, Q zTilde z := by
  rfl

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGapComparison.lean
-- Generalization plan (G0):
-- G0.1 naming: saddleGapComparison (orig was: Q)
-- G0.2 typeclass level used:
--   E: X has no structure; Y has [NormedAddCommGroup Y] [InnerProductSpace ℝ Y],
--     exactly enough for the Hilbert coupling term `⟪Aeval x, y⟫_ℝ`.
--   measure: none, this is a deterministic pointwise saddle-gap comparison.
--   convexity: none, this definition names the comparison value before imposing
--     convexity, concavity, compactness, or semicontinuity assumptions downstream.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual gap maximization `g(zt) = max_z Q(zt,z)`
--      in Lan Eq. (4.4.20)--(4.4.21).
--   2. stochastic mirror-prox and convex-concave saddle-point analyses that bound
--      a primal-dual gap by comparing `L(xt, y)` with `L(x, yt)`.
-- G0.4 search trace:
--   queries: ["saddle gap comparison", "saddle objective gap",
--     "saddle gap comparison Lagrangian f x y minus f x y swapped"]
--   top hits: ["gapValue", "gapMaximizer", "gap_measurable_of_compact_value_function",
--     "SOptLib.saddle_objective", "SOptLib.continuous_saddle_objective",
--     "SOptLib.objectiveGapIntegrand", "Mathlib.Order.SaddlePoint.IsSaddlePointOn"]
--   coverage: partial - Mathlib has saddle-point predicates and SOptLib has a
--     one-point saddle objective, but neither names the two-point swapped
--     comparison value `L(zt.x, z.y) - L(z.x, zt.y)`.
-- G0.4 not-a-thin-wrapper rationale: the definition fixes the reusable swapped
--   primal-dual orientation used by saddle-gap proofs, not merely a renamed
--   single saddle-objective evaluation.
-- G0.5 structural-content rationale: the declaration packages the recognized
--   convex-concave saddle-gap comparison formula with stable unfolding and
--   saddle-objective bridge lemmas.
-- G0.5c thin-wrapper self-detect: clean - the body contains the full two-point
--   comparison invariant and the API relates it to two saddle objective values.
-- G0.5d minimal-hypothesis check: all already minimal; no global continuity,
--   convexity, measurability, positivity, completeness, or finite-dimensional
--   hypotheses are used.

/-- Two-point saddle-gap comparison for a bilinear convex-concave objective.

For a saddle/Lagrangian value `L x y = hatf x + ⟪Aeval x, y⟫ - hatg y`,
`saddleGapComparison hatf Aeval hatg zTilde z` is the swapped comparison
`L zTilde.1 z.2 - L z.1 zTilde.2`.

Layer: Model | Concept: Objective
Proof: (definitional construction; two-point swapped saddle/Lagrangian
  comparison for a primal-dual pair)
Source: convex-concave saddle-point and Lagrangian gap models over real Hilbert
  spaces
Used in: stochastic accelerated primal-dual gap maximization over feasible
  comparison points
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def saddleGapComparison
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (zTilde z : X × Y) : ℝ :=
  hatf zTilde.1 + ⟪Aeval zTilde.1, z.2⟫_ℝ - hatg z.2 -
    hatf z.1 - ⟪Aeval z.1, zTilde.2⟫_ℝ + hatg zTilde.2

/-- The saddle-gap comparison unfolds to the explicit swapped bilinear formula.

Layer: Model | Gap: Level 0 (saddle-gap comparison unfolding)
Proof: by rfl after unfolding `saddleGapComparison`.
Source: convex-concave saddle-point and Lagrangian gap models over real Hilbert
  spaces
Used in: stochastic accelerated primal-dual algebraic normalization of the
  feasible comparison value
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem saddleGapComparison_def
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (zTilde z : X × Y) :
    saddleGapComparison hatf Aeval hatg zTilde z =
      hatf zTilde.1 + ⟪Aeval zTilde.1, z.2⟫_ℝ - hatg z.2 -
        hatf z.1 - ⟪Aeval z.1, zTilde.2⟫_ℝ + hatg zTilde.2 := by
  rfl

/-- The saddle-gap comparison agrees with its expanded swapped bilinear formula.

Layer: Model | Gap: Level 0 (saddle objective comparison bridge)
Proof: unfold `saddleGapComparison` and normalize the real additive expression.
Source: convex-concave saddle-point and Lagrangian gap models over real Hilbert
  spaces
Used in: stochastic accelerated primal-dual rewrites between the paper's
  expanded `Q` formula and named saddle-objective values
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem saddleGapComparison_eq_saddle_objective_sub
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (zTilde z : X × Y) :
    saddleGapComparison hatf Aeval hatg zTilde z =
      (hatf zTilde.1 + ⟪Aeval zTilde.1, z.2⟫_ℝ - hatg z.2) -
        (hatf z.1 + ⟪Aeval z.1, zTilde.2⟫_ℝ - hatg zTilde.2) := by
  simp [saddleGapComparison]
  ring

/-- The saddle-gap comparison vanishes when both comparison arguments coincide.

Layer: Model | Gap: Level 0 (diagonal saddle-gap normalization)
Proof: unfold `saddleGapComparison` and cancel the equal saddle terms by ring
  arithmetic.
Source: convex-concave saddle-point and Lagrangian gap models over real Hilbert
  spaces
Used in: stochastic accelerated primal-dual proof that the feasible maximum gap
  is nonnegative by evaluating at the diagonal comparison point
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem saddleGapComparison_self
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (z : X × Y) :
    saddleGapComparison hatf Aeval hatg z z = 0 := by
  rw [saddleGapComparison_def]
  ring

@[deprecated saddleGapComparison (since := "2026-06-14")]
noncomputable abbrev saddle_gap_comparison
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (zTilde z : X × Y) : ℝ :=
  saddleGapComparison hatf Aeval hatg zTilde z

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGapComparison_left_lowerSemicontinuous.lean
-- Generalization plan (G0):
-- G0.1 naming: saddle_gap_comparison_left_lowerSemicontinuous
--   (orig was: saddleGapComparison_left_lowerSemicontinuous /
--   Q_left_lowerSemicontinuous)
-- G0.2 typeclass level used:
--   E: XSpace uses [NormedAddCommGroup] [NormedSpace ℝ] exactly for a
--     continuous linear map into the dual Hilbert block; YSpace uses
--     [NormedAddCommGroup] [InnerProductSpace ℝ] exactly for the real inner
--     product and product-space topology. No finite-dimensional structure is
--     used.
--   measure: none, this is a deterministic topological saddle-gap section fact.
--   convexity: none, the proof only needs continuity/lower-semicontinuity
--     hypotheses on the objective components over the feasible carriers.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual gap-value semicontinuity before
--      applying compact supremum/measurability arguments.
--   2. stochastic mirror-prox or primal-dual mirror-descent saddle-gap
--      analyses with a continuous primal model and lower-semicontinuous dual
--      penalty.
-- G0.4 search trace:
--   queries: ["saddle gap lower semicontinuous",
--     "LowerSemicontinuousOn restrict product continuous inner",
--     "lower semicontinuous saddle gap comparison bilinear"]
--   top hits: ["SOptLib.saddle_gap_comparison",
--     "SOptLib.continuous_saddle_objective", "LowerSemicontinuousOn.add",
--     "LowerSemicontinuous.add", "lowerSemicontinuous_sum",
--     "lowerSemicontinuous_restrict_iff"]
--   coverage: partial — existing SOptLib names the comparison formula and
--     Mathlib supplies semicontinuity composition/addition/restriction APIs,
--     but no hit subsumes the feasible left-section theorem for a bilinear
--     saddle-gap comparison.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the recurring
--   product-carrier section argument, combining projection maps, lower
--   semicontinuity transport, continuous affine coupling, and subtype
--   restriction into one reusable saddle-gap invariant.
-- G0.5 structural-content rationale: the declaration proves an analytic
--   property of the named two-point saddle-gap comparison rather than exposing
--   or renaming its formula.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step proof content
--   using component lsc transport, continuous affine terms, addition, and
--   restriction to a feasible subtype.
-- G0.5d minimal-hypothesis check: primal continuity is used globally on X,
--   dual lower-semicontinuity globally on Y, and A as a continuous linear map;
--   no stronger smoothness, convexity, compactness, completeness, measure, or
--   finite-dimensional hypotheses are present.

/-- A fixed right comparison section of the bilinear saddle-gap comparison is
lower-semicontinuous on the feasible product subtype.

If the primal objective is continuous on `X`, the dual penalty is
lower-semicontinuous on `Y`, and the coupling map is continuous linear, then
`zTilde ↦ saddle_gap_comparison hatf A hatg zTilde z` is lower-semicontinuous
after restricting `zTilde` to `X ×ˢ Y`.

Layer: Model | Gap: Level 1 (saddle-gap section lower-semicontinuity)
Proof: transport component lower-semicontinuity through product projections,
  add the continuous affine coupling block, and pass from `LowerSemicontinuousOn`
  over `X ×ˢ Y` to the subtype restriction.
Source: Mathlib semicontinuity APIs for sums, continuous maps, product
  projections, continuous linear maps, and set restrictions
Used in: stochastic accelerated primal-dual gap maximization and
  lower-semicontinuity of feasible saddle-gap sections
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem saddleGapComparison_left_lowerSemicontinuous
    {XSpace YSpace : Type*}
    [NormedAddCommGroup XSpace] [NormedSpace ℝ XSpace]
    [NormedAddCommGroup YSpace] [InnerProductSpace ℝ YSpace]
    {X : Set XSpace} {Y : Set YSpace}
    {hatf : XSpace → ℝ} {hatg : YSpace → ℝ} (A : XSpace →L[ℝ] YSpace)
    (hhatf_cont : ContinuousOn hatf X)
    (hhatg_lsc : LowerSemicontinuousOn hatg Y)
    (z : {w : XSpace × YSpace // w ∈ X ×ˢ Y}) :
    LowerSemicontinuous
      (fun zTilde : {w : XSpace × YSpace // w ∈ X ×ˢ Y} =>
        saddleGapComparison hatf A hatg zTilde.1 z.1) := by
  let qAmb : XSpace × YSpace → ℝ :=
    fun zTilde =>
      saddleGapComparison hatf A hatg zTilde z.1
  have hhatf_lsc : LowerSemicontinuousOn hatf X :=
    hhatf_cont.lowerSemicontinuousOn
  have hhatf_lsc_fst :
      LowerSemicontinuousOn (fun w : XSpace × YSpace => hatf w.1) (X ×ˢ Y) := by
    have hmaps : Set.MapsTo (fun w : XSpace × YSpace => w.1) (X ×ˢ Y) X := by
      intro w hw
      exact hw.1
    simpa [Function.comp_def] using hhatf_lsc.comp continuous_fst.continuousOn hmaps
  have hhatg_lsc_snd :
      LowerSemicontinuousOn (fun w : XSpace × YSpace => hatg w.2) (X ×ˢ Y) := by
    have hmaps : Set.MapsTo (fun w : XSpace × YSpace => w.2) (X ×ˢ Y) Y := by
      intro w hw
      exact hw.2
    simpa [Function.comp_def] using hhatg_lsc.comp continuous_snd.continuousOn hmaps
  have haff_cont : ContinuousOn
      (fun w : XSpace × YSpace =>
        ⟪A w.1, z.1.2⟫_ℝ - hatg z.1.2 - hatf z.1.1 -
          ⟪A z.1.1, w.2⟫_ℝ) (X ×ˢ Y) := by
    have hAw : Continuous (fun w : XSpace × YSpace => A w.1) :=
      A.continuous.comp continuous_fst
    have hleft : Continuous (fun w : XSpace × YSpace => ⟪A w.1, z.1.2⟫_ℝ) :=
      hAw.inner continuous_const
    have hright : Continuous (fun w : XSpace × YSpace => ⟪A z.1.1, w.2⟫_ℝ) :=
      continuous_const.inner continuous_snd
    exact (((hleft.sub continuous_const).sub continuous_const).sub hright).continuousOn
  have hq_lsc : LowerSemicontinuousOn qAmb (X ×ˢ Y) := by
    have hsum := (hhatf_lsc_fst.add haff_cont.lowerSemicontinuousOn).add hhatg_lsc_snd
    simpa [qAmb, saddleGapComparison, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hsum
  have hrestrict : LowerSemicontinuous ((X ×ˢ Y).restrict qAmb) :=
    (lowerSemicontinuous_restrict_iff (s := X ×ˢ Y) (f := qAmb)).2 hq_lsc
  simpa only [Set.restrict, qAmb] using hrestrict

@[deprecated saddleGapComparison_left_lowerSemicontinuous (since := "2026-06-14")]
theorem Q_left_lowerSemicontinuous
    {XSpace YSpace : Type*}
    [NormedAddCommGroup XSpace] [NormedSpace ℝ XSpace]
    [NormedAddCommGroup YSpace] [InnerProductSpace ℝ YSpace]
    {X : Set XSpace} {Y : Set YSpace}
    {hatf : XSpace → ℝ} {hatg : YSpace → ℝ} (A : XSpace →L[ℝ] YSpace)
    (hhatf_cont : ContinuousOn hatf X)
    (hhatg_lsc : LowerSemicontinuousOn hatg Y)
    (z : {w : XSpace × YSpace // w ∈ X ×ˢ Y}) :
    LowerSemicontinuous
      (fun zTilde : {w : XSpace × YSpace // w ∈ X ×ˢ Y} =>
        saddleGapComparison hatf A hatg zTilde.1 z.1) :=
  saddleGapComparison_left_lowerSemicontinuous A hhatf_cont hhatg_lsc z

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGapValue_eq_isMax_value.lean
/-- An attained comparison-point maximum realizes the fixed-base saddle-gap
value.

If every value of the section `z ↦ Q zTilde z` is bounded by its value at
`zMax`, then the value-level saddle gap is exactly `Q zTilde zMax`.

Layer: Model | Gap: Level 0 (saddle-gap value attained at a selected maximum)
Proof: use the selected maximizer as a nonempty witness, derive boundedness of
  the value range from pointwise maximality, then combine `ciSup_le` and
  `le_ciSup`.
Source: convex-concave saddle-point gap functions and Mathlib indexed
  supremum/order-bound APIs
Used in: stochastic accelerated primal-dual feasible saddle-gap maximum
  identification after selecting an argmax
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem saddleGapValue_eq_isMax_value {Z : Type*} (Q : Z → Z → ℝ)
    (zTilde zMax : Z) (hmax : ∀ z : Z, Q zTilde z ≤ Q zTilde zMax) :
    saddleGap Q zTilde = Q zTilde zMax := by
  letI : Nonempty Z := ⟨zMax⟩
  have hbdd : BddAbove (Set.range fun z : Z => Q zTilde z) := by
    refine ⟨Q zTilde zMax, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hmax z
  unfold saddleGap
  apply le_antisymm
  · exact ciSup_le hmax
  · exact le_ciSup hbdd zMax

@[deprecated saddleGapValue_eq_isMax_value (since := "2026-06-14")]
theorem gapValue_eq_gapMaximizer_value {Z : Type*} (Q : Z → Z → ℝ)
    (zTilde zMax : Z) (hmax : ∀ z : Z, Q zTilde z ≤ Q zTilde zMax) :
    saddleGap Q zTilde = Q zTilde zMax :=
  saddleGapValue_eq_isMax_value Q zTilde zMax hmax

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGap_lowerSemicontinuous_of_sections.lean
/-- A saddle-gap value is lower-semicontinuous when every comparison section is.

For a comparison kernel `Q`, if each section `zTilde ↦ Q zTilde z` is
lower-semicontinuous and each feasible value section is bounded above, then
the fixed-base value-level gap `saddleGapValue Q` is lower-semicontinuous.

Layer: Model | Gap: Level 1 (saddle-gap value lower-semicontinuity)
Proof: unfold the named saddle-gap value to its indexed supremum form and
  apply Mathlib's lower-semicontinuity theorem for bounded real `ciSup`.
Source: Mathlib lower-semicontinuity API for conditionally complete linear
  orders and convex-concave saddle-point gap functions
Used in: stochastic accelerated primal-dual value-level gap measurability from
  section-wise feasible saddle-comparison regularity
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem saddleGap_lowerSemicontinuous_of_sections
    {Z : Type*} [TopologicalSpace Z] (Q : Z → Z → ℝ)
    (hbdd : ∀ zTilde : Z, BddAbove (Set.range fun z : Z => Q zTilde z))
    (hsections : ∀ z : Z, LowerSemicontinuous fun zTilde : Z => Q zTilde z) :
    LowerSemicontinuous (saddleGapValue Q) := by
  simpa [saddleGapValue] using
    lowerSemicontinuous_ciSup hbdd (fun z : Z => hsections z)

@[deprecated saddleGap_lowerSemicontinuous_of_sections (since := "2026-06-14")]
theorem gap_lowerSemicontinuous
    {Z : Type*} [TopologicalSpace Z] (Q : Z → Z → ℝ)
    (hbdd : ∀ zTilde : Z, BddAbove (Set.range fun z : Z => Q zTilde z))
    (hsections : ∀ z : Z, LowerSemicontinuous fun zTilde : Z => Q zTilde z) :
    LowerSemicontinuous (saddleGapValue Q) :=
  saddleGap_lowerSemicontinuous_of_sections Q hbdd hsections

-- Promoted from .sgd_phase3_staging/SOptLib/Model/saddleGap_nonneg_of_diag_eq_zero.lean
/-- A fixed-base saddle gap is nonnegative when the comparison kernel vanishes
on the diagonal point.

For a real comparison kernel `Q`, the saddle-gap value
`saddleGap Q zTilde = sup_z Q zTilde z` is at least the diagonal section value.
If that diagonal value is zero, the gap is nonnegative.

Layer: Model | Gap: Level 0 (saddle-gap nonnegativity from zero diagonal)
Proof: unfold the named saddle-gap value to an indexed supremum and apply
  Mathlib's real `iSup` nonnegativity theorem using the diagonal point as the
  witnessing nonnegative comparison value.
Source: convex-concave saddle-point gap functions and Mathlib real indexed
  supremum order API
Used in: stochastic accelerated primal-dual conversion from diagonal-zero
  comparison kernels to nonnegative feasible saddle gaps
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem saddleGap_nonneg_of_diag_eq_zero {Z : Type*} (Q : Z → Z → ℝ) (zTilde : Z)
    (hdiag : Q zTilde zTilde = 0) :
    0 ≤ saddleGap Q zTilde := by
  rw [saddleGap]
  exact Real.iSup_nonneg' ⟨zTilde, by simp [hdiag]⟩

@[deprecated saddleGap_nonneg_of_diag_eq_zero (since := "2026-06-14")]
theorem gap_nonneg {Z : Type*} (Q : Z → Z → ℝ) (zTilde : Z)
    (hdiag : Q zTilde zTilde = 0) :
    0 ≤ saddleGap Q zTilde :=
  saddleGap_nonneg_of_diag_eq_zero Q zTilde hdiag

end SOptLib


-- Generalization plan (G0):
-- concept/name: right-section upper semicontinuity of a saddle-gap comparison; orig was saddle_gap_upperSemicontinuousOn / local `husc` block
-- generality used: arbitrary topological primal carrier, real Hilbert dual carrier, lower-semicontinuous objective components, and a continuous coupling evaluator on the primal carrier; no measure, convexity, compactness, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: stochastic primal-dual and mirror-prox gap maximization, where a fixed feasible base point defines a comparison section over product feasible points and compact attainment needs upper-semicontinuity
-- counterargument checked: Mathlib has upper-semicontinuity under sums and negated lower-semicontinuity, and SOptLib has the left-section lower-semicontinuity theorem; neither covers the fixed-base right section with the objective signs reversed
-- coverage search: queried `UpperSemicontinuousOn LowerSemicontinuousOn continuous neg add`, `upper semicontinuous on sum of continuous and negative lower semicontinuous functions`, and saddle-gap comparison hits; coverage is partial, not duplicate
-- minimal hypotheses: generalized the continuous linear map to any coupling evaluator continuous on `X`; all other assumptions are pointwise carrier semicontinuity hypotheses used directly in the proof

open scoped InnerProductSpace

namespace SOptLib

/-- A fixed left argument of the bilinear saddle-gap comparison is
upper-semicontinuous in the right comparison point on the feasible product set.

If the two objective components are lower-semicontinuous on their carriers and
the coupling evaluator is continuous on the primal carrier, then
`z ↦ saddle_gap_comparison hatf Aeval hatg zTilde z` is upper-semicontinuous on
`X ×ˢ Y`.

Layer: Glue | Gap: Level 1 (saddle-gap right-section upper-semicontinuity)
Proof: transport lower-semicontinuity through product projections, turn the two
  negative objective terms into upper-semicontinuous terms, and add them to the
  continuous affine coupling block.
Source: Mathlib semicontinuity APIs for negation, sums, product projections,
  inner products, and continuous maps
Used in: stochastic accelerated primal-dual gap maximization over compact
  feasible comparison points
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem upperSemicontinuousOn_saddleGapComparison_right
    {XSpace YSpace : Type*}
    [TopologicalSpace XSpace]
    [NormedAddCommGroup YSpace] [InnerProductSpace ℝ YSpace]
    {X : Set XSpace} {Y : Set YSpace}
    {hatf : XSpace → ℝ} {Aeval : XSpace → YSpace} {hatg : YSpace → ℝ}
    (hhatf_lsc : LowerSemicontinuousOn hatf X)
    (hA_cont : ContinuousOn Aeval X)
    (hhatg_lsc : LowerSemicontinuousOn hatg Y)
    (zTilde : XSpace × YSpace) :
    UpperSemicontinuousOn
      (fun z : XSpace × YSpace => saddle_gap_comparison hatf Aeval hatg zTilde z)
      (X ×ˢ Y) := by
  have hhatf_lsc_fst :
      LowerSemicontinuousOn (fun z : XSpace × YSpace => hatf z.1) (X ×ˢ Y) := by
    have hmaps : Set.MapsTo (fun z : XSpace × YSpace => z.1) (X ×ˢ Y) X := by
      intro z hz
      exact hz.1
    simpa [Function.comp_def] using hhatf_lsc.comp continuous_fst.continuousOn hmaps
  have hhatg_lsc_snd :
      LowerSemicontinuousOn (fun z : XSpace × YSpace => hatg z.2) (X ×ˢ Y) := by
    have hmaps : Set.MapsTo (fun z : XSpace × YSpace => z.2) (X ×ˢ Y) Y := by
      intro z hz
      exact hz.2
    simpa [Function.comp_def] using hhatg_lsc.comp continuous_snd.continuousOn hmaps
  have hA_cont_fst :
      ContinuousOn (fun z : XSpace × YSpace => Aeval z.1) (X ×ˢ Y) := by
    have hmaps : Set.MapsTo (fun z : XSpace × YSpace => z.1) (X ×ˢ Y) X := by
      intro z hz
      exact hz.1
    simpa [Function.comp_def] using hA_cont.comp continuous_fst.continuousOn hmaps
  have hneg_antitone : Antitone (fun r : ℝ => -r) := by
    intro a b hab
    exact neg_le_neg hab
  have husc_neg_hatf :
      UpperSemicontinuousOn (fun z : XSpace × YSpace => -hatf z.1) (X ×ˢ Y) := by
    simpa [Function.comp_def] using
      (continuous_neg.comp_lowerSemicontinuousOn_antitone hhatf_lsc_fst hneg_antitone)
  have husc_neg_hatg :
      UpperSemicontinuousOn (fun z : XSpace × YSpace => -hatg z.2) (X ×ˢ Y) := by
    simpa [Function.comp_def] using
      (continuous_neg.comp_lowerSemicontinuousOn_antitone hhatg_lsc_snd hneg_antitone)
  have hcont_affine : ContinuousOn
      (fun z : XSpace × YSpace =>
        hatf zTilde.1 + ⟪Aeval zTilde.1, z.2⟫_ℝ -
          ⟪Aeval z.1, zTilde.2⟫_ℝ + hatg zTilde.2) (X ×ˢ Y) := by
    exact ((continuousOn_const.add ((continuous_const.inner continuous_snd).continuousOn)).sub
      (hA_cont_fst.inner continuousOn_const)).add continuousOn_const
  have husc_affine : UpperSemicontinuousOn
      (fun z : XSpace × YSpace =>
        hatf zTilde.1 + ⟪Aeval zTilde.1, z.2⟫_ℝ -
          ⟪Aeval z.1, zTilde.2⟫_ℝ + hatg zTilde.2) (X ×ˢ Y) :=
    hcont_affine.upperSemicontinuousOn
  have hsum := (husc_affine.add husc_neg_hatg).add husc_neg_hatf
  simpa [saddle_gap_comparison, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

end SOptLib
