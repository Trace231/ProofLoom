import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- G0.1 naming: SimpleConvexTermExpr (orig was: AcsSimpleTermExpr); the new name
--   removes the AC-SA acronym and describes the reusable generated expression
--   grammar for simple convex/composite terms.
-- G0.2 typeclass level used:
--   E: NormedAddCommGroup and InnerProductSpace over ℝ; the evaluator uses the
--     norm and real inner product, but not completeness, measurability,
--     second-countability, or finite-dimensionality.
--   measure: none; the declaration is deterministic model syntax and regularity.
--   convexity: none in the grammar; convexity assumptions on the represented
--     carrier function remain separate because signed scalar multiplication can
--     destroy convexity.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated gradient descent simple composite-term known
--      structure and carrier measurability bridge
--   2. stochastic mirror descent / variance-reduced mirror descent composite
--      objective simple-term regularity for structurally continuous penalties
-- G0.4 search trace:
--   queries: ["simple convex term", "continuous norm affine max expression",
--     "inductively generated expressions from constants norm affine addition scalar multiplication max are continuous and Lipschitz"]
--   top hits: ["carrierConvexOn_sublevel_nullMeasurable_volume",
--     "convexOnCarrier_segment_sub_le_mul_sub", "sublevel_nullMeasurableSet_volume",
--     "exists_nonneg_norm_bound_of_isCompact_of_continuousOn",
--     "canonicalDualNorm_continuous", "lipschitzWith_max",
--     "lipschitzWith_iff_norm_sub_le"]
--   coverage: partial — hits cover convex sublevel regularity, compact
--     continuous bounds, or primitive Lipschitz facts, but none defines a
--     finite expression grammar with evaluator plus structural continuity and
--     global Lipschitz certificates.
-- G0.4 not-a-thin-wrapper rationale: the inductive declaration packages a
--   reusable expression syntax and two structural induction invariants rather
--   than renaming a single Mathlib or SOptLib theorem.
-- G0.5 structural-content rationale: constructors, evaluator, continuity, and
--   Lipschitz proofs form a load-bearing model API for known-structure simple
--   terms.
-- G0.5c thin-wrapper self-detect: clean — the body contains a new inductive
--   grammar and multi-case structural induction proofs, not a single existing
--   lemma call.
-- G0.5d minimal-hypothesis check: all already minimal; no pointwise/global
--   analytic hypotheses are introduced, and the typeclasses are exactly those
--   needed for norm and inner-product leaves.

/-- Finite expression grammar for structurally simple real-valued terms on a Hilbert space.

The grammar records the common optimization leaves `constant`, ambient norm,
affine functional, finite sums, scalar multiples, and pointwise maxima. It is
used as a known-structure witness for composite penalties whose analytic
regularity is derived by structural recursion.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite syntax tree for simple composite
  objective terms)
Source: Convex-composite optimization models and Mathlib norm/inner-product
  primitives for real Hilbert spaces
Used in: stochastic accelerated gradient descent simple composite-term known
  structure and mirror-descent composite objective regularity
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
inductive SimpleConvexTermExpr (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  | const : ℝ → SimpleConvexTermExpr E
  | norm : SimpleConvexTermExpr E
  | affine : E → ℝ → SimpleConvexTermExpr E
  | add : SimpleConvexTermExpr E → SimpleConvexTermExpr E → SimpleConvexTermExpr E
  | smul : ℝ → SimpleConvexTermExpr E → SimpleConvexTermExpr E
  | max : SimpleConvexTermExpr E → SimpleConvexTermExpr E → SimpleConvexTermExpr E

namespace SimpleConvexTermExpr

/-- Evaluation of a simple term expression in the ambient Hilbert space.

The evaluator interprets constants, the ambient norm, affine functionals,
addition, scalar multiplication, and pointwise maximum as real-valued maps.

Layer: Model | Concept: Objective
Proof: (definitional construction; recursive interpretation of the expression
  grammar as a real-valued ambient function)
Source: Mathlib real Hilbert-space norm and inner-product APIs
Used in: stochastic accelerated gradient descent simple composite-term carrier
  agreement and measurability bridges
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def eval
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    SimpleConvexTermExpr E → E → ℝ
  | const c => fun _ => c
  | norm => fun x => ‖x‖
  | affine g c => fun x => ⟪g, x⟫_ℝ + c
  | add e₁ e₂ => fun x => eval e₁ x + eval e₂ x
  | smul c e => fun x => c * eval e x
  | max e₁ e₂ => fun x => Max.max (eval e₁ x) (eval e₂ x)

/-- Every generated simple-term expression evaluates to a continuous function.

Layer: Model | Gap: Level 0 (simple-term structural continuity)
Proof: structural induction over the expression grammar; continuity is closed
  under constants, norm, affine inner-product maps, addition, scalar
  multiplication, and pointwise maximum.
Source: Mathlib topology of normed groups, real inner products, and continuous
  lattice operations
Used in: stochastic accelerated gradient descent simple composite-term carrier
  measurability and mirror-descent composite objective regularity
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ e : SimpleConvexTermExpr E, Continuous e.eval
  | const c => by
      simpa [eval] using (continuous_const : Continuous fun _ : E => c)
  | norm => by
      simpa [eval] using (continuous_id.norm : Continuous fun x : E => ‖x‖)
  | affine g c => by
      have h : Continuous (fun x : E => ⟪g, x⟫_ℝ + c) := by
        fun_prop
      simpa [eval] using h
  | add e₁ e₂ => by
      simpa [eval] using e₁.continuous.add e₂.continuous
  | smul c e => by
      simpa [eval] using e.continuous.const_mul c
  | max e₁ e₂ => by
      simpa [eval] using e₁.continuous.max e₂.continuous

/-- Every generated simple-term expression has a global Hilbert-norm Lipschitz bound.

The constant is produced structurally: constants have bound `0`, the norm leaf
has bound `1`, affine leaves have bound `‖g‖`, sums add constants, scalar
multiples scale by `|c|`, and maxima use the sum of the two branch constants.

Layer: Model | Gap: Level 1 (simple-term structural Lipschitz bound)
Proof: structural induction over the expression grammar; use the reverse
  triangle inequality for the norm leaf, Cauchy-Schwarz for affine leaves, and
  the real maximum difference bound for pointwise maxima.
Source: Mathlib normed-space Lipschitz estimates, real Hilbert-space
  Cauchy-Schwarz, and ordered-ring maximum inequalities
Used in: stochastic accelerated gradient descent simple composite-term bounded
  variation estimates and composite mirror-descent penalty regularity
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem exists_lipschitz_eval
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : SimpleConvexTermExpr E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, |e.eval x - e.eval y| ≤ K * ‖x - y‖ := by
  induction e with
  | const c =>
      refine ⟨0, by norm_num, ?_⟩
      intro x y
      simp [eval]
  | norm =>
      refine ⟨1, by norm_num, ?_⟩
      intro x y
      simpa [eval, one_mul] using abs_norm_sub_norm_le x y
  | affine g c =>
      refine ⟨‖g‖, norm_nonneg g, ?_⟩
      intro x y
      have hinner :
          |⟪g, x⟫_ℝ - ⟪g, y⟫_ℝ| ≤ ‖g‖ * ‖x - y‖ := by
        calc
          |⟪g, x⟫_ℝ - ⟪g, y⟫_ℝ| = |⟪g, x - y⟫_ℝ| := by
            rw [inner_sub_right]
          _ ≤ ‖g‖ * ‖x - y‖ := abs_real_inner_le_norm g (x - y)
      have hrewrite :
          |(⟪g, x⟫_ℝ + c) - (⟪g, y⟫_ℝ + c)| =
            |⟪g, x⟫_ℝ - ⟪g, y⟫_ℝ| := by
        ring_nf
      simpa [eval, hrewrite] using hinner
  | add e₁ e₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨K₁, hK₁, hLip₁⟩
      rcases ih₂ with ⟨K₂, hK₂, hLip₂⟩
      refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
      intro x y
      have hsum :
          |(e₁.eval x - e₁.eval y) + (e₂.eval x - e₂.eval y)| ≤
            K₁ * ‖x - y‖ + K₂ * ‖x - y‖ :=
        (abs_add_le _ _).trans (add_le_add (hLip₁ x y) (hLip₂ x y))
      simpa [eval, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  | smul c e ih =>
      rcases ih with ⟨K, hK, hLip⟩
      refine ⟨|c| * K, mul_nonneg (abs_nonneg c) hK, ?_⟩
      intro x y
      have hmul :
          |c * e.eval x - c * e.eval y| ≤ |c| * (K * ‖x - y‖) := by
        calc
          |c * e.eval x - c * e.eval y| = |c| * |e.eval x - e.eval y| := by
            rw [← mul_sub, abs_mul]
          _ ≤ |c| * (K * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (hLip x y) (abs_nonneg c)
      simpa [eval, mul_assoc] using hmul
  | max e₁ e₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨K₁, hK₁, hLip₁⟩
      rcases ih₂ with ⟨K₂, hK₂, hLip₂⟩
      refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
      intro x y
      have hmax :
          |Max.max (e₁.eval x) (e₂.eval x) -
              Max.max (e₁.eval y) (e₂.eval y)| ≤
            Max.max |e₁.eval x - e₁.eval y| |e₂.eval x - e₂.eval y| :=
        abs_max_sub_max_le_max _ _ _ _
      have hmax_le_sum :
          Max.max |e₁.eval x - e₁.eval y| |e₂.eval x - e₂.eval y| ≤
            K₁ * ‖x - y‖ + K₂ * ‖x - y‖ := by
        refine max_le ?_ ?_
        · exact (hLip₁ x y).trans (by nlinarith [hK₂, norm_nonneg (x - y)])
        · exact (hLip₂ x y).trans (by nlinarith [hK₁, norm_nonneg (x - y)])
      exact hmax.trans (by simpa [eval, add_mul] using hmax_le_sum)

end SimpleConvexTermExpr

end SOptLib
