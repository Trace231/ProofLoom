import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import SOptLib.Model.SimpleConvexTermExpr

namespace SOptLib

-- Generalization plan (G0):
-- G0.1 naming: IsSimpleConvexTermOn (orig was: IsAcsSimpleConvexTerm); the
--   new name removes the AC-SA acronym and names the optimization concept: a
--   structurally simple convex term on a feasible set.
-- G0.2 typeclass level used:
--   E: NormedAddCommGroup and InnerProductSpace over ℝ for the expression
--     grammar leaves; no completeness, measurability, or finite-dimensionality
--     is used by the structure itself.
--   measure: none in the structure; the carrier-measurability API only uses
--     MeasurableSpace and BorelSpace on E.
--   convexity: Mathlib ConvexOn ℝ X h, stored directly as the canonical
--     convexity predicate for an ambient function on a set.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated gradient descent simple composite penalty
--      setup and prox-objective convexity steps
--   2. variance-reduced accelerated gradient descent and stochastic mirror
--      descent composite-term known-structure/measurability assumptions
-- G0.4 search trace:
--   queries: ["simple convex term", "known structure agrees on convex on",
--     "function convex on a set with known expression agrees on set measurable subtype"]
--   top hits: ["SimpleConvexTermExpr", "SOptLib.ConvexOnCarrier",
--     "SOptLib.carrierConvexOn_sublevel_nullMeasurable_volume",
--     "SOptLib.ConvexOnCarrier.integral", "Mathlib.ConvexOn.congr",
--     "Mathlib.ConvexOn"]
--   coverage: partial — the hits cover the expression syntax, carrier
--     convexity, sublevel regularity, or equality transport, but none bundles a
--     known simple-term expression witness, agreement on a carrier, and
--     ConvexOn for an ambient penalty.
-- G0.4 not-a-thin-wrapper rationale: this structure exposes a reusable
--   invariant linking generated expression syntax, carrier agreement, and
--   Mathlib ConvexOn, rather than projecting or renaming one existing theorem.
-- G0.5 structural-content rationale: all three fields are load-bearing:
--   the expression witness gives regularity, agreement connects it to h on X,
--   and convexOn supplies the convex-analysis assumption used in descent proofs.
-- G0.5c thin-wrapper self-detect: clean — the body is a bundled predicate with
--   a derived measurability theorem; it is not a direct single-lemma alias.
-- G0.5d minimal-hypothesis check: all already minimal; the structure has no
--   global analytic hypotheses beyond ConvexOn, and carrier_measurable adds
--   only the point-set measurability classes needed by its conclusion.

/-- Structurally simple convex real-valued term on a feasible set.

The predicate records a generated simple-term expression, its agreement with
the ambient penalty on the carrier `X`, and the Mathlib convexity assumption
used by composite stochastic-optimization proofs.

Layer: Model | Concept: Objective
Proof: (definitional construction; simple expression witness plus carrier
  agreement and Mathlib `ConvexOn` for the represented penalty)
Source: Convex-composite optimization models and Mathlib convex-analysis APIs
Used in: stochastic accelerated gradient descent composite penalty setup,
  carrier measurability, and prox-objective convexity steps
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
structure IsSimpleConvexTermOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (h : E → ℝ) where
  knownStructure : SimpleConvexTermExpr E
  agreesOn : ∀ x, x ∈ X → knownStructure.eval x = h x
  convexOn : ConvexOn ℝ X h

namespace IsSimpleConvexTermOn

/-- Convexity projection from a structurally simple convex term.

Layer: Model | Gap: Level 0 (simple-term convexity projection)
Proof: project the stored Mathlib `ConvexOn` field from the bundled simple-term
  predicate.
Source: Mathlib convex-analysis APIs for `ConvexOn`
Used in: stochastic accelerated gradient descent Jensen and prox-objective
  convexity steps for the simple composite penalty
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {h : E → ℝ}
    (hsimple : IsSimpleConvexTermOn X h) :
    ConvexOn ℝ X h :=
  hsimple.convexOn

/-- Carrier measurability from a structurally simple expression witness.

If `h` agrees on `X` with a generated simple-term expression, then the carrier
restriction of `h` is measurable because generated expressions are continuous.

Layer: Model | Gap: Level 0 (simple-term carrier measurability)
Proof: restrict the continuous generated expression to the carrier subtype,
  then rewrite by the agreement field on every feasible point.
Source: Mathlib Borel measurability of continuous maps and subtype restriction
  measurability
Used in: stochastic accelerated gradient descent composite penalty integrability
  and measurable carrier-objective construction
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem carrier_measurable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {X : Set E} {h : E → ℝ}
    (hsimple : IsSimpleConvexTermOn X h) :
    Measurable (fun x : {x : E // x ∈ X} => h x.1) := by
  have hm : Measurable
      (fun x : {x : E // x ∈ X} => hsimple.knownStructure.eval x.1) :=
    Set.measurable_restrict_apply X hsimple.knownStructure.continuous.measurable
  convert hm using 1
  ext x
  exact (hsimple.agreesOn x.1 x.2).symm

end IsSimpleConvexTermOn

end SOptLib
