import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: checked adaptive projected update relation; orig was `IsWellDefinedProjectedUpdate`.
-- generality used: an additive commutative real module for the iterate space, an abstract metric carrier, and pointwise square-root, quotient, metric, and weighted-projection contracts; no measure, convexity, smoothness, oracle, or finite-dimensional assumptions are needed.
-- portable call pattern: adaptive projected-gradient and Adam-family steps choose a square-root witness, certify the coordinate quotient, form the affine trial point, and apply a notation-domain-aware weighted projection while changing the feasible set, step size, direction data, accumulator, and metric representation.
-- counterargument checked: not paper-local traceability because the declaration is a reusable relation over arbitrary real modules and property-shaped contracts; not a caller-side expression because it packages the common existential witness and update boundary. It does not duplicate Mathlib or the existing feasible-argmin API.
-- coverage search: searched `checked adaptive projected update square root quotient weighted projection`, `coordinate square root quotient projection domain`, and `adaptive projected update relation`; hits were AMSGrad-local declarations plus the separate finite weighted-projection argmin relation, with no full reusable update contract.
-- minimal hypotheses: the additive real-module structure is sufficient for `x - alpha • direction`; the metric carrier and four contract arguments are explicit because their representations vary across adaptive projected algorithms.

/-- A checked adaptive projected update packages its square-root witness, quotient
certificate, affine trial point, and notation-domain-aware weighted projection.

The contract arguments keep the update boundary independent of a particular
coordinate representation or matrix metric: an algorithm supplies the
square-root and quotient relations, the metric built from the witness, and the
weighted-projection relation for that metric.

Layer: Model | Concept: checked adaptive projected update relation
Proof: (definitional construction; existential witness package for a quotient-based affine step followed by a weighted projection)
Source: Mathlib additive groups and real modules for the affine update algebra; weighted projection and adaptive-gradient update contracts from finite-dimensional optimization formalizations
Used in: projected adaptive-gradient steps that expose denominator nonzero and projection-domain obligations while changing the feasible set, accumulator, momentum direction, and metric representation
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/4
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def IsCheckedAdaptiveProjectedUpdate
    {E M : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Set E) (alpha : ℝ) (x m vhat xnext : E)
    (sqrt_spec : E → E → Prop)
    (quotient_spec : E → E → E → Prop)
    (projection_metric : E → M)
    (weighted_projection : Set E → M → E → E → Prop) : Prop :=
  ∃ sqrtVhat direction trial,
    sqrt_spec vhat sqrtVhat ∧
    quotient_spec m sqrtVhat direction ∧
    trial = x - alpha • direction ∧
    weighted_projection F (projection_metric sqrtVhat) trial xnext

@[simp]
theorem IsCheckedAdaptiveProjectedUpdate_def
    {E M : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Set E) (alpha : ℝ) (x m vhat xnext : E)
    (sqrt_spec : E → E → Prop)
    (quotient_spec : E → E → E → Prop)
    (projection_metric : E → M)
    (weighted_projection : Set E → M → E → E → Prop) :
    IsCheckedAdaptiveProjectedUpdate F alpha x m vhat xnext
      sqrt_spec quotient_spec projection_metric weighted_projection ↔
      ∃ sqrtVhat direction trial,
        sqrt_spec vhat sqrtVhat ∧
        quotient_spec m sqrtVhat direction ∧
        trial = x - alpha • direction ∧
        weighted_projection F (projection_metric sqrtVhat) trial xnext := by
  rfl

/-- A checked adaptive projected update remains valid when its component
contracts are weakened.  The same square-root witness, quotient direction,
affine trial point, and projected endpoint are retained. -/
theorem is_checked_adaptive_projected_update_of_implications
    {E M : Type*} [AddCommGroup E] [Module ℝ E]
    {F : Set E} {alpha : ℝ} {x m vhat xnext : E}
    {sqrt_spec sqrt_spec' : E → E → Prop}
    {quotient_spec quotient_spec' : E → E → E → Prop}
    {projection_metric : E → M}
    {weighted_projection weighted_projection' : Set E → M → E → E → Prop}
    (hsqrt : ∀ {vhat sqrtVhat}, sqrt_spec vhat sqrtVhat →
      sqrt_spec' vhat sqrtVhat)
    (hquotient : ∀ {m sqrtVhat direction},
      quotient_spec m sqrtVhat direction →
        quotient_spec' m sqrtVhat direction)
    (hprojection : ∀ {F metric trial xnext},
      weighted_projection F metric trial xnext →
        weighted_projection' F metric trial xnext)
    (hupdate :
      IsCheckedAdaptiveProjectedUpdate F alpha x m vhat xnext
        sqrt_spec quotient_spec projection_metric weighted_projection) :
    IsCheckedAdaptiveProjectedUpdate F alpha x m vhat xnext
      sqrt_spec' quotient_spec' projection_metric weighted_projection' := by
  rcases hupdate with
    ⟨sqrtVhat, direction, trial, hsqrt_spec, hquotient_spec, htrial,
      hprojection_spec⟩
  exact ⟨sqrtVhat, direction, trial, hsqrt hsqrt_spec,
    hquotient hquotient_spec, htrial, hprojection hprojection_spec⟩

end SOptLib
