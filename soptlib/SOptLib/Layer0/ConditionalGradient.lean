import Mathlib.Analysis.InnerProductSpace.Basic
import SOptLib.Glue.Algebra
import SOptLib.Model.ConditionalGradient

open scoped InnerProductSpace

namespace SOptLib.ConditionalGradient

/-- A Wolfe-gap value is bounded by an LMO model plus gradient-error diameter.

If `linearMinimizer G` minimizes the linear model with direction `G` over the
feasible set and all feasible displacements from `x` are bounded by `D`, then
the selected Wolfe gap at `x` for `grad` is at most the `G`-linear model gap
plus the norm of the gradient mismatch times `D`.

Layer: Layer0 | Gap: Level 1 (conditional-gradient Wolfe-gap surrogate bound)
Proof: expand the selected Wolfe-gap value, compare the selected feasible point
  against the LMO point for `G`, and control the remaining inner-product error
  by `abs_real_inner_le_norm` followed by the pointwise diameter bound.
Source: Frank-Wolfe conditional-gradient linear-oracle calculus, real Hilbert
  space Cauchy-Schwarz, and feasible-set diameter estimates
Used in: stochastic and finite-sum conditional-gradient descent proofs bounding
  true stationarity gaps by stochastic linear-model gaps plus estimator error
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/key_lemmas/0/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem wolfeGap_le_linearMinimizer_model_plus_gradient_error_mul_diameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (linearMinimizer : E → E)
    (linearMinimizer_is_argmin :
      ∀ g z : E, z ∈ X → ⟪g, linearMinimizer g⟫_ℝ ≤ ⟪g, z⟫_ℝ)
    (D : ℝ) (x G : E)
    (diameter_bound_at :
      ∀ y : E, y ∈ X → ‖x - y‖ ≤ D) :
    wolfeGap grad maximizer x ≤
      ⟪G, x - linearMinimizer G⟫_ℝ + ‖G - grad x‖ * D := by
  classical
  let z : {y : E // y ∈ X} := maximizer x
  let v : E := x - (z : E)
  have hmodel : ⟪G, v⟫_ℝ ≤ ⟪G, x - linearMinimizer G⟫_ℝ := by
    have hlmo : ⟪G, linearMinimizer G⟫_ℝ ≤ ⟪G, (z : E)⟫_ℝ :=
      linearMinimizer_is_argmin G (z : E) z.property
    simp [v, inner_sub_right]
    linarith
  have herr : -⟪G - grad x, v⟫_ℝ ≤ ‖G - grad x‖ * D := by
    have h_abs : -⟪G - grad x, v⟫_ℝ ≤ |⟪G - grad x, v⟫_ℝ| :=
      neg_le_abs _
    have h_cauchy :
        |⟪G - grad x, v⟫_ℝ| ≤ ‖G - grad x‖ * ‖v‖ :=
      abs_real_inner_le_norm (G - grad x) v
    have h_diam :
        ‖G - grad x‖ * ‖v‖ ≤ ‖G - grad x‖ * D := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [v, z] using diameter_bound_at (z : E) z.property)
        (norm_nonneg _)
    exact h_abs.trans (h_cauchy.trans h_diam)
  calc
    wolfeGap grad maximizer x = ⟪grad x, v⟫_ℝ := by
      simp [wolfeGap, z, v]
    _ = ⟪G, v⟫_ℝ - ⟪G - grad x, v⟫_ℝ := by
      rw [sub_eq_add_neg, inner_sub_left]
      ring
    _ ≤ ⟪G, x - linearMinimizer G⟫_ℝ + ‖G - grad x‖ * D := by
      linarith

end SOptLib.ConditionalGradient

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Layer0/maxLinearModelGap_nonneg_of_mem.lean
/-!
-- Generalization plan (G0):
-- concept/name: maxLinearModelGap_nonneg_of_mem exposes nonnegativity of the
--   selected shifted linear-model gap; orig was cndGGap_nonneg_of_mem, renamed
--   away from CndG and paper-local shifted subproblem notation.
-- generality used: arbitrary real inner-product normed additive group `E`, a
--   feasible set `X`, a model vector `G`, a current point, and a selected
--   maximizer; no measure, finite-dimensional, compactness, convexity,
--   smoothness, oracle, or filtration assumptions are used.
-- portable call pattern: conditional-gradient, Frank-Wolfe, projection-sliding,
--   and stochastic conditional-gradient proofs can compare a selected maximizer
--   of `y ↦ <G, current - y>` against the feasible current point to obtain
--   nonnegativity before weighted gap summation or stopping tests.
-- counterargument checked: not paper-local traceability because the statement
--   only uses a standard shifted linear model and Mathlib's `IsMaxOn`
--   certificate; not merely a pure rename because it packages the recurring
--   comparison-at-current step rather than restating an existing lemma.
-- coverage search: searched `max linear model nonnegative maximizer current
--   point inner`, catalog tokens `maxLinearModel`, `linear model`, `gap
--   nonneg`, and LeanSearch for maximum of an inner-product linear model; hits
--   `IsMaxOn` / `isMaxOn_iff` provide only the generic maximality predicate,
--   `SOptLib.ConditionalGradient.maxLinearModel` names the selected value, and
--   existing Layer0 hits bound max-linear values by LMO terms but do not prove
--   selected shifted-model nonnegativity.
-- minimal hypotheses: all already minimal; the proof uses only feasibility of
--   the current point and the pointwise maximum certificate specialized at that
--   current point.
-/

namespace SOptLib.ConditionalGradient

open scoped InnerProductSpace

/-- A selected shifted linear-model gap is nonnegative at feasible current points.

If `selected` maximizes `y ↦ ⟪G, current - y⟫` over the feasible set, then its
attained shifted linear-model value is at least the value at `current`, namely
zero, whenever `current` is feasible.

Layer: Layer0 | Gap: Level 0 (shifted linear-model gap nonnegativity)
Proof: specialize the `IsMaxOn` certificate to the feasible current point and
  simplify the self-displacement inner product to zero.
Source: Mathlib order extrema on sets and real inner-product subtraction algebra
Used in: conditional-gradient and Frank-Wolfe inner-loop Wolfe-gap
  nonnegativity before stopping tests and weighted finite-window summation
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem maxLinearModelGap_nonneg_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {G current selected : E}
    (hcurrent : current ∈ X)
    (hselected : IsMaxOn (fun y : E => ⟪G, current - y⟫_ℝ) X selected) :
    0 ≤ ⟪G, current - selected⟫_ℝ := by
  have hmax := (isMaxOn_iff.mp hselected) current hcurrent
  simpa using hmax

end SOptLib.ConditionalGradient


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Layer0/cndG_lineSearchQuotient_nonneg_of_current_mem.lean
/-!
-- Generalization plan (G0):
-- concept/name: cndG_lineSearchQuotient_nonneg_of_current_mem exposes
--   nonnegativity of the conditional-gradient line-search quotient induced by
--   a shifted linear-model maximizer; orig was
--   cndGStepsize_quotient_nonneg_of_current_mem, renamed away from the concrete
--   setup fields while retaining the conditional-gradient line-search concept.
-- generality used: arbitrary real inner-product normed additive group `E`, a
--   feasible set `X`, model parameters `g`, `u`, `β`, current point `ut`, and
--   selected point `v`; no measure, finite-dimensional, compactness,
--   convexity, smoothness, stochastic oracle, or filtration assumptions are
--   used.
-- portable call pattern: conditional-gradient, Frank-Wolfe, projection-sliding,
--   and stochastic conditional-gradient line-search proofs can supply a
--   shifted linear-model `IsMaxOn` certificate, current feasibility, positive
--   curvature, and nonzero displayed denominator; the quotient conclusion is
--   unchanged.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free apart from standard conditional-gradient terminology and
--   depends only on a pointwise linear-model optimality certificate; not a pure
--   wrapper because it combines the maximizer comparison, inner-product
--   sign-normalization, and positive-denominator division step used by
--   line-search proofs.
-- coverage search: searched catalog and symbols for `lineSearch quotient
--   nonnegative linear oracle current feasible denominator` and
--   `maxLinearModelGap_nonneg_of_mem line search quotient`; the closest hit
--   `maxLinearModelGap_nonneg_of_mem` proves only nonnegativity of the shifted
--   model value, while Mathlib/LeanSearch hits such as `div_nonneg` cover only
--   scalar division after the numerator and denominator signs are already
--   known.
-- minimal hypotheses: setup fields are reduced to `IsMaxOn`, `ut ∈ X`,
--   `0 < β`, and the exact nonzero denominator; all are used to obtain the
--   numerator sign or positive denominator.
-/

namespace SOptLib.ConditionalGradient

open scoped InnerProductSpace

/-- A shifted linear-oracle comparison gives a nonnegative line-search quotient.

If `v` maximizes the shifted conditional-gradient linear model
`x ↦ ⟪g + β • (ut - u), ut - x⟫` over the feasible set and the current point
`ut` is feasible, then the unclamped line-search quotient has nonnegative
numerator.  Positive curvature and a nonzero displayed denominator make the
whole quotient nonnegative.

Layer: Layer0 | Gap: Level 0 (conditional-gradient line-search quotient sign)
Proof: specialize the `IsMaxOn` certificate at the current feasible point,
  rewrite the shifted model value as the quotient numerator, and apply
  nonnegativity of division by the positive quadratic denominator.
Source: Frank-Wolfe conditional-gradient linear-oracle calculus, real
  inner-product subtraction algebra, and ordered-field division
Used in: conditional-gradient and Frank-Wolfe line-search proofs showing the
  lower endpoint of the clamped quotient is inactive at feasible current
  iterates
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem cndG_lineSearchQuotient_nonneg_of_current_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {g u : E} {β : ℝ} {ut v : E}
    (hut : ut ∈ X)
    (hselected : IsMaxOn (fun x : E => ⟪g + β • (ut - u), ut - x⟫_ℝ) X v)
    (hβ : 0 < β)
    (hden : β * ‖v - ut‖ ^ 2 ≠ 0) :
    0 ≤ ⟪β • (u - ut) - g, v - ut⟫_ℝ / (β * ‖v - ut‖ ^ 2) := by
  have hopt := (isMaxOn_iff.mp hselected) ut hut
  have hgap_nonneg : 0 ≤ ⟪g + β • (ut - u), ut - v⟫_ℝ := by
    simpa using hopt
  have hnum_nonneg : 0 ≤ ⟪β • (u - ut) - g, v - ut⟫_ℝ := by
    simpa [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, inner_smul_left, inner_smul_right, add_comm,
      add_left_comm, add_assoc] using hgap_nonneg
  have hnorm_ne : ‖v - ut‖ ^ 2 ≠ 0 := by
    intro hnorm
    exact hden (by simp [hnorm])
  have hnorm_pos : 0 < ‖v - ut‖ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg ‖v - ut‖) (Ne.symm hnorm_ne)
  have hden_pos : 0 < β * ‖v - ut‖ ^ 2 := mul_pos hβ hnorm_pos
  exact div_nonneg hnum_nonneg (le_of_lt hden_pos)

end SOptLib.ConditionalGradient


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Layer0/centeredQuadratic_residual_le_maxLinearModelGap.lean
/-!
-- Generalization plan (G0):
-- concept/name: centeredQuadratic_residual_le_maxLinearModelGap exposes the
--   standard comparison from a centered quadratic model residual to an attained
--   shifted max-linear-model gap; orig was cndG_gap_controls_phi_suboptimality,
--   renamed away from CndG and the paper's local `φ` notation.
-- generality used: arbitrary real inner-product normed additive group `E`, a
--   feasible set `X`, a linear coefficient `g`, a quadratic center, a current
--   point, a selected shifted-linear maximizer, a comparator, and a nonnegative
--   quadratic coefficient; no measure, finite-dimensionality, compactness,
--   convexity, smoothness, oracle, or filtration assumptions are used.
-- portable call pattern: CndG, Frank-Wolfe with proximal regularization, and
--   proximal-linear conditional-gradient proofs call this after an inner
--   linear oracle maximizes `y ↦ <g + β • (current - center), current - y>`,
--   while `g`, `center`, `current`, `β`, and the feasible comparator vary.
-- counterargument checked: not paper-local traceability because the statement
--   uses only a named centered quadratic model and a Mathlib `IsMaxOn`
--   certificate; not a caller-side expression because it packages the recurring
--   shifted-gradient identity plus the nonnegative quadratic remainder drop.
-- coverage search: searched catalog/symbols for `maxLinearModelGap`, `centered
--   quadratic residual`, `linear model gap`, and LeanSearch for centered
--   quadratic residual controlled by a linear-model gap. Existing hits cover
--   max-linear gap nonnegativity, Wolfe-gap estimator-error bounds, and
--   centered quadratic Bregman nonnegativity, but none states this residual to
--   shifted max-linear gap comparison.
-- minimal hypotheses: finite-dimensionality, probability, compactness,
--   convexity, smoothness, and algorithm setup fields were removed; the proof
--   uses only comparator feasibility, pointwise shifted linear maximality, and
--   `0 ≤ β`.
-/

open scoped InnerProductSpace

namespace SOptLib.ConditionalGradient

/-- A centered quadratic model residual is controlled by a shifted max-linear gap.

If `selected` maximizes the shifted linear model
`y ↦ ⟪g + β • (current - center), current - y⟫` over the feasible set, then
the residual of `x ↦ ⟪g, x⟫ + β / 2 * ‖x - center‖ ^ 2` from `current` to any
feasible comparator is at most the attained shifted max-linear-model value.

Layer: Layer0 | Gap: Level 0 (centered quadratic residual to max-linear gap)
Proof: expand the centered quadratic residual as the shifted linear model at
  the comparator minus the nonnegative quadratic remainder, then specialize the
  `IsMaxOn` certificate and drop the remainder using ordered real algebra.
Source: Frank-Wolfe conditional-gradient linear-model calculus and real
  Hilbert-space norm-square identities
Used in: conditional-gradient and proximal-linear inner-loop descent proofs
  replacing a centered quadratic objective residual by an attained Wolfe-style
  shifted max-linear gap
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem centeredQuadratic_residual_le_maxLinearModelGap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (g center current selected x : E) {β : ℝ}
    (hβ_nonneg : 0 ≤ β) (hx : x ∈ X)
    (hselected :
      IsMaxOn
        (fun y : E => ⟪g + β • (current - center), current - y⟫_ℝ)
        X selected) :
    (⟪g, current⟫_ℝ + β / 2 * ‖current - center‖ ^ 2) -
        (⟪g, x⟫_ℝ + β / 2 * ‖x - center‖ ^ 2) ≤
      ⟪g + β • (current - center), current - selected⟫_ℝ := by
  have hlin_gap :
      ⟪g + β • (current - center), current - x⟫_ℝ ≤
        ⟪g + β • (current - center), current - selected⟫_ℝ :=
    (isMaxOn_iff.mp hselected) x hx
  have hidentity :
      (⟪g, current⟫_ℝ + β / 2 * ‖current - center‖ ^ 2) -
          (⟪g, x⟫_ℝ + β / 2 * ‖x - center‖ ^ 2) =
        ⟪g + β • (current - center), current - x⟫_ℝ -
          β / 2 * ‖current - x‖ ^ 2 := by
    have hx_sub : x - center = (current - center) - (current - x) := by
      abel
    rw [hx_sub]
    simp [norm_sub_sq_real, inner_add_left, inner_sub_left, inner_sub_right,
      inner_smul_left, real_inner_comm]
    ring
  have hquad_nonneg : 0 ≤ β / 2 * ‖current - x‖ ^ 2 := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  nlinarith [hidentity, hlin_gap, hquad_nonneg]

end SOptLib.ConditionalGradient


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Layer0/cndGOutput_inner_le_eta.lean
/-!
-- Generalization plan (G0):
-- concept/name: conditional-gradient first-stopping projection inequality; orig was
-- outer_step_cndg_projection_inequality_succ, renamed to expose the reusable
-- inner-product certificate supplied by a gap-controlled CndG output.
-- generality used: arbitrary real inner-product normed additive group, compact
-- nonempty feasible set, first stopping output relation, and compact
-- linear-model maximizer; no measure, filtration, convexity, smoothness, outer
-- recursion, or finite-dimensional assumptions are used.
-- portable call pattern: stochastic conditional-gradient sliding,
-- Frank-Wolfe-with-inner-loop, and projection-sliding proofs call this after an
-- inner solver returns a first gap-controlled output, while the current model
-- vector, base iterate, tolerance, and comparator vary.
-- counterargument checked: not paper-local traceability because the theorem
-- mentions only a compact feasible set, the standard shifted linear model, and
-- the generic first-stopping output relation; not a pure wrapper because it
-- composes stopping-output and linear-model maximality into the exact
-- approximate projection inequality reused by later descent algebra.
-- coverage search: searched catalog/symbols for cndGOutput, projection
-- inequality, inner eta, cndGGap, compactLinearModelMaximizer, and LeanSearch
-- for conditional-gradient approximate projection inequality; relevant hits
-- were firstGapStoppingOutputRel_gap_le and compactLinearModelMaximizer_isMax,
-- which are partial ingredients but no existing declaration packages their
-- transitive approximate-projection consequence.
-- minimal hypotheses: finite-dimensionality, probability, convexity, and all
-- algorithm state hypotheses were removed; compactness and nonemptiness remain
-- only to instantiate the concrete compact linear-model maximizer.
-/

open scoped InnerProductSpace

namespace SOptLib

/-- A first-stopping conditional-gradient output satisfies the approximate
projection inequality against every feasible comparison point.

The gap certificate is the shifted compact linear-model gap at the returned
point.  Since the selected compact linear-model maximizer dominates every
feasible comparator and the first-stopping output bounds that gap by `eta`, the
same inner product against any feasible comparator is at most `eta`.

Layer: Layer0 | Gap: Level 0 (conditional-gradient stopping projection inequality)
Proof: specialize compact linear-model maximality at the returned point and
  chain it with the tolerance certificate from `firstGapStoppingOutputRel`.
Source: Frank-Wolfe conditional-gradient compact linear-model gap calculus over
  real Hilbert spaces
Used in: stochastic conditional-gradient sliding outer-step descent after the
  CndG inner solver returns a gap-controlled approximate projection
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem cndGOutput_inner_le_eta
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    {iterate : ℕ → E} {g u up x : E} {beta eta : ℝ}
    (hout :
      firstGapStoppingOutputRel
        (fun v =>
          ⟪g + beta • (v - u),
            v - compactLinearModelMaximizer hX_compact hX_nonempty v
              (g + beta • (v - u))⟫_ℝ)
        iterate eta up)
    (hx : x ∈ X) :
    ⟪g + beta • (up - u), up - x⟫_ℝ ≤ eta := by
  have hmax :
      ⟪g + beta • (up - u), up - x⟫_ℝ ≤
        ⟪g + beta • (up - u),
          up - compactLinearModelMaximizer hX_compact hX_nonempty up
            (g + beta • (up - u))⟫_ℝ := by
    exact compactLinearModelMaximizer_isMax hX_compact hX_nonempty up
      (g + beta • (up - u)) x hx
  have hstop :
      ⟪g + beta • (up - u),
          up - compactLinearModelMaximizer hX_compact hX_nonempty up
            (g + beta • (up - u))⟫_ℝ ≤ eta := by
    simpa using firstGapStoppingOutputRel_gap_le hout
  exact le_trans hmax hstop

end SOptLib

namespace SOptLib.ConditionalGradient

theorem shiftedLinearModel_lineSearchQuotient_nonneg_of_current_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {g u : E} {β : ℝ} {ut v : E}
    (hut : ut ∈ X)
    (hselected : IsMaxOn (fun x : E => ⟪g + β • (ut - u), ut - x⟫_ℝ) X v)
    (hβ : 0 < β)
    (hden : β * ‖v - ut‖ ^ 2 ≠ 0) :
    0 ≤ ⟪β • (u - ut) - g, v - ut⟫_ℝ / (β * ‖v - ut‖ ^ 2) :=
  cndG_lineSearchQuotient_nonneg_of_current_mem hut hselected hβ hden

end SOptLib.ConditionalGradient

namespace SOptLib

theorem inner_le_eta_of_firstGapStoppingOutputRel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    {iterate : ℕ → E} {g u up x : E} {beta eta : ℝ}
    (hout :
      firstGapStoppingOutputRel
        (fun v =>
          ⟪g + beta • (v - u),
            v - compactLinearModelMaximizer hX_compact hX_nonempty v
              (g + beta • (v - u))⟫_ℝ)
        iterate eta up)
    (hx : x ∈ X) :
    ⟪g + beta • (up - u), up - x⟫_ℝ ≤ eta :=
  cndGOutput_inner_le_eta hX_compact hX_nonempty hout hx

end SOptLib

-- Batch 2 promoted from Staging/firstGapOutput_isApproxConditionalGradientUpdate.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: firstGapOutput_isApproxConditionalGradientUpdate exposes the
--   reusable proof step from a first gap-controlled inner-loop output to an
--   approximate conditional-gradient update certificate; orig was
--   cndGUpdate_spec, renamed away from the paper's CndG abbreviation and setup.
-- generality used: arbitrary real inner-product normed additive group `E`,
--   feasible set `X`, model vector `G`, anchor `x`, curvature scale `beta`,
--   tolerance `eta`, named gap function, and iterate sequence; no measure,
--   filtration, compactness, convexity, smoothness, or finite-dimensional
--   assumptions are used once feasibility and gap domination are supplied.
-- portable call pattern: conditional-gradient, Frank-Wolfe, projection-sliding,
--   and proximal-linear inner solvers call this after proving the generated
--   iterates stay feasible and the selected gap dominates the residual, while
--   the feasible set, model vector, anchor, scale, gap definition, iterate
--   sequence, and first-gap relation vary.
-- counterargument checked: partially overlaps `SOptLib.cndGOutput_inner_le_eta`,
--   but that theorem specializes to compact linear-model maximizers and proves
--   only the variational inequality; this statement is stronger at the call
--   boundary because it also derives output feasibility from the first-gap
--   iterate relation and abstracts the gap-domination proof.
-- coverage search: searched catalog/source for `firstGapStoppingOutputRel`,
--   `cndGOutput_inner_le_eta`, `ApproxConditional`, `conditional gradient
--   update variational inequality`, and LeanSearch for first stopping gap
--   certificates; hits `firstGapStoppingOutputRel_gap_le` and
--   `cndGOutput_inner_le_eta` cover only ingredients or the compact-LMO
--   specialization, and no Mathlib theorem packages this optimization-specific
--   first-gap output certificate.
-- minimal hypotheses: global compactness/convexity/setup hypotheses are reduced
--   to pointwise iterate feasibility and pointwise residual domination by the
--   named gap at the returned output.

/-- A feasible first gap-controlled output is an approximate conditional-gradient
update.

If an inner procedure returns the first iterate whose named gap is at most
`eta`, all iterates in the procedure are feasible, and that gap dominates the
prox-linear residual at the returned point, then the returned point is feasible
and satisfies the `eta` variational inequality against every feasible
comparator.

Layer: Layer0 | Gap: Level 0 (first-gap approximate conditional-gradient update)
Proof: unpack the first-gap relation to obtain feasibility of the returned
  iterate, then chain pointwise residual domination with the first-gap tolerance
  certificate.
Source: Frank-Wolfe and conditional-gradient stopping certificates over
  real Hilbert spaces, using Mathlib order transitivity for scalar bounds
Used in: stochastic conditional-gradient sliding outer update after the CndG
  inner solver returns a first gap-controlled feasible iterate
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem firstGapOutput_isApproxConditionalGradientUpdate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {G x y : E} {beta eta : ℝ}
    {gap : E → ℝ} {iterate : ℕ → E}
    (hout : firstGapStoppingOutputRel gap iterate eta y)
    (hiterate_mem : ∀ n : ℕ, iterate n ∈ X)
    (hgap_dominates :
      ∀ z : E, z ∈ X → ⟪G + beta • (y - x), y - z⟫_ℝ ≤ gap y) :
    y ∈ X ∧ ∀ z : E, z ∈ X →
      ⟪G + beta • (y - x), y - z⟫_ℝ ≤ eta := by
  constructor
  · rcases hout with ⟨t, _, _, rfl⟩
    exact hiterate_mem t
  · intro z hz
    exact le_trans (hgap_dominates z hz) (firstGapStoppingOutputRel_gap_le hout)

end SOptLib


-- Batch 2 promoted from Staging/closedFormLineSearch_segment_minimizes.lean
open scoped InnerProductSpace

namespace SOptLib.ConditionalGradient

-- Generalization plan (G0):
-- concept/name: closed_form_segment_quadratic_line_search_minimizes exposes the closed-form
--   clamped quotient as the minimizing conditional-gradient segment line search;
--   orig was cndg_closed_form_line_search_segment_min, renamed away from the
--   paper-local CndG abbreviation while keeping standard line-search terminology.
-- generality used: arbitrary real inner-product normed additive group `E`,
--   feasible set `X`, model vector `G`, center `u`, positive curvature `beta`,
--   current point `ut`, selected endpoint `v`, and a pointwise `IsMaxOn`
--   shifted-linear-model certificate; no measure, convexity, smoothness,
--   oracle, filtration, compactness, or finite-dimensional assumptions are used.
-- portable call pattern: conditional-gradient, Frank-Wolfe, projection-sliding,
--   and proximal-linear proofs can provide feasibility of the current point,
--   positive curvature, a shifted linear-model maximizer, and any trial
--   `a ∈ [0,1]`; the closed-form line-search comparison is unchanged.
-- counterargument checked: not paper-local traceability because the theorem
--   states the reusable closed-form quotient-to-segment-minimum bridge; not a
--   duplicate of `segment_linear_quadratic_stepsize_minimizes`, which uses a
--   classical-choice minimizer rather than the displayed closed-form quotient,
--   and not a scalar-only wrapper because it combines the linear-oracle sign
--   certificate with the Hilbert segment quadratic expansion.
-- coverage search: searched catalog/source for `closed form line search`,
--   `segment linear quadratic stepsize`, `min one clamp quadratic`, and
--   `line search quotient nonnegative`; full-signature hits were
--   `segment_linear_quadratic_stepsize_minimizes`, partial abstract selector,
--   `closed_form_segment_quadratic_line_search`, partial def only,
--   `closed_form_segment_quadratic_line_search_mem_Icc_of_quotient_nonneg`,
--   partial interval membership, and `min_one_clamp_pos_quadratic_le`, scalar
--   component only. No hit covered the explicit Hilbert-space objective
--   comparison for the closed-form quotient.
-- minimal hypotheses: compact setup fields are reduced to the pointwise
--   `IsMaxOn` certificate used only at `ut`; positivity of `beta` is used only
--   to make the nonzero segment denominator positive in the nondegenerate case.

/-- The closed-form clamped quotient minimizes a segment quadratic line-search objective.

If `v` maximizes the shifted conditional-gradient linear model
`x ↦ ⟪G + beta • (ut - u), ut - x⟫` over a feasible set containing `ut`, then
the closed-form segment line-search stepsize gives no larger linear-plus-
centered-quadratic model value than any trial stepsize in `[0,1]`.

Layer: Layer0 | Gap: Level 1 (closed-form conditional-gradient line-search minimizer)
Proof: use the linear-model maximum at the current point to make the quotient
  numerator nonnegative, apply the scalar clamp minimizer inequality, and fold
  both sides through the Hilbert segment quadratic expansion.
Source: Frank-Wolfe conditional-gradient line-search calculus, real
  inner-product quadratic expansion, and ordered-field clamp minimization
Used in: stochastic conditional-gradient sliding inner update comparison
  against arbitrary feasible segment weights
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem closed_form_segment_quadratic_line_search_minimizes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (G u : E) {beta : ℝ} {ut v : E}
    (hut : ut ∈ X)
    (hmax : IsMaxOn (fun x : E => ⟪G + beta • (ut - u), ut - x⟫_ℝ) X v)
    (hbeta_pos : 0 < beta) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1,
      ⟪G, (1 - closed_form_segment_quadratic_line_search G u beta ut v) • ut +
          closed_form_segment_quadratic_line_search G u beta ut v • v⟫_ℝ +
          beta / 2 *
            ‖(1 - closed_form_segment_quadratic_line_search G u beta ut v) • ut +
                closed_form_segment_quadratic_line_search G u beta ut v • v - u‖ ^ 2 ≤
        ⟪G, (1 - a) • ut + a • v⟫_ℝ +
          beta / 2 * ‖(1 - a) • ut + a • v - u‖ ^ 2 := by
  classical
  intro a ha
  let d := v - ut
  by_cases hzero : d = 0
  · have hv_eq : v = ut := by
      have h : v - ut + ut = 0 + ut := congrArg (fun x => x + ut) hzero
      simpa [d, sub_eq_add_neg, add_assoc] using h
    have hleft_seg :
        (1 - closed_form_segment_quadratic_line_search G u beta ut v) • ut +
            closed_form_segment_quadratic_line_search G u beta ut v • v = ut := by
      rw [hv_eq]
      module
    have hright_seg : (1 - a) • ut + a • v = ut := by
      rw [hv_eq]
      module
    rw [hleft_seg, hright_seg]
  · let den := beta * ‖d‖ ^ 2
    let num := ⟪beta • (u - ut) - G, d⟫_ℝ
    let q := num / den
    let alpha := closed_form_segment_quadratic_line_search G u beta ut v
    have hnorm_ne : ‖d‖ ^ 2 ≠ 0 := by
      intro hnorm
      have hnorm0 : ‖d‖ = 0 := sq_eq_zero_iff.mp hnorm
      exact hzero (norm_eq_zero.mp hnorm0)
    have hnorm_pos : 0 < ‖d‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg ‖d‖) (Ne.symm hnorm_ne)
    have hden_pos : 0 < den := by
      simpa [den] using mul_pos hbeta_pos hnorm_pos
    have hden_ne : den ≠ 0 := ne_of_gt hden_pos
    have hmax0 :
        ⟪G + beta • (ut - u), ut - ut⟫_ℝ ≤
          ⟪G + beta • (ut - u), ut - v⟫_ℝ := by
      simpa using (isMaxOn_iff.mp hmax) ut hut
    have hgap_nonneg : 0 ≤ ⟪G + beta • (ut - u), ut - v⟫_ℝ := by
      simpa using hmax0
    have hnum_nonneg : 0 ≤ num := by
      simpa [num, d, sub_eq_add_neg, inner_add_left, inner_add_right,
        inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right,
        add_comm, add_left_comm, add_assoc] using hgap_nonneg
    have hq0 : 0 ≤ q := div_nonneg hnum_nonneg (le_of_lt hden_pos)
    have hdenq : den * q = num := by
      dsimp [q]
      field_simp [hden_ne]
    have halpha : alpha = min 1 q := by
      simp [alpha, d, den, num, q]
    have hscalar :
        (den / 2) * alpha ^ 2 - num * alpha ≤
          (den / 2) * a ^ 2 - num * a := by
      have hclamp :=
        _root_.min_one_clamp_pos_quadratic_le (den := den) (q := q) (a := a)
          hden_pos ha
      have hdenq_alpha : den * q * (min 1 q) = num * (min 1 q) := by
        rw [hdenq]
      have hdenq_alpha' : den * q * alpha = num * alpha := by
        rw [halpha]
        exact hdenq_alpha
      have hdenq_a : den * q * a = num * a := by
        rw [hdenq]
      have hclamp_alpha :
          (den / 2) * alpha ^ 2 - den * q * alpha ≤
            (den / 2) * a ^ 2 - den * q * a := by
        simpa [halpha] using hclamp
      nlinarith [hclamp_alpha, hdenq_alpha', hdenq_a]
    have hleft_exp :
        ⟪G, (1 - alpha) • ut + alpha • v⟫_ℝ +
            beta / 2 * ‖(1 - alpha) • ut + alpha • v - u‖ ^ 2 =
          (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
            (den / 2) * alpha ^ 2 - num * alpha := by
      simpa [d, den, num, alpha, sub_eq_add_neg, add_smul, add_assoc,
        add_left_comm, add_comm] using
        SOptLib.linear_centered_quadratic_along_line_eq_quadratic
          (g := G) (u := u) (ut := ut) (d := d) (beta := beta) (a := alpha)
    have hright_exp :
        ⟪G, (1 - a) • ut + a • v⟫_ℝ +
            beta / 2 * ‖(1 - a) • ut + a • v - u‖ ^ 2 =
          (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
            (den / 2) * a ^ 2 - num * a := by
      simpa [d, den, num, sub_eq_add_neg, add_smul, add_assoc, add_left_comm,
        add_comm] using
        SOptLib.linear_centered_quadratic_along_line_eq_quadratic
          (g := G) (u := u) (ut := ut) (d := d) (beta := beta) (a := a)
    nlinarith [hleft_exp, hright_exp, hscalar]

end SOptLib.ConditionalGradient


-- Batch 2 promoted from Staging/cndg_output_dist_model_minimizer_le_of_variational.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: conditional_gradient_output_dist_model_minimizer_le_of_variational exposes
--   the distance bound from an approximate conditional-gradient variational
--   inequality to an exact quadratic-model minimizer; orig was
--   theorem718_cndg_output_to_model_minimizer_distance, renamed away from the
--   theorem number and setup-field wording while retaining conditional-gradient
--   domain terminology.
-- generality used: arbitrary real inner-product normed additive group `E`, a
--   feasible set `X`, model vector `G`, anchor `x`, approximate output `y`,
--   exact model minimizer `zbar`, positive scaling `gamma`, and tolerance
--   `eta`; no measure, filtration, compactness, convexity, smoothness,
--   oracle, or finite-dimensional assumptions are used once the two pointwise
--   certificates are supplied.
-- portable call pattern: conditional-gradient sliding and approximate
--   prox-linear proofs can vary the feasible set, model vector, base point,
--   tolerance, approximate output certificate, and exact quadratic minimizer
--   certificate while reusing the same model-minimizer distance conclusion.
-- counterargument checked: not paper-local traceability because the statement
--   only links two standard pointwise certificates for an approximate
--   prox-linear/conditional-gradient output and an exact quadratic-model
--   minimizer; not a one-line wrapper because it composes a three-point
--   Hilbert identity, exact model minimality, and positive stepsize scalar
--   normalization.
-- coverage search: searched catalog/source for `cndGOutput inner eta`,
--   `model minimizer distance`, `quadratic model variational`, and LeanSearch
--   for "variational inequality approximate projection exact quadratic
--   minimizer distance bound Hilbert space"; the closest SOptLib hit
--   `SOptLib.cndGOutput_inner_le_eta` proves only the approximate projection
--   inequality, and Mathlib hits cover projection/minimality identities but
--   not this approximate-output versus exact-model-minimizer estimate.
-- minimal hypotheses: setup compactness, convexity, smoothness, algorithm
--   state, and the bundled paper update spec are reduced to `hy`,
--   `hzbar_mem`, the pointwise variational inequality, exact model minimality,
--   and `0 < gamma`.

namespace SOptLib

/-- An approximate conditional-gradient output is close to the exact quadratic-model minimizer.

If `y` satisfies the approximate prox-linear variational inequality and `zbar`
minimizes the same Euclidean quadratic model over the feasible set, then the
scaled squared distance from `y` to `zbar` is bounded by the approximation
tolerance.

Layer: Layer0 | Gap: Level 1 (approximate output to quadratic-model minimizer distance)
Proof: convert the approximate variational inequality into a three-point upper
  bound, use exact quadratic-model minimality at `y` for the reverse model
  lower bound, and cancel the shared model terms by ordered real arithmetic.
Source: Frank-Wolfe conditional-gradient prox-linear model calculus, real
  Hilbert three-point norm-square identities, and ordered-field normalization
Used in: stochastic conditional-gradient sliding comparison between a conditional-gradient
  inner-loop output and the exact Euclidean quadratic projected point
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem conditional_gradient_output_dist_model_minimizer_le_of_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {G x y zbar : E} {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (hy : y ∈ X)
    (hzbar_mem : zbar ∈ X)
    (hvariational : ∀ z : E, z ∈ X →
      ⟪G + gamma⁻¹ • (y - x), y - z⟫_ℝ ≤ eta)
    (hzbar_min : ∀ z : E, z ∈ X →
      ⟪G, zbar⟫_ℝ + gamma⁻¹ / 2 * ‖zbar - x‖ ^ 2 ≤
        ⟪G, z⟫_ℝ + gamma⁻¹ / 2 * ‖z - x‖ ^ 2) :
    (1 / (2 * gamma)) * ‖y - zbar‖ ^ 2 ≤ eta := by
  have hmin_y := hzbar_min y hy
  have hmodel_nonneg :
      0 ≤
        (⟪G, y⟫_ℝ + gamma⁻¹ / 2 * ‖y - x‖ ^ 2) -
          (⟪G, zbar⟫_ℝ + gamma⁻¹ / 2 * ‖zbar - x‖ ^ 2) := by
    linarith
  have hproj_upper :
      ⟪G, y - zbar⟫_ℝ ≤
        eta + gamma⁻¹ / 2 *
          (‖x - zbar‖ ^ 2 - ‖y - zbar‖ ^ 2 - ‖y - x‖ ^ 2) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (SOptLib.inner_le_eta_add_half_smul_norm_sub_sq_sub_of_add_smul_inner_le
        (g := G) (u := x) (up := y) (x := zbar) (beta := gamma⁻¹)
        (eta := eta) (hvariational zbar hzbar_mem))
  have hmin_lower :
      gamma⁻¹ / 2 * (‖zbar - x‖ ^ 2 - ‖y - x‖ ^ 2) ≤
        ⟪G, y - zbar⟫_ℝ := by
    have hinner :
        ⟪G, y - zbar⟫_ℝ = ⟪G, y⟫_ℝ - ⟪G, zbar⟫_ℝ := by
      simp [inner_sub_right]
    rw [hinner]
    linarith
  have hbeta :
      gamma⁻¹ / 2 * ‖y - zbar‖ ^ 2 ≤ eta := by
    have hnorm_xz : ‖x - zbar‖ ^ 2 = ‖zbar - x‖ ^ 2 := by rw [norm_sub_rev]
    have hproj_upper' :
        ⟪G, y - zbar⟫_ℝ ≤
          eta + gamma⁻¹ / 2 *
            (‖zbar - x‖ ^ 2 - ‖y - zbar‖ ^ 2 - ‖y - x‖ ^ 2) := by
      simpa [hnorm_xz] using hproj_upper
    have hchain := le_trans hmin_lower hproj_upper'
    nlinarith [hchain]
  have hcoef :
      (1 / (2 * gamma)) * ‖y - zbar‖ ^ 2 =
        gamma⁻¹ / 2 * ‖y - zbar‖ ^ 2 := by
    field_simp [ne_of_gt hgamma_pos]
  rwa [hcoef]

end SOptLib

