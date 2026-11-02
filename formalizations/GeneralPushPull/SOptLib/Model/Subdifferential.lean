import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace SOptLib

open scoped InnerProductSpace


/-- Subdifferential of a real-valued function at an ambient point:
`g ∈ ∂f(w)` iff `f y ≥ f w + ⟪g, y - w⟫` for every `y`.
Layer: Model | Concept: Subdifferential
Proof: (definitional construction; ambient subdifferential set via support inequalities)
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  Eq. (4.1.6).
Used in: stochastic mirror descent oracle subgradient assumptions
Book citation: `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math`
Origin algorithm: FOML stochastic mirror descent -/
def subdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (w : E) : Set E :=
  {g : E | ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ}

/-- Membership in the ambient subdifferential is the supporting-hyperplane inequality.
Layer: Model | Gap: Level 0 (subdifferential membership)
Proof: unfold the staged definition.
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  Eq. (4.1.6).
Used in: stochastic mirror descent oracle subgradient assumptions
Book citation: `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math`
Origin algorithm: FOML stochastic mirror descent -/
theorem mem_subdifferential_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {w g : E} :
    g ∈ subdifferential f w ↔ ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ := by
  rfl

/-- Carrier-restricted subdifferential for a function canonically defined on a feasible
set. The supporting inequality quantifies only over feasible carrier points.
Layer: Model | Concept: Subdifferential
Proof: (definitional construction; carrier-restricted subdifferential set via carrier support inequalities)
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  Eq. (4.1.6).
Used in: stochastic mirror descent paper-facing oracle subgradient assumptions
Book citation: `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math`
Origin algorithm: FOML stochastic mirror descent -/
def carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ)
    (w : {x : E // x ∈ X}) : Set E :=
  {g : E | ∀ y : {x : E // x ∈ X}, f y ≥ f w + ⟪g, y.1 - w.1⟫_ℝ}

/-- Membership in the carrier subdifferential is the carrier-restricted supporting
hyperplane inequality.
Layer: Model | Gap: Level 0 (carrier subdifferential membership)
Proof: unfold the staged carrier definition.
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  Eq. (4.1.6).
Used in: stochastic mirror descent paper-facing oracle subgradient assumptions
Book citation: `book/FOML/StochasticMirrorDescent.json#/assumptions/1/math`
Origin algorithm: FOML stochastic mirror descent -/
theorem mem_carrierSubdifferential_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {f : {x : E // x ∈ X} → ℝ}
    {w : {x : E // x ∈ X}} {g : E} :
    g ∈ carrierSubdifferential f w ↔
      ∀ y : {x : E // x ∈ X}, f y ≥ f w + ⟪g, y.1 - w.1⟫_ℝ := by
  rfl


-- Generalization plan (G0):
-- concept/name: selected carrier subgradient subtype; orig was DualConjugateSubgradient, renamed away from dual-conjugate and random-primal-dual-gradient vocabulary.
-- generality used: arbitrary real inner-product carrier `X`, carrier-valued objective `f`, and base point `w`; no measure, filtration, convexity, smoothness, oracle, compactness, completeness, or finite-dimensionality hypotheses are used.
-- portable call pattern: mirror-prox, nonsmooth Bregman, Fenchel-dual, and randomized block primal-dual proofs can store a chosen carrier subgradient at a base point while varying the carrier, objective, and base point.
-- counterargument checked: this is a thin subtype wrapper over `carrierSubdifferential`, but it is not paper-local traceability because later selected-Bregman formulas need a reusable type for local chosen subgradients when no global gradient selector exists; Mathlib has gradient/subgradient predicates but not this carrier-selected subtype.
-- coverage search: checked `docs/knowledge/CATALOG.md`, `SOptLib/Model/Subdifferential.lean`, `SOptLib/Layer0/Subgradient.lean`, and project/Staging tokens for `CarrierSelectedSubgradient`, `selected carrier subgradient`, and `carrierSubdifferential`; LeanSearch for "subtype of selected subgradients of a function on a carrier set at a base point" returned gradient-within APIs, not a selected carrier-subgradient subtype.
-- minimal hypotheses: all already minimal; the original complete and finite-dimensional ambient assumptions are dropped, and the statement keeps the concrete `carrierSubdifferential` def rather than abstracting a formula by equality.

/-- A selected carrier subgradient of a function at a base point.

The subtype packages a vector together with membership in the
carrier-restricted subdifferential. This is useful when a Bregman or
Fenchel-dual argument selects only local subgradients at recursive base points
instead of assuming a global gradient selector.

Layer: Model | Concept: Subdifferential
Proof: (definitional construction; subtype of the carrier-subdifferential set)
Source: convex-analysis subdifferentials and SOptLib carrier-restricted
  support inequalities
Used in: random primal-dual gradient selected dual Bregman bases and
  mirror-prox selected-subgradient Bregman formulas
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
abbrev CarrierSelectedSubgradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ)
    (w : {x : E // x ∈ X}) : Type _ :=
  {g : E // g ∈ carrierSubdifferential f w}

namespace CarrierSelectedSubgradient

/-- The value stored in a selected carrier subgradient belongs to the carrier
subdifferential at the base point.

Layer: Model | Gap: Level 0 (selected carrier-subgradient projection)
Proof: project the proof component of the selected-subgradient subtype.
Source: convex-analysis subdifferentials and SOptLib carrier-restricted
  support inequalities
Used in: random primal-dual gradient selected dual Bregman bases and
  mirror-prox selected-subgradient Bregman formulas
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem coe_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {f : {x : E // x ∈ X} → ℝ}
    {w : {x : E // x ∈ X}} (g : CarrierSelectedSubgradient f w) :
    (g : E) ∈ carrierSubdifferential f w := by
  exact g.2

end CarrierSelectedSubgradient

end SOptLib
