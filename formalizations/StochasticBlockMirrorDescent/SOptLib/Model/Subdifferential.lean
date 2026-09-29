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

end SOptLib
