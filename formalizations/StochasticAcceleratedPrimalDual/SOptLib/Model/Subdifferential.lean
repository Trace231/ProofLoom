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

namespace SOptLib

open scoped BigOperators
open scoped InnerProductSpace

/-- Product-space subdifferential over a finite dependent block product.

For a block carrier family `X`, `g` belongs to this subdifferential at `x` when
the finite sum of coordinate pairings supports `f` at every product-feasible
comparison point.

Layer: Model | Concept: Subdifferential
Proof: (definitional construction; finite block-product support inequalities)
Source: Convex analysis subgradient support inequalities on finite product Hilbert spaces
Used in: stochastic block mirror descent mean-oracle subgradient assumption over a block product carrier
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
def productSubdifferential
    {ι : Type*} {Block : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (X : ∀ i, Set (Block i)) (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) :
    Set (∀ i, Block i) :=
  {g | ∀ y, (∀ i, y i ∈ X i) →
    f y ≥ f x + Finset.sum Finset.univ (fun i => ⟪g i, y i - x i⟫_ℝ)}

/-- Membership in the finite product subdifferential is the blockwise support inequality.

Layer: Model | Gap: Level 0 (product subdifferential membership)
Proof: by rfl after unfolding `productSubdifferential`.
Source: Convex analysis subgradient support inequalities on finite product Hilbert spaces
Used in: stochastic block mirror descent conversion of mean-oracle subgradient membership into the finite block support inequality
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem mem_productSubdifferential_iff
    {ι : Type*} {Block : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    {X : ∀ i, Set (Block i)} {f : (∀ i, Block i) → ℝ} {x g : ∀ i, Block i} :
    g ∈ productSubdifferential X f x ↔
      ∀ y, (∀ i, y i ∈ X i) →
        f y ≥ f x + Finset.sum Finset.univ (fun i => ⟪g i, y i - x i⟫_ℝ) := by
  rfl

end SOptLib
