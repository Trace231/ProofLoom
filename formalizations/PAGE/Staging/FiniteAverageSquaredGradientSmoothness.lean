import SOptLib.Model.Objective

open scoped Gradient

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-average squared-gradient smoothness; orig was AverageLSmooth
-- generality used: finite index type `ι`, real inner-product space `E`, objective family `F`, selected gradient family `gradF`, and positive scale `L`; no measure, independence, integrability, convexity, filtration, or finite-dimensional assumptions are used.
-- portable call pattern: finite-sum stochastic-gradient and variance-reduced methods can replace the component objective/gradient families and scale while reusing the same positivity, pointwise gradient-realization, and finite-uniform-average squared-difference bound.
-- counterargument checked: this is not paper-only traceability or a caller-side expression; it names the recurring average-squared-gradient contract. Existing `FiniteFamilyGradientSmoothness` covers pointwise component Lipschitz constants, which is structurally different from this average squared-difference hypothesis, and Mathlib has no matching finite-family predicate.
-- coverage search: searched `finite average squared gradient difference smoothness`, `finiteUniformAverage gradient difference bound`, and `component gradient HasGradientAt squared difference`; existing hits were `FiniteFamilyGradientSmoothness`, finite-average gradient calculus, and smooth-descent transfer theorems, all partial rather than this contract.
-- minimal hypotheses: removed PAGE's setup record, sample spaces, nonempty index assumptions, and finite-dimensionality; retained `[Fintype ι]`, `[NormedAddCommGroup E]`, `[InnerProductSpace ℝ E]`, and `[CompleteSpace E]` because `HasGradientAt` uses the Hilbert-space gradient API.

/-- Positive finite-average smoothness with pointwise component gradient realization.

Layer: Model | Concept: finite-average squared-gradient smoothness
Proof: (definitional construction; positivity, pointwise `HasGradientAt`, and a finite-uniform-average squared-gradient-difference bound)
Source: Mathlib Hilbert-space gradient predicates, finite sums, and norm inequalities for finite-average smoothness assumptions
Used in: finite-sum stochastic-gradient and variance-reduced proofs before identifying the full gradient and bounding recursive estimator differences
Book citation: book/research/PAGE.json#/assumptions/1
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
def FiniteAverageSquaredGradientSmoothness
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (L : ℝ) : Prop :=
  0 < L ∧
    (∀ (i : ι) (x : E), HasGradientAt (F i) (gradF i x) x) ∧
    ∀ x y : E,
      finiteUniformAverage
          (fun i : ι => ‖gradF i x - gradF i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2

/-- The finite-average squared-gradient smoothness predicate unfolds to its three
component contracts: positive scale, pointwise gradient realization, and the
uniform average squared-difference bound.

Layer: Model | Gap: Level 0 (finite-average squared-gradient smoothness unfolding)
Proof: by rfl after unfolding `FiniteAverageSquaredGradientSmoothness`.
Source: Mathlib propositional conjunctions, gradient predicates, and finite-uniform averages
Used in: exposing the positivity, gradient, and average-bound clauses to finite-sum estimator and descent proofs
Book citation: book/research/PAGE.json#/assumptions/1
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
@[simp] theorem FiniteAverageSquaredGradientSmoothness_def
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (L : ℝ) :
    FiniteAverageSquaredGradientSmoothness F gradF L ↔
      0 < L ∧
        (∀ (i : ι) (x : E), HasGradientAt (F i) (gradF i x) x) ∧
        ∀ x y : E,
          finiteUniformAverage
              (fun i : ι => ‖gradF i x - gradF i y‖ ^ 2) ≤
          L ^ 2 * ‖x - y‖ ^ 2 := by
  rfl

namespace FiniteAverageSquaredGradientSmoothness

/-- The scale in a finite-average squared-gradient smoothness predicate is
strictly positive. -/
theorem positive
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : ι → E → ℝ} {gradF : ι → E → E} {L : ℝ}
    (h : FiniteAverageSquaredGradientSmoothness F gradF L) :
    0 < L :=
  h.1

/-- The selected component gradient realizes the component derivative. -/
theorem hasGradientAt
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : ι → E → ℝ} {gradF : ι → E → E} {L : ℝ}
    (h : FiniteAverageSquaredGradientSmoothness F gradF L)
    (i : ι) (x : E) :
    HasGradientAt (F i) (gradF i x) x :=
  h.2.1 i x

/-- The component gradients satisfy the finite-uniform average squared
difference bound. -/
theorem average_squared_gradient_difference_le
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : ι → E → ℝ} {gradF : ι → E → E} {L : ℝ}
    (h : FiniteAverageSquaredGradientSmoothness F gradF L)
    (x y : E) :
    finiteUniformAverage
        (fun i : ι => ‖gradF i x - gradF i y‖ ^ 2) ≤
      L ^ 2 * ‖x - y‖ ^ 2 :=
  h.2.2 x y

end FiniteAverageSquaredGradientSmoothness

end SOptLib
