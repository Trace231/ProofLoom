import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-horizon realized-gradient bound; orig was BoundedGradientsOnHorizon
-- generality used: a real Hilbert carrier `E`, feasible set `F`, time-indexed objectives `f`, an arbitrary gradient gauge, a real bound, and a natural horizon; no measure, convexity, smoothness, oracle, or finite-dimensional hypothesis is used
-- portable call pattern: deterministic online optimization, stochastic-gradient, and adaptive-gradient proofs instantiate the feasible carrier, objective family, gauge, bound, and horizon, then use the same finite-window existence contract and realized-gradient bound
-- counterargument checked: not paper-local traceability or a caller-side expression because the declaration packages the recurring horizon-local existence-and-bound assumption; it is not covered by finite-family smoothness, subgradient bounds, or Mathlib's pointwise gradient APIs
-- coverage search: searched `finite horizon realized gradient bounded gauge`, `gradient realization bound on feasible set finite window`, and the SOptLib catalog; closest hits were finite-family smoothness and subgradient Lipschitz consequences, with no matching existence-and-bound contract
-- minimal hypotheses: only `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]` are retained for `HasGradientAt`; all AMSGrad setup fields and finite-dimensional Euclidean structure are removed

/-- Every feasible point in a finite time window has a realized gradient whose
gauge is bounded by a common constant.

Layer: Layer0 | Concept: finite-horizon realized-gradient bound
Proof: (definitional construction; finite-window pointwise existence of a `HasGradientAt` witness and a gauge bound)
Source: Mathlib Hilbert-space gradient calculus and finite interval APIs for online optimization assumptions
Used in: deterministic online optimization and adaptive-gradient proofs that certify the gradient realization and bound before applying horizon-local regret or descent estimates
Book citation: book/ICLR2018/AMSGrad.json#/assumptions/3
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad (Algorithm 2) -/
def BoundedGradientsOnFiniteHorizon
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (F : Set E) (f : ℕ → E → ℝ) (gradGauge : E → ℝ) (G : ℝ)
    (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ x, x ∈ F →
    ∃ g, HasGradientAt (f t) g x ∧ gradGauge g ≤ G

/-- The finite-horizon realized-gradient bound unfolds to its pointwise
existence-and-bound contract.

Layer: Layer0 | Gap: Level 0 (finite-horizon gradient-bound unfolding)
Proof: by rfl after unfolding `BoundedGradientsOnFiniteHorizon`
Source: Mathlib finite intervals, conjunctions, and Hilbert-space gradient predicates
Used in: exposing the horizon-local gradient assumption when an online optimization proof specializes it to a time, feasible point, and gradient witness
Book citation: book/ICLR2018/AMSGrad.json#/assumptions/3
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad (Algorithm 2) -/
@[simp] theorem BoundedGradientsOnFiniteHorizon_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (F : Set E) (f : ℕ → E → ℝ) (gradGauge : E → ℝ) (G : ℝ)
    (T : ℕ) :
    BoundedGradientsOnFiniteHorizon F f gradGauge G T =
      (∀ t ∈ Finset.Icc 1 T, ∀ x, x ∈ F →
        ∃ g, HasGradientAt (f t) g x ∧ gradGauge g ≤ G) := rfl

/-- A realized gradient inherits the finite-horizon gauge bound from the
existence contract.

Layer: Layer0 | Gap: Level 1 (realized-gradient bound transport)
Proof: choose the bounded witness supplied by the horizon contract, identify it
with the given gradient using `HasGradientAt.unique`, and rewrite the bound.
Source: Mathlib uniqueness of Hilbert-space gradients and propositional witness elimination
Used in: online regret and adaptive-gradient proofs that replace the existential gradient certificate by the particular realized gradient selected by an algorithm step
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/0
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad (Algorithm 2) -/
theorem BoundedGradientsOnFiniteHorizon.bound_of_hasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {F : Set E} {f : ℕ → E → ℝ} {gradGauge : E → ℝ} {G : ℝ} {T t : ℕ}
    {x g : E}
    (hbound : BoundedGradientsOnFiniteHorizon F f gradGauge G T)
    (ht : t ∈ Finset.Icc 1 T) (hx : x ∈ F)
    (hg : HasGradientAt (f t) g x) :
    gradGauge g ≤ G := by
  rcases hbound t ht x hx with ⟨g0, hg0, hg0_bound⟩
  have h_eq : g0 = g := hg0.unique hg
  simpa [h_eq] using hg0_bound

end SOptLib
