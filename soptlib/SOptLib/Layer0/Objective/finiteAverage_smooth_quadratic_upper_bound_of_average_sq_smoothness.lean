import SOptLib.Layer0.Objective
import SOptLib.Layer0.Objective.finiteAverageGradient_lipschitz_of_average_sq_smoothness
open scoped BigOperators Gradient InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-average smooth quadratic upper bound from averaged squared-gradient smoothness; orig was averageLSmooth_implies_quadratic_upper_bound
-- generality used: a finite index type, a complete real inner-product space, component objectives and selected component gradients, an averaged objective and averaged gradient selector, pointwise component HasGradientAt certificates, and a nonnegative averaged squared-gradient scale; no probability, convexity, filtration, integrability, or finite-dimensional assumptions are used.
-- portable call pattern: finite-sum SGD, PAGE/SPIDER/SARAH, and other variance-reduced proofs can change the component family, averaged objective, gradient selector, and smoothness scale while reusing the same global quadratic upper model.
-- counterargument checked: the existing finite-average component-Lipschitz theorem has stronger and structurally different pointwise hypotheses, while the generic smooth upper-bound theorem does not derive the averaged objective gradient or its Lipschitz estimate from a squared-average bound; this declaration composes those missing reusable steps.
-- coverage search: searched `finite average smooth quadratic upper bound`, `average squared gradient difference`, and `finite-average objective gradient`; relevant hits were `finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz`, `finiteAverageObjective_hasGradientAt`, and `finiteAverageGradient_lipschitz_of_average_sq_smoothness`, which are partial rather than this combined contract.
-- minimal hypotheses: the proof uses only `[Fintype ι]`, `[NormedAddCommGroup E]`, `[InnerProductSpace ℝ E]`, and `[CompleteSpace E]`; no finite-dimensional, nonempty-index, probability, or carrier assumptions are needed.

/-- Averaged squared-gradient smoothness gives the standard quadratic upper model.

If each component objective has a selected gradient, the averaged objective and
gradient selectors are the corresponding finite uniform averages, and the
average squared component-gradient difference is bounded by `L ^ 2`, then the
averaged objective satisfies the global `L`-smooth upper bound.

Layer: Layer0 | Gap: Level 1 (finite-average smooth descent from averaged squared-gradient smoothness)
Proof: derive the averaged objective gradient by finite-sum gradient calculus, derive its Lipschitz estimate from the finite-average squared-gradient bound, and apply the generic smooth quadratic upper-bound theorem on the universal convex set.
Source: SOptLib finite-average gradient calculus, finite-average squared-norm Jensen bounds, and Mathlib convex-segment smooth descent APIs
Used in: PAGE, SPIDER, SARAH, and finite-sum stochastic-gradient proofs when an averaged squared component-gradient bound must be converted into the objective smoothness inequality used for descent
Book citation: book/research/PAGE.json#/key_lemmas/0
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finiteAverage_smooth_quadratic_upper_bound_of_average_sq_smoothness
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E)
    (objective : E → ℝ) (avgGrad : E → E) (L : ℝ)
    (hobjective : ∀ x : E,
      objective x = finiteUniformAverage (fun i : ι => F i x))
    (havgGrad : ∀ x : E,
      avgGrad x = finiteUniformAverage (fun i : ι => gradF i x))
    (hgrad : ∀ i : ι, ∀ x : E, HasGradientAt (F i) (gradF i x) x)
    (hL : 0 ≤ L)
    (hsq : ∀ x y : E,
      finiteUniformAverage
          (fun i : ι => ‖gradF i x - gradF i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2) :
    ∀ x y : E,
      objective y ≤
        objective x + inner ℝ (avgGrad x) (y - x) +
          (L / 2) * ‖y - x‖ ^ 2 := by
  have hobjective_eq : objective = finiteUniformAverage F := by
    funext x
    simpa [finiteUniformAverage] using hobjective x
  have hgrad_avg : ∀ x : E, HasGradientAt objective (avgGrad x) x := by
    intro x
    have hraw := finiteAverageObjective_hasGradientAt F gradF x (fun i => hgrad i x)
    have havg : HasGradientAt (finiteUniformAverage F)
        (finiteUniformAverage (fun i : ι => gradF i x)) x := by
      rw [show finiteUniformAverage F =
          (fun z : E => (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i : ι => F i z)) by
        funext z
        simp [finiteUniformAverage]]
      simpa [finiteUniformAverage] using hraw
    rw [hobjective_eq, havgGrad x]
    exact havg
  have hLip : ∀ x y : E, ‖avgGrad x - avgGrad y‖ ≤ L * ‖x - y‖ := by
    exact finiteAverageGradient_lipschitz_of_average_sq_smoothness
      (avgGrad := avgGrad) (componentGrad := gradF) (L := L) hL havgGrad hsq
  intro x y
  exact smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
    (Set.univ : Set E) objective avgGrad L
    (by simpa using (convex_univ : Convex ℝ (Set.univ : Set E)))
    (by intro z hz; simpa using hgrad_avg z)
    (by intro z hz w hw; simpa using hLip z w)
    (by simp) (by simp)

end SOptLib
