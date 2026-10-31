import SOptLib.Glue.Algebra
import SOptLib.Model.Selection

open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finiteAverageGradient_lipschitz_of_average_sq_smoothness; orig was averageLSmooth_implies_fullGradient_lipschitz
-- generality used: finite index type with a uniform average, a seminormed real module for the gradient carrier, an averaged gradient map, component gradients, and a positive average squared-difference bound; no measure, objective, differentiability, inner-product, completeness, or finite-dimensional assumptions are needed.
-- portable call pattern: finite-sum stochastic-gradient, PAGE/SPIDER/SARAH, and minibatch variance-reduction proofs can change the component family, averaged gradient realization, and positive scale while reusing the same Lipschitz conclusion.
-- counterargument checked: the existing componentwise Lipschitz transfer theorem has a different hypothesis (one Lipschitz constant per component) and cannot consume an average squared bound; Mathlib/SOptLib has the Jensen norm-square ingredient but no theorem connecting this contract to an averaged-gradient Lipschitz bound.
-- coverage search: searched "average squared gradient bound implies Lipschitz average gradient", "finite average norm squared", and existing finite-average gradient Lipschitz declarations; top hits were `finiteAverageGradient_lipschitzOn_of_component_lipschitz` (different pointwise hypotheses) and `norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq` (Jensen ingredient), so coverage is partial.
-- minimal hypotheses: no nonemptiness assumption is needed; the empty finite
-- family is discharged by the zero-average case, while the nonempty case uses
-- the positive-cardinality finite-average norm-square lemma. The carrier is
-- reduced to `[SeminormedAddCommGroup E] [NormedSpace ℝ E]`.

/-- An averaged gradient is Lipschitz when component squared differences have a
uniform finite-average bound.

If `avgGrad` is the uniform finite average of `componentGrad` and the average
of the component squared differences is bounded by `L² ‖x-y‖²`, then `avgGrad`
is `L`-Lipschitz.

Layer: Layer0 | Gap: Level 1 (finite-average squared-smoothness to gradient Lipschitzness)
Proof: rewrite the averaged-gradient difference as a normalized finite sum, apply the finite-average squared-norm Jensen bound, then use nonnegativity of `L` and of norms to pass from the squared inequality to the Lipschitz inequality.
Source: Mathlib finite sums, normed real modules, and ordered-field square inequalities; SOptLib finite-average algebra and Jensen bound
Used in: PAGE and future finite-sum stochastic-gradient or variance-reduced proofs when an average squared component-gradient bound must be converted into a deterministic averaged-gradient Lipschitz estimate
Book citation: book/research/PAGE.json#/key_lemmas/0
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finiteAverageGradient_lipschitz_of_average_sq_smoothness
    {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (avgGrad : E → E) (componentGrad : ι → E → E) (L : ℝ)
    (hL : 0 ≤ L)
    (havg : ∀ x : E,
      avgGrad x = finiteUniformAverage (fun i : ι => componentGrad i x))
    (hsq : ∀ x y : E,
      finiteUniformAverage (fun i : ι => ‖componentGrad i x - componentGrad i y‖ ^ 2) ≤
        L ^ 2 * ‖x - y‖ ^ 2) :
    ∀ x y : E, ‖avgGrad x - avgGrad y‖ ≤ L * ‖x - y‖ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      intro x y
      have hx := havg x
      have hy := havg y
      simp [finiteUniformAverage] at hx hy
      rw [hx, hy]
      simpa using (mul_nonneg hL (norm_nonneg (x - y)))
  | inr hι =>
      letI := hι
      intro x y
      have hdiff :
          avgGrad x - avgGrad y =
            finiteUniformAverage
              (fun i : ι => componentGrad i x - componentGrad i y) := by
        rw [havg x, havg y]
        simp [finiteUniformAverage, Finset.smul_sum, smul_sub,
          Finset.sum_sub_distrib]
      have haverage_norm_sq :
          ‖finiteUniformAverage
              (fun i : ι => componentGrad i x - componentGrad i y)‖ ^ 2 ≤
            finiteUniformAverage
              (fun i : ι => ‖componentGrad i x - componentGrad i y‖ ^ 2) := by
        simpa [finiteUniformAverage] using
          (norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq
            (s := (Finset.univ : Finset ι))
            (f := fun i : ι => componentGrad i x - componentGrad i y)
            (by exact Fintype.card_pos))
      have hsquare : ‖avgGrad x - avgGrad y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
        calc
          ‖avgGrad x - avgGrad y‖ ^ 2 =
              ‖finiteUniformAverage
                  (fun i : ι => componentGrad i x - componentGrad i y)‖ ^ 2 := by
                rw [hdiff]
          _ ≤ finiteUniformAverage
                (fun i : ι => ‖componentGrad i x - componentGrad i y‖ ^ 2) :=
              haverage_norm_sq
          _ ≤ L ^ 2 * ‖x - y‖ ^ 2 := hsq x y
      have hR_nonneg : 0 ≤ L * ‖x - y‖ :=
        mul_nonneg hL (norm_nonneg (x - y))
      have hLhs_nonneg : 0 ≤ ‖avgGrad x - avgGrad y‖ :=
        norm_nonneg _
      nlinarith [sq_nonneg (‖avgGrad x - avgGrad y‖ - L * ‖x - y‖)]

end SOptLib
