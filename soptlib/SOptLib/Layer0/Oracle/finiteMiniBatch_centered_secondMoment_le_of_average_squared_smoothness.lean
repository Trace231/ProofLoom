import SOptLib.Glue.Algebra
import SOptLib.Glue.Algebra.finite_function_row_centered_average_secondMoment_le
noncomputable section

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite mini-batch centered second-moment bound from averaged squared smoothness; orig was the PAGE-local row-increment fiber bound.
-- generality used: finite nonempty row and component types, Hilbert-valued component differences, a normed state space, an arbitrary component mean with a centered finite average, and a pointwise finite-average squared-smoothness budget; no measure, convexity, or finite-dimensionality is used.
-- portable call pattern: recursive finite-mini-batch gradient estimators can change the row type, component map, state points, mean, and smoothness constant while retaining the `L^2 / card(row)` centered second-moment bound.
-- counterargument checked: measure-level centered mini-batch variance lemmas and the finite-row covariance theorem cover only component pieces; this theorem packages their deterministic centering and smoothness composition and is not a pure wrapper or paper traceability alias.
-- coverage search: searched `finite mini batch centered second moment average squared smoothness`, `centered row second moment smoothness displacement bound`, and `finiteUniformAverage`; existing hits were `centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero` (measure-level), `randomQuery_centeredMiniBatchGradientDiff_secondMoment_le` (random-query), and `finite_function_row_centered_average_second_moment_le` (uncentered budget only), so coverage was partial.
-- minimal hypotheses: finite type nonemptiness is needed for cardinal inverses; Hilbert structure is needed by the row contraction and weighted variance inequality; the state space only needs a normed additive group.

/-- A centered finite mini-batch row has second moment at most the averaged
 squared-smoothness budget divided by the row cardinality.

Layer: Layer0 | Gap: Level 1 (finite centered mini-batch smoothness contraction)
Proof: apply the finite-row centered second-moment theorem, bound the centered component budget by the uncentered budget with the finite weighted variance inequality, and divide the supplied averaged squared-smoothness bound by the row cardinality.
Source: SOptLib `Finset.weighted_variance_le_second_moment` and `finite_function_row_centered_average_second_moment_le`, with Mathlib finite sums, real Hilbert-space norm-square identities, and ordered-field division
Used in: the recursive PAGE estimator step, where a centered row of component gradient differences is converted into the `L^2 / card(row)` displacement budget before the variance recursion
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finite_mini_batch_centered_second_moment_le_of_average_squared_smoothness
    {I J V D : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup D]
    (raw : J → V) (mean : V) (x y : D) (L : ℝ)
    (hcenter : finiteUniformAverage (fun j : J => raw j - mean) = 0)
    (hsmooth : finiteUniformAverage (fun j : J => ‖raw j‖ ^ 2) ≤
      L ^ 2 * ‖x - y‖ ^ 2) :
    let _ : DecidableEq I := Classical.decEq I
    (Fintype.card (I → J) : ℝ)⁻¹ *
        Finset.univ.sum
          (fun r : I → J =>
            ‖((Fintype.card I : ℝ)⁻¹) •
              Finset.univ.sum (fun i : I => raw (r i) - mean)‖ ^ 2) ≤
      L ^ 2 / (Fintype.card I : ℝ) * ‖x - y‖ ^ 2 := by
  classical
  let atom : J → V := fun j => raw j - mean
  have hcardJ : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card J ≠ 0)
  have hsum_const :
      Finset.univ.sum (fun _j : J => mean) =
        (Fintype.card J : ℝ) • mean := by
    rw [Finset.sum_const]
    exact (Nat.cast_smul_eq_nsmul ℝ (Fintype.card J) mean).symm
  have hcenter' :
      (Fintype.card J : ℝ)⁻¹ • Finset.univ.sum raw -
          (Fintype.card J : ℝ)⁻¹ •
            (Fintype.card J : ℝ) • mean = 0 := by
    simpa [atom, finiteUniformAverage_def, Finset.sum_sub_distrib,
      smul_sub, hsum_const] using hcenter
  have hmean_weighted :
      (Fintype.card J : ℝ)⁻¹ • Finset.univ.sum raw = mean := by
    have hweighted :
        (Fintype.card J : ℝ)⁻¹ • Finset.univ.sum raw =
          (Fintype.card J : ℝ)⁻¹ • (Fintype.card J : ℝ) • mean :=
      sub_eq_zero.mp hcenter'
    simpa [inv_smul_smul₀ hcardJ] using hweighted
  have hcenter_atom : finiteUniformAverage atom = 0 := by
    simpa [atom] using hcenter
  have hrow :=
    finite_function_row_centered_average_second_moment_le
      (α := I) (β := J) (V := V) atom hcenter_atom
  have hqsum :
      Finset.univ.sum (fun _j : J => (Fintype.card J : ℝ)⁻¹) = 1 := by
    have hcard : (Fintype.card J : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card J ≠ 0)
    simp [Finset.sum_const, hcard]
  have hmean_weighted' :
      Finset.univ.sum
          (fun j : J => (Fintype.card J : ℝ)⁻¹ • raw j) = mean := by
    rw [← Finset.smul_sum]
    exact hmean_weighted
  have hcenter_budget :
      finiteUniformAverage (fun j : J => ‖atom j‖ ^ 2) ≤
        finiteUniformAverage (fun j : J => ‖raw j‖ ^ 2) := by
    have hw :=
      Finset.weighted_variance_le_second_moment
        (s := (Finset.univ : Finset J))
        (q := fun _j : J => (Fintype.card J : ℝ)⁻¹)
        (a := raw) (μ := mean) hqsum hmean_weighted'
    simpa [finiteUniformAverage_def, atom, Finset.mul_sum] using hw
  have hcardI_nonneg : 0 ≤ (Fintype.card I : ℝ) := by positivity
  calc
    (Fintype.card (I → J) : ℝ)⁻¹ *
        Finset.univ.sum
          (fun r : I → J =>
            ‖((Fintype.card I : ℝ)⁻¹) •
              Finset.univ.sum (fun i : I => raw (r i) - mean)‖ ^ 2)
        ≤ finiteUniformAverage (fun j : J => ‖atom j‖ ^ 2) /
            (Fintype.card I : ℝ) := by
      simpa [atom] using hrow
    _ ≤ finiteUniformAverage (fun j : J => ‖raw j‖ ^ 2) /
          (Fintype.card I : ℝ) := by
      exact div_le_div_of_nonneg_right hcenter_budget hcardI_nonneg
    _ ≤ (L ^ 2 * ‖x - y‖ ^ 2) / (Fintype.card I : ℝ) := by
      exact div_le_div_of_nonneg_right hsmooth hcardI_nonneg
    _ = L ^ 2 / (Fintype.card I : ℝ) * ‖x - y‖ ^ 2 := by
      ring

end SOptLib
