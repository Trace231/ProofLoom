import SOptLib.Glue.Martingale
import SOptLib.Glue.Probability.finiteUniformAverage_function_eval_eq
import SOptLib.Glue.Probability.finiteUniformAverage_function_eval_inner_eval_eq_zero_of_average_zero
noncomputable section

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite function-row centered average second-moment contraction; orig was the PAGE-local `finite_function_row_centered_average_secondMoment_le`.
-- generality used: finite nonempty row and value types, a real Hilbert-valued component map, and its zero finite uniform average; no measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: finite-product sampling proofs can change the row size and centered component map while reusing the `1 / card row` second-moment bound for the row average.
-- counterargument checked: existing mini-batch variance theorems are measure-level and require stochastic hypotheses; the finite covariance diagonalization plus coordinate marginal specialization here is a distinct reusable algebraic backend.
-- coverage search: searched `finite function row centered average second moment`, `finiteUniformAverage`, and finite covariance APIs; `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero` covers only the measure-level diagonalization, so this finite-row contraction is partial coverage.
-- minimal hypotheses: `[Fintype α] [Fintype β] [DecidableEq α] [Nonempty α] [Nonempty β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]` are exactly those used for nonzero cardinalities, finite sums, and Hilbert inner-product expansion.

/-- A centered finite function-row average has second moment at most the component
average second moment divided by the row size.

Layer: Glue | Gap: Level 1 (finite centered row second-moment contraction)
Proof: apply finite Hilbert covariance diagonalization to the uniform count measure on
function rows, cancel off-diagonal terms using centered coordinate cross averages, and
identify each diagonal marginal with the component finite uniform average.
Source: Mathlib finite sums, real inner-product spaces, and Bochner-integral covariance expansion, with SOptLib finite-uniform average APIs
Used in: recursive finite-product gradient estimators, where a centered row of component differences is converted into the `1 / card row` variance bound before the estimator recurrence.
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finite_function_row_centered_average_second_moment_le
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [Nonempty α] [Nonempty β]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : β → V) (hmean : finiteUniformAverage f = 0) :
    (Fintype.card (α → β) : ℝ)⁻¹ *
        Finset.univ.sum
          (fun r : α → β =>
            ‖((Fintype.card α : ℝ)⁻¹) •
              Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) ≤
      finiteUniformAverage (fun b : β => ‖f b‖ ^ 2) /
        (Fintype.card α : ℝ) := by
  classical
  let m : ℝ := Fintype.card α
  let rowCard : ℝ := Fintype.card (α → β)
  let diagAvg : ℝ := finiteUniformAverage (fun b : β => ‖f b‖ ^ 2)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hrow_ne : rowCard ≠ 0 := by
    dsimp [rowCard]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (α → β) ≠ 0)
  have hcov :
      Finset.univ.sum
          (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) =
        Finset.univ.sum
          (fun j : α =>
            Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2)) := by
    letI : MeasurableSpace (α → β) := ⊤
    let μ : MeasureTheory.Measure (α → β) := MeasureTheory.Measure.count
    have hdiag :=
      integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
        (μ := μ) (I := (Finset.univ : Finset α))
        (δ := fun j r => f (r j))
        (hmeas := by
          intro j hj
          exact
            aestronglyMeasurable_of_countable_key_reconstruction
              (μ := μ) (Y := fun r : α → β => r)
              (Z := fun r : α → β => f (r j))
              (by exact measurable_id.aemeasurable)
              (fun r : α → β => f (r j))
              (by exact Filter.EventuallyEq.rfl))
        (hL2 := by
          intro j hj
          exact integrable_of_finite_range
            ((measurable_of_finite
              (fun r : α → β => ‖f (r j)‖ ^ 2)).aestronglyMeasurable)
            (Set.toFinite (Set.range (fun r : α → β => ‖f (r j)‖ ^ 2))))
        (hcross := by
          intro j hj l hl hjl
          have hcross_avg :
              finiteUniformAverage
                (fun r : α → β => inner ℝ (f (r j)) (f (r l))) = 0 :=
            finiteUniformAverage_function_eval_inner_eval_eq_zero_of_average_zero
              (α := α) (β := β) (V := V) hjl f hmean
          have hsum_zero :
              Finset.univ.sum
                (fun r : α → β => inner ℝ (f (r j)) (f (r l))) = 0 := by
            have hcard_ne : (Fintype.card (α → β) : ℝ)⁻¹ ≠ 0 := by
              exact inv_ne_zero
                (by exact_mod_cast
                  (Fintype.card_ne_zero : Fintype.card (α → β) ≠ 0))
            rw [finiteUniformAverage_def] at hcross_avg
            exact (smul_eq_zero.mp hcross_avg).resolve_left hcard_ne
          simpa [μ] using hsum_zero)
    simpa [μ] using hdiag
  have hdiag_avg :
      ∀ j : α,
        (Fintype.card (α → β) : ℝ)⁻¹ *
            Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2) =
          diagAvg := by
    intro j
    have h :=
      finite_uniform_average_function_eval_eq
        (α := α) (β := β) (V := ℝ) j (fun b : β => ‖f b‖ ^ 2)
    simpa [finiteUniformAverage_def, diagAvg] using h
  have hscaled :
      Finset.univ.sum
          (fun r : α → β =>
            ‖((Fintype.card α : ℝ)⁻¹) •
              Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) =
        (m⁻¹) ^ 2 *
          Finset.univ.sum
            (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    have hnonneg : 0 ≤ (Fintype.card α : ℝ)⁻¹ := by positivity
    simp [m, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, sq]
    ring
  calc
    (Fintype.card (α → β) : ℝ)⁻¹ *
        Finset.univ.sum
          (fun r : α → β =>
            ‖((Fintype.card α : ℝ)⁻¹) •
              Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) =
      (m⁻¹) ^ 2 *
        ((Fintype.card (α → β) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2)) := by
        rw [hscaled]
        ring
    _ = (m⁻¹) ^ 2 *
        ((Fintype.card (α → β) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun j : α =>
              Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2))) := by
        rw [hcov]
    _ = (m⁻¹) ^ 2 *
        Finset.univ.sum (fun _j : α => diagAvg) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact hdiag_avg j
    _ = diagAvg / (Fintype.card α : ℝ) := by
        simp [m]
        field_simp [hm_ne]
    _ ≤ finiteUniformAverage (fun b : β => ‖f b‖ ^ 2) /
        (Fintype.card α : ℝ) := by
        rfl

end SOptLib
