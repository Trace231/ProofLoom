import SOptLib.Model.Selection

noncomputable section

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: uniform finite average under coordinate evaluation of function rows; orig was the PAGE-local `finiteUniformAverage_function_eval_eq`.
-- generality used: finite types `α` and `β`, a chosen coordinate `j : α`, and an additive commutative monoid with real module structure `V`; no topology, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: finite-product sampling proofs can replace the row space, coordinate, and additive response function while reusing that a uniformly sampled function row has a uniform coordinate marginal.
-- counterargument checked: `finiteUniformAverage_comp_equiv` only handles direct reindexing by an equivalence, while this statement additionally aggregates the unused coordinates; Mathlib and SOptLib have no theorem for this fixed-coordinate marginal identity.
-- coverage search: searched `finite uniform average function evaluation coordinate`, `finiteUniformAverage`, and `Fintype.sum_prod_type`; existing hits provide the average definition, centering algebra, or arbitrary equivalence reindexing, so coverage is partial.
-- minimal hypotheses: `[Fintype α] [Fintype β] [Fintype (α → β)] [Nonempty β]
-- [AddCommMonoid V] [Module ℝ V]` are exactly those used for the finite
-- function-space product decomposition and scalar cancellation.

/-- The finite uniform average of a function row evaluated at one coordinate equals
 the finite uniform average of the underlying coordinate function.

Layer: Glue | Gap: Level 1 (finite function-row coordinate marginal)
Proof: Decompose the finite function space into the chosen coordinate and the remaining coordinates, reindex the finite sum through that equivalence, and cancel the constant multiplicity after expanding the normalized averages.
Source: Mathlib finite-type equivalences, finite sums over products, and real-module scalar algebra, with SOptLib's finite-uniform average API
Used in: PAGE variance calculations that replace a uniform function-row sample by the uniform component distribution at a selected coordinate; the same step applies to any finite product sampling estimator
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finite_uniform_average_function_eval_eq
    {α β V : Type*} [Fintype α] [Fintype β] [Fintype (α → β)] [Nonempty β]
    [AddCommMonoid V] [Module ℝ V]
    (j : α) (f : β → V) :
    finiteUniformAverage (fun r : α → β => f (r j)) =
      finiteUniformAverage f := by
  classical
  let rest := {i : α // i ≠ j}
  let e : (α → β) ≃ β × (rest → β) := by
    refine
      { toFun := fun r : α → β =>
          (r j, fun i : rest => r i.1)
        invFun := fun p : β × (rest → β) => fun i : α =>
          if h : i = j then p.1 else p.2 ⟨i, h⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro r
      funext i
      by_cases h : i = j
      · simp [h]
      · simp [h]
    · intro p
      ext i
      · simp
      · simp [i.2]
  have hsum_reindex :
      (Finset.univ.sum (fun r : α → β => f (r j))) =
        Finset.univ.sum (fun p : β × (rest → β) => f p.1) := by
    refine Fintype.sum_equiv e (fun r : α → β => f (r j))
      (fun p : β × (rest → β) => f p.1) ?_
    intro r
    rfl
  have hsum_prod :
      (Finset.univ.sum (fun p : β × (rest → β) => f p.1)) =
        Finset.univ.sum (fun b : β =>
          Finset.univ.sum (fun _ : rest → β => f b)) := by
    rw [Fintype.sum_prod_type]
  have hsum_const :
      (Finset.univ.sum (fun b : β =>
          Finset.univ.sum (fun _ : rest → β => f b))) =
        Finset.univ.sum (fun b : β =>
          Fintype.card (rest → β) • f b) := by
    simp
  have hcard : Fintype.card (α → β) =
      Fintype.card β * Fintype.card (rest → β) := by
    rw [← Fintype.card_prod, ← Fintype.card_congr e]
  rw [finiteUniformAverage_def, finiteUniformAverage_def,
    hsum_reindex, hsum_prod, hsum_const]
  rw [← Finset.smul_sum]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul]
  rw [hcard]
  congr 1
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0)
  field_simp
  rw [Nat.cast_mul]
  ring

end SOptLib
