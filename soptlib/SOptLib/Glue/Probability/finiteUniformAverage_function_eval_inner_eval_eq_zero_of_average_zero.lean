import SOptLib.Model.Selection

noncomputable section

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: zero cross-inner-product average for distinct coordinates of a finite uniform function row; orig was the PAGE-local `finiteUniformAverage_function_eval_inner_eval_eq_zero_of_average_zero`.
-- generality used: finite types `α` and `β`, distinct coordinates `j l : α`, a nonempty value type `β`, and a real inner-product space `V`; no measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: finite-product sampling proofs can replace the row index type, value type, and centered Hilbert-valued function while reusing that distinct independently uniform coordinates have zero cross inner product when the coordinate mean vanishes.
-- counterargument checked: the existing one-coordinate marginal theorem only identifies a single coordinate average; it does not establish the two-coordinate factorization needed for an inner product, and Mathlib/SOptLib have no equivalent centered cross-coordinate theorem.
-- coverage search: searched `finite uniform average inner product coordinate zero`, `finiteUniformAverage`, and finite product sum APIs; existing hits were the finite-uniform average definition and one-coordinate marginal theorem, so coverage is partial.
-- minimal hypotheses: `[Fintype α] [Fintype β] [DecidableEq α] [Nonempty β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]` are exactly those used for the finite row decomposition, scalar cancellation, and inner-product linearity.

/-- Distinct coordinates of a uniformly sampled finite function row have zero
cross-inner-product average when the underlying Hilbert-valued function has zero
uniform average.

Layer: Glue | Gap: Level 1 (finite-product centered cross-coordinate cancellation)
Proof: Decompose the finite function space into the two selected coordinates and the remaining coordinates, reindex the finite sum through that equivalence, and cancel one coordinate sum using the zero finite average.
Source: Mathlib finite-type equivalences, finite sums over products, and real inner-product linearity, with SOptLib's finite-uniform average API
Used in: variance calculations for recursive finite-product gradient estimators, where off-diagonal row-coordinate cross terms are removed before applying a diagonal second-moment bound
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finiteUniformAverage_function_eval_inner_eval_eq_zero_of_average_zero
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [Nonempty β]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {j l : α} (hjl : j ≠ l) (f : β → V)
    (hmean : finiteUniformAverage f = 0) :
    finiteUniformAverage
      (fun r : α → β => inner ℝ (f (r j)) (f (r l))) = 0 := by
  classical
  let rest := {i : α // i ≠ j ∧ i ≠ l}
  let e : (α → β) ≃ β × β × (rest → β) := by
    refine
      { toFun := fun r : α → β =>
          (r j, r l, fun i : rest => r i.1)
        invFun := fun p : β × β × (rest → β) => fun i : α =>
          if hij : i = j then
            p.1
          else if hil : i = l then
            p.2.1
          else
            p.2.2 ⟨i, hij, hil⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro r
      funext i
      by_cases hij : i = j
      · simp [hij]
      · by_cases hil : i = l
        · have hlj : l ≠ j := by
            intro h
            exact hij (hil.trans h)
          simp [hij, hil, hlj]
        · simp [hij, hil]
    · intro p
      ext i
      · simp
      · simp [hjl.symm]
      · simp [i.2.1, i.2.2]
  have hsum_reindex :
      (Finset.univ.sum
          (fun r : α → β => inner ℝ (f (r j)) (f (r l)))) =
        Finset.univ.sum
          (fun p : β × β × (rest → β) => inner ℝ (f p.1) (f p.2.1)) := by
    refine Fintype.sum_equiv e
      (fun r : α → β => inner ℝ (f (r j)) (f (r l)))
      (fun p : β × β × (rest → β) => inner ℝ (f p.1) (f p.2.1)) ?_
    intro r
    rfl
  have hsum_prod :
      (Finset.univ.sum
          (fun p : β × β × (rest → β) => inner ℝ (f p.1) (f p.2.1))) =
        Finset.univ.sum (fun b₁ : β =>
          Finset.univ.sum (fun b₂ : β =>
            Finset.univ.sum (fun _ : rest → β => inner ℝ (f b₁) (f b₂)))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro b₁ _hb₁
    rw [Fintype.sum_prod_type]
  have hsum_const :
      (Finset.univ.sum (fun b₁ : β =>
          Finset.univ.sum (fun b₂ : β =>
            Finset.univ.sum (fun _ : rest → β => inner ℝ (f b₁) (f b₂))))) =
        Finset.univ.sum (fun b₁ : β =>
          Finset.univ.sum (fun b₂ : β =>
            Fintype.card (rest → β) • inner ℝ (f b₁) (f b₂))) := by
    simp
  have hsum_f_zero : Finset.univ.sum f = 0 := by
    have hcard_ne : (Fintype.card β : ℝ)⁻¹ ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0))
    rw [finiteUniformAverage_def] at hmean
    exact (smul_eq_zero.mp hmean).resolve_left hcard_ne
  have hinner_sum_zero :
      ∀ b₁ : β, Finset.univ.sum (fun b₂ : β => inner ℝ (f b₁) (f b₂)) = 0 := by
    intro b₁
    calc
      Finset.univ.sum (fun b₂ : β => inner ℝ (f b₁) (f b₂))
          = inner ℝ (f b₁) (Finset.univ.sum f) := by
              rw [inner_sum]
      _ = 0 := by
              rw [hsum_f_zero]
              simp
  have hscaled_inner_sum_zero :
      ∀ b₁ : β,
        Finset.univ.sum
          (fun b₂ : β =>
            ((Fintype.card β : ℝ) ^ Fintype.card rest) *
              inner ℝ (f b₁) (f b₂)) = 0 := by
    intro b₁
    rw [← Finset.mul_sum, hinner_sum_zero b₁]
    simp
  rw [finiteUniformAverage_def, hsum_reindex, hsum_prod, hsum_const]
  simp [hscaled_inner_sum_zero]

end SOptLib
