import SOptLib.Glue.Probability
import SOptLib.Glue.Probability.map_prod_assoc_reverse_eq_prod
-- Generalization plan (G0):
-- concept/name: canonical middle-coordinate shuffle of a triple product measure; orig was map_prod_prod_shuffle_eq_prod
-- generality used: arbitrary measurable carriers A, β, C; measures μ, ν, κ with SFinite instances; no optimization-specific assumptions
-- portable call pattern: stochastic proofs that regroup a triple product law and move a current branch or sample coordinate behind a history coordinate; carrier types and measures change while the pushforward equality stays fixed
-- counterargument checked: the prior reverse-association theorem handles only reassociation and does not swap the middle and final coordinates; this theorem packages the additional measurable permutation and is a substantive reusable Glue step
-- coverage search: searched product-measure shuffle, prodAssoc_prod, map_prod_map, and reverse reassociation; Mathlib and SOptLib provide the component APIs but no theorem for this complete permutation
-- minimal hypotheses: measurable-space instances and [SFinite μ] [SFinite ν] [SFinite κ], exactly those consumed by product/map APIs

open MeasureTheory

noncomputable section

/-- Reassociate a triple product measure and move the middle coordinate to the end.

Layer: Glue | Gap: Level 1 (middle-coordinate permutation of a triple product law)
Proof: Compose measurable pushforwards for reassociation and coordinate swap, using product-measure associativity and map-of-product identities, then identify the composite map pointwise.
Source: Mathlib MeasureTheory product measures, measurable equivalences, and pushforward map composition
Used in: PAGE random-source proofs that move the current branch coordinate after the past-key coordinates before combining it with a recursive sample law
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, Richtárik — PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization, ICML 2021, Algorithm 1 -/
theorem map_prod_prod_shuffle_eq_prod
    {A β C : Type*} [MeasurableSpace A] [MeasurableSpace β] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure β) (κ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite κ] :
    Measure.map
        (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
        ((μ.prod ν).prod κ) =
      (μ.prod κ).prod ν := by
  classical
  let assoc₁ : ((A × β) × C) → A × β × C :=
    fun z => (z.1.1, z.1.2, z.2)
  let swap₂ : A × β × C → A × C × β :=
    fun z => (z.1, z.2.2, z.2.1)
  let assoc₂ : A × C × β → (A × C) × β :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hassoc₁_meas : Measurable assoc₁ := by
    simpa [assoc₁] using
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hswap₂_meas : Measurable swap₂ := by
    simpa [swap₂] using
      (measurable_fst.prodMk (measurable_swap.comp measurable_snd))
  have hassoc₂_meas : Measurable assoc₂ := by
    simpa [assoc₂] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have h_assoc₁ :
      Measure.map assoc₁ ((μ.prod ν).prod κ) =
        μ.prod (ν.prod κ) := by
    simpa [assoc₁] using
      (Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := κ))
  have h_swap :
      Measure.map swap₂ (μ.prod (ν.prod κ)) =
        μ.prod (κ.prod ν) := by
    calc
      Measure.map swap₂ (μ.prod (ν.prod κ)) =
          (Measure.map id μ).prod (Measure.map Prod.swap (ν.prod κ)) := by
            simpa [swap₂] using
              (Measure.map_prod_map μ (ν.prod κ)
                measurable_id measurable_swap).symm
      _ = μ.prod (κ.prod ν) := by
          simp [Measure.prod_swap]
  have h_assoc₂ :
      Measure.map assoc₂ (μ.prod (κ.prod ν)) =
        (μ.prod κ).prod ν := by
    have hforward :
        Measure.map
            (MeasurableEquiv.prodAssoc : (A × C) × β ≃ᵐ A × C × β)
            ((μ.prod κ).prod ν) =
          μ.prod (κ.prod ν) := by
      exact Measure.prodAssoc_prod (μ := μ) (ν := κ) (τ := ν)
    calc
      Measure.map assoc₂ (μ.prod (κ.prod ν)) =
          Measure.map assoc₂
            (Measure.map
              (MeasurableEquiv.prodAssoc : (A × C) × β ≃ᵐ A × C × β)
              ((μ.prod κ).prod ν)) := by
            rw [hforward]
      _ = (μ.prod κ).prod ν := by
          rw [Measure.map_map]
          · trans Measure.map id ((μ.prod κ).prod ν)
            · apply Measure.map_congr
              filter_upwards with x
              rcases x with ⟨⟨a, c⟩, b⟩
              rfl
            · simp
          · exact hassoc₂_meas
          · exact
              (MeasurableEquiv.prodAssoc : (A × C) × β ≃ᵐ A × C × β).measurable
  have h_nested :
      Measure.map assoc₂
          (Measure.map swap₂
            (Measure.map assoc₁ ((μ.prod ν).prod κ))) =
        Measure.map
          (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
          ((μ.prod ν).prod κ) := by
    calc
      Measure.map assoc₂
          (Measure.map swap₂
            (Measure.map assoc₁ ((μ.prod ν).prod κ))) =
          Measure.map ((assoc₂ ∘ swap₂) ∘ assoc₁)
            ((μ.prod ν).prod κ) := by
          rw [Measure.map_map]
          · rw [Measure.map_map]
            · exact hassoc₂_meas.comp hswap₂_meas
            · exact hassoc₁_meas
          · exact hassoc₂_meas
          · exact hswap₂_meas
      _ = Measure.map
          (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
          ((μ.prod ν).prod κ) := by
          apply Measure.map_congr
          filter_upwards with z
          rcases z with ⟨⟨a, b⟩, c⟩
          rfl
  calc
    Measure.map
        (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
        ((μ.prod ν).prod κ) =
        Measure.map assoc₂
          (Measure.map swap₂
            (Measure.map assoc₁ ((μ.prod ν).prod κ))) := by
          exact h_nested.symm
    _ = (μ.prod κ).prod ν := by
        rw [h_assoc₁, h_swap, h_assoc₂]

end
