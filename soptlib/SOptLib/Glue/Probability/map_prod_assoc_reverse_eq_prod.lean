import SOptLib.Glue.Probability

-- Generalization plan (G0):
-- concept/name: reverse reassociation of a nested product measure; orig was map_prod_assoc_reverse_eq_prod
-- generality used: arbitrary measurable carriers A, β, C; measures μ, ν, κ with SFinite instances; no optimization-specific assumptions
-- portable call pattern: stochastic proofs that reindex a three-factor product law from A × (β × C) to (A × β) × C; carrier types and finite measures change while the pushforward equality stays fixed
-- counterargument checked: the candidate is more than a caller-side expression because it packages measurable-map composition and reverse use of product associativity; no matching SOptLib/Mathlib declaration was found
-- coverage search: searched `prodAssoc_prod`, reverse product reassociation, and map/product associativity; Mathlib provides only the forward `Measure.prodAssoc_prod`, so this reverse contract is a genuine Glue gap
-- minimal hypotheses: measurable-space instances and `[SFinite μ] [SFinite ν] [SFinite κ]`, exactly those consumed by product/map APIs

open MeasureTheory

noncomputable section

/-- Reverse product associativity as a pushforward by the canonical reassociation map.

Layer: Glue | Gap: Level 1 (reverse pushforward for nested product measures)
Proof: Compose the forward `Measure.prodAssoc_prod` identity with measurable map composition, then identify the composite reassociation map pointwise.
Source: Mathlib MeasureTheory product measures, measurable equivalences, and pushforward map composition
Used in: stochastic mini-batch proofs that regroup a refresh-stream law, recursive-prefix law, and current-row law into a left-associated product
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, Richtárik — PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization, recursive mini-batch product-law proof -/
theorem map_prod_assoc_reverse_eq_prod
    {A β C : Type*} [MeasurableSpace A] [MeasurableSpace β] [MeasurableSpace C]
    (μ : MeasureTheory.Measure A) (ν : MeasureTheory.Measure β)
    (κ : MeasureTheory.Measure C)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] [MeasureTheory.SFinite κ] :
    MeasureTheory.Measure.map
        (fun z : A × (β × C) => ((z.1, z.2.1), z.2.2))
        (μ.prod (ν.prod κ)) =
      (μ.prod ν).prod κ := by
  classical
  let splitRight : A × (β × C) → (A × β) × C :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hsplitMeas : Measurable splitRight := by
    simpa [splitRight] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have hforward :
      MeasureTheory.Measure.map
          (MeasurableEquiv.prodAssoc : (A × β) × C ≃ᵐ A × β × C)
          ((μ.prod ν).prod κ) =
        μ.prod (ν.prod κ) := by
    exact MeasureTheory.Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := κ)
  calc
    MeasureTheory.Measure.map splitRight (μ.prod (ν.prod κ)) =
        MeasureTheory.Measure.map splitRight
          (MeasureTheory.Measure.map
            (MeasurableEquiv.prodAssoc : (A × β) × C ≃ᵐ A × β × C)
            ((μ.prod ν).prod κ)) := by
          rw [hforward]
    _ = (μ.prod ν).prod κ := by
        rw [MeasureTheory.Measure.map_map]
        · trans MeasureTheory.Measure.map id ((μ.prod ν).prod κ)
          · apply MeasureTheory.Measure.map_congr
            filter_upwards with x
            rcases x with ⟨⟨a, b⟩, c⟩
            rfl
          · simp
        · exact hsplitMeas
        · exact
            (MeasurableEquiv.prodAssoc : (A × β) × C ≃ᵐ A × β × C).measurable

end
