import SOptLib.Glue.Probability
import SOptLib.Glue.Probability.map_prod_prod_shuffle_eq_prod
-- Generalization plan (G0):
-- concept/name: four-coordinate product-measure shuffle under a measurable permutation; orig was map_prod_prod_prod_shuffle_eq_prod
-- generality used: arbitrary measurable carriers A, β, C, D; measures μ, ν, κ, τ with SFinite instances; no optimization-specific assumptions
-- portable call pattern: stochastic algorithms that regroup a history/branch/sample product law and move the second coordinate behind the third while preserving the fourth; carriers and laws vary while the pushforward equality remains fixed
-- counterargument checked: Mathlib supplies product reassociation, product-map transport, and two-coordinate swap, while the complete four-coordinate permutation is absent; the theorem composes these substantive steps and is not a paper-only wrapper
-- coverage search: searched product-measure shuffle, fourfold product permutation, prodAssoc_prod, prod_swap, map_prod_map, and existing SOptLib entries; only the three-coordinate shuffle and reverse reassociation were found
-- minimal hypotheses: measurable-space instances and [SFinite μ] [SFinite ν] [SFinite κ] [SFinite τ], exactly those required by the product/map APIs

open MeasureTheory

noncomputable section

/-- Reassociate a four-coordinate product measure and move the second coordinate
behind the third, leaving the fourth coordinate last.

Layer: Glue | Gap: Level 1 (four-coordinate product-law permutation)
Proof: Split the right product, apply the reusable three-coordinate shuffle to the left block, transport product measures through measurable maps, and identify the composite map pointwise.
Source: Mathlib MeasureTheory product measures, measurable equivalences, and pushforward map composition
Used in: stochastic random-source proofs that reorder a past key, current branch, refresh/recursive sample block, and current recursive row before combining the resulting law with the output coordinate
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, Richtárik — PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization, ICML 2021, Algorithm 1 -/
theorem map_prod_prod_prod_shuffle_eq_prod
    {A β C D : Type*} [MeasurableSpace A] [MeasurableSpace β]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure β) (κ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite κ] [SFinite τ] :
    Measure.map
        (fun z : (A × β) × (C × D) =>
          (((z.1.1, z.2.1), z.1.2), z.2.2))
        ((μ.prod ν).prod (κ.prod τ)) =
      ((μ.prod κ).prod ν).prod τ := by
  classical
  let splitRight : (A × β) × (C × D) → ((A × β) × C) × D :=
    fun z => ((z.1, z.2.1), z.2.2)
  let shuffleLeft : ((A × β) × C) → (A × C) × β :=
    fun z => ((z.1.1, z.2), z.1.2)
  have hsplitMeas : Measurable splitRight := by
    simpa [splitRight] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have hshuffleMeas : Measurable shuffleLeft := by
    simpa [shuffleLeft] using
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst)
  have hsplit :
      Measure.map splitRight ((μ.prod ν).prod (κ.prod τ)) =
        ((μ.prod ν).prod κ).prod τ := by
    have hforward :
        Measure.map
            (MeasurableEquiv.prodAssoc : ((A × β) × C) × D ≃ᵐ
              (A × β) × C × D)
            (((μ.prod ν).prod κ).prod τ) =
          (μ.prod ν).prod (κ.prod τ) := by
      exact Measure.prodAssoc_prod
        (μ := μ.prod ν) (ν := κ) (τ := τ)
    calc
      Measure.map splitRight ((μ.prod ν).prod (κ.prod τ)) =
          Measure.map splitRight
            (Measure.map
              (MeasurableEquiv.prodAssoc : ((A × β) × C) × D ≃ᵐ
                (A × β) × C × D)
              (((μ.prod ν).prod κ).prod τ)) := by
            rw [hforward]
      _ = ((μ.prod ν).prod κ).prod τ := by
          rw [Measure.map_map]
          · trans Measure.map id (((μ.prod ν).prod κ).prod τ)
            · apply Measure.map_congr
              filter_upwards with x
              rcases x with ⟨⟨⟨a, b⟩, c⟩, d⟩
              rfl
            · simp
          · exact hsplitMeas
          · exact
              (MeasurableEquiv.prodAssoc : ((A × β) × C) × D ≃ᵐ
                (A × β) × C × D).measurable
  have hshuffleProd :
      Measure.map (Prod.map shuffleLeft id)
          (((μ.prod ν).prod κ).prod τ) =
        ((μ.prod κ).prod ν).prod τ := by
    calc
      Measure.map (Prod.map shuffleLeft id)
          (((μ.prod ν).prod κ).prod τ) =
        (Measure.map shuffleLeft ((μ.prod ν).prod κ)).prod
          (Measure.map id τ) := by
          exact (Measure.map_prod_map
            ((μ.prod ν).prod κ) τ hshuffleMeas measurable_id).symm
      _ = ((μ.prod κ).prod ν).prod τ := by
          rw [map_prod_prod_shuffle_eq_prod (μ := μ) (ν := ν) (κ := κ)]
          simp
  have hmap :
      Measure.map
          (fun z : (A × β) × (C × D) =>
            (((z.1.1, z.2.1), z.1.2), z.2.2))
          ((μ.prod ν).prod (κ.prod τ)) =
        Measure.map (Prod.map shuffleLeft id)
          (Measure.map splitRight ((μ.prod ν).prod (κ.prod τ))) := by
    symm
    calc
      Measure.map (Prod.map shuffleLeft id)
          (Measure.map splitRight ((μ.prod ν).prod (κ.prod τ))) =
        Measure.map ((Prod.map shuffleLeft id) ∘ splitRight)
          ((μ.prod ν).prod (κ.prod τ)) := by
          rw [Measure.map_map]
          · exact (hshuffleMeas.prodMap measurable_id)
          · exact hsplitMeas
      _ = Measure.map
          (fun z : (A × β) × (C × D) =>
            (((z.1.1, z.2.1), z.1.2), z.2.2))
          ((μ.prod ν).prod (κ.prod τ)) := by
          apply Measure.map_congr
          filter_upwards with z
          rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
          rfl
  rw [hmap, hsplit, hshuffleProd]

end
