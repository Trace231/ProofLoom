import Mathlib.Probability.Independence.InfinitePi
import SOptLib.Model.BlockSampling
import SOptLib.Model.BlockSampling.iidMiniBatchSampleLaw_prefix_row_map_eq_prod
import SOptLib.Glue.Probability.map_prod_assoc_reverse_eq_prod
open MeasureTheory

noncomputable section

-- Generalization plan (G0):
-- concept/name: paired iid mini-batch prefix/current-row product law
-- generality used: arbitrary measurable sample type A, finite batch index types C and D,
--   a probability measure μ on A, and a natural cutoff t; no optimization or finite-dimensional assumptions
-- portable call pattern: variance-reduced and stochastic block algorithms that pair an independent
--   refresh prefix with a recursive strict prefix/current row; μ, C, D, and t may all change
-- counterargument checked: this is not a caller-side expression or a pure wrapper; it composes
--   the recursive iid prefix/current theorem, independent product pushforward, and measure reassociation
--   Existing single-stream prefix/current and row-law entries do not cover the two-stream paired
--   output shape, so the paired contract remains a reusable library step.
-- coverage search: searched paired iid mini-batch prefix current row product map law and inspected
--   iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod, infinitePi_prefix_current_map_eq_prod,
--   and map_prod_assoc_reverse_eq_prod; coverage is partial, with no matching paired declaration
-- minimal hypotheses: [MeasurableSpace A], [Fintype C], [Fintype D], and [IsProbabilityMeasure μ]

/-- The refresh prefix and recursive prefix/current row of two independent iid mini-batch streams
have the displayed product law after finite-index reindexing.

Layer: Model | Gap: Level 1 (paired iid mini-batch prefix/current product-law decomposition)
Proof: map the independent stream factors and apply the iid prefix/current law to the recursive factor;
then reassociate the resulting three-factor product measure and identify the mapped prefixes.
Source: Mathlib infinite-product measures, measurable product maps, and product-measure reassociation,
together with SOptLib's iid mini-batch row and prefix/current product-law theorems.
Used in: variance-reduced estimator proofs that separate all refresh history and recursive history from
the fresh recursive row before combining those laws with a branch event.
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, Richtárik — PAGE: A Simple and Optimal Probabilistic Gradient Estimator
for Nonconvex Optimization, ICML 2021, Algorithm 1 (PAGE) -/
theorem paired_iidMiniBatch_prefix_current_row_map_eq_prod
    {A C D : Type*} [MeasurableSpace A] [Fintype C] [Fintype D]
    (μ : Measure A) [IsProbabilityMeasure μ] (t : ℕ) :
    Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card C) A ×
              SOptLib.miniBatchSamplePath (Fintype.card D) A =>
          ((fun k : Fin (t + 1) => fun j : C =>
              z.1 k.1 (Fintype.equivFin C j),
            fun k : Fin t => fun j : D =>
              z.2 k.1 (Fintype.equivFin D j)),
            fun j : D => z.2 t (Fintype.equivFin D j)))
        ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) =
      (Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card C) A ×
              SOptLib.miniBatchSamplePath (Fintype.card D) A =>
          (fun k : Fin (t + 1) => fun j : C =>
              z.1 k.1 (Fintype.equivFin C j),
            fun k : Fin t => fun j : D =>
              z.2 k.1 (Fintype.equivFin D j)))
        ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ))).prod
        (Measure.pi (fun _ : D => μ)) := by
  classical
  let refreshKey :
      SOptLib.miniBatchSamplePath (Fintype.card C) A →
        Fin (t + 1) → C → A :=
    fun omega k j => omega k.1 (Fintype.equivFin C j)
  let recPrefix :
      SOptLib.miniBatchSamplePath (Fintype.card D) A →
        Fin t → D → A :=
    fun omega k j => omega k.1 (Fintype.equivFin D j)
  let recRow :
      SOptLib.miniBatchSamplePath (Fintype.card D) A → D → A :=
    fun omega j => omega t (Fintype.equivFin D j)
  let recPair :
      SOptLib.miniBatchSamplePath (Fintype.card D) A →
        (Fin t → D → A) × (D → A) :=
    fun omega => (recPrefix omega, recRow omega)
  have hCMeas : Measurable refreshKey := by
    refine measurable_pi_lambda _ ?_
    intro k
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin C j)).comp
      (measurable_pi_apply k.1)
  have hDPrefixMeas : Measurable recPrefix := by
    refine measurable_pi_lambda _ ?_
    intro k
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin D j)).comp
      (measurable_pi_apply k.1)
  have hDRowMeas : Measurable recRow := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin D j)).comp
      (measurable_pi_apply t)
  have hDPairMeas : Measurable recPair :=
    hDPrefixMeas.prodMk hDRowMeas
  have hDPairLaw :
      Measure.map recPair (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ) =
        (Measure.map recPrefix (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)).prod
          (Measure.pi (fun _ : D => μ)) := by
    simpa [SOptLib.iidMiniBatchSampleLaw, SOptLib.miniBatchSamplePath,
      recPair, recPrefix, recRow] using
      (iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod
        (A := A) (C := D) μ t)
  have hraw :
      Measure.map (Prod.map refreshKey recPair)
          ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
            (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) =
        (Measure.map refreshKey (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)).prod
          (Measure.map recPair (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) := by
    exact (Measure.map_prod_map
      (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)
      (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)
      hCMeas hDPairMeas).symm
  let splitRight :
      (Fin (t + 1) → C → A) × ((Fin t → D → A) × (D → A)) →
        ((Fin (t + 1) → C → A) × (Fin t → D → A)) × (D → A) :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hsplitMeas : Measurable splitRight := by
    simpa [splitRight] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have htargetAsSplit :
      Measure.map
          (fun z :
              SOptLib.miniBatchSamplePath (Fintype.card C) A ×
                SOptLib.miniBatchSamplePath (Fintype.card D) A =>
            ((refreshKey z.1, recPrefix z.2), recRow z.2))
          ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
            (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) =
        Measure.map splitRight
          (Measure.map (Prod.map refreshKey recPair)
            ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
              (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ))) := by
    simpa [splitRight, recPair] using
      (AEMeasurable.map_map_of_aemeasurable
        hsplitMeas.aemeasurable
        (hCMeas.prodMap hDPairMeas).aemeasurable).symm
  have hminiKey :
      Measure.map
          (fun z :
              SOptLib.miniBatchSamplePath (Fintype.card C) A ×
                SOptLib.miniBatchSamplePath (Fintype.card D) A =>
            (refreshKey z.1, recPrefix z.2))
          ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
            (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) =
        (Measure.map refreshKey (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)).prod
          (Measure.map recPrefix (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) := by
    exact (Measure.map_prod_map
      (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)
      (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)
      hCMeas hDPrefixMeas).symm
  calc
    Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card C) A ×
              SOptLib.miniBatchSamplePath (Fintype.card D) A =>
          ((fun k : Fin (t + 1) => fun j : C =>
              z.1 k.1 (Fintype.equivFin C j),
            fun k : Fin t => fun j : D =>
              z.2 k.1 (Fintype.equivFin D j)),
            fun j : D => z.2 t (Fintype.equivFin D j)))
        ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) =
      Measure.map
          (fun z :
              SOptLib.miniBatchSamplePath (Fintype.card C) A ×
                SOptLib.miniBatchSamplePath (Fintype.card D) A =>
            ((refreshKey z.1, recPrefix z.2), recRow z.2))
          ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
            (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)) := by
        rfl
    _ = Measure.map splitRight
          ((Measure.map refreshKey (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)).prod
            ((Measure.map recPrefix (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ)).prod
              (Measure.pi (fun _ : D => μ)))) := by
        rw [htargetAsSplit, hraw, hDPairLaw]
    _ = ((Measure.map refreshKey (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)).prod
          (Measure.map recPrefix (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ))).prod
          (Measure.pi (fun _ : D => μ)) := by
        exact map_prod_assoc_reverse_eq_prod
          (μ := Measure.map refreshKey (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ))
          (ν := Measure.map recPrefix (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ))
          (κ := Measure.pi (fun _ : D => μ))
    _ =
      (Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card C) A ×
              SOptLib.miniBatchSamplePath (Fintype.card D) A =>
          (fun k : Fin (t + 1) => fun j : C =>
              z.1 k.1 (Fintype.equivFin C j),
            fun k : Fin t => fun j : D =>
              z.2 k.1 (Fintype.equivFin D j)))
        ((SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ).prod
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card D) μ))).prod
        (Measure.pi (fun _ : D => μ)) := by
        rw [hminiKey]

end
