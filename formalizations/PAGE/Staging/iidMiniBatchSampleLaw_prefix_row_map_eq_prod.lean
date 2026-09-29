-- Import the exact current modules required by the checked declarations.
--
-- Generalization plan (G0):
-- concept/name: iid mini-batch prefix/current row product law;
--   orig was iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod.
-- generality used: arbitrary measurable sample type A, finite batch index type C,
--   arbitrary probability marginal μ, and natural cutoff t; no finite-dimensional
--   or optimization assumptions are used.
-- portable call pattern: split the strict history of iid mini-batch rows from the
--   current row in PAGE-style recursive estimators, stochastic block methods, or
--   variance-reduced algorithms; the sample marginal, batch index type, and time
--   cutoff can all vary while the product-law conclusion is unchanged.
-- counterargument checked: this is not a caller-side expression or pure wrapper;
--   it derives row independence from coordinate independence and combines it with
--   the nontrivial finite-product row marginal. Existing APIs provide only the
--   coordinate law or generic infinite-product decomposition separately.
-- coverage search: searched "iid mini-batch prefix current row product map law",
--   "independence finite prefix current row pushforward product", and inspected
--   SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval, iidMiniBatchSampleLaw_map_eval,
--   iid_mini_batch_sample_law_row_reindex_map_eq_pi, and
--   infinitePi_prefix_current_map_eq_prod (partial coverage; none has the
--   reindexed finite-row conclusion).
-- minimal hypotheses: [MeasurableSpace A], [Fintype C], and [IsProbabilityMeasure μ];
--   DecidableEq/nonempty assumptions and finite-dimensional structure are unused.

import Mathlib.Probability.Independence.InfinitePi
import SOptLib.Glue.Probability
import SOptLib.Model.BlockSampling
import Staging.iidMiniBatchSampleLaw_row_reindex_map_eq_pi
import Staging.infinitePi_prefix_current_map_eq_prod

open MeasureTheory ProbabilityTheory

/-- The strict prefix and current row of an iid mini-batch path have product law
after reindexing each row from `Fin (card C)` to the finite batch type `C`.

Layer: Model | Gap: Level 1 (iid mini-batch prefix/current product-law decomposition)
Proof: transport the generic infinite-product prefix/current decomposition
through the measurable row reindexing on both factors, then identify the current
row law using the finite-row reindexing theorem.
Source: the generic infinite-product prefix/current law, Mathlib measure-map
composition and product transport, and the iid mini-batch row marginal theorem.
Used in: PAGE-style recursive estimator proofs when separating all prior batch
rows from the fresh current batch before combining their laws with branch events.
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, Richtarik, PAGE: A Simple and Optimal
Probabilistic Gradient Estimator for Nonconvex Optimization, ICML 2021,
Algorithm 1 (PAGE) -/
theorem iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod
    {A C : Type*} [MeasurableSpace A] [Fintype C]
    (μ : Measure A) [IsProbabilityMeasure μ] (t : ℕ) :
    Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          (fun k : Fin t => fun j : C => omega k.1 (Fintype.equivFin C j),
            fun j : C => omega t (Fintype.equivFin C j)))
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ) =
      (Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun k : Fin t => fun j : C => omega k.1 (Fintype.equivFin C j))
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)).prod
        (Measure.pi (fun _ : C => μ)) := by
  classical
  let rowMap : (Fin (Fintype.card C) → A) → (C → A) :=
    fun v j => v (Fintype.equivFin C j)
  let prefixRowMap : (Fin t → (Fin (Fintype.card C) → A)) →
      (Fin t → C → A) := fun v k => rowMap (v k)
  have hrowMapMeas : Measurable rowMap := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact measurable_pi_apply (Fintype.equivFin C j)
  have hprefixRowMapMeas : Measurable prefixRowMap := by
    refine measurable_pi_lambda _ ?_
    intro k
    exact hrowMapMeas.comp (measurable_pi_apply k)
  have hrowLaw :
      Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
            rowMap (omega t))
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ) =
        Measure.pi (fun _ : C => μ) := by
    simpa [rowMap] using
      (iid_mini_batch_sample_law_row_reindex_map_eq_pi
        (A := A) (C := C) μ t)
  have hbase :=
    infinitePi_prefix_current_map_eq_prod
      (A := Fin (Fintype.card C) → A)
      (fun _ : ℕ => Measure.infinitePi (fun _ : Fin (Fintype.card C) => μ)) t
  have hcurrentRawLaw :
      Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A => omega t)
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ) =
        Measure.infinitePi (fun _ : Fin (Fintype.card C) => μ) := by
    unfold SOptLib.iidMiniBatchSampleLaw
    simpa [SOptLib.miniBatchSamplePath] using
      (Measure.infinitePi_map_eval
        (μ := fun _ : ℕ => Measure.infinitePi (fun _ : Fin (Fintype.card C) => μ)) t)
  have hbase' :
      Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
            (fun k : Fin t => omega k.1, omega t))
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ) =
      (Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun k : Fin t => omega k.1)
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)).prod
        (Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A => omega t)
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ)) := by
    rw [hcurrentRawLaw]
    simpa [SOptLib.iidMiniBatchSampleLaw, SOptLib.miniBatchSamplePath] using hbase
  have hrawPrefixMeas :
      Measurable
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun k : Fin t => omega k.1) := by
    refine measurable_pi_lambda _ ?_
    intro k
    exact measurable_pi_apply k.1
  have hrawCurrentMeas :
      Measurable
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A => omega t) :=
    measurable_pi_apply t
  have hmapBase :=
    congrArg (Measure.map (Prod.map prefixRowMap rowMap)) hbase'
  rw [Measure.map_map (hprefixRowMapMeas.prodMap hrowMapMeas)
      (hrawPrefixMeas.prodMk hrawCurrentMeas),
    ← Measure.map_prod_map _ _ hprefixRowMapMeas hrowMapMeas,
    Measure.map_map hprefixRowMapMeas hrawPrefixMeas,
    Measure.map_map hrowMapMeas hrawCurrentMeas] at hmapBase
  simpa only [Function.comp_def, Prod.map_apply, hrowLaw] using hmapBase
