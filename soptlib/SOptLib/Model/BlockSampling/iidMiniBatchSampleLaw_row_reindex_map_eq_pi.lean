-- Import the exact current modules required by the checked declarations.
--
-- Generalization plan (G0):
-- concept/name: iid mini-batch row reindexing and finite product law;
--   orig was iidMiniBatchSampleLaw_row_map_eq_uniform_pi.
-- generality used: an arbitrary measurable sample type A, finite nonempty batch
--   index type C, arbitrary probability measure μ on A, and a natural row k;
--   no finite-dimensional or optimization assumptions are used.
-- portable call pattern: identify the law of one row of any iid finite-batch
--   stream after changing its Fin index to an algorithm's finite batch type;
--   the sample marginal, batch type, and row number may vary.
-- counterargument checked: this is more than a caller-side expression because
--   it composes the nested infinite-product marginal theorem with the product
--   measure transport across a finite equivalence; existing coordinate-marginal
--   APIs do not provide the joint row law.
-- coverage search: searched "iid mini-batch row pushforward finite product
--   measure reindex" and "map reindexed finite product equals product measure";
--   found SOptLib.iidMiniBatchSampleLaw_map_eval and Mathlib's
--   Measure.infinitePi_map_eval, infinitePi_eq_pi, and
--   measurePreserving_piCongrLeft (partial ingredients, no matching row-law
--   theorem). The active registry has no alpha-equivalent approved entry.
-- minimal hypotheses: [MeasurableSpace A], [Fintype C], [Nonempty C], and
--   [IsProbabilityMeasure μ]; DecidableEq C is retained for compatibility with
--   finite-index algorithm frames.

import Mathlib.Probability.Independence.InfinitePi
import SOptLib.Model.BlockSampling

open MeasureTheory

/-- A fixed row of the canonical iid mini-batch law is the finite product of its
marginal measure after reindexing from `Fin (card C)` to a finite batch type `C`.

Layer: Model | Gap: Level 1 (finite product row-law reindexing)
Proof: Project the row from the outer infinite product, rewrite the finite inner
product as `Measure.pi`, and transport it across the measurable index equivalence.
Source: Mathlib infinite product measures, coordinate maps, and measurable
equivalences of Pi spaces, together with SOptLib's iid mini-batch law.
Used in: PAGE-style estimator proofs when the current mini-batch row is expressed
with the paper's finite batch indices before combining it with a history law.
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, Richtarik, PAGE: A Simple and Optimal
Probabilistic Gradient Estimator for Nonconvex Optimization, ICML 2021,
Algorithm 1 (PAGE) -/
theorem iid_mini_batch_sample_law_row_reindex_map_eq_pi
    {A C : Type*} [MeasurableSpace A] [Fintype C]
    (μ : Measure A) [IsProbabilityMeasure μ] (k : ℕ) :
    Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun j : C => omega k (Fintype.equivFin C j))
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ) =
      Measure.pi (fun _ : C => μ) := by
  classical
  let rowEquiv : (Fin (Fintype.card C) → A) ≃ᵐ (C → A) :=
    MeasurableEquiv.piCongrLeft (fun _ : C => A) (Fintype.equivFin C).symm
  have hrowMeas :
      Measure.map
          (rowEquiv ∘
            fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A => omega k)
          (SOptLib.iidMiniBatchSampleLaw (Fintype.card C) μ) =
        Measure.pi (fun _ : C => μ) := by
    unfold SOptLib.iidMiniBatchSampleLaw
    rw [← Measure.map_map]
    · have houter :
          Measure.map
              (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A => omega k)
              (Measure.infinitePi fun _ : ℕ =>
                Measure.infinitePi fun _ : Fin (Fintype.card C) => μ) =
            Measure.infinitePi (fun _ : Fin (Fintype.card C) => μ) := by
        simpa [SOptLib.miniBatchSamplePath] using
          (Measure.infinitePi_map_eval
            (μ := fun _ : ℕ =>
              Measure.infinitePi fun _ : Fin (Fintype.card C) => μ) k)
      rw [houter]
      rw [Measure.infinitePi_eq_pi]
      simpa [rowEquiv] using
        (measurePreserving_piCongrLeft
          (μ := fun _ : C => μ)
          (f := (Fintype.equivFin C).symm)).map_eq
    · exact rowEquiv.measurable
    · fun_prop
  have hfun :
      (rowEquiv ∘ fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A => omega k) =
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun j : C => omega k (Fintype.equivFin C j)) := by
    funext omega j
    simpa [rowEquiv] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : C => A)
        (Fintype.equivFin C).symm (omega k) (Fintype.equivFin C j))
  rw [← hfun]
  exact hrowMeas
