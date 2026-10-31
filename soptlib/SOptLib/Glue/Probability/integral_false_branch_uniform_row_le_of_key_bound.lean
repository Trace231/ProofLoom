-- Generalization plan (G0):
-- concept/name: false-branch uniform-row integral bound from a keywise row bound;
--   orig was line4_false_branch_recursive_row_integral_le_key_bound.
-- generality used: a countable measurable key with finite observed range, an
--   arbitrary finite row type, a finite source measure, scalar row payload and key bound, and a supplied
--   false-branch-to-row-average transport equality; no optimization, norm, or
--   finite-dimensional assumptions are needed.
-- portable call pattern: stochastic variance-reduction and randomized-refresh
--   proofs first transport a nonrefresh sample to a uniform finite-row average,
--   then call this theorem with a nonnegative branch weight and a keywise row
--   average bound; the key, row payload, bound, weight, and transport law vary.
-- counterargument checked: this is not paper-local traceability or a pure rename.
--   Mathlib supplies integral monotonicity and finite-range integrability, while
--   the combined branch-weighted row-bound composition is absent. The preceding
--   transport equality is intentionally a premise so other product-law APIs can
--   feed the same reusable inequality.
-- coverage search: searched "false branch uniform row integral bound key",
--   "integral mono weighted finite range measurable key bound", and the SOptLib
--   catalog. Closest hits were integral_false_branch_uniform_row_transport and
--   integral_sample_le_integral_bound_of_indep_weighted_fiber_bound; the former
--   gives equality only, and the latter assumes a different independent-sample
--   interface. No existing declaration covers this transport-plus-bound shape.
-- minimal hypotheses: only a finite (not probability) source measure, countable
--   measurable-singleton key, finite row type, key a.e.-measurability, a
--   nonnegative branch weight, and the pointwise row-average bound are needed.

import SOptLib.Glue.Probability

open MeasureTheory
open scoped BigOperators

/-- Bound a false-branch integral after transport to a uniform finite-row average.

If a false-branch sample integral equals a branch-weighted uniform row average,
then a nonnegative branch weight and a pointwise keywise bound on that row
average give the corresponding integral bound for the keywise majorant.

Layer: Glue | Gap: Level 1 (branch-weighted finite-row integral comparison)
Proof: reconstruct the transported row average and key bound from the finite
  countable key with finite observed range, obtain integrability from their finite ranges, and apply
  `MeasureTheory.integral_mono_ae` after multiplying the pointwise bound by the
  nonnegative branch weight.
Source: Mathlib finite-range Bochner integrability and ordered integral
  monotonicity, composed with the finite-row transport API used by stochastic
  sampling laws
Used in: PAGE's recursive nonrefresh estimator branch, where the transported
  minibatch row average is bounded by the old estimator error plus the smoothness
  displacement budget
Book citation: book/research/PAGE.json#/key_lemmas/2/proof/2
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal
  Probabilistic Gradient Estimator for Nonconvex Optimization, Algorithm 1 -/
theorem integral_false_branch_uniform_row_le_of_key_bound
    {Ω K R : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    [Countable K] [MeasurableSingletonClass K] [Fintype R]
    (P : Measure Ω) [IsFiniteMeasure P]
    (W : Ω → K) (branch : Ω → Bool) (Y : Ω → R)
    (F : K → R → ℝ) (G : K → ℝ) (q : ℝ)
    (hW : AEMeasurable W P)
    (hfin : (Set.range W).Finite)
    (htransport :
      (∫ ω : Ω,
          (if branch ω = false then F (W ω) (Y ω) else 0) ∂P) =
        ∫ ω : Ω,
          (1 - q) *
            ((Fintype.card R : ℝ)⁻¹ *
              Finset.univ.sum (fun r : R => F (W ω) r)) ∂P)
    (hq : 0 ≤ 1 - q)
    (h_bound :
      ∀ k : K,
        (Fintype.card R : ℝ)⁻¹ *
            Finset.univ.sum (fun r : R => F k r) ≤ G k) :
    (∫ ω : Ω,
        (if branch ω = false then F (W ω) (Y ω) else 0) ∂P) ≤
      ∫ ω : Ω, (1 - q) * G (W ω) ∂P := by
  classical
  let avgF : K → ℝ := fun k =>
    (1 - q) *
      ((Fintype.card R : ℝ)⁻¹ *
        Finset.univ.sum (fun r : R => F k r))
  let weightedG : K → ℝ := fun k => (1 - q) * G k
  have hleft_int :
      Integrable (fun ω : Ω => avgF (W ω)) P := by
    have haestrong :
        AEStronglyMeasurable (fun ω : Ω => avgF (W ω)) P := by
      exact
        aestronglyMeasurable_of_countable_key_reconstruction
          (μ := P) (Y := W) (Z := fun ω : Ω => avgF (W ω))
          hW avgF (Filter.Eventually.of_forall fun _ω => rfl)
    have hfin : (Set.range (fun ω : Ω => avgF (W ω))).Finite := by
      have hsubset :
          Set.range (fun ω : Ω => avgF (W ω)) ⊆
            avgF '' Set.range W := by
        rintro z ⟨ω, rfl⟩
        exact ⟨W ω, ⟨ω, rfl⟩, rfl⟩
      exact hfin.image avgF |>.subset hsubset
    exact integrable_of_finite_range haestrong hfin
  have hright_int :
      Integrable (fun ω : Ω => weightedG (W ω)) P := by
    have haestrong :
        AEStronglyMeasurable (fun ω : Ω => weightedG (W ω)) P := by
      exact
        aestronglyMeasurable_of_countable_key_reconstruction
          (μ := P) (Y := W) (Z := fun ω : Ω => weightedG (W ω))
          hW weightedG (Filter.Eventually.of_forall fun _ω => rfl)
    have hfin : (Set.range (fun ω : Ω => weightedG (W ω))).Finite := by
      have hsubset :
          Set.range (fun ω : Ω => weightedG (W ω)) ⊆
            weightedG '' Set.range W := by
        rintro z ⟨ω, rfl⟩
        exact ⟨W ω, ⟨ω, rfl⟩, rfl⟩
      exact hfin.image weightedG |>.subset hsubset
    exact integrable_of_finite_range haestrong hfin
  have hmono :
      (∫ ω : Ω, avgF (W ω) ∂P) ≤
        ∫ ω : Ω, weightedG (W ω) ∂P := by
    refine MeasureTheory.integral_mono_ae hleft_int hright_int ?_
    filter_upwards with ω
    exact mul_le_mul_of_nonneg_left (h_bound (W ω)) hq
  rw [htransport]
  simpa [avgF, weightedG] using hmono
