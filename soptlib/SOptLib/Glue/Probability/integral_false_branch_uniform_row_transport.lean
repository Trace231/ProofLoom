-- Generalization plan (G0):
-- concept/name: false-branch uniform-row integral transport; orig was
--   line4_false_branch_recursive_row_integral.
-- generality used: measurable source and key spaces, measurable key/row
--   singletons, a finite row type, finite measures, an a.e.-measurable
--   finite-range key/Boolean pair, and a normed real vector space of payloads.
-- portable call pattern: loopless variance reduction and randomized refresh
--   estimators average a fresh row on the nonrefresh branch; the key, row,
--   product laws, branch mass, and vector or scalar payload may all change.
-- counterargument checked: the existing weighted-fiber transport handles one
--   fresh index only. This theorem combines two product laws, computes the
--   Boolean branch weight, and supplies integrability from finite support.
--   Neither that API nor an indicator-probability identity alone gives this
--   conclusion. No new definition is needed for the ordinary finite sum.
-- coverage search: "integral of independent Boolean branch and uniform finite
--   row equals branch probability times row average" and "integral indicator
--   independent event equals probability times integral finite average" found
--   partial hits expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law,
--   SOptLib.integral_comp_indep_finite_uniform_eq_integral_inv_card_sum, and
--   setIntegral_indicator_eq_prob_mul_of_indep. Full signatures and companion
--   integrable_map_of_finite_range / integrable_prod_of_finite_left_map_fintype_right
--   were inspected; the first and the integrability APIs are reused below.
--   The round registry has no equivalent entry. Mathlib LeanSearch returned
--   HTTP 500; the project symbol search supplied the verified partial APIs.
-- minimal hypotheses: probability is weakened to finite measure, finite key
--   type to finite range, and real payload to NormedSpace over the reals;
--   no completeness, finite dimension, optimization assumptions, or separate
--   integrability assumptions are needed. Only the false-branch mass is used.

import SOptLib.Glue.Probability

open MeasureTheory
open scoped BigOperators

/-- Under successive product laws for a key/Boolean pair and a uniform finite
row, the false-branch integral is the branch mass times the row-average integral.

Layer: Glue | Gap: Level 1 (Boolean branch and uniform finite-row integral transport)
Proof: apply weighted-fiber joint-law transport first to the row and then to
  the Boolean branch; finite-range pushforward integrability supplies both
  product kernels, and the singleton masses simplify the two finite sums.
Source: Mathlib Bochner product and pushforward integration, with SOptLib
  weighted-fiber joint-law transport and finite-support integrability
Used in: recursive gradient-estimator cross-term cancellation and second-moment
  bounds after conditioning on the past and selecting the nonrefresh branch
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, and Richtarik, PAGE: A Simple and Optimal
  Probabilistic Gradient Estimator for Nonconvex Optimization, Algorithm 1 -/
theorem integral_false_branch_uniform_row_transport
    {Ω K R E : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    [MeasurableSingletonClass K] [MeasurableSpace R] [Fintype R]
    [MeasurableSingletonClass R] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P]
    (W : Ω → K × Bool) (Y : Ω → R) (F : K → R → E)
    (ν : Measure R) [IsFiniteMeasure ν]
    (β : Measure Bool) [IsFiniteMeasure β] (p : ℝ)
    (hW : AEMeasurable W P) (hY : AEMeasurable Y P)
    (hrow : Measure.map (fun ω => (W ω, Y ω)) P = (Measure.map W P).prod ν)
    (hbranch : Measure.map W P = (Measure.map (fun ω => (W ω).1) P).prod β)
    (hfin : (Set.range W).Finite)
    (huniform : ∀ r : R, ν.real {r} = (Fintype.card R : ℝ)⁻¹)
    (hfalse : β.real {false} = 1 - p) :
    (∫ ω, (if (W ω).2 = false then F (W ω).1 (Y ω) else 0) ∂P) =
      ∫ ω, (1 - p) • ((Fintype.card R : ℝ)⁻¹ • ∑ r, F (W ω).1 r) ∂P := by
  classical
  let G : K × Bool → R → E := fun k r => if k.2 = false then F k.1 r else 0
  let avg : K → E := fun k => (Fintype.card R : ℝ)⁻¹ • ∑ r, F k r
  have hrow_transport :=
    expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law
      (P := P) (W := W) (Y := Y) ν (fun _ => (Fintype.card R : ℝ)⁻¹) G
      hW hY hrow huniform
      (integrable_prod_of_finite_left_map_fintype_right W hW hfin ν G)
      (integrable_map_of_finite_range W hW hfin _).aestronglyMeasurable
  have hkey_fin : (Set.range (fun ω => (W ω).1)).Finite :=
    (hfin.image Prod.fst).subset (by
      rintro k ⟨ω, rfl⟩
      exact ⟨W ω, ⟨ω, rfl⟩, rfl⟩)
  let H : K → Bool → E := fun k b => if b = false then avg k else 0
  have hbranch_transport :=
    expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law
      (P := P) (W := fun ω => (W ω).1) (Y := fun ω => (W ω).2)
      β (fun b => β.real {b}) H hW.fst hW.snd hbranch (fun _ => rfl)
      (integrable_prod_of_finite_left_map_fintype_right
        (fun ω => (W ω).1) hW.fst hkey_fin β H)
      (integrable_map_of_finite_range
        (fun ω => (W ω).1) hW.fst hkey_fin _).aestronglyMeasurable
  calc
    (∫ ω, (if (W ω).2 = false then F (W ω).1 (Y ω) else 0) ∂P) =
        ∫ ω, (if (W ω).2 = false then avg (W ω).1 else 0) ∂P := by
      refine hrow_transport.trans (integral_congr_ae ?_)
      filter_upwards with ω
      by_cases hb : (W ω).2 = false <;> simp [G, avg, hb, Finset.smul_sum]
    _ = ∫ ω, (1 - p) • ((Fintype.card R : ℝ)⁻¹ • ∑ r, F (W ω).1 r) ∂P := by
      simpa [H, avg, hfalse] using hbranch_transport
