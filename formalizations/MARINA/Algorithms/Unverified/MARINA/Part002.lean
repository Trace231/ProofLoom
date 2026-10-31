import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SOptLib.Model.BlockSampling
import SOptLib.Model.BlockSampling.infinitePi_prefix_current_map_eq_prod
import SOptLib.Model.Iterates
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Model.ParameterChoices.PositiveRealParameter
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Objective.finiteAverageGradient_lipschitz_of_average_sq_smoothness
import SOptLib.Glue.Algebra.inner_neg_smul_eq_neg_half_eta_norm_sq_sub_step_sq_add_error_sq
import Algorithms.Unverified.MARINA.Part001

/-!
# MARINA family: source-facing object model

This file models Algorithms 1--4 of Gorbunov--Burlachenko--Li--Richtárik.
The estimator and iterate processes below are generated definitions, rather
than witness processes constrained by theorem hypotheses.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace MARINA

def iidStreamPrefixTailEquiv
    (A : Type*) [MeasurableSpace A] (N : ℕ) :
    (ℕ → A) ≃ᵐ ((Fin N → A) × (ℕ → A)) where
  toFun x := ((fun i => x i.1), fun k => x (N + k))
  invFun p k := if hk : k < N then p.1 ⟨k, hk⟩ else p.2 (k - N)
  left_inv x := by
    funext k
    by_cases hk : k < N
    · simp [hk]
    · simp [hk, Nat.add_sub_of_le (Nat.le_of_not_gt hk)]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp [i.2]
    · funext k
      simp
  measurable_toFun := by fun_prop
  measurable_invFun := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k < N <;> simp [hk] <;> fun_prop

/-- Completed measurability of a scalar cylinder on an iid stream descends to
the finite-prefix law.  This rules out hiding a nonmeasurable two-round
residual in the unused infinite tail of the canonical path. -/
theorem aestronglyMeasurable_prefix_of_comp
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    [IsProbabilityMeasure mu] (N : ℕ) (f : (Fin N → A) → ℝ)
    (h : AEStronglyMeasurable
      (fun x : ℕ → A => f (fun i : Fin N => x i.1))
      (SOptLib.iidStreamLaw mu)) :
    AEStronglyMeasurable f (Measure.infinitePi (fun _ : Fin N => mu)) := by
  let e := iidStreamPrefixTailEquiv A N
  have hemap : Measure.map e (SOptLib.iidStreamLaw mu) =
      (Measure.infinitePi (fun _ : Fin N => mu)).prod
        (SOptLib.iidStreamLaw mu) := by
    simpa [e, iidStreamPrefixTailEquiv] using
      (iidStream_prefix_tail_map_eq_prod mu N)
  have hpair : AEStronglyMeasurable
      (fun p : (Fin N → A) × (ℕ → A) => f p.1)
      (Measure.map e (SOptLib.iidStreamLaw mu)) := by
    apply e.measurableEmbedding.aestronglyMeasurable_map_iff.mpr
    simpa [e, iidStreamPrefixTailEquiv, Function.comp_def] using h
  rw [hemap] at hpair
  have hnull : NullMeasurable
      (f ∘ Prod.fst)
      ((Measure.infinitePi (fun _ : Fin N => mu)).prod
        (SOptLib.iidStreamLaw mu)) := by
    exact hpair.aemeasurable.nullMeasurable
  have hfnull : NullMeasurable f (Measure.infinitePi (fun _ : Fin N => mu)) :=
    (Measure.nullMeasurable_comp_fst).mp hnull
  exact hfnull.aemeasurable.aestronglyMeasurable

/-- A vector-valued strict-prefix random variable can be recovered from its
composition with the canonical iid stream.  Unlike the historical Eq. (46)
route, this transfer applies separately to exactly the query/residual
components used by the scalar calculation. -/
theorem aestronglyMeasurable_prefix_of_comp_general
    {A X : Type*} [MeasurableSpace A] [TopologicalSpace X]
    (mu : Measure A) [IsProbabilityMeasure mu] (N : ℕ)
    (f : (Fin N → A) → X)
    (h : AEStronglyMeasurable
      (fun x : ℕ → A => f (fun i : Fin N => x i.1))
      (SOptLib.iidStreamLaw mu)) :
    AEStronglyMeasurable f (Measure.infinitePi (fun _ : Fin N => mu)) := by
  let e := iidStreamPrefixTailEquiv A N
  have hemap : Measure.map e (SOptLib.iidStreamLaw mu) =
      (Measure.infinitePi (fun _ : Fin N => mu)).prod
        (SOptLib.iidStreamLaw mu) := by
    simpa [e, iidStreamPrefixTailEquiv] using
      (iidStream_prefix_tail_map_eq_prod mu N)
  have hpair : AEStronglyMeasurable
      (fun p : (Fin N → A) × (ℕ → A) => f p.1)
      (Measure.map e (SOptLib.iidStreamLaw mu)) := by
    apply e.measurableEmbedding.aestronglyMeasurable_map_iff.mpr
    simpa [e, iidStreamPrefixTailEquiv, Function.comp_def] using h
  rw [hemap] at hpair
  exact hpair.of_comp_fst
    (IsProbabilityMeasure.ne_zero (SOptLib.iidStreamLaw mu))

/-- Integrability analogue of
`aestronglyMeasurable_prefix_of_comp_general`, used to transport the scalar
step/error certificates to the strict-prefix carrier without constructing a
measurable complete state. -/
theorem integrable_prefix_of_comp_general
    {A X : Type*} [MeasurableSpace A] [NormedAddCommGroup X]
    (mu : Measure A) [IsProbabilityMeasure mu] (N : ℕ)
    (f : (Fin N → A) → X)
    (h : Integrable
      (fun x : ℕ → A => f (fun i : Fin N => x i.1))
      (SOptLib.iidStreamLaw mu)) :
    Integrable f (Measure.infinitePi (fun _ : Fin N => mu)) := by
  let e := iidStreamPrefixTailEquiv A N
  have hemap : Measure.map e (SOptLib.iidStreamLaw mu) =
      (Measure.infinitePi (fun _ : Fin N => mu)).prod
        (SOptLib.iidStreamLaw mu) := by
    simpa [e, iidStreamPrefixTailEquiv] using
      (iidStream_prefix_tail_map_eq_prod mu N)
  have hpair : Integrable
      (fun p : (Fin N → A) × (ℕ → A) => f p.1)
      (Measure.map e (SOptLib.iidStreamLaw mu)) := by
    apply e.measurableEmbedding.integrable_map_iff.mpr
    simpa [e, iidStreamPrefixTailEquiv, Function.comp_def] using h
  rw [hemap] at hpair
  exact hpair.of_comp_fst
    (IsProbabilityMeasure.ne_zero (SOptLib.iidStreamLaw mu))

/-- An initial random minibatch can be retained as part of the strict-past
carrier while the unused iid tail is discarded.  This is the executable
Algorithm 3 analogue of `aestronglyMeasurable_prefix_of_comp_general`. -/
theorem aestronglyMeasurable_initial_prefix_of_comp_general
    {B A X : Type*} [MeasurableSpace B] [MeasurableSpace A]
    [TopologicalSpace X]
    (mu0 : Measure B) [IsProbabilityMeasure mu0]
    (mu : Measure A) [IsProbabilityMeasure mu] (N : ℕ)
    (f : (B × (Fin N → A)) → X)
    (h : AEStronglyMeasurable
      (fun x : B × (ℕ → A) => f (x.1, fun i : Fin N => x.2 i.1))
      (mu0.prod (SOptLib.iidStreamLaw mu))) :
    AEStronglyMeasurable f
      (mu0.prod (Measure.infinitePi (fun _ : Fin N => mu))) := by
  let e0 := iidStreamPrefixTailEquiv A N
  let e : (B × (ℕ → A)) ≃ᵐ ((B × (Fin N → A)) × (ℕ → A)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0).trans
      MeasurableEquiv.prodAssoc.symm
  have hemap : Measure.map e (mu0.prod (SOptLib.iidStreamLaw mu)) =
      (mu0.prod (Measure.infinitePi (fun _ : Fin N => mu))).prod
        (SOptLib.iidStreamLaw mu) := by
    have hstream : Measure.map e0 (SOptLib.iidStreamLaw mu) =
        (Measure.infinitePi (fun _ : Fin N => mu)).prod
          (SOptLib.iidStreamLaw mu) := by
      simpa [e0, iidStreamPrefixTailEquiv] using
        (iidStream_prefix_tail_map_eq_prod mu N)
    have hfirst : Measure.map
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0)
        (mu0.prod (SOptLib.iidStreamLaw mu)) =
        mu0.prod ((Measure.infinitePi (fun _ : Fin N => mu)).prod
          (SOptLib.iidStreamLaw mu)) := by
      have hrefl : Measure.map (MeasurableEquiv.refl B) mu0 = mu0 := by
        change Measure.map id mu0 = mu0
        exact Measure.map_id
      calc
        _ = (Measure.map (MeasurableEquiv.refl B) mu0).prod
              (Measure.map e0 (SOptLib.iidStreamLaw mu)) :=
            (MeasureTheory.Measure.map_prod_map mu0
              (SOptLib.iidStreamLaw mu)
              (MeasurableEquiv.refl B).measurable e0.measurable).symm
        _ = _ := by rw [hrefl, hstream]
    change Measure.map
        (MeasurableEquiv.prodAssoc.symm ∘
          (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0))
          (mu0.prod (SOptLib.iidStreamLaw mu)) = _
    calc
      _ = Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map
            (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0)
            (mu0.prod (SOptLib.iidStreamLaw mu))) :=
        (MeasureTheory.Measure.map_map
          MeasurableEquiv.prodAssoc.symm.measurable
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl B) e0).measurable).symm
      _ = Measure.map MeasurableEquiv.prodAssoc.symm
          (mu0.prod ((Measure.infinitePi (fun _ : Fin N => mu)).prod
            (SOptLib.iidStreamLaw mu))) := by rw [hfirst]
      _ = _ := by
        have hassoc : Measure.map MeasurableEquiv.prodAssoc
            ((mu0.prod (Measure.infinitePi (fun _ : Fin N => mu))).prod
              (SOptLib.iidStreamLaw mu)) =
            mu0.prod ((Measure.infinitePi (fun _ : Fin N => mu)).prod
              (SOptLib.iidStreamLaw mu)) := Measure.prodAssoc_prod
        rw [← hassoc, MeasurableEquiv.prodAssoc.map_symm_map]
  have hpair : AEStronglyMeasurable
      (fun p : (B × (Fin N → A)) × (ℕ → A) => f p.1)
      (Measure.map e (mu0.prod (SOptLib.iidStreamLaw mu))) := by
    apply e.measurableEmbedding.aestronglyMeasurable_map_iff.mpr
    simpa [e, e0, iidStreamPrefixTailEquiv, Function.comp_def] using h
  rw [hemap] at hpair
  exact hpair.of_comp_fst
    (IsProbabilityMeasure.ne_zero (SOptLib.iidStreamLaw mu))

/-- Integrability companion to
`aestronglyMeasurable_initial_prefix_of_comp_general`. -/
theorem integrable_initial_prefix_of_comp_general
    {B A X : Type*} [MeasurableSpace B] [MeasurableSpace A]
    [NormedAddCommGroup X]
    (mu0 : Measure B) [IsProbabilityMeasure mu0]
    (mu : Measure A) [IsProbabilityMeasure mu] (N : ℕ)
    (f : (B × (Fin N → A)) → X)
    (h : Integrable
      (fun x : B × (ℕ → A) => f (x.1, fun i : Fin N => x.2 i.1))
      (mu0.prod (SOptLib.iidStreamLaw mu))) :
    Integrable f (mu0.prod (Measure.infinitePi (fun _ : Fin N => mu))) := by
  let e0 := iidStreamPrefixTailEquiv A N
  let e : (B × (ℕ → A)) ≃ᵐ ((B × (Fin N → A)) × (ℕ → A)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0).trans
      MeasurableEquiv.prodAssoc.symm
  have hemap : Measure.map e (mu0.prod (SOptLib.iidStreamLaw mu)) =
      (mu0.prod (Measure.infinitePi (fun _ : Fin N => mu))).prod
        (SOptLib.iidStreamLaw mu) := by
    have hstream : Measure.map e0 (SOptLib.iidStreamLaw mu) =
        (Measure.infinitePi (fun _ : Fin N => mu)).prod
          (SOptLib.iidStreamLaw mu) := by
      simpa [e0, iidStreamPrefixTailEquiv] using
        (iidStream_prefix_tail_map_eq_prod mu N)
    have hfirst : Measure.map
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0)
        (mu0.prod (SOptLib.iidStreamLaw mu)) =
        mu0.prod ((Measure.infinitePi (fun _ : Fin N => mu)).prod
          (SOptLib.iidStreamLaw mu)) := by
      have hrefl : Measure.map (MeasurableEquiv.refl B) mu0 = mu0 := by
        change Measure.map id mu0 = mu0
        exact Measure.map_id
      calc
        _ = (Measure.map (MeasurableEquiv.refl B) mu0).prod
              (Measure.map e0 (SOptLib.iidStreamLaw mu)) :=
            (MeasureTheory.Measure.map_prod_map mu0
              (SOptLib.iidStreamLaw mu)
              (MeasurableEquiv.refl B).measurable e0.measurable).symm
        _ = _ := by rw [hrefl, hstream]
    change Measure.map
        (MeasurableEquiv.prodAssoc.symm ∘
          (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0))
          (mu0.prod (SOptLib.iidStreamLaw mu)) = _
    calc
      _ = Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map
            (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) e0)
            (mu0.prod (SOptLib.iidStreamLaw mu))) :=
        (MeasureTheory.Measure.map_map
          MeasurableEquiv.prodAssoc.symm.measurable
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl B) e0).measurable).symm
      _ = Measure.map MeasurableEquiv.prodAssoc.symm
          (mu0.prod ((Measure.infinitePi (fun _ : Fin N => mu)).prod
            (SOptLib.iidStreamLaw mu))) := by rw [hfirst]
      _ = _ := by
        have hassoc : Measure.map MeasurableEquiv.prodAssoc
            ((mu0.prod (Measure.infinitePi (fun _ : Fin N => mu))).prod
              (SOptLib.iidStreamLaw mu)) =
            mu0.prod ((Measure.infinitePi (fun _ : Fin N => mu)).prod
              (SOptLib.iidStreamLaw mu)) := Measure.prodAssoc_prod
        rw [← hassoc, MeasurableEquiv.prodAssoc.map_symm_map]
  have hpair : Integrable
      (fun p : (B × (Fin N → A)) × (ℕ → A) => f p.1)
      (Measure.map e (mu0.prod (SOptLib.iidStreamLaw mu))) := by
    apply e.measurableEmbedding.integrable_map_iff.mpr
    simpa [e, e0, iidStreamPrefixTailEquiv, Function.comp_def] using h
  rw [hemap] at hpair
  exact hpair.of_comp_fst
    (IsProbabilityMeasure.ne_zero (SOptLib.iidStreamLaw mu))

/-- The first `N` coordinates of the canonical iid stream have the finite
product law, stated with the `Fin N` prefix representation used by Algorithm
3. -/
theorem iidStream_prefix_map_eq_infinitePi
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    [IsProbabilityMeasure mu] (N : ℕ) :
    Measure.map (fun x : ℕ → A => fun i : Fin N => x i.1)
        (SOptLib.iidStreamLaw mu) =
      Measure.infinitePi (fun _ : Fin N => mu) := by
  let e := iidStreamPrefixTailEquiv A N
  have hemap : Measure.map e (SOptLib.iidStreamLaw mu) =
      (Measure.infinitePi (fun _ : Fin N => mu)).prod
        (SOptLib.iidStreamLaw mu) := by
    simpa [e, iidStreamPrefixTailEquiv] using
      (iidStream_prefix_tail_map_eq_prod mu N)
  calc
    Measure.map (fun x : ℕ → A => fun i : Fin N => x i.1)
        (SOptLib.iidStreamLaw mu) =
        Measure.map Prod.fst (Measure.map e (SOptLib.iidStreamLaw mu)) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · exact measurable_fst
          · exact e.measurable
    _ = Measure.map Prod.fst
        ((Measure.infinitePi (fun _ : Fin N => mu)).prod
          (SOptLib.iidStreamLaw mu)) := by rw [hemap]
    _ = Measure.infinitePi (fun _ : Fin N => mu) := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]

abbrev OnlineGeneratedRefreshRound :=
  OnlineRoundNoise onlineCoarseCounterexampleWorkers
    onlineGeneratedRefreshBatch onlineGeneratedDifferenceBatch
    OnlineGeneratedRefreshSample Unit

abbrev OnlineGeneratedRefreshBatchNoise :=
  (i : Worker onlineCoarseCounterexampleWorkers) →
    Fin onlineGeneratedRefreshBatch.1 → OnlineGeneratedRefreshSample i

abbrev OnlineGeneratedRefreshDifferenceNoise :=
  (i : Worker onlineCoarseCounterexampleWorkers) →
    Fin onlineGeneratedDifferenceBatch.1 → OnlineGeneratedRefreshSample i

abbrev OnlineGeneratedRefreshCompressionNoise :=
  Worker onlineCoarseCounterexampleWorkers → Unit

abbrev OnlineGeneratedRefreshBatchRest :=
  ℝ × OnlineGeneratedRefreshSample 0

abbrev OnlineGeneratedRefreshRoundRest :=
  Bool × ((OnlineGeneratedRefreshBatchRest ×
    OnlineGeneratedRefreshDifferenceNoise) ×
      OnlineGeneratedRefreshCompressionNoise)

/-- Separate the first coarse coordinate of the two-sample refresh batch.
The equivalence is measure preserving for the canonical batch law. -/
def onlineGeneratedRefreshBatchFirstCoarseEquiv :
    OnlineGeneratedRefreshBatchNoise ≃ᵐ
      OnlineCoarseReal × OnlineGeneratedRefreshBatchRest :=
  ((MeasurableEquiv.funUnique
      (Worker onlineCoarseCounterexampleWorkers)
      (Fin onlineGeneratedRefreshBatch.1 → OnlineGeneratedRefreshSample 0)).trans
    (MeasurableEquiv.piFinTwo
      (fun _ : Fin 2 => OnlineGeneratedRefreshSample 0))).trans
    MeasurableEquiv.prodAssoc

theorem onlineGeneratedRefreshBatchFirstCoarseEquiv_measurePreserving :
    MeasurePreserving onlineGeneratedRefreshBatchFirstCoarseEquiv
      (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedRefreshBatch)
      (onlineCoarseLaw.prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (onlineGeneratedRefreshProblem.sampleLaw 0))) := by
  let sampleLaw := onlineGeneratedRefreshProblem.sampleLaw 0
  let rowLaw := Measure.infinitePi (fun _ : Fin 2 => sampleLaw)
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  letI : IsProbabilityMeasure sampleLaw :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability 0
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    infer_instance
  have hworker : MeasurePreserving
      (MeasurableEquiv.funUnique
        (Worker onlineCoarseCounterexampleWorkers)
        (Fin 2 → OnlineGeneratedRefreshSample 0))
      (Measure.infinitePi (fun _ : Worker onlineCoarseCounterexampleWorkers => rowLaw))
      rowLaw := by
    rw [Measure.infinitePi_eq_pi]
    exact measurePreserving_funUnique rowLaw
      (Worker onlineCoarseCounterexampleWorkers)
  have hrow : MeasurePreserving
      (MeasurableEquiv.piFinTwo
        (fun _ : Fin 2 => OnlineGeneratedRefreshSample 0))
      rowLaw (sampleLaw.prod sampleLaw) := by
    dsimp [rowLaw]
    rw [Measure.infinitePi_eq_pi]
    exact measurePreserving_piFinTwo (fun _ : Fin 2 => sampleLaw)
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (OnlineCoarseReal × ℝ) × OnlineGeneratedRefreshSample 0 ≃ᵐ
          OnlineCoarseReal × (ℝ × OnlineGeneratedRefreshSample 0))
      (sampleLaw.prod sampleLaw)
      (onlineCoarseLaw.prod
        ((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw)) := by
    refine ⟨MeasurableEquiv.prodAssoc.measurable, ?_⟩
    change Measure.map MeasurableEquiv.prodAssoc
        ((onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)).prod
          sampleLaw) = _
    exact Measure.prodAssoc_prod
  have h := hassoc.comp (hrow.comp hworker)
  simpa [onlineGeneratedRefreshBatchFirstCoarseEquiv,
    OnlineGeneratedRefreshBatchNoise, onlineGeneratedRefreshBatch,
    onlineBatchLaw, sampleLaw, rowLaw, Function.comp_def] using h

def onlineGeneratedRefreshRoundFirstCoarseEquiv :
    OnlineGeneratedRefreshRound ≃ᵐ
      OnlineCoarseReal × OnlineGeneratedRefreshRoundRest :=
  let eBatch := MeasurableEquiv.prodCongr (MeasurableEquiv.refl Bool)
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr
        onlineGeneratedRefreshBatchFirstCoarseEquiv
        (MeasurableEquiv.refl OnlineGeneratedRefreshDifferenceNoise))
      (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise))
  let e1 := (MeasurableEquiv.prodAssoc :
    (Bool × ((OnlineCoarseReal × OnlineGeneratedRefreshBatchRest) ×
      OnlineGeneratedRefreshDifferenceNoise)) ×
        OnlineGeneratedRefreshCompressionNoise ≃ᵐ
      Bool × (((OnlineCoarseReal × OnlineGeneratedRefreshBatchRest) ×
        OnlineGeneratedRefreshDifferenceNoise) ×
          OnlineGeneratedRefreshCompressionNoise)).symm
  let e2 := MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodAssoc :
      (Bool × (OnlineCoarseReal × OnlineGeneratedRefreshBatchRest)) ×
          OnlineGeneratedRefreshDifferenceNoise ≃ᵐ
        Bool × ((OnlineCoarseReal × OnlineGeneratedRefreshBatchRest) ×
          OnlineGeneratedRefreshDifferenceNoise)).symm
    (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise)
  let e3 := MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodAssoc :
        (Bool × OnlineCoarseReal) × OnlineGeneratedRefreshBatchRest ≃ᵐ
          Bool × (OnlineCoarseReal × OnlineGeneratedRefreshBatchRest)).symm
      (MeasurableEquiv.refl OnlineGeneratedRefreshDifferenceNoise))
    (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise)
  let e4 := MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
        (MeasurableEquiv.refl OnlineGeneratedRefreshBatchRest))
      (MeasurableEquiv.refl OnlineGeneratedRefreshDifferenceNoise))
    (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise)
  let e5 := MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc
      (MeasurableEquiv.refl OnlineGeneratedRefreshDifferenceNoise))
    (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise)
  let e6 := MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc
    (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise)
  let e7 := (MeasurableEquiv.prodAssoc :
    (OnlineCoarseReal ×
      ((Bool × OnlineGeneratedRefreshBatchRest) ×
        OnlineGeneratedRefreshDifferenceNoise)) ×
      OnlineGeneratedRefreshCompressionNoise ≃ᵐ
    OnlineCoarseReal ×
      (((Bool × OnlineGeneratedRefreshBatchRest) ×
        OnlineGeneratedRefreshDifferenceNoise) ×
          OnlineGeneratedRefreshCompressionNoise))
  let e8 := MeasurableEquiv.prodCongr (MeasurableEquiv.refl OnlineCoarseReal)
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc
      (MeasurableEquiv.refl OnlineGeneratedRefreshCompressionNoise))
  let e9 := MeasurableEquiv.prodCongr (MeasurableEquiv.refl OnlineCoarseReal)
    MeasurableEquiv.prodAssoc
  eBatch.trans (e1.trans (e2.trans (e3.trans (e4.trans
    (e5.trans (e6.trans (e7.trans (e8.trans e9))))))))

theorem measurePreserving_prodAssoc
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (mu : Measure A) (nu : Measure B) (tau : Measure C)
    [SFinite mu] [SFinite nu] [SFinite tau] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (A × B) × C ≃ᵐ A × (B × C))
      ((mu.prod nu).prod tau) (mu.prod (nu.prod tau)) :=
  ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩

theorem onlineGeneratedRefreshRoundFirstCoarseEquiv_measurePreserving :
    MeasurePreserving onlineGeneratedRefreshRoundFirstCoarseEquiv
      (onlineRoundLaw onlineGeneratedRefreshData)
      (onlineCoarseLaw.prod
        ((refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible).prod
          ((((ProbabilityTheory.gaussianReal 0 1).prod
              (onlineGeneratedRefreshProblem.sampleLaw 0)).prod
            (onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedDifferenceBatch)).prod
            (workerCompressionLaw onlineGeneratedRefreshData.quantizer)))) := by
  let batchRestLaw := (ProbabilityTheory.gaussianReal 0 1).prod
    (onlineGeneratedRefreshProblem.sampleLaw 0)
  let differenceLaw := onlineBatchLaw onlineGeneratedRefreshProblem
    onlineGeneratedDifferenceBatch
  let compressionLaw := workerCompressionLaw
    (n := onlineCoarseCounterexampleWorkers) onlineGeneratedRefreshData.quantizer
  let coinLaw := refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceLaw := by
    dsimp [differenceLaw]
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
    onlineGeneratedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    dsimp [compressionLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  have hBatch := onlineGeneratedRefreshBatchFirstCoarseEquiv_measurePreserving
  unfold onlineRoundLaw
  change MeasurePreserving onlineGeneratedRefreshRoundFirstCoarseEquiv
    (coinLaw.prod
      (((onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedRefreshBatch).prod
        differenceLaw).prod compressionLaw))
    (onlineCoarseLaw.prod
      (coinLaw.prod (((batchRestLaw.prod differenceLaw).prod compressionLaw))))
  have h0 := (MeasurePreserving.id coinLaw).prod
    ((hBatch.prod (MeasurePreserving.id differenceLaw)).prod
      (MeasurePreserving.id compressionLaw))
  have h1 := (measurePreserving_prodAssoc coinLaw
    ((onlineCoarseLaw.prod batchRestLaw).prod differenceLaw)
    compressionLaw).symm
  have h2 := ((measurePreserving_prodAssoc coinLaw
    (onlineCoarseLaw.prod batchRestLaw) differenceLaw).symm).prod
      (MeasurePreserving.id compressionLaw)
  have h3 := (((measurePreserving_prodAssoc coinLaw onlineCoarseLaw
    batchRestLaw).symm).prod (MeasurePreserving.id differenceLaw)).prod
      (MeasurePreserving.id compressionLaw)
  have h4 := (((Measure.measurePreserving_swap (μ := coinLaw)
    (ν := onlineCoarseLaw)).prod
      (MeasurePreserving.id batchRestLaw)).prod
        (MeasurePreserving.id differenceLaw)).prod
          (MeasurePreserving.id compressionLaw)
  have h5 := ((measurePreserving_prodAssoc onlineCoarseLaw coinLaw
    batchRestLaw).prod (MeasurePreserving.id differenceLaw)).prod
      (MeasurePreserving.id compressionLaw)
  have h6 := (measurePreserving_prodAssoc onlineCoarseLaw
    (coinLaw.prod batchRestLaw) differenceLaw).prod
      (MeasurePreserving.id compressionLaw)
  have h7 := measurePreserving_prodAssoc onlineCoarseLaw
    ((coinLaw.prod batchRestLaw).prod differenceLaw) compressionLaw
  have h8 := (MeasurePreserving.id onlineCoarseLaw).prod
    ((measurePreserving_prodAssoc coinLaw batchRestLaw differenceLaw).prod
      (MeasurePreserving.id compressionLaw))
  have h9 := (MeasurePreserving.id onlineCoarseLaw).prod
    (measurePreserving_prodAssoc coinLaw (batchRestLaw.prod differenceLaw)
      compressionLaw)
  have h := h9.comp (h8.comp (h7.comp (h6.comp (h5.comp
    (h4.comp (h3.comp (h2.comp (h1.comp h0))))))))
  simpa [onlineGeneratedRefreshRoundFirstCoarseEquiv, Function.comp_def] using h

noncomputable def onlineGeneratedRefreshRoundRestLaw :
    Measure OnlineGeneratedRefreshRoundRest :=
  (refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible).prod
    (((((ProbabilityTheory.gaussianReal 0 1).prod
        (onlineGeneratedRefreshProblem.sampleLaw 0)).prod
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch)).prod
      (workerCompressionLaw
        (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedRefreshData.quantizer)))

def onlineGeneratedRefreshRoundRestSecondCoarse
    (r : OnlineGeneratedRefreshRoundRest) : OnlineCoarseReal :=
  r.2.1.1.2.1

theorem onlineGeneratedRefreshRoundRestSecondCoarse_map :
    Measure.map onlineGeneratedRefreshRoundRestSecondCoarse
      onlineGeneratedRefreshRoundRestLaw = onlineCoarseLaw := by
  let sampleLaw := onlineGeneratedRefreshProblem.sampleLaw 0
  let differenceLaw := onlineBatchLaw onlineGeneratedRefreshProblem
    onlineGeneratedDifferenceBatch
  let compressionLaw := workerCompressionLaw
    (n := onlineCoarseCounterexampleWorkers) onlineGeneratedRefreshData.quantizer
  let coinLaw := refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  letI : IsProbabilityMeasure sampleLaw :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability 0
  haveI : IsProbabilityMeasure differenceLaw := by
    dsimp [differenceLaw]
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
    onlineGeneratedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    dsimp [compressionLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  change Measure.map
      (fun r : OnlineGeneratedRefreshRoundRest => r.2.1.1.2.1)
      (coinLaw.prod
        (((((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw).prod
          differenceLaw).prod compressionLaw))) = onlineCoarseLaw
  have h1 : MeasurePreserving Prod.snd
      (coinLaw.prod (((((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw).prod
        differenceLaw).prod compressionLaw)))
      (((((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw).prod
        differenceLaw).prod compressionLaw)) :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
  have h2 : MeasurePreserving Prod.fst
      (((((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw).prod
        differenceLaw).prod compressionLaw))
      ((((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw).prod
        differenceLaw)) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
  have h3 : MeasurePreserving Prod.fst
      ((((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw).prod differenceLaw))
      ((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
  have h4 : MeasurePreserving Prod.snd
      ((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw) sampleLaw :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
  have h5 : MeasurePreserving Prod.fst sampleLaw onlineCoarseLaw := by
    refine ⟨measurable_fst, ?_⟩
    change Measure.map Prod.fst
      (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) = _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  simpa [Function.comp_def] using h.map_eq

theorem onlineGeneratedRefreshCenteredCoordinate_injective :
    Function.Injective onlineGeneratedRefreshCenteredCoordinate := by
  intro x y hxy
  have hxden : 0 < 1 + |x| := by positivity
  have hyden : 0 < 1 + |y| := by positivity
  change x / (1 + |x|) = y / (1 + |y|) at hxy
  rw [div_eq_div_iff (ne_of_gt hxden) (ne_of_gt hyden)] at hxy
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at hxy
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy] at hxy
      nlinarith
    · have hy' : y < 0 := lt_of_not_ge hy
      rw [abs_of_neg hy'] at hxy
      nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hx'] at hxy
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy] at hxy
      nlinarith
    · have hy' : y < 0 := lt_of_not_ge hy
      rw [abs_of_neg hy'] at hxy
      nlinarith

noncomputable def onlineGeneratedRefreshQueryFormula (p : ℝ × ℝ) : ℝ :=
  -(10 + (onlineGeneratedRefreshCenteredCoordinate p.1 +
    onlineGeneratedRefreshCenteredCoordinate p.2) / 2)

theorem onlineGeneratedRefreshCenteredCoordinate_measurable :
    Measurable onlineGeneratedRefreshCenteredCoordinate := by
  unfold onlineGeneratedRefreshCenteredCoordinate
  exact measurable_id.div (measurable_const.add measurable_id.abs)

theorem onlineGeneratedRefreshQueryFormula_measurable :
    Measurable onlineGeneratedRefreshQueryFormula := by
  unfold onlineGeneratedRefreshQueryFormula
  exact (measurable_const.add
    (((onlineGeneratedRefreshCenteredCoordinate_measurable.comp measurable_fst).add
      (onlineGeneratedRefreshCenteredCoordinate_measurable.comp measurable_snd)).div_const 2)).neg

theorem onlineGeneratedRefreshQueryFormula_fiber_zero (z : ℝ) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1))
      {p | onlineGeneratedRefreshQueryFormula p = z} = 0 := by
  let ν := ProbabilityTheory.gaussianReal 0 1
  let s : Set (ℝ × ℝ) := {p | onlineGeneratedRefreshQueryFormula p = z}
  have hs : MeasurableSet s :=
    (measurableSet_singleton z).preimage
      onlineGeneratedRefreshQueryFormula_measurable
  rw [show {p | onlineGeneratedRefreshQueryFormula p = z} = s by rfl,
    Measure.prod_apply hs]
  apply lintegral_eq_zero_of_ae_eq_zero
  letI : NoAtoms (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.noAtoms_gaussianReal one_ne_zero
  filter_upwards [] with y
  by_cases hex : ∃ x : ℝ, onlineGeneratedRefreshQueryFormula (y, x) = z
  · rcases hex with ⟨x0, hx0⟩
    apply measure_mono_null
      (show Prod.mk y ⁻¹' s ⊆ {x0} by
        intro x hx
        have hxz : onlineGeneratedRefreshQueryFormula (y, x) = z := hx
        have hcenter : onlineGeneratedRefreshCenteredCoordinate x =
            onlineGeneratedRefreshCenteredCoordinate x0 := by
          dsimp [onlineGeneratedRefreshQueryFormula] at hxz hx0
          linarith
        exact Set.mem_singleton_iff.mpr
          (onlineGeneratedRefreshCenteredCoordinate_injective hcenter))
    exact measure_singleton x0
  · have hempty : Prod.mk y ⁻¹' s = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hex ⟨x, hx⟩)
      · intro hx
        simpa using hx
    simp [hempty]

theorem onlineGeneratedRefreshQueryFormula_noAtoms :
    NoAtoms (Measure.map onlineGeneratedRefreshQueryFormula
      ((ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1))) where
  measure_singleton z := by
    rw [Measure.map_apply onlineGeneratedRefreshQueryFormula_measurable
      (measurableSet_singleton z)]
    exact onlineGeneratedRefreshQueryFormula_fiber_zero z

noncomputable def onlineGeneratedRefreshRoundQueryFormula
    (z : OnlineGeneratedRefreshRound) : ℝ :=
  onlineGeneratedRefreshQueryFormula
    (((z.2.1.1 0 0).2), ((z.2.1.1 0 1).2))

theorem onlineGeneratedRefreshRoundQueryFormula_measurable :
    Measurable onlineGeneratedRefreshRoundQueryFormula := by
  unfold onlineGeneratedRefreshRoundQueryFormula
  exact onlineGeneratedRefreshQueryFormula_measurable.comp (by fun_prop)

theorem onlineGeneratedRefreshRoundQueryFormula_map :
    Measure.map onlineGeneratedRefreshRoundQueryFormula
        (onlineRoundLaw onlineGeneratedRefreshData) =
      Measure.map onlineGeneratedRefreshQueryFormula
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)) := by
  let pair : OnlineGeneratedRefreshRound → ℝ × ℝ := fun z =>
    (((z.2.1.1 0 0).2), ((z.2.1.1 0 1).2))
  have hpair : Measure.map pair (onlineRoundLaw onlineGeneratedRefreshData) =
      (ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1) := by
    let batchLaw := onlineBatchLaw onlineGeneratedRefreshProblem
      onlineGeneratedRefreshBatch
    let sampleLaw := onlineGeneratedRefreshProblem.sampleLaw 0
    letI (w : Worker onlineCoarseCounterexampleWorkers) :
        IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure batchLaw := by
      dsimp [batchLaw]
      unfold onlineBatchLaw
      infer_instance
    have hroundBatch : MeasurePreserving
        (fun z : OnlineGeneratedRefreshRound => z.2.1.1)
        (onlineRoundLaw onlineGeneratedRefreshData) batchLaw :=
      ⟨by fun_prop, by simpa [batchLaw] using
        onlineRoundLaw_refreshBatch_marginal onlineGeneratedRefreshData⟩
    have hbatch := onlineGeneratedRefreshBatchFirstCoarseEquiv_measurePreserving
    have hsnd : MeasurePreserving Prod.snd
        (onlineCoarseLaw.prod
          ((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw))
        ((ProbabilityTheory.gaussianReal 0 1).prod sampleLaw) :=
      ⟨measurable_snd, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    have hsampleSnd : MeasurePreserving Prod.snd sampleLaw
        (ProbabilityTheory.gaussianReal 0 1) := by
      refine ⟨measurable_snd, ?_⟩
      change Measure.map Prod.snd
        (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) = _
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    have hpairMap := (MeasurePreserving.id
      (ProbabilityTheory.gaussianReal 0 1)).prod hsampleSnd
    have h := hpairMap.comp (hsnd.comp (hbatch.comp hroundBatch))
    simpa [pair, onlineGeneratedRefreshBatchFirstCoarseEquiv,
      onlineGeneratedRefreshBatch, Function.comp_def] using h.map_eq
  calc
    Measure.map onlineGeneratedRefreshRoundQueryFormula
        (onlineRoundLaw onlineGeneratedRefreshData) =
      Measure.map onlineGeneratedRefreshQueryFormula
        (Measure.map pair (onlineRoundLaw onlineGeneratedRefreshData)) := by
          rw [Measure.map_map]
          · rfl
          · exact onlineGeneratedRefreshQueryFormula_measurable
          · fun_prop
    _ = _ := by rw [hpair]

theorem onlineGeneratedRefreshRoundQueryFormula_noAtoms :
    NoAtoms (Measure.map onlineGeneratedRefreshRoundQueryFormula
      (onlineRoundLaw onlineGeneratedRefreshData)) := by
  rw [onlineGeneratedRefreshRoundQueryFormula_map]
  exact onlineGeneratedRefreshQueryFormula_noAtoms

def onlineGeneratedRefreshTwoRoundFirstCoarseEquiv :
    (Fin 2 → OnlineGeneratedRefreshRound) ≃ᵐ
      OnlineCoarseReal ×
        (OnlineGeneratedRefreshRound × OnlineGeneratedRefreshRoundRest) :=
  let e0 := MeasurableEquiv.piFinTwo
    (fun _ : Fin 2 => OnlineGeneratedRefreshRound)
  let e1 := MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl OnlineGeneratedRefreshRound)
    onlineGeneratedRefreshRoundFirstCoarseEquiv
  let e2 := (MeasurableEquiv.prodAssoc :
    (OnlineGeneratedRefreshRound × OnlineCoarseReal) ×
        OnlineGeneratedRefreshRoundRest ≃ᵐ
      OnlineGeneratedRefreshRound ×
        (OnlineCoarseReal × OnlineGeneratedRefreshRoundRest)).symm
  let e3 := MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
    (MeasurableEquiv.refl OnlineGeneratedRefreshRoundRest)
  let e4 := (MeasurableEquiv.prodAssoc :
    (OnlineCoarseReal × OnlineGeneratedRefreshRound) ×
        OnlineGeneratedRefreshRoundRest ≃ᵐ
      OnlineCoarseReal ×
        (OnlineGeneratedRefreshRound × OnlineGeneratedRefreshRoundRest))
  e0.trans (e1.trans (e2.trans (e3.trans e4)))

theorem onlineGeneratedRefreshTwoRoundFirstCoarseEquiv_measurePreserving :
    MeasurePreserving onlineGeneratedRefreshTwoRoundFirstCoarseEquiv
      (Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw onlineGeneratedRefreshData))
      (onlineCoarseLaw.prod
        ((onlineRoundLaw onlineGeneratedRefreshData).prod
          onlineGeneratedRefreshRoundRestLaw)) := by
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw onlineGeneratedRefreshData
  let restLaw := onlineGeneratedRefreshRoundRestLaw
  haveI : IsProbabilityMeasure roundLaw := by
    letI (w : Worker onlineCoarseCounterexampleWorkers) :
        IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedRefreshBatch) := by
      unfold onlineBatchLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedDifferenceBatch) := by
      unfold onlineBatchLaw
      infer_instance
    letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
      onlineGeneratedRefreshData.quantizer.law_isProbability
    haveI : IsProbabilityMeasure
        (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
          onlineGeneratedRefreshData.quantizer) := by
      unfold workerCompressionLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible) := by
      unfold refreshLaw
      infer_instance
    unfold roundLaw onlineRoundLaw
    change IsProbabilityMeasure
      ((refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible).prod
        (((onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedRefreshBatch).prod
            (onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedDifferenceBatch)).prod
          (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
            onlineGeneratedRefreshData.quantizer)))
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    letI (w : Worker onlineCoarseCounterexampleWorkers) :
        IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedDifferenceBatch) := by
      unfold onlineBatchLaw
      infer_instance
    letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
      onlineGeneratedRefreshData.quantizer.law_isProbability
    haveI : IsProbabilityMeasure
        (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
          onlineGeneratedRefreshData.quantizer) := by
      unfold workerCompressionLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible) := by
      unfold refreshLaw
      infer_instance
    unfold restLaw onlineGeneratedRefreshRoundRestLaw
    infer_instance
  have h0 : MeasurePreserving
      (MeasurableEquiv.piFinTwo
        (fun _ : Fin 2 => OnlineGeneratedRefreshRound))
      (Measure.infinitePi (fun _ : Fin 2 => roundLaw))
      (roundLaw.prod roundLaw) := by
    rw [Measure.infinitePi_eq_pi]
    exact measurePreserving_piFinTwo (fun _ : Fin 2 => roundLaw)
  have h1 := (MeasurePreserving.id roundLaw).prod
    onlineGeneratedRefreshRoundFirstCoarseEquiv_measurePreserving
  have h2 := (measurePreserving_prodAssoc roundLaw onlineCoarseLaw restLaw).symm
  have h3 := (Measure.measurePreserving_swap
    (μ := roundLaw) (ν := onlineCoarseLaw)).prod
      (MeasurePreserving.id restLaw)
  have h4 := measurePreserving_prodAssoc onlineCoarseLaw roundLaw restLaw
  have h := h4.comp (h3.comp (h2.comp (h1.comp h0)))
  simpa [onlineGeneratedRefreshTwoRoundFirstCoarseEquiv,
    roundLaw, restLaw, Function.comp_def] using h

theorem onlineGeneratedRefresh_union_diagonals_not_nullMeasurable :
    ¬ NullMeasurableSet
      ({pref : Fin 2 → OnlineGeneratedRefreshRound |
        onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 0).1.val ∨
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 1).1.val})
      (Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw onlineGeneratedRefreshData)) := by
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw onlineGeneratedRefreshData
  let restLaw := onlineGeneratedRefreshRoundRestLaw
  let D : Set (OnlineCoarseReal ×
      (OnlineGeneratedRefreshRound × OnlineGeneratedRefreshRoundRest)) :=
    {p | p.1.val = onlineGeneratedRefreshRoundQueryFormula p.2.1 ∨
      onlineGeneratedRefreshRoundQueryFormula p.2.1 =
        (onlineGeneratedRefreshRoundRestSecondCoarse p.2.2).val}
  letI : IsProbabilityMeasure roundLaw := by
    letI (w : Worker onlineCoarseCounterexampleWorkers) :
        IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedRefreshBatch) := by
      unfold onlineBatchLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedDifferenceBatch) := by
      unfold onlineBatchLaw
      infer_instance
    letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
      onlineGeneratedRefreshData.quantizer.law_isProbability
    haveI : IsProbabilityMeasure
        (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
          onlineGeneratedRefreshData.quantizer) := by
      unfold workerCompressionLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible) := by
      unfold refreshLaw
      infer_instance
    unfold roundLaw onlineRoundLaw
    change IsProbabilityMeasure
      ((refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible).prod
        (((onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedRefreshBatch).prod
            (onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedDifferenceBatch)).prod
          (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
            onlineGeneratedRefreshData.quantizer)))
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    letI (w : Worker onlineCoarseCounterexampleWorkers) :
        IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedDifferenceBatch) := by
      unfold onlineBatchLaw
      infer_instance
    letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
      onlineGeneratedRefreshData.quantizer.law_isProbability
    haveI : IsProbabilityMeasure
        (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
          onlineGeneratedRefreshData.quantizer) := by
      unfold workerCompressionLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible) := by
      unfold refreshLaw
      infer_instance
    unfold restLaw onlineGeneratedRefreshRoundRestLaw
    infer_instance
  letI : NoAtoms (Measure.map onlineGeneratedRefreshRoundQueryFormula roundLaw) := by
    dsimp [roundLaw]
    exact onlineGeneratedRefreshRoundQueryFormula_noAtoms
  have hD : ¬ NullMeasurableSet D
      (onlineCoarseLaw.prod (roundLaw.prod restLaw)) := by
    exact onlineCoarseUnionDiagonals_of_maps_not_nullMeasurable
      roundLaw restLaw onlineGeneratedRefreshRoundQueryFormula
      onlineGeneratedRefreshRoundRestSecondCoarse
      onlineGeneratedRefreshRoundQueryFormula_measurable (by
        unfold onlineGeneratedRefreshRoundRestSecondCoarse
        fun_prop)
      (by simpa [restLaw] using
        onlineGeneratedRefreshRoundRestSecondCoarse_map)
  intro hpref
  have hpull : NullMeasurableSet
      (onlineGeneratedRefreshTwoRoundFirstCoarseEquiv.symm ⁻¹'
        {pref : Fin 2 → OnlineGeneratedRefreshRound |
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
              ((pref 1).2.1.1 0 0).1.val ∨
            onlineGeneratedRefreshRoundQueryFormula (pref 0) =
              ((pref 1).2.1.1 0 1).1.val})
      (onlineCoarseLaw.prod (roundLaw.prod restLaw)) :=
    hpref.preimage
      onlineGeneratedRefreshTwoRoundFirstCoarseEquiv_measurePreserving.symm.quasiMeasurePreserving
  have hset :
      onlineGeneratedRefreshTwoRoundFirstCoarseEquiv.symm ⁻¹'
        {pref : Fin 2 → OnlineGeneratedRefreshRound |
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
              ((pref 1).2.1.1 0 0).1.val ∨
            onlineGeneratedRefreshRoundQueryFormula (pref 0) =
              ((pref 1).2.1.1 0 1).1.val} = D := by
    ext p
    change
      (onlineGeneratedRefreshRoundQueryFormula p.2.1 = p.1.val ∨
        onlineGeneratedRefreshRoundQueryFormula p.2.1 =
          (onlineGeneratedRefreshRoundRestSecondCoarse p.2.2).val) ↔
      (p.1.val = onlineGeneratedRefreshRoundQueryFormula p.2.1 ∨
        onlineGeneratedRefreshRoundQueryFormula p.2.1 =
          (onlineGeneratedRefreshRoundRestSecondCoarse p.2.2).val)
    rw [eq_comm]
  rw [hset] at hpull
  exact hD hpull

noncomputable def onlineGeneratedRefreshTwoRoundState
    (pref : Fin 2 → OnlineGeneratedRefreshRound) :
    State oldInitialBoundCounterexampleDimension :=
  onlineStep onlineGeneratedRefreshData
    (onlineDriverOfRoundNoise (pref 1))
    (onlineStep onlineGeneratedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedRefreshData
        onlineGeneratedRefreshInitialPoint))

noncomputable def onlineGeneratedRefreshTimeTwoQuery
    (pref : Fin 2 → OnlineGeneratedRefreshRound) : ℝ :=
  (onlineGeneratedRefreshTwoRoundState pref).x 0

theorem onlineGeneratedRefresh_timeTwo_query_formula
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh : (pref 0).1 = true)
    (hcoarse0 : ((pref 0).2.1.1 0 0).1.val ≠ 0)
    (hcoarse1 : ((pref 0).2.1.1 0 1).1.val ≠ 0) :
    onlineGeneratedRefreshTimeTwoQuery pref =
      -(10 + (onlineGeneratedRefreshCenteredCoordinate
          ((pref 0).2.1.1 0 0).2 +
        onlineGeneratedRefreshCenteredCoordinate
          ((pref 0).2.1.1 0 1).2) / 2) := by
  have hzero0 : (0 : ℝ) ≠ ((pref 0).2.1.1 0 0).1.val := hcoarse0.symm
  have hzero1 : (0 : ℝ) ≠ ((pref 0).2.1.1 0 1).1.val := hcoarse1.symm
  unfold onlineGeneratedRefreshTimeTwoQuery onlineGeneratedRefreshTwoRoundState
  simp only [onlineStep]
  change (primalStep onlineGeneratedRefreshData.stepSize
    (onlineStep onlineGeneratedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedRefreshData
        onlineGeneratedRefreshInitialPoint))).1 0 = _
  rw [primalStep_eq]
  have hx1 : (onlineStep onlineGeneratedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedRefreshData
        onlineGeneratedRefreshInitialPoint)).x = 0 := by
    exact onlineGeneratedRefresh_proofExact_x_one
      (fun k => if k = 0 then pref 0 else pref 1)
  rw [hx1]
  simp only [Pi.zero_apply, zero_sub]
  have hxnext0 : primalStep onlineGeneratedRefreshData.stepSize
      (onlineProofExactInitialState onlineGeneratedRefreshData
        onlineGeneratedRefreshInitialPoint) = 0 := by
    change (onlineStep onlineGeneratedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedRefreshData
        onlineGeneratedRefreshInitialPoint)).x = 0
    exact hx1
  simp only [onlineStep]
  unfold onlineWorkerEstimator
  rw [hxnext0]
  simp only [onlineDriverOfRoundNoise, onlineGeneratedRefreshData, hrefresh, if_true]
  unfold average SOptLib.finiteUniformAverage
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num [onlineCoarseCounterexampleWorkers, onlineGeneratedRefreshBatch]
  rw [show stochasticGradient onlineGeneratedRefreshProblem 0
        ((pref 0).2.1.1 0 0) 0 =
        onlineGeneratedRefreshSlope ((pref 0).2.1.1 0 0) •
          oldInitialBoundCounterexampleDirection by
      simpa [stochasticGradient, onlineGeneratedRefreshProblem,
        onlineCoarseCounterexamplePoint, hzero0] using
        (onlineGeneratedRefreshLoss_gradient_at_query
          ((pref 0).2.1.1 0 0) 0),
    show stochasticGradient onlineGeneratedRefreshProblem 0
        ((pref 0).2.1.1 0 1) 0 =
        onlineGeneratedRefreshSlope ((pref 0).2.1.1 0 1) •
          oldInitialBoundCounterexampleDirection by
      simpa [stochasticGradient, onlineGeneratedRefreshProblem,
        onlineCoarseCounterexamplePoint, hzero1] using
        (onlineGeneratedRefreshLoss_gradient_at_query
          ((pref 0).2.1.1 0 1) 0)]
  simp [onlineGeneratedRefreshSlope, oldInitialBoundCounterexampleDirection]
  ring

def onlineGeneratedRefreshTimeZeroGaussianPair
    (pref : Fin 2 → OnlineGeneratedRefreshRound) : ℝ × ℝ :=
  (((pref 0).2.1.1 0 0).2, ((pref 0).2.1.1 0 1).2)

theorem onlineGeneratedRefreshTimeZeroGaussianPair_map :
    Measure.map onlineGeneratedRefreshTimeZeroGaussianPair
        (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw onlineGeneratedRefreshData)) =
      (ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1) := by
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
    onlineGeneratedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedRefreshData.refreshProbability
        onlineGeneratedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData) := by
    unfold onlineRoundLaw
    change IsProbabilityMeasure
      ((refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible).prod
        (((onlineBatchLaw onlineGeneratedRefreshProblem
            onlineGeneratedRefreshBatch).prod
          (onlineBatchLaw onlineGeneratedRefreshProblem
            onlineGeneratedDifferenceBatch)).prod
          (workerCompressionLaw onlineGeneratedRefreshData.quantizer)))
    infer_instance
  let round0 : (Fin 2 → OnlineGeneratedRefreshRound) →
      OnlineGeneratedRefreshRound := fun pref => pref 0
  let refreshBatch : OnlineGeneratedRefreshRound →
      ((w : Worker onlineCoarseCounterexampleWorkers) →
        Fin onlineGeneratedRefreshBatch.1 → OnlineGeneratedRefreshSample w) :=
    fun z => z.2.1.1
  let row : ((w : Worker onlineCoarseCounterexampleWorkers) →
      Fin onlineGeneratedRefreshBatch.1 → OnlineGeneratedRefreshSample w) →
      (Fin 2 → OnlineGeneratedRefreshSample 0) := fun batch => batch 0
  let pair : (Fin 2 → OnlineGeneratedRefreshSample 0) →
      OnlineGeneratedRefreshSample 0 × OnlineGeneratedRefreshSample 0 :=
    fun samples => (samples 0, samples 1)
  let gaussianPair :
      (OnlineGeneratedRefreshSample 0 × OnlineGeneratedRefreshSample 0) → ℝ × ℝ :=
    fun samples => (samples.1.2, samples.2.2)
  have hround : Measure.map round0
      (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData)) =
      onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData := by
    simpa [round0] using
      (Measure.infinitePi_map_eval
        (fun _ : Fin 2 => onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData) (0 : Fin 2))
  have hbatch : Measure.map refreshBatch
      (onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData) =
      onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedRefreshBatch := by
    simpa [refreshBatch] using
      (onlineRoundLaw_refreshBatch_marginal onlineGeneratedRefreshData)
  have hrow : Measure.map row
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedRefreshBatch) =
      Measure.infinitePi (fun _ : Fin 2 =>
        onlineGeneratedRefreshProblem.sampleLaw 0) := by
    simpa [row, onlineGeneratedRefreshBatch] using
      (onlineBatchLaw_worker_marginal onlineGeneratedRefreshProblem
        (b := onlineGeneratedRefreshBatch)
        (0 : Worker onlineCoarseCounterexampleWorkers))
  have hpair : Measure.map pair
      (Measure.infinitePi (fun _ : Fin 2 =>
        onlineGeneratedRefreshProblem.sampleLaw 0)) =
      (onlineGeneratedRefreshProblem.sampleLaw 0).prod
        (onlineGeneratedRefreshProblem.sampleLaw 0) := by
    rw [Measure.infinitePi_eq_pi]
    simpa [pair] using
      (MeasureTheory.measurePreserving_piFinTwo
        (fun _ : Fin 2 => onlineGeneratedRefreshProblem.sampleLaw 0)).map_eq
  have hsnd : Measure.map Prod.snd
      (onlineGeneratedRefreshProblem.sampleLaw 0) =
      ProbabilityTheory.gaussianReal 0 1 := by
    change Measure.map Prod.snd
      (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hgaussian : Measure.map gaussianPair
      ((onlineGeneratedRefreshProblem.sampleLaw 0).prod
        (onlineGeneratedRefreshProblem.sampleLaw 0)) =
      (ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1) := by
    simpa [gaussianPair, hsnd] using
      (Measure.map_prod_map
        (onlineGeneratedRefreshProblem.sampleLaw 0)
        (onlineGeneratedRefreshProblem.sampleLaw 0)
        measurable_snd measurable_snd).symm
  calc
    Measure.map onlineGeneratedRefreshTimeZeroGaussianPair
        (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData)) =
        Measure.map gaussianPair
          (Measure.map pair
            (Measure.map row
              (Measure.map refreshBatch
                (Measure.map round0
                  (Measure.infinitePi (fun _ : Fin 2 =>
                    onlineRoundLaw (b := onlineGeneratedRefreshBatch)
                      (b0 := onlineGeneratedDifferenceBatch)
                      onlineGeneratedRefreshData)))))) := by
          repeat' rw [Measure.map_map]
          · rfl
          all_goals fun_prop
    _ = _ := by rw [hround, hbatch, hrow, hpair, hgaussian]

theorem onlineGeneratedRefreshTimeZeroSample_marginal (j : Fin 2) :
    Measure.map
        (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
          (pref 0).2.1.1 0 j)
        (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData)) =
      onlineGeneratedRefreshProblem.sampleLaw 0 := by
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
    onlineGeneratedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedRefreshData.refreshProbability
        onlineGeneratedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData) := by
    unfold onlineRoundLaw
    change IsProbabilityMeasure
      ((refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible).prod
        (((onlineBatchLaw onlineGeneratedRefreshProblem
            onlineGeneratedRefreshBatch).prod
          (onlineBatchLaw onlineGeneratedRefreshProblem
            onlineGeneratedDifferenceBatch)).prod
          (workerCompressionLaw onlineGeneratedRefreshData.quantizer)))
    infer_instance
  calc
    Measure.map
        (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
          (pref 0).2.1.1 0 j)
        (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData)) =
      Measure.map
        (fun batch : (w : Worker onlineCoarseCounterexampleWorkers) →
          Fin onlineGeneratedRefreshBatch.1 → OnlineGeneratedRefreshSample w =>
          batch 0 j)
        (Measure.map
          (fun z : OnlineGeneratedRefreshRound => z.2.1.1)
        (Measure.map
            (fun pref : Fin 2 → OnlineGeneratedRefreshRound => pref 0)
            (Measure.infinitePi (fun _ : Fin 2 =>
              onlineRoundLaw (b := onlineGeneratedRefreshBatch)
                (b0 := onlineGeneratedDifferenceBatch)
                onlineGeneratedRefreshData)))) := by
        repeat' rw [Measure.map_map]
        · rfl
        all_goals fun_prop
    _ = _ := by
      rw [Measure.infinitePi_map_eval,
        onlineRoundLaw_refreshBatch_marginal onlineGeneratedRefreshData]
      change Measure.map
        (fun batch : (w : Worker onlineCoarseCounterexampleWorkers) →
          Fin onlineGeneratedRefreshBatch.1 → OnlineGeneratedRefreshSample w =>
          batch 0 j)
        (onlineBatchLaw onlineGeneratedRefreshProblem
          onlineGeneratedRefreshBatch) =
        onlineGeneratedRefreshProblem.sampleLaw 0
      exact onlineBatchLaw_coordinate_marginal
        (b := onlineGeneratedRefreshBatch)
        onlineGeneratedRefreshProblem 0 j

theorem onlineGeneratedRefreshCoin_ae_true (t : Fin 2) :
    ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData),
      (pref t).1 = true := by
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
    onlineGeneratedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedRefreshData.refreshProbability
        onlineGeneratedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData) := by
    unfold onlineRoundLaw
    change IsProbabilityMeasure
      ((refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible).prod
        (((onlineBatchLaw onlineGeneratedRefreshProblem
            onlineGeneratedRefreshBatch).prod
          (onlineBatchLaw onlineGeneratedRefreshProblem
            onlineGeneratedDifferenceBatch)).prod
          (workerCompressionLaw onlineGeneratedRefreshData.quantizer)))
    infer_instance
  have hmap : Measure.map
      (fun pref : Fin 2 → OnlineGeneratedRefreshRound => (pref t).1)
      (Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData)) = Measure.dirac true := by
    calc
      Measure.map
          (fun pref : Fin 2 → OnlineGeneratedRefreshRound => (pref t).1)
          (Measure.infinitePi (fun _ : Fin 2 =>
            onlineRoundLaw (b := onlineGeneratedRefreshBatch)
              (b0 := onlineGeneratedDifferenceBatch)
              onlineGeneratedRefreshData)) =
        Measure.map Prod.fst
          (Measure.map
            (fun pref : Fin 2 → OnlineGeneratedRefreshRound => pref t)
            (Measure.infinitePi (fun _ : Fin 2 =>
              onlineRoundLaw (b := onlineGeneratedRefreshBatch)
                (b0 := onlineGeneratedDifferenceBatch)
                onlineGeneratedRefreshData))) := by
          rw [Measure.map_map]
          · rfl
          all_goals fun_prop
      _ = Measure.map Prod.fst
          (onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData) := by
        rw [Measure.infinitePi_map_eval]
      _ = refreshLaw 1 onlineGeneratedRefreshData.refresh_admissible := by
        unfold onlineRoundLaw
        change Measure.map Prod.fst
          ((refreshLaw onlineGeneratedRefreshData.refreshProbability
              onlineGeneratedRefreshData.refresh_admissible).prod
            (((onlineBatchLaw onlineGeneratedRefreshProblem
                onlineGeneratedRefreshBatch).prod
              (onlineBatchLaw onlineGeneratedRefreshProblem
                onlineGeneratedDifferenceBatch)).prod
              (workerCompressionLaw onlineGeneratedRefreshData.quantizer))) = _
        rw [Measure.map_fst_prod, measure_univ, one_smul]
        rfl
      _ = Measure.dirac true := by
        unfold refreshLaw
        rw [← PMF.toMeasure_pure]
        apply congrArg PMF.toMeasure
        ext b
        cases b
        · simp only [PMF.bernoulli_apply, Bool.cond_false,
            PMF.pure_apply, Bool.false_eq_true, if_false]
          change (1 : ENNReal) - 1 = 0
          simp
        · simp only [PMF.bernoulli_apply, Bool.cond_true,
            PMF.pure_apply, if_pos rfl]
          rfl
  have hqmp : Measure.QuasiMeasurePreserving
      (fun pref : Fin 2 → OnlineGeneratedRefreshRound => (pref t).1)
      (Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData)) (Measure.dirac true) :=
    ⟨by fun_prop, by rw [hmap]⟩
  exact hqmp.tendsto_ae
    ((MeasureTheory.ae_dirac_iff (measurableSet_singleton true)).2 rfl)

theorem onlineGeneratedRefreshTimeZeroCoin_ae_true :
    ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData),
      (pref 0).1 = true :=
  onlineGeneratedRefreshCoin_ae_true 0

theorem onlineGeneratedRefreshTimeOneCoin_ae_true :
    ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData),
      (pref 1).1 = true :=
  onlineGeneratedRefreshCoin_ae_true 1

theorem onlineGeneratedRefreshSample_coarse_ne_zero_ae :
    ∀ᵐ s ∂onlineGeneratedRefreshProblem.sampleLaw 0, s.1.val ≠ 0 := by
  letI : NoAtoms (ProbabilityTheory.cauchyMeasure 0 1) :=
    onlineCauchy_one_noAtoms
  have hcoarse : ∀ᵐ c ∂onlineCoarseLaw, c.val ≠ 0 := by
    rw [ae_iff]
    have hset : {c : OnlineCoarseReal | ¬c.val ≠ 0} =
        {onlineCoarseWrap 0} := by
      ext c
      cases c
      simp [onlineCoarseWrap]
    rw [hset]
    exact onlineCoarseLaw_apply_countable _ (Set.countable_singleton _)
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : OnlineGeneratedRefreshSample 0 → OnlineCoarseReal)
      (onlineGeneratedRefreshProblem.sampleLaw 0) onlineCoarseLaw := by
    refine ⟨measurable_fst, ?_⟩
    have hmap : Measure.map Prod.fst
        (onlineGeneratedRefreshProblem.sampleLaw 0) = onlineCoarseLaw := by
      change Measure.map Prod.fst
        (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) = _
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [hmap]
  exact hqmp.tendsto_ae hcoarse

theorem onlineGeneratedRefresh_timeTwo_query_formula_ae :
    onlineGeneratedRefreshTimeTwoQuery =ᵐ[
      Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData)]
      (fun pref => -(10 +
        (onlineGeneratedRefreshCenteredCoordinate ((pref 0).2.1.1 0 0).2 +
          onlineGeneratedRefreshCenteredCoordinate ((pref 0).2.1.1 0 1).2) / 2)) := by
  have hsample (j : Fin 2) :
      ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData),
        ((pref 0).2.1.1 0 j).1.val ≠ 0 := by
    have hqmp : Measure.QuasiMeasurePreserving
        (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
          (pref 0).2.1.1 0 j)
        (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData))
        (onlineGeneratedRefreshProblem.sampleLaw 0) :=
      ⟨by fun_prop, by rw [onlineGeneratedRefreshTimeZeroSample_marginal j]⟩
    exact hqmp.tendsto_ae onlineGeneratedRefreshSample_coarse_ne_zero_ae
  filter_upwards [onlineGeneratedRefreshTimeZeroCoin_ae_true,
    hsample 0, hsample 1] with pref hcoin hzero hzero' using
    onlineGeneratedRefresh_timeTwo_query_formula pref hcoin hzero hzero'

theorem onlineGeneratedRefresh_timeTwo_query_map :
    Measure.map onlineGeneratedRefreshTimeTwoQuery
        (Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData)) =
      Measure.map onlineGeneratedRefreshQueryFormula
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)) := by
  let μ := Measure.infinitePi (fun _ : Fin 2 =>
    onlineRoundLaw (b := onlineGeneratedRefreshBatch)
      (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedRefreshData)
  have hae : onlineGeneratedRefreshTimeTwoQuery =ᵐ[μ]
      onlineGeneratedRefreshQueryFormula ∘
        onlineGeneratedRefreshTimeZeroGaussianPair := by
    simpa [μ, onlineGeneratedRefreshQueryFormula,
      onlineGeneratedRefreshTimeZeroGaussianPair, Function.comp_def] using
      onlineGeneratedRefresh_timeTwo_query_formula_ae
  calc
    Measure.map onlineGeneratedRefreshTimeTwoQuery μ =
        Measure.map (onlineGeneratedRefreshQueryFormula ∘
          onlineGeneratedRefreshTimeZeroGaussianPair) μ :=
      Measure.map_congr hae
    _ = Measure.map onlineGeneratedRefreshQueryFormula
        (Measure.map onlineGeneratedRefreshTimeZeroGaussianPair μ) := by
      rw [Measure.map_map onlineGeneratedRefreshQueryFormula_measurable (by fun_prop)]
    _ = _ := by rw [onlineGeneratedRefreshTimeZeroGaussianPair_map]

theorem onlineGeneratedRefresh_timeTwo_query_noAtoms :
    NoAtoms (Measure.map onlineGeneratedRefreshTimeTwoQuery
      (Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData))) := by
  rw [onlineGeneratedRefresh_timeTwo_query_map]
  exact onlineGeneratedRefreshQueryFormula_noAtoms

noncomputable def onlineGeneratedRefreshTimeTwoResidualSq
    (pref : Fin 2 → OnlineGeneratedRefreshRound) : ℝ :=
  ‖(onlineGeneratedRefreshTwoRoundState pref).g -
      globalGradient (onlineLocalProblem onlineGeneratedRefreshData.problem)
        (onlineGeneratedRefreshTwoRoundState pref).x‖ ^ 2

theorem onlineGeneratedRefresh_average_worker
    (f : Worker onlineCoarseCounterexampleWorkers →
      Point oldInitialBoundCounterexampleDimension) :
    average f = f 0 := by
  unfold average SOptLib.finiteUniformAverage
  rw [Finset.sum_eq_single (0 : Worker onlineCoarseCounterexampleWorkers)]
  · norm_num [onlineCoarseCounterexampleWorkers]
  · intro b _ hne
    exact False.elim (hne (Subsingleton.elim _ _))
  · simp

theorem onlineGeneratedRefresh_timeTwo_refreshResidual_formula
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh : (pref 1).1 = true) :
    onlineGeneratedRefreshTimeTwoResidualSq pref =
      (((if onlineGeneratedRefreshTimeTwoQuery pref =
            ((pref 1).2.1.1 0 0).1.val then 0
          else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 0)) +
        (if onlineGeneratedRefreshTimeTwoQuery pref =
            ((pref 1).2.1.1 0 1).1.val then 0
          else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 1))) / 2 - 10) ^ 2 := by
  let state := onlineGeneratedRefreshTwoRoundState pref
  let q := onlineGeneratedRefreshTimeTwoQuery pref
  have hx : state.x = onlineCoarseCounterexamplePoint q := by
    ext i
    fin_cases i
    simpa [state, q, onlineGeneratedRefreshTimeTwoQuery,
      onlineCoarseCounterexamplePoint,
      oldInitialBoundCounterexampleDirection]
  have hgrad (j : Fin 2) :
      stochasticGradient onlineGeneratedRefreshProblem 0
          ((pref 1).2.1.1 0 j) state.x =
        (if q = ((pref 1).2.1.1 0 j).1.val then 0
          else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 j) •
            oldInitialBoundCounterexampleDirection) := by
    rw [hx]
    exact onlineGeneratedRefreshLoss_gradient_at_query _ q
  have hg : state.g = average (fun _ : Worker onlineCoarseCounterexampleWorkers =>
      average (fun j : Fin onlineGeneratedRefreshBatch.1 =>
        stochasticGradient onlineGeneratedRefreshProblem 0
          ((pref 1).2.1.1 0 j) state.x)) := by
    dsimp [state, onlineGeneratedRefreshTwoRoundState]
    simp only [onlineStep, onlineWorkerEstimator, onlineDriverOfRoundNoise,
      hrefresh, if_true]
    rfl
  unfold onlineGeneratedRefreshTimeTwoResidualSq
  change ‖state.g -
      globalGradient (onlineLocalProblem onlineGeneratedRefreshProblem) state.x‖ ^ 2 = _
  rw [onlineGeneratedRefresh_globalGradient state.x, hg]
  rw [onlineGeneratedRefresh_average_worker]
  unfold average SOptLib.finiteUniformAverage
  rw [Fin.sum_univ_two, hgrad 0, hgrad 1]
  norm_num [onlineCoarseCounterexampleWorkers, onlineGeneratedRefreshBatch,
    oldInitialBoundCounterexampleDirection]
  have hdirnorm : ‖oldInitialBoundCounterexampleDirection‖ = 1 := by
    rw [oldInitialBoundCounterexampleDirection, EuclideanSpace.norm_single]
    norm_num
  have hten : ‖(10 : ℝ) • oldInitialBoundCounterexampleDirection‖ = 10 := by
    rw [norm_smul, hdirnorm]
    norm_num
  have hten' : ‖(10 : ℝ) •
      (EuclideanSpace.single 0 1 :
        Point oldInitialBoundCounterexampleDimension)‖ = 10 := by
    exact hten
  split_ifs <;> simp_all
  · rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
      EuclideanSpace.norm_single]
    norm_num
  · rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp only [smul_smul, ← sub_smul, norm_smul, hdirnorm, mul_one]
    simp only [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one]
    rw [sq_abs]
    ring
  · rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp only [smul_smul, ← sub_smul, norm_smul, hdirnorm, mul_one]
    simp only [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one]
    rw [sq_abs]
    ring
  · rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp only [smul_smul, ← add_smul, ← sub_smul, norm_smul, hdirnorm,
      mul_one]
    simp only [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one]
    rw [sq_abs]
    ring

theorem onlineGeneratedRefreshCenteredCoordinate_abs_lt_one (u : ℝ) :
    |onlineGeneratedRefreshCenteredCoordinate u| < 1 := by
  have hden : 0 < 1 + |u| := by positivity
  rw [onlineGeneratedRefreshCenteredCoordinate, abs_div, abs_of_pos hden]
  exact (div_lt_one hden).2 (by linarith [abs_nonneg u])

theorem onlineGeneratedRefresh_timeTwo_refreshResidual_threshold_preimage
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh : (pref 1).1 = true) :
    4 < onlineGeneratedRefreshTimeTwoResidualSq pref ↔
      onlineGeneratedRefreshTimeTwoQuery pref =
          ((pref 1).2.1.1 0 0).1.val ∨
        onlineGeneratedRefreshTimeTwoQuery pref =
          ((pref 1).2.1.1 0 1).1.val := by
  rw [onlineGeneratedRefresh_timeTwo_refreshResidual_formula pref hrefresh]
  let c0 := onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 0).2
  let c1 := onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 1).2
  have hc0 := (abs_lt.mp
    (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
      ((pref 1).2.1.1 0 0).2))
  have hc1 := (abs_lt.mp
    (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
      ((pref 1).2.1.1 0 1).2))
  change 4 <
      (((if onlineGeneratedRefreshTimeTwoQuery pref =
            ((pref 1).2.1.1 0 0).1.val then 0 else 10 + c0) +
        (if onlineGeneratedRefreshTimeTwoQuery pref =
            ((pref 1).2.1.1 0 1).1.val then 0 else 10 + c1)) / 2 - 10) ^ 2 ↔ _
  by_cases h0 : onlineGeneratedRefreshTimeTwoQuery pref =
      ((pref 1).2.1.1 0 0).1.val
  all_goals by_cases h1 : onlineGeneratedRefreshTimeTwoQuery pref =
      ((pref 1).2.1.1 0 1).1.val
  · have h01 : ((pref 1).2.1.1 0 0).1.val =
        ((pref 1).2.1.1 0 1).1.val := h0.symm.trans h1
    simp [h0, h1, h01]
    norm_num
  · have h01 : ((pref 1).2.1.1 0 0).1.val ≠
        ((pref 1).2.1.1 0 1).1.val := fun h => h1 (h0.trans h)
    simp only [h0, if_true, true_or, h01, if_false, iff_true]
    dsimp [c1] at hc1 ⊢
    let z := (onlineGeneratedRefreshCenteredCoordinate
      ((pref 1).2.1.1 0 1).2 - 10) / 2
    have hz : 0 < (z + 2) * (z - 2) := by
      apply mul_pos_of_neg_of_neg <;> dsimp [z] <;> linarith
    have hzsq : 4 < z ^ 2 := by nlinarith [hz]
    convert hzsq using 1 <;> dsimp [z] <;> ring
  · have h10 : ((pref 1).2.1.1 0 1).1.val ≠
        ((pref 1).2.1.1 0 0).1.val := fun h => h0 (h1.trans h)
    simp only [h0, if_false, false_or, h1, if_true, h10, iff_true]
    dsimp [c0] at hc0 ⊢
    let z := (onlineGeneratedRefreshCenteredCoordinate
      ((pref 1).2.1.1 0 0).2 - 10) / 2
    have hz : 0 < (z + 2) * (z - 2) := by
      apply mul_pos_of_neg_of_neg <;> dsimp [z] <;> linarith
    have hzsq : 4 < z ^ 2 := by nlinarith [hz]
    convert hzsq using 1 <;> dsimp [z] <;> ring
  · simp only [h0, if_false, false_or, h1, iff_false]
    dsimp [c0, c1] at hc0 hc1 ⊢
    let z := (onlineGeneratedRefreshCenteredCoordinate
      ((pref 1).2.1.1 0 0).2 +
        onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 1).2) / 2
    have hz : 0 < (1 - z) * (1 + z) := by
      apply mul_pos <;> dsimp [z] <;> linarith
    intro hbad
    dsimp [z] at hz
    nlinarith [hz]
/-! ## Partial-participation MARINA (Algorithm 4) -/

/-- Internal recursion carrier for the refresh coin and the latent samples used
by a non-refresh Algorithm 4 round.  The `r` sampled clients remain latent on a
refresh round; `ppActiveClients` below computes the paper's branch-dependent
set `I⁰_k` and exposes all workers in that branch. -/
structure PPDriver (n r : Count) (Ξ : Type*) where
  refresh : Bool
  sampledClient : Fin r.1 → Worker n
  compressionSample : Fin r.1 → Ξ

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/6`: the two possible
shapes of Algorithm 4's active-client family `I⁰_k`.  The non-refresh branch
is an indexed family, rather than a `Finset`, because the source samples `r`
clients independently and therefore permits repeated clients. -/
inductive PPActiveClients (n r : Count) where
  | allWorkers
  | sampled (client : Fin r.1 → Worker n)

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/6`:
`I⁰_k={1,…,n}` on refresh, and the `r` iid uniform client draws otherwise. -/
def ppActiveClients {n r : Count} {Ξ : Type*}
    (z : PPDriver n r Ξ) : PPActiveClients n r :=
  if z.refresh then .allWorkers else .sampled z.sampledClient

/-- Internal typed input for one of Algorithm 4's worker messages.  A refresh
message needs only a worker, whereas a difference message additionally needs
the compressor sample paired with the sampled client occurrence. -/
inductive PPWorkerRequest (n : Count) (Ξ : Type*) where
  | refresh (worker : Worker n)
  | difference (worker : Worker n) (compressionSample : Ξ)

/-- Uniform client law in Algorithm 4. -/
noncomputable def workerLaw (n : Count) : Measure (Worker n) :=
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  (PMF.uniformOfFintype (Worker n)).toMeasure

/-- Law of `r` independent uniform client draws. -/
noncomputable def ppClientLaw (n r : Count) : Measure (Fin r.1 → Worker n) :=
  Measure.infinitePi (fun _ : Fin r.1 => workerLaw n)

/-- Law of `r` independent compression samples. -/
noncomputable def ppCompressionLaw {d r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ) : Measure (Fin r.1 → Ξ) :=
  Measure.infinitePi (fun _ : Fin r.1 => Q.law)

/-- Internal product noise for one Algorithm 4 round.  The client and
compressor coordinates are latent on refresh rounds; the source-facing active
family is the computed object `ppActiveClients`. -/
abbrev PPRoundNoise (n r : Count) (Ξ : Type*) :=
  Bool × ((Fin r.1 → Worker n) × (Fin r.1 → Ξ))

/-- Canonical probability realization of the refresh coin and the iid uniform
client/compressor coordinates used on Algorithm 4's non-refresh branch.  The
unused pre-sampled coordinates stay internal on refresh; `ppActiveClients`
computes the all-worker family quoted at
`book/MARINA/MARINA.json#/algorithm_spec/steps/6`. -/
noncomputable def ppRoundLaw {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) : Measure (PPRoundNoise n r Ξ) :=
  (refreshLaw A.refreshProbability A.refresh_admissible).prod
    ((ppClientLaw n r).prod (ppCompressionLaw A.quantizer))

/-- Path-law realization of `book/MARINA/MARINA.json#/algorithm_spec/variants/3`
and the repeated transition at `#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/6`, `#/algorithm_spec/steps/7`, and
`#/algorithm_spec/steps/8`. -/
noncomputable def ppPathLaw {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) : Measure (ℕ → PPRoundNoise n r Ξ) :=
  SOptLib.iidStreamLaw (ppRoundLaw A)

def ppDriverOfNoise {n r : Count} {Ξ : Type*}
    (z : PPRoundNoise n r Ξ) : PPDriver n r Ξ :=
  { refresh := z.1, sampledClient := z.2.1, compressionSample := z.2.2 }

/-- Every latent non-refresh PP-MARINA client coordinate is uniform over workers. -/
theorem ppPathLaw_client_marginal {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ)
    (k : ℕ) (j : Fin r.1) :
    Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => (path k).2.1 j)
      (ppPathLaw A) = workerLaw n := by
  haveI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  have hclient :
      Measure.map (fun clients : Fin r.1 → Worker n => clients j)
          (ppClientLaw n r) = workerLaw n := by
    unfold ppClientLaw
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin r.1 => workerLaw n) j)
  have hround :
      Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => path k)
          (ppPathLaw A) = ppRoundLaw A := by
    unfold ppPathLaw
    exact SOptLib.iidStreamLaw_map_eval (ppRoundLaw A) k
  have hroundClients :
      Measure.map (fun z : PPRoundNoise n r Ξ => z.2.1) (ppRoundLaw A) =
        ppClientLaw n r := by
    calc
      Measure.map (fun z : PPRoundNoise n r Ξ => z.2.1) (ppRoundLaw A) =
          Measure.map Prod.fst (Measure.map Prod.snd (ppRoundLaw A)) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.map_map measurable_fst measurable_snd
            (μ := ppRoundLaw A)).symm
      _ = Measure.map Prod.fst
          ((ppClientLaw n r).prod (ppCompressionLaw A.quantizer)) := by
        unfold ppRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = ppClientLaw n r := by
        rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  calc
    Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => (path k).2.1 j)
        (ppPathLaw A) =
        Measure.map (fun z : PPRoundNoise n r Ξ => z.2.1 j)
          (Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => path k)
            (ppPathLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
          (measurable_pi_apply k) (μ := ppPathLaw A)).symm
    _ = Measure.map (fun z : PPRoundNoise n r Ξ => z.2.1 j)
        (ppRoundLaw A) := by
      rw [hround]
    _ = Measure.map (fun clients : Fin r.1 → Worker n => clients j)
        (Measure.map (fun z : PPRoundNoise n r Ξ => z.2.1) (ppRoundLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map (measurable_pi_apply j)
          (measurable_fst.comp measurable_snd) (μ := ppRoundLaw A)).symm
    _ = Measure.map (fun clients : Fin r.1 → Worker n => clients j)
        (ppClientLaw n r) := by
      rw [hroundClients]
    _ = workerLaw n := hclient

/-- PP client draws and their compressor samples are independent consequences
of the Algorithm 4 product law. -/
theorem ppRoundLaw_clients_compression_independent {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) :
    ProbabilityTheory.IndepFun
      (fun z : PPRoundNoise n r Ξ => z.2.1)
      (fun z : PPRoundNoise n r Ξ => z.2.2)
      (ppRoundLaw A) := by
  haveI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hPairLaw :
      Measure.map (fun z : PPRoundNoise n r Ξ => z.2) (ppRoundLaw A) =
        (ppClientLaw n r).prod (ppCompressionLaw A.quantizer) := by
    unfold ppRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  exact indepFun_of_map_prod_eq_prod_laws measurable_snd.aemeasurable hPairLaw

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/7`, Algorithm 4 line 9:
the message `g_i^{k+1}` produced by a refresh worker or by one sampled
non-refresh client occurrence. -/
noncomputable def ppWorkerEstimator {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (s : State d) (request : PPWorkerRequest n Ξ) : Point d :=
  let xNext := primalStep A.stepSize s
  match request with
  | .refresh i => localGradient A.problem i xNext
  | .difference i ξ =>
      s.g + A.quantizer.apply
        (localGradientDifference A.problem i xNext s.x) ξ

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/8`, Algorithm 4 line 11:
aggregate every worker message on refresh and the `r` sampled-client messages
otherwise. -/
noncomputable def ppAggregation {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (z : PPDriver n r Ξ) (s : State d)
    (active : PPActiveClients n r) : Point d :=
  match active with
  | .allWorkers =>
      average (fun i : Worker n =>
        ppWorkerEstimator A s (.refresh i))
  | .sampled client =>
      average (fun j : Fin r.1 =>
        ppWorkerEstimator A s
          (.difference (client j) (z.compressionSample j)))

/-- Composition of Algorithm 4's branch-dependent client selection, worker
messages, and server aggregation. -/
noncomputable def ppEstimatorStep {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (z : PPDriver n r Ξ) (s : State d) : Point d :=
  ppAggregation A z s (ppActiveClients z)

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0` and `#/algorithm_spec/steps/6-8`:
canonical PP-MARINA state transition through active-client selection, worker
messages, and branch-specific aggregation. -/
noncomputable def ppStep {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (z : PPDriver n r Ξ) (s : State d) : State d :=
  { x := primalStep A.stepSize s
    g := ppEstimatorStep A z s }

/-- `book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/4`:
"`g^0=∇f(x^0)`". -/
noncomputable def ppInitialState {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) : State d :=
  { x := x0, g := globalGradient A.problem x0 }

/-- Generated recursion for `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/6`, `#/algorithm_spec/steps/7`, and
`#/algorithm_spec/steps/8`
from the initialization at `#/algorithm_spec/initialization/facts/4`. -/
noncomputable def ppRun {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) :
    ℕ → (ℕ → PPDriver n r Ξ) → State d :=
  SOptLib.recursiveIterateProcess (ppInitialState A x0)
    (fun k s path => ppStep A (path k) s)

/-- Random-process realization of `book/MARINA/MARINA.json#/algorithm_spec/variants/3`
and the quoted PP-MARINA transition at `#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/6`, `#/algorithm_spec/steps/7`, and
`#/algorithm_spec/steps/8`. -/
noncomputable def ppProcess {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (x0 : Point d) :
    ℕ → (ℕ → PPRoundNoise n r Ξ) → State d :=
  fun k path => ppRun A x0 k (fun t => ppDriverOfNoise (path t))

@[simp] theorem ppRun_succ {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (k : ℕ)
    (path : ℕ → PPDriver n r Ξ) :
    ppRun A x0 (k + 1) path = ppStep A (path k) (ppRun A x0 k path) := by
  rfl

/-- Algorithm 4's source-side parameter restriction `r ≤ n`. -/
def PPBatchAdmissible (n r : Count) : Prop := r.1 ≤ n.1

/-! ## Source stepsize and density schedules -/

/-- `book/MARINA/MARINA.json#/assumptions/12`, Eq. (16). -/
def MARINAStepsizeCondition (γ L p ω : ℝ) (n : Count) : Prop :=
  γ * (L * (1 + Real.sqrt ((1 - p) * ω / (p * n.1)))) ≤ 1

/-- `book/MARINA/MARINA.json#/assumptions/13`, Eq. (23). -/
def MARINAPLStepsizeCondition (γ L p ω : ℝ) (μ : PositivePLParameter)
    (n : Count) : Prop :=
  γ * (L * (1 + Real.sqrt (2 * (1 - p) * ω / (p * n.1)))) ≤ 1 ∧
    2 * γ * μ ≤ p

/-- `book/MARINA/MARINA.json#/assumptions/14`, Eq. (27). -/
def FiniteSumVRStepsizeCondition (γ L ℒ p ω : ℝ) (n b0 : Count) : Prop :=
  γ * (L + Real.sqrt (((1 - p) / (p * n.1)) *
    (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1))) ≤ 1

/-- `book/MARINA/MARINA.json#/assumptions/15`, Eq. (35). -/
def FiniteSumVRPLStepsizeCondition (γ L ℒ p ω : ℝ) (μ : PositivePLParameter)
    (n b0 : Count) : Prop :=
  γ * (L + Real.sqrt ((2 * (1 - p) / (p * n.1)) *
      (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1))) ≤ 1 ∧
    2 * γ * μ ≤ p

/-- `book/MARINA/MARINA.json#/assumptions/16`, Eq. (40). -/
def OnlineVRStepsizeCondition (γ L ℒ p ω : ℝ) (n b0 : Count) : Prop :=
  FiniteSumVRStepsizeCondition γ L ℒ p ω n b0

/-- `book/MARINA/MARINA.json#/assumptions/17`, Eq. (48). -/
def OnlineVRPLStepsizeCondition (γ L ℒ p ω : ℝ) (μ : PositivePLParameter)
    (n b0 : Count) : Prop :=
  FiniteSumVRPLStepsizeCondition γ L ℒ p ω μ n b0

/-- `book/MARINA/MARINA.json#/assumptions/18`, Eq. (54). -/
def PPStepsizeCondition (γ L p ω : ℝ) (r : Count) : Prop :=
  γ * (L * (1 + Real.sqrt ((1 - p) * (1 + ω) / (p * r.1)))) ≤ 1

/-- `book/MARINA/MARINA.json#/assumptions/19`, Eq. (61). -/
def PPPLStepsizeCondition (γ L p ω : ℝ) (μ : PositivePLParameter)
    (r : Count) : Prop :=
  γ * (L * (1 + Real.sqrt (2 * (1 - p) * (1 + ω) / (p * r.1)))) ≤ 1 ∧
    2 * γ * μ ≤ p

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/4`:
"`p=ζ_Q/d`". -/
noncomputable def marinaDensityRefreshSchedule (ζ : ℝ) (d : Count) : ℝ := ζ / d.1

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/5`:
"`p=min{ζ_Q/d,b⁰/(m+b⁰)}`". -/
noncomputable def finiteSumDensityBatchRefreshSchedule (ζ : ℝ) (d m b0 : Count) : ℝ :=
  min (ζ / d.1) ((b0.1 : ℝ) / (m.1 + b0.1 : ℕ))

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/6`:
"`p=min{ζ_Q/d,b⁰/(b+b⁰)}`". -/
noncomputable def onlineDensityBatchRefreshSchedule (ζ : ℝ) (d b b0 : Count) : ℝ :=
  min (ζ / d.1) ((b0.1 : ℝ) / (b.1 + b0.1 : ℕ))

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/7`:
"`p=ζ_Q r/(dn)`". -/
noncomputable def ppDensityRefreshSchedule (ζ : ℝ) (d n r : Count) : ℝ :=
  ζ * r.1 / (d.1 * n.1)

/-! The eight corollaries state their stepsize bound after substituting the
density-based choice of `p`.  These predicates preserve that source order;
the following bridge theorems connect them to the general theorem predicates. -/

def MARINADensityStepsizeCondition (γ L ω ζ : ℝ) (d n : Count) : Prop :=
  MARINAStepsizeCondition γ L (marinaDensityRefreshSchedule ζ d) ω n

def MARINAPLDensityStepsizeCondition (γ L ω ζ : ℝ)
    (μ : PositivePLParameter) (d n : Count) : Prop :=
  MARINAPLStepsizeCondition γ L (marinaDensityRefreshSchedule ζ d) ω μ n

def FiniteSumDensityStepsizeCondition (γ L ℒ ω ζ : ℝ)
    (d n m b0 : Count) : Prop :=
  FiniteSumVRStepsizeCondition γ L ℒ
    (finiteSumDensityBatchRefreshSchedule ζ d m b0) ω n b0

def FiniteSumPLDensityStepsizeCondition (γ L ℒ ω ζ : ℝ)
    (μ : PositivePLParameter) (d n m b0 : Count) : Prop :=
  FiniteSumVRPLStepsizeCondition γ L ℒ
    (finiteSumDensityBatchRefreshSchedule ζ d m b0) ω μ n b0

def OnlineDensityStepsizeCondition (γ L ℒ ω ζ : ℝ)
    (d n b b0 : Count) : Prop :=
  OnlineVRStepsizeCondition γ L ℒ
    (onlineDensityBatchRefreshSchedule ζ d b b0) ω n b0

def OnlinePLDensityStepsizeCondition (γ L ℒ ω ζ : ℝ)
    (μ : PositivePLParameter) (d n b b0 : Count) : Prop :=
  OnlineVRPLStepsizeCondition γ L ℒ
    (onlineDensityBatchRefreshSchedule ζ d b b0) ω μ n b0

def PPDensityStepsizeCondition (γ L ω ζ : ℝ) (d n r : Count) : Prop :=
  PPStepsizeCondition γ L (ppDensityRefreshSchedule ζ d n r) ω r

def PPPLDensityStepsizeCondition (γ L ω ζ : ℝ)
    (μ : PositivePLParameter) (d n r : Count) : Prop :=
  PPPLStepsizeCondition γ L (ppDensityRefreshSchedule ζ d n r) ω μ r

theorem density_stepsize_bridge_MARINA {d n : Count} {γ L ω ζ p : ℝ}
    (hp : p = marinaDensityRefreshSchedule ζ d)
    (h : MARINADensityStepsizeCondition γ L ω ζ d n) :
    MARINAStepsizeCondition γ L p ω n := by simpa [hp, MARINADensityStepsizeCondition]

theorem density_stepsize_bridge_MARINA_PL {d n : Count} {γ L ω ζ p : ℝ}
    {μ : PositivePLParameter} (hp : p = marinaDensityRefreshSchedule ζ d)
    (h : MARINAPLDensityStepsizeCondition γ L ω ζ μ d n) :
    MARINAPLStepsizeCondition γ L p ω μ n := by
  simpa [hp, MARINAPLDensityStepsizeCondition]

theorem density_stepsize_bridge_finiteSum {d n m b0 : Count}
    {γ L ℒ ω ζ p : ℝ} (hp : p = finiteSumDensityBatchRefreshSchedule ζ d m b0)
    (h : FiniteSumDensityStepsizeCondition γ L ℒ ω ζ d n m b0) :
    FiniteSumVRStepsizeCondition γ L ℒ p ω n b0 := by
  simpa [hp, FiniteSumDensityStepsizeCondition]

theorem density_stepsize_bridge_finiteSum_PL {d n m b0 : Count}
    {γ L ℒ ω ζ p : ℝ} {μ : PositivePLParameter}
    (hp : p = finiteSumDensityBatchRefreshSchedule ζ d m b0)
    (h : FiniteSumPLDensityStepsizeCondition γ L ℒ ω ζ μ d n m b0) :
    FiniteSumVRPLStepsizeCondition γ L ℒ p ω μ n b0 := by
  simpa [hp, FiniteSumPLDensityStepsizeCondition]

theorem density_stepsize_bridge_online {d n b b0 : Count}
    {γ L ℒ ω ζ p : ℝ} (hp : p = onlineDensityBatchRefreshSchedule ζ d b b0)
    (h : OnlineDensityStepsizeCondition γ L ℒ ω ζ d n b b0) :
    OnlineVRStepsizeCondition γ L ℒ p ω n b0 := by
  simpa [hp, OnlineDensityStepsizeCondition]

theorem density_stepsize_bridge_online_PL {d n b b0 : Count}
    {γ L ℒ ω ζ p : ℝ} {μ : PositivePLParameter}
    (hp : p = onlineDensityBatchRefreshSchedule ζ d b b0)
    (h : OnlinePLDensityStepsizeCondition γ L ℒ ω ζ μ d n b b0) :
    OnlineVRPLStepsizeCondition γ L ℒ p ω μ n b0 := by
  simpa [hp, OnlinePLDensityStepsizeCondition]

theorem density_stepsize_bridge_PP {d n r : Count} {γ L ω ζ p : ℝ}
    (hp : p = ppDensityRefreshSchedule ζ d n r)
    (h : PPDensityStepsizeCondition γ L ω ζ d n r) :
    PPStepsizeCondition γ L p ω r := by simpa [hp, PPDensityStepsizeCondition]

theorem density_stepsize_bridge_PP_PL {d n r : Count} {γ L ω ζ p : ℝ}
    {μ : PositivePLParameter} (hp : p = ppDensityRefreshSchedule ζ d n r)
    (h : PPPLDensityStepsizeCondition γ L ω ζ μ d n r) :
    PPPLStepsizeCondition γ L p ω μ r := by
  simpa [hp, PPPLDensityStepsizeCondition]

/-! ## Canonical source cost expressions -/

/-- Eqs. (19), (26), (31), (39), (44), and (52): expected per-worker
communication count for all-worker variants. -/
noncomputable def allWorkerCommunicationCount
    (d K : Count) (p ζ : ℝ) : ℝ :=
  d.1 + K.1 * (p * d.1 + (1 - p) * ζ)

/-- Eqs. (30) and (38): finite-sum stochastic-oracle calls per worker. -/
noncomputable def finiteSumOracleCallCount
    (m b0 K : Count) (p : ℝ) : ℝ :=
  m.1 + K.1 * (p * m.1 + 2 * (1 - p) * b0.1)

/-- Eqs. (43) and (51): online stochastic-oracle calls per worker. -/
noncomputable def onlineOracleCallCount
    (b b0 K : Count) (p : ℝ) : ℝ :=
  b.1 + K.1 * (p * b.1 + 2 * (1 - p) * b0.1)

/-- Eqs. (57) and (64): total PP-MARINA communication count. -/
noncomputable def ppCommunicationCount
    (d n r K : Count) (p ζ : ℝ) : ℝ :=
  d.1 * n.1 + K.1 * (p * d.1 * n.1 + (1 - p) * ζ * r.1)

/-- Companion endpoint for Theorems C.1/C.2, Eqs. (19)/(26). -/
theorem Theorem_C1_C2_communication_count {d K : Count} (p ζ : ℝ) :
    allWorkerCommunicationCount d K p ζ =
      d.1 + K.1 * (p * d.1 + (1 - p) * ζ) := by
  rfl

/-- Companion oracle and communication endpoints for Theorems D.1/D.2,
Eqs. (30)-(31) and (38)-(39). -/
theorem Theorem_D1_D2_cost_counts {d m b0 K : Count} (p ζ : ℝ) :
    finiteSumOracleCallCount m b0 K p =
        m.1 + K.1 * (p * m.1 + 2 * (1 - p) * b0.1) ∧
      allWorkerCommunicationCount d K p ζ =
        d.1 + K.1 * (p * d.1 + (1 - p) * ζ) := by
  exact ⟨rfl, rfl⟩

/-- Companion oracle and communication endpoints for Theorems D.3/D.4,
Eqs. (43)-(44) and (51)-(52). -/
theorem Theorem_D3_D4_cost_counts {d b b0 K : Count} (p ζ : ℝ) :
    onlineOracleCallCount b b0 K p =
        b.1 + K.1 * (p * b.1 + 2 * (1 - p) * b0.1) ∧
      allWorkerCommunicationCount d K p ζ =
        d.1 + K.1 * (p * d.1 + (1 - p) * ζ) := by
  exact ⟨rfl, rfl⟩

/-- Companion communication endpoint for Theorems E.1/E.2,
Eqs. (57)/(64). -/
theorem Theorem_E1_E2_communication_count {d n r K : Count} (p ζ : ℝ) :
    ppCommunicationCount d n r K p ζ =
      d.1 * n.1 + K.1 * (p * d.1 * n.1 + (1 - p) * ζ * r.1) := by
  rfl

/-! ## Output object shared by Algorithms 1--4 -/

/-- `book/MARINA/MARINA.json#/algorithm_spec/output`:
"`x̂^K chosen uniformly at random from {x^k}_{k=0}^{K-1}`".  This evaluates
the generated process at the selected source index. -/
def outputAt {d K : Count} {Ω : Type*}
    (run : ℕ → Ω → State d) (index : Fin K.1) (path : Ω) : Point d :=
  (run index.1 path).x

/-- `book/MARINA/MARINA.json#/algorithm_spec/output`:
"`x̂^K chosen uniformly at random from {x^k}_{k=0}^{K-1}`". -/
noncomputable def uniformOutputIndexLaw (K : Count) : Measure (Fin K.1) :=
  letI : Nonempty (Fin K.1) := ⟨⟨0, K.2⟩⟩
  (PMF.uniformOfFintype (Fin K.1)).toMeasure

/-- The joint experiment for a generated path and an independent uniform
output index. -/
noncomputable def uniformOutputExperimentLaw {Ω : Type*} [MeasurableSpace Ω]
    (pathLaw : Measure Ω) (K : Count) : Measure (Ω × Fin K.1) :=
  pathLaw.prod (uniformOutputIndexLaw K)

/-- `book/MARINA/MARINA.json#/algorithm_spec/output`:
"`x̂^K chosen uniformly at random from {x^k}_{k=0}^{K-1}`". -/
def uniformOutput {d K : Count} {Ω : Type*}
    (run : ℕ → Ω → State d) (experiment : Ω × Fin K.1) : Point d :=
  outputAt run experiment.2 experiment.1

/-- Pushforward output law, with measurability passed as a derived bridge so
`Measure.map` cannot silently take its nonmeasurable fallback branch. -/
noncomputable def uniformOutputLaw {d K : Count} {Ω : Type*}
    [MeasurableSpace Ω] (run : ℕ → Ω → State d) (pathLaw : Measure Ω)
    (_hMeasurable : Measurable (uniformOutput (K := K) run)) : Measure (Point d) :=
  Measure.map (uniformOutput (K := K) run) (uniformOutputExperimentLaw pathLaw K)

/-- Uniform-output averaging identity used by all four nonconvex theorems. -/
theorem uniformOutput_expectation_eq_average {d K : Count} {Ω : Type*}
    [MeasurableSpace Ω] (run : ℕ → Ω → State d) (pathLaw : Measure Ω)
    (φ : Point d → ℝ)
    (hIntegrable : ∀ k : Fin K.1, Integrable (fun path => φ ((run k.1 path).x)) pathLaw) :
    (∫ z, φ (uniformOutput (K := K) run z) ∂uniformOutputExperimentLaw pathLaw K) =
      average (fun k : Fin K.1 => ∫ path, φ ((run k.1 path).x) ∂pathLaw) := by
  classical
  letI : Nonempty (Fin K.1) := ⟨⟨0, K.2⟩⟩
  let c : ENNReal := ENNReal.ofReal ((K.1 : ℝ)⁻¹)
  let F : Fin K.1 → Ω → ℝ := fun k path => φ ((run k.1 path).x)
  have hF : ∀ k, Integrable (F k) pathLaw := hIntegrable
  have hIndex :
      uniformOutputIndexLaw K = ∑ k : Fin K.1, c • Measure.dirac k := by
    apply Measure.ext_of_singleton
    intro j
    simp [uniformOutputIndexLaw, c, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply, ENNReal.ofReal_inv_of_pos, K.2, Pi.single_apply]
  have hProdDirac : ∀ k : Fin K.1,
      pathLaw.prod (Measure.dirac k) =
        Measure.map (fun path : Ω => (path, k)) pathLaw := by
    intro k
    by_cases hSFinite : SFinite pathLaw
    · letI : SFinite pathLaw := hSFinite
      exact Measure.prod_dirac k
    · apply Measure.ext
      intro s hs
      rw [Measure.prod_apply hs, Measure.map_apply measurable_prodMk_right hs]
      simp
      have ht : MeasurableSet {x : Ω | (x, k) ∈ s} :=
        measurable_prodMk_right hs
      change (∫⁻ x : Ω, {x : Ω | (x, k) ∈ s}.indicator (fun _ => 1) x ∂pathLaw) =
        pathLaw {x : Ω | (x, k) ∈ s}
      exact MeasureTheory.lintegral_indicator_one ht
  have hAtomInt : ∀ k : Fin K.1,
      Integrable (fun z : Ω × Fin K.1 => F z.2 z.1)
        (pathLaw.prod (Measure.dirac k)) := by
    intro k
    rw [hProdDirac k]
    rw [(measurableEmbedding_prod_mk_right k).integrable_map_iff]
    exact hF k
  have hScaledAtomInt : ∀ k : Fin K.1,
      Integrable (fun z : Ω × Fin K.1 => F z.2 z.1)
        (pathLaw.prod (c • Measure.dirac k)) := by
    intro k
    rw [Measure.prod_smul_right (μ := pathLaw) (ν := Measure.dirac k) c]
    exact (hAtomInt k).smul_measure (by simp [c])
  have hSumInt :
      Integrable (fun z : Ω × Fin K.1 => F z.2 z.1)
        (Measure.sum (fun k : Fin K.1 => pathLaw.prod (c • Measure.dirac k))) := by
    rw [Measure.sum_fintype, MeasureTheory.integrable_finset_sum_measure]
    intro k _hk
    exact hScaledAtomInt k
  change (∫ z : Ω × Fin K.1, F z.2 z.1
      ∂pathLaw.prod (uniformOutputIndexLaw K)) =
    average (fun k : Fin K.1 => ∫ path, F k path ∂pathLaw)
  rw [hIndex, ← Measure.sum_fintype, Measure.prod_sum_right]
  rw [MeasureTheory.integral_sum_measure hSumInt, tsum_fintype]
  calc
    (∑ k : Fin K.1, ∫ z : Ω × Fin K.1, F z.2 z.1
        ∂pathLaw.prod (c • Measure.dirac k)) =
        ∑ k : Fin K.1, c.toReal * ∫ path, F k path ∂pathLaw := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Measure.prod_smul_right (μ := pathLaw) (ν := Measure.dirac k) c]
          rw [MeasureTheory.integral_smul_measure]
          rw [hProdDirac k]
          rw [(measurableEmbedding_prod_mk_right k).integral_map]
          rfl
    _ = average (fun k : Fin K.1 => ∫ path, F k path ∂pathLaw) := by
          simp [average, SOptLib.finiteUniformAverage, c, ENNReal.toReal_ofReal,
            inv_nonneg, Fintype.card_fin, Finset.mul_sum]

/-! ## Registered Appendix B identities and estimator recurrences -/

/-- `book/MARINA/MARINA.json#/key_lemmas/0`, Eq. (13):
"`E[‖ξ-Eξ‖²]=E[‖ξ-x‖²]-‖Eξ-x‖²`".  The moment premises
only express the equation's stated well-definedness. -/
theorem VarianceDecomposition_B13 {d : Count} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Point d) (x : Point d)
    (hξ : Integrable ξ μ)
    (hCentered : Integrable (fun ω => ‖ξ ω - ∫ z, ξ z ∂μ‖ ^ 2) μ)
    (hShifted : Integrable (fun ω => ‖ξ ω - x‖ ^ 2) μ) :
    (∫ ω, ‖ξ ω - ∫ z, ξ z ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖ξ ω - x‖ ^ 2 ∂μ) - ‖(∫ z, ξ z ∂μ) - x‖ ^ 2 := by
  have hG : Integrable (fun ω => ξ ω - x) μ :=
    hξ.sub (integrable_const (c := x))
  have hGmean :
      (∫ ω, ξ ω - x ∂μ) = (∫ ω, ξ ω ∂μ) - x := by
    have hsub := integral_sub hξ (integrable_const (c := x))
    simpa [integral_const, probReal_univ] using hsub
  have hcenter_eq :
      (fun ω => ‖(ξ ω - x) - ((∫ z, ξ z ∂μ) - x)‖ ^ (2 : ℕ)) =
        (fun ω => ‖ξ ω - ∫ z, ξ z ∂μ‖ ^ (2 : ℕ)) := by
    funext ω
    congr 2
    abel
  have hcenter_shift :
      Integrable
        (fun ω => ‖(ξ ω - x) - ((∫ z, ξ z ∂μ) - x)‖ ^ (2 : ℕ)) μ := by
    rw [hcenter_eq]
    exact hCentered
  have hshifted_int :
      Integrable (fun ω => ‖ξ ω - x‖ ^ (2 : ℕ)) μ := hShifted
  have hdecomp :=
    integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
      μ (fun ω => ξ ω - x) ((∫ z, ξ z ∂μ) - x)
      hG hcenter_shift hGmean
  rw [hcenter_eq] at hdecomp
  linarith

/-- `book/MARINA/MARINA.json#/key_lemmas/1`, Eq. (14):
"`E[ξ]=E[E[ξ|η]]` under an assumption that all expectations are
well-defined." -/
theorem TowerProperty_B14 {Ω E : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (m : MeasurableSpace Ω) (ξ : Ω → E)
    (h : @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
      Ω E m0 _ μ m ξ) :
    (∫ ω, ξ ω ∂μ) =
      ∫ ω, (@MeasureTheory.condExp Ω E m (m₀ := m0) _ _ _ μ ξ) ω ∂μ := by
  exact
    (@SOptLib.ConditionalExpectation.conditionalExpectationWellDefined.integral_condExp
      Ω E m0 _ _ _ μ m ξ h).symm

/-- Paper-level meaning of "`f` is `L`-smooth" used in Lemma B.1. -/
def IsGradientLipschitz {d : Count} (f : Point d → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ f ∧ ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- `book/MARINA/MARINA.json#/key_lemmas/2`, Lemma B.1 / Eq. (15). -/
theorem DescentLemma_B1 {d : Count} (f : Point d → ℝ) (L γ : ℝ)
    (x g : Point d) (hSmooth : IsGradientLipschitz f L) :
    f (x - γ • g) ≤ f x - γ / 2 * ‖gradient f x‖ ^ 2 -
      (1 / (2 * γ) - L / 2) * ‖(x - γ • g) - x‖ ^ 2 +
      γ / 2 * ‖g - gradient f x‖ ^ 2 := by
  rcases hSmooth with ⟨hDiff, hLip⟩
  by_cases hγ : γ = 0
  · simp [hγ]
  · have hsmooth :
        f (x - γ • g) ≤
          f x + inner ℝ (gradient f x) ((x - γ • g) - x) +
            (L / 2) * ‖(x - γ • g) - x‖ ^ 2 := by
      apply smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
        Set.univ f (gradient f) L convex_univ
      · intro z _hz
        exact (hDiff z).hasGradientAt
      · intro z _hz w _hw
        exact hLip z w
      · simp
      · simp
    have hinner :
        inner ℝ (gradient f x) (-γ • g) =
          -(γ / 2) * ‖gradient f x‖ ^ 2 -
            (2 * γ)⁻¹ * ‖-γ • g‖ ^ 2 +
            (γ / 2) * ‖g - gradient f x‖ ^ 2 :=
      SOptLib.inner_neg_smul_eq_neg_half_eta_norm_sq_sub_step_sq_add_error_sq
        hγ (gradient f x) g
    have hdisp : (x - γ • g) - x = -γ • g := by
      calc
        (x - γ • g) - x = -(γ • g) := by abel
        _ = -γ • g := by rw [neg_smul]
    calc
      f (x - γ • g) ≤
          f x + inner ℝ (gradient f x) (-γ • g) +
            (L / 2) * ‖-γ • g‖ ^ 2 := by
        simpa [hdisp] using hsmooth
      _ = f x - γ / 2 * ‖gradient f x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) * ‖(x - γ • g) - x‖ ^ 2 +
          γ / 2 * ‖g - gradient f x‖ ^ 2 := by
        rw [hinner, hdisp]
        ring

/-- `book/MARINA/MARINA.json#/key_lemmas/3`: Assumption 1.2 implies
global `L`-smoothness for `L²=n⁻¹∑Lᵢ²`. -/
theorem GlobalSmoothness_from_Assumption_1_2 {d n : Count}
    (P : LocalProblem d n) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth P Llocal) :
    IsGradientLipschitz (globalObjective P) (rootMeanSquare Llocal) := by
  classical
  rcases hSmooth with ⟨hDiff, hLip⟩
  have hLlocal_nonneg : ∀ i, 0 ≤ Llocal i := by
    intro i
    let e : Point d := EuclideanSpace.single ⟨0, d.2⟩ 1
    have hbound := hLip i (0 : Point d) e
    have he : ‖(0 : Point d) - e‖ = 1 := by
      simp [e]
    rw [he, mul_one] at hbound
    exact le_trans (norm_nonneg _) hbound
  have hMeanSquare_nonneg : 0 ≤ meanSquare Llocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hRms_nonneg : 0 ≤ rootMeanSquare Llocal :=
    Real.sqrt_nonneg _
  have hRms_sq :
      (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
    unfold rootMeanSquare
    exact Real.sq_sqrt hMeanSquare_nonneg
  have hsq : ∀ x y : Point d,
      SOptLib.finiteUniformAverage
          (fun i : Worker n =>
            ‖localGradient P i x - localGradient P i y‖ ^ 2) ≤
        (rootMeanSquare Llocal) ^ 2 * ‖x - y‖ ^ 2 := by
    intro x y
    have hpoint : ∀ i : Worker n,
        ‖localGradient P i x - localGradient P i y‖ ^ 2 ≤
          (Llocal i) ^ 2 * ‖x - y‖ ^ 2 := by
      intro i
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (hLlocal_nonneg i) (norm_nonneg _))).2 (hLip i x y)
    rw [hRms_sq]
    unfold meanSquare average SOptLib.finiteUniformAverage
    simp only [smul_eq_mul]
    calc
      (Fintype.card (Worker n) : ℝ)⁻¹ *
          ∑ i : Worker n, ‖localGradient P i x - localGradient P i y‖ ^ 2 ≤
        (Fintype.card (Worker n) : ℝ)⁻¹ *
          ∑ i : Worker n, (Llocal i) ^ 2 * ‖x - y‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _hi => hpoint i) (by positivity)
      _ = ((Fintype.card (Worker n) : ℝ)⁻¹ *
          ∑ i : Worker n, (Llocal i) ^ 2) * ‖x - y‖ ^ 2 := by
            rw [← Finset.sum_mul]
            ring
  constructor
  · unfold globalObjective average SOptLib.finiteUniformAverage
    fun_prop
  · have hAvgLip :=
      SOptLib.finiteAverageGradient_lipschitz_of_average_sq_smoothness
        (averageLocalGradient P) (localGradient P)
        (rootMeanSquare Llocal) hRms_nonneg
        (by
          intro x
          rfl)
        hsq
    intro x y
    change ‖globalGradient P x - globalGradient P y‖ ≤
      rootMeanSquare Llocal * ‖x - y‖
    rw [globalGradient_eq_averageLocalGradient P hDiff x,
      globalGradient_eq_averageLocalGradient P hDiff y]
    exact hAvgLip x y

theorem average_const_add {I V : Type*} [Fintype I] [Nonempty I]
    [AddCommMonoid V] [Module ℝ V] (c : V) (u : I → V) :
    average (fun i => c + u i) = c + average u := by
  unfold average
  calc
    SOptLib.finiteUniformAverage (fun i => c + u i) =
        SOptLib.finiteUniformAverage (fun _i : I => c) +
          SOptLib.finiteUniformAverage u := by
      simp only [SOptLib.finiteUniformAverage_def, Finset.sum_add_distrib, smul_add]
    _ = c + SOptLib.finiteUniformAverage u := by
      rw [SOptLib.finiteUniformAverage_const]

/-- `book/MARINA/MARINA.json#/key_lemmas/4`, the Algorithm 1 two-branch
server-estimator update derived from the canonical transition. -/
theorem MARINA_estimator_update {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (z : BasicDriver n Ξ)
    (s : State d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) :
    (marinaStep A z s).g =
      if z.refresh then globalGradient A.problem (primalStep A.stepSize s)
      else s.g + average (fun i : Worker n =>
        A.quantizer.apply
          (localGradientDifference A.problem i (primalStep A.stepSize s) s.x)
          (z.compressionSample i)) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  cases h : z.refresh with
  | false =>
      simp only [marinaStep, h, Bool.false_eq_true, if_false]
      unfold marinaWorkerEstimator localGradientDifference
      simp only [h, Bool.false_eq_true, if_false]
      change average (fun i : Worker n =>
          s.g + A.quantizer.apply
            (localGradient A.problem i (primalStep A.stepSize s) -
              localGradient A.problem i s.x)
            (z.compressionSample i)) =
        s.g + average (fun i : Worker n =>
          A.quantizer.apply
            (localGradient A.problem i (primalStep A.stepSize s) -
              localGradient A.problem i s.x)
            (z.compressionSample i))
      exact average_const_add s.g _
  | true =>
      simp only [marinaStep, h, if_true]
      unfold marinaWorkerEstimator
      simp only [h, if_true]
      change average (fun i : Worker n =>
          localGradient A.problem i (primalStep A.stepSize s)) =
        globalGradient A.problem (primalStep A.stepSize s)
      simpa [averageLocalGradient] using
        (globalGradient_eq_averageLocalGradient A.problem hSmooth.1
          (primalStep A.stepSize s)).symm

/-- `book/MARINA/MARINA.json#/key_lemmas/5`, the Algorithm 4 two-branch
server estimator derived from `ppActiveClients`, `ppWorkerEstimator`,
`ppAggregation`, and `ppStep`. -/
theorem PP_estimator_update {d n r : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (z : PPDriver n r Ξ)
    (s : State d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) :
    (ppStep A z s).g =
      if z.refresh then globalGradient A.problem (primalStep A.stepSize s)
      else s.g + average (fun j : Fin r.1 =>
        A.quantizer.apply
          (localGradientDifference A.problem (z.sampledClient j)
            (primalStep A.stepSize s) s.x)
          (z.compressionSample j)) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin r.1) := ⟨⟨0, r.2⟩⟩
  cases h : z.refresh with
  | false =>
      simp only [ppStep, ppEstimatorStep, ppActiveClients, h,
        Bool.false_eq_true, if_false, ppAggregation]
      unfold ppWorkerEstimator localGradientDifference
      exact average_const_add s.g _
  | true =>
      simp only [ppStep, ppEstimatorStep, ppActiveClients, h, if_true,
        ppAggregation]
      unfold ppWorkerEstimator
      change average (fun i : Worker n =>
          localGradient A.problem i (primalStep A.stepSize s)) =
        globalGradient A.problem (primalStep A.stepSize s)
      simpa [averageLocalGradient] using
        (globalGradient_eq_averageLocalGradient A.problem hSmooth.1
          (primalStep A.stepSize s)).symm

/-- Expected squared estimator error of a generated state process. -/
noncomputable def estimatorErrorMoment {d n : Count} {Ω : Type*}
    [MeasurableSpace Ω] (P : LocalProblem d n) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (k : ℕ) : ℝ :=
  ∫ path, ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂pathLaw

/-- Domain certificate ensuring `estimatorErrorMoment` denotes the paper's
expectation rather than Mathlib's nonintegrable fallback. -/
def EstimatorErrorMomentWellDefined {d n : Count} {Ω : Type*}
    [MeasurableSpace Ω] (P : LocalProblem d n) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (k : ℕ) : Prop :=
  Integrable (fun path =>
    ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) pathLaw

/-- Expected squared primal displacement of a generated state process. -/
noncomputable def stepMoment {d : Count} {Ω : Type*} [MeasurableSpace Ω]
    (run : ℕ → Ω → State d) (pathLaw : Measure Ω) (k : ℕ) : ℝ :=
  ∫ path, ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂pathLaw

/-- Domain certificate ensuring `stepMoment` is a nonfallback expectation. -/
def StepMomentWellDefined {d : Count} {Ω : Type*} [MeasurableSpace Ω]
    (run : ℕ → Ω → State d) (pathLaw : Measure Ω) (k : ℕ) : Prop :=
  Integrable (fun path =>
    ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) pathLaw

/-- The strict round prefix and current round have their canonical product law.
This is the conditional-freshness bridge used in the proof of Eq. (33). -/
theorem finite_sum_prefix_current_round_map_eq_prod
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
          ((fun j : Fin k => path j.1), path k))
        (finiteSumPathLaw A batchLaw) =
      (Measure.map
          (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
            fun j : Fin k => path j.1)
          (finiteSumPathLaw A batchLaw)).prod
        (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  unfold finiteSumPathLaw
  simpa using
    (infinitePi_prefix_current_map_eq_prod
      (fun t : ℕ =>
        finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) k)

theorem finite_sum_path_worker_noise_map_eq_prod
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (k : ℕ) (i : Worker n) :
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i))
        (finiteSumPathLaw A batchLaw) =
      (batchLaw k i).prod A.quantizer.law := by
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (batchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  calc
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i))
        (finiteSumPathLaw A batchLaw) =
        Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i))
          (Measure.map
            (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
            (finiteSumPathLaw A batchLaw)) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_pi_apply k
    _ = Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i))
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
            rw [finiteSumPathLaw_round_marginal A batchLaw hBatchLaw k]
    _ = Measure.map
          (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
            (z.1 i, z.2 i))
          ((finiteSumBatchJointLaw batchLaw k).prod
            (workerCompressionLaw A.quantizer)) := by
              unfold finiteSumRoundLaw
              calc
                Measure.map
                    (fun z : FiniteSumRoundNoise n m b0 Ξ =>
                      (z.2.1 i, z.2.2 i))
                    ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                      ((finiteSumBatchJointLaw batchLaw k).prod
                        (workerCompressionLaw A.quantizer))) =
                    Measure.map
                      (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
                        (z.1 i, z.2 i))
                      (Measure.map Prod.snd
                        ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                          ((finiteSumBatchJointLaw batchLaw k).prod
                            (workerCompressionLaw A.quantizer)))) := by
                              rw [MeasureTheory.Measure.map_map]
                              · rfl
                              · fun_prop
                              · exact measurable_snd
                _ = Measure.map
                    (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
                      (z.1 i, z.2 i))
                    ((finiteSumBatchJointLaw batchLaw k).prod
                      (workerCompressionLaw A.quantizer)) := by
                        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
    _ = (Measure.map (fun batch : FiniteSumBatch n m b0 => batch i)
          (finiteSumBatchJointLaw batchLaw k)).prod
        (Measure.map (fun samples : Worker n → Ξ => samples i)
          (workerCompressionLaw A.quantizer)) := by
            simpa [Prod.map] using
              (MeasureTheory.Measure.map_prod_map
                (finiteSumBatchJointLaw batchLaw k)
                (workerCompressionLaw A.quantizer)
                (measurable_pi_apply i) (measurable_pi_apply i)).symm
    _ = (batchLaw k i).prod A.quantizer.law := by
      rw [finiteSumBatchJointLaw_worker_marginal batchLaw hBatchLaw k i,
        workerCompressionLaw_component_marginal A.quantizer i]

theorem finite_sum_strictPast_query_indep_worker_noise
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (k : ℕ) (i : Worker n) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((finiteSumProcess (b0 := b0) A x0 (k + 1) path).x,
          (finiteSumProcess (b0 := b0) A x0 k path).x))
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i))
      (finiteSumPathLaw A batchLaw) := by
  classical
  let query : (ℕ → FiniteSumRoundNoise n m b0 Ξ) → Point d × Point d := fun path =>
    (primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path),
      (finiteSumProcess (b0 := b0) A x0 k path).x)
  let workerNoise : (ℕ → FiniteSumRoundNoise n m b0 Ξ) →
      FiniteSumWorkerBatch m b0 × Ξ := fun path =>
    ((path k).2.1 i, (path k).2.2 i)
  let pastBlock := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    fun j : Fin k => path j.1
  let current := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k
  let prefixLaw := Measure.map pastBlock (finiteSumPathLaw A batchLaw)
  let roundLaw := finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (batchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure (finiteSumPathLaw A batchLaw) := by
    unfold finiteSumPathLaw
    infer_instance
  have hquery : Measurable[finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] query := by
    have hs := finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k
    exact ((measurable_primalStep A.stepSize).comp hs).prodMk
      ((measurable_state_x d).comp hs)
  have hpastBlock : Measurable pastBlock := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastBlock.aemeasurable
  have hpast_current : ProbabilityTheory.IndepFun pastBlock current
      (finiteSumPathLaw A batchLaw) := by
    refine indepFun_of_map_prod_eq_prod_laws
      (P := finiteSumPathLaw A batchLaw)
      (Z := fun path => (pastBlock path, current path))
      (mu := prefixLaw) (nu := roundLaw) ?_ ?_
    · exact (hpastBlock.prodMk hcurrent).aemeasurable
    · simpa [pastBlock, current, prefixLaw, roundLaw] using
        finite_sum_prefix_current_round_map_eq_prod A batchLaw hBatchLaw k
  have hpast_worker : ProbabilityTheory.IndepFun pastBlock workerNoise
      (finiteSumPathLaw A batchLaw) := by
    have hcomp := hpast_current.comp measurable_id
      (show Measurable
        (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i)) by
          fun_prop)
    simpa [current, workerNoise, Function.comp_def] using hcomp
  have hstrict_le : finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      MeasurableSpace.comap pastBlock inferInstance := by
    refine iSup_le fun j => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastBlock inferInstance]
        pastBlock := measurable_iff_comap_le.mpr le_rfl
    have hj : Measurable[MeasurableSpace.comap pastBlock inferInstance]
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path j.1) :=
      (measurable_pi_apply j).comp hpast_comap
    exact hj.comap_le
  have hcomap_indep : ProbabilityTheory.Indep
      (MeasurableSpace.comap pastBlock inferInstance)
      (MeasurableSpace.comap workerNoise inferInstance)
      (finiteSumPathLaw A batchLaw) := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpast_worker
  have hquery_worker : ProbabilityTheory.IndepFun query workerNoise
      (finiteSumPathLaw A batchLaw) :=
    indepFun_of_measurable_left_of_indep_comap hquery
      (ProbabilityTheory.indep_of_indep_of_le_left hcomap_indep hstrict_le)
  simpa only [query, workerNoise, finiteSumProcess, finiteSumRun_succ,
    finiteSumStep] using hquery_worker

theorem finite_sum_fixed_worker_innovation_centered_second_moment
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n)
    (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) :
    let x := (finiteSumProcess (b0 := b0) A x0 k path).x
    let xNext := (finiteSumProcess (b0 := b0) A x0 (k + 1) path).x
    let delta := localGradientDifference (finiteSumLocalProblem A.problem) i xNext x
    let innovation := fun q : FiniteSumWorkerBatch m b0 × Ξ =>
      A.quantizer.apply
          (finiteSumWorkerBatchDifference A.problem q.1 i xNext x) q.2 - delta
    Integrable (fun q => ‖innovation q‖ ^ 2)
        ((batchLaw k i).prod A.quantizer.law) ∧
      (∫ q, innovation q ∂(batchLaw k i).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(batchLaw k i).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  let x := (finiteSumProcess (b0 := b0) A x0 k path).x
  let xNext := (finiteSumProcess (b0 := b0) A x0 (k + 1) path).x
  let delta := localGradientDifference (finiteSumLocalProblem A.problem) i xNext x
  let D := fun batch : FiniteSumWorkerBatch m b0 =>
    finiteSumWorkerBatchDifference A.problem batch i xNext x
  let innovation := fun q : FiniteSumWorkerBatch m b0 × Ξ =>
    A.quantizer.apply (D q.1) q.2 - delta
  change Integrable (fun q => ‖innovation q‖ ^ 2)
        ((batchLaw k i).prod A.quantizer.law) ∧
      (∫ q, innovation q ∂(batchLaw k i).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(batchLaw k i).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2
  letI : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  have hD_meas : Measurable D := by
    have hpair : Measurable (fun batch : FiniteSumWorkerBatch m b0 =>
        ((xNext, x), batch)) :=
      (measurable_const.prodMk measurable_const).prodMk measurable_id
    simpa [D] using
      (finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0) A.problem i).comp hpair
  have hinnovation_meas : Measurable innovation := by
    have hquantized : Measurable (fun q : FiniteSumWorkerBatch m b0 × Ξ =>
        A.quantizer.apply (D q.1) q.2) :=
      A.quantizer.measurable_apply_uncurry.comp
        ((hD_meas.comp measurable_fst).prodMk measurable_snd)
    exact hquantized.sub measurable_const
  rcases hAverageSmooth.2 k i path with
    ⟨hD_int, hD_center_sq, hD_mean, hD_var⟩
  change Integrable D (batchLaw k i) at hD_int
  change Integrable (fun batch => ‖D batch - delta‖ ^ 2) (batchLaw k i)
    at hD_center_sq
  change (∫ batch, D batch ∂batchLaw k i) = delta at hD_mean
  change (∫ batch, ‖D batch - delta‖ ^ 2 ∂batchLaw k i) ≤
      (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2 at hD_var
  have hD_sq : Integrable (fun batch => ‖D batch‖ ^ 2) (batchLaw k i) :=
    oracle_second_moment_integrable_of_centered_second_moment_integrable
      (batchLaw k i) D delta hD_meas.aestronglyMeasurable hD_center_sq
  have hD_second_eq :
      (∫ batch, ‖D batch‖ ^ 2 ∂batchLaw k i) =
        (∫ batch, ‖D batch - delta‖ ^ 2 ∂batchLaw k i) +
          ‖delta‖ ^ 2 :=
    integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
      (batchLaw k i) D delta hD_int hD_center_sq hD_mean
  have hfiber_int : ∀ batch,
      Integrable (fun ξ => ‖innovation (batch, ξ)‖ ^ 2) A.quantizer.law := by
    intro batch
    let v := D batch
    have hnoise_sq : Integrable
        (fun ξ => ‖A.quantizer.apply v ξ - v‖ ^ 2) A.quantizer.law :=
      quantizer_error_sq_integrable hQuantizer v
    have hconst_sq : Integrable
        (fun _ : Ξ => ‖v - delta‖ ^ 2) A.quantizer.law :=
      integrable_const (c := ‖v - delta‖ ^ 2)
    have hnoise_meas : AEStronglyMeasurable
        (fun ξ => A.quantizer.apply v ξ - v) A.quantizer.law :=
      ((hQuantizer.2 v).1.sub (integrable_const (c := v))).aestronglyMeasurable
    have hsum := integrable_sq_norm_add
      hnoise_meas aestronglyMeasurable_const hnoise_sq hconst_sq
    convert hsum using 1
    funext ξ
    congr 2
    simp only [innovation, v]
    abel
  have hfiber_mean : ∀ batch,
      (∫ ξ, innovation (batch, ξ) ∂A.quantizer.law) = D batch - delta := by
    intro batch
    rw [integral_sub (hQuantizer.2 (D batch)).1 (integrable_const (c := delta))]
    rw [(hQuantizer.2 (D batch)).2.2.1]
    simp [innovation, integral_const, probReal_univ]
  have hfiber_sq_eq : ∀ batch,
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) =
        (∫ ξ, ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := by
    intro batch
    let G := fun ξ => A.quantizer.apply (D batch) ξ - delta
    have hG_int : Integrable G A.quantizer.law :=
      (hQuantizer.2 (D batch)).1.sub (integrable_const (c := delta))
    have hcenter_sq : Integrable
        (fun ξ => ‖G ξ - (D batch - delta)‖ ^ 2) A.quantizer.law := by
      convert (hQuantizer.2 (D batch)).2.1 using 1
      funext ξ
      congr 2
      simp only [G]
      abel
    have hG_mean : (∫ ξ, G ξ ∂A.quantizer.law) = D batch - delta := by
      rw [integral_sub (hQuantizer.2 (D batch)).1 (integrable_const (c := delta))]
      rw [(hQuantizer.2 (D batch)).2.2.1]
      simp [integral_const, probReal_univ]
    have hdecomp :=
      integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
        A.quantizer.law G (D batch - delta) hG_int hcenter_sq hG_mean
    calc
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) =
          ∫ ξ, ‖G ξ‖ ^ 2 ∂A.quantizer.law := by rfl
      _ = (∫ ξ, ‖G ξ - (D batch - delta)‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := hdecomp
      _ = (∫ ξ, ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := by
            congr 1
            apply integral_congr_ae
            refine Filter.Eventually.of_forall fun ξ => ?_
            have hvec : G ξ - (D batch - delta) =
                A.quantizer.apply (D batch) ξ - D batch := by
              simp only [G]
              abel
            change ‖G ξ - (D batch - delta)‖ ^ 2 =
              ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
            rw [hvec]
  have hfiber_bound : ∀ batch,
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) ≤
        ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2 := by
    intro batch
    rw [hfiber_sq_eq batch]
    exact add_le_add (hQuantizer.2 (D batch)).2.2.2 le_rfl
  have hbudget_int : Integrable
      (fun batch => ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
      (batchLaw k i) :=
    (hD_sq.const_mul ω).add hD_center_sq
  have hprod_sq : Integrable (fun q => ‖innovation q‖ ^ 2)
      ((batchLaw k i).prod A.quantizer.law) := by
    apply integrable_prod_of_fiber_integral_norm_le_integrable_bound
      (μ := batchLaw k i) (ν := A.quantizer.law)
      (φ := fun batch ξ => ‖innovation (batch, ξ)‖ ^ 2)
      (B := fun batch => ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
    · simpa [pow_two] using
        (hinnovation_meas.norm.mul hinnovation_meas.norm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hfiber_int
    · exact hbudget_int
    · refine Filter.Eventually.of_forall fun batch => ?_
      calc
        (∫ ξ, ‖‖innovation (batch, ξ)‖ ^ 2‖ ∂A.quantizer.law) =
            ∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ξ =>
                Real.norm_of_nonneg (sq_nonneg _)
        _ ≤ ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2 :=
          hfiber_bound batch
  have hprod_innovation : Integrable innovation
      ((batchLaw k i).prod A.quantizer.law) :=
    integrable_of_integrable_norm_sq hinnovation_meas.aestronglyMeasurable hprod_sq
  have hprod_mean :
      (∫ q, innovation q ∂(batchLaw k i).prod A.quantizer.law) = 0 := by
    rw [integral_prod _ hprod_innovation]
    calc
      (∫ batch, ∫ ξ, innovation (batch, ξ) ∂A.quantizer.law
          ∂batchLaw k i) =
          ∫ batch, D batch - delta ∂batchLaw k i := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hfiber_mean
      _ = 0 := by
        rw [integral_sub hD_int (integrable_const (c := delta)), hD_mean]
        simp [integral_const, probReal_univ]
  have hdelta_norm : ‖delta‖ ≤ Llocal i * ‖xNext - x‖ := by
    simpa [delta, localGradientDifference] using hSmooth.2 i xNext x
  have hdelta_sq : ‖delta‖ ^ 2 ≤ (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _)
      (le_trans (norm_nonneg _) hdelta_norm)).2 hdelta_norm
  have homega_nonneg : 0 ≤ ω := le_of_lt hQuantizer.1
  have hone_omega_nonneg : 0 ≤ 1 + ω := by linarith
  have hdelta_scaled := mul_le_mul_of_nonneg_left hdelta_sq homega_nonneg
  have hvar_scaled := mul_le_mul_of_nonneg_left hD_var hone_omega_nonneg
  refine ⟨hprod_sq, hprod_mean, ?_⟩
  rw [integral_prod _ hprod_sq]
  calc
    (∫ batch, ∫ ξ, ‖innovation (batch, ξ)‖ ^ 2
        ∂A.quantizer.law ∂batchLaw k i) ≤
        ∫ batch, (ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
          ∂batchLaw k i := by
            exact integral_mono hprod_sq.integral_prod_left hbudget_int hfiber_bound
    _ = ω * (∫ batch, ‖D batch‖ ^ 2 ∂batchLaw k i) +
          ∫ batch, ‖D batch - delta‖ ^ 2 ∂batchLaw k i := by
            rw [integral_add (hD_sq.const_mul ω) hD_center_sq,
              integral_const_mul]
    _ = ω * ‖delta‖ ^ 2 + (1 + ω) *
          (∫ batch, ‖D batch - delta‖ ^ 2 ∂batchLaw k i) := by
            rw [hD_second_eq]
            ring
    _ ≤ ω * ((Llocal i) ^ 2 * ‖xNext - x‖ ^ 2) +
          (1 + ω) * ((ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2) :=
            add_le_add hdelta_scaled hvar_scaled
    _ = (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by ring

theorem finite_sum_worker_innovation_centered_second_moment
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n)
    (hStep : StepMomentWellDefined (finiteSumProcess (b0 := b0) A x0)
      (finiteSumPathLaw A batchLaw) k) :
    Integrable (fun path => ‖finiteSumWorkerInnovation A x0 k i path‖ ^ 2)
        (finiteSumPathLaw A batchLaw) ∧
      (∫ path, finiteSumWorkerInnovation A x0 k i path
          ∂finiteSumPathLaw A batchLaw) = 0 ∧
      (∫ path, ‖finiteSumWorkerInnovation A x0 k i path‖ ^ 2
          ∂finiteSumPathLaw A batchLaw) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          stepMoment (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let query0 := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ((finiteSumProcess (b0 := b0) A x0 (k + 1) path).x,
      (finiteSumProcess (b0 := b0) A x0 k path).x)
  let Query := Set.range query0
  let query : (ℕ → FiniteSumRoundNoise n m b0 Ξ) → Query := fun path =>
    ⟨query0 path, ⟨path, rfl⟩⟩
  let sample := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ((path k).2.1 i, (path k).2.2 i)
  let innovation := fun (z : Query) (q : FiniteSumWorkerBatch m b0 × Ξ) =>
    A.quantizer.apply
        (finiteSumWorkerBatchDifference A.problem q.1 i z.1.1 z.1.2) q.2 -
      localGradientDifference (finiteSumLocalProblem A.problem) i z.1.1 z.1.2
  let coeff := ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1
  let budget := fun z : Query => coeff * ‖z.1.1 - z.1.2‖ ^ 2
  let ν := (batchLaw k i).prod A.quantizer.law
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (batchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hquery0 : Measurable query0 := by
    have hk := (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
    have hks := (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 (k + 1)).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) (k + 1)) le_rfl
    exact ((measurable_state_x d).comp hks).prodMk ((measurable_state_x d).comp hk)
  have hquery : Measurable query := Measurable.subtype_mk hquery0
  have hsample : Measurable sample := by
    dsimp [sample]
    fun_prop
  have hindep0 : ProbabilityTheory.IndepFun query0 sample P := by
    simpa [query0, sample, P] using
      finite_sum_strictPast_query_indep_worker_noise A x0 batchLaw hBatchLaw k i
  have hindep : ProbabilityTheory.IndepFun query sample P := by
    have hquery_comap : Measurable[MeasurableSpace.comap query0 inferInstance]
        query := by
      apply Measurable.subtype_mk
      exact measurable_iff_comap_le.mpr le_rfl
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap query0 inferInstance)
        (MeasurableSpace.comap sample inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hindep0
    exact indepFun_of_measurable_left_of_indep_comap hquery_comap hcomap
  have hdist : Measure.map sample P = ν := by
    simpa [sample, P, ν] using
      finite_sum_path_worker_noise_map_eq_prod A batchLaw hBatchLaw k i
  have hinnovation : Measurable (Function.uncurry innovation) := by
    have hpair : Measurable (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
        ((p.1.1, p.2.1) : (Point d × Point d) × FiniteSumWorkerBatch m b0)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)
    have hdiff : Measurable (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
        finiteSumWorkerBatchDifference A.problem p.2.1 i p.1.1.1 p.1.1.2) := by
      simpa only [Function.comp_apply] using
        (finiteSumWorkerBatchDifference_joint_measurable
          (b0 := b0) A.problem i).comp hpair
    have hsampleXi : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) => p.2.2) :=
      measurable_snd.comp measurable_snd
    have hquantized := A.quantizer.measurable_apply_uncurry.comp
      (hdiff.prodMk hsampleXi)
    have hxNext : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) => p.1.1.1) :=
      measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)
    have hx : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) => p.1.1.2) :=
      measurable_snd.comp (measurable_subtype_coe.comp measurable_fst)
    have hmean : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          localGradientDifference (finiteSumLocalProblem A.problem) i p.1.1.1 p.1.1.2) := by
      unfold localGradientDifference
      exact ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp
        hxNext).sub
        ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp hx)
    simpa [innovation, Function.uncurry] using hquantized.sub hmean
  have hbudget : Measurable budget := by
    dsimp [budget]
    fun_prop
  have hfixed : ∀ z : Query,
      Integrable (fun q => ‖innovation z q‖ ^ 2) ν ∧
        (∫ q, innovation z q ∂ν) = 0 ∧
        (∫ q, ‖innovation z q‖ ^ 2 ∂ν) ≤ budget z := by
    intro z
    rcases z with ⟨z, hz⟩
    rcases hz with ⟨path, rfl⟩
    simpa [innovation, budget, coeff, ν, query0] using
      finite_sum_fixed_worker_innovation_centered_second_moment
        A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k i path
  have hbudget_int : Integrable (fun path => budget (query path)) P := by
    simpa [budget, query, query0, coeff, P, StepMomentWellDefined] using
      hStep.const_mul coeff
  have hsq_prod : AEStronglyMeasurable
      (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
        ‖innovation p.1 p.2‖ ^ 2) ((Measure.map query P).prod ν) :=
    hinnovation.norm.pow_const 2 |>.aestronglyMeasurable
  have hsq : Integrable (fun path => ‖innovation (query path) (sample path)‖ ^ 2) P :=
    integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := P) (ν := ν)
      (φ := fun z q => ‖innovation z q‖ ^ 2) (B := budget)
      (X := query) (Y := sample) hsq_prod hbudget.aestronglyMeasurable
      hquery.aemeasurable hsample.aemeasurable hindep hdist
      (fun _ _ => sq_nonneg _) (fun z => (hfixed z).1) hbudget_int
      (fun z => (hfixed z).2.2)
  have hsq_le :
      (∫ path, ‖innovation (query path) (sample path)‖ ^ 2 ∂P) ≤
        ∫ path, budget (query path) ∂P :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := P) (ν := ν)
      (φ := fun z q => ‖innovation z q‖ ^ 2) (B := budget)
      (X := query) (Y := sample) hsq_prod hbudget.aestronglyMeasurable
      hquery.aemeasurable hsample.aemeasurable hindep hdist hsq hbudget_int
      (fun z => (hfixed z).2.2)
  have hinnovation_comp : AEStronglyMeasurable
      (fun path => innovation (query path) (sample path)) P :=
    (hinnovation.comp (hquery.prodMk hsample)).aestronglyMeasurable
  have hint : Integrable (fun path => innovation (query path) (sample path)) P :=
    integrable_of_integrable_norm_sq hinnovation_comp hsq
  have hmean : (∫ path, innovation (query path) (sample path) ∂P) = 0 :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := P) (ν := ν) (φ := innovation) (X := query) (Y := sample)
      hinnovation.aestronglyMeasurable hquery.aemeasurable hsample.aemeasurable
      hindep hdist hint (fun z => (hfixed z).2.1)
  refine ⟨?_, ?_, ?_⟩
  · simpa [innovation, query, query0, sample, P, finiteSumWorkerInnovation,
      finiteSumProcess, finiteSumRun_succ, finiteSumStep] using hsq
  · simpa [innovation, query, query0, sample, P, finiteSumWorkerInnovation,
      finiteSumProcess, finiteSumRun_succ, finiteSumStep] using hmean
  · have hbudget_eq :
        (∫ path, budget (query path) ∂P) = coeff *
          stepMoment (finiteSumProcess (b0 := b0) A x0) P k := by
      simp only [budget, query, query0, integral_const_mul]
      rfl
    rw [hbudget_eq] at hsq_le
    simpa [innovation, query, query0, sample, P, coeff,
      finiteSumWorkerInnovation, finiteSumProcess, finiteSumRun_succ,
      finiteSumStep] using hsq_le

/-- Adjoining an independent product-space prefix to one member of an
independent pair preserves independence from the other member. -/
theorem indepFun_prod_left_adjoin_of_indepFun
    {A Ω B C : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Yj : Ω → B) (Yi : Ω → C)
    (hYj : Measurable Yj) (hYi : Measurable Yi)
    (hindep : ProbabilityTheory.IndepFun Yj Yi ν) :
    ProbabilityTheory.IndepFun
      (fun z : A × Ω => (z.1, Yj z.2))
      (fun z : A × Ω => Yi z.2) (μ.prod ν) := by
  let νj := Measure.map Yj ν
  let νi := Measure.map Yi ν
  have hpair : Measurable (fun z : Ω => (Yj z, Yi z)) := hYj.prodMk hYi
  have hpair_law : Measure.map (fun z => (Yj z, Yi z)) ν = νj.prod νi := by
    simpa [νj, νi] using
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hYj.aemeasurable hYi.aemeasurable).1 hindep
  have hjoined :
      Measure.map (fun z : A × Ω => (z.1, (Yj z.2, Yi z.2))) (μ.prod ν) =
        μ.prod (νj.prod νi) := by
    calc
      Measure.map (fun z : A × Ω => (z.1, (Yj z.2, Yi z.2))) (μ.prod ν) =
          Measure.map (Prod.map id (fun z => (Yj z, Yi z))) (μ.prod ν) := by
            rfl
      _ = (Measure.map id μ).prod
          (Measure.map (fun z => (Yj z, Yi z)) ν) := by
            exact (MeasureTheory.Measure.map_prod_map μ ν measurable_id hpair).symm
      _ = μ.prod (νj.prod νi) := by
            rw [Measure.map_id, hpair_law]
  have hassoc :
      Measure.map MeasurableEquiv.prodAssoc.symm (μ.prod (νj.prod νi)) =
        (μ.prod νj).prod νi := by
    have h := MeasureTheory.Measure.prodAssoc_prod
      (μ := μ) (ν := νj) (τ := νi)
    rw [← h, MeasureTheory.Measure.map_map]
    · simp
    · exact MeasurableEquiv.prodAssoc.symm.measurable
    · exact MeasurableEquiv.prodAssoc.measurable
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_fst.prodMk (hYj.comp measurable_snd)).aemeasurable)
    ((hYi.comp measurable_snd).aemeasurable)).2
  calc
    Measure.map
        (fun z : A × Ω => ((z.1, Yj z.2), Yi z.2)) (μ.prod ν) =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map (fun z : A × Ω => (z.1, (Yj z.2, Yi z.2)))
            (μ.prod ν)) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · exact MeasurableEquiv.prodAssoc.symm.measurable
          · exact (measurable_fst.prodMk (hpair.comp measurable_snd))
    _ = (μ.prod νj).prod νi := by rw [hjoined, hassoc]
    _ = (Measure.map (fun z : A × Ω => (z.1, Yj z.2)) (μ.prod ν)).prod
          (Measure.map (fun z : A × Ω => Yi z.2) (μ.prod ν)) := by
      rw [show Measure.map (fun z : A × Ω => (z.1, Yj z.2)) (μ.prod ν) =
          μ.prod νj by
        calc
          Measure.map (fun z : A × Ω => (z.1, Yj z.2)) (μ.prod ν) =
              Measure.map (Prod.map id Yj) (μ.prod ν) := by rfl
          _ = (Measure.map id μ).prod (Measure.map Yj ν) :=
            (MeasureTheory.Measure.map_prod_map μ ν measurable_id hYj).symm
          _ = μ.prod νj := by simp [νj]]
      rw [show Measure.map (fun z : A × Ω => Yi z.2) (μ.prod ν) = νi by
        calc
          Measure.map (fun z : A × Ω => Yi z.2) (μ.prod ν) =
              Measure.map Yi (Measure.map Prod.snd (μ.prod ν)) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · exact hYi
                · exact measurable_snd
          _ = Measure.map Yi ν := by simp
          _ = νi := rfl]

/-- The adaptive query together with one worker's current noise is fresh from
the current noise of every distinct worker. -/
theorem finite_sum_query_peer_noise_indep_worker_noise
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (k : ℕ) (i j : Worker n) (hij : i ≠ j) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        (((finiteSumProcess (b0 := b0) A x0 (k + 1) path).x,
            (finiteSumProcess (b0 := b0) A x0 k path).x),
          ((path k).2.1 j, (path k).2.2 j)))
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i))
      (finiteSumPathLaw A batchLaw) := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let query : (ℕ → FiniteSumRoundNoise n m b0 Ξ) → Point d × Point d :=
    fun path =>
      (primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path),
        (finiteSumProcess (b0 := b0) A x0 k path).x)
  let workerNoise : Worker n →
      (ℕ → FiniteSumRoundNoise n m b0 Ξ) →
        FiniteSumWorkerBatch m b0 × Ξ :=
    fun q path => ((path k).2.1 q, (path k).2.2 q)
  let roundNoise : Worker n → FiniteSumRoundNoise n m b0 Ξ →
      FiniteSumWorkerBatch m b0 × Ξ :=
    fun q z => (z.2.1 q, z.2.2 q)
  let pastBlock := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    fun q : Fin k => path q.1
  let current := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k
  let prefixLaw := Measure.map pastBlock P
  let roundLaw := finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)
  let joined := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (pastBlock path, workerNoise j path)
  let Z := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (pastBlock path, current path)
  let leftProd := fun z : (Fin k → FiniteSumRoundNoise n m b0 Ξ) ×
      FiniteSumRoundNoise n m b0 Ξ => (z.1, roundNoise j z.2)
  let rightProd := fun z : (Fin k → FiniteSumRoundNoise n m b0 Ξ) ×
      FiniteSumRoundNoise n m b0 Ξ => roundNoise i z.2
  letI (t : ℕ) (q : Worker n) : IsProbabilityMeasure (batchLaw t q) :=
    hBatchLaw t q
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hpastBlock : Measurable pastBlock := by
    refine measurable_pi_lambda _ ?_
    intro q
    exact measurable_pi_apply q.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hroundNoise : ∀ q : Worker n, Measurable (roundNoise q) := by
    intro q
    dsimp [roundNoise]
    fun_prop
  have hworkerNoise : ∀ q : Worker n, Measurable (workerNoise q) := by
    intro q
    exact (hroundNoise q).comp hcurrent
  have hZ : Measurable Z := hpastBlock.prodMk hcurrent
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastBlock.aemeasurable
  have hZlaw : Measure.map Z P = prefixLaw.prod roundLaw := by
    simpa [Z, pastBlock, current, prefixLaw, roundLaw, P] using
      finite_sum_prefix_current_round_map_eq_prod A batchLaw hBatchLaw k
  have hround_pair : ProbabilityTheory.IndepFun (roundNoise j) (roundNoise i)
      roundLaw := by
    exact (finiteSumRoundLaw_worker_noise_iIndep
      A batchLaw hBatchLaw k).indepFun (Ne.symm hij)
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (prefixLaw.prod roundLaw) := by
    exact indepFun_prod_left_adjoin_of_indepFun prefixLaw roundLaw
      (roundNoise j) (roundNoise i) (hroundNoise j) (hroundNoise i) hround_pair
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk ((hroundNoise j).comp measurable_snd)
  have hrightProd : Measurable rightProd :=
    (hroundNoise i).comp measurable_snd
  have hpull : ProbabilityTheory.IndepFun joined (workerNoise i) P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hpastBlock.prodMk (hworkerNoise j)).aemeasurable)
      ((hworkerNoise i).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, workerNoise i path)) P =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z P) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleftProd.prodMk hrightProd
            · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (prefixLaw.prod roundLaw)).prod
          (Measure.map rightProd (prefixLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map (workerNoise i) P) := by
        rw [show Measure.map leftProd (prefixLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            Measure.map leftProd (prefixLaw.prod roundLaw) =
                Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (prefixLaw.prod roundLaw) =
            Measure.map (workerNoise i) P by
          calc
            Measure.map rightProd (prefixLaw.prod roundLaw) =
                Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map (workerNoise i) P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  have hstrict_le : finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      MeasurableSpace.comap pastBlock inferInstance := by
    refine iSup_le fun q => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastBlock inferInstance]
        pastBlock := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply q).comp hpast_comap).comap_le
  have hjoined_comap : Measurable[MeasurableSpace.comap joined inferInstance]
      joined := measurable_iff_comap_le.mpr le_rfl
  have hpast_joined : MeasurableSpace.comap pastBlock inferInstance ≤
      MeasurableSpace.comap joined inferInstance :=
    ((measurable_fst.comp hjoined_comap).comap_le)
  have hpeer_joined : MeasurableSpace.comap (workerNoise j) inferInstance ≤
      MeasurableSpace.comap joined inferInstance :=
    ((measurable_snd.comp hjoined_comap).comap_le)
  have hjoined_indep : ProbabilityTheory.Indep
      (MeasurableSpace.comap joined inferInstance)
      (MeasurableSpace.comap (workerNoise i) inferInstance) P := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpull
  have hpast_peer_indep : ProbabilityTheory.Indep
      (finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ⊔
        MeasurableSpace.comap (workerNoise j) inferInstance)
      (MeasurableSpace.comap (workerNoise i) inferInstance) P := by
    apply ProbabilityTheory.indep_of_indep_of_le_left hjoined_indep
    exact sup_le (le_trans hstrict_le hpast_joined) hpeer_joined
  have hquery : Measurable[finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] query := by
    have hs := finiteSumProcess_strictPast_measurable (b0 := b0) A x0 k
    exact ((measurable_primalStep A.stepSize).comp hs).prodMk
      ((measurable_state_x d).comp hs)
  have hresult : ProbabilityTheory.IndepFun
      (fun path => (query path, workerNoise j path)) (workerNoise i) P :=
    indepFun_prod_past_current_of_indep_current hquery hpast_peer_indep
  simpa only [query, workerNoise, P, finiteSumProcess, finiteSumRun_succ,
    finiteSumStep] using hresult

/-- The complete generated strict past is independent of one current worker's
noise coordinate. -/
theorem finite_sum_strictPast_indep_worker_noise
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (k : ℕ) (i : Worker n) :
    ProbabilityTheory.Indep
      (finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
      (MeasurableSpace.comap
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i)) inferInstance)
      (finiteSumPathLaw A batchLaw) := by
  let P := finiteSumPathLaw A batchLaw
  let pastBlock := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    fun j : Fin k => path j.1
  let current := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k
  let workerNoise := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ((path k).2.1 i, (path k).2.2 i)
  let prefixLaw := Measure.map pastBlock P
  let roundLaw := finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (batchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hpastBlock : Measurable pastBlock := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastBlock.aemeasurable
  have hpast_current : ProbabilityTheory.IndepFun pastBlock current P := by
    refine indepFun_of_map_prod_eq_prod_laws
      (P := P) (Z := fun path => (pastBlock path, current path))
      (mu := prefixLaw) (nu := roundLaw) ?_ ?_
    · exact (hpastBlock.prodMk hcurrent).aemeasurable
    · simpa [P, pastBlock, current, prefixLaw, roundLaw] using
        finite_sum_prefix_current_round_map_eq_prod A batchLaw hBatchLaw k
  have hpast_worker : ProbabilityTheory.IndepFun pastBlock workerNoise P := by
    have h := hpast_current.comp measurable_id
      (show Measurable
        (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i)) by
          fun_prop)
    simpa [current, workerNoise, Function.comp_def] using h
  have hstrict_le : finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      MeasurableSpace.comap pastBlock inferInstance := by
    refine iSup_le fun j => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastBlock inferInstance]
        pastBlock := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hpast_comap).comap_le
  have hcomap : ProbabilityTheory.Indep
      (MeasurableSpace.comap pastBlock inferInstance)
      (MeasurableSpace.comap workerNoise inferInstance) P := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpast_worker
  exact ProbabilityTheory.indep_of_indep_of_le_left hcomap hstrict_le

/-- The nonrefresh residual square is independent of the current refresh coin;
it depends only on the strict past and the non-coin part of the current round. -/
theorem finite_sum_nonrefresh_square_indep_refresh
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ‖(finiteSumProcess (b0 := b0) A x0 k path).g -
            globalGradient (finiteSumLocalProblem A.problem)
              (finiteSumProcess (b0 := b0) A x0 k path).x +
          average (fun i : Worker n =>
            finiteSumWorkerInnovation A x0 k i path)‖ ^ 2)
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).1)
      (finiteSumPathLaw A batchLaw) := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let pastBlock := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    fun j : Fin k => path j.1
  let current := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k
  let rest := fun z : FiniteSumRoundNoise n m b0 Ξ => z.2
  let branchRound := fun z : FiniteSumRoundNoise n m b0 Ξ => z.1
  let restPath := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (path k).2
  let branch := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (path k).1
  let joined := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (pastBlock path, restPath path)
  let Z := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (pastBlock path, current path)
  let prefixLaw := Measure.map pastBlock P
  let restLaw := (finiteSumBatchJointLaw batchLaw k).prod
    (workerCompressionLaw (n := n) A.quantizer)
  let roundLaw := finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)
  let leftProd := fun z : (Fin k → FiniteSumRoundNoise n m b0 Ξ) ×
      FiniteSumRoundNoise n m b0 Ξ => (z.1, rest z.2)
  let rightProd := fun z : (Fin k → FiniteSumRoundNoise n m b0 Ξ) ×
      FiniteSumRoundNoise n m b0 Ξ => branchRound z.2
  let nonrefreshSq := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ‖(finiteSumProcess (b0 := b0) A x0 k path).g -
        globalGradient (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0 k path).x +
      average (fun i : Worker n =>
        finiteSumWorkerInnovation A x0 k i path)‖ ^ 2
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hpastBlock : Measurable pastBlock := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hrest : Measurable rest := measurable_snd
  have hbranchRound : Measurable branchRound := measurable_fst
  have hZ : Measurable Z := hpastBlock.prodMk hcurrent
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastBlock.aemeasurable
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hZlaw : Measure.map Z P = prefixLaw.prod roundLaw := by
    simpa [Z, pastBlock, current, prefixLaw, roundLaw, P] using
      finite_sum_prefix_current_round_map_eq_prod A batchLaw hBatchLaw k
  have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [roundLaw, finiteSumRoundLaw, restLaw, rest, branchRound] using h
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (prefixLaw.prod roundLaw) :=
    indepFun_prod_left_adjoin_of_indepFun prefixLaw roundLaw rest branchRound
      hrest hbranchRound hround
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk (hrest.comp measurable_snd)
  have hrightProd : Measurable rightProd :=
    hbranchRound.comp measurable_snd
  have hpull : ProbabilityTheory.IndepFun joined branch P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hpastBlock.prodMk (hrest.comp hcurrent)).aemeasurable)
      ((hbranchRound.comp hcurrent).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, branch path)) P =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z P) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleftProd.prodMk hrightProd
            · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (prefixLaw.prod roundLaw)).prod
          (Measure.map rightProd (prefixLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map branch P) := by
        rw [show Measure.map leftProd (prefixLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            Measure.map leftProd (prefixLaw.prod roundLaw) =
                Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (prefixLaw.prod roundLaw) =
            Measure.map branch P by
          calc
            Measure.map rightProd (prefixLaw.prod roundLaw) =
                Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map branch P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  have hjoined_comap : Measurable[MeasurableSpace.comap joined inferInstance]
      joined := measurable_iff_comap_le.mpr le_rfl
  have hpast_meas : Measurable[MeasurableSpace.comap joined inferInstance]
      pastBlock := measurable_fst.comp hjoined_comap
  have hrest_meas : Measurable[MeasurableSpace.comap joined inferInstance]
      restPath := by
    have h : Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path => (joined path).2) := measurable_snd.comp hjoined_comap
    simpa [joined, restPath] using h
  have hstrict_le : finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      MeasurableSpace.comap joined inferInstance := by
    refine iSup_le fun j => ?_
    exact ((measurable_pi_apply j).comp hpast_meas).comap_le
  have hstate : Measurable[MeasurableSpace.comap joined inferInstance]
      (finiteSumProcess (b0 := b0) A x0 k) :=
    (finiteSumProcess_strictPast_measurable (b0 := b0) A x0 k).mono
      hstrict_le le_rfl
  have hresidual : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path =>
        (finiteSumProcess (b0 := b0) A x0 k path).g -
          globalGradient (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0 k path).x) :=
    ((measurable_state_g d).comp hstate).sub
      ((measurable_gradient (globalObjective (finiteSumLocalProblem A.problem))).comp
        ((measurable_state_x d).comp hstate))
  have hinnovation : ∀ i : Worker n,
      Measurable[MeasurableSpace.comap joined inferInstance]
        (finiteSumWorkerInnovation A x0 k i) := by
    intro i
    have hnoise : Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i)) := by
      exact (show Measurable
        (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
          (z.1 i, z.2 i)) by fun_prop).comp hrest_meas
    exact (finiteSumWorkerInnovation_measurable_wrt_history A x0 k i).mono
      (sup_le hstrict_le hnoise.comap_le) le_rfl
  have havg : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => average (fun i : Worker n =>
        finiteSumWorkerInnovation A x0 k i path)) := by
    unfold average SOptLib.finiteUniformAverage
    fun_prop
  have hsq : Measurable[MeasurableSpace.comap joined inferInstance]
      nonrefreshSq := by
    have hsum : Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path =>
          ((finiteSumProcess (b0 := b0) A x0 k path).g -
            globalGradient (finiteSumLocalProblem A.problem)
              (finiteSumProcess (b0 := b0) A x0 k path).x) +
          average (fun i : Worker n =>
            finiteSumWorkerInnovation A x0 k i path)) :=
      hresidual.add havg
    have hnorm : Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path => ‖((finiteSumProcess (b0 := b0) A x0 k path).g -
            globalGradient (finiteSumLocalProblem A.problem)
              (finiteSumProcess (b0 := b0) A x0 k path).x) +
          average (fun i : Worker n =>
            finiteSumWorkerInnovation A x0 k i path)‖) :=
      continuous_norm.measurable.comp hsum
    have hpow := hnorm.pow_const 2
    change Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => ‖((finiteSumProcess (b0 := b0) A x0 k path).g -
          globalGradient (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0 k path).x) +
        average (fun i : Worker n =>
          finiteSumWorkerInnovation A x0 k i path)‖ ^ 2)
    exact hpow
  have hjoined_indep : ProbabilityTheory.Indep
      (MeasurableSpace.comap joined inferInstance)
      (MeasurableSpace.comap branch inferInstance) P := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpull
  have h := indepFun_of_measurable_left_of_indep_comap hsq hjoined_indep
  simpa [nonrefreshSq, branch, P] using h

/-- The generated finite-sum process stays in `L²` at every time.  This is
the nonfallback integrability infrastructure needed to interpret Eq. (33). -/
theorem finite_sum_process_l2_invariant
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    ∀ t,
      Integrable (fun path =>
        ‖(finiteSumProcess (b0 := b0) A x0 t path).x - x0‖ ^ 2)
          (finiteSumPathLaw A batchLaw) ∧
      Integrable (fun path =>
        ‖(finiteSumProcess (b0 := b0) A x0 t path).g‖ ^ 2)
          (finiteSumPathLaw A batchLaw) ∧
      EstimatorErrorMomentWellDefined (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) t ∧
      StepMomentWellDefined (finiteSumProcess (b0 := b0) A x0)
        (finiteSumPathLaw A batchLaw) t := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let run := finiteSumProcess (b0 := b0) A x0
  let localP := finiteSumLocalProblem A.problem
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hstate_meas : ∀ t, Measurable (run t) := by
    intro t
    exact (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 t).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) t) le_rfl
  have hx_meas : ∀ t, AEStronglyMeasurable (fun path => (run t path).x) P := by
    intro t
    exact ((measurable_state_x d).comp (hstate_meas t)).aestronglyMeasurable
  have hg_meas : ∀ t, AEStronglyMeasurable (fun path => (run t path).g) P := by
    intro t
    exact ((measurable_state_g d).comp (hstate_meas t)).aestronglyMeasurable
  have hlocal_grad_l2 : ∀ (t : ℕ) (i : Worker n),
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) P →
      Integrable (fun path => ‖localGradient localP i (run t path).x‖ ^ 2) P := by
    intro t i hx
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (localGradient localP i) (Llocal i) (fun path => (run t path).x)
      (hx_meas t)
    · simpa [norm_sub_rev] using hx
    · intro x y
      exact hSmooth.2 i y x
  have hglobal_grad_l2 : ∀ (t : ℕ),
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) P →
      Integrable (fun path => ‖globalGradient localP (run t path).x‖ ^ 2) P := by
    intro t hx
    have hGlobal := GlobalSmoothness_from_Assumption_1_2 localP Llocal hSmooth
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient localP) (rootMeanSquare Llocal)
        (fun path => (run t path).x) (hx_meas t)
    · simpa [norm_sub_rev] using hx
    · intro x y
      exact hGlobal.2 y x
  intro t
  induction t with
  | zero =>
      have hx0 : Integrable (fun path => ‖(run 0 path).x - x0‖ ^ 2) P := by
        have heq : (fun path => ‖(run 0 path).x - x0‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext path
          change ‖x0 - x0‖ ^ 2 = 0
          simp
        rw [heq]
        exact integrable_const (μ := P) (c := (0 : ℝ))
      have hg0 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) P := by
        have heq : (fun path => ‖(run 0 path).g‖ ^ 2) =
            (fun _ => ‖globalGradient localP x0‖ ^ 2) := by
          funext path
          rfl
        rw [heq]
        exact integrable_const (μ := P)
          (c := ‖globalGradient localP x0‖ ^ 2)
      have herr0 : EstimatorErrorMomentWellDefined localP run P 0 := by
        have heq : (fun path =>
              ‖(run 0 path).g - globalGradient localP (run 0 path).x‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext path
          change ‖globalGradient localP x0 - globalGradient localP x0‖ ^ 2 = 0
          simp
        rw [EstimatorErrorMomentWellDefined, heq]
        exact integrable_const (μ := P) (c := (0 : ℝ))
      have hstep0 : StepMomentWellDefined run P 0 := by
        have heq : (fun path => ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
            (fun _ => ‖(-(A.stepSize : ℝ)) • globalGradient localP x0‖ ^ 2) := by
          funext path
          change ‖(x0 - (A.stepSize : ℝ) • globalGradient localP x0) - x0‖ ^ 2 = _
          congr 2
          rw [neg_smul]
          abel
        rw [StepMomentWellDefined, heq]
        exact integrable_const (μ := P)
          (c := ‖(-(A.stepSize : ℝ)) • globalGradient localP x0‖ ^ 2)
      exact ⟨hx0, hg0, herr0, hstep0⟩
  | succ t ih =>
      have hstep : StepMomentWellDefined run P t := ih.2.2.2
      have hx_succ : Integrable
          (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) P := by
        have h := integrable_sq_norm_sub_smul_sub_const_of_l2
          (fun path => (run t path).x) (fun path => (run t path).g)
          x0 (A.stepSize : ℝ) (hx_meas t) (hg_meas t) ih.1 ih.2.1
        simpa [run, finiteSumProcess, finiteSumRun_succ, finiteSumStep,
          primalStep_eq] using h
      have hworker_sq : ∀ i : Worker n, Integrable
          (fun path => ‖finiteSumWorkerEstimator A
            (finiteSumDriverOfNoise (path t)) (run t path) i‖ ^ 2) P := by
        intro i
        let innovation := finiteSumWorkerInnovation (b0 := b0) A x0 t i
        let gradDiff := fun path =>
          localGradientDifference localP i (run (t + 1) path).x (run t path).x
        let carried := fun path =>
          (run t path).g + (innovation path + gradDiff path)
        let refreshed := fun path => localGradient localP i (run (t + 1) path).x
        let s : Set (ℕ → FiniteSumRoundNoise n m b0 Ξ) :=
          {path | (path t).1 = true}
        have hinn := finite_sum_worker_innovation_centered_second_moment
          A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
            hQuantizer t i hstep
        have hgrad_t := hlocal_grad_l2 t i ih.1
        have hgrad_succ := hlocal_grad_l2 (t + 1) i hx_succ
        have hdiff_meas : AEStronglyMeasurable gradDiff P := by
          dsimp [gradDiff, localGradientDifference]
          exact ((measurable_localGradient localP i).comp
            ((measurable_state_x d).comp (hstate_meas (t + 1)))).sub
              ((measurable_localGradient localP i).comp
                ((measurable_state_x d).comp (hstate_meas t))) |>.aestronglyMeasurable
        have hdiff_sq : Integrable (fun path => ‖gradDiff path‖ ^ 2) P := by
          exact integrable_sq_norm_sub
            (((measurable_localGradient localP i).comp
              ((measurable_state_x d).comp (hstate_meas (t + 1)))).aestronglyMeasurable)
            (((measurable_localGradient localP i).comp
              ((measurable_state_x d).comp (hstate_meas t))).aestronglyMeasurable)
            hgrad_succ hgrad_t
        have hinn_meas : AEStronglyMeasurable innovation P := by
          exact finiteSumWorkerInnovation_aestronglyMeasurable A x0 batchLaw t i
        have hcenter_sq : Integrable
            (fun path => ‖innovation path + gradDiff path‖ ^ 2) P :=
          integrable_sq_norm_add hinn_meas hdiff_meas hinn.1 hdiff_sq
        have hcarried_sq : Integrable (fun path => ‖carried path‖ ^ 2) P := by
          exact integrable_sq_norm_add (hg_meas t) (hinn_meas.add hdiff_meas)
            ih.2.1 hcenter_sq
        have hrefreshed_sq : Integrable
            (fun path => ‖refreshed path‖ ^ 2) P := hgrad_succ
        have hs : MeasurableSet s := by
          dsimp [s]
          exact ((measurable_fst.comp (measurable_pi_apply t))
            (measurableSet_singleton true))
        have hpiece := Integrable.piecewise hs
          hrefreshed_sq.integrableOn hcarried_sq.integrableOn
        have heq : s.piecewise
              (fun path => ‖refreshed path‖ ^ 2)
              (fun path => ‖carried path‖ ^ 2) =
            (fun path => ‖finiteSumWorkerEstimator A
              (finiteSumDriverOfNoise (path t)) (run t path) i‖ ^ 2) := by
          funext path
          by_cases hp : (path t).1 = true
          · simp [s, Set.piecewise, hp, refreshed, carried, innovation, gradDiff,
              run, localP, finiteSumWorkerEstimator, finiteSumDriverOfNoise,
              finiteSumDifference, finiteSumBatchDifference,
              finiteSumWorkerBatchDifference, finiteSumWorkerInnovation,
              localGradientDifference,
              finiteSumProcess, finiteSumRun_succ, finiteSumStep, primalStep_eq]
          · simp [s, Set.piecewise, hp, refreshed, carried, innovation, gradDiff,
              run, localP, finiteSumWorkerEstimator, finiteSumDriverOfNoise,
              finiteSumDifference, finiteSumBatchDifference,
              finiteSumWorkerBatchDifference, finiteSumWorkerInnovation,
              localGradientDifference,
              finiteSumProcess, finiteSumRun_succ, finiteSumStep, primalStep_eq]
        rw [← heq]
        exact hpiece
      have hg_succ : Integrable
          (fun path => ‖(run (t + 1) path).g‖ ^ 2) P := by
        apply integrable_sq_norm_centeredMiniBatchAverage P Finset.univ n.1
          (fun i path => finiteSumWorkerEstimator A
            (finiteSumDriverOfNoise (path t)) (run t path) i)
          (fun path => (run (t + 1) path).g)
        · intro i _hi
          exact (finiteSumWorkerEstimator_round_joint_measurable A i).comp
            ((hstate_meas t).prodMk (measurable_pi_apply t)) |>.aestronglyMeasurable
        · intro i _hi
          exact hworker_sq i
        · funext path
          simp [run, finiteSumProcess, finiteSumRun_succ, finiteSumStep,
            average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
      have hgrad_global_succ := hglobal_grad_l2 (t + 1) hx_succ
      have herr_succ : EstimatorErrorMomentWellDefined localP run P (t + 1) := by
        exact integrable_sq_norm_sub (hg_meas (t + 1))
          ((measurable_gradient (globalObjective localP)).comp
            ((measurable_state_x d).comp (hstate_meas (t + 1))) |>.aestronglyMeasurable)
          hg_succ hgrad_global_succ
      have hstep_succ : StepMomentWellDefined run P (t + 1) := by
        have hscaled := integrable_sq_norm_const_smul (-(A.stepSize : ℝ)) hg_succ
        simpa [StepMomentWellDefined, run, finiteSumProcess, finiteSumRun_succ,
          finiteSumStep, primalStep_eq] using hscaled
      exact ⟨hx_succ, hg_succ, herr_succ, hstep_succ⟩

/-- Distinct adaptive worker innovations have zero integrated inner product.
Their shared query is kept on the parameter side of the freshness statement. -/
theorem finite_sum_worker_innovation_cross_integral_eq_zero
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i j : Worker n) (hij : i ≠ j) :
    (∫ path,
      ⟪finiteSumWorkerInnovation A x0 k i path,
        finiteSumWorkerInnovation A x0 k j path⟫_ℝ
      ∂finiteSumPathLaw A batchLaw) = 0 := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let query0 := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ((finiteSumProcess (b0 := b0) A x0 (k + 1) path).x,
      (finiteSumProcess (b0 := b0) A x0 k path).x)
  let Query := Set.range query0
  let query : (ℕ → FiniteSumRoundNoise n m b0 Ξ) → Query := fun path =>
    ⟨query0 path, ⟨path, rfl⟩⟩
  let sample := fun q : Worker n =>
      fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 q, (path k).2.2 q)
  let innovation := fun (q : Worker n) (z : Query)
      (s : FiniteSumWorkerBatch m b0 × Ξ) =>
    A.quantizer.apply
        (finiteSumWorkerBatchDifference A.problem s.1 q z.1.1 z.1.2) s.2 -
      localGradientDifference (finiteSumLocalProblem A.problem) q z.1.1 z.1.2
  let param := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (query path, sample j path)
  let residual := fun w : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
    fun s => innovation i w.1 s
  let direction := fun w : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
    innovation j w.1 w.2
  let ν := (batchLaw k i).prod A.quantizer.law
  letI (t : ℕ) (q : Worker n) : IsProbabilityMeasure (batchLaw t q) :=
    hBatchLaw t q
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hquery0 : Measurable query0 := by
    have hk := (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
    have hks := (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 (k + 1)).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) (k + 1)) le_rfl
    exact ((measurable_state_x d).comp hks).prodMk
      ((measurable_state_x d).comp hk)
  have hquery : Measurable query := Measurable.subtype_mk hquery0
  have hsample : ∀ q : Worker n, Measurable (sample q) := by
    intro q
    dsimp [sample]
    fun_prop
  have hinnovation : ∀ q : Worker n,
      Measurable (Function.uncurry (innovation q)) := by
    intro q
    have hpair : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          ((p.1.1, p.2.1) : (Point d × Point d) × FiniteSumWorkerBatch m b0)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)
    have hdiff : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          finiteSumWorkerBatchDifference A.problem p.2.1 q p.1.1.1 p.1.1.2) := by
      simpa only [Function.comp_apply] using
        (finiteSumWorkerBatchDifference_joint_measurable
          (b0 := b0) A.problem q).comp hpair
    have hquantized : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          A.quantizer.apply
            (finiteSumWorkerBatchDifference A.problem p.2.1 q p.1.1.1 p.1.1.2)
            p.2.2) :=
      A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk (measurable_snd.comp measurable_snd))
    have hmean : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          localGradientDifference (finiteSumLocalProblem A.problem) q
            p.1.1.1 p.1.1.2) := by
      unfold localGradientDifference
      exact ((measurable_localGradient (finiteSumLocalProblem A.problem) q).comp
        (measurable_fst.comp (measurable_subtype_coe.comp measurable_fst))).sub
        ((measurable_localGradient (finiteSumLocalProblem A.problem) q).comp
          (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst)))
    simpa [innovation, Function.uncurry] using hquantized.sub hmean
  have hparam : Measurable param := hquery.prodMk (hsample j)
  have hraw_indep : ProbabilityTheory.IndepFun
      (fun path => (query0 path, sample j path)) (sample i) P := by
    simpa [query0, sample, P] using
      finite_sum_query_peer_noise_indep_worker_noise
        A x0 batchLaw hBatchLaw k i j hij
  have hindep : ProbabilityTheory.IndepFun param (sample i) P := by
    let raw := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
      (query0 path, sample j path)
    have hraw_comap : Measurable[MeasurableSpace.comap raw inferInstance] raw :=
      measurable_iff_comap_le.mpr le_rfl
    have hparam_comap : Measurable[MeasurableSpace.comap raw inferInstance]
        param := by
      have hq : Measurable[MeasurableSpace.comap raw inferInstance] query :=
        Measurable.subtype_mk (measurable_fst.comp hraw_comap)
      exact hq.prodMk (measurable_snd.comp hraw_comap)
    have hraw_sigma : ProbabilityTheory.Indep
        (MeasurableSpace.comap raw inferInstance)
        (MeasurableSpace.comap (sample i) inferInstance) P := by
      simpa [raw, ProbabilityTheory.IndepFun_iff_Indep] using hraw_indep
    exact indepFun_of_measurable_left_of_indep_comap hparam_comap hraw_sigma
  have hdist : Measure.map (sample i) P = ν := by
    simpa [sample, P, ν] using
      finite_sum_path_worker_noise_map_eq_prod A batchLaw hBatchLaw k i
  have hresidual : Measurable
      (fun p : (Query × (FiniteSumWorkerBatch m b0 × Ξ)) ×
          (FiniteSumWorkerBatch m b0 × Ξ) => residual p.1 p.2) := by
    have harg : Measurable
        (fun p : (Query × (FiniteSumWorkerBatch m b0 × Ξ)) ×
            (FiniteSumWorkerBatch m b0 × Ξ) => (p.1.1, p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h := (hinnovation i).comp harg
    simpa only [residual] using h
  have hdirection : Measurable direction := by
    have harg : Measurable
        (fun w : Query × (FiniteSumWorkerBatch m b0 × Ξ) => (w.1, w.2)) :=
      measurable_fst.prodMk measurable_snd
    have h := (hinnovation j).comp harg
    simpa only [direction] using h
  have hfixed : ∀ w : Query × (FiniteSumWorkerBatch m b0 × Ξ),
      Integrable (residual w) ν ∧ ∫ s, residual w s ∂ν = 0 := by
    intro w
    rcases w with ⟨⟨z, hz⟩, ws⟩
    rcases hz with ⟨path, rfl⟩
    have hworker := finite_sum_fixed_worker_innovation_centered_second_moment
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i path
    have hmeas : AEStronglyMeasurable
        (residual ⟨⟨query0 path, ⟨path, rfl⟩⟩, ws⟩) ν := by
      exact ((hinnovation i).comp (measurable_const.prodMk measurable_id))
        |>.aestronglyMeasurable
    constructor
    · apply integrable_of_integrable_norm_sq hmeas
      simpa [residual, innovation, ν, query0] using hworker.1
    · simpa [residual, innovation, ν, query0] using hworker.2.1
  have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
    P ν param (sample i) residual direction hresidual hdirection hparam
      (hsample i) hindep hdist (fun w => (hfixed w).1) (fun w => (hfixed w).2)
  simpa [P, param, query, query0, sample, residual, direction, innovation,
    finiteSumWorkerInnovation, real_inner_comm] using hzero

/-- The previous estimator residual is orthogonal to each centered current
worker innovation. -/
theorem finite_sum_estimator_residual_worker_innovation_cross_eq_zero
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    (∫ path,
      ⟪ (finiteSumProcess (b0 := b0) A x0 k path).g -
          globalGradient (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0 k path).x,
        finiteSumWorkerInnovation A x0 k i path ⟫_ℝ
      ∂finiteSumPathLaw A batchLaw) = 0 := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let query0 := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (finiteSumProcess (b0 := b0) A x0 k path,
      primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path))
  let Query := Set.range query0
  let query : (ℕ → FiniteSumRoundNoise n m b0 Ξ) → Query := fun path =>
    ⟨query0 path, ⟨path, rfl⟩⟩
  let sample := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ((path k).2.1 i, (path k).2.2 i)
  let innovation := fun (z : Query) (s : FiniteSumWorkerBatch m b0 × Ξ) =>
    A.quantizer.apply
        (finiteSumWorkerBatchDifference A.problem s.1 i z.1.2 z.1.1.x) s.2 -
      localGradientDifference (finiteSumLocalProblem A.problem) i z.1.2 z.1.1.x
  let direction := fun z : Query =>
    z.1.1.g - globalGradient (finiteSumLocalProblem A.problem) z.1.1.x
  let ν := (batchLaw k i).prod A.quantizer.law
  letI (t : ℕ) (q : Worker n) : IsProbabilityMeasure (batchLaw t q) :=
    hBatchLaw t q
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hquery0_past : Measurable[finiteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] query0 := by
    have hs := finiteSumProcess_strictPast_measurable (b0 := b0) A x0 k
    exact hs.prodMk ((measurable_primalStep A.stepSize).comp hs)
  have hquery0 : Measurable query0 :=
    hquery0_past.mono
      (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
  have hquery : Measurable query := Measurable.subtype_mk hquery0
  have hsample : Measurable sample := by
    dsimp [sample]
    fun_prop
  have hindep0 : ProbabilityTheory.IndepFun query0 sample P :=
    indepFun_of_measurable_left_of_indep_comap hquery0_past
      (by simpa [P, sample] using
        finite_sum_strictPast_indep_worker_noise A batchLaw hBatchLaw k i)
  have hindep : ProbabilityTheory.IndepFun query sample P := by
    have hquery_comap : Measurable[MeasurableSpace.comap query0 inferInstance]
        query := Measurable.subtype_mk (measurable_iff_comap_le.mpr le_rfl)
    have hsigma : ProbabilityTheory.Indep
        (MeasurableSpace.comap query0 inferInstance)
        (MeasurableSpace.comap sample inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hindep0
    exact indepFun_of_measurable_left_of_indep_comap hquery_comap hsigma
  have hdist : Measure.map sample P = ν := by
    simpa [sample, P, ν] using
      finite_sum_path_worker_noise_map_eq_prod A batchLaw hBatchLaw k i
  have hinnovation : Measurable (Function.uncurry innovation) := by
    have hpair : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          (((p.1.1.2, p.1.1.1.x), p.2.1) :
            (Point d × Point d) × FiniteSumWorkerBatch m b0)) :=
      ((measurable_snd.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
        ((measurable_state_x d).comp
          (measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)))).prodMk
            (measurable_fst.comp measurable_snd)
    have hdiff : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          finiteSumWorkerBatchDifference A.problem p.2.1 i p.1.1.2 p.1.1.1.x) := by
      simpa only [Function.comp_apply] using
        (finiteSumWorkerBatchDifference_joint_measurable
          (b0 := b0) A.problem i).comp hpair
    have hquantized := A.quantizer.measurable_apply_uncurry.comp
      (hdiff.prodMk (measurable_snd.comp measurable_snd))
    have hmean : Measurable
        (fun p : Query × (FiniteSumWorkerBatch m b0 × Ξ) =>
          localGradientDifference (finiteSumLocalProblem A.problem) i
            p.1.1.2 p.1.1.1.x) := by
      unfold localGradientDifference
      exact ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp
        (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst))).sub
        ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp
          ((measurable_state_x d).comp
            (measurable_fst.comp (measurable_subtype_coe.comp measurable_fst))))
    simpa [innovation, Function.uncurry] using hquantized.sub hmean
  have hdirection : Measurable direction := by
    have hs : Measurable (fun z : Query => z.1.1) :=
      measurable_fst.comp measurable_subtype_coe
    exact ((measurable_state_g d).comp hs).sub
      ((measurable_gradient (globalObjective (finiteSumLocalProblem A.problem))).comp
        ((measurable_state_x d).comp hs))
  have hfixed : ∀ z : Query,
      Integrable (innovation z) ν ∧ ∫ s, innovation z s ∂ν = 0 := by
    intro z
    rcases z with ⟨z, ⟨path, rfl⟩⟩
    have hworker := finite_sum_fixed_worker_innovation_centered_second_moment
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i path
    have hmeas : AEStronglyMeasurable
        (innovation ⟨query0 path, ⟨path, rfl⟩⟩) ν :=
      (hinnovation.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    constructor
    · apply integrable_of_integrable_norm_sq hmeas
      simpa [innovation, ν, query0, finiteSumProcess, finiteSumRun_succ,
        finiteSumStep] using hworker.1
    · simpa [innovation, ν, query0, finiteSumProcess, finiteSumRun_succ,
        finiteSumStep] using hworker.2.1
  have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
    P ν query sample innovation direction hinnovation hdirection hquery hsample
      hindep hdist (fun z => (hfixed z).1) (fun z => (hfixed z).2)
  simpa [P, query, query0, sample, innovation, direction,
    finiteSumWorkerInnovation, finiteSumProcess, finiteSumRun_succ,
    finiteSumStep] using hzero

/-- The average of the centered worker innovations has the exact `1 / n`
second-moment factor from covariance diagonalization. -/
theorem finite_sum_worker_average_second_moment_le
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ)
    (hStep : StepMomentWellDefined (finiteSumProcess (b0 := b0) A x0)
      (finiteSumPathLaw A batchLaw) k) :
    Integrable
        (fun path => ‖average (fun i : Worker n =>
          finiteSumWorkerInnovation A x0 k i path)‖ ^ 2)
        (finiteSumPathLaw A batchLaw) ∧
      (∫ path, ‖average (fun i : Worker n =>
          finiteSumWorkerInnovation A x0 k i path)‖ ^ 2
          ∂finiteSumPathLaw A batchLaw) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k := by
  classical
  let P := finiteSumPathLaw A batchLaw
  let eps := fun i : Worker n =>
    finiteSumWorkerInnovation (b0 := b0) A x0 k i
  let step := stepMoment (finiteSumProcess (b0 := b0) A x0) P k
  have hdiag : ∀ i : Worker n,
      Integrable (fun path => ‖eps i path‖ ^ 2) P ∧
        (∫ path, ‖eps i path‖ ^ 2 ∂P) ≤
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            step := by
    intro i
    have h := finite_sum_worker_innovation_centered_second_moment
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i hStep
    exact ⟨h.1, h.2.2⟩
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (eps i) P := by
    intro i
    exact finiteSumWorkerInnovation_aestronglyMeasurable A x0 batchLaw k i
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ path, ⟪ eps i path, eps j path ⟫_ℝ ∂P) = 0 := by
    intro i j hij
    exact finite_sum_worker_innovation_cross_integral_eq_zero
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i j hij
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    P (Finset.univ : Finset (Worker n)) eps
      (fun i _ => hmeas i) (fun i _ => (hdiag i).1)
      (fun i _ j _ hij => hcross hij)
  have havg_int : Integrable
      (fun path => ‖average (fun i : Worker n => eps i path)‖ ^ 2) P := by
    apply integrable_sq_norm_centeredMiniBatchAverage P
      (Finset.univ : Finset (Worker n)) n.1 eps
      (fun path => average (fun i : Worker n => eps i path))
    · intro i _hi
      exact hmeas i
    · intro i _hi
      exact (hdiag i).1
    · funext path
      simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
  refine ⟨by simpa [eps, P] using havg_int, ?_⟩
  have hcoeff_sum :
      (∑ i : Worker n,
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1)) =
      ω * ∑ i : Worker n, (Llocal i) ^ 2 +
        ((1 + ω) / b0.1) * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    calc
      _ = (∑ i : Worker n, ω * (Llocal i) ^ 2) +
          ∑ i : Worker n, ((1 + ω) / b0.1) * (ℒlocal i) ^ 2 := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have hmean_L : 0 ≤ meanSquare Llocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hmean_A : 0 ≤ meanSquare ℒlocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hrms_L : (rootMeanSquare Llocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (Llocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_L]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hrms_A : (rootMeanSquare ℒlocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_A]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  have hb : (b0.1 : ℝ) ≠ 0 := by exact_mod_cast b0.2.ne'
  calc
    (∫ path, ‖average (fun i : Worker n =>
        finiteSumWorkerInnovation A x0 k i path)‖ ^ 2 ∂finiteSumPathLaw A batchLaw) =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ∫ path, ‖Finset.sum Finset.univ (fun i => eps i path)‖ ^ 2 ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with path
      change ‖average (fun i : Worker n => eps i path)‖ ^ 2 = _
      unfold average SOptLib.finiteUniformAverage
      simp only [Fintype.card_fin]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n, ∫ path, ‖eps i path‖ ^ 2 ∂P := by rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n,
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            step := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) * step := by
      rw [← Finset.sum_mul, hcoeff_sum, hrms_L, hrms_A]
      field_simp [hn, hb]

/-- `book/MARINA/MARINA.json#/key_lemmas/6`, Eq. (33). -/
theorem finite_sum_estimator_recurrence_33
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ) :
    EstimatorErrorMomentWellDefined (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) (k + 1) ∧
    EstimatorErrorMomentWellDefined (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) k ∧
    StepMomentWellDefined (finiteSumProcess (b0 := b0) A x0)
        (finiteSumPathLaw A batchLaw) k ∧
    estimatorErrorMoment (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) k := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.property⟩⟩
  have hL2 := finite_sum_process_l2_invariant
    A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth hQuantizer
  have hL2k := hL2 k
  have hL2succ := hL2 (k + 1)
  have hWorkerMoment : ∀ i : Worker n,
      Integrable (fun path => ‖finiteSumWorkerInnovation A x0 k i path‖ ^ 2)
          (finiteSumPathLaw A batchLaw) ∧
        (∫ path, finiteSumWorkerInnovation A x0 k i path
            ∂finiteSumPathLaw A batchLaw) = 0 ∧
        (∫ path, ‖finiteSumWorkerInnovation A x0 k i path‖ ^ 2
            ∂finiteSumPathLaw A batchLaw) ≤
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            stepMoment (finiteSumProcess (b0 := b0) A x0)
              (finiteSumPathLaw A batchLaw) k := by
    intro i
    exact finite_sum_worker_innovation_centered_second_moment
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i hL2k.2.2.2
  have hWorkerCross : ∀ {i j : Worker n}, i ≠ j →
      (∫ path,
        ⟪finiteSumWorkerInnovation A x0 k i path,
          finiteSumWorkerInnovation A x0 k j path⟫_ℝ
        ∂finiteSumPathLaw A batchLaw) = 0 := by
    intro i j hij
    exact finite_sum_worker_innovation_cross_integral_eq_zero
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i j hij
  have hWorkerAverage := finite_sum_worker_average_second_moment_le
    A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
      hQuantizer k hL2k.2.2.2
  let residual := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (finiteSumProcess (b0 := b0) A x0 k path).g -
      globalGradient (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0 k path).x
  let innovation := fun i : Worker n => finiteSumWorkerInnovation
    (b0 := b0) A x0 k i
  have hstateK : Measurable (finiteSumProcess (b0 := b0) A x0 k) :=
    (finiteSumProcess_strictPast_measurable (b0 := b0) A x0 k).mono
      (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
  have hresidual_meas : AEStronglyMeasurable residual
      (finiteSumPathLaw A batchLaw) := by
    exact (((measurable_state_g d).comp hstateK).sub
      ((measurable_gradient (globalObjective (finiteSumLocalProblem A.problem))).comp
        ((measurable_state_x d).comp hstateK))).aestronglyMeasurable
  have hresidual_sq : Integrable (fun path => ‖residual path‖ ^ 2)
      (finiteSumPathLaw A batchLaw) := by
    simpa [residual, EstimatorErrorMomentWellDefined] using hL2k.2.2.1
  have hResidualWorkerCross : ∀ i : Worker n,
      (∫ path, ⟪ residual path, innovation i path ⟫_ℝ
        ∂finiteSumPathLaw A batchLaw) = 0 := by
    intro i
    simpa [residual, innovation] using
      finite_sum_estimator_residual_worker_innovation_cross_eq_zero
        A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k i
  have hResidualAverageCross :
      (∫ path, ⟪ residual path,
          average (fun i : Worker n => innovation i path) ⟫_ℝ
        ∂finiteSumPathLaw A batchLaw) = 0 := by
    have h := pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
      (finiteSumPathLaw A batchLaw) (Finset.univ : Finset (Worker n)) n.1
      residual innovation hresidual_meas
      (fun i _ =>
        finiteSumWorkerInnovation_aestronglyMeasurable A x0 batchLaw k i)
      hresidual_sq (fun i _ => (hWorkerMoment i).1)
      (fun i _ => hResidualWorkerCross i)
    simpa [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin] using h
  let avgInnovation := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    average (fun i : Worker n => innovation i path)
  have havg_meas : AEStronglyMeasurable avgInnovation
      (finiteSumPathLaw A batchLaw) := by
    dsimp [avgInnovation]
    unfold average SOptLib.finiteUniformAverage
    have h := (Finset.aestronglyMeasurable_sum (s := Finset.univ)
      (fun i _ => finiteSumWorkerInnovation_aestronglyMeasurable
        A x0 batchLaw k i)).const_smul
          ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro path
    simp [innovation, Finset.sum_apply]
  have havg_sq : Integrable (fun path => ‖avgInnovation path‖ ^ 2)
      (finiteSumPathLaw A batchLaw) := by
    simpa [avgInnovation, innovation] using hWorkerAverage.1
  have hnonrefresh_sq : Integrable
      (fun path => ‖residual path + avgInnovation path‖ ^ 2)
      (finiteSumPathLaw A batchLaw) :=
    integrable_sq_norm_add hresidual_meas havg_meas hresidual_sq havg_sq
  have hnonrefresh_eq :
      (∫ path, ‖residual path + avgInnovation path‖ ^ 2
        ∂finiteSumPathLaw A batchLaw) =
      (∫ path, ‖residual path‖ ^ 2 ∂finiteSumPathLaw A batchLaw) +
        ∫ path, ‖avgInnovation path‖ ^ 2
          ∂finiteSumPathLaw A batchLaw := by
    let pair : Bool → (ℕ → FiniteSumRoundNoise n m b0 Ξ) → Point d :=
      fun b => if b then avgInnovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      (finiteSumPathLaw A batchLaw) (Finset.univ : Finset Bool) pair
      (fun b _ => by cases b <;> simp [pair, hresidual_meas, havg_meas])
      (fun b _ => by cases b <;> simp [pair, hresidual_sq, havg_sq])
      (fun a _ b _ hab => by
        cases a <;> cases b
        · exact False.elim (hab rfl)
        · simpa [pair] using hResidualAverageCross
        · simpa [pair, real_inner_comm] using hResidualAverageCross
        · exact False.elim (hab rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  have hnonrefresh_bound :
      (∫ path, ‖residual path + avgInnovation path‖ ^ 2
        ∂finiteSumPathLaw A batchLaw) ≤
      estimatorErrorMoment (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0)
          (finiteSumPathLaw A batchLaw) k +
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k := by
    rw [hnonrefresh_eq]
    change estimatorErrorMoment (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) k +
        (∫ path, ‖avgInnovation path‖ ^ 2 ∂finiteSumPathLaw A batchLaw) ≤ _
    have havg_bound :
        (∫ path, ‖avgInnovation path‖ ^ 2 ∂finiteSumPathLaw A batchLaw) ≤
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment (finiteSumProcess (b0 := b0) A x0)
              (finiteSumPathLaw A batchLaw) k := by
      simpa [avgInnovation, innovation] using hWorkerAverage.2
    exact add_le_add_right havg_bound _
  let branch := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).1
  let nextResidual := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (finiteSumProcess (b0 := b0) A x0 (k + 1) path).g -
      globalGradient (finiteSumLocalProblem A.problem)
        (finiteSumProcess (b0 := b0) A x0 (k + 1) path).x
  have hbranch_decomp : ∀ path,
      nextResidual path = if branch path then 0
        else residual path + avgInnovation path := by
    intro path
    let s := finiteSumProcess (b0 := b0) A x0 k path
    let xNext := primalStep A.stepSize s
    let q := fun i : Worker n =>
      A.quantizer.apply
        (finiteSumWorkerBatchDifference A.problem ((path k).2.1 i) i xNext s.x)
        ((path k).2.2 i)
    have hgradAvg : average (fun i : Worker n =>
        localGradient (finiteSumLocalProblem A.problem) i xNext) =
        globalGradient (finiteSumLocalProblem A.problem) xNext := by
      simpa [averageLocalGradient] using
        (globalGradient_eq_averageLocalGradient
          (finiteSumLocalProblem A.problem) hSmooth.1 xNext).symm
    have hdiffAvg : average (fun i : Worker n =>
        localGradientDifference (finiteSumLocalProblem A.problem) i xNext s.x) =
        globalGradient (finiteSumLocalProblem A.problem) xNext -
          globalGradient (finiteSumLocalProblem A.problem) s.x := by
      rw [globalGradient_eq_averageLocalGradient
          (finiteSumLocalProblem A.problem) hSmooth.1 xNext,
        globalGradient_eq_averageLocalGradient
          (finiteSumLocalProblem A.problem) hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : avgInnovation path =
        average q - average (fun i : Worker n =>
          localGradientDifference (finiteSumLocalProblem A.problem) i xNext s.x) := by
      dsimp [avgInnovation, innovation, finiteSumWorkerInnovation, q, xNext, s]
      unfold average SOptLib.finiteUniformAverage finiteSumWorkerBatchDifference
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n =>
          finiteSumWorkerEstimator A (finiteSumDriverOfNoise (path k)) s i) -
          globalGradient (finiteSumLocalProblem A.problem) xNext := by
      rfl
    cases h : (path k).1 with
    | false =>
        simp only [branch, h, Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [finiteSumWorkerEstimator, finiteSumDriverOfNoise, h, if_false]
        change average (fun i : Worker n => s.g + q i) -
            globalGradient (finiteSumLocalProblem A.problem) xNext =
          residual path + avgInnovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [branch, h, if_true]
        rw [hnext]
        simp only [finiteSumWorkerEstimator, finiteSumDriverOfNoise, h, if_true]
        change average (fun i : Worker n =>
            localGradient (finiteSumLocalProblem A.problem) i xNext) -
            globalGradient (finiteSumLocalProblem A.problem) xNext = 0
        rw [hgradAvg]
        simp
  let nonrefreshSq := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    ‖residual path + avgInnovation path‖ ^ 2
  have hrefresh_indep : ProbabilityTheory.IndepFun nonrefreshSq branch
      (finiteSumPathLaw A batchLaw) := by
    simpa [nonrefreshSq, branch, residual, avgInnovation, innovation] using
      finite_sum_nonrefresh_square_indep_refresh A x0 batchLaw hBatchLaw k
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure (finiteSumPathLaw A batchLaw) := by
    unfold finiteSumPathLaw
    infer_instance
  have hbranch_meas : Measurable branch := by
    dsimp [branch]
    fun_prop
  have hnonrefresh_meas : Measurable nonrefreshSq := by
    dsimp [nonrefreshSq]
    have hresidual : Measurable residual := by
      exact ((measurable_state_g d).comp hstateK).sub
        ((measurable_gradient
          (globalObjective (finiteSumLocalProblem A.problem))).comp
          ((measurable_state_x d).comp hstateK))
    have hinnovation : ∀ i : Worker n, Measurable (innovation i) := by
      intro i
      have hcurrent : Measurable
          (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
            ((path k).2.1 i, (path k).2.2 i)) := by fun_prop
      exact (finiteSumWorkerInnovation_measurable_wrt_history A x0 k i).mono
        (sup_le
          (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
          hcurrent.comap_le) le_rfl
    have havg : Measurable avgInnovation := by
      dsimp [avgInnovation]
      unfold average SOptLib.finiteUniformAverage
      exact (Finset.measurable_sum Finset.univ (fun i _ =>
        hinnovation i)).const_smul ((Fintype.card (Worker n) : ℝ)⁻¹)
    exact (hresidual.add havg).norm.pow_const 2
  have hbranch_law : Measure.map branch (finiteSumPathLaw A batchLaw) =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch (finiteSumPathLaw A batchLaw) =
          Measure.map Prod.fst
            (Measure.map (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
              path k) (finiteSumPathLaw A batchLaw)) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact measurable_fst
            · exact measurable_pi_apply k
      _ = Measure.map Prod.fst
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
            rw [finiteSumPathLaw_round_marginal A batchLaw hBatchLaw k]
      _ = refreshLaw A.refreshProbability A.refresh_admissible := by
            simp [finiteSumRoundLaw]
  have hfalse_mass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real ({false} : Set Bool) =
        1 - A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
    simp only [PMF.bernoulli_apply, Bool.cond_false]
    let pNN : NNReal :=
      ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
    have hpNN : pNN ≤ (1 : NNReal) := by
      exact_mod_cast A.refresh_admissible.2
    change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
    rw [NNReal.coe_sub hpNN]
    rfl
  let phi : ℝ → Bool → ℝ := fun z b => if b = false then z else 0
  let budget : ℝ → ℝ := fun z => (1 - A.refreshProbability) * z
  have hphi : Measurable (Function.uncurry phi) := by
    dsimp [phi, Function.uncurry]
    apply Measurable.ite
    · exact measurable_snd (measurableSet_singleton false)
    · exact measurable_fst
    · exact measurable_const
  have hbudget : Measurable budget := by
    dsimp [budget]
    fun_prop
  have hgate_int : Integrable
      (fun path => phi (nonrefreshSq path) (branch path))
      (finiteSumPathLaw A batchLaw) := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranch_meas (measurableSet_singleton false)
    have hpiece := Integrable.piecewise hs
      hnonrefresh_sq.integrableOn (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phi, Set.piecewise] using hpiece
  have hbudget_int : Integrable (fun path => budget (nonrefreshSq path))
      (finiteSumPathLaw A batchLaw) := by
    simpa [budget, nonrefreshSq] using
      hnonrefresh_sq.const_mul (1 - A.refreshProbability)
  have hfixed : ∀ z : ℝ,
      (∫ b, phi z b ∂refreshLaw A.refreshProbability A.refresh_admissible) ≤
        budget z := by
    intro z
    rw [MeasureTheory.integral_fintype]
    · simp [Fintype.sum_bool, phi, budget, hfalse_mass]
    · exact Integrable.of_finite
  have hgate := integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound
    hphi hbudget hnonrefresh_meas hbranch_meas hrefresh_indep hbranch_law
      hgate_int hbudget_int hfixed
  have hnext_gate :
      estimatorErrorMoment (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0)
          (finiteSumPathLaw A batchLaw) (k + 1) =
        ∫ path, phi (nonrefreshSq path) (branch path)
          ∂finiteSumPathLaw A batchLaw := by
    apply integral_congr_ae
    filter_upwards [] with path
    rw [show
      (finiteSumProcess (b0 := b0) A x0 (k + 1) path).g -
          globalGradient (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0 (k + 1) path).x =
        nextResidual path by rfl, hbranch_decomp]
    by_cases hb : branch path
    · simp [hb, phi]
    · simp [hb, phi, nonrefreshSq]
  have hrefresh_bound :
      estimatorErrorMoment (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0)
          (finiteSumPathLaw A batchLaw) (k + 1) ≤
        (1 - A.refreshProbability) *
          (∫ path, nonrefreshSq path ∂finiteSumPathLaw A batchLaw) := by
    rw [hnext_gate]
    calc
      _ ≤ ∫ path, budget (nonrefreshSq path)
          ∂finiteSumPathLaw A batchLaw := hgate
      _ = _ := by simp [budget, integral_const_mul]
  refine ⟨hL2succ.2.2.1, hL2k.2.2.1, hL2k.2.2.2, ?_⟩
  calc
    estimatorErrorMoment (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0)
          (finiteSumPathLaw A batchLaw) (k + 1) ≤
        (1 - A.refreshProbability) *
          (∫ path, nonrefreshSq path ∂finiteSumPathLaw A batchLaw) :=
      hrefresh_bound
    _ ≤ (1 - A.refreshProbability) *
        (estimatorErrorMoment (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k +
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment (finiteSumProcess (b0 := b0) A x0)
              (finiteSumPathLaw A batchLaw) k) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [nonrefreshSq] using hnonrefresh_bound
      · exact sub_nonneg.mpr A.refresh_admissible.2
    _ = (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0)
            (finiteSumPathLaw A batchLaw) k := by
      ring

/-- One worker's difference minibatch and compressor coordinate have exactly
the product law used by the fixed-worker nonrefresh calculation. -/
theorem onlineRoundLaw_differenceWorkerNoise_marginal
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (i : Worker n) :
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          (z.2.1.2 i, z.2.2 i))
        (onlineRoundLaw A) =
      (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
        A.quantizer.law := by
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  let batches :=
    (onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)
  let compressions := workerCompressionLaw (n := n) A.quantizer
  have hsnd : Measure.map Prod.snd (onlineRoundLaw A) =
      batches.prod compressions := by
    unfold onlineRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  have hbatch : Measure.map
      (fun q : ((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w) => q.2 i)
      batches = Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i) := by
    calc
      Measure.map
          (fun q : ((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w) => q.2 i)
          batches =
          Measure.map
            (fun row : (w : Worker n) → Fin b0.1 → Sample w => row i)
            (Measure.map Prod.snd batches) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_pi_apply i
              · exact measurable_snd
      _ = Measure.map
          (fun row : (w : Worker n) → Fin b0.1 → Sample w => row i)
          (onlineBatchLaw A.problem b0) := by
            simp [batches]
      _ = _ := onlineBatchLaw_worker_marginal A.problem i
  have hcompression : Measure.map
      (fun q : Worker n → Ξ => q i) compressions = A.quantizer.law := by
    simpa [compressions] using workerCompressionLaw_component_marginal A.quantizer i
  calc
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          (z.2.1.2 i, z.2.2 i))
        (onlineRoundLaw A) =
        Measure.map
          (fun q : (((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ) =>
            (q.1.2 i, q.2 i))
          (Measure.map Prod.snd (onlineRoundLaw A)) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
    _ = Measure.map
          (fun q : (((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ) =>
            (q.1.2 i, q.2 i))
          (batches.prod compressions) := by rw [hsnd]
    _ = (Measure.map
          (fun q : ((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w) => q.2 i) batches).prod
          (Measure.map (fun q : Worker n → Ξ => q i) compressions) := by
            symm
            simpa [Prod.map] using
              (MeasureTheory.Measure.map_prod_map batches compressions
                (by fun_prop : Measurable
                  (fun q : ((w : Worker n) → Fin b.1 → Sample w) ×
                    ((w : Worker n) → Fin b0.1 → Sample w) => q.2 i))
                (measurable_pi_apply i))
    _ = _ := by rw [hbatch, hcompression]

/-- A strict online round prefix is independent of one worker's current
difference/compressor coordinate, with the latter's exact product marginal. -/
theorem online_corrected_prefix_indep_differenceWorkerNoise
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) (i : Worker n) :
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let prefMap := onlineRoundPrefix
      (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
    let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      ((path k).2.1.2 i, (path k).2.2 i)
    ProbabilityTheory.IndepFun prefMap noise law ∧
      Measure.map noise law =
        (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
          A.quantizer.law := by
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let prefMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((path k).2.1.2 i, (path k).2.2 i)
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefMap := by
    dsimp [prefMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  haveI : IsProbabilityMeasure prefixLaw := by
    unfold prefixLaw onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun prefMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (prefMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk (measurable_pi_apply k)).aemeasurable
    · simpa [law, prefixLaw, roundLaw, prefMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hindep : ProbabilityTheory.IndepFun prefMap noise law := by
    simpa [noise, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (by fun_prop : Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
            (z.2.1.2 i, z.2.2 i)))
  have hnoiseLaw : Measure.map noise law =
      (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
        A.quantizer.law := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
            (z.2.1.2 i, z.2.2 i)) (Measure.map current law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_pi_apply k
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
            (z.2.1.2 i, z.2.2 i)) roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = _ := onlineRoundLaw_differenceWorkerNoise_marginal A i
  exact ⟨hindep, hnoiseLaw⟩

/-- The generated query pair is independent of each worker's current
difference-minibatch/compressor coordinate.  This is the exact freshness
interface needed to transport the fixed-worker Eq. (46) moment. -/
theorem online_corrected_queryPair_indep_differenceWorkerNoise
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (k : ℕ) (i : Worker n) :
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      ((run (k + 1) path).x, (run k path).x)
    let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      ((path k).2.1.2 i, (path k).2.2 i)
    ProbabilityTheory.IndepFun query noise law ∧
      Measure.map noise law =
        (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
          A.quantizer.law := by
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((path k).2.1.2 i, (path k).2.2 i)
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  haveI : IsProbabilityMeasure prefixLaw := by
    unfold prefixLaw onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineCorrectedPrefixState A hE x0 hBatch fallback k
  let prefixQuery := fun pref =>
    (primalStep A.stepSize (prefixState pref), (prefixState pref).x)
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineCorrectedPrefixState_all_aemeasurable
        A hE x0 hBatch σ hVariance fallback k
  have hprefixQuery : AEMeasurable prefixQuery prefixLaw :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hprefixState).prodMk
      ((measurable_state_x d).comp_aemeasurable hprefixState)
  let queryMk := hprefixQuery.mk prefixQuery
  have hqueryMk : Measurable queryMk := hprefixQuery.measurable_mk
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk (measurable_pi_apply k)).aemeasurable
    · simpa [law, prefixLaw, roundLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hindepMk : ProbabilityTheory.IndepFun
      (queryMk ∘ prefixMap)
      ((fun z : OnlineRoundNoise n b b0 Sample Ξ =>
        (z.2.1.2 i, z.2.2 i)) ∘ current) law :=
    hpastCurrent.comp hqueryMk (by fun_prop)
  have hquery_eq_prefix : ∀ path, query path = prefixQuery (prefixMap path) := by
    intro path
    dsimp [query, prefixQuery, prefixState, run]
    rw [onlineCorrectedProofExactProcess_succ]
    have hs := onlineCorrectedProofExactProcess_congr_prefix
      A hE x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
    rw [hs]
    rfl
  have hprefix_qmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
    ⟨hprefix, by rfl⟩
  have hquery_ae : query =ᵐ[law] queryMk ∘ prefixMap := by
    have hmk := hprefix_qmp.tendsto_ae hprefixQuery.ae_eq_mk
    filter_upwards [hmk] with path hp
    rw [hquery_eq_prefix path, hp]
    rfl
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    apply hindepMk.congr hquery_ae.symm
      (Filter.Eventually.of_forall fun path => by rfl)
  have hnoiseLaw : Measure.map noise law =
      (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
        A.quantizer.law := by
    calc
      Measure.map noise law =
          Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
              (z.2.1.2 i, z.2.2 i))
            (Measure.map current law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_pi_apply k
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
            (z.2.1.2 i, z.2.2 i)) roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = _ := onlineRoundLaw_differenceWorkerNoise_marginal A i
  exact ⟨hindep, hnoiseLaw⟩

/-- The generated corrected query `x^{k+1}` is independent of the fresh
refresh minibatch in round `k`, and that minibatch has the canonical product
law.  The proof uses a measurable modification on the finite prefix law, then
transfers back to the generated query by almost-everywhere equality. -/
theorem online_corrected_query_indep_refreshBatch
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (k : ℕ) :
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (run (k + 1) path).x
    let refreshBatch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (path k).2.1.1
    ProbabilityTheory.IndepFun query refreshBatch law ∧
      Measure.map refreshBatch law = onlineBatchLaw A.problem b := by
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run (k + 1) path).x
  let refreshBatch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (path k).2.1.1
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  haveI : IsProbabilityMeasure prefixLaw := by
    unfold prefixLaw onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineCorrectedPrefixState A hE x0 hBatch fallback k
  let prefixQuery := fun pref => primalStep A.stepSize (prefixState pref)
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineCorrectedPrefixState_all_aemeasurable
        A hE x0 hBatch σ hVariance fallback k
  have hprefixQuery : AEMeasurable prefixQuery prefixLaw :=
    (measurable_primalStep A.stepSize).comp_aemeasurable hprefixState
  let queryMk := hprefixQuery.mk prefixQuery
  have hqueryMk : Measurable queryMk := hprefixQuery.measurable_mk
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk (measurable_pi_apply k)).aemeasurable
    · simpa [law, prefixLaw, roundLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hindepMk : ProbabilityTheory.IndepFun
      (queryMk ∘ prefixMap)
      ((fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) ∘ current) law :=
    hpastCurrent.comp hqueryMk (by fun_prop)
  have hquery_eq_prefix : ∀ path, query path = prefixQuery (prefixMap path) := by
    intro path
    dsimp [query, prefixQuery, prefixState, run]
    rw [onlineCorrectedProofExactProcess_succ]
    apply congrArg (primalStep A.stepSize)
    apply onlineCorrectedProofExactProcess_congr_prefix A hE x0 hBatch k
    intro t ht
    simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht]
  have hprefix_qmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
    ⟨hprefix, by rfl⟩
  have hquery_ae : query =ᵐ[law] queryMk ∘ prefixMap := by
    have hmk := hprefix_qmp.tendsto_ae hprefixQuery.ae_eq_mk
    filter_upwards [hmk] with path hp
    rw [hquery_eq_prefix path, hp]
    rfl
  have hindep : ProbabilityTheory.IndepFun query refreshBatch law := by
    apply hindepMk.congr hquery_ae.symm
      (Filter.Eventually.of_forall fun path => by rfl)
  have hbatchLaw : Measure.map refreshBatch law = onlineBatchLaw A.problem b := by
    calc
      Measure.map refreshBatch law =
          Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
            (Measure.map current law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_pi_apply k
      _ = Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
          roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = onlineBatchLaw A.problem b := by
        simpa [roundLaw] using onlineRoundLaw_refreshBatch_marginal
          (b0 := b0) A
  exact ⟨hindep, hbatchLaw⟩

set_option maxHeartbeats 1600000 in
/-- Complete refresh-branch moment in the corrected Eq. (46) calculation.
The refresh samples are centered at each local gradient before worker
averaging; only after that cancellation is the local-gradient average
identified with the global gradient. -/
theorem online_corrected_refresh_average_second_moment
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (hRegularities : ∀ i : Worker n,
      OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch k i ∧
        OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch k i ∧
        AEMeasurable (onlineCorrectedProofExactProcess A hE x0 hBatch k)
          (onlineProofExactPathLaw (b := b) (b0 := b0) A) ∧
        AEMeasurable (onlineCorrectedProofExactProcess A hE x0 hBatch (k + 1))
          (onlineProofExactPathLaw (b := b) (b0 := b0) A)) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      average (fun i : Worker n => average (fun j : Fin b.1 =>
        stochasticGradient A.problem i ((path k).2.1.1 i j)
          (run (k + 1) path).x)) -
        globalGradient P (run (k + 1) path).x
    Integrable (fun path => ‖refreshError path‖ ^ 2) law ∧
      (∫ path, ‖refreshError path‖ ^ 2 ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) ∧
      ProbabilityTheory.IndepFun
        (fun path => ‖refreshError path‖ ^ 2)
        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path k).1) law := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let query := fun path => (run (k + 1) path).x
  let refreshBatch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (path k).2.1.1
  let batchLaw := onlineBatchLaw A.problem b
  let φ := fun (x : Point d)
      (batch : (i : Worker n) → Fin b.1 → Sample i) =>
    ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
        stochasticGradient A.problem i (batch i j) x)) -
      globalGradient P x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let i0 : Worker n := ⟨0, n.2⟩
  have hquery : AEMeasurable query law := by
    exact (measurable_state_x d).comp_aemeasurable (hRegularities i0).2.2.2
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw = A.problem.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
  have hsampleDiff (i : Worker n) (j : Fin b.1) :
      ∀ᵐ batch ∂batchLaw,
        Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
    let coord := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
        (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop),
        by rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
          simpa [coord] using hcoord i j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleLossInt (i : Worker n) (j : Fin b.1) (x : Point d) :
      Integrable (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        A.problem.sampleLoss i (batch i j) x) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
        simpa [coord] using hcoord i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        stochasticGradient A.problem i (p.2 i j) p.1)
      ((Measure.map query law).prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i (Measure.map query law) batchLaw id (fun batch => batch i j)
      stronglyMeasurable_id.aestronglyMeasurable
      (hsampleDiff i j) (hsampleLossInt i j)
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1))
      ((Measure.map query law).prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1)))
      ((Measure.map query law).prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        globalGradient P p.1)
      ((Measure.map query law).prod batchLaw) :=
    ((measurable_gradient (globalObjective P)).comp measurable_fst).aestronglyMeasurable
  have hφ : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        φ p.1 p.2) ((Measure.map query law).prod batchLaw) := by
    have hv := havg.sub hglobal
    simpa [φ, pow_two] using hv.norm.mul hv.norm
  have hindepLaw := online_corrected_query_indep_refreshBatch
    A hE x0 hBatch σ hVariance k
  have hfixed (x : Point d) :
      Integrable (φ x) batchLaw ∧
        (∫ batch, φ x batch ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [φ, batchLaw, P,
      onlineLocalProblemCorrected_eq_onlineLocalProblem] using
      (online_fixed_refresh_average_second_moment A x σ hVariance hSmooth.1)
  have hrefreshBatch : AEMeasurable refreshBatch law := by
    exact ((measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_pi_apply k))))).aemeasurable
  have hint : Integrable (fun path => φ (query path) (refreshBatch path)) law :=
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := refreshBatch)
      (C := varianceAggregateSq σ / (n.1 * b.1)) hφ hquery
      hrefreshBatch
      hindepLaw.1 hindepLaw.2 (fun _ _ => sq_nonneg _)
      (fun x => (hfixed x).1) (fun x => (hfixed x).2)
  have hbound :
      (∫ path, φ (query path) (refreshBatch path) ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) :=
    integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := refreshBatch)
      hφ hquery hrefreshBatch
      hindepLaw.1 hindepLaw.2 hint (fun x => (hfixed x).2)
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path k).1
  let rest := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2
  let branchRound := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.1
  let restLaw := ((onlineBatchLaw A.problem b).prod
    (onlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let joined := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (prefixMap path, refreshBatch path)
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by rfl
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (prefixMap path, current path))
      (P := law) (mu := prefixLaw)
      (nu := onlineRoundLaw (b := b) (b0 := b0) A)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hroundRest : ProbabilityTheory.IndepFun rest branchRound
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [onlineRoundLaw, restLaw, rest, branchRound] using h
  have hprefixRestBranch : ProbabilityTheory.IndepFun
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ => (z.1, rest z.2))
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ => branchRound z.2)
      (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) :=
    indepFun_prod_left_adjoin_of_indepFun prefixLaw
      (onlineRoundLaw (b := b) (b0 := b0) A) rest branchRound
      measurable_snd measurable_fst hroundRest
  have hpastRestBranch : ProbabilityTheory.IndepFun
      (fun path => (prefixMap path, rest (current path))) branch law := by
    let leftProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ => (z.1, rest z.2)
    let rightProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ => branchRound z.2
    let Z := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (prefixMap path, current path)
    have hleft : Measurable leftProd := by dsimp [leftProd]; fun_prop
    have hright : Measurable rightProd := by dsimp [rightProd]; fun_prop
    have hZ : Measurable Z := hprefix.prodMk hcurrent
    have hmap : Measure.map Z law =
        prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) := by
      simpa [Z, law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hprefix.prodMk ((measurable_snd).comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    calc
      Measure.map
          (fun path => ((prefixMap path, rest (current path)), branch path)) law =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleft.prodMk hright
            · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by rw [← hmap]
      _ = (Measure.map leftProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))).prod
          (Measure.map rightProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleft.aemeasurable hright.aemeasurable).1 hprefixRestBranch
      _ = (Measure.map (fun path => (prefixMap path, rest (current path))) law).prod
          (Measure.map branch law) := by
        rw [show Measure.map leftProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map (fun path => (prefixMap path, rest (current path))) law by
          calc
            _ = Measure.map leftProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hleft hZ]
              congr 1]
        rw [show Measure.map rightProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map branch law by
          calc
            _ = Measure.map rightProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hright hZ]
              congr 1]
  have hjointBranch : ProbabilityTheory.IndepFun joined branch law := by
    have h := hpastRestBranch.comp
      (show Measurable
        (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
            ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) => (z.1, z.2.1.1)) by fun_prop)
      measurable_id
    simpa [joined, refreshBatch, current, rest, branch, Function.comp_def] using h
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineCorrectedPrefixState A hE x0 hBatch fallback k
  let prefixQuery := fun pref => primalStep A.stepSize (prefixState pref)
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineCorrectedPrefixState_all_aemeasurable
        A hE x0 hBatch σ hVariance fallback k
  have hprefixQuery : AEMeasurable prefixQuery prefixLaw :=
    (measurable_primalStep A.stepSize).comp_aemeasurable hprefixState
  let queryRep := hprefixQuery.mk prefixQuery
  have hqueryRep : Measurable queryRep := hprefixQuery.measurable_mk
  have hqueryEq : query =ᵐ[law] queryRep ∘ prefixMap := by
    have hqmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
      ⟨hprefix, by rfl⟩
    have hmk := hqmp.tendsto_ae hprefixQuery.ae_eq_mk
    filter_upwards [hmk] with path hp
    dsimp [query, prefixQuery, prefixState, run]
    rw [onlineCorrectedProofExactProcess_succ]
    have hs := onlineCorrectedProofExactProcess_congr_prefix
      A hE x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by intro t ht; simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
    rw [hs]
    change prefixQuery (prefixMap path) = queryRep (prefixMap path)
    exact hp
  have hqueryRepBatch : ProbabilityTheory.IndepFun
      (queryRep ∘ prefixMap) refreshBatch law := by
    have h := hpastCurrent.comp hqueryRep
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) by fun_prop)
    simpa [refreshBatch, current, Function.comp_def] using h
  have hφRep : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) => φ p.1 p.2)
      ((Measure.map (queryRep ∘ prefixMap) law).prod batchLaw) := by
    rw [← Measure.map_congr hqueryEq]
    exact hφ
  have hrefreshBatchMeas : Measurable refreshBatch := by
    dsimp [refreshBatch]
    fun_prop
  have hjJoined : Measurable joined := by
    dsimp [joined]
    exact hprefix.prodMk hrefreshBatchMeas
  have hqueryTarget : Measurable[MeasurableSpace.comap joined inferInstance]
      (queryRep ∘ prefixMap) := by
    exact hqueryRep.comp (measurable_fst.comp
      (measurable_iff_comap_le.mpr le_rfl))
  have hbatchTarget : Measurable[MeasurableSpace.comap joined inferInstance]
      refreshBatch := by
    exact measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)
  have hφRepMap : AEStronglyMeasurable (Function.uncurry φ)
      ((Measure.map (queryRep ∘ prefixMap) law).prod
        (Measure.map refreshBatch law)) := by
    rw [hindepLaw.2]
    exact hφRep
  obtain ⟨refreshRep, hrefreshRepMeas, hrefreshAe⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (MeasurableSpace.comap joined inferInstance)
      query (queryRep ∘ prefixMap) refreshBatch φ law
      (inferInstance : SigmaFinite (Measure.map (queryRep ∘ prefixMap) law))
      (inferInstance : SigmaFinite (Measure.map refreshBatch law))
      hjJoined.comap_le hqueryTarget hbatchTarget hqueryEq hqueryRepBatch hφRepMap
  have hrepIndep : ProbabilityTheory.IndepFun refreshRep branch law := by
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap joined inferInstance)
        (MeasurableSpace.comap branch inferInstance) law := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hjointBranch
    exact indepFun_of_measurable_left_of_indep_comap
      hrefreshRepMeas.measurable hcomap
  have hrefreshIndep : ProbabilityTheory.IndepFun
      (fun path => ‖(average (fun i : Worker n => average (fun j : Fin b.1 =>
        stochasticGradient A.problem i ((path k).2.1.1 i j)
          (run (k + 1) path).x)) - globalGradient P (run (k + 1) path).x)‖ ^ 2)
      branch law := by
    apply hrepIndep.congr ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hrefreshAe] with path hp
    exact hp.symm
  exact ⟨by simpa [φ, query, refreshBatch, P, run, law] using hint,
    by simpa [φ, query, refreshBatch, P, run, law] using hbound,
    by simpa [branch, P, run, law] using hrefreshIndep⟩

set_option maxHeartbeats 1600000 in
/-- The fixed-query nonrefresh calculation in Eq. (46).  This is the online
counterpart of the finite-sum worker-innovation calculation, but its minibatch
moment inputs are exactly Assumption 3.2. -/
theorem online_corrected_fixed_nonrefresh_worker_moment
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (xNext x : Point d) (i : Worker n) (Llocal ℒlocal : Worker n → ℝ)
    (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hAverageFiber :
      let delta := localGradientDifference
        (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
      let D := fun batch => onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch => ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2 ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let delta := localGradientDifference
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
    let innovation := fun q :
        ((w : Worker n) → Fin b0.1 → Sample w) × Ξ =>
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta
    Integrable innovation
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      Integrable (fun q => ‖innovation q‖ ^ 2)
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      (∫ q, innovation q
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  let delta := localGradientDifference
    (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
  let D := fun batch : (w : Worker n) → Fin b0.1 → Sample w =>
    onlineBatchDifference A.problem batch i xNext x
  let innovation := fun q :
      ((w : Worker n) → Fin b0.1 → Sample w) × Ξ =>
    A.quantizer.apply (D q.1) q.2 - delta
  change Integrable innovation
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      Integrable (fun q => ‖innovation q‖ ^ 2)
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      (∫ q, innovation q
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  rcases hAverageFiber with ⟨hD_int, hD_center_sq, hD_mean, hD_var⟩
  change Integrable D (onlineBatchLaw A.problem b0) at hD_int
  change Integrable (fun batch => ‖D batch - delta‖ ^ 2)
    (onlineBatchLaw A.problem b0) at hD_center_sq
  change (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta at hD_mean
  change (∫ batch, ‖D batch - delta‖ ^ 2
      ∂onlineBatchLaw A.problem b0) ≤
        (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2 at hD_var
  have hinnovation_aesm : AEStronglyMeasurable innovation
      ((onlineBatchLaw A.problem b0).prod A.quantizer.law) := by
    have hDprod : AEStronglyMeasurable
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ => D q.1)
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) :=
      hD_int.aestronglyMeasurable.comp_fst
    have hpair : AEMeasurable
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ =>
          (D q.1, q.2))
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) :=
      hDprod.aemeasurable.prodMk measurable_snd.aemeasurable
    exact (A.quantizer.measurable_apply_uncurry.comp_aemeasurable hpair)
      |>.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hD_sq : Integrable (fun batch => ‖D batch‖ ^ 2)
      (onlineBatchLaw A.problem b0) :=
    oracle_second_moment_integrable_of_centered_second_moment_integrable
      (onlineBatchLaw A.problem b0) D delta hD_int.aestronglyMeasurable
        hD_center_sq
  have hD_second_eq :
      (∫ batch, ‖D batch‖ ^ 2 ∂onlineBatchLaw A.problem b0) =
        (∫ batch, ‖D batch - delta‖ ^ 2 ∂onlineBatchLaw A.problem b0) +
          ‖delta‖ ^ 2 :=
    integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
      (onlineBatchLaw A.problem b0) D delta hD_int hD_center_sq hD_mean
  have hfiber_int : ∀ batch,
      Integrable (fun ξ => ‖innovation (batch, ξ)‖ ^ 2) A.quantizer.law := by
    intro batch
    let v := D batch
    have hnoise_sq : Integrable
        (fun ξ => ‖A.quantizer.apply v ξ - v‖ ^ 2) A.quantizer.law :=
      quantizer_error_sq_integrable hQuantizer v
    have hconst_sq : Integrable
        (fun _ : Ξ => ‖v - delta‖ ^ 2) A.quantizer.law :=
      integrable_const (c := ‖v - delta‖ ^ 2)
    have hnoise_meas : AEStronglyMeasurable
        (fun ξ => A.quantizer.apply v ξ - v) A.quantizer.law :=
      ((hQuantizer.2 v).1.sub (integrable_const (c := v))).aestronglyMeasurable
    have hsum := integrable_sq_norm_add
      hnoise_meas aestronglyMeasurable_const hnoise_sq hconst_sq
    convert hsum using 1
    funext ξ
    congr 2
    simp only [innovation, v]
    abel
  have hfiber_mean : ∀ batch,
      (∫ ξ, innovation (batch, ξ) ∂A.quantizer.law) = D batch - delta := by
    intro batch
    rw [integral_sub (hQuantizer.2 (D batch)).1
      (integrable_const (c := delta))]
    rw [(hQuantizer.2 (D batch)).2.2.1]
    simp [innovation, integral_const, probReal_univ]
  have hfiber_sq_eq : ∀ batch,
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) =
        (∫ ξ, ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := by
    intro batch
    let G := fun ξ => A.quantizer.apply (D batch) ξ - delta
    have hG_int : Integrable G A.quantizer.law :=
      (hQuantizer.2 (D batch)).1.sub (integrable_const (c := delta))
    have hcenter_sq : Integrable
        (fun ξ => ‖G ξ - (D batch - delta)‖ ^ 2) A.quantizer.law := by
      convert (hQuantizer.2 (D batch)).2.1 using 1
      funext ξ
      congr 2
      simp only [G]
      abel
    have hG_mean : (∫ ξ, G ξ ∂A.quantizer.law) = D batch - delta := by
      rw [integral_sub (hQuantizer.2 (D batch)).1
        (integrable_const (c := delta))]
      rw [(hQuantizer.2 (D batch)).2.2.1]
      simp [integral_const, probReal_univ]
    have hdecomp :=
      integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
        A.quantizer.law G (D batch - delta) hG_int hcenter_sq hG_mean
    calc
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) =
          ∫ ξ, ‖G ξ‖ ^ 2 ∂A.quantizer.law := by rfl
      _ = (∫ ξ, ‖G ξ - (D batch - delta)‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := hdecomp
      _ = (∫ ξ, ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := by
            congr 1
            apply integral_congr_ae
            refine Filter.Eventually.of_forall fun ξ => ?_
            have hvec : G ξ - (D batch - delta) =
                A.quantizer.apply (D batch) ξ - D batch := by
              simp only [G]
              abel
            change ‖G ξ - (D batch - delta)‖ ^ 2 =
              ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
            rw [hvec]
  have hfiber_bound : ∀ batch,
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) ≤
        ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2 := by
    intro batch
    rw [hfiber_sq_eq batch]
    exact add_le_add (hQuantizer.2 (D batch)).2.2.2 le_rfl
  have hbudget_int : Integrable
      (fun batch => ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
      (onlineBatchLaw A.problem b0) :=
    (hD_sq.const_mul ω).add hD_center_sq
  have hprod_sq : Integrable (fun q => ‖innovation q‖ ^ 2)
      ((onlineBatchLaw A.problem b0).prod A.quantizer.law) := by
    apply integrable_prod_of_fiber_integral_norm_le_integrable_bound
      (μ := onlineBatchLaw A.problem b0) (ν := A.quantizer.law)
      (φ := fun batch ξ => ‖innovation (batch, ξ)‖ ^ 2)
      (B := fun batch => ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
    · simpa [pow_two] using
        (hinnovation_aesm.norm.mul hinnovation_aesm.norm)
    · exact Filter.Eventually.of_forall hfiber_int
    · exact hbudget_int
    · refine Filter.Eventually.of_forall fun batch => ?_
      calc
        (∫ ξ, ‖‖innovation (batch, ξ)‖ ^ 2‖ ∂A.quantizer.law) =
            ∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ξ =>
                Real.norm_of_nonneg (sq_nonneg _)
        _ ≤ ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2 :=
          hfiber_bound batch
  have hprod_innovation : Integrable innovation
      ((onlineBatchLaw A.problem b0).prod A.quantizer.law) :=
    integrable_of_integrable_norm_sq hinnovation_aesm hprod_sq
  have hprod_mean :
      (∫ q, innovation q
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) = 0 := by
    rw [integral_prod _ hprod_innovation]
    calc
      (∫ batch, ∫ ξ, innovation (batch, ξ) ∂A.quantizer.law
          ∂onlineBatchLaw A.problem b0) =
          ∫ batch, D batch - delta ∂onlineBatchLaw A.problem b0 := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hfiber_mean
      _ = 0 := by
        rw [integral_sub hD_int (integrable_const (c := delta)), hD_mean]
        simp [integral_const, probReal_univ]
  have hdelta_norm : ‖delta‖ ≤ Llocal i * ‖xNext - x‖ := by
    simpa [delta, localGradientDifference] using hSmooth.2 i xNext x
  have hdelta_sq : ‖delta‖ ^ 2 ≤ (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _)
      (le_trans (norm_nonneg _) hdelta_norm)).2 hdelta_norm
  have homega_nonneg : 0 ≤ ω := le_of_lt hQuantizer.1
  have hone_omega_nonneg : 0 ≤ 1 + ω := by linarith
  have hdelta_scaled := mul_le_mul_of_nonneg_left hdelta_sq homega_nonneg
  have hvar_scaled := mul_le_mul_of_nonneg_left hD_var hone_omega_nonneg
  refine ⟨hprod_innovation, hprod_sq, hprod_mean, ?_⟩
  rw [integral_prod _ hprod_sq]
  calc
    (∫ batch, ∫ ξ, ‖innovation (batch, ξ)‖ ^ 2
        ∂A.quantizer.law ∂onlineBatchLaw A.problem b0) ≤
        ∫ batch, (ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
          ∂onlineBatchLaw A.problem b0 := by
            exact integral_mono hprod_sq.integral_prod_left hbudget_int hfiber_bound
    _ = ω * (∫ batch, ‖D batch‖ ^ 2 ∂onlineBatchLaw A.problem b0) +
          ∫ batch, ‖D batch - delta‖ ^ 2
            ∂onlineBatchLaw A.problem b0 := by
            rw [integral_add (hD_sq.const_mul ω) hD_center_sq,
              integral_const_mul]
    _ = ω * ‖delta‖ ^ 2 + (1 + ω) *
          (∫ batch, ‖D batch - delta‖ ^ 2
            ∂onlineBatchLaw A.problem b0) := by
            rw [hD_second_eq]
            ring
    _ ≤ ω * ((Llocal i) ^ 2 * ‖xNext - x‖ ^ 2) +
          (1 + ω) * ((ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2) :=
            add_le_add hdelta_scaled hvar_scaled
    _ = (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by ring

/-- Worker-local form of the fixed nonrefresh moment.  The earlier helper is
stated over the complete difference minibatch; this theorem pushes it through
the canonical worker-row marginal so that distinct workers can subsequently
be separated by the outer product law. -/
theorem online_corrected_fixed_nonrefresh_worker_local_moment
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (xNext x : Point d) (i : Worker n) (Llocal ℒlocal σ : Worker n → ℝ)
    (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hAverageFiber :
      let delta := localGradientDifference
        (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
      let D := fun batch => onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch => ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let rowLaw := Measure.infinitePi
      (fun _ : Fin b0.1 => A.problem.sampleLaw i)
    let delta := localGradientDifference
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
    let innovation := fun q : (Fin b0.1 → Sample i) × Ξ =>
      A.quantizer.apply
        (average (fun j : Fin b0.1 =>
          stochasticGradient A.problem i (q.1 j) xNext -
            stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
    Integrable innovation (rowLaw.prod A.quantizer.law) ∧
      Integrable (fun q => ‖innovation q‖ ^ 2)
        (rowLaw.prod A.quantizer.law) ∧
      (∫ q, innovation q ∂rowLaw.prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw.prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let rowLaw := Measure.infinitePi
    (fun _ : Fin b0.1 => A.problem.sampleLaw i)
  let delta := localGradientDifference
    (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
  let localD := fun row : Fin b0.1 → Sample i =>
    average (fun j : Fin b0.1 =>
      stochasticGradient A.problem i (row j) xNext -
        stochasticGradient A.problem i (row j) x)
  let innovation := fun q : (Fin b0.1 → Sample i) × Ξ =>
    A.quantizer.apply (localD q.1) q.2 - delta
  let fullLaw := (onlineBatchLaw A.problem b0).prod A.quantizer.law
  let project := fun q :
      ((w : Worker n) → Fin b0.1 → Sample w) × Ξ => (q.1 i, q.2)
  change Integrable innovation (rowLaw.prod A.quantizer.law) ∧
      Integrable (fun q => ‖innovation q‖ ^ 2)
        (rowLaw.prod A.quantizer.law) ∧
      (∫ q, innovation q ∂rowLaw.prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw.prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure rowLaw := by
    unfold rowLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  have hproject : Measurable project := by
    dsimp [project]
    fun_prop
  have hmap : Measure.map project fullLaw = rowLaw.prod A.quantizer.law := by
    dsimp [project, fullLaw]
    calc
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ =>
            (q.1 i, q.2))
          ((onlineBatchLaw A.problem b0).prod A.quantizer.law) =
          (Measure.map
            (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i)
            (onlineBatchLaw A.problem b0)).prod
            (Measure.map id A.quantizer.law) := by
              symm
              simpa [Prod.map] using
                (MeasureTheory.Measure.map_prod_map
                  (onlineBatchLaw A.problem b0) A.quantizer.law
                  (measurable_pi_apply i) measurable_id)
      _ = rowLaw.prod A.quantizer.law := by
        rw [onlineBatchLaw_worker_marginal A.problem i]
        simp [rowLaw]
  have hcoord (j : Fin b0.1) :
      Measure.map (fun row : Fin b0.1 → Sample i => row j) rowLaw =
        A.problem.sampleLaw i := by
    unfold rowLaw
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin b0.1 => A.problem.sampleLaw i) j)
  have hgrad (j : Fin b0.1) (z : Point d) : AEStronglyMeasurable
      (fun row : Fin b0.1 → Sample i =>
        stochasticGradient A.problem i (row j) z) rowLaw := by
    have honMap : AEStronglyMeasurable
        (fun ξ => stochasticGradient A.problem i ξ z)
        (Measure.map (fun row : Fin b0.1 → Sample i => row j) rowLaw) := by
      rw [hcoord]
      exact (hVariance.1.2 i z).1.aestronglyMeasurable
    exact honMap.comp_aemeasurable (measurable_pi_apply j).aemeasurable
  have hlocalD : AEStronglyMeasurable localD rowLaw := by
    unfold localD average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => (hgrad j xNext).sub (hgrad j x))).const_smul
        ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro row
    simp [Finset.sum_apply]
  have hinnovation : AEStronglyMeasurable innovation
      (rowLaw.prod A.quantizer.law) := by
    have hDprod : AEStronglyMeasurable
        (fun q : (Fin b0.1 → Sample i) × Ξ => localD q.1)
        (rowLaw.prod A.quantizer.law) := hlocalD.comp_fst
    have hpair : AEMeasurable
        (fun q : (Fin b0.1 → Sample i) × Ξ => (localD q.1, q.2))
        (rowLaw.prod A.quantizer.law) :=
      hDprod.aemeasurable.prodMk measurable_snd.aemeasurable
    exact (A.quantizer.measurable_apply_uncurry.comp_aemeasurable hpair)
      |>.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hinnovation_map : AEStronglyMeasurable innovation
      (Measure.map project fullLaw) := by
    rw [hmap]
    exact hinnovation
  have hsq_map : AEStronglyMeasurable (fun q => ‖innovation q‖ ^ 2)
      (Measure.map project fullLaw) := by
    simpa [pow_two] using hinnovation_map.norm.mul hinnovation_map.norm
  have hglobal := online_corrected_fixed_nonrefresh_worker_moment
    A hE xNext x i Llocal ℒlocal ω hSmooth hAverageFiber hQuantizer
  have hcomp : innovation ∘ project =
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ =>
          A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta) := by
    funext q
    rfl
  have hlocal_int : Integrable innovation (rowLaw.prod A.quantizer.law) := by
    rw [← hmap]
    apply (MeasureTheory.integrable_map_measure
      hinnovation_map hproject.aemeasurable).mpr
    rw [hcomp]
    exact hglobal.1
  have hlocal_sq : Integrable (fun q => ‖innovation q‖ ^ 2)
      (rowLaw.prod A.quantizer.law) := by
    rw [← hmap]
    apply (MeasureTheory.integrable_map_measure
      hsq_map hproject.aemeasurable).mpr
    simpa [hcomp] using hglobal.2.1
  have hmean : (∫ q, innovation q ∂rowLaw.prod A.quantizer.law) = 0 := by
    rw [← hmap, MeasureTheory.integral_map hproject.aemeasurable hinnovation_map]
    change (∫ q, (innovation ∘ project) q ∂fullLaw) = 0
    rw [hcomp]
    exact hglobal.2.2.1
  have hsquare : (∫ q, ‖innovation q‖ ^ 2
      ∂rowLaw.prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    rw [← hmap, MeasureTheory.integral_map hproject.aemeasurable hsq_map]
    simpa [hcomp] using hglobal.2.2.2
  exact ⟨hlocal_int, hlocal_sq, hmean, hsquare⟩

/-- The measurable equivalence between a dependent function of pairs and a
pair of dependent functions.  Mathlib's bundled measurable equivalence is
currently stated only for constant fibers, while Algorithm 3 has a
worker-dependent sample type. -/
def dependentArrowProdMeasurableEquiv
    {ι : Type*} (α β : ι → Type*)
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)] :
    ((i : ι) → α i × β i) ≃ᵐ ((i : ι) → α i) × ((i : ι) → β i) where
  __ := Equiv.arrowProdEquivProdArrow ι α β
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

/-- Product measures commute with the dependent function/pair equivalence.
This is the dependent-fiber form of Mathlib's
`MeasureTheory.measurePreserving_arrowProdEquivProdArrow`. -/
theorem measurePreserving_dependentArrowProdMeasurableEquiv
    {ι : Type*} [Fintype ι]
    (α β : ι → Type*) [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentArrowProdMeasurableEquiv α β)
      (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (dependentArrowProdMeasurableEquiv α β).measurable
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_
      ((isPiSystem_pi).prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi
        fun i => (μ i).toFiniteSpanningSetsIn).prod
      (Measure.FiniteSpanningSetsIn.pi
        (fun i => (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi
          (fun i => (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi
          (fun i => (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, dependentArrowProdMeasurableEquiv,
        MeasurableEquiv.coe_mk]
      rw [show Equiv.arrowProdEquivProdArrow ι α β ⁻¹'
          (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i => s i ×ˢ t i) by
        ext
        simp [Set.mem_pi, forall_and]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi,
        Finset.prod_mul_distrib]

/-- The complete difference-minibatch/compressor law for one online round,
with the refresh coordinates projected away. -/
noncomputable def onlineDifferenceCompressionLaw
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) :=
  (onlineBatchLaw A.problem b0).prod (workerCompressionLaw A.quantizer)

/-- The complete difference/compression coordinate of one online round has
the product law used by the corrected nonrefresh calculation. -/
theorem onlineRoundLaw_differenceCompression_marginal
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2))
        (onlineRoundLaw A) =
      onlineDifferenceCompressionLaw (b0 := b0) A := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  let batches :=
    (onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)
  let compressions := workerCompressionLaw (n := n) A.quantizer
  have hsnd : Measure.map Prod.snd (onlineRoundLaw A) =
      batches.prod compressions := by
    unfold onlineRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2))
        (onlineRoundLaw A) =
        Measure.map (fun q => (q.1.2, q.2))
          (Measure.map Prod.snd (onlineRoundLaw A)) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
    _ = Measure.map (fun q => (q.1.2, q.2))
          (batches.prod compressions) := by rw [hsnd]
    _ = (Measure.map Prod.snd batches).prod compressions := by
          symm
          simpa [Prod.map] using
            (MeasureTheory.Measure.map_prod_map batches compressions
              measurable_snd measurable_id)
    _ = (onlineBatchLaw A.problem b0).prod compressions := by
          rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
    _ = onlineDifferenceCompressionLaw (b0 := b0) A := by
          rfl

/-- The complete generated nonrefresh parameter (the query pair together
with the carried estimator residual) is independent of the whole fresh
difference/compression coordinate.  Keeping the whole coordinate here is
what permits the fixed-query worker covariance calculation to be transported
without rebuilding it worker by worker. -/
theorem online_corrected_nonrefreshParameter_indep_noise
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (k : ℕ) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let parameter := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (((run (k + 1) path).x, (run k path).x),
        (run k path).g - globalGradient P (run k path).x)
    let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      ((path k).2.1.2, (path k).2.2)
    ProbabilityTheory.IndepFun parameter noise law ∧
      Measure.map noise law = onlineDifferenceCompressionLaw (b0 := b0) A := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let parameter := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (((run (k + 1) path).x, (run k path).x),
      (run k path).g - globalGradient P (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((path k).2.1.2, (path k).2.2)
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  haveI : IsProbabilityMeasure prefixLaw := by
    unfold prefixLaw onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineCorrectedPrefixState A hE x0 hBatch fallback k
  let prefixParameter := fun pref =>
    (((primalStep A.stepSize (prefixState pref), (prefixState pref).x),
      (prefixState pref).g - globalGradient P (prefixState pref).x))
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineCorrectedPrefixState_all_aemeasurable
        A hE x0 hBatch σ hVariance fallback k
  have hprefixParameter : AEMeasurable prefixParameter prefixLaw := by
    have hxnext := (measurable_primalStep A.stepSize).comp_aemeasurable hprefixState
    have hx := (measurable_state_x d).comp_aemeasurable hprefixState
    have hg := (measurable_state_g d).comp_aemeasurable hprefixState
    have hgrad := (measurable_gradient (globalObjective P)).comp_aemeasurable hx
    exact (hxnext.prodMk hx).prodMk (hg.sub hgrad)
  let parameterMk := hprefixParameter.mk prefixParameter
  have hparameterMk : Measurable parameterMk := hprefixParameter.measurable_mk
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk (measurable_pi_apply k)).aemeasurable
    · simpa [law, prefixLaw, roundLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hindepMk : ProbabilityTheory.IndepFun
      (parameterMk ∘ prefixMap)
      ((fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2)) ∘
        current) law :=
    hpastCurrent.comp hparameterMk (by fun_prop)
  have hparameter_eq_prefix : ∀ path,
      parameter path = prefixParameter (prefixMap path) := by
    intro path
    dsimp [parameter, prefixParameter, prefixState, run]
    rw [onlineCorrectedProofExactProcess_succ]
    have hs := onlineCorrectedProofExactProcess_congr_prefix
      A hE x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
    rw [hs]
    rfl
  have hprefix_qmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
    ⟨hprefix, by rfl⟩
  have hparameter_ae : parameter =ᵐ[law] parameterMk ∘ prefixMap := by
    have hmk := hprefix_qmp.tendsto_ae hprefixParameter.ae_eq_mk
    filter_upwards [hmk] with path hp
    rw [hparameter_eq_prefix path, hp]
    rfl
  have hindep : ProbabilityTheory.IndepFun parameter noise law := by
    apply hindepMk.congr hparameter_ae.symm
      (Filter.Eventually.of_forall fun path => by rfl)
  have hnoiseLaw : Measure.map noise law =
      onlineDifferenceCompressionLaw (b0 := b0) A := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2))
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_pi_apply k
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2))
          roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = _ := onlineRoundLaw_differenceCompression_marginal A
  exact ⟨hindep, hnoiseLaw⟩

/-- The centered worker innovation in the nonrefresh branch of Algorithm 3,
viewed on the complete current-round difference/compressor coordinate. -/
noncomputable def onlineCorrectedFixedWorkerInnovation
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (xNext x : Point d) (i : Worker n)
    (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) :
    Point d :=
  A.quantizer.apply (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
    localGradientDifference (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
      i xNext x

/-- The worker rows paired with their compressor coordinates are independent
under the complete nonrefresh noise law. -/
theorem onlineDifferenceCompressionLaw_worker_iIndep
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    ProbabilityTheory.iIndepFun
      (fun i (q : ((w : Worker n) → Fin b0.1 → Sample w) ×
          (Worker n → Ξ)) => (q.1 i, q.2 i))
      (onlineDifferenceCompressionLaw A) := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineDifferenceCompressionLaw (b0 := b0) A) := by
    unfold onlineDifferenceCompressionLaw
    infer_instance
  have hWhole :
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
              (Worker n → Ξ) => fun i => (q.1 i, q.2 i))
          (onlineDifferenceCompressionLaw (b0 := b0) A) =
        Measure.infinitePi (fun i : Worker n =>
          (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
            A.quantizer.law) := by
    let α := fun i : Worker n => Fin b0.1 → Sample i
    let β := fun _ : Worker n => Ξ
    let μ := fun i : Worker n =>
      Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)
    let ν := fun _ : Worker n => A.quantizer.law
    have hmp := measurePreserving_dependentArrowProdMeasurableEquiv α β μ ν
    have hinv := MeasurePreserving.symm
      (dependentArrowProdMeasurableEquiv α β) hmp
    simpa [onlineDifferenceCompressionLaw, onlineBatchLaw,
      workerCompressionLaw, α, β, μ, ν,
      MeasureTheory.Measure.infinitePi_eq_pi] using hinv.map_eq
  have hcoord (i : Worker n) :
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
              (Worker n → Ξ) => (q.1 i, q.2 i))
          (onlineDifferenceCompressionLaw (b0 := b0) A) =
        (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
          A.quantizer.law := by
    calc
      _ = Measure.map
          (fun rows : (i : Worker n) → (Fin b0.1 → Sample i) × Ξ => rows i)
          (Measure.map
            (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
                (Worker n → Ξ) => fun j => (q.1 j, q.2 j))
            (onlineDifferenceCompressionLaw (b0 := b0) A)) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_pi_apply i
              · fun_prop
      _ = Measure.map
          (fun rows : (i : Worker n) → (Fin b0.1 → Sample i) × Ξ => rows i)
          (Measure.infinitePi (fun j : Worker n =>
            (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw j)).prod
              A.quantizer.law)) := by rw [hWhole]
      _ = _ := by
        simpa using
          (MeasureTheory.Measure.infinitePi_map_eval
            (μ := fun j : Worker n =>
              (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw j)).prod
                A.quantizer.law) i)
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    fun_prop)).2
  calc
    Measure.map
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) => fun i => (q.1 i, q.2 i))
        (onlineDifferenceCompressionLaw (b0 := b0) A) =
      Measure.infinitePi (fun i : Worker n =>
        (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
          A.quantizer.law) := hWhole
    _ = Measure.infinitePi (fun i : Worker n =>
        Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
              (Worker n → Ξ) => (q.1 i, q.2 i))
          (onlineDifferenceCompressionLaw (b0 := b0) A)) := by
      congr 1
      funext i
      exact (hcoord i).symm

/-- A worker row and its compressor coordinate have the canonical marginal
under the complete nonrefresh noise law. -/
theorem onlineDifferenceCompressionLaw_worker_marginal
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (i : Worker n) :
    Measure.map
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) => (q.1 i, q.2 i))
        (onlineDifferenceCompressionLaw (b0 := b0) A) =
      (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
        A.quantizer.law := by
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  unfold onlineDifferenceCompressionLaw
  calc
    Measure.map
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) => (q.1 i, q.2 i))
        ((onlineBatchLaw A.problem b0).prod
          (workerCompressionLaw A.quantizer)) =
      (Measure.map
          (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i)
          (onlineBatchLaw A.problem b0)).prod
        (Measure.map (fun ξ : Worker n → Ξ => ξ i)
          (workerCompressionLaw A.quantizer)) := by
            symm
            simpa [Prod.map] using
              (MeasureTheory.Measure.map_prod_map
                (onlineBatchLaw A.problem b0)
                (workerCompressionLaw (n := n) A.quantizer)
                (measurable_pi_apply i) (measurable_pi_apply i))
    _ = _ := by
      rw [onlineBatchLaw_worker_marginal A.problem i]
      unfold workerCompressionLaw
      rw [MeasureTheory.Measure.infinitePi_map_eval]

set_option maxHeartbeats 1600000 in
/-- Fixed-query complete nonrefresh worker aggregation.  This is the
formula-level covariance calculation behind the adaptive nonrefresh branch:
the canonical product law makes distinct centered worker innovations
orthogonal and yields the exact `1 / n` coefficient. -/
theorem online_corrected_fixed_nonrefresh_average_second_moment
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (xNext x : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hAverageFiber : ∀ i : Worker n,
      let delta := localGradientDifference
        (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
      let D := fun batch => onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch => ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let law := onlineDifferenceCompressionLaw (b0 := b0) A
    let innovation := fun i : Worker n =>
      onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE xNext x i
    Integrable (fun q => average (fun i : Worker n => innovation i q)) law ∧
      (∫ q, average (fun i : Worker n => innovation i q) ∂law) = 0 ∧
      Integrable (fun q => ‖average (fun i : Worker n => innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n => innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let law := onlineDifferenceCompressionLaw (b0 := b0) A
  let source := fun i : Worker n =>
    fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) =>
      (q.1 i, q.2 i)
  let rowLaw := fun i : Worker n =>
    (Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i)).prod
      A.quantizer.law
  let localInnovation := fun i : Worker n =>
    fun q : (Fin b0.1 → Sample i) × Ξ =>
      A.quantizer.apply
        (average (fun j : Fin b0.1 =>
          stochasticGradient A.problem i (q.1 j) xNext -
            stochasticGradient A.problem i (q.1 j) x)) q.2 -
        localGradientDifference
          (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
  let innovation := fun i : Worker n =>
    onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE xNext x i
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineDifferenceCompressionLaw
    infer_instance
  have hsource : ∀ i : Worker n, Measurable (source i) := by
    intro i
    dsimp [source]
    fun_prop
  have hmap : ∀ i : Worker n, Measure.map (source i) law = rowLaw i := by
    intro i
    simpa [source, law, rowLaw] using
      onlineDifferenceCompressionLaw_worker_marginal (b0 := b0) A i
  have hlocal : ∀ i : Worker n,
      Integrable (localInnovation i) (rowLaw i) ∧
      Integrable (fun q => ‖localInnovation i q‖ ^ 2) (rowLaw i) ∧
      (∫ q, localInnovation i q ∂rowLaw i) = 0 ∧
      (∫ q, ‖localInnovation i q‖ ^ 2 ∂rowLaw i) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    intro i
    simpa [localInnovation, rowLaw] using
      online_corrected_fixed_nonrefresh_worker_local_moment
        A hE xNext x i Llocal ℒlocal σ ω hSmooth hVariance
          (hAverageFiber i) hQuantizer
  have hcomp : ∀ i : Worker n,
      localInnovation i ∘ source i = innovation i := by
    intro i
    funext q
    rfl
  have hdiag : ∀ i : Worker n,
      Integrable (fun q => ‖innovation i q‖ ^ 2) law ∧
      (∫ q, ‖innovation i q‖ ^ 2 ∂law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    intro i
    have hsqaesm : AEStronglyMeasurable
        (fun q => ‖localInnovation i q‖ ^ 2) (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hlocal i).2.1.aestronglyMeasurable
    constructor
    · have honMap : Integrable (fun q => ‖localInnovation i q‖ ^ 2)
          (Measure.map (source i) law) := by
        simpa only [hmap i] using (hlocal i).2.1
      have hpull : Integrable
          ((fun q => ‖localInnovation i q‖ ^ 2) ∘ source i) law :=
        (MeasureTheory.integrable_map_measure hsqaesm
          (hsource i).aemeasurable).mp honMap
      simpa [Function.comp_def, ← hcomp i] using hpull
    · have hInt :
          (∫ q, ‖localInnovation i (source i q)‖ ^ 2 ∂law) =
            ∫ q, ‖localInnovation i q‖ ^ 2
              ∂Measure.map (source i) law := by
        rw [MeasureTheory.integral_map (hsource i).aemeasurable hsqaesm]
      change (∫ q, ‖localInnovation i (source i q)‖ ^ 2 ∂law) ≤ _
      rw [hInt, hmap i]
      exact (hlocal i).2.2.2
  have hvec : ∀ i : Worker n,
      Integrable (innovation i) law ∧ (∫ q, innovation i q ∂law) = 0 := by
    intro i
    have hlocalOnMap : Integrable (localInnovation i)
        (Measure.map (source i) law) := by
      simpa only [hmap i] using (hlocal i).1
    have hlocalAesm : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := hlocalOnMap.aestronglyMeasurable
    have hpull : Integrable (localInnovation i ∘ source i) law :=
      (MeasureTheory.integrable_map_measure hlocalAesm
        (hsource i).aemeasurable).mp hlocalOnMap
    constructor
    · simpa [← hcomp i] using hpull
    · change (∫ q, (localInnovation i ∘ source i) q ∂law) = 0
      have hInt := (MeasureTheory.integral_map
        (hsource i).aemeasurable hlocalAesm).symm
      rw [show (∫ q, (localInnovation i ∘ source i) q ∂law) =
          ∫ q, localInnovation i q ∂Measure.map (source i) law by
        simpa [Function.comp_def] using hInt,
        hmap i]
      exact (hlocal i).2.2.1
  have hindep := onlineDifferenceCompressionLaw_worker_iIndep (b0 := b0) A
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) = 0 := by
    intro i j hij
    let fi := localInnovation i
    let fj := localInnovation j
    let fiMk := (hlocal i).1.aestronglyMeasurable.mk fi
    let fjMk := (hlocal j).1.aestronglyMeasurable.mk fj
    have hfiMk : Measurable fiMk :=
      (hlocal i).1.aestronglyMeasurable.measurable_mk
    have hfjMk : Measurable fjMk :=
      (hlocal j).1.aestronglyMeasurable.measurable_mk
    have hfi_ae : fi =ᵐ[rowLaw i] fiMk :=
      (hlocal i).1.aestronglyMeasurable.ae_eq_mk
    have hfj_ae : fj =ᵐ[rowLaw j] fjMk :=
      (hlocal j).1.aestronglyMeasurable.ae_eq_mk
    have hqmpi : Measure.QuasiMeasurePreserving (source i) law (rowLaw i) :=
      ⟨hsource i, by rw [hmap i]⟩
    have hqmpj : Measure.QuasiMeasurePreserving (source j) law (rowLaw j) :=
      ⟨hsource j, by rw [hmap j]⟩
    have hfi_pull : (fi ∘ source i) =ᵐ[law] (fiMk ∘ source i) :=
      hqmpi.tendsto_ae hfi_ae
    have hfj_pull : (fj ∘ source j) =ᵐ[law] (fjMk ∘ source j) :=
      hqmpj.tendsto_ae hfj_ae
    have hfi_global : innovation i =ᵐ[law] fiMk ∘ source i := by
      rw [← hcomp i]
      simpa [fi] using hfi_pull
    have hfj_global : innovation j =ᵐ[law] fjMk ∘ source j := by
      rw [← hcomp j]
      simpa [fj] using hfj_pull
    have hfixed_int : ∀ _ : (Fin b0.1 → Sample j) × Ξ,
        Integrable (fun s => fiMk s) (rowLaw i) := by
      intro _
      exact (hlocal i).1.congr hfi_ae
    have hfixed_zero : ∀ _ : (Fin b0.1 → Sample j) × Ξ,
        (∫ s, fiMk s ∂rowLaw i) = 0 := by
      intro _
      rw [← integral_congr_ae hfi_ae]
      exact (hlocal i).2.2.1
    have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      law (rowLaw i) (source j) (source i)
      (fun _ s => fiMk s) fjMk
      (by exact hfiMk.comp measurable_snd) hfjMk
      (hsource j) (hsource i) (hindep.indepFun (Ne.symm hij))
      (hmap i) hfixed_int hfixed_zero
    calc
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) =
          ∫ q, ⟪fiMk (source i q), fjMk (source j q)⟫_ℝ ∂law := by
            apply integral_congr_ae
            filter_upwards [hfi_global, hfj_global] with q hi hj
            simpa [Function.comp_apply] using congrArg₂ (inner ℝ) hi hj
      _ = ∫ q, ⟪fjMk (source j q), fiMk (source i q)⟫_ℝ ∂law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun q => real_inner_comm _ _
      _ = 0 := hzero
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (innovation i) law := by
    intro i
    have honMap : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hlocal i).1.aestronglyMeasurable
    have hpull := honMap.comp_aemeasurable (hsource i).aemeasurable
    simpa [Function.comp_def, ← hcomp i] using hpull
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    law (Finset.univ : Finset (Worker n)) innovation
      (fun i _ => hmeas i) (fun i _ => (hdiag i).1)
      (fun i _ j _ hij => hcross hij)
  have havg_int : Integrable
      (fun q => ‖average (fun i : Worker n => innovation i q)‖ ^ 2) law := by
    apply integrable_sq_norm_centeredMiniBatchAverage law
      (Finset.univ : Finset (Worker n)) n.1 innovation
      (fun q => average (fun i : Worker n => innovation i q))
    · intro i _
      exact hmeas i
    · intro i _
      exact (hdiag i).1
    · funext q
      simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
  have havg_vec : Integrable
      (fun q => average (fun i : Worker n => innovation i q)) law := by
    unfold average SOptLib.finiteUniformAverage
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ => (hvec i).1)).smul ((n.1 : ℝ)⁻¹)
  have havg_zero :
      (∫ q, average (fun i : Worker n => innovation i q) ∂law) = 0 := by
    unfold average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ => (hvec i).1)]
    simp [hvec]
  refine ⟨by simpa [innovation, law] using havg_vec,
    by simpa [innovation, law] using havg_zero,
    by simpa [innovation, law] using havg_int, ?_⟩
  have hcoeff_sum :
      (∑ i : Worker n,
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1)) =
      ω * ∑ i : Worker n, (Llocal i) ^ 2 +
        ((1 + ω) / b0.1) * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    calc
      _ = (∑ i : Worker n, ω * (Llocal i) ^ 2) +
          ∑ i : Worker n, ((1 + ω) / b0.1) * (ℒlocal i) ^ 2 := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have hmean_L : 0 ≤ meanSquare Llocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hmean_A : 0 ≤ meanSquare ℒlocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hrms_L : (rootMeanSquare Llocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (Llocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_L]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hrms_A : (rootMeanSquare ℒlocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_A]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  have hb : (b0.1 : ℝ) ≠ 0 := by exact_mod_cast b0.2.ne'
  calc
    (∫ q, ‖average (fun i : Worker n => innovation i q)‖ ^ 2 ∂law) =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ∫ q, ‖Finset.sum Finset.univ (fun i => innovation i q)‖ ^ 2 ∂law := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      unfold average SOptLib.finiteUniformAverage
      simp only [Fintype.card_fin]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n, ∫ q, ‖innovation i q‖ ^ 2 ∂law := by rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n,
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
      rw [← Finset.sum_mul, hcoeff_sum, hrms_L, hrms_A]
      field_simp [hn, hb]

/-- Canonical fixed-query nonrefresh calculation for the proof-exact Eq. (46)
route.  This exposes the paper's actual `onlineLocalProblem` object and removes
the legacy corrected spelling from the scalar source API. -/
theorem online_proofExact_fixed_nonrefresh_average_second_moment
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (xNext x : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hAverageFiber : ∀ i : Worker n,
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let D := fun batch => onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch => ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let law := onlineDifferenceCompressionLaw (b0 := b0) A
    let innovation := fun i : Worker n =>
      fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) =>
        A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q => average (fun i : Worker n => innovation i q)) law ∧
      (∫ q, average (fun i : Worker n => innovation i q) ∂law) = 0 ∧
      Integrable (fun q => ‖average (fun i : Worker n => innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n => innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  let hE : OnlineExpectationRealization A.problem :=
    onlineExpectationRealization A.problem
  simpa [onlineCorrectedFixedWorkerInnovation,
    onlineLocalProblemCorrected_eq_onlineLocalProblem] using
    (online_corrected_fixed_nonrefresh_average_second_moment
      (b0 := b0) A hE xNext x Llocal ℒlocal σ ω hSmooth hVariance
      hAverageFiber hQuantizer)

/-- Product-law regularity of the refresh residual vector at an arbitrary
query law.  It is the component-sized replacement for complete generated-state
measurability in the proof-exact Eq. (46) route. -/
theorem online_refresh_average_product_aestronglyMeasurable
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (p.2 i j) p.1)) -
          globalGradient (onlineLocalProblem A.problem) p.1)
      (μ.prod (onlineBatchLaw A.problem b)) := by
  classical
  let batchLaw := onlineBatchLaw A.problem b
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw = A.problem.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
  have hsampleDiff (i : Worker n) (j : Fin b.1) :
      ∀ᵐ batch ∂batchLaw,
        Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
    let coord := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
        (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop),
        by rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
          simpa [coord] using hcoord i j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleLossInt (i : Worker n) (j : Fin b.1) (x : Point d) :
      Integrable (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        A.problem.sampleLoss i (batch i j) x) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
        simpa [coord] using hcoord i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        stochasticGradient A.problem i (p.2 i j) p.1)
      (μ.prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i μ batchLaw id (fun batch => batch i j)
      stronglyMeasurable_id.aestronglyMeasurable
      (hsampleDiff i j) (hsampleLossInt i j)
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1))
      (μ.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1)))
      (μ.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        globalGradient (onlineLocalProblem A.problem) p.1)
      (μ.prod batchLaw) :=
    ((measurable_gradient (globalObjective (onlineLocalProblem A.problem))).comp
      measurable_fst).aestronglyMeasurable
  simpa [batchLaw] using havg.sub hglobal

/-- Product-law regularity of the scalar refresh residual at an arbitrary
query law.  This is the source-sized regularity interface needed by Eq. (46):
it mentions neither a generated process nor a complete algorithm `State`. -/
theorem online_refresh_average_sq_product_aestronglyMeasurable
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (p.2 i j) p.1)) -
          globalGradient (onlineLocalProblem A.problem) p.1‖ ^ 2)
      (μ.prod (onlineBatchLaw A.problem b)) := by
  classical
  let batchLaw := onlineBatchLaw A.problem b
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw = A.problem.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
  have hsampleDiff (i : Worker n) (j : Fin b.1) :
      ∀ᵐ batch ∂batchLaw,
        Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
    let coord := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
        (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop),
        by rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
          simpa [coord] using hcoord i j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleLossInt (i : Worker n) (j : Fin b.1) (x : Point d) :
      Integrable (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        A.problem.sampleLoss i (batch i j) x) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
        simpa [coord] using hcoord i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        stochasticGradient A.problem i (p.2 i j) p.1)
      (μ.prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i μ batchLaw id (fun batch => batch i j)
      stronglyMeasurable_id.aestronglyMeasurable
      (hsampleDiff i j) (hsampleLossInt i j)
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1))
      (μ.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1)))
      (μ.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        globalGradient (onlineLocalProblem A.problem) p.1)
      (μ.prod batchLaw) :=
    ((measurable_gradient (globalObjective (onlineLocalProblem A.problem))).comp
      measurable_fst).aestronglyMeasurable
  have hv := havg.sub hglobal
  simpa [batchLaw, pow_two] using hv.norm.mul hv.norm

/-- Law-scoped product regularity for the complete corrected nonrefresh
innovation.  The query law is arbitrary; sampled-loss differentiability is
used only to construct the stochastic-gradient finite differences under this
particular product law. -/
theorem online_corrected_nonrefresh_average_product_aestronglyMeasurable
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    [MeasurableSpace Q]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (mu : Measure Q) [SFinite mu] (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) :
    AEStronglyMeasurable
      (fun p : Q ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
        average (fun i : Worker n =>
          onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
            (xNext p.1) (x p.1) i p.2))
      (mu.prod (onlineDifferenceCompressionLaw (b0 := b0) A)) := by
  classical
  let nu := onlineDifferenceCompressionLaw (b0 := b0) A
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure nu := by
    unfold nu onlineDifferenceCompressionLaw
    infer_instance
  have hcoord (i : Worker n) (j : Fin b0.1) :
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) => q.1 i j) nu = A.problem.sampleLaw i := by
    calc
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) => q.1 i j) nu =
          Measure.map
            (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j)
            (Measure.map Prod.fst nu) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_fst
      _ = Measure.map
            (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j)
            (onlineBatchLaw A.problem b0) := by
              rw [show Measure.map Prod.fst nu = onlineBatchLaw A.problem b0 by
                unfold nu onlineDifferenceCompressionLaw
                rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]]
      _ = _ := onlineBatchLaw_coordinate_marginal A.problem i j
  have hsampleDiff (i : Worker n) (j : Fin b0.1) :
      ∀ᵐ q ∂nu, Differentiable ℝ (A.problem.sampleLoss i (q.1 i j)) := by
    let coord := fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
      (Worker n → Ξ) => q.1 i j
    have hqmp : Measure.QuasiMeasurePreserving coord nu (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop), by rw [show Measure.map coord nu =
        A.problem.sampleLaw i by simpa [coord] using hcoord i j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleInt (i : Worker n) (j : Fin b0.1) (x : Point d) :
      Integrable
        (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
          (Worker n → Ξ) => A.problem.sampleLoss i (q.1 i j) x) nu := by
    let coord := fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
      (Worker n → Ξ) => q.1 i j
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map coord nu) := by
      rw [show Measure.map coord nu = A.problem.sampleLaw i by
        simpa [coord] using hcoord i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by dsimp [coord]; fun_prop)).mp hm
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Q ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
        onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
          (xNext p.1) (x p.1) i p.2) (mu.prod nu) := by
    have hnext (j : Fin b0.1) : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          stochasticGradient A.problem i (p.2.1 i j) (xNext p.1)) (mu.prod nu) := by
      exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
        A.problem i mu nu xNext
          (fun q => q.1 i j) hxNext
          (hsampleDiff i j) (hsampleInt i j)
    have hcurrent (j : Fin b0.1) : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          stochasticGradient A.problem i (p.2.1 i j) (x p.1)) (mu.prod nu) := by
      exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
        A.problem i mu nu x
          (fun q => q.1 i j) hx
          (hsampleDiff i j) (hsampleInt i j)
    have hD : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          onlineBatchDifference A.problem p.2.1 i (xNext p.1) (x p.1))
        (mu.prod nu) := by
      unfold onlineBatchDifference average SOptLib.finiteUniformAverage
      have hs := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => (hnext j).sub (hcurrent j))).const_smul
          ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
      refine hs.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply, Finset.sum_sub_distrib]
    have hquantized : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          A.quantizer.apply
            (onlineBatchDifference A.problem p.2.1 i (xNext p.1) (x p.1))
            (p.2.2 i))
        (mu.prod nu) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hD.aemeasurable.prodMk
          ((measurable_pi_apply i).comp
            (measurable_snd.comp measurable_snd)).aemeasurable)).aestronglyMeasurable
    have hdelta : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          localGradientDifference P i (xNext p.1) (x p.1)) (mu.prod nu) := by
      unfold localGradientDifference
      exact (((measurable_localGradient P i).comp_aemeasurable
        hxNext.aemeasurable).aestronglyMeasurable.comp_fst).sub
        (((measurable_localGradient P i).comp_aemeasurable
          hx.aemeasurable).aestronglyMeasurable.comp_fst)
    simpa [onlineCorrectedFixedWorkerInnovation, nu, P] using
      hquantized.sub hdelta
  unfold average SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ => hworker i)).const_smul ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply]

/-- The complete generated nonrefresh worker average is a random vector under
the canonical path law.  This is the direct whole-vector consumer of fresh
round independence and the law-scoped product kernel above. -/
theorem online_corrected_generated_nonrefresh_average_aestronglyMeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (k : ℕ) :
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        average (fun i : Worker n =>
          onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
            (run (k + 1) path).x (run k path).x i
            ((path k).2.1.2, (path k).2.2))) law := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let parameter := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (((run (k + 1) path).x, (run k path).x),
      (run k path).g - globalGradient P (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((path k).2.1.2, (path k).2.2)
  let kernel := fun p : ((Point d × Point d) × Point d) ×
      (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
    average (fun i : Worker n =>
      onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
        p.1.1.1 p.1.1.2 i p.2)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstates := onlineEq46_all_exactLaw_regularities
    A hE x0 hBatch σ hVariance k ⟨0, n.2⟩
  have hparameter : AEMeasurable parameter law := by
    have hk := hstates.2.2.1
    have hsucc := hstates.2.2.2
    have hxk := (measurable_state_x d).comp_aemeasurable hk
    have hxsucc := (measurable_state_x d).comp_aemeasurable hsucc
    have hgk := (measurable_state_g d).comp_aemeasurable hk
    have hgrad := (measurable_gradient (globalObjective P)).comp_aemeasurable hxk
    exact (hxsucc.prodMk hxk).prodMk (hgk.sub hgrad)
  have hnoise : AEMeasurable noise law := by
    dsimp [noise]
    fun_prop
  have hfresh := online_corrected_nonrefreshParameter_indep_noise
    A hE x0 hBatch σ hVariance k
  haveI : IsProbabilityMeasure (Measure.map parameter law) :=
    Measure.isProbabilityMeasure_map hparameter
  haveI : IsProbabilityMeasure (Measure.map noise law) :=
    Measure.isProbabilityMeasure_map hnoise
  have hkernel : AEStronglyMeasurable kernel
      ((Measure.map parameter law).prod (Measure.map noise law)) := by
    rw [hfresh.2]
    exact online_corrected_nonrefresh_average_product_aestronglyMeasurable
      (b0 := b0) A hE σ hVariance (Measure.map parameter law)
        (fun q : (Point d × Point d) × Point d => q.1.1)
        (fun q : (Point d × Point d) × Point d => q.1.2)
        ((measurable_fst.comp measurable_fst).aestronglyMeasurable)
        ((measurable_snd.comp measurable_fst).aestronglyMeasurable)
  have hcomp := aestronglyMeasurable_comp_of_indep_product_law
    hparameter hnoise (inferInstance : SigmaFinite (Measure.map parameter law))
      (inferInstance : SigmaFinite (Measure.map noise law)) hfresh.1 hkernel
  simpa [kernel, parameter, noise, run, law] using hcomp

set_option maxHeartbeats 1600000 in
/-- Complete generated nonrefresh branch moment for the corrected Eq. (46)
calculation.  The strict prefix is the parameter of the fixed-fiber
calculation, while the complete difference/compression coordinate is the
fresh sample.  Consequently Assumption 3.2 is consumed at exactly the
generated pair and the carried estimator residual cancels against the
centered innovation. -/
theorem online_corrected_nonrefresh_branch_moments
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ℒlocal)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
      (onlineCorrectedProofExactProcess A hE x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (onlineCorrectedProofExactProcess A hE x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let residual := fun path =>
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path => average (fun i : Worker n =>
      onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
        (run (k + 1) path).x (run k path).x i
        ((path k).2.1.2, (path k).2.2))
    Integrable (fun path => ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k ∧
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path => ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k ∧
      ProbabilityTheory.IndepFun
        (fun path => ‖residual path + innovation path‖ ^ 2)
        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path k).1) law := by
  classical
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((path k).2.1.2, (path k).2.2)
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let C := (1 / (n.1 : ℝ)) *
    (ω * (rootMeanSquare Llocal) ^ 2 +
      (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineCorrectedPrefixState A hE x0 hBatch fallback k
  let xNext := fun pref => primalStep A.stepSize (prefixState pref)
  let x := fun pref => (prefixState pref).x
  let direction := fun pref =>
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let innovationKernel := fun pref q => average (fun i : Worker n =>
    onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
      (xNext pref) (x pref) i q)
  let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    average (fun i : Worker n =>
      onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
        (run (k + 1) path).x (run k path).x i (noise path))
  let B := fun pref => C * ‖xNext pref - x pref‖ ^ 2
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by rfl
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hcurrent : Measurable current := measurable_pi_apply k
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (prefixMap path, current path))
      (P := law) (mu := prefixLaw)
      (nu := onlineRoundLaw (b := b) (b0 := b0) A)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [noise, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (by fun_prop : Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2)))
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2))
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => (z.2.1.2, z.2.2))
          (onlineRoundLaw A) := by
            rw [show Measure.map current law = onlineRoundLaw A by
              simpa [current, law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = noiseLaw := by
            simpa [noiseLaw] using onlineRoundLaw_differenceCompression_marginal
              (b := b) (b0 := b0) A
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineCorrectedPrefixState_all_aemeasurable
        A hE x0 hBatch σ hVariance fallback k
  have hxNext : AEStronglyMeasurable xNext prefixLaw :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hprefixState)
      |>.aestronglyMeasurable
  have hx : AEStronglyMeasurable x prefixLaw :=
    ((measurable_state_x d).comp_aemeasurable hprefixState).aestronglyMeasurable
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    exact (((measurable_state_g d).comp_aemeasurable hprefixState).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hprefixState))).aestronglyMeasurable
  have hkernel : AEStronglyMeasurable
      (fun p => innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
    simpa [innovationKernel, xNext, x, noiseLaw] using
      online_corrected_nonrefresh_average_product_aestronglyMeasurable
        (b0 := b0) A hE σ hVariance prefixLaw xNext x hxNext hx
  have hkernelSq : AEStronglyMeasurable
      (fun p => ‖innovationKernel p.1 p.2‖ ^ 2) (prefixLaw.prod noiseLaw) := by
    simpa [pow_two] using hkernel.norm.mul hkernel.norm
  have hfixed (pref) := online_corrected_fixed_nonrefresh_average_second_moment
    (b0 := b0) A hE (xNext pref) (x pref) Llocal ℒlocal σ ω
      hSmooth hVariance
      (fun i => by
        simpa [xNext, x, prefixState, onlineCorrectedPrefixState,
          onlineCorrectedProofExactProcess_succ, onlineStep] using
          hAverageSmooth.2 k i (onlineExtendRoundPrefix fallback pref))
      hQuantizer
  have hB_aesm : AEStronglyMeasurable B (Measure.map prefixMap law) := by
    rw [hprefixLaw]
    dsimp [B]
    simpa [pow_two] using
      ((hxNext.sub hx).norm.mul (hxNext.sub hx).norm).const_mul C
  have hB_comp_int : Integrable (fun path => B (prefixMap path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    dsimp [B, xNext, x, prefixState, run]
    rw [onlineCorrectedProofExactProcess_succ]
    have heq := onlineCorrectedProofExactProcess_congr_prefix
      A hE x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
    rw [heq]
    rfl
  have havgSqComp : Integrable
      (fun path => ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2) law :=
    integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := law) (ν := noiseLaw)
      (X := prefixMap) (Y := noise)
      (φ := fun pref q => ‖innovationKernel pref q‖ ^ 2) (B := B)
      hkernelSq hB_aesm hprefix.aemeasurable hnoise.aemeasurable hfresh
      hnoiseLaw (fun _ _ => sq_nonneg _) (fun pref => (hfixed pref).2.2.1)
      hB_comp_int (fun pref => by simpa [B, C] using (hfixed pref).2.2.2)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, run]
    exact (onlineCorrectedProofExactProcess_congr_prefix
      A hE x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])).symm
  have hinnovationComp : ∀ path,
      innovationKernel (prefixMap path) (noise path) = innovation path := by
    intro path
    dsimp [innovationKernel, innovation, xNext, x]
    rw [hstatePrefix path]
    rw [show (run (k + 1) path).x = primalStep A.stepSize (run k path) by rfl]
  have havgSq : Integrable (fun path => ‖innovation path‖ ^ 2) law := by
    exact havgSqComp.congr (Filter.Eventually.of_forall fun path => by
      simpa only using congrArg (fun z : Point d => ‖z‖ ^ 2)
        (hinnovationComp path))
  have havgBoundComp :
      (∫ path, ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2 ∂law) ≤
        ∫ path, B (prefixMap path) ∂law :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := noiseLaw)
      (X := prefixMap) (Y := noise)
      (φ := fun pref q => ‖innovationKernel pref q‖ ^ 2) (B := B)
      hkernelSq hB_aesm hprefix.aemeasurable hnoise.aemeasurable hfresh
      hnoiseLaw havgSqComp hB_comp_int
      (fun pref => by simpa [B, C] using (hfixed pref).2.2.2)
  have havgBound : (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
      C * stepMoment run law k := by
    calc
      (∫ path, ‖innovation path‖ ^ 2 ∂law) =
          ∫ path, ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2 ∂law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun path => by
              simpa only using congrArg (fun z : Point d => ‖z‖ ^ 2)
                (hinnovationComp path).symm
      _ ≤ ∫ path, B (prefixMap path) ∂law := havgBoundComp
      _ = C * stepMoment run law k := by
            unfold stepMoment
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [] with path
            dsimp [B, xNext, x, prefixState, run, stepMoment]
            rw [onlineCorrectedProofExactProcess_succ]
            have heq := onlineCorrectedProofExactProcess_congr_prefix
              A hE x0 hBatch k
              (path := path)
              (path' := onlineExtendRoundPrefix fallback (prefixMap path))
              (by
                intro t ht
                simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
            rw [heq]
            rfl
  have hresidualMeas : AEStronglyMeasurable residual law := by
    let i0 : Worker n := ⟨0, n.2⟩
    have hs := (onlineEq46_all_exactLaw_regularities
      A hE x0 hBatch σ hVariance k i0).2.2.1
    exact (((measurable_state_g d).comp_aemeasurable hs).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hs))).aestronglyMeasurable
  have hinnovationMeas : AEStronglyMeasurable innovation law := by
    simpa [innovation, noise, run, law] using
      online_corrected_generated_nonrefresh_average_aestronglyMeasurable
        A hE x0 hBatch σ hVariance k
  have hresidualSq : Integrable (fun path => ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnerInt : Integrable
      (fun path => ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq havgSq
  have hscalarProd : AEStronglyMeasurable
      (fun p => ⟪direction p.1, innovationKernel p.1 p.2⟫_ℝ)
      (prefixLaw.prod noiseLaw) :=
    hdirection.comp_fst.inner hkernel
  have hinnerComp : ∀ path,
      ⟪direction (prefixMap path), innovationKernel (prefixMap path) (noise path)⟫_ℝ =
        ⟪residual path, innovation path⟫_ℝ := by
    intro path
    rw [hinnovationComp path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hinnerCompInt : Integrable
      (fun path => ⟪direction (prefixMap path),
        innovationKernel (prefixMap path) (noise path)⟫_ℝ) law :=
    hinnerInt.congr (Filter.Eventually.of_forall fun path => (hinnerComp path).symm)
  have hfixedInnerZero : ∀ pref,
      (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) = 0 := by
    intro pref
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction pref)) (hfixed pref).1
    calc
      (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) =
          (innerSL ℝ) (direction pref)
            (∫ q, innovationKernel pref q ∂noiseLaw) := hlin
      _ = 0 := by rw [(hfixed pref).2.1]; simp
  have hcrossComp :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := law) (ν := noiseLaw)
      (X := prefixMap) (Y := noise)
      (φ := fun pref q => ⟪direction pref, innovationKernel pref q⟫_ℝ)
      hscalarProd hprefix.aemeasurable hnoise.aemeasurable hfresh hnoiseLaw
      hinnerCompInt hfixedInnerZero
  have hcross : (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
        ∫ path, ⟪direction (prefixMap path),
          innovationKernel (prefixMap path) (noise path)⟫_ℝ ∂law by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path => (hinnerComp path).symm]
    exact hcrossComp
  have hnonrefreshInt : Integrable
      (fun path => ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas hresidualSq havgSq
  have hnonrefreshEq :
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          ∫ path, ‖innovation path‖ ^ 2 ∂law := by
    let pair : Bool → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) → Point d :=
      fun z => if z then innovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      law (Finset.univ : Finset Bool) pair
      (fun z _ => by cases z <;> simp [pair, hresidualMeas, hinnovationMeas])
      (fun z _ => by cases z <;> simp [pair, hresidualSq, havgSq])
      (fun z _ w _ hzw => by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path k).1
  let rest := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2
  let branchRound := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.1
  let restLaw := ((onlineBatchLaw A.problem b).prod
    (onlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let joined := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (prefixMap path, noise path)
  have hroundRest : ProbabilityTheory.IndepFun rest branchRound
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [onlineRoundLaw, restLaw, rest, branchRound] using h
  have hprefixRestBranch : ProbabilityTheory.IndepFun
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ => (z.1, rest z.2))
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ => branchRound z.2)
      (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by
    exact indepFun_prod_left_adjoin_of_indepFun prefixLaw
      (onlineRoundLaw (b := b) (b0 := b0) A) rest branchRound
      measurable_snd measurable_fst hroundRest
  have hpastRestBranch : ProbabilityTheory.IndepFun
      (fun path => (prefixMap path, rest (current path))) branch law := by
    have hmap : Measure.map (fun path => (prefixMap path, current path)) law =
        prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) := by
      simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hprefix.prodMk ((measurable_snd).comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    let leftProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ => (z.1, rest z.2)
    let rightProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ => branchRound z.2
    let Z := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (prefixMap path, current path)
    have hleft : Measurable leftProd := by dsimp [leftProd]; fun_prop
    have hright : Measurable rightProd := by dsimp [rightProd]; fun_prop
    have hZ : Measurable Z := hprefix.prodMk hcurrent
    calc
      Measure.map
          (fun path => ((prefixMap path, rest (current path)), branch path)) law =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleft.prodMk hright
            · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by
            rw [show Measure.map Z law =
                prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) by
              simpa [Z] using hmap]
      _ = (Measure.map leftProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))).prod
          (Measure.map rightProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleft.aemeasurable hright.aemeasurable).1 hprefixRestBranch
      _ = (Measure.map (fun path => (prefixMap path, rest (current path))) law).prod
          (Measure.map branch law) := by
        rw [show Measure.map leftProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map (fun path => (prefixMap path, rest (current path))) law by
          calc
            _ = Measure.map leftProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hleft hZ]
              congr 1]
        rw [show Measure.map rightProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map branch law by
          calc
            _ = Measure.map rightProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hright hZ]
              congr 1]
  have hjointBranch : ProbabilityTheory.IndepFun joined branch law := by
    have h := hpastRestBranch.comp
      (show Measurable
        (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
            ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) => (z.1, (z.2.1.2, z.2.2))) by fun_prop)
      measurable_id
    simpa [joined, noise, current, rest, branch, Function.comp_def] using h
  have hnonrefreshKernel : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
        ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
      (prefixLaw.prod noiseLaw) := by
    have hv := hdirection.comp_fst.add hkernel
    simpa [pow_two] using hv.norm.mul hv.norm
  have hjJoined : Measurable joined := by
    dsimp [joined]
    exact hprefix.prodMk hnoise
  have hprefixJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      prefixMap := by
    exact measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)
  have hnoiseJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      noise := by
    exact measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)
  obtain ⟨nonrefreshRep, hnonrefreshRepMeas, hnonrefreshAe⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (MeasurableSpace.comap joined inferInstance) prefixMap prefixMap noise
      (fun pref q => ‖direction pref + innovationKernel pref q‖ ^ 2) law
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hjJoined.comap_le hprefixJoined hnoiseJoined
      (Filter.Eventually.of_forall fun _ => rfl) hfresh
      (by simpa [hprefixLaw, hnoiseLaw] using hnonrefreshKernel)
  have hrepIndep : ProbabilityTheory.IndepFun nonrefreshRep branch law := by
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap joined inferInstance)
        (MeasurableSpace.comap branch inferInstance) law := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hjointBranch
    exact indepFun_of_measurable_left_of_indep_comap
      hnonrefreshRepMeas.measurable hcomap
  have hnonrefreshComp : ∀ path,
      ‖direction (prefixMap path) + innovationKernel (prefixMap path) (noise path)‖ ^ 2 =
        ‖residual path + innovation path‖ ^ 2 := by
    intro path
    rw [hinnovationComp path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hnonrefreshIndep : ProbabilityTheory.IndepFun
      (fun path => ‖residual path + innovation path‖ ^ 2) branch law := by
    apply hrepIndep.congr ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hnonrefreshAe] with path hp
    exact hp.symm.trans (hnonrefreshComp path)
  refine ⟨havgSq, ?_, hcross, hnonrefreshInt, ?_, hnonrefreshIndep⟩
  · simpa [C] using havgBound
  · rw [hnonrefreshEq]
    change estimatorErrorMoment P run law k +
        (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ _
    exact add_le_add_right (by simpa [C] using havgBound) _

set_option maxHeartbeats 1600000 in
/-- The corrected proof-exact online process stays in `L²` at every time.
Unlike the finite-sum invariant, the induction uses the complete locally
centered refresh and stochastic nonrefresh branch moments, so no uncentered
sample-gradient moment is required. -/
theorem online_corrected_process_l2_invariant
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ℒlocal) :
    ∀ t,
      let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
      let run := onlineCorrectedProofExactProcess A hE x0 hBatch
      let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run t path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law t ∧
      StepMomentWellDefined run law t := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let i0 : Worker n := ⟨0, n.2⟩
  have hstate : ∀ t, AEMeasurable (run t) law := by
    intro t
    exact (onlineEq46_all_exactLaw_regularities
      A hE x0 hBatch σ hVariance t i0).2.2.1
  have hxMeas : ∀ t, AEStronglyMeasurable (fun path => (run t path).x) law := by
    intro t
    exact ((measurable_state_x d).comp_aemeasurable (hstate t)).aestronglyMeasurable
  have hgMeas : ∀ t, AEStronglyMeasurable (fun path => (run t path).g) law := by
    intro t
    exact ((measurable_state_g d).comp_aemeasurable (hstate t)).aestronglyMeasurable
  have hglobalGradL2 : ∀ t,
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) law →
      Integrable (fun path => ‖globalGradient P (run t path).x‖ ^ 2) law := by
    intro t hx0
    have hGlobal := GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) (rootMeanSquare Llocal)
        (fun path => (run t path).x) (hxMeas t)
    · simpa [norm_sub_rev] using hx0
    · intro x y
      exact hGlobal.2 y x
  intro t
  induction t with
  | zero =>
      have hx0 : Integrable (fun path => ‖(run 0 path).x - x0‖ ^ 2) law := by
        have heq : (fun path => ‖(run 0 path).x - x0‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext path
          change ‖x0 - x0‖ ^ 2 = 0
          simp
        rw [heq]
        exact integrable_const (μ := law) (c := (0 : ℝ))
      have hg0 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) law := by
        have heq : (fun path => ‖(run 0 path).g‖ ^ 2) =
            (fun _ => ‖globalGradient P x0‖ ^ 2) := by
          funext path
          rfl
        rw [heq]
        exact integrable_const (μ := law) (c := ‖globalGradient P x0‖ ^ 2)
      have herr0 : EstimatorErrorMomentWellDefined P run law 0 := by
        have heq : (fun path =>
            ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext path
          change ‖globalGradient P x0 - globalGradient P x0‖ ^ 2 = 0
          simp
        rw [EstimatorErrorMomentWellDefined, heq]
        exact integrable_const (μ := law) (c := (0 : ℝ))
      have hstep0 : StepMomentWellDefined run law 0 := by
        have heq : (fun path => ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
            (fun _ => ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2) := by
          funext path
          change ‖(x0 - (A.stepSize : ℝ) • globalGradient P x0) - x0‖ ^ 2 = _
          congr 2
          rw [neg_smul]
          abel
        rw [StepMomentWellDefined, heq]
        exact integrable_const (μ := law)
          (c := ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2)
      exact ⟨hx0, hg0, herr0, hstep0⟩
  | succ t ih =>
      have hxSucc : Integrable
          (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
        have h := integrable_sq_norm_sub_smul_sub_const_of_l2
          (fun path => (run t path).x) (fun path => (run t path).g)
          x0 (A.stepSize : ℝ) (hxMeas t) (hgMeas t) ih.1 ih.2.1
        simpa [run, onlineCorrectedProofExactProcess_succ, onlineStep,
          primalStep_eq] using h
      have hbranch := online_corrected_nonrefresh_branch_moments
        A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
          hAverageSmooth t ih.2.2.1 ih.2.2.2
      have hrefresh := online_corrected_refresh_average_second_moment
        A hE x0 Llocal σ hSmooth hVariance hBatch t
          (fun i => onlineEq46_all_exactLaw_regularities
            A hE x0 hBatch σ hVariance t i)
      let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        (run t path).g - globalGradient P (run t path).x
      let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        average (fun i : Worker n =>
          onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
            (run (t + 1) path).x (run t path).x i
            ((path t).2.1.2, (path t).2.2))
      let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient A.problem i ((path t).2.1.1 i j)
            (run (t + 1) path).x)) -
          globalGradient P (run (t + 1) path).x
      let nextResidual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        (run (t + 1) path).g - globalGradient P (run (t + 1) path).x
      have hdecomp : ∀ path, nextResidual path =
          if (path t).1 then refreshError path
          else residual path + innovation path := by
        intro path
        let s := run t path
        let xN := primalStep A.stepSize s
        let q := fun i : Worker n =>
          A.quantizer.apply
            (onlineBatchDifference A.problem (path t).2.1.2 i xN s.x)
            ((path t).2.2 i)
        have hdiffAvg : average (fun i : Worker n =>
            localGradientDifference P i xN s.x) =
            globalGradient P xN - globalGradient P s.x := by
          rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
            globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
          unfold averageLocalGradient localGradientDifference average
            SOptLib.finiteUniformAverage
          rw [Finset.sum_sub_distrib, smul_sub]
        have hinnovationAvg : innovation path =
            average q - average (fun i : Worker n =>
              localGradientDifference P i xN s.x) := by
          dsimp [innovation, onlineCorrectedFixedWorkerInnovation, q, xN, s]
          rw [show (run (t + 1) path).x = xN by rfl]
          unfold average SOptLib.finiteUniformAverage
          rw [Finset.sum_sub_distrib, smul_sub]
        have hnext : nextResidual path =
            average (fun i : Worker n =>
              onlineWorkerEstimator A (onlineDriverOfRoundNoise (path t)) s i) -
              globalGradient P xN := by
          rfl
        cases h : (path t).1 with
        | false =>
            simp only [h, Bool.false_eq_true, if_false]
            rw [hnext]
            simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, h, if_false]
            change average (fun i : Worker n => s.g + q i) -
                globalGradient P xN = residual path + innovation path
            rw [average_const_add, hinnovationAvg, hdiffAvg]
            dsimp [residual, s]
            abel
        | true =>
            simp only [h, if_true]
            rw [hnext]
            simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, h, if_true]
            rfl
      have hnextError : EstimatorErrorMomentWellDefined P run law (t + 1) := by
        let s : Set (ℕ → OnlineRoundNoise n b b0 Sample Ξ) :=
          {path | (path t).1 = true}
        have hs : MeasurableSet s := by
          dsimp [s]
          exact (measurable_fst.comp (measurable_pi_apply t))
            (measurableSet_singleton true)
        have hpiece := Integrable.piecewise hs
          hrefresh.1.integrableOn hbranch.2.2.2.1.integrableOn
        have heq : s.piecewise
              (fun path => ‖refreshError path‖ ^ 2)
              (fun path => ‖residual path + innovation path‖ ^ 2) =
            (fun path => ‖nextResidual path‖ ^ 2) := by
          funext path
          by_cases hp : (path t).1 = true
          · simp [s, Set.piecewise, hp, hdecomp path]
          · have hf : (path t).1 = false := Bool.eq_false_of_not_eq_true hp
            simp [s, Set.piecewise, hp, hf, hdecomp path]
        rw [EstimatorErrorMomentWellDefined]
        rw [← heq]
        exact hpiece
      have hglobalSucc := hglobalGradL2 (t + 1) hxSucc
      have hresidualSuccMeas : AEStronglyMeasurable nextResidual law := by
        exact (((measurable_state_g d).comp_aemeasurable (hstate (t + 1))).sub
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            ((measurable_state_x d).comp_aemeasurable (hstate (t + 1)))))
          |>.aestronglyMeasurable
      have hgSucc : Integrable (fun path => ‖(run (t + 1) path).g‖ ^ 2) law := by
        have hadd := integrable_sq_norm_add hresidualSuccMeas
          (((measurable_gradient (globalObjective P)).comp_aemeasurable
            ((measurable_state_x d).comp_aemeasurable (hstate (t + 1))))
            |>.aestronglyMeasurable)
          (by simpa [nextResidual, EstimatorErrorMomentWellDefined] using hnextError)
          hglobalSucc
        convert hadd using 1
        funext path
        congr 2
        dsimp [nextResidual]
        unfold globalGradient
        abel
      have hstepSucc : StepMomentWellDefined run law (t + 1) := by
        have hscaled := integrable_sq_norm_const_smul (-(A.stepSize : ℝ)) hgSucc
        simpa [StepMomentWellDefined, run, onlineCorrectedProofExactProcess_succ,
          onlineStep, primalStep_eq] using hscaled
      exact ⟨hxSucc, hgSucc, hnextError, hstepSucc⟩

/-- The stochastic initialization of executable Algorithm 3 has the scalar
L² base facts needed by Eq. (46), including the sharp `σ²/(n b)` estimator
error bound.  This is derived from Assumptions 1.2 and 3.3 and the canonical
initial-batch/round-stream product law; it is not an added process premise. -/
theorem online_executable_initial_scalar_moments
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hBatch : OnlineBatchAdmissible b b0) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law 0 ∧
      StepMomentWellDefined run law 0 ∧
      estimatorErrorMoment P run law 0 ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let batchLaw := onlineBatchLaw A.problem b
  let initG := fun batch : (i : Worker n) → Fin b.1 → Sample i =>
    average (fun i : Worker n => average (fun j : Fin b.1 =>
      stochasticGradient A.problem i (batch i j) x0))
  let initResidual := fun batch : (i : Worker n) → Fin b.1 → Sample i =>
    initG batch - globalGradient P x0
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (SOptLib.iidStreamLaw (onlineRoundLaw (b := b) (b0 := b0) A)) := by
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw
    infer_instance
  have hfstLaw : Measure.map
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1) law = batchLaw := by
    unfold law onlinePathLaw batchLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hfst : Measure.QuasiMeasurePreserving
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1) law batchLaw :=
    ⟨measurable_fst, by rw [hfstLaw]⟩
  have hInitFixed :
      Integrable (fun batch => ‖initResidual batch‖ ^ 2) batchLaw ∧
        (∫ batch, ‖initResidual batch‖ ^ 2 ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [initResidual, initG, P, batchLaw] using
      (online_fixed_refresh_average_second_moment
        (b := b) A x0 σ hVariance hSmooth.1)
  have hError0 : EstimatorErrorMomentWellDefined P run law 0 := by
    rw [EstimatorErrorMomentWellDefined]
    have hlift : Integrable (fun path => ‖initResidual path.1‖ ^ 2) law := by
      have hm : Integrable (fun batch => ‖initResidual batch‖ ^ 2)
          (Measure.map Prod.fst law) := by
        rw [hfstLaw]
        exact hInitFixed.1
      have hmeas : AEStronglyMeasurable (fun batch => ‖initResidual batch‖ ^ 2)
          (Measure.map Prod.fst law) := by
        rw [hfstLaw]
        exact hInitFixed.1.aestronglyMeasurable
      exact (MeasureTheory.integrable_map_measure
        hmeas measurable_fst.aemeasurable).mp hm
    simpa [run, P, initResidual, initG, onlineProcess, onlineRun_zero,
      onlinePathOfNoise, onlineInitialState, onlinePrintedInitialEstimatorAt] using hlift
  have hError0Bound : estimatorErrorMoment P run law 0 ≤
      varianceAggregateSq σ / (n.1 * b.1) := by
    have hmeas : AEStronglyMeasurable (fun batch => ‖initResidual batch‖ ^ 2)
        (Measure.map
          (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1) law) := by
      rw [hfstLaw]
      exact hInitFixed.1.aestronglyMeasurable
    have hmapIntegral := MeasureTheory.integral_map
      (μ := law) (φ := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1)
      measurable_fst.aemeasurable hmeas
    rw [hfstLaw] at hmapIntegral
    calc
      estimatorErrorMoment P run law 0 =
          ∫ path, ‖initResidual path.1‖ ^ 2 ∂law := by
            apply integral_congr_ae
            filter_upwards [] with path
            rfl
      _ = ∫ batch, ‖initResidual batch‖ ^ 2 ∂batchLaw := hmapIntegral.symm
      _ ≤ varianceAggregateSq σ / (n.1 * b.1) := hInitFixed.2
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw = A.problem.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
  have hgrad (i : Worker n) (j : Fin b.1) : Integrable
      (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        stochasticGradient A.problem i (batch i j) x0) batchLaw := by
    have hm : Integrable (fun xi => stochasticGradient A.problem i xi x0)
        (Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw) := by
      rw [hcoord i j]
      exact (hVariance.1.2 i x0).1
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (((measurable_pi_apply j).comp
        (measurable_pi_apply i)).aemeasurable)).mp hm
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (batch i j) x0)) batchLaw := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => (hgrad i j).aestronglyMeasurable)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro batch
    simp [Finset.sum_apply]
  have hInitG : AEStronglyMeasurable initG batchLaw := by
    unfold initG average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro batch
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hInitGPath : AEStronglyMeasurable (fun path => initG path.1) law :=
    hInitG.comp_quasiMeasurePreserving hfst
  have hResidualPath : AEStronglyMeasurable
      (fun path => initResidual path.1) law := by
    exact hInitGPath.sub aestronglyMeasurable_const
  have hInitGSq : Integrable (fun path => ‖initG path.1‖ ^ 2) law := by
    have hsum := integrable_sq_norm_add hResidualPath
      (aestronglyMeasurable_const : AEStronglyMeasurable
        (fun _ : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => globalGradient P x0) law)
      (by simpa [EstimatorErrorMomentWellDefined, run, P, initResidual, initG,
          onlineProcess, onlineRun_zero, onlinePathOfNoise, onlineInitialState,
          onlinePrintedInitialEstimatorAt] using hError0)
      (integrable_const (μ := law) (c := ‖globalGradient P x0‖ ^ 2))
    apply hsum.congr
    filter_upwards [] with path
    congr 2
    dsimp [initResidual]
    abel
  have hStep0 : StepMomentWellDefined run law 0 := by
    have hscaled := integrable_sq_norm_const_smul (-(A.stepSize : ℝ)) hInitGSq
    have heq : (fun path => ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
        (fun path => ‖(-(A.stepSize : ℝ)) • initG path.1‖ ^ 2) := by
      funext path
      change ‖(x0 - (A.stepSize : ℝ) • initG path.1) - x0‖ ^ 2 = _
      congr 2
      rw [neg_smul]
      abel
    rw [StepMomentWellDefined, heq]
    exact hscaled
  exact ⟨hError0, hStep0, hError0Bound⟩

@[simp] theorem onlineProcess_succ
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :
    onlineProcess A x0 hBatch (k + 1) path =
      onlineStep A (onlineDriverOfRoundNoise (path.2 k))
        (onlineProcess A x0 hBatch k path) := by
  rfl

theorem onlineProcess_congr_round_prefix
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (initial : (i : Worker n) → Fin b.1 → Sample i)
    {path path' : ℕ → OnlineRoundNoise n b b0 Sample Ξ}
    (hpath : ∀ t < k, path t = path' t) :
    onlineProcess A x0 hBatch k (initial, path) =
      onlineProcess A x0 hBatch k (initial, path') := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [onlineProcess_succ, onlineProcess_succ]
      have hprev : ∀ t < k, path t = path' t :=
        fun t ht => hpath t (Nat.lt_trans ht (Nat.lt_succ_self k))
      rw [ih hprev]
      simp only [Prod.snd]
      rw [hpath k (Nat.lt_succ_self k)]

noncomputable def onlineExecutablePrefixState
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ)
    (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
      (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) : State d :=
  onlineProcess A x0 hBatch k
    (pref.1, onlineExtendRoundPrefix fallback pref.2)

/-- Query/residual-specific strict-past freshness for the proof-exact online
process.  The hypotheses are precisely the two component random-variable facts
carried by the scalar Eq. (46) induction.  No measurability statement for a
complete `State` is assumed or concluded. -/
theorem onlineProofExact_nonrefreshParameter_indep_noise_of_components
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (hx : AEStronglyMeasurable
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        (onlineProofExactProcess A x0 hBatch k path).x)
      (onlineProofExactPathLaw A))
    (hresidual : AEStronglyMeasurable
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        (onlineProofExactProcess A x0 hBatch k path).g -
          globalGradient (onlineLocalProblem A.problem)
            (onlineProofExactProcess A x0 hBatch k path).x)
      (onlineProofExactPathLaw A)) :
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let parameter := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (((run (k + 1) path).x, (run k path).x),
        (run k path).g -
          globalGradient (onlineLocalProblem A.problem) (run k path).x)
    let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      ((path k).2.1.2, (path k).2.2)
    ProbabilityTheory.IndepFun parameter
        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k) law ∧
      ProbabilityTheory.IndepFun parameter noise law ∧
      Measure.map noise law = onlineDifferenceCompressionLaw A := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let parameter := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (((run (k + 1) path).x, (run k path).x),
      (run k path).g - globalGradient P (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    ((path k).2.1.2, (path k).2.2)
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  let prefixLaw := Measure.map prefixMap law
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hgrad : AEStronglyMeasurable
      (fun path => globalGradient P (run k path).x) law := by
    exact ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path => (run k path).g) law := by
    have hsum := hresidual.add hgrad
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro path
    dsimp [run, P] at hsum ⊢
    abel
  have hxNext : AEStronglyMeasurable
      (fun path => (run (k + 1) path).x) law := by
    have hstep := hx.sub (hg.const_smul (A.stepSize : ℝ))
    simpa [run, onlineProofExactProcess_succ, onlineStep, primalStep_eq] using hstep
  have hparameter : AEStronglyMeasurable parameter law :=
    (hxNext.prodMk hx).prodMk hresidual
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let prefixParameter := fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ =>
    ((primalStep A.stepSize (prefixState pref), (prefixState pref).x),
      (prefixState pref).g - globalGradient P (prefixState pref).x)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hparameterPrefix : ∀ path,
      prefixParameter (prefixMap path) = parameter path := by
    intro path
    dsimp [prefixParameter, parameter]
    rw [hstatePrefix path]
    rfl
  have hprefixParameter : AEStronglyMeasurable prefixParameter prefixLaw := by
    have hcomp : AEStronglyMeasurable
        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
          prefixParameter (fun i : Fin k => path i.1)) law := by
      refine hparameter.congr (Filter.Eventually.of_forall ?_)
      intro path
      simpa [prefixMap, onlineRoundPrefix] using (hparameterPrefix path).symm
    have hfinite := aestronglyMeasurable_prefix_of_comp_general
      roundLaw k prefixParameter (by
        simpa [law, roundLaw, onlineProofExactPathLaw] using hcomp)
    have hprefixLaw : prefixLaw =
        Measure.infinitePi (fun _ : Fin k => roundLaw) := by
      let e := iidStreamPrefixTailEquiv
        (OnlineRoundNoise n b b0 Sample Ξ) k
      have hemap : Measure.map e law =
          (Measure.infinitePi (fun _ : Fin k => roundLaw)).prod law := by
        simpa [e, law, roundLaw, onlineProofExactPathLaw,
          iidStreamPrefixTailEquiv] using
          (iidStream_prefix_tail_map_eq_prod roundLaw k)
      calc
        prefixLaw = Measure.map Prod.fst (Measure.map e law) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · exact measurable_fst
          · exact e.measurable
        _ = Measure.map Prod.fst
            ((Measure.infinitePi (fun _ : Fin k => roundLaw)).prod law) := by
              rw [hemap]
        _ = Measure.infinitePi (fun _ : Fin k => roundLaw) := by
          rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [hprefixLaw]
    exact hfinite
  let prefixParameterMk := hprefixParameter.mk prefixParameter
  have hprefixParameterMk : Measurable prefixParameterMk :=
    hprefixParameter.measurable_mk
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (P := law) (Z := fun path => (prefixMap path, current path))
      (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [prefixMap, current, prefixLaw, roundLaw, law,
        onlineProofExactPathLaw, SOptLib.iidStreamLaw, onlineRoundPrefix] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  let noiseOfRound := fun z : OnlineRoundNoise n b b0 Sample Ξ =>
    (z.2.1.2, z.2.2)
  have hnoiseOfRound : Measurable noiseOfRound := by
    dsimp [noiseOfRound]
    fun_prop
  have hindepCurrentMk : ProbabilityTheory.IndepFun
      (prefixParameterMk ∘ prefixMap) current law :=
    hpastCurrent.comp hprefixParameterMk measurable_id
  have hprefixQmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
    ⟨hprefix, (show Measure.map prefixMap law = prefixLaw from rfl).absolutelyContinuous⟩
  have hparameterAE : parameter =ᵐ[law] prefixParameterMk ∘ prefixMap := by
    have hmk := hprefixQmp.tendsto_ae hprefixParameter.ae_eq_mk
    filter_upwards [hmk] with path hp
    rw [← hparameterPrefix path, hp]
    rfl
  have hindepCurrent : ProbabilityTheory.IndepFun parameter current law := by
    apply hindepCurrentMk.congr hparameterAE.symm
      (Filter.Eventually.of_forall fun _ => rfl)
  have hindep : ProbabilityTheory.IndepFun parameter noise law := by
    simpa [noise, current, noiseOfRound, Function.comp_def] using
      hindepCurrent.comp measurable_id hnoiseOfRound
  have hnoiseLaw : Measure.map noise law =
      onlineDifferenceCompressionLaw (b0 := b0) A := by
    calc
      Measure.map noise law = Measure.map noiseOfRound (Measure.map current law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact hnoiseOfRound
        · exact hcurrent
      _ = Measure.map noiseOfRound roundLaw := by
        rw [show Measure.map current law = roundLaw by
          simpa [current, law, roundLaw, onlineProofExactPathLaw] using
            SOptLib.iidStreamLaw_map_eval
              (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = _ := by
        simpa [noiseOfRound, roundLaw] using
          onlineRoundLaw_differenceCompression_marginal (b := b) A
  exact ⟨by simpa [current] using hindepCurrent, hindep, hnoiseLaw⟩

/-- Query/residual strict-past freshness for executable Algorithm 3.  The
initial minibatch is retained in the past carrier, while the current round is
the fresh iid coordinate. -/
theorem onlineExecutable_nonrefreshParameter_indep_noise_of_components
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (hx : AEStronglyMeasurable
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
        (onlineProcess A x0 hBatch k path).x)
      (onlinePathLaw A))
    (hresidual : AEStronglyMeasurable
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
        (onlineProcess A x0 hBatch k path).g -
          globalGradient (onlineLocalProblem A.problem)
            (onlineProcess A x0 hBatch k path).x)
      (onlinePathLaw A)) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    let parameter := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      (((run (k + 1) path).x, (run k path).x),
        (run k path).g -
          globalGradient (onlineLocalProblem A.problem) (run k path).x)
    let noise := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      (((path.2 k).2.1.2), (path.2 k).2.2)
    ProbabilityTheory.IndepFun parameter
        (fun path => path.2 k) law ∧
      ProbabilityTheory.IndepFun parameter noise law ∧
      Measure.map noise law = onlineDifferenceCompressionLaw A := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let batchLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let parameter := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    (((run (k + 1) path).x, (run k path).x),
      (run k path).g - globalGradient P (run k path).x)
  let noise := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let prefixMap := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    (path.1, onlineRoundPrefix k path.2)
  let current := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k
  let prefixLaw := Measure.map prefixMap law
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j =>
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hgrad : AEStronglyMeasurable
      (fun path => globalGradient P (run k path).x) law :=
    ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path => (run k path).g) law := by
    have hsum := hresidual.add hgrad
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro path
    dsimp [P, run] at hsum ⊢
    abel
  have hxNext : AEStronglyMeasurable
      (fun path => (run (k + 1) path).x) law := by
    have hstep := hx.sub (hg.const_smul (A.stepSize : ℝ))
    simpa [run, onlineProcess_succ, onlineStep, primalStep_eq] using hstep
  have hparameter : AEStronglyMeasurable parameter law :=
    (hxNext.prodMk hx).prodMk hresidual
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ => Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let prefixParameter := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((primalStep A.stepSize (prefixState pref), (prefixState pref).x),
      (prefixState pref).g - globalGradient P (prefixState pref).x)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hparameterPrefix : ∀ path,
      prefixParameter (prefixMap path) = parameter path := by
    intro path
    dsimp [prefixParameter, parameter]
    rw [hstatePrefix path]
    rfl
  have hprefixLaw : prefixLaw =
      batchLaw.prod (Measure.infinitePi (fun _ : Fin k => roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map batchLaw streamLaw measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) => measurable_pi_apply j.1)
    have hstreamPrefix : Measure.map
        (fun x : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
          fun j : Fin k => x j.1) streamLaw =
        Measure.infinitePi (fun _ : Fin k => roundLaw) := by
      simpa [streamLaw] using iidStream_prefix_map_eq_infinitePi roundLaw k
    rw [Measure.map_id, hstreamPrefix] at hm
    simpa [prefixLaw, prefixMap, law, batchLaw, streamLaw, onlinePathLaw,
      onlineRoundPrefix] using hm.symm
  have hprefixParameter : AEStronglyMeasurable prefixParameter prefixLaw := by
    have hcomp : AEStronglyMeasurable
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
          prefixParameter (path.1, fun j : Fin k => path.2 j.1)) law := by
      refine hparameter.congr (Filter.Eventually.of_forall ?_)
      intro path
      simpa [prefixMap, onlineRoundPrefix] using (hparameterPrefix path).symm
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      batchLaw roundLaw k prefixParameter (by
        simpa [law, batchLaw, roundLaw, onlinePathLaw] using hcomp)
    rw [hprefixLaw]
    exact hfinite
  let prefixParameterMk := hprefixParameter.mk prefixParameter
  have hprefixParameterMk : Measurable prefixParameterMk :=
    hprefixParameter.measurable_mk
  let streamPrefix := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    fun j : Fin k => path j.1
  let streamCurrent := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
  have hstreamPrefixMeas : Measurable streamPrefix := by
    dsimp [streamPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hstreamCurrentMeas : Measurable streamCurrent := measurable_pi_apply k
  haveI : IsProbabilityMeasure (Measure.map streamPrefix streamLaw) :=
    Measure.isProbabilityMeasure_map hstreamPrefixMeas.aemeasurable
  have hstreamIndep : ProbabilityTheory.IndepFun streamPrefix streamCurrent streamLaw := by
    apply indepFun_of_map_prod_eq_prod_laws
      (P := streamLaw) (Z := fun path => (streamPrefix path, streamCurrent path))
      (mu := Measure.map streamPrefix streamLaw) (nu := roundLaw)
    · exact (hstreamPrefixMeas.prodMk hstreamCurrentMeas).aemeasurable
    · simpa [streamPrefix, streamCurrent, streamLaw, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => roundLaw) k)
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    have h := indepFun_prod_left_adjoin_of_indepFun
      batchLaw streamLaw streamPrefix streamCurrent
      hstreamPrefixMeas hstreamCurrentMeas hstreamIndep
    simpa [prefixMap, current, law, batchLaw, streamLaw, onlinePathLaw,
      streamPrefix, streamCurrent, onlineRoundPrefix] using h
  have hindepCurrentMk : ProbabilityTheory.IndepFun
      (prefixParameterMk ∘ prefixMap) current law :=
    hpastCurrent.comp hprefixParameterMk measurable_id
  have hprefixQmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
    ⟨hprefix, (show Measure.map prefixMap law = prefixLaw from rfl).absolutelyContinuous⟩
  have hparameterAE : parameter =ᵐ[law] prefixParameterMk ∘ prefixMap := by
    have hmk := hprefixQmp.tendsto_ae hprefixParameter.ae_eq_mk
    filter_upwards [hmk] with path hp
    rw [← hparameterPrefix path, hp]
    rfl
  have hindepCurrent : ProbabilityTheory.IndepFun parameter current law :=
    hindepCurrentMk.congr hparameterAE.symm (Filter.Eventually.of_forall fun _ => rfl)
  let noiseOfRound := fun z : OnlineRoundNoise n b b0 Sample Ξ =>
    (z.2.1.2, z.2.2)
  have hnoiseOfRound : Measurable noiseOfRound := by
    dsimp [noiseOfRound]
    fun_prop
  have hindep : ProbabilityTheory.IndepFun parameter noise law := by
    simpa [noise, current, noiseOfRound, Function.comp_def] using
      hindepCurrent.comp measurable_id hnoiseOfRound
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law =
          Measure.map streamCurrent (Measure.map Prod.snd law) := by
            rw [MeasureTheory.Measure.map_map hstreamCurrentMeas measurable_snd]
            rfl
      _ = Measure.map streamCurrent streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law, streamLaw, onlinePathLaw]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := by
            simpa [streamCurrent, streamLaw] using
              SOptLib.iidStreamLaw_map_eval roundLaw k
  have hnoiseLaw : Measure.map noise law =
      onlineDifferenceCompressionLaw (b0 := b0) A := by
    calc
      Measure.map noise law = Measure.map noiseOfRound (Measure.map current law) := by
        rw [MeasureTheory.Measure.map_map hnoiseOfRound hcurrent]
        rfl
      _ = Measure.map noiseOfRound roundLaw := by rw [hcurrentLaw]
      _ = _ := by
        simpa [noiseOfRound, roundLaw] using
          onlineRoundLaw_differenceCompression_marginal (b := b) A
  exact ⟨by simpa [current] using hindepCurrent, hindep, hnoiseLaw⟩

/-- A scalar observable built from the strict prefix and the non-coin part of
the current iid round is independent of the current Bernoulli coin. -/
theorem iidStream_prefix_current_snd_kernel_indep_fst
    {R : Type*} [MeasurableSpace R]
    (coinLaw : Measure Bool) (restLaw : Measure R)
    [IsProbabilityMeasure coinLaw] [IsProbabilityMeasure restLaw]
    (k : ℕ) (F : (Fin k → Bool × R) → R → ℝ)
    (hF : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.infinitePi (fun _ : Fin k => coinLaw.prod restLaw)).prod restLaw)) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → Bool × R => F (fun j : Fin k => path j.1) (path k).2)
      (fun path : ℕ → Bool × R => (path k).1)
      (SOptLib.iidStreamLaw (coinLaw.prod restLaw)) := by
  classical
  let law := SOptLib.iidStreamLaw (coinLaw.prod restLaw)
  let prefixMap := fun path : ℕ → Bool × R => fun j : Fin k => path j.1
  let current := fun path : ℕ → Bool × R => path k
  let rest := fun z : Bool × R => z.2
  let branchRound := fun z : Bool × R => z.1
  let prefixLaw := Measure.map prefixMap law
  let joined := fun path : ℕ → Bool × R => (prefixMap path, rest (current path))
  let branch := fun path : ℕ → Bool × R => branchRound (current path)
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hrest : Measurable rest := measurable_snd
  have hbranchRound : Measurable branchRound := measurable_fst
  haveI : IsProbabilityMeasure (coinLaw.prod restLaw) := by infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (P := law) (Z := fun path => (prefixMap path, current path))
      (mu := prefixLaw) (nu := coinLaw.prod restLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixLaw, prefixMap, current, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod (fun _ : ℕ => coinLaw.prod restLaw) k)
  have hroundRest : ProbabilityTheory.IndepFun rest branchRound
      (coinLaw.prod restLaw) := by
    simpa [rest, branchRound] using
      (ProbabilityTheory.indepFun_prod
        (μ := coinLaw) (ν := restLaw) measurable_id measurable_id).symm
  have hprefixRestBranch : ProbabilityTheory.IndepFun
      (fun z : (Fin k → Bool × R) × (Bool × R) => (z.1, rest z.2))
      (fun z : (Fin k → Bool × R) × (Bool × R) => branchRound z.2)
      (prefixLaw.prod (coinLaw.prod restLaw)) :=
    indepFun_prod_left_adjoin_of_indepFun prefixLaw (coinLaw.prod restLaw)
      rest branchRound hrest hbranchRound hroundRest
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch law := by
    have hmap : Measure.map (fun path => (prefixMap path, current path)) law =
        prefixLaw.prod (coinLaw.prod restLaw) := by
      simpa [law, prefixLaw, prefixMap, current, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => coinLaw.prod restLaw) k)
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hprefix.prodMk (hrest.comp hcurrent)).aemeasurable)
      ((hbranchRound.comp hcurrent).aemeasurable)).2
    let leftProd := fun z : (Fin k → Bool × R) × (Bool × R) =>
      (z.1, rest z.2)
    let rightProd := fun z : (Fin k → Bool × R) × (Bool × R) => branchRound z.2
    let Z := fun path : ℕ → Bool × R => (prefixMap path, current path)
    have hleft : Measurable leftProd := by dsimp [leftProd]; fun_prop
    have hright : Measurable rightProd := by dsimp [rightProd]; fun_prop
    have hZ : Measurable Z := hprefix.prodMk hcurrent
    calc
      Measure.map (fun path => (joined path, branch path)) law =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleft.prodMk hright
            · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod (coinLaw.prod restLaw)) := by rw [hmap]
      _ = (Measure.map leftProd (prefixLaw.prod (coinLaw.prod restLaw))).prod
          (Measure.map rightProd (prefixLaw.prod (coinLaw.prod restLaw))) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleft.aemeasurable hright.aemeasurable).mp hprefixRestBranch
      _ = (Measure.map joined law).prod (Measure.map branch law) := by
        rw [show Measure.map leftProd (prefixLaw.prod (coinLaw.prod restLaw)) =
            Measure.map joined law by
          calc
            _ = Measure.map leftProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by rw [MeasureTheory.Measure.map_map hleft hZ]; rfl]
        rw [show Measure.map rightProd (prefixLaw.prod (coinLaw.prod restLaw)) =
            Measure.map branch law by
          calc
            _ = Measure.map rightProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by rw [MeasureTheory.Measure.map_map hright hZ]; rfl]
  have hjointed : Measurable joined := hprefix.prodMk (hrest.comp hcurrent)
  have hprefixJoined : Measurable[MeasurableSpace.comap joined inferInstance] prefixMap :=
    measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)
  have hrestJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => rest (current path)) := by
    have hs : Measurable[MeasurableSpace.comap joined inferInstance]
        (Prod.snd ∘ joined) :=
      measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)
    simpa [joined, Function.comp_def] using hs
  have hprefixRest : ProbabilityTheory.IndepFun prefixMap
      (fun path => rest (current path)) law := hpastCurrent.comp measurable_id hrest
  have hprefixLawEq : prefixLaw =
      Measure.infinitePi (fun _ : Fin k => coinLaw.prod restLaw) := by
    simpa [prefixLaw, prefixMap, law, SOptLib.iidStreamLaw] using
      iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) k
  have hrestLawEq : Measure.map (fun path => rest (current path)) law = restLaw := by
    calc
      Measure.map (fun path => rest (current path)) law =
          Measure.map rest (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map hrest hcurrent]
            rfl
      _ = Measure.map rest (coinLaw.prod restLaw) := by
            rw [show Measure.map current law = coinLaw.prod restLaw by
              simpa [current, law] using
                SOptLib.iidStreamLaw_map_eval (coinLaw.prod restLaw) k]
      _ = restLaw := by
        dsimp [rest]
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hkernel : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map prefixMap law).prod
        (Measure.map (fun path => rest (current path)) law)) := by
    change AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod (Measure.map (fun path => rest (current path)) law))
    rw [hprefixLawEq, hrestLawEq]
    exact hF
  obtain ⟨rep, hrepMeas, hrepAE⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (MeasurableSpace.comap joined inferInstance)
      prefixMap prefixMap (fun path => rest (current path)) F law
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map (fun path => rest (current path)) law))
      hjointed.comap_le hprefixJoined hrestJoined
      (Filter.Eventually.of_forall fun _ => rfl) hprefixRest hkernel
  have hrepIndep : ProbabilityTheory.IndepFun rep branch law := by
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap joined inferInstance)
        (MeasurableSpace.comap branch inferInstance) law := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hjoinedBranch
    exact indepFun_of_measurable_left_of_indep_comap hrepMeas.measurable hcomap
  apply hrepIndep.congr hrepAE.symm (Filter.Eventually.of_forall fun _ => rfl)

/-- A scalar observable built from Algorithm 3's independent initial minibatch,
the strict iid round prefix, and the non-coin part of the current round is
independent of the current Bernoulli coin. -/
theorem initial_iidStream_prefix_current_snd_kernel_indep_fst
    {B R : Type*} [MeasurableSpace B] [MeasurableSpace R]
    (initialLaw : Measure B) (coinLaw : Measure Bool) (restLaw : Measure R)
    [IsProbabilityMeasure initialLaw]
    [IsProbabilityMeasure coinLaw] [IsProbabilityMeasure restLaw]
    (k : ℕ) (F : (B × (Fin k → Bool × R)) → R → ℝ)
    (hF : AEStronglyMeasurable (Function.uncurry F)
      ((initialLaw.prod
        (Measure.infinitePi (fun _ : Fin k => coinLaw.prod restLaw))).prod restLaw)) :
    ProbabilityTheory.IndepFun
      (fun path : B × (ℕ → Bool × R) =>
        F (path.1, fun j : Fin k => path.2 j.1) (path.2 k).2)
      (fun path : B × (ℕ → Bool × R) => (path.2 k).1)
      (initialLaw.prod (SOptLib.iidStreamLaw (coinLaw.prod restLaw))) := by
  classical
  let streamLaw := SOptLib.iidStreamLaw (coinLaw.prod restLaw)
  let law := initialLaw.prod streamLaw
  let prefixMap := fun path : ℕ → Bool × R => fun j : Fin k => path j.1
  let current := fun path : ℕ → Bool × R => path k
  let rest := fun z : Bool × R => z.2
  let branchRound := fun z : Bool × R => z.1
  let prefixLaw := Measure.map prefixMap streamLaw
  let joined := fun path : ℕ → Bool × R => (prefixMap path, rest (current path))
  let branch := fun path : ℕ → Bool × R => branchRound (current path)
  let fullPrefix := fun path : B × (ℕ → Bool × R) => (path.1, prefixMap path.2)
  let restAt := fun path : B × (ℕ → Bool × R) => rest (current path.2)
  let fullJoined := fun path : B × (ℕ → Bool × R) =>
    (fullPrefix path, restAt path)
  let fullBranch := fun path : B × (ℕ → Bool × R) => branch path.2
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hrest : Measurable rest := measurable_snd
  have hbranchRound : Measurable branchRound := measurable_fst
  haveI : IsProbabilityMeasure (coinLaw.prod restLaw) := by infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw]
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current streamLaw := by
    apply indepFun_of_map_prod_eq_prod_laws
      (P := streamLaw) (Z := fun path => (prefixMap path, current path))
      (mu := prefixLaw) (nu := coinLaw.prod restLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [streamLaw, prefixLaw, prefixMap, current, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => coinLaw.prod restLaw) k)
  have hroundRest : ProbabilityTheory.IndepFun rest branchRound
      (coinLaw.prod restLaw) := by
    simpa [rest, branchRound] using
      (ProbabilityTheory.indepFun_prod
        (μ := coinLaw) (ν := restLaw) measurable_id measurable_id).symm
  have hprefixRestBranch : ProbabilityTheory.IndepFun
      (fun z : (Fin k → Bool × R) × (Bool × R) => (z.1, rest z.2))
      (fun z : (Fin k → Bool × R) × (Bool × R) => branchRound z.2)
      (prefixLaw.prod (coinLaw.prod restLaw)) :=
    indepFun_prod_left_adjoin_of_indepFun prefixLaw (coinLaw.prod restLaw)
      rest branchRound hrest hbranchRound hroundRest
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch streamLaw := by
    have hmap : Measure.map (fun path => (prefixMap path, current path)) streamLaw =
        prefixLaw.prod (coinLaw.prod restLaw) := by
      simpa [streamLaw, prefixLaw, prefixMap, current, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => coinLaw.prod restLaw) k)
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hprefix.prodMk (hrest.comp hcurrent)).aemeasurable)
      ((hbranchRound.comp hcurrent).aemeasurable)).2
    let leftProd := fun z : (Fin k → Bool × R) × (Bool × R) =>
      (z.1, rest z.2)
    let rightProd := fun z : (Fin k → Bool × R) × (Bool × R) => branchRound z.2
    let Z := fun path : ℕ → Bool × R => (prefixMap path, current path)
    have hleft : Measurable leftProd := by dsimp [leftProd]; fun_prop
    have hright : Measurable rightProd := by dsimp [rightProd]; fun_prop
    have hZ : Measurable Z := hprefix.prodMk hcurrent
    calc
      Measure.map (fun path => (joined path, branch path)) streamLaw =
          Measure.map (fun z => (leftProd z, rightProd z))
            (Measure.map Z streamLaw) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleft.prodMk hright
              · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod (coinLaw.prod restLaw)) := by rw [hmap]
      _ = (Measure.map leftProd (prefixLaw.prod (coinLaw.prod restLaw))).prod
          (Measure.map rightProd (prefixLaw.prod (coinLaw.prod restLaw))) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleft.aemeasurable hright.aemeasurable).mp hprefixRestBranch
      _ = (Measure.map joined streamLaw).prod (Measure.map branch streamLaw) := by
        rw [show Measure.map leftProd (prefixLaw.prod (coinLaw.prod restLaw)) =
            Measure.map joined streamLaw by
          calc
            _ = Measure.map leftProd (Measure.map Z streamLaw) := by rw [hmap]
            _ = _ := by rw [MeasureTheory.Measure.map_map hleft hZ]; rfl]
        rw [show Measure.map rightProd (prefixLaw.prod (coinLaw.prod restLaw)) =
            Measure.map branch streamLaw by
          calc
            _ = Measure.map rightProd (Measure.map Z streamLaw) := by rw [hmap]
            _ = _ := by rw [MeasureTheory.Measure.map_map hright hZ]; rfl]
  have hjoined : Measurable joined := hprefix.prodMk (hrest.comp hcurrent)
  have hbranch : Measurable branch := hbranchRound.comp hcurrent
  have hfullJoinedBranch : ProbabilityTheory.IndepFun fullJoined fullBranch law := by
    have hAdjoined := indepFun_prod_left_adjoin_of_indepFun initialLaw streamLaw
      joined branch hjoined hbranch hjoinedBranch
    let reassoc := fun z : B × ((Fin k → Bool × R) × R) =>
      ((z.1, z.2.1), z.2.2)
    have hreassoc : Measurable reassoc := by dsimp [reassoc]; fun_prop
    simpa [fullJoined, fullBranch, fullPrefix, restAt, joined, reassoc] using
      hAdjoined.comp hreassoc measurable_id
  have hprefixRest : ProbabilityTheory.IndepFun prefixMap
      (fun path => rest (current path)) streamLaw :=
    hpastCurrent.comp measurable_id hrest
  have hfullPrefixRest : ProbabilityTheory.IndepFun fullPrefix restAt law := by
    simpa [fullPrefix, restAt] using
      indepFun_prod_left_adjoin_of_indepFun initialLaw streamLaw prefixMap
        (fun path => rest (current path)) hprefix (hrest.comp hcurrent) hprefixRest
  have hfullJoined : Measurable fullJoined := by
    dsimp [fullJoined, fullPrefix, restAt]
    fun_prop
  have hfullPrefixJoined :
      Measurable[MeasurableSpace.comap fullJoined inferInstance] fullPrefix :=
    measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)
  have hrestJoined :
      Measurable[MeasurableSpace.comap fullJoined inferInstance] restAt := by
    have hs : Measurable[MeasurableSpace.comap fullJoined inferInstance]
        (Prod.snd ∘ fullJoined) :=
      measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)
    simpa [fullJoined, Function.comp_def] using hs
  have hprefixLawEq : prefixLaw =
      Measure.infinitePi (fun _ : Fin k => coinLaw.prod restLaw) := by
    simpa [prefixLaw, prefixMap, streamLaw, SOptLib.iidStreamLaw] using
      iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) k
  have hfullPrefixLaw : Measure.map fullPrefix law = initialLaw.prod prefixLaw := by
    have hmap := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id hprefix
    rw [Measure.map_id] at hmap
    simpa [law, fullPrefix, prefixLaw] using hmap.symm
  have hrestLawEq : Measure.map restAt law = restLaw := by
    calc
      Measure.map restAt law =
          Measure.map (fun path => rest (current path))
            (Measure.map Prod.snd law) := by
              change Measure.map
                ((rest ∘ current) ∘ Prod.snd) law =
                  Measure.map (rest ∘ current) (Measure.map Prod.snd law)
              exact (MeasureTheory.Measure.map_map
                (hrest.comp hcurrent) measurable_snd).symm
      _ = Measure.map (fun path => rest (current path)) streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map rest (Measure.map current streamLaw) := by
            rw [MeasureTheory.Measure.map_map hrest hcurrent]
            rfl
      _ = Measure.map rest (coinLaw.prod restLaw) := by
            rw [show Measure.map current streamLaw = coinLaw.prod restLaw by
              simpa [current, streamLaw] using
                SOptLib.iidStreamLaw_map_eval (coinLaw.prod restLaw) k]
      _ = restLaw := by
        dsimp [rest]
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hkernel : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map fullPrefix law).prod (Measure.map restAt law)) := by
    rw [hfullPrefixLaw, hprefixLawEq, hrestLawEq]
    exact hF
  obtain ⟨rep, hrepMeas, hrepAE⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (MeasurableSpace.comap fullJoined inferInstance)
      fullPrefix fullPrefix restAt F law
      (inferInstance : SigmaFinite (Measure.map fullPrefix law))
      (inferInstance : SigmaFinite (Measure.map restAt law))
      hfullJoined.comap_le hfullPrefixJoined hrestJoined
      (Filter.Eventually.of_forall fun _ => rfl) hfullPrefixRest hkernel
  have hrepIndep : ProbabilityTheory.IndepFun rep fullBranch law := by
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap fullJoined inferInstance)
        (MeasurableSpace.comap fullBranch inferInstance) law := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hfullJoinedBranch
    exact indepFun_of_measurable_left_of_indep_comap hrepMeas.measurable hcomap
  apply hrepIndep.congr hrepAE.symm (Filter.Eventually.of_forall fun _ => rfl)

/-- Integrating one branch of an independent Boolean gate multiplies the
payload integral by the gate's singleton mass. -/
theorem integral_independent_bool_gate_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (coinLaw : Measure Bool) (selected : Bool) (weight : ℝ)
    (F : Ω → ℝ) (branch : Ω → Bool)
    (hF : Integrable F P) (hbranch : Measurable branch)
    (hindep : ProbabilityTheory.IndepFun F branch P)
    (hbranchLaw : Measure.map branch P = coinLaw)
    (hmass : coinLaw.real ({selected} : Set Bool) = weight) :
    (∫ ω, if branch ω = selected then F ω else 0 ∂P) ≤
      weight * ∫ ω, F ω ∂P := by
  letI : IsProbabilityMeasure coinLaw := by
    rw [← hbranchLaw]
    exact Measure.isProbabilityMeasure_map hbranch.aemeasurable
  let φ : ℝ → Bool → ℝ := fun z c => if c = selected then z else 0
  let B : ℝ → ℝ := fun z => weight * z
  have hφ : Measurable (Function.uncurry φ) := by
    dsimp [φ, Function.uncurry]
    apply Measurable.ite
    · exact measurable_snd (measurableSet_singleton selected)
    · exact measurable_fst
    · exact measurable_const
  have hB : AEStronglyMeasurable B (Measure.map F P) := by
    exact (measurable_const.mul measurable_id).aestronglyMeasurable
  have hgateInt : Integrable (fun ω => φ (F ω) (branch ω)) P := by
    have hs : MeasurableSet {ω | branch ω = selected} :=
      hbranch (measurableSet_singleton selected)
    have hpiece := Integrable.piecewise hs hF.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [φ, Set.piecewise] using hpiece
  have hBInt : Integrable (fun ω => B (F ω)) P := by
    simpa [B] using hF.const_mul weight
  have hfixed : ∀ z : ℝ, (∫ c, φ z c ∂coinLaw) ≤ B z := by
    intro z
    rw [MeasureTheory.integral_fintype]
    · simpa [φ, B, hmass, mul_comm]
    · exact Integrable.of_finite
  have hbound :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := P) (ν := coinLaw) (X := F) (Y := branch) (φ := φ) (B := B)
      hφ.aestronglyMeasurable hB hF.aestronglyMeasurable.aemeasurable
      hbranch.aemeasurable hindep hbranchLaw hgateInt hBInt hfixed
  simpa [φ, B, integral_const_mul] using hbound

/- Exact-header executable Eq. (46) attempt.  The proved initialization helper
is consumed immediately, and the guarded failure is now the simultaneous
successor induction for the two scalar moment certificates, rather than an
unstructured fixed-time integrability placeholder. -/
set_option maxHeartbeats 1600000 in
/--
trace: case succ
-/
#guard_msgs (trace, drop error, substring := true) in
example
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) :
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) (k + 1) ∧
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) k ∧
    StepMomentWellDefined (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) k ∧
    estimatorErrorMoment (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
            (onlinePathLaw (b := b) (b0 := b0) A) k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment (onlineLocalProblem A.problem)
            (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
            (onlinePathLaw (b := b) (b0 := b0) A) k +
        A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  have hBase := online_executable_initial_scalar_moments
    (b := b) (b0 := b0) A x0 Llocal σ hSmooth hVariance hBatch
  have hMoments : ∀ t,
      EstimatorErrorMomentWellDefined P run law t ∧
        StepMomentWellDefined run law t := by
    intro t
    induction t with
    | zero => exact ⟨hBase.1, hBase.2.1⟩
    | succ t ih =>
        trace_state
        fun_prop
  exact online_estimator_recurrence_46_literal_source_boundary
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k

/- Retained legacy counterexample for the fixed-query-only interpretation.
Its header now explicitly names `LegacyOnlineFixedQueryUnbiasedBoundedVariance`,
so it no longer purports to refute the reconstructed Assumption 3.3 source
boundary.  The proof still records the exact failure caused by allowing
Mathlib's totalized gradient at sample-selected nondifferentiability points. -/
theorem onlineProofExactProcess_refresh_not_wellDefined_counterexample :
    IsLocallySmooth
        (onlineLocalProblem onlineGeneratedRefreshData.problem) (fun _ ↦ 0) ∧
      LegacyOnlineFixedQueryUnbiasedBoundedVariance onlineGeneratedRefreshData.problem
        (fun _ ↦ 1) ∧
      IsUnbiasedQuantizer onlineGeneratedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData onlineGeneratedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ ↦ 0) ∧
      ¬ EstimatorErrorMomentWellDefined
        (onlineLocalProblem onlineGeneratedRefreshData.problem)
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData onlineGeneratedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (onlineProofExactPathLaw
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData)
        2 := by
  rcases onlineGeneratedRefresh_literal_assumptions with
    ⟨hSmooth, hVariance, hQuantizer, hBatch, hAverageSmooth⟩
  refine ⟨hSmooth, hVariance, hQuantizer, hBatch, hAverageSmooth, ?_⟩
  intro hwell
  have hscalar := hwell.aestronglyMeasurable
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw onlineGeneratedRefreshData
  let prefixLaw : Measure (Fin 2 → OnlineGeneratedRefreshRound) :=
    Measure.infinitePi (fun _ : Fin 2 => roundLaw)
  haveI : IsProbabilityMeasure roundLaw := by
    letI (w : Worker onlineCoarseCounterexampleWorkers) :
        IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem
          onlineGeneratedRefreshBatch) := by
      unfold onlineBatchLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (onlineBatchLaw onlineGeneratedRefreshProblem
          onlineGeneratedDifferenceBatch) := by
      unfold onlineBatchLaw
      infer_instance
    letI : IsProbabilityMeasure onlineGeneratedRefreshData.quantizer.law :=
      onlineGeneratedRefreshData.quantizer.law_isProbability
    haveI : IsProbabilityMeasure
        (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
          onlineGeneratedRefreshData.quantizer) := by
      unfold workerCompressionLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible) := by
      unfold refreshLaw
      infer_instance
    unfold roundLaw onlineRoundLaw
    change IsProbabilityMeasure
      ((refreshLaw onlineGeneratedRefreshData.refreshProbability
          onlineGeneratedRefreshData.refresh_admissible).prod
        (((onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedRefreshBatch).prod
            (onlineBatchLaw onlineGeneratedRefreshProblem
              onlineGeneratedDifferenceBatch)).prod
          (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
            onlineGeneratedRefreshData.quantizer)))
    infer_instance
  have hpref : AEStronglyMeasurable
      onlineGeneratedRefreshTimeTwoResidualSq prefixLaw := by
    apply aestronglyMeasurable_prefix_of_comp roundLaw 2
    simpa [roundLaw, onlineProofExactPathLaw,
      onlineGeneratedRefreshTimeTwoResidualSq,
      onlineGeneratedRefreshTwoRoundState, onlineProofExactProcess,
      onlineProofExactRun, SOptLib.recursiveIterateProcess] using hscalar
  have hthreshold : NullMeasurableSet
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        4 < onlineGeneratedRefreshTimeTwoResidualSq pref} prefixLaw := by
    have h := hpref.aemeasurable.nullMeasurableSet_preimage
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (4 : ℝ)))
    simpa only [Set.preimage_setOf_eq] using h
  have hcoin : ∀ᵐ pref ∂prefixLaw, (pref 1).1 = true := by
    simpa [prefixLaw, roundLaw] using
      onlineGeneratedRefreshTimeOneCoin_ae_true
  have hquery : onlineGeneratedRefreshTimeTwoQuery =ᵐ[prefixLaw]
      (fun pref => onlineGeneratedRefreshRoundQueryFormula (pref 0)) := by
    simpa [prefixLaw, roundLaw, onlineGeneratedRefreshRoundQueryFormula,
      onlineGeneratedRefreshQueryFormula] using
        onlineGeneratedRefresh_timeTwo_query_formula_ae
  have hevent :
      ({pref : Fin 2 → OnlineGeneratedRefreshRound |
        4 < onlineGeneratedRefreshTimeTwoResidualSq pref} :
          Set (Fin 2 → OnlineGeneratedRefreshRound)) =ᵐ[prefixLaw]
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 0).1.val ∨
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 1).1.val} := by
    filter_upwards [hcoin, hquery] with pref hc hq
    apply propext
    change (4 < onlineGeneratedRefreshTimeTwoResidualSq pref) ↔
      (onlineGeneratedRefreshRoundQueryFormula (pref 0) =
          ((pref 1).2.1.1 0 0).1.val ∨
        onlineGeneratedRefreshRoundQueryFormula (pref 0) =
          ((pref 1).2.1.1 0 1).1.val)
    rw [onlineGeneratedRefresh_timeTwo_refreshResidual_threshold_preimage pref hc,
      hq]
  have hbad := NullMeasurableSet.congr hthreshold hevent
  exact onlineGeneratedRefresh_union_diagonals_not_nullMeasurable (by
    simpa [prefixLaw, roundLaw] using hbad)

/- RETIRED DIAGNOSTIC (noncurrent superseded route).  This guarded experiment
concluded complete-State AEMeasurability and is intentionally excluded from
the active scalar source route.

/- Direct attempt at the first internal obligation exposed by the literal
proof-exact Eq. (46) source route.  The base case and finite-prefix reduction
are proved from the canonical recursive process and iid prefix law.  The
remaining successor goal is deliberately the exact product-law measurability
of one Algorithm 3 transition under the unchanged literal assumptions. -/
/--
trace: d n b b0 : Count
Sample : Worker n → Type u_1
Ξ : Type u_2
inst✝¹ : (i : Worker n) → MeasurableSpace (Sample i)
inst✝ : MeasurableSpace Ξ
A : OnlineData d n Sample Ξ
x0 : Point d
hBatch : OnlineBatchAdmissible b b0
sigma ell : Worker n → ℝ
hVariance : OnlineUnbiasedBoundedVariance A.problem sigma
hAverageSmooth : OnlineAverageSmoothness A.problem (onlineProofExactProcess A x0 hBatch) ell
law : Measure (ℕ → OnlineRoundNoise n b b0 Sample Ξ) := onlineProofExactPathLaw A
this✝⁷ : ∀ (w : Worker n), IsProbabilityMeasure (A.problem.sampleLaw w) := fun w => A.problem.sampleLaw_isProbability w
this✝⁶ : IsProbabilityMeasure (onlineBatchLaw A.problem b)
this✝⁵ : IsProbabilityMeasure (onlineBatchLaw A.problem b0)
this✝⁴ : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
this✝³ : IsProbabilityMeasure (workerCompressionLaw A.quantizer)
this✝² : IsProbabilityMeasure (refreshLaw A.refreshProbability ⋯)
this✝¹ : IsProbabilityMeasure (onlineRoundLaw A)
this✝ : IsProbabilityMeasure law
fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ := Classical.choice ⋯
hprefix_meas : ∀ (t : ℕ), Measurable (onlineRoundPrefix t)
this : ∀ (t : ℕ), IsProbabilityMeasure (onlineRoundPrefixLaw A t)
k : ℕ
ih : AEMeasurable (onlineProofExactPrefixState A x0 hBatch fallback k) (onlineRoundPrefixLaw A k)
split : (Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ) →
  (Fin k → OnlineRoundNoise n b b0 Sample Ξ) × OnlineRoundNoise n b b0 Sample Ξ :=
  fun pref => (fun j => pref j.castSucc, pref (Fin.last k))
hsplit : Measurable split
hsplitLaw : Measure.map split (onlineRoundPrefixLaw A (k + 1)) = (onlineRoundPrefixLaw A k).prod (onlineRoundLaw A)
⊢ AEMeasurable
    (fun p => onlineStep A (onlineDriverOfRoundNoise p.2) (onlineProofExactPrefixState A x0 hBatch fallback k p.1))
    ((onlineRoundPrefixLaw A k).prod (onlineRoundLaw A))
-/
#guard_msgs (trace, drop error, substring := true) in
theorem onlineProofExactProcess_all_aemeasurable_literal
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem sigma)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ell)
    (k : ℕ) :
    AEMeasurable
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch k)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  have hprefix_meas (t : ℕ) : Measurable
      (onlineRoundPrefix (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) t) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  haveI (t : ℕ) : IsProbabilityMeasure (onlineRoundPrefixLaw A t) := by
    unfold onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map (hprefix_meas t).aemeasurable
  have hpref : AEMeasurable
      (onlineProofExactPrefixState A x0 hBatch fallback k)
      (onlineRoundPrefixLaw A k) := by
    induction k with
    | zero =>
        have hconst : onlineProofExactPrefixState A x0 hBatch fallback 0 =
            fun _ => onlineProofExactInitialState A x0 := by
          funext pref
          rfl
        rw [hconst]
        exact measurable_const.aemeasurable
    | succ k ih =>
        let split : (Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ) →
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ :=
          fun pref => ((fun j => pref j.castSucc), pref (Fin.last k))
        have hsplit : Measurable split := by
          dsimp [split]
          fun_prop
        have hsplitLaw :
            Measure.map split (onlineRoundPrefixLaw A (k + 1)) =
              (onlineRoundPrefixLaw A k).prod (onlineRoundLaw A) := by
          simpa [split] using onlineRoundPrefixLaw_split_succ A k
        have hstep : AEMeasurable
            (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ =>
              onlineStep A (onlineDriverOfRoundNoise p.2)
                (onlineProofExactPrefixState A x0 hBatch fallback k p.1))
            ((onlineRoundPrefixLaw A k).prod (onlineRoundLaw A)) := by
          trace_state
          fun_prop
        have honMap : AEMeasurable
            (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ =>
              onlineStep A (onlineDriverOfRoundNoise p.2)
                (onlineProofExactPrefixState A x0 hBatch fallback k p.1))
            (Measure.map split (onlineRoundPrefixLaw A (k + 1))) := by
          rw [hsplitLaw]
          exact hstep
        have hpull := honMap.comp_aemeasurable hsplit.aemeasurable
        refine hpull.congr (Filter.Eventually.of_forall ?_)
        intro pref
        simpa [split, Function.comp_def] using
          (onlineProofExactPrefixState_succ A x0 hBatch fallback k pref).symm
  have hprefix := (hprefix_meas k).aemeasurable
  have hpull := hpref.comp_aemeasurable hprefix
  change AEMeasurable
    (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch k) law
  refine hpull.congr (Filter.Eventually.of_forall ?_)
  intro path
  apply onlineProofExactProcess_congr_prefix A x0 hBatch k
  intro t ht
  simp [onlineRoundPrefix, onlineExtendRoundPrefix, ht]

-/

/- Direct source-granularity attempt at Eq. (46) for the proof-exact
Algorithm 3 interpretation.  It proves the exact refresh/nonrefresh residual
identity, constructs the refresh product kernel, and performs a
query/residual-specific scalar induction.  At the successor it transports only
the iterate, residual, and step square to the strict-prefix law, consumes the
canonical fixed-fiber nonrefresh moment theorem, proves the generated
innovation square integrable, proves the carried-residual/innovation cross
integral is zero, and establishes the complete nonrefresh integral bound.  The
adaptive refresh residual-square integrability is discharged through an
arbitrary-query product-law theorem.  Independent Boolean gating then gives
the exact Bernoulli coefficients, and component L² closure supplies the next
step certificate.  It calls none of the retired complete-State regularity
declarations and adds no premise or axiom. -/
set_option maxHeartbeats 4000000 in
/-- Simultaneous scalar/component regularity and Eq. (46) history for the
proof-exact Algorithm 3 process.  This is the reusable output of the direct
refresh/nonrefresh induction: it exposes exactly the iterate and residual
measurability, the two component `L²` facts, the two scalar moment
certificates, and all preceding Eq. (46) steps.  In particular it does not
route through complete-`State` prefix measurability. -/
theorem onlineProofExactProcess_scalar_recurrence_components
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path => (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path => (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
        stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    average (fun i : Worker n =>
      A.quantizer.apply
          (onlineBatchDifference A.problem (path k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path k).2.2 i) -
        localGradientDifference P i (run (k + 1) path).x (run k path).x)
  let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    average (fun i : Worker n => average (fun j : Fin b.1 =>
      stochasticGradient A.problem i ((path k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path k).1
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n =>
      A.quantizer.apply
        (onlineBatchDifference A.problem (path k).2.1.2 i xN s.x)
        ((path k).2.2 i)
    have hdiffAvg : average (fun i : Worker n =>
        localGradientDifference P i xN s.x) =
        globalGradient P xN - globalGradient P s.x := by
      rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
        globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : innovation path =
        average q - average (fun i : Worker n =>
          localGradientDifference P i xN s.x) := by
      dsimp [innovation, q, xN, s]
      rw [show (run (k + 1) path).x = xN by rfl]
      unfold average SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n =>
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path k)) s i) -
          globalGradient P xN := by
      rfl
    cases h : branch path with
    | false =>
        simp only [h, Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        change average (fun i : Worker n => s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [h, if_true]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        rfl
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run (k + 1) path).x
  let refreshBatch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (path k).2.1.1
  let batchLaw := onlineBatchLaw A.problem b
  let φ := fun (x : Point d)
      (batch : (i : Worker n) → Fin b.1 → Sample i) =>
    ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
        stochasticGradient A.problem i (batch i j) x)) -
      globalGradient P x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hfixed (x : Point d) :
      Integrable (φ x) batchLaw ∧
        (∫ batch, φ x batch ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [φ, batchLaw, P] using
      (online_fixed_refresh_average_second_moment A x σ hVariance hSmooth.1)
  /- Assumption 3.3's sampled-loss differentiability closes the scalar
  product-law regularity that the preceding attempt left open.  This is the
  complete refresh-error square, not a state-valued wrapper. -/
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw = A.problem.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
  have hsampleDiff (i : Worker n) (j : Fin b.1) :
      ∀ᵐ batch ∂batchLaw,
        Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
    let coord := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
        (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop),
        by rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
          simpa [coord] using hcoord i j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleLossInt (i : Worker n) (j : Fin b.1) (x : Point d) :
      Integrable (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        A.problem.sampleLoss i (batch i j) x) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
        simpa [coord] using hcoord i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        stochasticGradient A.problem i (p.2 i j) p.1)
      ((Measure.map query law).prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i (Measure.map query law) batchLaw id (fun batch => batch i j)
      stronglyMeasurable_id.aestronglyMeasurable
      (hsampleDiff i j) (hsampleLossInt i j)
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1))
      ((Measure.map query law).prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1)))
      ((Measure.map query law).prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        globalGradient P p.1)
      ((Measure.map query law).prod batchLaw) :=
    ((measurable_gradient (globalObjective P)).comp measurable_fst).aestronglyMeasurable
  have hφ : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        φ p.1 p.2) ((Measure.map query law).prod batchLaw) := by
    have hv := havg.sub hglobal
    simpa [φ, pow_two] using hv.norm.mul hv.norm
  /- The direct source route carries only the iterate and residual random
  variables, plus their two scalar L² certificates.  At the successor step it
  transports those components to the strict-prefix law, consumes the
  canonical fixed-fiber Eq. (33)-style calculation, and reaches the Bernoulli
  branch recombination without constructing a measurable complete `State`. -/
  have hScalarComponents : ∀ t,
      AEStronglyMeasurable (fun path => (run t path).x) law ∧
      AEStronglyMeasurable
        (fun path => (run t path).g - globalGradient P (run t path).x) law ∧
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run t path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law t ∧
      StepMomentWellDefined run law t ∧
      ∀ j, j < t →
        estimatorErrorMoment P run law (j + 1) ≤
          (1 - A.refreshProbability) / n.1 *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
    intro t
    induction t with
    | zero =>
        have hx : AEStronglyMeasurable (fun path => (run 0 path).x) law := by
          simpa [run] using
            (aestronglyMeasurable_const : AEStronglyMeasurable
              (fun _ : ℕ → OnlineRoundNoise n b b0 Sample Ξ => x0) law)
        have hr : AEStronglyMeasurable
            (fun path => (run 0 path).g - globalGradient P (run 0 path).x) law := by
          have heq : (fun path =>
              (run 0 path).g - globalGradient P (run 0 path).x) =
              (fun _ => (0 : Point d)) := by
            funext path
            change globalGradient P x0 - globalGradient P x0 = 0
            simp
          rw [heq]
          exact aestronglyMeasurable_const
        have hxl2 : Integrable (fun path => ‖(run 0 path).x - x0‖ ^ 2) law := by
          have heq : (fun path => ‖(run 0 path).x - x0‖ ^ 2) =
              (fun _ => (0 : ℝ)) := by
            funext path
            change ‖x0 - x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (c := (0 : ℝ))
        have hgl2 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) law := by
          have heq : (fun path => ‖(run 0 path).g‖ ^ 2) =
              (fun _ => ‖globalGradient P x0‖ ^ 2) := by
            funext path
            rfl
          rw [heq]
          exact integrable_const (c := ‖globalGradient P x0‖ ^ 2)
        have he : EstimatorErrorMomentWellDefined P run law 0 := by
          rw [EstimatorErrorMomentWellDefined]
          have heq : (fun path =>
              ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
              (fun _ => (0 : ℝ)) := by
            funext path
            change ‖globalGradient P x0 - globalGradient P x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (c := (0 : ℝ))
        have hs : StepMomentWellDefined run law 0 := by
          have heq : (fun path => ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
              (fun _ => ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2) := by
            funext path
            change ‖(x0 - (A.stepSize : ℝ) • globalGradient P x0) - x0‖ ^ 2 = _
            congr 2
            rw [neg_smul]
            abel
          rw [StepMomentWellDefined, heq]
          exact integrable_const
            (c := ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2)
        refine ⟨hx, hr, hxl2, hgl2, he, hs, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
          (run t path).g - globalGradient P (run t path).x
        have hgrad : AEStronglyMeasurable
            (fun path => globalGradient P (run t path).x) law :=
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            ih.1.aemeasurable).aestronglyMeasurable
        have hg : AEStronglyMeasurable (fun path => (run t path).g) law := by
          have hsum := ih.2.1.add hgrad
          refine hsum.congr (Filter.Eventually.of_forall ?_)
          intro path
          dsimp [residual] at hsum ⊢
          abel
        have hxNext : AEStronglyMeasurable
            (fun path => (run (t + 1) path).x) law := by
          have hstep := ih.1.sub (hg.const_smul (A.stepSize : ℝ))
          simpa [run, onlineProofExactProcess_succ, onlineStep, primalStep_eq] using hstep
        let prefixMap := onlineRoundPrefix
          (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) t
        let prefixLaw := Measure.map prefixMap law
        let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
        let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
          ((path t).2.1.2, (path t).2.2)
        let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
        let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
          Classical.choice (nonempty_of_isProbabilityMeasure law)
        let prefixState := onlineProofExactPrefixState A x0 hBatch fallback t
        let x := fun pref => (prefixState pref).x
        let xNext := fun pref => primalStep A.stepSize (prefixState pref)
        let direction := fun pref =>
          (prefixState pref).g - globalGradient P (prefixState pref).x
        let innovationKernel := fun
            (pref : Fin t → OnlineRoundNoise n b b0 Sample Ξ)
            (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          average (fun i : Worker n =>
            A.quantizer.apply
                (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
                (q.2 i) -
              localGradientDifference P i (xNext pref) (x pref))
        let C := (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
        let B := fun pref => C * ‖xNext pref - x pref‖ ^ 2
        have hprefix : Measurable prefixMap := by
          dsimp [prefixMap, onlineRoundPrefix]
          exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
        haveI : IsProbabilityMeasure prefixLaw :=
          Measure.isProbabilityMeasure_map hprefix.aemeasurable
        have hstatePrefix : ∀ path, prefixState (prefixMap path) = run t path := by
          intro path
          dsimp [prefixState, prefixMap, run]
          exact (onlineProofExactProcess_congr_prefix A x0 hBatch t
            (path := path)
            (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix t path))
            (by
              intro j hj
              simp [onlineExtendRoundPrefix, onlineRoundPrefix, hj])).symm
        have hxPrefix : AEStronglyMeasurable x prefixLaw := by
          have hcomp : AEStronglyMeasurable
              (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
                x (fun j : Fin t => path j.1)) law := by
            refine ih.1.congr (Filter.Eventually.of_forall ?_)
            intro path
            simpa [prefixMap, onlineRoundPrefix, x] using
              congrArg State.x (hstatePrefix path).symm
          have hfinite := aestronglyMeasurable_prefix_of_comp_general
            roundLaw t x (by
              simpa [law, roundLaw, onlineProofExactPathLaw] using hcomp)
          have hprefixLaw : prefixLaw =
              Measure.infinitePi (fun _ : Fin t => roundLaw) := by
            simpa [prefixLaw, prefixMap, law, roundLaw, onlineProofExactPathLaw,
              onlineRoundPrefix] using iidStream_prefix_map_eq_infinitePi roundLaw t
          rw [hprefixLaw]
          exact hfinite
        have hdirection : AEStronglyMeasurable direction prefixLaw := by
          have hcomp : AEStronglyMeasurable
              (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
                direction (fun j : Fin t => path j.1)) law := by
            refine ih.2.1.congr (Filter.Eventually.of_forall ?_)
            intro path
            simpa [prefixMap, onlineRoundPrefix, direction] using
              congrArg
                (fun s : State d => s.g - globalGradient P s.x)
                (hstatePrefix path).symm
          have hfinite := aestronglyMeasurable_prefix_of_comp_general
            roundLaw t direction (by
              simpa [law, roundLaw, onlineProofExactPathLaw] using hcomp)
          have hprefixLaw : prefixLaw =
              Measure.infinitePi (fun _ : Fin t => roundLaw) := by
            simpa [prefixLaw, prefixMap, law, roundLaw, onlineProofExactPathLaw,
              onlineRoundPrefix] using iidStream_prefix_map_eq_infinitePi roundLaw t
          rw [hprefixLaw]
          exact hfinite
        have hxNextPrefix : AEStronglyMeasurable xNext prefixLaw := by
          have hgradPrefix : AEStronglyMeasurable
              (fun pref => globalGradient P (x pref)) prefixLaw :=
            ((measurable_gradient (globalObjective P)).comp_aemeasurable
              hxPrefix.aemeasurable).aestronglyMeasurable
          have hgPrefix : AEStronglyMeasurable
              (fun pref => (prefixState pref).g) prefixLaw := by
            have hsum := hdirection.add hgradPrefix
            refine hsum.congr (Filter.Eventually.of_forall ?_)
            intro pref
            dsimp [direction, x]
            abel
          have hstep := hxPrefix.sub (hgPrefix.const_smul (A.stepSize : ℝ))
          simpa [xNext, x, primalStep_eq] using hstep
        have hkernel : AEStronglyMeasurable
            (fun p => innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
          let hE : OnlineExpectationRealization A.problem :=
            onlineExpectationRealization A.problem
          simpa [innovationKernel, xNext, x, noiseLaw,
            onlineCorrectedFixedWorkerInnovation,
            onlineLocalProblemCorrected_eq_onlineLocalProblem] using
            (online_corrected_nonrefresh_average_product_aestronglyMeasurable
              (b0 := b0) A hE σ hVariance prefixLaw xNext x
              hxNextPrefix hxPrefix)
        have hfixed (pref) :=
          online_proofExact_fixed_nonrefresh_average_second_moment
            (b0 := b0) A (xNext pref) (x pref) Llocal ℒlocal σ ω
            hSmooth hVariance
            (fun i => by
              simpa [xNext, x, prefixState, onlineProofExactPrefixState,
                onlineProofExactProcess_succ, onlineStep] using
                hAverageSmooth.2 t i (onlineExtendRoundPrefix fallback pref))
            hQuantizer
        have hStepPrefix : Integrable
            (fun pref => ‖xNext pref - x pref‖ ^ 2) prefixLaw := by
          have hcomp : Integrable
              (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
                ‖xNext (fun j : Fin t => path j.1) -
                  x (fun j : Fin t => path j.1)‖ ^ 2) law := by
            refine ih.2.2.2.2.2.1.congr (Filter.Eventually.of_forall ?_)
            intro path
            dsimp [StepMomentWellDefined]
            congr 2
            rw [show x (fun j : Fin t => path j.1) = (run t path).x by
              simpa [prefixMap, onlineRoundPrefix, x] using
                congrArg State.x (hstatePrefix path)]
            rw [show xNext (fun j : Fin t => path j.1) = (run (t + 1) path).x by
              dsimp [xNext]
              rw [show prefixState (fun j : Fin t => path j.1) = run t path by
                simpa [prefixMap, onlineRoundPrefix] using hstatePrefix path]
              rfl]
          have hfinite := integrable_prefix_of_comp_general roundLaw t
            (fun pref => ‖xNext pref - x pref‖ ^ 2) (by
              simpa [law, roundLaw, onlineProofExactPathLaw] using hcomp)
          have hprefixLaw : prefixLaw =
              Measure.infinitePi (fun _ : Fin t => roundLaw) := by
            simpa [prefixLaw, prefixMap, law, roundLaw, onlineProofExactPathLaw,
              onlineRoundPrefix] using iidStream_prefix_map_eq_infinitePi roundLaw t
          rw [hprefixLaw]
          exact hfinite
        have hB : Integrable B prefixLaw := by
          simpa [B] using hStepPrefix.const_mul C
        haveI : IsProbabilityMeasure noiseLaw := by
          unfold noiseLaw onlineDifferenceCompressionLaw
          infer_instance
        have hkernelSq : AEStronglyMeasurable
            (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
            (prefixLaw.prod noiseLaw) := by
          simpa [pow_two] using hkernel.norm.mul hkernel.norm
        have hproductInnovationSq : Integrable
            (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
            (prefixLaw.prod noiseLaw) := by
          rw [integrable_prod_iff hkernelSq]
          refine ⟨Filter.Eventually.of_forall (fun pref => (hfixed pref).2.2.1), ?_⟩
          refine Integrable.mono hB
            (hkernelSq.norm.integral_prod_right') (Filter.Eventually.of_forall ?_)
          intro pref
          have hb := (hfixed pref).2.2.2
          have hBnonneg : 0 ≤ B pref :=
            (integral_nonneg fun _ => sq_nonneg _).trans hb
          rw [Real.norm_of_nonneg hBnonneg]
          have heq : (fun q => ‖‖innovationKernel pref q‖ ^ 2‖) =
              (fun q => ‖innovationKernel pref q‖ ^ 2) := by
            funext q
            rw [Real.norm_of_nonneg (sq_nonneg _)]
          rw [heq, Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
          simpa [B, C] using hb
        have hFresh :=
          onlineProofExact_nonrefreshParameter_indep_noise_of_components
            A x0 hBatch t ih.1 ih.2.1
        let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t
        let noiseOfRound := fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          (z.2.1.2, z.2.2)
        have hcurrent : Measurable current := measurable_pi_apply t
        have hnoiseOfRound : Measurable noiseOfRound := by
          dsimp [noiseOfRound]
          fun_prop
        have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
          apply indepFun_of_map_prod_eq_prod_laws
            (P := law) (Z := fun path => (prefixMap path, current path))
            (mu := prefixLaw) (nu := roundLaw)
          · exact (hprefix.prodMk hcurrent).aemeasurable
          · simpa [prefixMap, current, prefixLaw, roundLaw, law,
              onlineProofExactPathLaw, SOptLib.iidStreamLaw, onlineRoundPrefix] using
              (infinitePi_prefix_current_map_eq_prod
                (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) t)
        have hfreshPrefix : ProbabilityTheory.IndepFun prefixMap noise law := by
          simpa [noise, current, noiseOfRound, Function.comp_def] using
            hpastCurrent.comp measurable_id hnoiseOfRound
        have hnoise : AEMeasurable noise law := by
          dsimp [noise]
          fun_prop
        have hnoiseLaw : Measure.map noise law = noiseLaw := by
          simpa [noiseLaw] using hFresh.2.2
        have hjoint : AEMeasurable (fun path => (prefixMap path, noise path)) law :=
          hprefix.aemeasurable.prodMk hnoise
        have hjointLaw : Measure.map (fun path => (prefixMap path, noise path)) law =
            prefixLaw.prod noiseLaw := by
          rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
            hprefix.aemeasurable hnoise).mp hfreshPrefix, hnoiseLaw]
        let innovation := fun path => innovationKernel (prefixMap path) (noise path)
        have hInnovationSq : Integrable
            (fun path => ‖innovation path‖ ^ 2) law := by
          have honMap : Integrable
              (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
              (Measure.map (fun path => (prefixMap path, noise path)) law) := by
            rw [hjointLaw]
            exact hproductInnovationSq
          have hcomp := (MeasureTheory.integrable_map_measure
            (by
              rw [hjointLaw]
              exact hkernelSq)
            hjoint).mp honMap
          simpa [innovation, Function.comp_def] using hcomp
        have hInnovationMeas : AEStronglyMeasurable innovation law := by
          have hkernelMapped : AEStronglyMeasurable
              (fun p => innovationKernel p.1 p.2)
              ((Measure.map prefixMap law).prod (Measure.map noise law)) := by
            rw [hnoiseLaw]
            simpa [prefixLaw] using hkernel
          have hcomp := aestronglyMeasurable_comp_of_indep_product_law
            hprefix.aemeasurable hnoise
            (inferInstance : SigmaFinite (Measure.map prefixMap law))
            (inferInstance : SigmaFinite (Measure.map noise law))
            hfreshPrefix hkernelMapped
          simpa [innovation, Function.comp_def] using hcomp
        have hResidualSq : Integrable (fun path => ‖residual path‖ ^ 2) law := by
          simpa [residual, EstimatorErrorMomentWellDefined] using ih.2.2.2.2.1
        have hInnerInt : Integrable
            (fun path => ⟪residual path, innovation path⟫_ℝ) law :=
          integrable_inner_of_integrable_sq_norm ih.2.1 hInnovationMeas
            hResidualSq hInnovationSq
        have hscalarProduct : AEStronglyMeasurable
            (fun p => ⟪direction p.1, innovationKernel p.1 p.2⟫_ℝ)
            (prefixLaw.prod noiseLaw) :=
          hdirection.comp_fst.inner hkernel
        have hinnerComp : ∀ path,
            ⟪direction (prefixMap path), innovationKernel (prefixMap path) (noise path)⟫_ℝ =
              ⟪residual path, innovation path⟫_ℝ := by
          intro path
          dsimp [direction, residual, innovation]
          rw [hstatePrefix path]
        have hfixedInnerZero : ∀ pref,
            (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) = 0 := by
          intro pref
          have hlin := ContinuousLinearMap.integral_comp_comm
            (L := (innerSL ℝ) (direction pref)) (hfixed pref).1
          calc
            (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) =
                (innerSL ℝ) (direction pref)
                  (∫ q, innovationKernel pref q ∂noiseLaw) := hlin
            _ = 0 := by rw [(hfixed pref).2.1]; simp
        have hCross :
            (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
          have hcompInt : Integrable
              (fun path => ⟪direction (prefixMap path),
                innovationKernel (prefixMap path) (noise path)⟫_ℝ) law :=
            hInnerInt.congr (Filter.Eventually.of_forall fun path =>
              (hinnerComp path).symm)
          have hzero :=
            integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
              (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
              (φ := fun pref q => ⟪direction pref, innovationKernel pref q⟫_ℝ)
              (by simpa [prefixLaw] using hscalarProduct)
              hprefix.aemeasurable hnoise hfreshPrefix hnoiseLaw hcompInt
              hfixedInnerZero
          rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
              ∫ path, ⟪direction (prefixMap path),
                innovationKernel (prefixMap path) (noise path)⟫_ℝ ∂law by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun path => (hinnerComp path).symm]
          exact hzero
        have hNonrefreshInt : Integrable
            (fun path => ‖residual path + innovation path‖ ^ 2) law :=
          integrable_sq_norm_add ih.2.1 hInnovationMeas hResidualSq hInnovationSq
        have hNonrefreshEq :
            (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
              (∫ path, ‖residual path‖ ^ 2 ∂law) +
                ∫ path, ‖innovation path‖ ^ 2 ∂law := by
          let pair : Bool → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) → Point d :=
            fun z => if z then innovation else residual
          have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
            law (Finset.univ : Finset Bool) pair
            (fun z _ => by
              cases z with
              | false =>
                  change AEStronglyMeasurable residual law
                  exact ih.2.1
              | true =>
                  change AEStronglyMeasurable innovation law
                  exact hInnovationMeas)
            (fun z _ => by
              cases z with
              | false =>
                  change Integrable (fun path => ‖residual path‖ ^ 2) law
                  exact hResidualSq
              | true =>
                  change Integrable (fun path => ‖innovation path‖ ^ 2) law
                  exact hInnovationSq)
            (fun z _ w _ hzw => by
              cases z <;> cases w
              · exact False.elim (hzw rfl)
              · simpa [pair] using hCross
              · simpa [pair, real_inner_comm] using hCross
              · exact False.elim (hzw rfl))
          simpa [pair, Fintype.sum_bool, add_comm] using hsum
        have hBMeas : AEStronglyMeasurable B prefixLaw := hB.aestronglyMeasurable
        have hBComp : Integrable (fun path => B (prefixMap path)) law := by
          have hs := ih.2.2.2.2.2.1.const_mul C
          apply hs.congr
          filter_upwards [] with path
          dsimp [B, xNext, x, prefixState, prefixMap, run]
          rw [onlineProofExactProcess_succ]
          have heq := onlineProofExactProcess_congr_prefix A x0 hBatch t
            (path := path)
            (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix t path))
            (by
              intro j hj
              simp [onlineExtendRoundPrefix, onlineRoundPrefix, hj])
          rw [heq]
          rfl
        have hInnovationBound :
            (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
              C * stepMoment run law t := by
          have hbound :=
            integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
              (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
              (φ := fun pref q => ‖innovationKernel pref q‖ ^ 2) (B := B)
              (by simpa [prefixLaw] using hkernelSq) hBMeas
              hprefix.aemeasurable hnoise hfreshPrefix hnoiseLaw
              hInnovationSq hBComp
              (fun pref => by simpa [B, C] using (hfixed pref).2.2.2)
          calc
            (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
                ∫ path, B (prefixMap path) ∂law := by
                  simpa [innovation] using hbound
            _ = C * stepMoment run law t := by
              unfold stepMoment
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with path
              dsimp [B, xNext, x, prefixState, prefixMap, run]
              rw [onlineProofExactProcess_succ]
              have heq := onlineProofExactProcess_congr_prefix A x0 hBatch t
                (path := path)
                (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix t path))
                (by
                  intro j hj
                  simp [onlineExtendRoundPrefix, onlineRoundPrefix, hj])
              rw [heq]
              rfl
        have hNonrefreshBound :
            (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
              estimatorErrorMoment P run law t + C * stepMoment run law t := by
          rw [hNonrefreshEq]
          change estimatorErrorMoment P run law t +
              (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ _
          exact add_le_add_right hInnovationBound _
        let refreshErrorAt :=
          fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            average (fun i : Worker n => average (fun j : Fin b.1 =>
              stochasticGradient A.problem i ((path t).2.1.1 i j)
                (run (t + 1) path).x)) -
              globalGradient P (run (t + 1) path).x
        have hRefreshAt : Integrable
            (fun path => ‖refreshErrorAt path‖ ^ 2) law := by
          let queryAt := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            (run (t + 1) path).x
          let refreshBatchAt :=
            fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
              (path t).2.1.1
          have hqueryAt : AEStronglyMeasurable queryAt law := by
            simpa [queryAt] using hxNext
          have hqueryRefreshAt : ProbabilityTheory.IndepFun
              queryAt refreshBatchAt law := by
            have hindep := hFresh.1.comp
              (show Measurable
                (fun p : (Point d × Point d) × Point d => p.1.1) by fun_prop)
              (show Measurable
                (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) by fun_prop)
            simpa [queryAt, refreshBatchAt] using hindep
          have hrefreshBatchAtAE : AEMeasurable refreshBatchAt law := by
            exact ((measurable_fst.comp (measurable_fst.comp
              (measurable_snd.comp (measurable_pi_apply t))))).aemeasurable
          have hrefreshBatchAtLaw :
              Measure.map refreshBatchAt law = batchLaw := by
            calc
              Measure.map refreshBatchAt law =
                  Measure.map
                    (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                    (Measure.map
                      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t)
                      law) := by
                        rw [MeasureTheory.Measure.map_map]
                        · rfl
                        · fun_prop
                        · exact measurable_pi_apply t
              _ = Measure.map
                    (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                    (onlineRoundLaw A) := by
                      rw [show Measure.map
                          (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t)
                          law = onlineRoundLaw A by
                        simpa [law, onlineProofExactPathLaw] using
                          SOptLib.iidStreamLaw_map_eval
                            (onlineRoundLaw (b := b) (b0 := b0) A) t]
              _ = batchLaw := by
                simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
                  (b0 := b0) A
          have hφAt : AEStronglyMeasurable
              (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
                φ p.1 p.2) ((Measure.map queryAt law).prod batchLaw) := by
            letI : IsProbabilityMeasure (Measure.map queryAt law) :=
              Measure.isProbabilityMeasure_map hqueryAt.aemeasurable
            simpa [φ, P, batchLaw] using
              (online_refresh_average_sq_product_aestronglyMeasurable
                (b := b) A σ hVariance (Measure.map queryAt law))
          have hrefreshFixed (z : Point d) :
              Integrable (φ z) batchLaw ∧
                (∫ batch, φ z batch ∂batchLaw) ≤
                  varianceAggregateSq σ / (n.1 * b.1) := by
            simpa [φ, batchLaw, P] using
              (online_fixed_refresh_average_second_moment
                (b := b) A z σ hVariance hSmooth.1)
          have hcomp : Integrable
              (fun path => φ (queryAt path) (refreshBatchAt path)) law :=
            integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
              (P := law) (ν := batchLaw) (X := queryAt) (Y := refreshBatchAt)
              (C := varianceAggregateSq σ / (n.1 * b.1)) hφAt
              hqueryAt.aemeasurable hrefreshBatchAtAE hqueryRefreshAt
              hrefreshBatchAtLaw (fun _ _ => sq_nonneg _)
              (fun z => (hrefreshFixed z).1) (fun z => (hrefreshFixed z).2)
          simpa [refreshErrorAt, queryAt, refreshBatchAt, φ] using hcomp
        let queryAt := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
          (run (t + 1) path).x
        let refreshBatchAt :=
          fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path t).2.1.1
        have hqueryAt : AEStronglyMeasurable queryAt law := by
          simpa [queryAt] using hxNext
        have hqueryRefreshAt : ProbabilityTheory.IndepFun
            queryAt refreshBatchAt law := by
          have hindep := hFresh.1.comp
            (show Measurable
              (fun p : (Point d × Point d) × Point d => p.1.1) by fun_prop)
            (show Measurable
              (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) by fun_prop)
          simpa [queryAt, refreshBatchAt] using hindep
        have hrefreshBatchAtAE : AEMeasurable refreshBatchAt law := by
          exact ((measurable_fst.comp (measurable_fst.comp
            (measurable_snd.comp (measurable_pi_apply t))))).aemeasurable
        have hrefreshBatchAtLaw : Measure.map refreshBatchAt law = batchLaw := by
          calc
            Measure.map refreshBatchAt law =
                Measure.map
                  (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                  (Measure.map
                    (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t)
                    law) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · fun_prop
                      · exact measurable_pi_apply t
            _ = Measure.map
                  (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                  (onlineRoundLaw A) := by
                    rw [show Measure.map
                        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t)
                        law = onlineRoundLaw A by
                      simpa [law, onlineProofExactPathLaw] using
                        SOptLib.iidStreamLaw_map_eval
                          (onlineRoundLaw (b := b) (b0 := b0) A) t]
            _ = batchLaw := by
              simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
                (b0 := b0) A
        have hRefreshBoundAt :
            (∫ path, ‖refreshErrorAt path‖ ^ 2 ∂law) ≤
              varianceAggregateSq σ / (n.1 * b.1) := by
          have hφAt : AEStronglyMeasurable
              (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
                φ p.1 p.2) ((Measure.map queryAt law).prod batchLaw) := by
            letI : IsProbabilityMeasure (Measure.map queryAt law) :=
              Measure.isProbabilityMeasure_map hqueryAt.aemeasurable
            simpa [φ, P, batchLaw] using
              (online_refresh_average_sq_product_aestronglyMeasurable
                (b := b) A σ hVariance (Measure.map queryAt law))
          have hrefreshFixed (z : Point d) :
              Integrable (φ z) batchLaw ∧
                (∫ batch, φ z batch ∂batchLaw) ≤
                  varianceAggregateSq σ / (n.1 * b.1) := by
            simpa [φ, batchLaw, P] using
              (online_fixed_refresh_average_second_moment
                (b := b) A z σ hVariance hSmooth.1)
          have hcomp : Integrable
              (fun path => φ (queryAt path) (refreshBatchAt path)) law := by
            simpa [refreshErrorAt, queryAt, refreshBatchAt, φ] using hRefreshAt
          have hbound :=
            integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
              (P := law) (ν := batchLaw) (X := queryAt) (Y := refreshBatchAt)
              hφAt hqueryAt.aemeasurable hrefreshBatchAtAE hqueryRefreshAt
              hrefreshBatchAtLaw hcomp (fun z => (hrefreshFixed z).2)
          simpa [refreshErrorAt, queryAt, refreshBatchAt, φ] using hbound
        have hRefreshVectorAt : AEStronglyMeasurable refreshErrorAt law := by
          have hkernel : AEStronglyMeasurable
              (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
                average (fun i : Worker n => average (fun j : Fin b.1 =>
                    stochasticGradient A.problem i (p.2 i j) p.1)) -
                  globalGradient P p.1)
              ((Measure.map queryAt law).prod (Measure.map refreshBatchAt law)) := by
            rw [hrefreshBatchAtLaw]
            letI : IsProbabilityMeasure (Measure.map queryAt law) :=
              Measure.isProbabilityMeasure_map hqueryAt.aemeasurable
            simpa [P, batchLaw] using
              (online_refresh_average_product_aestronglyMeasurable
                (b := b) A σ hVariance (Measure.map queryAt law))
          have hcomp := aestronglyMeasurable_comp_of_indep_product_law
            hqueryAt.aemeasurable hrefreshBatchAtAE
            (inferInstance : SigmaFinite (Measure.map queryAt law))
            (inferInstance : SigmaFinite (Measure.map refreshBatchAt law))
            hqueryRefreshAt hkernel
          simpa [refreshErrorAt, queryAt, refreshBatchAt] using hcomp
        let nextResidualAt :=
          fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            (run (t + 1) path).g - globalGradient P (run (t + 1) path).x
        have hdecompAt : ∀ path, nextResidualAt path =
            if (path t).1 then refreshErrorAt path
            else residual path + innovation path := by
          intro path
          let s := run t path
          let xN := primalStep A.stepSize s
          let q := fun i : Worker n =>
            A.quantizer.apply
              (onlineBatchDifference A.problem (path t).2.1.2 i xN s.x)
              ((path t).2.2 i)
          have hdiffAvg : average (fun i : Worker n =>
              localGradientDifference P i xN s.x) =
              globalGradient P xN - globalGradient P s.x := by
            rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
              globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
            unfold averageLocalGradient localGradientDifference average
              SOptLib.finiteUniformAverage
            rw [Finset.sum_sub_distrib, smul_sub]
          have hinnovationAvg : innovation path =
              average q - average (fun i : Worker n =>
                localGradientDifference P i xN s.x) := by
            dsimp [innovation, innovationKernel, noise, xNext, x, q, xN, s]
            rw [hstatePrefix path]
            unfold average SOptLib.finiteUniformAverage
            rw [Finset.sum_sub_distrib, smul_sub]
          have hnext : nextResidualAt path =
              average (fun i : Worker n =>
                onlineWorkerEstimator A (onlineDriverOfRoundNoise (path t)) s i) -
                globalGradient P xN := by
            rfl
          cases h : (path t).1 with
          | false =>
              simp only [h, Bool.false_eq_true, if_false]
              rw [hnext]
              simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, h, if_false]
              change average (fun i : Worker n => s.g + q i) -
                  globalGradient P xN = residual path + innovation path
              rw [average_const_add, hinnovationAvg, hdiffAvg]
              dsimp [residual, s]
              abel
          | true =>
              simp only [h, if_true]
              rw [hnext]
              simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, h, if_true]
              rfl
        have hNextError : EstimatorErrorMomentWellDefined P run law (t + 1) := by
          let s : Set (ℕ → OnlineRoundNoise n b b0 Sample Ξ) :=
            {path | (path t).1 = true}
          have hs : MeasurableSet s := by
            dsimp [s]
            exact (measurable_fst.comp (measurable_pi_apply t))
              (measurableSet_singleton true)
          have hpiece := Integrable.piecewise hs
            hRefreshAt.integrableOn hNonrefreshInt.integrableOn
          have heq : s.piecewise
                (fun path => ‖refreshErrorAt path‖ ^ 2)
                (fun path => ‖residual path + innovation path‖ ^ 2) =
              (fun path => ‖nextResidualAt path‖ ^ 2) := by
            funext path
            by_cases hp : (path t).1 = true
            · simp [s, Set.piecewise, hp, hdecompAt path]
            · have hf : (path t).1 = false := Bool.eq_false_of_not_eq_true hp
              simp [s, Set.piecewise, hp, hf, hdecompAt path]
          rw [EstimatorErrorMomentWellDefined, ← heq]
          exact hpiece
        have hNextResidualMeas : AEStronglyMeasurable nextResidualAt law := by
          let s : Set (ℕ → OnlineRoundNoise n b b0 Sample Ξ) :=
            {path | (path t).1 = true}
          have hs : MeasurableSet s := by
            dsimp [s]
            exact (measurable_fst.comp (measurable_pi_apply t))
              (measurableSet_singleton true)
          have hNonrefreshMeas : AEStronglyMeasurable
              (fun path => residual path + innovation path) law := by
            simpa [residual] using ih.2.1.add hInnovationMeas
          have hpiece := (hRefreshVectorAt.mono_measure Measure.restrict_le_self).piecewise hs
            (hNonrefreshMeas.mono_measure Measure.restrict_le_self)
          refine hpiece.congr (Filter.Eventually.of_forall ?_)
          intro path
          by_cases hp : (path t).1 = true
          · simp [s, Set.piecewise, hp, hdecompAt path]
          · have hf : (path t).1 = false := Bool.eq_false_of_not_eq_true hp
            simp [s, Set.piecewise, hp, hf, hdecompAt path]
        have hxL2Succ : Integrable
            (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
          have h := integrable_sq_norm_sub_smul_sub_const_of_l2
            (fun path => (run t path).x) (fun path => (run t path).g)
            x0 (A.stepSize : ℝ) ih.1 hg ih.2.2.1 ih.2.2.2.1
          simpa [run, onlineProofExactProcess_succ, onlineStep, primalStep_eq] using h
        have hglobalSucc : Integrable
            (fun path => ‖globalGradient P (run (t + 1) path).x‖ ^ 2) law := by
          have hGlobal := GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
          apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
            x0 (globalGradient P) (rootMeanSquare Llocal)
              (fun path => (run (t + 1) path).x) hxNext
          · simpa [norm_sub_rev] using hxL2Succ
          · intro x y
            exact hGlobal.2 y x
        have hgL2Succ : Integrable (fun path => ‖(run (t + 1) path).g‖ ^ 2) law := by
          have hgradMeas : AEStronglyMeasurable
              (fun path => globalGradient P (run (t + 1) path).x) law :=
            ((measurable_gradient (globalObjective P)).comp_aemeasurable
              hxNext.aemeasurable).aestronglyMeasurable
          have hadd := integrable_sq_norm_add hNextResidualMeas hgradMeas
            (by simpa [nextResidualAt, EstimatorErrorMomentWellDefined] using hNextError)
            hglobalSucc
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          dsimp [nextResidualAt]
          abel
        have hStepSucc : StepMomentWellDefined run law (t + 1) := by
          have hscaled := integrable_sq_norm_const_smul (-(A.stepSize : ℝ)) hgL2Succ
          simpa [StepMomentWellDefined, run, onlineProofExactProcess_succ,
            onlineStep, primalStep_eq] using hscaled
        let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
        let restLaw := ((onlineBatchLaw A.problem b).prod
          (onlineBatchLaw A.problem b0)).prod
            (workerCompressionLaw (n := n) A.quantizer)
        let projectNoise := fun r :
            ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
          (r.1.2, r.2)
        haveI : IsProbabilityMeasure restLaw := by
          dsimp [restLaw]
          infer_instance
        have hprojectNoise : Measurable projectNoise := by
          dsimp [projectNoise]
          fun_prop
        have hprojectNoiseLaw : Measure.map projectNoise restLaw = noiseLaw := by
          dsimp [projectNoise, restLaw, noiseLaw, onlineDifferenceCompressionLaw]
          simpa using
            (MeasureTheory.Measure.map_prod_map
              ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0))
              (workerCompressionLaw (n := n) A.quantizer)
              measurable_snd measurable_id).symm
        let nonrefreshKernelRest := fun
            (pref : Fin t → OnlineRoundNoise n b b0 Sample Ξ)
            (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) =>
          ‖direction pref + innovationKernel pref (projectNoise r)‖ ^ 2
        have hNonrefreshKernelRest : AEStronglyMeasurable
            (Function.uncurry nonrefreshKernelRest) (prefixLaw.prod restLaw) := by
          let pull := fun p :
              (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                ((((w : Worker n) → Fin b.1 → Sample w) ×
                  ((w : Worker n) → Fin b0.1 → Sample w)) ×
                    (Worker n → Ξ)) => (p.1, projectNoise p.2)
          have hpull : Measurable pull := by dsimp [pull]; fun_prop
          have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
              prefixLaw.prod noiseLaw := by
            have hmap := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
              measurable_id hprojectNoise
            rw [Measure.map_id, hprojectNoiseLaw] at hmap
            simpa [pull] using hmap.symm
          have hbase : AEStronglyMeasurable
              (fun p => ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
              (prefixLaw.prod noiseLaw) := by
            have hv := hdirection.comp_fst.add hkernel
            simpa [pow_two] using hv.norm.mul hv.norm
          have hqmp : Measure.QuasiMeasurePreserving pull
              (prefixLaw.prod restLaw) (prefixLaw.prod noiseLaw) :=
            ⟨hpull, by rw [hpullLaw]⟩
          simpa [nonrefreshKernelRest, Function.uncurry, pull] using
            hbase.comp_quasiMeasurePreserving hqmp
        have hNonrefreshIndep : ProbabilityTheory.IndepFun
            (fun path => ‖residual path + innovation path‖ ^ 2)
            (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path t).1)
            law := by
          have h := iidStream_prefix_current_snd_kernel_indep_fst
            coinLaw restLaw t nonrefreshKernelRest
            (by
              have hprefixLawEq : prefixLaw =
                  Measure.infinitePi
                    (fun _ : Fin t => coinLaw.prod restLaw) := by
                simpa [prefixLaw, prefixMap, law, roundLaw, coinLaw, restLaw,
                  onlineProofExactPathLaw, onlineRoundLaw] using
                  iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) t
              rw [← hprefixLawEq]
              exact hNonrefreshKernelRest)
          apply h.congr (Filter.Eventually.of_forall ?_)
            (Filter.Eventually.of_forall fun _ => rfl)
          intro path
          change ‖direction (prefixMap path) +
              innovationKernel (prefixMap path) (noise path)‖ ^ 2 =
            ‖residual path + innovation path‖ ^ 2
          dsimp [direction, residual]
          rw [hstatePrefix path]
        let refreshKernelRest := fun
            (pref : Fin t → OnlineRoundNoise n b b0 Sample Ξ)
            (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) =>
          ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
              stochasticGradient A.problem i (r.1.1 i j) (xNext pref))) -
            globalGradient P (xNext pref)‖ ^ 2
        have hRefreshKernelRest : AEStronglyMeasurable
            (Function.uncurry refreshKernelRest) (prefixLaw.prod restLaw) := by
          let refreshKernelPrefixBatch := fun p :
              (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                ((w : Worker n) → Fin b.1 → Sample w) =>
            ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
                stochasticGradient A.problem i (p.2 i j) (xNext p.1))) -
              globalGradient P (xNext p.1)‖ ^ 2
          have hRefreshPrefixBatch : AEStronglyMeasurable
              refreshKernelPrefixBatch (prefixLaw.prod batchLaw) := by
            let X := fun p : (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                ((w : Worker n) → Fin b.1 → Sample w) => xNext p.1
            let Y := fun p : (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                ((w : Worker n) → Fin b.1 → Sample w) => p.2
            have hX : AEMeasurable X (prefixLaw.prod batchLaw) :=
              hxNextPrefix.comp_fst.aemeasurable
            have hY : AEMeasurable Y (prefixLaw.prod batchLaw) :=
              measurable_snd.aemeasurable
            have hXY : ProbabilityTheory.IndepFun X Y
                (prefixLaw.prod batchLaw) := by
              let xMk := hxNextPrefix.mk xNext
              have hxMk : Measurable xMk := hxNextPrefix.measurable_mk
              have hindepMk := (ProbabilityTheory.indepFun_prod
                (μ := prefixLaw) (ν := batchLaw) hxMk measurable_id)
              have hxae : X =ᵐ[prefixLaw.prod batchLaw]
                  (fun p => xMk p.1) := by
                have hpull := (Measure.quasiMeasurePreserving_fst
                  (μ := prefixLaw) (ν := batchLaw))
                exact hpull.tendsto_ae hxNextPrefix.ae_eq_mk
              apply hindepMk.congr hxae.symm (Filter.Eventually.of_forall fun _ => rfl)
            haveI : IsProbabilityMeasure (Measure.map X (prefixLaw.prod batchLaw)) :=
              Measure.isProbabilityMeasure_map hX
            have hmapX : Measure.map X (prefixLaw.prod batchLaw) =
                Measure.map xNext prefixLaw := by
              have hxMap : AEMeasurable xNext
                  (Measure.map Prod.fst (prefixLaw.prod batchLaw)) := by
                rw [Measure.map_fst_prod, measure_univ, one_smul]
                exact hxNextPrefix.aemeasurable
              calc
                Measure.map X (prefixLaw.prod batchLaw) =
                    Measure.map xNext
                      (Measure.map Prod.fst (prefixLaw.prod batchLaw)) := by
                      dsimp [X]
                      exact (AEMeasurable.map_map_of_aemeasurable
                        hxMap measurable_fst.aemeasurable).symm
                _ = Measure.map xNext prefixLaw := by
                  rw [Measure.map_fst_prod, measure_univ, one_smul]
            have hmapY : Measure.map Y (prefixLaw.prod batchLaw) = batchLaw := by
              dsimp [Y]
              rw [Measure.map_snd_prod, measure_univ, one_smul]
            have hbase : AEStronglyMeasurable
                (fun p : Point d × ((w : Worker n) → Fin b.1 → Sample w) =>
                  ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
                      stochasticGradient A.problem i (p.2 i j) p.1)) -
                    globalGradient P p.1‖ ^ 2)
                ((Measure.map X (prefixLaw.prod batchLaw)).prod
                  (Measure.map Y (prefixLaw.prod batchLaw))) := by
              rw [hmapX, hmapY]
              letI : IsProbabilityMeasure (Measure.map xNext prefixLaw) :=
                Measure.isProbabilityMeasure_map hxNextPrefix.aemeasurable
              simpa [P] using
                (online_refresh_average_sq_product_aestronglyMeasurable
                  (b := b) A σ hVariance (Measure.map xNext prefixLaw))
            have hcomp := aestronglyMeasurable_comp_of_indep_product_law
              hX hY (inferInstance : SigmaFinite (Measure.map X (prefixLaw.prod batchLaw)))
              (inferInstance : SigmaFinite (Measure.map Y (prefixLaw.prod batchLaw)))
              hXY hbase
            simpa [refreshKernelPrefixBatch, X, Y] using hcomp
          let pullBatch := fun p :
              (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                ((((w : Worker n) → Fin b.1 → Sample w) ×
                  ((w : Worker n) → Fin b0.1 → Sample w)) ×
                    (Worker n → Ξ)) => (p.1, p.2.1.1)
          have hpullBatch : Measurable pullBatch := by
            dsimp [pullBatch]
            fun_prop
          have hpullBatchLaw : Measure.map pullBatch (prefixLaw.prod restLaw) =
              prefixLaw.prod batchLaw := by
            let projectBatch := fun r :
                ((((w : Worker n) → Fin b.1 → Sample w) ×
                  ((w : Worker n) → Fin b0.1 → Sample w)) ×
                    (Worker n → Ξ)) => r.1.1
            have hprojectBatch : Measurable projectBatch := by
              dsimp [projectBatch]
              fun_prop
            have hprojectBatchLaw : Measure.map projectBatch restLaw = batchLaw := by
              calc
                Measure.map projectBatch restLaw =
                    Measure.map Prod.fst (Measure.map Prod.fst restLaw) := by
                      rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
                      rfl
                _ = Measure.map Prod.fst
                    ((onlineBatchLaw A.problem b).prod
                      (onlineBatchLaw A.problem b0)) := by
                      rw [show Measure.map Prod.fst restLaw =
                          (onlineBatchLaw A.problem b).prod
                            (onlineBatchLaw A.problem b0) by
                        dsimp [restLaw]
                        rw [Measure.map_fst_prod, measure_univ, one_smul]]
                _ = batchLaw := by
                  dsimp [batchLaw]
                  rw [Measure.map_fst_prod, measure_univ, one_smul]
            have hmap := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
              measurable_id hprojectBatch
            rw [hprojectBatchLaw] at hmap
            simpa [pullBatch, projectBatch] using hmap.symm
          have hqmp : Measure.QuasiMeasurePreserving pullBatch
              (prefixLaw.prod restLaw)
              (prefixLaw.prod batchLaw) := ⟨hpullBatch, by rw [hpullBatchLaw]⟩
          simpa [refreshKernelRest, refreshKernelPrefixBatch, pullBatch,
            Function.uncurry] using
            hRefreshPrefixBatch.comp_quasiMeasurePreserving hqmp
        have hRefreshIndep : ProbabilityTheory.IndepFun
            (fun path => ‖refreshErrorAt path‖ ^ 2)
            (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path t).1)
            law := by
          have h := iidStream_prefix_current_snd_kernel_indep_fst
            coinLaw restLaw t refreshKernelRest
            (by
              have hprefixLawEq : prefixLaw =
                  Measure.infinitePi
                    (fun _ : Fin t => coinLaw.prod restLaw) := by
                simpa [prefixLaw, prefixMap, law, roundLaw, coinLaw, restLaw,
                  onlineProofExactPathLaw, onlineRoundLaw] using
                  iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) t
              rw [← hprefixLawEq]
              exact hRefreshKernelRest)
          apply h.congr (Filter.Eventually.of_forall ?_)
            (Filter.Eventually.of_forall fun _ => rfl)
          intro path
          change refreshKernelRest (prefixMap path) (path t).2 =
            ‖refreshErrorAt path‖ ^ 2
          dsimp [refreshKernelRest, refreshErrorAt, xNext]
          rw [hstatePrefix path]
          rfl
        let branchAt :=
          fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path t).1
        have hbranchAt : Measurable branchAt := by
          dsimp [branchAt]
          fun_prop
        have hbranchLaw : Measure.map branchAt law = coinLaw := by
          calc
            Measure.map branchAt law = Measure.map Prod.fst
                (Measure.map
                  (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t)
                  law) := by
                    rw [MeasureTheory.Measure.map_map]
                    · rfl
                    · exact measurable_fst
                    · exact measurable_pi_apply t
            _ = Measure.map Prod.fst (onlineRoundLaw A) := by
              rw [show Measure.map
                  (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path t)
                  law = onlineRoundLaw A by
                simpa [law, onlineProofExactPathLaw] using
                  SOptLib.iidStreamLaw_map_eval
                    (onlineRoundLaw (b := b) (b0 := b0) A) t]
            _ = coinLaw := by
              dsimp [coinLaw]
              unfold onlineRoundLaw
              rw [Measure.map_fst_prod, measure_univ, one_smul]
        have htrueMass : coinLaw.real ({true} : Set Bool) =
            A.refreshProbability := by
          rw [measureReal_def]
          dsimp [coinLaw]
          unfold refreshLaw
          rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
          simp [PMF.bernoulli_apply]
        have hfalseMass : coinLaw.real ({false} : Set Bool) =
            1 - A.refreshProbability := by
          rw [measureReal_def]
          dsimp [coinLaw]
          unfold refreshLaw
          rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
          simp only [PMF.bernoulli_apply, Bool.cond_false]
          let pNN : NNReal :=
            ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
          have hpNN : pNN ≤ (1 : NNReal) := by
            exact_mod_cast A.refresh_admissible.2
          change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
          rw [NNReal.coe_sub hpNN]
          rfl
        let refreshSq := fun path => ‖refreshErrorAt path‖ ^ 2
        let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
        have hRefreshGate :
            (∫ path, if branchAt path = true then refreshSq path else 0 ∂law) ≤
              A.refreshProbability * ∫ path, refreshSq path ∂law := by
          exact integral_independent_bool_gate_le law coinLaw true
            A.refreshProbability refreshSq branchAt
            (by simpa [refreshSq] using hRefreshAt) hbranchAt
            (by simpa [refreshSq, branchAt] using hRefreshIndep)
            hbranchLaw htrueMass
        have hNonrefreshGate :
            (∫ path, if branchAt path = false then nonrefreshSq path else 0 ∂law) ≤
              (1 - A.refreshProbability) * ∫ path, nonrefreshSq path ∂law := by
          exact integral_independent_bool_gate_le law coinLaw false
            (1 - A.refreshProbability) nonrefreshSq branchAt
            (by simpa [nonrefreshSq] using hNonrefreshInt) hbranchAt
            (by simpa [nonrefreshSq, branchAt] using hNonrefreshIndep)
            hbranchLaw hfalseMass
        have hRefreshGateInt : Integrable
            (fun path => if branchAt path = true then refreshSq path else 0) law := by
          have hs : MeasurableSet {path | branchAt path = true} :=
            hbranchAt (measurableSet_singleton true)
          have hp := Integrable.piecewise hs hRefreshAt.integrableOn
            (integrable_const (c := (0 : ℝ))).integrableOn
          simpa [refreshSq, Set.piecewise] using hp
        have hNonrefreshGateInt : Integrable
            (fun path => if branchAt path = false then nonrefreshSq path else 0) law := by
          have hs : MeasurableSet {path | branchAt path = false} :=
            hbranchAt (measurableSet_singleton false)
          have hp := Integrable.piecewise hs hNonrefreshInt.integrableOn
            (integrable_const (c := (0 : ℝ))).integrableOn
          simpa [nonrefreshSq, Set.piecewise] using hp
        have hNextSplit : estimatorErrorMoment P run law (t + 1) =
            (∫ path, if branchAt path = true then refreshSq path else 0 ∂law) +
              ∫ path, if branchAt path = false then nonrefreshSq path else 0 ∂law := by
          unfold estimatorErrorMoment
          rw [← integral_add hRefreshGateInt hNonrefreshGateInt]
          apply integral_congr_ae
          filter_upwards [] with path
          rw [show (run (t + 1) path).g - globalGradient P (run (t + 1) path).x =
              nextResidualAt path by rfl, hdecompAt path]
          by_cases hb : branchAt path = true
          · simp [hb, branchAt, refreshSq, nonrefreshSq]
          · have hf : branchAt path = false := Bool.eq_false_of_not_eq_true hb
            simp [hb, hf, branchAt, refreshSq, nonrefreshSq]
        have hRecurrenceAt : estimatorErrorMoment P run law (t + 1) ≤
            (1 - A.refreshProbability) / n.1 *
                (ω * (rootMeanSquare Llocal) ^ 2 +
                  (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                stepMoment run law t +
              (1 - A.refreshProbability) * estimatorErrorMoment P run law t +
              A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
          rw [hNextSplit]
          calc
            _ ≤ A.refreshProbability * (∫ path, refreshSq path ∂law) +
                (1 - A.refreshProbability) *
                  (∫ path, nonrefreshSq path ∂law) :=
              add_le_add hRefreshGate hNonrefreshGate
            _ ≤ A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
                (1 - A.refreshProbability) *
                  (estimatorErrorMoment P run law t + C * stepMoment run law t) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (by simpa [refreshSq] using hRefreshBoundAt)
                  (le_of_lt A.refresh_admissible.1)
              · exact mul_le_mul_of_nonneg_left
                  (by simpa [nonrefreshSq] using hNonrefreshBound)
                  (sub_nonneg.mpr A.refresh_admissible.2)
            _ = _ := by
              dsimp [C]
              ring
        have hHistory : ∀ j, j < t + 1 →
            estimatorErrorMoment P run law (j + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                  stepMoment run law j +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
                A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjt | rfl
          · exact ih.2.2.2.2.2.2 j hjt
          · exact hRecurrenceAt
        exact ⟨hxNext, hNextResidualMeas, hxL2Succ, hgL2Succ,
          hNextError, hStepSucc, hHistory⟩
  exact hScalarComponents k

set_option maxHeartbeats 4000000 in
theorem online_executable_scalar_components_all
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path => (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path => (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
        stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let residual := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    average (fun i : Worker n =>
      A.quantizer.apply
          (onlineBatchDifference A.problem (path.2 k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i (run (k + 1) path).x (run k path).x)
  let refreshError := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    average (fun i : Worker n => average (fun j : Fin b.1 =>
      stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).1
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n =>
      A.quantizer.apply
        (onlineBatchDifference A.problem (path.2 k).2.1.2 i xN s.x)
        ((path.2 k).2.2 i)
    have hdiffAvg : average (fun i : Worker n =>
        localGradientDifference P i xN s.x) =
        globalGradient P xN - globalGradient P s.x := by
      rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
        globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : innovation path =
        average q - average (fun i : Worker n =>
          localGradientDifference P i xN s.x) := by
      dsimp [innovation, q, xN, s]
      rw [show (run (k + 1) path).x = xN by rfl]
      unfold average SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n =>
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path.2 k)) s i) -
          globalGradient P xN := by
      rfl
    cases h : branch path with
    | false =>
        simp only [h, Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        change average (fun i : Worker n => s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [h, if_true]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        rfl
  let query := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    (run (k + 1) path).x
  let refreshBatch := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    (path.2 k).2.1.1
  let batchLaw := onlineBatchLaw A.problem b
  let φ := fun (x : Point d)
      (batch : (i : Worker n) → Fin b.1 → Sample i) =>
    ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
        stochasticGradient A.problem i (batch i j) x)) -
      globalGradient P x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hfixed (x : Point d) :
      Integrable (φ x) batchLaw ∧
        (∫ batch, φ x batch ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [φ, batchLaw, P] using
      (online_fixed_refresh_average_second_moment A x σ hVariance hSmooth.1)
  /- Assumption 3.3's sampled-loss differentiability closes the scalar
  product-law regularity that the preceding attempt left open.  This is the
  complete refresh-error square, not a state-valued wrapper. -/
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j)
          batchLaw = A.problem.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
  have hsampleDiff (i : Worker n) (j : Fin b.1) :
      ∀ᵐ batch ∂batchLaw,
        Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
    let coord := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
        (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop),
        by rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
          simpa [coord] using hcoord i j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleLossInt (i : Worker n) (j : Fin b.1) (x : Point d) :
      Integrable (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        A.problem.sampleLoss i (batch i j) x) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
        simpa [coord] using hcoord i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        stochasticGradient A.problem i (p.2 i j) p.1)
      ((Measure.map query law).prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i (Measure.map query law) batchLaw id (fun batch => batch i j)
      stronglyMeasurable_id.aestronglyMeasurable
      (hsampleDiff i j) (hsampleLossInt i j)
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1))
      ((Measure.map query law).prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2 i j) p.1)))
      ((Measure.map query law).prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        globalGradient P p.1)
      ((Measure.map query law).prod batchLaw) :=
    ((measurable_gradient (globalObjective P)).comp measurable_fst).aestronglyMeasurable
  have hφ : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
        φ p.1 p.2) ((Measure.map query law).prod batchLaw) := by
    have hv := havg.sub hglobal
    simpa [φ, pow_two] using hv.norm.mul hv.norm
  /- The direct source route carries only the iterate and residual random
  variables, plus their two scalar L² certificates.  At the successor step it
  transports those components to the strict-prefix law, consumes the
  canonical fixed-fiber Eq. (33)-style calculation, and reaches the Bernoulli
  branch recombination without constructing a measurable complete `State`. -/
  have hScalarComponents : ∀ t,
      AEStronglyMeasurable (fun path => (run t path).x) law ∧
      AEStronglyMeasurable
        (fun path => (run t path).g - globalGradient P (run t path).x) law ∧
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run t path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law t ∧
      StepMomentWellDefined run law t ∧
      ∀ j, j < t →
        estimatorErrorMoment P run law (j + 1) ≤
          (1 - A.refreshProbability) / n.1 *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
    intro t
    induction t with
    | zero =>
        have hx : AEStronglyMeasurable (fun path => (run 0 path).x) law := by
          simpa [run, onlineProcess, onlineRun_zero, onlinePathOfNoise,
            onlineInitialState] using
            (aestronglyMeasurable_const : AEStronglyMeasurable
              (fun _ : ((i : Worker n) → Fin b.1 → Sample i) ×
                (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => x0) law)
        let initG := fun batch : (i : Worker n) → Fin b.1 → Sample i =>
          average (fun i : Worker n => average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (batch i j) x0))
        have hcoord0 (i : Worker n) (j : Fin b.1) :
            Measure.map
                (fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j)
                batchLaw = A.problem.sampleLaw i := by
          simpa [batchLaw] using onlineBatchLaw_coordinate_marginal A.problem i j
        have hgrad0 (i : Worker n) (j : Fin b.1) : Integrable
            (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
              stochasticGradient A.problem i (batch i j) x0) batchLaw := by
          have hm : Integrable (fun xi => stochasticGradient A.problem i xi x0)
              (Measure.map
                (fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j)
                batchLaw) := by
            rw [hcoord0 i j]
            exact (hVariance.1.2 i x0).1
          exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
            (((measurable_pi_apply j).comp
              (measurable_pi_apply i)).aemeasurable)).mp hm
        have hworker0 (i : Worker n) : AEStronglyMeasurable
            (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
              average (fun j : Fin b.1 =>
                stochasticGradient A.problem i (batch i j) x0)) batchLaw := by
          unfold average SOptLib.finiteUniformAverage
          have hs0 := (Finset.aestronglyMeasurable_sum Finset.univ
            (fun j _ => (hgrad0 i j).aestronglyMeasurable)).const_smul
              ((Fintype.card (Fin b.1) : ℝ)⁻¹)
          refine hs0.congr (Filter.Eventually.of_forall ?_)
          intro batch
          simp [Finset.sum_apply]
        have hInitG : AEStronglyMeasurable initG batchLaw := by
          unfold initG average SOptLib.finiteUniformAverage
          have hs0 := (Finset.aestronglyMeasurable_sum Finset.univ
            (fun i _ => hworker0 i)).const_smul
              ((Fintype.card (Worker n) : ℝ)⁻¹)
          refine hs0.congr (Filter.Eventually.of_forall ?_)
          intro batch
          simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
        have hfstLaw : Measure.map Prod.fst law = batchLaw := by
          dsimp [law, batchLaw]
          unfold onlinePathLaw
          rw [Measure.map_fst_prod, measure_univ, one_smul]
        have hfst : Measure.QuasiMeasurePreserving Prod.fst law batchLaw :=
          ⟨measurable_fst, by rw [hfstLaw]⟩
        have hInitGPath : AEStronglyMeasurable
            (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => initG path.1) law :=
          hInitG.comp_quasiMeasurePreserving hfst
        have hr : AEStronglyMeasurable
            (fun path => (run 0 path).g - globalGradient P (run 0 path).x) law := by
          simpa [run, P, initG, onlineProcess, onlineRun_zero, onlinePathOfNoise,
            onlineInitialState, onlinePrintedInitialEstimatorAt] using
            hInitGPath.sub (aestronglyMeasurable_const : AEStronglyMeasurable
              (fun _ : ((i : Worker n) → Fin b.1 → Sample i) ×
                (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => globalGradient P x0) law)
        have hxl2 : Integrable (fun path => ‖(run 0 path).x - x0‖ ^ 2) law := by
          have heq : (fun path => ‖(run 0 path).x - x0‖ ^ 2) =
              (fun _ => (0 : ℝ)) := by
            funext path
            change ‖x0 - x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (c := (0 : ℝ))
        have hinit := online_executable_initial_scalar_moments
          A x0 Llocal σ hSmooth hVariance hBatch
        have he : EstimatorErrorMomentWellDefined P run law 0 := hinit.1
        have hs : StepMomentWellDefined run law 0 := hinit.2.1
        have hgl2 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) law := by
          have hadd := integrable_sq_norm_add hr
            (aestronglyMeasurable_const : AEStronglyMeasurable
              (fun _ : ((i : Worker n) → Fin b.1 → Sample i) ×
                (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => globalGradient P x0) law)
            (by simpa [EstimatorErrorMomentWellDefined] using he)
            (integrable_const (μ := law) (c := ‖globalGradient P x0‖ ^ 2))
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          simpa [run, P, initG, onlineProcess, onlineRun_zero,
            onlinePathOfNoise, onlineInitialState,
            onlinePrintedInitialEstimatorAt] using
              (sub_add_cancel (initG path.1) (globalGradient P x0))
        refine ⟨hx, hr, hxl2, hgl2, he, hs, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        let residual := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
          (run t path).g - globalGradient P (run t path).x
        have hgrad : AEStronglyMeasurable
            (fun path => globalGradient P (run t path).x) law :=
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            ih.1.aemeasurable).aestronglyMeasurable
        have hg : AEStronglyMeasurable (fun path => (run t path).g) law := by
          have hsum := ih.2.1.add hgrad
          refine hsum.congr (Filter.Eventually.of_forall ?_)
          intro path
          dsimp [residual] at hsum ⊢
          abel
        have hxNext : AEStronglyMeasurable
            (fun path => (run (t + 1) path).x) law := by
          have hstep := ih.1.sub (hg.const_smul (A.stepSize : ℝ))
          simpa [run, onlineProcess_succ, onlineStep, primalStep_eq] using hstep
        let prefixMap := fun path :
            ((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
          (path.1, onlineRoundPrefix t path.2)
        let prefixLaw := Measure.map prefixMap law
        let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
        let noise := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
          ((path.2 t).2.1.2, (path.2 t).2.2)
        let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
        let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
          fun _ => Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
        let prefixState := onlineExecutablePrefixState A x0 hBatch fallback t
        let x := fun pref => (prefixState pref).x
        let xNext := fun pref => primalStep A.stepSize (prefixState pref)
        let direction := fun pref =>
          (prefixState pref).g - globalGradient P (prefixState pref).x
        let innovationKernel := fun
            (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin t → OnlineRoundNoise n b b0 Sample Ξ))
            (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) =>
          average (fun i : Worker n =>
            A.quantizer.apply
                (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
                (q.2 i) -
              localGradientDifference P i (xNext pref) (x pref))
        let C := (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
        let B := fun pref => C * ‖xNext pref - x pref‖ ^ 2
        have hprefix : Measurable prefixMap := by
          dsimp [prefixMap, onlineRoundPrefix]
          exact measurable_fst.prodMk
            (measurable_pi_lambda _ fun j =>
              (measurable_pi_apply j.1).comp measurable_snd)
        haveI : IsProbabilityMeasure prefixLaw :=
          Measure.isProbabilityMeasure_map hprefix.aemeasurable
        have hstatePrefix : ∀ path, prefixState (prefixMap path) = run t path := by
          intro path
          dsimp [prefixState, prefixMap, run]
          exact (onlineProcess_congr_round_prefix A x0 hBatch t
            path.1 (path := path.2)
            (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix t path.2))
            (by
              intro j hj
              simp [onlineExtendRoundPrefix, onlineRoundPrefix, hj])).symm
        have hxPrefix : AEStronglyMeasurable x prefixLaw := by
          have hcomp : AEStronglyMeasurable
              (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
                x (path.1, fun j : Fin t => path.2 j.1)) law := by
            refine ih.1.congr (Filter.Eventually.of_forall ?_)
            intro path
            simpa [prefixMap, onlineRoundPrefix, x] using
              congrArg State.x (hstatePrefix path).symm
          have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
            batchLaw roundLaw t x (by
              simpa [law, batchLaw, roundLaw, onlinePathLaw] using hcomp)
          have hprefixLaw : prefixLaw =
              batchLaw.prod (Measure.infinitePi (fun _ : Fin t => roundLaw)) := by
            have hm := MeasureTheory.Measure.map_prod_map batchLaw
              (SOptLib.iidStreamLaw roundLaw) measurable_id
              (measurable_pi_lambda _ fun (j : Fin t) => measurable_pi_apply j.1)
            rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw t] at hm
            simpa [prefixLaw, prefixMap, law, batchLaw, roundLaw, onlinePathLaw,
              onlineRoundPrefix] using hm.symm
          rw [hprefixLaw]
          exact hfinite
        have hdirection : AEStronglyMeasurable direction prefixLaw := by
          have hcomp : AEStronglyMeasurable
              (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
                direction (path.1, fun j : Fin t => path.2 j.1)) law := by
            refine ih.2.1.congr (Filter.Eventually.of_forall ?_)
            intro path
            simpa [prefixMap, onlineRoundPrefix, direction] using
              congrArg
                (fun s : State d => s.g - globalGradient P s.x)
                (hstatePrefix path).symm
          have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
            batchLaw roundLaw t direction (by
              simpa [law, batchLaw, roundLaw, onlinePathLaw] using hcomp)
          have hprefixLaw : prefixLaw =
              batchLaw.prod (Measure.infinitePi (fun _ : Fin t => roundLaw)) := by
            have hm := MeasureTheory.Measure.map_prod_map batchLaw
              (SOptLib.iidStreamLaw roundLaw) measurable_id
              (measurable_pi_lambda _ fun (j : Fin t) => measurable_pi_apply j.1)
            rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw t] at hm
            simpa [prefixLaw, prefixMap, law, batchLaw, roundLaw, onlinePathLaw,
              onlineRoundPrefix] using hm.symm
          rw [hprefixLaw]
          exact hfinite
        have hxNextPrefix : AEStronglyMeasurable xNext prefixLaw := by
          have hgradPrefix : AEStronglyMeasurable
              (fun pref => globalGradient P (x pref)) prefixLaw :=
            ((measurable_gradient (globalObjective P)).comp_aemeasurable
              hxPrefix.aemeasurable).aestronglyMeasurable
          have hgPrefix : AEStronglyMeasurable
              (fun pref => (prefixState pref).g) prefixLaw := by
            have hsum := hdirection.add hgradPrefix
            refine hsum.congr (Filter.Eventually.of_forall ?_)
            intro pref
            dsimp [direction, x]
            abel
          have hstep := hxPrefix.sub (hgPrefix.const_smul (A.stepSize : ℝ))
          simpa [xNext, x, primalStep_eq] using hstep
        have hkernel : AEStronglyMeasurable
            (fun p => innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
          let hE : OnlineExpectationRealization A.problem :=
            onlineExpectationRealization A.problem
          simpa [innovationKernel, xNext, x, noiseLaw,
            onlineCorrectedFixedWorkerInnovation,
            onlineLocalProblemCorrected_eq_onlineLocalProblem] using
            (online_corrected_nonrefresh_average_product_aestronglyMeasurable
              (b0 := b0) A hE σ hVariance prefixLaw xNext x
              hxNextPrefix hxPrefix)
        have hfixed (pref) :=
          online_proofExact_fixed_nonrefresh_average_second_moment
            (b0 := b0) A (xNext pref) (x pref) Llocal ℒlocal σ ω
            hSmooth hVariance
            (fun i => by
              simpa [xNext, x, prefixState, onlineExecutablePrefixState,
                onlineProcess_succ, onlineStep] using
                hAverageSmooth.2 t i
                  (pref.1, onlineExtendRoundPrefix fallback pref.2))
            hQuantizer
        have hStepPrefix : Integrable
            (fun pref => ‖xNext pref - x pref‖ ^ 2) prefixLaw := by
          have hcomp : Integrable
              (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
                ‖xNext (path.1, fun j : Fin t => path.2 j.1) -
                  x (path.1, fun j : Fin t => path.2 j.1)‖ ^ 2) law := by
            refine ih.2.2.2.2.2.1.congr (Filter.Eventually.of_forall ?_)
            intro path
            dsimp [StepMomentWellDefined]
            congr 2
            rw [show x (path.1, fun j : Fin t => path.2 j.1) = (run t path).x by
              simpa [prefixMap, onlineRoundPrefix, x] using
                congrArg State.x (hstatePrefix path)]
            rw [show xNext (path.1, fun j : Fin t => path.2 j.1) =
                (run (t + 1) path).x by
              dsimp [xNext]
              rw [show prefixState (path.1, fun j : Fin t => path.2 j.1) =
                  run t path by
                simpa [prefixMap, onlineRoundPrefix] using hstatePrefix path]
              rfl]
          have hfinite := integrable_initial_prefix_of_comp_general batchLaw roundLaw t
            (fun pref => ‖xNext pref - x pref‖ ^ 2) (by
              simpa [law, batchLaw, roundLaw, onlinePathLaw] using hcomp)
          have hprefixLaw : prefixLaw =
              batchLaw.prod (Measure.infinitePi (fun _ : Fin t => roundLaw)) := by
            have hm := MeasureTheory.Measure.map_prod_map batchLaw
              (SOptLib.iidStreamLaw roundLaw) measurable_id
              (measurable_pi_lambda _ fun (j : Fin t) => measurable_pi_apply j.1)
            rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw t] at hm
            simpa [prefixLaw, prefixMap, law, batchLaw, roundLaw, onlinePathLaw,
              onlineRoundPrefix] using hm.symm
          rw [hprefixLaw]
          exact hfinite
        have hB : Integrable B prefixLaw := by
          simpa [B] using hStepPrefix.const_mul C
        haveI : IsProbabilityMeasure noiseLaw := by
          unfold noiseLaw onlineDifferenceCompressionLaw
          infer_instance
        have hkernelSq : AEStronglyMeasurable
            (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
            (prefixLaw.prod noiseLaw) := by
          simpa [pow_two] using hkernel.norm.mul hkernel.norm
        have hproductInnovationSq : Integrable
            (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
            (prefixLaw.prod noiseLaw) := by
          rw [integrable_prod_iff hkernelSq]
          refine ⟨Filter.Eventually.of_forall (fun pref => (hfixed pref).2.2.1), ?_⟩
          refine Integrable.mono hB
            (hkernelSq.norm.integral_prod_right') (Filter.Eventually.of_forall ?_)
          intro pref
          have hb := (hfixed pref).2.2.2
          have hBnonneg : 0 ≤ B pref :=
            (integral_nonneg fun _ => sq_nonneg _).trans hb
          rw [Real.norm_of_nonneg hBnonneg]
          have heq : (fun q => ‖‖innovationKernel pref q‖ ^ 2‖) =
              (fun q => ‖innovationKernel pref q‖ ^ 2) := by
            funext q
            rw [Real.norm_of_nonneg (sq_nonneg _)]
          rw [heq, Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
          simpa [B, C] using hb
        have hFresh :=
          onlineExecutable_nonrefreshParameter_indep_noise_of_components
            A x0 hBatch t ih.1 ih.2.1
        let current := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 t
        let noiseOfRound := fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          (z.2.1.2, z.2.2)
        have hcurrent : Measurable current := by
          dsimp [current]
          exact (measurable_pi_apply t).comp measurable_snd
        have hnoiseOfRound : Measurable noiseOfRound := by
          dsimp [noiseOfRound]
          fun_prop
        have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
          let streamLaw := SOptLib.iidStreamLaw roundLaw
          let streamPrefix := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            fun j : Fin t => path j.1
          let streamCurrent := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            path t
          have hstreamPrefix : Measurable streamPrefix := by
            dsimp [streamPrefix]
            exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
          have hstreamCurrent : Measurable streamCurrent := measurable_pi_apply t
          haveI : IsProbabilityMeasure streamLaw := by
            dsimp [streamLaw]
            infer_instance
          haveI : IsProbabilityMeasure (Measure.map streamPrefix streamLaw) :=
            Measure.isProbabilityMeasure_map hstreamPrefix.aemeasurable
          have hstreamIndep : ProbabilityTheory.IndepFun
              streamPrefix streamCurrent streamLaw := by
            apply indepFun_of_map_prod_eq_prod_laws
              (P := streamLaw)
              (Z := fun path => (streamPrefix path, streamCurrent path))
              (mu := Measure.map streamPrefix streamLaw) (nu := roundLaw)
            · exact (hstreamPrefix.prodMk hstreamCurrent).aemeasurable
            · simpa [streamPrefix, streamCurrent, streamLaw,
                SOptLib.iidStreamLaw] using
                (infinitePi_prefix_current_map_eq_prod
                  (fun _ : ℕ => roundLaw) t)
          have h := indepFun_prod_left_adjoin_of_indepFun
            batchLaw streamLaw streamPrefix streamCurrent
            hstreamPrefix hstreamCurrent hstreamIndep
          simpa [prefixMap, current, law, batchLaw, roundLaw, streamLaw,
            onlinePathLaw, streamPrefix, streamCurrent, onlineRoundPrefix] using h
        have hfreshPrefix : ProbabilityTheory.IndepFun prefixMap noise law := by
          simpa [noise, current, noiseOfRound, Function.comp_def] using
            hpastCurrent.comp measurable_id hnoiseOfRound
        have hnoise : AEMeasurable noise law := by
          dsimp [noise]
          fun_prop
        have hnoiseLaw : Measure.map noise law = noiseLaw := by
          simpa [noiseLaw] using hFresh.2.2
        have hjoint : AEMeasurable (fun path => (prefixMap path, noise path)) law :=
          hprefix.aemeasurable.prodMk hnoise
        have hjointLaw : Measure.map (fun path => (prefixMap path, noise path)) law =
            prefixLaw.prod noiseLaw := by
          rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
            hprefix.aemeasurable hnoise).mp hfreshPrefix, hnoiseLaw]
        let innovation := fun path => innovationKernel (prefixMap path) (noise path)
        have hInnovationSq : Integrable
            (fun path => ‖innovation path‖ ^ 2) law := by
          have honMap : Integrable
              (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
              (Measure.map (fun path => (prefixMap path, noise path)) law) := by
            rw [hjointLaw]
            exact hproductInnovationSq
          have hcomp := (MeasureTheory.integrable_map_measure
            (by
              rw [hjointLaw]
              exact hkernelSq)
            hjoint).mp honMap
          simpa [innovation, Function.comp_def] using hcomp
        have hInnovationMeas : AEStronglyMeasurable innovation law := by
          have hkernelMapped : AEStronglyMeasurable
              (fun p => innovationKernel p.1 p.2)
              ((Measure.map prefixMap law).prod (Measure.map noise law)) := by
            rw [hnoiseLaw]
            simpa [prefixLaw] using hkernel
          have hcomp := aestronglyMeasurable_comp_of_indep_product_law
            hprefix.aemeasurable hnoise
            (inferInstance : SigmaFinite (Measure.map prefixMap law))
            (inferInstance : SigmaFinite (Measure.map noise law))
            hfreshPrefix hkernelMapped
          simpa [innovation, Function.comp_def] using hcomp
        have hResidualSq : Integrable (fun path => ‖residual path‖ ^ 2) law := by
          simpa [residual, EstimatorErrorMomentWellDefined] using ih.2.2.2.2.1
        have hInnerInt : Integrable
            (fun path => ⟪residual path, innovation path⟫_ℝ) law :=
          integrable_inner_of_integrable_sq_norm ih.2.1 hInnovationMeas
            hResidualSq hInnovationSq
        have hscalarProduct : AEStronglyMeasurable
            (fun p => ⟪direction p.1, innovationKernel p.1 p.2⟫_ℝ)
            (prefixLaw.prod noiseLaw) :=
          hdirection.comp_fst.inner hkernel
        have hinnerComp : ∀ path,
            ⟪direction (prefixMap path), innovationKernel (prefixMap path) (noise path)⟫_ℝ =
              ⟪residual path, innovation path⟫_ℝ := by
          intro path
          dsimp [direction, residual, innovation]
          rw [hstatePrefix path]
        have hfixedInnerZero : ∀ pref,
            (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) = 0 := by
          intro pref
          have hlin := ContinuousLinearMap.integral_comp_comm
            (L := (innerSL ℝ) (direction pref)) (hfixed pref).1
          calc
            (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) =
                (innerSL ℝ) (direction pref)
                  (∫ q, innovationKernel pref q ∂noiseLaw) := hlin
            _ = 0 := by rw [(hfixed pref).2.1]; simp
        have hCross :
            (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
          have hcompInt : Integrable
              (fun path => ⟪direction (prefixMap path),
                innovationKernel (prefixMap path) (noise path)⟫_ℝ) law :=
            hInnerInt.congr (Filter.Eventually.of_forall fun path =>
              (hinnerComp path).symm)
          have hzero :=
            integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
              (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
              (φ := fun pref q => ⟪direction pref, innovationKernel pref q⟫_ℝ)
              (by simpa [prefixLaw] using hscalarProduct)
              hprefix.aemeasurable hnoise hfreshPrefix hnoiseLaw hcompInt
              hfixedInnerZero
          rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
              ∫ path, ⟪direction (prefixMap path),
                innovationKernel (prefixMap path) (noise path)⟫_ℝ ∂law by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun path => (hinnerComp path).symm]
          exact hzero
        have hNonrefreshInt : Integrable
            (fun path => ‖residual path + innovation path‖ ^ 2) law :=
          integrable_sq_norm_add ih.2.1 hInnovationMeas hResidualSq hInnovationSq
        have hNonrefreshEq :
            (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
              (∫ path, ‖residual path‖ ^ 2 ∂law) +
                ∫ path, ‖innovation path‖ ^ 2 ∂law := by
          let pair : Bool → (((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) → Point d :=
            fun z => if z then innovation else residual
          have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
            law (Finset.univ : Finset Bool) pair
            (fun z _ => by
              cases z with
              | false =>
                  change AEStronglyMeasurable residual law
                  exact ih.2.1
              | true =>
                  change AEStronglyMeasurable innovation law
                  exact hInnovationMeas)
            (fun z _ => by
              cases z with
              | false =>
                  change Integrable (fun path => ‖residual path‖ ^ 2) law
                  exact hResidualSq
              | true =>
                  change Integrable (fun path => ‖innovation path‖ ^ 2) law
                  exact hInnovationSq)
            (fun z _ w _ hzw => by
              cases z <;> cases w
              · exact False.elim (hzw rfl)
              · simpa [pair] using hCross
              · simpa [pair, real_inner_comm] using hCross
              · exact False.elim (hzw rfl))
          simpa [pair, Fintype.sum_bool, add_comm] using hsum
        have hBMeas : AEStronglyMeasurable B prefixLaw := hB.aestronglyMeasurable
        have hBComp : Integrable (fun path => B (prefixMap path)) law := by
          have hs := ih.2.2.2.2.2.1.const_mul C
          apply hs.congr
          filter_upwards [] with path
          dsimp [B, xNext, x, prefixState, prefixMap, run]
          rw [onlineProcess_succ]
          have heq := onlineProcess_congr_round_prefix A x0 hBatch t
            path.1 (path := path.2)
            (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix t path.2))
            (by
              intro j hj
              simp [onlineExtendRoundPrefix, onlineRoundPrefix, hj])
          rw [heq]
          rfl
        have hInnovationBound :
            (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
              C * stepMoment run law t := by
          have hbound :=
            integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
              (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
              (φ := fun pref q => ‖innovationKernel pref q‖ ^ 2) (B := B)
              (by simpa [prefixLaw] using hkernelSq) hBMeas
              hprefix.aemeasurable hnoise hfreshPrefix hnoiseLaw
              hInnovationSq hBComp
              (fun pref => by simpa [B, C] using (hfixed pref).2.2.2)
          calc
            (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
                ∫ path, B (prefixMap path) ∂law := by
                  simpa [innovation] using hbound
            _ = C * stepMoment run law t := by
              unfold stepMoment
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with path
              dsimp [B, xNext, x, prefixState, prefixMap, run]
              rw [onlineProcess_succ]
              have heq := onlineProcess_congr_round_prefix A x0 hBatch t
                path.1 (path := path.2)
                (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix t path.2))
                (by
                  intro j hj
                  simp [onlineExtendRoundPrefix, onlineRoundPrefix, hj])
              rw [heq]
              rfl
        have hNonrefreshBound :
            (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
              estimatorErrorMoment P run law t + C * stepMoment run law t := by
          rw [hNonrefreshEq]
          change estimatorErrorMoment P run law t +
              (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ _
          exact add_le_add_right hInnovationBound _
        have hcurrentLaw : Measure.map current law = roundLaw := by
          let streamLaw := SOptLib.iidStreamLaw roundLaw
          let streamCurrent := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            path t
          have hstreamCurrent : Measurable streamCurrent := measurable_pi_apply t
          calc
            Measure.map current law =
                Measure.map streamCurrent (Measure.map Prod.snd law) := by
                  rw [MeasureTheory.Measure.map_map hstreamCurrent measurable_snd]
                  rfl
            _ = Measure.map streamCurrent streamLaw := by
                  rw [show Measure.map Prod.snd law = streamLaw by
                    dsimp [law, streamLaw, roundLaw, onlinePathLaw]
                    rw [Measure.map_snd_prod, measure_univ, one_smul]]
            _ = roundLaw := by
                  simpa [streamCurrent, streamLaw] using
                    SOptLib.iidStreamLaw_map_eval roundLaw t
        let refreshErrorAt :=
          fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
            average (fun i : Worker n => average (fun j : Fin b.1 =>
              stochasticGradient A.problem i ((path.2 t).2.1.1 i j)
                (run (t + 1) path).x)) -
              globalGradient P (run (t + 1) path).x
        have hRefreshAt : Integrable
            (fun path => ‖refreshErrorAt path‖ ^ 2) law := by
          let queryAt := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
            (run (t + 1) path).x
          let refreshBatchAt :=
            fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
              (path.2 t).2.1.1
          have hqueryAt : AEStronglyMeasurable queryAt law := by
            simpa [queryAt] using hxNext
          have hqueryRefreshAt : ProbabilityTheory.IndepFun
              queryAt refreshBatchAt law := by
            have hindep := hFresh.1.comp
              (show Measurable
                (fun p : (Point d × Point d) × Point d => p.1.1) by fun_prop)
              (show Measurable
                (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) by fun_prop)
            simpa [queryAt, refreshBatchAt] using hindep
          have hrefreshBatchAtAE : AEMeasurable refreshBatchAt law := by
            dsimp [refreshBatchAt]
            fun_prop
          have hrefreshBatchAtLaw :
              Measure.map refreshBatchAt law = batchLaw := by
            calc
              Measure.map refreshBatchAt law =
                  Measure.map
                    (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                    (Measure.map
                      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 t)
                      law) := by
                        rw [MeasureTheory.Measure.map_map]
                        · rfl
                        · fun_prop
                        · exact hcurrent
              _ = Measure.map
                    (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                    (onlineRoundLaw A) := by
                      rw [hcurrentLaw]
              _ = batchLaw := by
                simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
                  (b0 := b0) A
          have hφAt : AEStronglyMeasurable
              (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
                φ p.1 p.2) ((Measure.map queryAt law).prod batchLaw) := by
            letI : IsProbabilityMeasure (Measure.map queryAt law) :=
              Measure.isProbabilityMeasure_map hqueryAt.aemeasurable
            simpa [φ, P, batchLaw] using
              (online_refresh_average_sq_product_aestronglyMeasurable
                (b := b) A σ hVariance (Measure.map queryAt law))
          have hrefreshFixed (z : Point d) :
              Integrable (φ z) batchLaw ∧
                (∫ batch, φ z batch ∂batchLaw) ≤
                  varianceAggregateSq σ / (n.1 * b.1) := by
            simpa [φ, batchLaw, P] using
              (online_fixed_refresh_average_second_moment
                (b := b) A z σ hVariance hSmooth.1)
          have hcomp : Integrable
              (fun path => φ (queryAt path) (refreshBatchAt path)) law :=
            integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
              (P := law) (ν := batchLaw) (X := queryAt) (Y := refreshBatchAt)
              (C := varianceAggregateSq σ / (n.1 * b.1)) hφAt
              hqueryAt.aemeasurable hrefreshBatchAtAE hqueryRefreshAt
              hrefreshBatchAtLaw (fun _ _ => sq_nonneg _)
              (fun z => (hrefreshFixed z).1) (fun z => (hrefreshFixed z).2)
          simpa [refreshErrorAt, queryAt, refreshBatchAt, φ] using hcomp
        let queryAt := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
          (run (t + 1) path).x
        let refreshBatchAt :=
          fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 t).2.1.1
        have hqueryAt : AEStronglyMeasurable queryAt law := by
          simpa [queryAt] using hxNext
        have hqueryRefreshAt : ProbabilityTheory.IndepFun
            queryAt refreshBatchAt law := by
          have hindep := hFresh.1.comp
            (show Measurable
              (fun p : (Point d × Point d) × Point d => p.1.1) by fun_prop)
            (show Measurable
              (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) by fun_prop)
          simpa [queryAt, refreshBatchAt] using hindep
        have hrefreshBatchAtAE : AEMeasurable refreshBatchAt law := by
          dsimp [refreshBatchAt]
          fun_prop
        have hrefreshBatchAtLaw : Measure.map refreshBatchAt law = batchLaw := by
          calc
            Measure.map refreshBatchAt law =
                Measure.map
                  (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                  (Measure.map
                    (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 t)
                    law) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · fun_prop
                      · exact hcurrent
            _ = Measure.map
                  (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
                  (onlineRoundLaw A) := by
                    rw [hcurrentLaw]
            _ = batchLaw := by
              simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
                (b0 := b0) A
        have hRefreshBoundAt :
            (∫ path, ‖refreshErrorAt path‖ ^ 2 ∂law) ≤
              varianceAggregateSq σ / (n.1 * b.1) := by
          have hφAt : AEStronglyMeasurable
              (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
                φ p.1 p.2) ((Measure.map queryAt law).prod batchLaw) := by
            letI : IsProbabilityMeasure (Measure.map queryAt law) :=
              Measure.isProbabilityMeasure_map hqueryAt.aemeasurable
            simpa [φ, P, batchLaw] using
              (online_refresh_average_sq_product_aestronglyMeasurable
                (b := b) A σ hVariance (Measure.map queryAt law))
          have hrefreshFixed (z : Point d) :
              Integrable (φ z) batchLaw ∧
                (∫ batch, φ z batch ∂batchLaw) ≤
                  varianceAggregateSq σ / (n.1 * b.1) := by
            simpa [φ, batchLaw, P] using
              (online_fixed_refresh_average_second_moment
                (b := b) A z σ hVariance hSmooth.1)
          have hcomp : Integrable
              (fun path => φ (queryAt path) (refreshBatchAt path)) law := by
            simpa [refreshErrorAt, queryAt, refreshBatchAt, φ] using hRefreshAt
          have hbound :=
            integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
              (P := law) (ν := batchLaw) (X := queryAt) (Y := refreshBatchAt)
              hφAt hqueryAt.aemeasurable hrefreshBatchAtAE hqueryRefreshAt
              hrefreshBatchAtLaw hcomp (fun z => (hrefreshFixed z).2)
          simpa [refreshErrorAt, queryAt, refreshBatchAt, φ] using hbound
        have hRefreshVectorAt : AEStronglyMeasurable refreshErrorAt law := by
          have hkernel : AEStronglyMeasurable
              (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) =>
                average (fun i : Worker n => average (fun j : Fin b.1 =>
                    stochasticGradient A.problem i (p.2 i j) p.1)) -
                  globalGradient P p.1)
              ((Measure.map queryAt law).prod (Measure.map refreshBatchAt law)) := by
            rw [hrefreshBatchAtLaw]
            letI : IsProbabilityMeasure (Measure.map queryAt law) :=
              Measure.isProbabilityMeasure_map hqueryAt.aemeasurable
            simpa [P, batchLaw] using
              (online_refresh_average_product_aestronglyMeasurable
                (b := b) A σ hVariance (Measure.map queryAt law))
          have hcomp := aestronglyMeasurable_comp_of_indep_product_law
            hqueryAt.aemeasurable hrefreshBatchAtAE
            (inferInstance : SigmaFinite (Measure.map queryAt law))
            (inferInstance : SigmaFinite (Measure.map refreshBatchAt law))
            hqueryRefreshAt hkernel
          simpa [refreshErrorAt, queryAt, refreshBatchAt] using hcomp
        let nextResidualAt :=
          fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
            (run (t + 1) path).g - globalGradient P (run (t + 1) path).x
        have hdecompAt : ∀ path, nextResidualAt path =
            if (path.2 t).1 then refreshErrorAt path
            else residual path + innovation path := by
          intro path
          let s := run t path
          let xN := primalStep A.stepSize s
          let q := fun i : Worker n =>
            A.quantizer.apply
              (onlineBatchDifference A.problem (path.2 t).2.1.2 i xN s.x)
              ((path.2 t).2.2 i)
          have hdiffAvg : average (fun i : Worker n =>
              localGradientDifference P i xN s.x) =
              globalGradient P xN - globalGradient P s.x := by
            rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
              globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
            unfold averageLocalGradient localGradientDifference average
              SOptLib.finiteUniformAverage
            rw [Finset.sum_sub_distrib, smul_sub]
          have hinnovationAvg : innovation path =
              average q - average (fun i : Worker n =>
                localGradientDifference P i xN s.x) := by
            dsimp [innovation, innovationKernel, noise, xNext, x, q, xN, s]
            rw [hstatePrefix path]
            unfold average SOptLib.finiteUniformAverage
            rw [Finset.sum_sub_distrib, smul_sub]
          have hnext : nextResidualAt path =
              average (fun i : Worker n =>
                onlineWorkerEstimator A (onlineDriverOfRoundNoise (path.2 t)) s i) -
                globalGradient P xN := by
            rfl
          cases h : (path.2 t).1 with
          | false =>
              simp only [h, Bool.false_eq_true, if_false]
              rw [hnext]
              simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, h, if_false]
              change average (fun i : Worker n => s.g + q i) -
                  globalGradient P xN = residual path + innovation path
              rw [average_const_add, hinnovationAvg, hdiffAvg]
              dsimp [residual, s]
              abel
          | true =>
              simp only [h, if_true]
              rw [hnext]
              simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, h, if_true]
              rfl
        have hNextError : EstimatorErrorMomentWellDefined P run law (t + 1) := by
          let s : Set (((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :=
            {path | (path.2 t).1 = true}
          have hs : MeasurableSet s := by
            dsimp [s]
            exact ((measurable_fst.comp
              ((measurable_pi_apply t).comp measurable_snd))
                (measurableSet_singleton true))
          have hpiece := Integrable.piecewise hs
            hRefreshAt.integrableOn hNonrefreshInt.integrableOn
          have heq : s.piecewise
                (fun path => ‖refreshErrorAt path‖ ^ 2)
                (fun path => ‖residual path + innovation path‖ ^ 2) =
              (fun path => ‖nextResidualAt path‖ ^ 2) := by
            funext path
            by_cases hp : (path.2 t).1 = true
            · simp [s, Set.piecewise, hp, hdecompAt path]
            · have hf : (path.2 t).1 = false := Bool.eq_false_of_not_eq_true hp
              simp [s, Set.piecewise, hp, hf, hdecompAt path]
          rw [EstimatorErrorMomentWellDefined, ← heq]
          exact hpiece
        have hNextResidualMeas : AEStronglyMeasurable nextResidualAt law := by
          let s : Set (((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :=
            {path | (path.2 t).1 = true}
          have hs : MeasurableSet s := by
            dsimp [s]
            exact ((measurable_fst.comp
              ((measurable_pi_apply t).comp measurable_snd))
                (measurableSet_singleton true))
          have hNonrefreshMeas : AEStronglyMeasurable
              (fun path => residual path + innovation path) law := by
            simpa [residual] using ih.2.1.add hInnovationMeas
          have hpiece := (hRefreshVectorAt.mono_measure Measure.restrict_le_self).piecewise hs
            (hNonrefreshMeas.mono_measure Measure.restrict_le_self)
          refine hpiece.congr (Filter.Eventually.of_forall ?_)
          intro path
          by_cases hp : (path.2 t).1 = true
          · simp [s, Set.piecewise, hp, hdecompAt path]
          · have hf : (path.2 t).1 = false := Bool.eq_false_of_not_eq_true hp
            simp [s, Set.piecewise, hp, hf, hdecompAt path]
        have hxL2Succ : Integrable
            (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
          have h := integrable_sq_norm_sub_smul_sub_const_of_l2
            (fun path => (run t path).x) (fun path => (run t path).g)
            x0 (A.stepSize : ℝ) ih.1 hg ih.2.2.1 ih.2.2.2.1
          simpa [run, onlineProcess_succ, onlineStep, primalStep_eq] using h
        have hglobalSucc : Integrable
            (fun path => ‖globalGradient P (run (t + 1) path).x‖ ^ 2) law := by
          have hGlobal := GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
          apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
            x0 (globalGradient P) (rootMeanSquare Llocal)
              (fun path => (run (t + 1) path).x) hxNext
          · simpa [norm_sub_rev] using hxL2Succ
          · intro x y
            exact hGlobal.2 y x
        have hgL2Succ : Integrable (fun path => ‖(run (t + 1) path).g‖ ^ 2) law := by
          have hgradMeas : AEStronglyMeasurable
              (fun path => globalGradient P (run (t + 1) path).x) law :=
            ((measurable_gradient (globalObjective P)).comp_aemeasurable
              hxNext.aemeasurable).aestronglyMeasurable
          have hadd := integrable_sq_norm_add hNextResidualMeas hgradMeas
            (by simpa [nextResidualAt, EstimatorErrorMomentWellDefined] using hNextError)
            hglobalSucc
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          dsimp [nextResidualAt]
          abel
        have hStepSucc : StepMomentWellDefined run law (t + 1) := by
          have hscaled := integrable_sq_norm_const_smul (-(A.stepSize : ℝ)) hgL2Succ
          simpa [StepMomentWellDefined, run, onlineProcess_succ,
            onlineStep, primalStep_eq] using hscaled
        let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
        let restLaw := ((onlineBatchLaw A.problem b).prod
          (onlineBatchLaw A.problem b0)).prod
            (workerCompressionLaw (n := n) A.quantizer)
        let projectNoise := fun r :
            ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
          (r.1.2, r.2)
        haveI : IsProbabilityMeasure restLaw := by
          dsimp [restLaw]
          infer_instance
        have hprojectNoise : Measurable projectNoise := by
          dsimp [projectNoise]
          fun_prop
        have hprojectNoiseLaw : Measure.map projectNoise restLaw = noiseLaw := by
          dsimp [projectNoise, restLaw, noiseLaw, onlineDifferenceCompressionLaw]
          simpa using
            (MeasureTheory.Measure.map_prod_map
              ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0))
              (workerCompressionLaw (n := n) A.quantizer)
              measurable_snd measurable_id).symm
        let nonrefreshKernelRest := fun
            (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin t → OnlineRoundNoise n b b0 Sample Ξ))
            (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) =>
          ‖direction pref + innovationKernel pref (projectNoise r)‖ ^ 2
        have hNonrefreshKernelRest : AEStronglyMeasurable
            (Function.uncurry nonrefreshKernelRest) (prefixLaw.prod restLaw) := by
          let pull := fun p :
              (((i : Worker n) → Fin b.1 → Sample i) ×
                (Fin t → OnlineRoundNoise n b b0 Sample Ξ)) ×
                ((((w : Worker n) → Fin b.1 → Sample w) ×
                  ((w : Worker n) → Fin b0.1 → Sample w)) ×
                    (Worker n → Ξ)) => (p.1, projectNoise p.2)
          have hpull : Measurable pull := by dsimp [pull]; fun_prop
          have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
              prefixLaw.prod noiseLaw := by
            have hmap := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
              measurable_id hprojectNoise
            rw [Measure.map_id, hprojectNoiseLaw] at hmap
            simpa [pull] using hmap.symm
          have hbase : AEStronglyMeasurable
              (fun p => ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
              (prefixLaw.prod noiseLaw) := by
            have hv := hdirection.comp_fst.add hkernel
            simpa [pow_two] using hv.norm.mul hv.norm
          have hqmp : Measure.QuasiMeasurePreserving pull
              (prefixLaw.prod restLaw) (prefixLaw.prod noiseLaw) :=
            ⟨hpull, by rw [hpullLaw]⟩
          simpa [nonrefreshKernelRest, Function.uncurry, pull] using
            hbase.comp_quasiMeasurePreserving hqmp
        have hNonrefreshIndep : ProbabilityTheory.IndepFun
            (fun path => ‖residual path + innovation path‖ ^ 2)
            (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 t).1)
            law := by
          have h := initial_iidStream_prefix_current_snd_kernel_indep_fst
            batchLaw coinLaw restLaw t nonrefreshKernelRest
            (by
              have hprefixLawEq : prefixLaw =
                  batchLaw.prod (Measure.infinitePi
                    (fun _ : Fin t => coinLaw.prod restLaw)) := by
                have hm := MeasureTheory.Measure.map_prod_map batchLaw
                  (SOptLib.iidStreamLaw (coinLaw.prod restLaw)) measurable_id
                  (measurable_pi_lambda _ fun (j : Fin t) => measurable_pi_apply j.1)
                rw [Measure.map_id,
                  iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) t] at hm
                simpa [prefixLaw, prefixMap, law, roundLaw, coinLaw, restLaw,
                  onlinePathLaw, onlineRoundLaw, onlineRoundPrefix] using hm.symm
              rw [← hprefixLawEq]
              exact hNonrefreshKernelRest)
          apply h.congr (Filter.Eventually.of_forall ?_)
            (Filter.Eventually.of_forall fun _ => rfl)
          intro path
          change ‖direction (prefixMap path) +
              innovationKernel (prefixMap path) (noise path)‖ ^ 2 =
            ‖residual path + innovation path‖ ^ 2
          dsimp [direction, residual]
          rw [hstatePrefix path]
        let refreshKernelRest := fun
            (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin t → OnlineRoundNoise n b b0 Sample Ξ))
            (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) =>
          ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
              stochasticGradient A.problem i (r.1.1 i j) (xNext pref))) -
            globalGradient P (xNext pref)‖ ^ 2
        have hRefreshKernelRest : AEStronglyMeasurable
            (Function.uncurry refreshKernelRest) (prefixLaw.prod restLaw) := by
          let refreshKernelPrefixBatch := fun p :
              (((i : Worker n) → Fin b.1 → Sample i) ×
                (Fin t → OnlineRoundNoise n b b0 Sample Ξ)) ×
                ((w : Worker n) → Fin b.1 → Sample w) =>
            ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
                stochasticGradient A.problem i (p.2 i j) (xNext p.1))) -
              globalGradient P (xNext p.1)‖ ^ 2
          have hRefreshPrefixBatch : AEStronglyMeasurable
              refreshKernelPrefixBatch (prefixLaw.prod batchLaw) := by
            let X := fun p : (((i : Worker n) → Fin b.1 → Sample i) ×
                (Fin t → OnlineRoundNoise n b b0 Sample Ξ)) ×
                ((w : Worker n) → Fin b.1 → Sample w) => xNext p.1
            let Y := fun p : (((i : Worker n) → Fin b.1 → Sample i) ×
                (Fin t → OnlineRoundNoise n b b0 Sample Ξ)) ×
                ((w : Worker n) → Fin b.1 → Sample w) => p.2
            have hX : AEMeasurable X (prefixLaw.prod batchLaw) :=
              hxNextPrefix.comp_fst.aemeasurable
            have hY : AEMeasurable Y (prefixLaw.prod batchLaw) :=
              measurable_snd.aemeasurable
            have hXY : ProbabilityTheory.IndepFun X Y
                (prefixLaw.prod batchLaw) := by
              let xMk := hxNextPrefix.mk xNext
              have hxMk : Measurable xMk := hxNextPrefix.measurable_mk
              have hindepMk := (ProbabilityTheory.indepFun_prod
                (μ := prefixLaw) (ν := batchLaw) hxMk measurable_id)
              have hxae : X =ᵐ[prefixLaw.prod batchLaw]
                  (fun p => xMk p.1) := by
                have hpull := (Measure.quasiMeasurePreserving_fst
                  (μ := prefixLaw) (ν := batchLaw))
                exact hpull.tendsto_ae hxNextPrefix.ae_eq_mk
              apply hindepMk.congr hxae.symm (Filter.Eventually.of_forall fun _ => rfl)
            haveI : IsProbabilityMeasure (Measure.map X (prefixLaw.prod batchLaw)) :=
              Measure.isProbabilityMeasure_map hX
            have hmapX : Measure.map X (prefixLaw.prod batchLaw) =
                Measure.map xNext prefixLaw := by
              have hxMap : AEMeasurable xNext
                  (Measure.map Prod.fst (prefixLaw.prod batchLaw)) := by
                rw [Measure.map_fst_prod, measure_univ, one_smul]
                exact hxNextPrefix.aemeasurable
              calc
                Measure.map X (prefixLaw.prod batchLaw) =
                    Measure.map xNext
                      (Measure.map Prod.fst (prefixLaw.prod batchLaw)) := by
                      dsimp [X]
                      exact (AEMeasurable.map_map_of_aemeasurable
                        hxMap measurable_fst.aemeasurable).symm
                _ = Measure.map xNext prefixLaw := by
                  rw [Measure.map_fst_prod, measure_univ, one_smul]
            have hmapY : Measure.map Y (prefixLaw.prod batchLaw) = batchLaw := by
              dsimp [Y]
              rw [Measure.map_snd_prod, measure_univ, one_smul]
            have hbase : AEStronglyMeasurable
                (fun p : Point d × ((w : Worker n) → Fin b.1 → Sample w) =>
                  ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
                      stochasticGradient A.problem i (p.2 i j) p.1)) -
                    globalGradient P p.1‖ ^ 2)
                ((Measure.map X (prefixLaw.prod batchLaw)).prod
                  (Measure.map Y (prefixLaw.prod batchLaw))) := by
              rw [hmapX, hmapY]
              letI : IsProbabilityMeasure (Measure.map xNext prefixLaw) :=
                Measure.isProbabilityMeasure_map hxNextPrefix.aemeasurable
              simpa [P] using
                (online_refresh_average_sq_product_aestronglyMeasurable
                  (b := b) A σ hVariance (Measure.map xNext prefixLaw))
            have hcomp := aestronglyMeasurable_comp_of_indep_product_law
              hX hY (inferInstance : SigmaFinite (Measure.map X (prefixLaw.prod batchLaw)))
              (inferInstance : SigmaFinite (Measure.map Y (prefixLaw.prod batchLaw)))
              hXY hbase
            simpa [refreshKernelPrefixBatch, X, Y] using hcomp
          let pullBatch := fun p :
              (((i : Worker n) → Fin b.1 → Sample i) ×
                (Fin t → OnlineRoundNoise n b b0 Sample Ξ)) ×
                ((((w : Worker n) → Fin b.1 → Sample w) ×
                  ((w : Worker n) → Fin b0.1 → Sample w)) ×
                    (Worker n → Ξ)) => (p.1, p.2.1.1)
          have hpullBatch : Measurable pullBatch := by
            dsimp [pullBatch]
            fun_prop
          have hpullBatchLaw : Measure.map pullBatch (prefixLaw.prod restLaw) =
              prefixLaw.prod batchLaw := by
            let projectBatch := fun r :
                ((((w : Worker n) → Fin b.1 → Sample w) ×
                  ((w : Worker n) → Fin b0.1 → Sample w)) ×
                    (Worker n → Ξ)) => r.1.1
            have hprojectBatch : Measurable projectBatch := by
              dsimp [projectBatch]
              fun_prop
            have hprojectBatchLaw : Measure.map projectBatch restLaw = batchLaw := by
              calc
                Measure.map projectBatch restLaw =
                    Measure.map Prod.fst (Measure.map Prod.fst restLaw) := by
                      rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
                      rfl
                _ = Measure.map Prod.fst
                    ((onlineBatchLaw A.problem b).prod
                      (onlineBatchLaw A.problem b0)) := by
                      rw [show Measure.map Prod.fst restLaw =
                          (onlineBatchLaw A.problem b).prod
                            (onlineBatchLaw A.problem b0) by
                        dsimp [restLaw]
                        rw [Measure.map_fst_prod, measure_univ, one_smul]]
                _ = batchLaw := by
                  dsimp [batchLaw]
                  rw [Measure.map_fst_prod, measure_univ, one_smul]
            have hmap := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
              measurable_id hprojectBatch
            rw [hprojectBatchLaw] at hmap
            simpa [pullBatch, projectBatch] using hmap.symm
          have hqmp : Measure.QuasiMeasurePreserving pullBatch
              (prefixLaw.prod restLaw)
              (prefixLaw.prod batchLaw) := ⟨hpullBatch, by rw [hpullBatchLaw]⟩
          simpa [refreshKernelRest, refreshKernelPrefixBatch, pullBatch,
            Function.uncurry] using
            hRefreshPrefixBatch.comp_quasiMeasurePreserving hqmp
        have hRefreshIndep : ProbabilityTheory.IndepFun
            (fun path => ‖refreshErrorAt path‖ ^ 2)
            (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 t).1)
            law := by
          have h := initial_iidStream_prefix_current_snd_kernel_indep_fst
            batchLaw coinLaw restLaw t refreshKernelRest
            (by
              have hprefixLawEq : prefixLaw =
                  batchLaw.prod (Measure.infinitePi
                    (fun _ : Fin t => coinLaw.prod restLaw)) := by
                have hm := MeasureTheory.Measure.map_prod_map batchLaw
                  (SOptLib.iidStreamLaw (coinLaw.prod restLaw)) measurable_id
                  (measurable_pi_lambda _ fun (j : Fin t) => measurable_pi_apply j.1)
                rw [Measure.map_id,
                  iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) t] at hm
                simpa [prefixLaw, prefixMap, law, roundLaw, coinLaw, restLaw,
                  onlinePathLaw, onlineRoundLaw, onlineRoundPrefix] using hm.symm
              rw [← hprefixLawEq]
              exact hRefreshKernelRest)
          apply h.congr (Filter.Eventually.of_forall ?_)
            (Filter.Eventually.of_forall fun _ => rfl)
          intro path
          change refreshKernelRest (prefixMap path) (path.2 t).2 =
            ‖refreshErrorAt path‖ ^ 2
          dsimp [refreshKernelRest, refreshErrorAt, xNext]
          rw [hstatePrefix path]
          rfl
        let branchAt :=
          fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 t).1
        have hbranchAt : Measurable branchAt := by
          dsimp [branchAt]
          fun_prop
        have hbranchLaw : Measure.map branchAt law = coinLaw := by
          calc
            Measure.map branchAt law = Measure.map Prod.fst
                (Measure.map
                  (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 t)
                  law) := by
                    rw [MeasureTheory.Measure.map_map]
                    · rfl
                    · exact measurable_fst
                    · exact (measurable_pi_apply t).comp measurable_snd
            _ = Measure.map Prod.fst (onlineRoundLaw A) := by
              rw [show Measure.map
                  (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 t)
                  law = onlineRoundLaw A by exact hcurrentLaw]
            _ = coinLaw := by
              dsimp [coinLaw]
              unfold onlineRoundLaw
              rw [Measure.map_fst_prod, measure_univ, one_smul]
        have htrueMass : coinLaw.real ({true} : Set Bool) =
            A.refreshProbability := by
          rw [measureReal_def]
          dsimp [coinLaw]
          unfold refreshLaw
          rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
          simp [PMF.bernoulli_apply]
        have hfalseMass : coinLaw.real ({false} : Set Bool) =
            1 - A.refreshProbability := by
          rw [measureReal_def]
          dsimp [coinLaw]
          unfold refreshLaw
          rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
          simp only [PMF.bernoulli_apply, Bool.cond_false]
          let pNN : NNReal :=
            ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
          have hpNN : pNN ≤ (1 : NNReal) := by
            exact_mod_cast A.refresh_admissible.2
          change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
          rw [NNReal.coe_sub hpNN]
          rfl
        let refreshSq := fun path => ‖refreshErrorAt path‖ ^ 2
        let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
        have hRefreshGate :
            (∫ path, if branchAt path = true then refreshSq path else 0 ∂law) ≤
              A.refreshProbability * ∫ path, refreshSq path ∂law := by
          exact integral_independent_bool_gate_le law coinLaw true
            A.refreshProbability refreshSq branchAt
            (by simpa [refreshSq] using hRefreshAt) hbranchAt
            (by simpa [refreshSq, branchAt] using hRefreshIndep)
            hbranchLaw htrueMass
        have hNonrefreshGate :
            (∫ path, if branchAt path = false then nonrefreshSq path else 0 ∂law) ≤
              (1 - A.refreshProbability) * ∫ path, nonrefreshSq path ∂law := by
          exact integral_independent_bool_gate_le law coinLaw false
            (1 - A.refreshProbability) nonrefreshSq branchAt
            (by simpa [nonrefreshSq] using hNonrefreshInt) hbranchAt
            (by simpa [nonrefreshSq, branchAt] using hNonrefreshIndep)
            hbranchLaw hfalseMass
        have hRefreshGateInt : Integrable
            (fun path => if branchAt path = true then refreshSq path else 0) law := by
          have hs : MeasurableSet {path | branchAt path = true} :=
            hbranchAt (measurableSet_singleton true)
          have hp := Integrable.piecewise hs hRefreshAt.integrableOn
            (integrable_const (c := (0 : ℝ))).integrableOn
          simpa [refreshSq, Set.piecewise] using hp
        have hNonrefreshGateInt : Integrable
            (fun path => if branchAt path = false then nonrefreshSq path else 0) law := by
          have hs : MeasurableSet {path | branchAt path = false} :=
            hbranchAt (measurableSet_singleton false)
          have hp := Integrable.piecewise hs hNonrefreshInt.integrableOn
            (integrable_const (c := (0 : ℝ))).integrableOn
          simpa [nonrefreshSq, Set.piecewise] using hp
        have hNextSplit : estimatorErrorMoment P run law (t + 1) =
            (∫ path, if branchAt path = true then refreshSq path else 0 ∂law) +
              ∫ path, if branchAt path = false then nonrefreshSq path else 0 ∂law := by
          unfold estimatorErrorMoment
          rw [← integral_add hRefreshGateInt hNonrefreshGateInt]
          apply integral_congr_ae
          filter_upwards [] with path
          rw [show (run (t + 1) path).g - globalGradient P (run (t + 1) path).x =
              nextResidualAt path by rfl, hdecompAt path]
          by_cases hb : branchAt path = true
          · simp [hb, branchAt, refreshSq, nonrefreshSq]
          · have hf : branchAt path = false := Bool.eq_false_of_not_eq_true hb
            simp [hb, hf, branchAt, refreshSq, nonrefreshSq]
        have hRecurrenceAt : estimatorErrorMoment P run law (t + 1) ≤
            (1 - A.refreshProbability) / n.1 *
                (ω * (rootMeanSquare Llocal) ^ 2 +
                  (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                stepMoment run law t +
              (1 - A.refreshProbability) * estimatorErrorMoment P run law t +
              A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
          rw [hNextSplit]
          calc
            _ ≤ A.refreshProbability * (∫ path, refreshSq path ∂law) +
                (1 - A.refreshProbability) *
                  (∫ path, nonrefreshSq path ∂law) :=
              add_le_add hRefreshGate hNonrefreshGate
            _ ≤ A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
                (1 - A.refreshProbability) *
                  (estimatorErrorMoment P run law t + C * stepMoment run law t) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (by simpa [refreshSq] using hRefreshBoundAt)
                  (le_of_lt A.refresh_admissible.1)
              · exact mul_le_mul_of_nonneg_left
                  (by simpa [nonrefreshSq] using hNonrefreshBound)
                  (sub_nonneg.mpr A.refresh_admissible.2)
            _ = _ := by
              dsimp [C]
              ring
        have hHistory : ∀ j, j < t + 1 →
            estimatorErrorMoment P run law (j + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                  stepMoment run law j +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
                A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjt | rfl
          · exact ih.2.2.2.2.2.2 j hjt
          · exact hRecurrenceAt
        exact ⟨hxNext, hNextResidualMeas, hxL2Succ, hgL2Succ,
          hNextError, hStepSucc, hHistory⟩
  exact hScalarComponents k

/-- `book/MARINA/MARINA.json#/key_lemmas/7`, Eq. (46), for the executable
Algorithm 3 process with the printed stochastic initialization and its joint
`onlinePathLaw`.  This full-paper obligation is intentionally distinct from
the proof-exact Eq. (46) supplier over `onlineProofExactProcess` and
`onlineProofExactPathLaw` used by Theorems D.3 and D.4. -/
theorem online_estimator_recurrence_46_literal_source_boundary
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) :
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) (k + 1) ∧
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) k ∧
    StepMomentWellDefined (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) k ∧
    estimatorErrorMoment (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
            (onlinePathLaw (b := b) (b0 := b0) A) k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment (onlineLocalProblem A.problem)
            (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
            (onlinePathLaw (b := b) (b0 := b0) A) k +
        A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  have hk := online_executable_scalar_components_all A x0 Llocal ℒlocal σ ω
    hSmooth hVariance hQuantizer hBatch hAverageSmooth k
  have hks := online_executable_scalar_components_all A x0 Llocal ℒlocal σ ω
    hSmooth hVariance hQuantizer hBatch hAverageSmooth (k + 1)
  exact ⟨hks.2.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1,
    hks.2.2.2.2.2.2 k (Nat.lt_succ_self k)⟩

/-- Direct proof-exact Eq. (46) supplier over the canonical round-only
Algorithm 3 process and path law.  Its three well-definedness conjuncts and
exact source coefficients are projections of the simultaneous scalar
induction above. -/
theorem online_estimator_recurrence_46_proof_exact_direct_supplier
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
      stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
        A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  have hk := onlineProofExactProcess_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k
  have hks := onlineProofExactProcess_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth (k + 1)
  exact ⟨hks.2.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1,
    hks.2.2.2.2.2.2 k (Nat.lt_succ_self k)⟩
  /- RETIRED DIAGNOSTIC continuation: once the component-specific induction
  reaches the displayed successor packaging goal, the historical fixed-index
  continuation below no longer contributes typed evidence.  It is retained as
  source history only and is not elaborated.
  /- RETIRED DIAGNOSTIC (noncurrent superseded route): the following block is
  preserved only as iteration history and is not elaborated or consumed.  It
  reconstructed complete-prefix `State` AEMeasurability and therefore must not
  supply the source/public Eq. (46) route.

  /- Query-specific strict-prefix factorization.  The only public-facing
  outputs of this block are the exact random-variable and freshness facts
  needed by the scalar refresh integral; no complete-State regularity theorem
  is added to the source dependency cone. -/
  have hqueryFacts : AEMeasurable query law ∧
      ProbabilityTheory.IndepFun query refreshBatch law := by
    let pastPrefix := onlineRoundPrefix (n := n) (b := b) (b0 := b0)
      (Sample := Sample) (Ξ := Ξ) k
    let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k
    let prefixLaw := Measure.map pastPrefix law
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    have hpastPrefix : Measurable pastPrefix := by
      dsimp [pastPrefix, onlineRoundPrefix]
      exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
    have hcurrent : Measurable current := measurable_pi_apply k
    haveI : IsProbabilityMeasure prefixLaw :=
      Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
    haveI : IsProbabilityMeasure roundLaw := by
      dsimp [roundLaw]
      infer_instance
    have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current law := by
      apply indepFun_of_map_prod_eq_prod_laws
        (P := law) (Z := fun path => (pastPrefix path, current path))
        (mu := prefixLaw) (nu := roundLaw)
      · exact (hpastPrefix.prodMk hcurrent).aemeasurable
      · simpa [pastPrefix, current, prefixLaw, roundLaw, law,
          onlineProofExactPathLaw, SOptLib.iidStreamLaw, onlineRoundPrefix] using
          (infinitePi_prefix_current_map_eq_prod
            (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
    let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
      Classical.choice (nonempty_of_isProbabilityMeasure law)
    let prefixQuery := fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ =>
      primalStep A.stepSize
        (onlineProofExactPrefixState A x0 hBatch fallback k pref)
    have hprefixLaw : prefixLaw = onlineRoundPrefixLaw A k := by
      rfl
    have hprefixQuery : AEMeasurable prefixQuery prefixLaw := by
      rw [hprefixLaw]
      exact (measurable_primalStep A.stepSize).comp_aemeasurable
        (by
          let hE : OnlineExpectationRealization A.problem :=
            onlineExpectationRealization A.problem
          have hprefix_meas (t : ℕ) : Measurable
              (onlineRoundPrefix (n := n) (b := b) (b0 := b0)
                (Sample := Sample) (Ξ := Ξ) t) :=
            measurable_pi_lambda _ fun j => measurable_pi_apply j.1
          haveI (t : ℕ) : IsProbabilityMeasure (onlineRoundPrefixLaw A t) := by
            unfold onlineRoundPrefixLaw
            exact Measure.isProbabilityMeasure_map (hprefix_meas t).aemeasurable
          have hall : ∀ t, AEMeasurable
              (onlineProofExactPrefixState A x0 hBatch fallback t)
              (onlineRoundPrefixLaw A t) := by
            intro t
            induction t with
            | zero =>
                have hconst : onlineProofExactPrefixState A x0 hBatch fallback 0 =
                    fun _ => onlineProofExactInitialState A x0 := by
                  funext pref
                  rfl
                rw [hconst]
                exact measurable_const.aemeasurable
            | succ t ih =>
              let split : (Fin (t + 1) → OnlineRoundNoise n b b0 Sample Ξ) →
                  (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                    OnlineRoundNoise n b b0 Sample Ξ :=
                fun pref => ((fun j => pref j.castSucc), pref (Fin.last t))
              have hsplit : Measurable split := by
                dsimp [split]
                fun_prop
              have hsplitLaw :
                  Measure.map split (onlineRoundPrefixLaw A (t + 1)) =
                    (onlineRoundPrefixLaw A t).prod (onlineRoundLaw A) := by
                simpa [split] using onlineRoundPrefixLaw_split_succ A t
              have hstep : AEMeasurable
                  (fun p : (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                    OnlineRoundNoise n b b0 Sample Ξ =>
                    onlineStep A (onlineDriverOfRoundNoise p.2)
                      (onlineProofExactPrefixState A x0 hBatch fallback t p.1))
                  ((onlineRoundPrefixLaw A t).prod (onlineRoundLaw A)) := by
                exact onlineStep_product_aemeasurable_of_state
                  A hE σ hVariance (onlineRoundPrefixLaw A t)
                  (onlineProofExactPrefixState A x0 hBatch fallback t) ih
              have honMap : AEMeasurable
                  (fun p : (Fin t → OnlineRoundNoise n b b0 Sample Ξ) ×
                    OnlineRoundNoise n b b0 Sample Ξ =>
                    onlineStep A (onlineDriverOfRoundNoise p.2)
                      (onlineProofExactPrefixState A x0 hBatch fallback t p.1))
                  (Measure.map split (onlineRoundPrefixLaw A (t + 1))) := by
                rw [hsplitLaw]
                exact hstep
              have hpull := honMap.comp_aemeasurable hsplit.aemeasurable
              refine hpull.congr (Filter.Eventually.of_forall ?_)
              intro pref
              simpa [split, Function.comp_def] using
                (onlineProofExactPrefixState_succ A x0 hBatch fallback t pref).symm
          exact hall k)
    let refreshOfRound := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1
    have hrefreshOfRound : Measurable refreshOfRound := by
      dsimp [refreshOfRound]
      fun_prop
    have hindep := hpastCurrent.comp₀ hpastPrefix.aemeasurable
      hcurrent.aemeasurable hprefixQuery
      (by
        have : Measure.map current law = roundLaw := by
          simpa [current, law, roundLaw, onlineProofExactPathLaw] using
            SOptLib.iidStreamLaw_map_eval
              (onlineRoundLaw (b := b) (b0 := b0) A) k
        rw [this]
        exact hrefreshOfRound.aemeasurable)
    have hqueryEq : (prefixQuery ∘ pastPrefix) = query := by
      funext path
      dsimp [prefixQuery, pastPrefix, query]
      congr 1
      apply onlineProofExactProcess_congr_prefix A x0 hBatch k
      intro t ht
      simp [onlineRoundPrefix, onlineExtendRoundPrefix, ht]
    have hrefreshEq : (refreshOfRound ∘ current) = refreshBatch := by
      rfl
    have hqueryAE : AEMeasurable query law := by
      simpa only [hqueryEq] using
        hprefixQuery.comp_aemeasurable hpastPrefix.aemeasurable
    exact ⟨hqueryAE, by simpa only [hqueryEq, hrefreshEq] using hindep⟩ -/
  have hqueryFacts : AEMeasurable query law ∧
      ProbabilityTheory.IndepFun query refreshBatch law := by
    have hk := hScalarComponents k
    have hks := hScalarComponents (k + 1)
    have hfresh :=
      onlineProofExact_nonrefreshParameter_indep_noise_of_components
        A x0 hBatch k hk.1 hk.2.1
    have hindep := hfresh.1.comp
      (show Measurable
        (fun p : (Point d × Point d) × Point d => p.1.1) by fun_prop)
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1) by fun_prop)
    exact ⟨by simpa [query] using hks.1.aemeasurable,
      by simpa [query, refreshBatch] using hindep⟩
  have hqueryAE : AEMeasurable query law := hqueryFacts.1
  have hqueryRefreshIndep :
      ProbabilityTheory.IndepFun query refreshBatch law := hqueryFacts.2
  have hrefreshBatchAE : AEMeasurable refreshBatch law := by
    exact ((measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_pi_apply k))))).aemeasurable
  have hrefreshBatchLaw : Measure.map refreshBatch law = batchLaw := by
    calc
      Measure.map refreshBatch law =
          Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
            (Measure.map
              (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k)
              law) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · exact measurable_pi_apply k
      _ = Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
            (onlineRoundLaw A) := by
              rw [show Measure.map
                  (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k)
                  law = onlineRoundLaw A by
                simpa [law, onlineProofExactPathLaw] using
                  SOptLib.iidStreamLaw_map_eval
                    (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = batchLaw := by
        simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
          (b0 := b0) A
  have hRefreshComposed :
      Integrable (fun path => φ (query path) (refreshBatch path)) law := by
    exact integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := refreshBatch)
      (C := varianceAggregateSq σ / (n.1 * b.1)) hφ hqueryAE
      hrefreshBatchAE hqueryRefreshIndep hrefreshBatchLaw
      (fun _ _ => sq_nonneg _) (fun x => (hfixed x).1)
      (fun x => (hfixed x).2)
  have hRefreshBound :
      (∫ path, φ (query path) (refreshBatch path) ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
    exact integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := refreshBatch)
      hφ hqueryAE hrefreshBatchAE hqueryRefreshIndep hrefreshBatchLaw
      hRefreshComposed (fun x => (hfixed x).2)
  have hRefreshWellDefined :
      Integrable (fun path => ‖refreshError path‖ ^ 2) law := by
    simpa [φ, query, refreshBatch, refreshError] using hRefreshComposed
  have hRefreshMomentBound :
      (∫ path, ‖refreshError path‖ ^ 2 ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [φ, query, refreshBatch, refreshError] using hRefreshBound
  /- The branch identity and refresh calculation above are now followed by
  the simultaneous scalar induction required by the nonrefresh branch.  The
  exact-gradient base case is fully discharged; the guarded successor goal
  exposes precisely the pair of induction certificates that must be
  propagated before the fixed-fiber nonrefresh estimate can be applied. -/
  have hError0 : EstimatorErrorMomentWellDefined P run law 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient P x0 - globalGradient P x0‖ ^ 2 = 0
      simp
    rw [EstimatorErrorMomentWellDefined, heq]
    exact integrable_const (μ := law) (c := (0 : ℝ))
  have hStep0 : StepMomentWellDefined run law 0 := by
    have heq : (fun path => ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
        (fun _ => ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2) := by
      funext path
      change ‖(x0 - (A.stepSize : ℝ) • globalGradient P x0) - x0‖ ^ 2 = _
      congr 2
      rw [neg_smul]
      abel
    rw [StepMomentWellDefined, heq]
    exact integrable_const (μ := law)
      (c := ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2)
  have hMoments : ∀ t,
      EstimatorErrorMomentWellDefined P run law t ∧
        StepMomentWellDefined run law t := by
    intro t
    induction t with
    | zero => exact ⟨hError0, hStep0⟩
    | succ t ih =>
        trace_state
        fun_prop -/

end MARINA
