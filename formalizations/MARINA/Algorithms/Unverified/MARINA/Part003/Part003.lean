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
import Algorithms.Unverified.MARINA.Part002
import Algorithms.Unverified.MARINA.Part003.Part002

/-!
# MARINA family: source-facing object model

This file models Algorithms 1--4 of Gorbunov--Burlachenko--Li--Richtárik.
The estimator and iterate processes below are generated definitions, rather
than witness processes constrained by theorem hypotheses.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace MARINA

/-- Generated-path transport of the fixed-query heterogeneous worker moment.
This is the missing first source-facing step toward the heterogeneous Eq. (33):
the exact worker coefficient is retained and the squared displacement is
integrated into `stepMoment`. -/
theorem heterogeneous_finite_sum_generated_worker_innovation_centered_second_moment
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n)
    (hStep : StepMomentWellDefined
      (heterogeneousFiniteSumProcess (b0 := b0) A x0)
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) k) :
    let law := heterogeneousFiniteSumPathLaw A
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
    Integrable (heterogeneousFiniteSumWorkerInnovation A x0 k i) law ∧
      Integrable
        (fun path =>
          ‖heterogeneousFiniteSumWorkerInnovation A x0 k i path‖ ^ 2) law ∧
      (∫ path, heterogeneousFiniteSumWorkerInnovation A x0 k i path ∂law) = 0 ∧
      (∫ path, ‖heterogeneousFiniteSumWorkerInnovation A x0 k i path‖ ^ 2
          ∂law) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
          stepMoment (heterogeneousFiniteSumProcess (b0 := b0) A x0) law k := by
  classical
  dsimp only
  let P := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let query0 := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    ((heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x,
      (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x)
  let Query := Set.range query0
  let query : (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) → Query :=
    fun path => ⟨query0 path, ⟨path, rfl⟩⟩
  let sample := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    ((path k).2.1 i, (path k).2.2 i)
  let innovation := fun (z : Query)
      (q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
    A.quantizer.apply
        (finiteSumWorkerBatchDifference A.problem q.1 i z.1.1 z.1.2) q.2 -
      localGradientDifference (finiteSumLocalProblem A.problem) i z.1.1 z.1.2
  let coeff := ω * (Llocal i) ^ 2 +
    (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1
  let budget := fun z : Query => coeff * ‖z.1.1 - z.1.2‖ ^ 2
  let ν := (workerBatchLaw k i).prod A.quantizer.law
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hquery0 : Measurable query0 := by
    have hk := (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (heterogeneousFiniteSumStrictPast_le
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
    have hks := (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 (k + 1)).mono
        (heterogeneousFiniteSumStrictPast_le
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) (k + 1)) le_rfl
    exact ((measurable_state_x d).comp hks).prodMk
      ((measurable_state_x d).comp hk)
  have hquery : Measurable query := Measurable.subtype_mk hquery0
  have hsample : Measurable sample := by
    dsimp [sample]
    fun_prop
  have hindep0 : ProbabilityTheory.IndepFun query0 sample P := by
    simpa [query0, sample, P] using
      heterogeneousFiniteSum_strictPast_query_indep_worker_noise
        A x0 workerBatchLaw hBatchLaw k i
  have hindep : ProbabilityTheory.IndepFun query sample P := by
    have hquery_comap : Measurable[MeasurableSpace.comap query0 inferInstance]
        query := Measurable.subtype_mk (measurable_iff_comap_le.mpr le_rfl)
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap query0 inferInstance)
        (MeasurableSpace.comap sample inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hindep0
    exact indepFun_of_measurable_left_of_indep_comap hquery_comap hcomap
  have hdist : Measure.map sample P = ν := by
    calc
      Measure.map sample P =
          Measure.map
            (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              (z.2.1 i, z.2.2 i))
            (Measure.map
              (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
                path k) P) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · fun_prop
          · exact measurable_pi_apply k
      _ = Measure.map
            (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              (z.2.1 i, z.2.2 i))
            (heterogeneousFiniteSumRoundLaw A
              (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)) := by
          rw [heterogeneousFiniteSumPathLaw_round_marginal
            A workerBatchLaw hBatchLaw k]
      _ = (workerBatchLaw k i).prod A.quantizer.law := by
        unfold heterogeneousFiniteSumRoundLaw
        rw [show Measure.map
            (fun z : Bool ×
              (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
                (z.2.1 i, z.2.2 i))
            ((refreshLaw A.refreshProbability A.refresh_admissible).prod
              ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                (workerCompressionLaw A.quantizer))) =
            Measure.map
              (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
                (z.1 i, z.2 i))
              ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                (workerCompressionLaw A.quantizer)) by
              calc
                _ = Measure.map
                    (fun z : HeterogeneousFiniteSumBatch n m b0 ×
                      (Worker n → Ξ) => (z.1 i, z.2 i))
                    (Measure.map Prod.snd
                      ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                        ((heterogeneousFiniteSumIndependentBatchLaw
                          workerBatchLaw k).prod
                          (workerCompressionLaw A.quantizer)))) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · fun_prop
                      · exact measurable_snd
                _ = _ := by
                  rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]]
        calc
          Measure.map
              (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
                (z.1 i, z.2 i))
              ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                (workerCompressionLaw A.quantizer)) =
            (Measure.map (fun batch : HeterogeneousFiniteSumBatch n m b0 =>
                batch i)
                (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)).prod
              (Measure.map (fun q : Worker n → Ξ => q i)
                (workerCompressionLaw A.quantizer)) := by
                  simpa [Prod.map] using
                    (MeasureTheory.Measure.map_prod_map
                      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)
                      (workerCompressionLaw A.quantizer)
                      (measurable_pi_apply i) (measurable_pi_apply i)).symm
          _ = (workerBatchLaw k i).prod A.quantizer.law := by
            rw [heterogeneousFiniteSumIndependentBatchLaw_worker_marginal
              workerBatchLaw hBatchLaw k i,
              workerCompressionLaw_component_marginal A.quantizer i]
  have hinnovation : Measurable (Function.uncurry innovation) := by
    have hpair : Measurable
        (fun p : Query ×
            (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
          ((p.1.1, p.2.1) :
            (Point d × Point d) × FiniteSumWorkerBatch m (b0 i))) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)
    have hdiff : Measurable
        (fun p : Query ×
            (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
          finiteSumWorkerBatchDifference A.problem p.2.1 i p.1.1.1 p.1.1.2) := by
      simpa only [Function.comp_apply] using
        (finiteSumWorkerBatchDifference_joint_measurable
          (b0 := b0 i) A.problem i).comp hpair
    have hquantized := A.quantizer.measurable_apply_uncurry.comp
      (hdiff.prodMk (measurable_snd.comp measurable_snd))
    have hmean : Measurable
        (fun p : Query ×
            (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
          localGradientDifference (finiteSumLocalProblem A.problem) i
            p.1.1.1 p.1.1.2) := by
      unfold localGradientDifference
      exact ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp
        (measurable_fst.comp (measurable_subtype_coe.comp measurable_fst))).sub
        ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp
          (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst)))
    simpa [innovation, Function.uncurry] using hquantized.sub hmean
  have hbudget : Measurable budget := by
    dsimp [budget]
    fun_prop
  have hfixed : ∀ z : Query,
      Integrable (fun q => ‖innovation z q‖ ^ 2) ν ∧
        (∫ q, innovation z q ∂ν) = 0 ∧
        (∫ q, ‖innovation z q‖ ^ 2 ∂ν) ≤ budget z := by
    intro z
    rcases z with ⟨z, ⟨path, rfl⟩⟩
    simpa [innovation, budget, coeff, ν, query0,
      heterogeneousFiniteSumBatchDifference] using
      heterogeneous_finite_sum_fixed_worker_innovation_centered_second_moment
        A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k i path
  have hbudget_int : Integrable (fun path => budget (query path)) P := by
    simpa [budget, query, query0, coeff, P, StepMomentWellDefined] using
      hStep.const_mul coeff
  have hsq_prod : AEStronglyMeasurable
      (fun p : Query × (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
        ‖innovation p.1 p.2‖ ^ 2) ((Measure.map query P).prod ν) :=
    hinnovation.norm.pow_const 2 |>.aestronglyMeasurable
  have hsq : Integrable
      (fun path => ‖innovation (query path) (sample path)‖ ^ 2) P :=
    integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := P) (ν := ν) (φ := fun z q => ‖innovation z q‖ ^ 2)
      (B := budget) (X := query) (Y := sample) hsq_prod
      hbudget.aestronglyMeasurable hquery.aemeasurable hsample.aemeasurable
      hindep hdist (fun _ _ => sq_nonneg _) (fun z => (hfixed z).1)
      hbudget_int (fun z => (hfixed z).2.2)
  have hsq_le :
      (∫ path, ‖innovation (query path) (sample path)‖ ^ 2 ∂P) ≤
        ∫ path, budget (query path) ∂P :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := P) (ν := ν) (φ := fun z q => ‖innovation z q‖ ^ 2)
      (B := budget) (X := query) (Y := sample) hsq_prod
      hbudget.aestronglyMeasurable hquery.aemeasurable hsample.aemeasurable
      hindep hdist hsq hbudget_int (fun z => (hfixed z).2.2)
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [innovation, query, query0, sample, P,
      heterogeneousFiniteSumWorkerInnovation,
      heterogeneousFiniteSumBatchDifference] using hint
  · simpa [innovation, query, query0, sample, P,
      heterogeneousFiniteSumWorkerInnovation,
      heterogeneousFiniteSumBatchDifference] using hsq
  · simpa [innovation, query, query0, sample, P,
      heterogeneousFiniteSumWorkerInnovation,
      heterogeneousFiniteSumBatchDifference] using hmean
  · have hbudget_eq :
        (∫ path, budget (query path) ∂P) = coeff *
          stepMoment (heterogeneousFiniteSumProcess (b0 := b0) A x0) P k := by
      simp only [budget, query, query0, integral_const_mul]
      rfl
    rw [hbudget_eq] at hsq_le
    simpa [innovation, query, query0, sample, P, coeff,
      heterogeneousFiniteSumWorkerInnovation,
      heterogeneousFiniteSumBatchDifference] using hsq_le

/-- The adaptive heterogeneous query together with one worker's current noise
is independent of every distinct worker's current noise.  This is the
source-level conditional-independence input for the off-diagonal terms in
Remark D.1's version of Eq. (33). -/
theorem heterogeneousFiniteSum_query_peer_noise_indep_worker_noise
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (k : ℕ) (i j : Worker n) (hij : i ≠ j) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (((heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x,
            (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x),
          ((path k).2.1 j, (path k).2.2 j)))
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i))
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) := by
  classical
  let P := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let query := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (primalStep A.stepSize
        (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path),
      (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x)
  let pastBlock := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    fun q : Fin k => path q.1
  let current := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    path k
  let prefixLaw := Measure.map pastBlock P
  let roundLaw := heterogeneousFiniteSumRoundLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)
  let joined := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (pastBlock path, ((path k).2.1 j, (path k).2.2 j))
  let Z := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (pastBlock path, current path)
  let leftProd := fun z :
      (Fin k → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) ×
        HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (z.1, (z.2.2.1 j, z.2.2.2 j))
  let rightProd := fun z :
      (Fin k → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) ×
        HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (z.2.2.1 i, z.2.2.2 i)
  letI (t : ℕ) (q : Worker n) : IsProbabilityMeasure (workerBatchLaw t q) :=
    hBatchLaw t q
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hpastBlock : Measurable pastBlock := by
    refine measurable_pi_lambda _ fun q => ?_
    exact measurable_pi_apply q.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hZ : Measurable Z := hpastBlock.prodMk hcurrent
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastBlock.aemeasurable
  have hZlaw : Measure.map Z P = prefixLaw.prod roundLaw := by
    simpa [Z, pastBlock, current, prefixLaw, roundLaw, P,
      heterogeneousFiniteSumPathLaw] using
      (infinitePi_prefix_current_map_eq_prod
        (fun t : ℕ => heterogeneousFiniteSumRoundLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) k)
  have hround_pair : ProbabilityTheory.IndepFun
      (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (z.2.1 j, z.2.2 j))
      (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (z.2.1 i, z.2.2 i)) roundLaw := by
    exact (heterogeneousFiniteSumRoundLaw_worker_noise_iIndep
      A workerBatchLaw hBatchLaw k).indepFun (Ne.symm hij)
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (prefixLaw.prod roundLaw) := by
    exact indepFun_prod_left_adjoin_of_indepFun prefixLaw roundLaw
      (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (z.2.1 j, z.2.2 j))
      (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (z.2.1 i, z.2.2 i)) (by fun_prop) (by fun_prop) hround_pair
  have hleftProd : Measurable leftProd := by dsimp [leftProd]; fun_prop
  have hrightProd : Measurable rightProd := by dsimp [rightProd]; fun_prop
  have hpull : ProbabilityTheory.IndepFun joined
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i)) P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hpastBlock.prodMk (by fun_prop)).aemeasurable)
      ((show Measurable
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i)) by fun_prop).aemeasurable)).2
    calc
      Measure.map (fun path =>
          (joined path, ((path k).2.1 i, (path k).2.2 i))) P =
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
      _ = (Measure.map joined P).prod
          (Measure.map (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            ((path k).2.1 i, (path k).2.2 i)) P) := by
        rw [show Measure.map leftProd (prefixLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            _ = Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (prefixLaw.prod roundLaw) =
            Measure.map (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              ((path k).2.1 i, (path k).2.2 i)) P by
          calc
            _ = Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  have hstrict_le : heterogeneousFiniteSumStrictPast
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
    (measurable_fst.comp hjoined_comap).comap_le
  have hpeer_joined : MeasurableSpace.comap
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 j, (path k).2.2 j)) inferInstance ≤
      MeasurableSpace.comap joined inferInstance :=
    (measurable_snd.comp hjoined_comap).comap_le
  have hjoined_indep : ProbabilityTheory.Indep
      (MeasurableSpace.comap joined inferInstance)
      (MeasurableSpace.comap
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i)) inferInstance) P := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpull
  have hpast_peer_indep : ProbabilityTheory.Indep
      (heterogeneousFiniteSumStrictPast
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ⊔
        MeasurableSpace.comap
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            ((path k).2.1 j, (path k).2.2 j)) inferInstance)
      (MeasurableSpace.comap
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i)) inferInstance) P := by
    apply ProbabilityTheory.indep_of_indep_of_le_left hjoined_indep
    exact sup_le (le_trans hstrict_le hpast_joined) hpeer_joined
  have hquery : Measurable[heterogeneousFiniteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] query := by
    have hs := heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k
    exact ((measurable_primalStep A.stepSize).comp hs).prodMk
      ((measurable_state_x d).comp hs)
  have hresult := indepFun_prod_past_current_of_indep_current
    hquery hpast_peer_indep
  simpa [query, P, heterogeneousFiniteSumProcess,
    SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep] using hresult

/-- Workerwise averaging of the preceding fixed-query calculation gives the
exact heterogeneous coefficient appearing in Remark D.1.  This is the scalar
aggregation step immediately before the cross-worker covariance cancellation
in the proof of Eq. (33). -/
theorem heterogeneous_finite_sum_fixed_worker_innovation_average_second_moment_le
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :
    let x := (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x
    let xNext :=
      (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
    average (fun i : Worker n =>
      ∫ q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ,
        ‖A.quantizer.apply
            (finiteSumWorkerBatchDifference A.problem q.1 i xNext x) q.2 -
          localGradientDifference (finiteSumLocalProblem A.problem) i xNext x‖ ^ 2
        ∂(workerBatchLaw k i).prod A.quantizer.law) ≤
      (ω * (rootMeanSquare Llocal) ^ 2 +
        (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
  dsimp
  have hpoint : ∀ i : Worker n,
      (∫ q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ,
        ‖A.quantizer.apply
            (finiteSumWorkerBatchDifference A.problem q.1 i
              (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
              (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x) q.2 -
          localGradientDifference (finiteSumLocalProblem A.problem) i
            (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
            (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x‖ ^ 2
        ∂(workerBatchLaw k i).prod A.quantizer.law) ≤
      (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
        ‖(heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x -
          (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x‖ ^ 2 := by
    intro i
    exact (heterogeneous_finite_sum_fixed_worker_innovation_centered_second_moment
      A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i path).2.2
  have havg := average_le_average_of_pointwise hpoint
  calc
    average (fun i : Worker n =>
        ∫ q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ,
          ‖A.quantizer.apply
              (finiteSumWorkerBatchDifference A.problem q.1 i
                (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
                (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x) q.2 -
            localGradientDifference (finiteSumLocalProblem A.problem) i
              (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
              (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x‖ ^ 2
          ∂(workerBatchLaw k i).prod A.quantizer.law) ≤
        average (fun i : Worker n =>
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
            ‖(heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x -
              (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x‖ ^ 2) :=
      havg
    _ = (ω * (rootMeanSquare Llocal) ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
        ‖(heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x -
          (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x‖ ^ 2 := by
      have hmean_nonneg : 0 ≤ meanSquare Llocal := by
        unfold meanSquare average SOptLib.finiteUniformAverage
        positivity
      have hrms : (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
        unfold rootMeanSquare
        exact Real.sq_sqrt hmean_nonneg
      rw [hrms]
      unfold meanSquare heterogeneousFiniteBatchSmoothnessTerm average
        SOptLib.finiteUniformAverage
      simp only [smul_eq_mul]
      rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ i : Worker n,
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) =
          (1 + ω) * ∑ i : Worker n, (ℒlocal i) ^ 2 / (b0 i).1 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
      ring

/-- Simultaneous scalar `L²` closure for the generated heterogeneous Algorithm 2
process.  This is proved from the source smoothness and product-law semantics
and is consumed immediately by the heterogeneous Eq. (33) theorem below. -/
theorem heterogeneous_finite_sum_process_l2_invariant
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    ∀ t,
      Integrable (fun path =>
        ‖(heterogeneousFiniteSumProcess (b0 := b0) A x0 t path).x - x0‖ ^ 2)
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      Integrable (fun path =>
        ‖(heterogeneousFiniteSumProcess (b0 := b0) A x0 t path).g‖ ^ 2)
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      EstimatorErrorMomentWellDefined (finiteSumLocalProblem A.problem)
        (heterogeneousFiniteSumProcess (b0 := b0) A x0)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) t ∧
      StepMomentWellDefined (heterogeneousFiniteSumProcess (b0 := b0) A x0)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) t := by
  classical
  let P := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
  let localP := finiteSumLocalProblem A.problem
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (workerBatchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hstate_meas : ∀ t, Measurable (run t) := by
    intro t
    exact (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 t).mono
        (heterogeneousFiniteSumStrictPast_le
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) t) le_rfl
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
        exact integrable_const (c := (0 : ℝ))
      have hg0 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) P := by
        have heq : (fun path => ‖(run 0 path).g‖ ^ 2) =
            (fun _ => ‖globalGradient localP x0‖ ^ 2) := by
          funext path
          rfl
        rw [heq]
        exact integrable_const (c := ‖globalGradient localP x0‖ ^ 2)
      have herr0 : EstimatorErrorMomentWellDefined localP run P 0 := by
        have heq : (fun path =>
              ‖(run 0 path).g - globalGradient localP (run 0 path).x‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext path
          change ‖globalGradient localP x0 - globalGradient localP x0‖ ^ 2 = 0
          simp
        rw [EstimatorErrorMomentWellDefined, heq]
        exact integrable_const (c := (0 : ℝ))
      have hstep0 : StepMomentWellDefined run P 0 := by
        have heq : (fun path => ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
            (fun _ => ‖(-(A.stepSize : ℝ)) • globalGradient localP x0‖ ^ 2) := by
          funext path
          change ‖(x0 - (A.stepSize : ℝ) • globalGradient localP x0) - x0‖ ^ 2 = _
          congr 2
          rw [neg_smul]
          abel
        rw [StepMomentWellDefined, heq]
        exact integrable_const
          (c := ‖(-(A.stepSize : ℝ)) • globalGradient localP x0‖ ^ 2)
      exact ⟨hx0, hg0, herr0, hstep0⟩
  | succ t ih =>
      have hstep : StepMomentWellDefined run P t := ih.2.2.2
      have hx_succ : Integrable
          (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) P := by
        have h := integrable_sq_norm_sub_smul_sub_const_of_l2
          (fun path => (run t path).x) (fun path => (run t path).g)
          x0 (A.stepSize : ℝ) (hx_meas t) (hg_meas t) ih.1 ih.2.1
        simpa [run, heterogeneousFiniteSumProcess,
          SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep,
          primalStep_eq] using h
      have hworker_sq : ∀ i : Worker n, Integrable
          (fun path => ‖heterogeneousFiniteSumWorkerEstimator A (path t)
            (run t path) i‖ ^ 2) P := by
        intro i
        let innovation := heterogeneousFiniteSumWorkerInnovation
          (b0 := b0) A x0 t i
        let gradDiff := fun path =>
          localGradientDifference localP i (run (t + 1) path).x (run t path).x
        let carried := fun path =>
          (run t path).g + (innovation path + gradDiff path)
        let refreshed := fun path => localGradient localP i (run (t + 1) path).x
        let s : Set (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :=
          {path | (path t).1 = true}
        have hinn :=
          heterogeneous_finite_sum_generated_worker_innovation_centered_second_moment
            A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw
              hAverageSmooth hQuantizer t i hstep
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
          simpa [innovation] using hinn.1.aestronglyMeasurable
        have hcenter_sq : Integrable
            (fun path => ‖innovation path + gradDiff path‖ ^ 2) P :=
          integrable_sq_norm_add hinn_meas hdiff_meas hinn.2.1 hdiff_sq
        have hcarried_sq : Integrable (fun path => ‖carried path‖ ^ 2) P :=
          integrable_sq_norm_add (hg_meas t) (hinn_meas.add hdiff_meas)
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
            (fun path => ‖heterogeneousFiniteSumWorkerEstimator A (path t)
              (run t path) i‖ ^ 2) := by
          funext path
          by_cases hp : (path t).1 = true
          · simp [s, Set.piecewise, hp, refreshed, carried, innovation, gradDiff,
              run, localP, heterogeneousFiniteSumWorkerEstimator,
              heterogeneousFiniteSumBatchDifference,
              heterogeneousFiniteSumWorkerInnovation, localGradientDifference,
              heterogeneousFiniteSumProcess, SOptLib.recursiveIterateProcess,
              heterogeneousFiniteSumStep, primalStep_eq]
          · simp [s, Set.piecewise, hp, refreshed, carried, innovation, gradDiff,
              run, localP, heterogeneousFiniteSumWorkerEstimator,
              heterogeneousFiniteSumBatchDifference,
              heterogeneousFiniteSumWorkerInnovation, localGradientDifference,
              heterogeneousFiniteSumProcess, SOptLib.recursiveIterateProcess,
              heterogeneousFiniteSumStep, primalStep_eq]
        rw [← heq]
        exact hpiece
      have hg_succ : Integrable (fun path => ‖(run (t + 1) path).g‖ ^ 2) P := by
        apply integrable_sq_norm_centeredMiniBatchAverage P Finset.univ n.1
          (fun i path => heterogeneousFiniteSumWorkerEstimator A (path t)
            (run t path) i) (fun path => (run (t + 1) path).g)
        · intro i _hi
          exact (heterogeneousFiniteSumWorkerEstimator_round_joint_measurable A i).comp
            ((hstate_meas t).prodMk (measurable_pi_apply t)) |>.aestronglyMeasurable
        · intro i _hi
          exact hworker_sq i
        · funext path
          simp [run, heterogeneousFiniteSumProcess,
            SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep,
            average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
      have hgrad_global_succ := hglobal_grad_l2 (t + 1) hx_succ
      have herr_succ : EstimatorErrorMomentWellDefined localP run P (t + 1) := by
        exact integrable_sq_norm_sub (hg_meas (t + 1))
          ((measurable_gradient (globalObjective localP)).comp
            ((measurable_state_x d).comp (hstate_meas (t + 1))) |>.aestronglyMeasurable)
          hg_succ hgrad_global_succ
      have hstep_succ : StepMomentWellDefined run P (t + 1) := by
        have hscaled := integrable_sq_norm_const_smul (-(A.stepSize : ℝ)) hg_succ
        simpa [StepMomentWellDefined, run, heterogeneousFiniteSumProcess,
          SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep,
          primalStep_eq] using hscaled
      exact ⟨hx_succ, hg_succ, herr_succ, hstep_succ⟩

set_option maxHeartbeats 3200000 in
/-- `book/MARINA/MARINA.json#/key_lemmas/6` and `#/key_lemmas/15`:
the formula-level heterogeneous version of Eq. (33).  Unlike the earlier
workerwise moment lemmas, this source-stage interface supplies all moment
well-definedness facts from the generated process itself and exposes exactly
the coefficient used by Remark D.1. -/
theorem heterogeneous_finite_sum_estimator_recurrence_33
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ) :
    let law := heterogeneousFiniteSumPathLaw A
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
    let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
    EstimatorErrorMomentWellDefined (finiteSumLocalProblem A.problem) run law (k + 1) ∧
    EstimatorErrorMomentWellDefined (finiteSumLocalProblem A.problem) run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment (finiteSumLocalProblem A.problem) run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment (finiteSumLocalProblem A.problem) run law k := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  dsimp only
  have hL2 := heterogeneous_finite_sum_process_l2_invariant
    A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
      hQuantizer
  have hWorkerMoment : ∀ i : Worker n,
      Integrable (heterogeneousFiniteSumWorkerInnovation A x0 k i)
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      Integrable (fun path =>
          ‖heterogeneousFiniteSumWorkerInnovation A x0 k i path‖ ^ 2)
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      (∫ path, heterogeneousFiniteSumWorkerInnovation A x0 k i path
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) = 0 ∧
      (∫ path, ‖heterogeneousFiniteSumWorkerInnovation A x0 k i path‖ ^ 2
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
        stepMoment (heterogeneousFiniteSumProcess (b0 := b0) A x0)
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) k := by
    intro i
    exact heterogeneous_finite_sum_generated_worker_innovation_centered_second_moment
      A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k i (hL2 k).2.2.2
  have hWorkerFresh : ∀ {i j : Worker n}, i ≠ j →
      ProbabilityTheory.IndepFun
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          (((heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x,
              (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x),
            ((path k).2.1 j, (path k).2.2 j)))
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i))
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) := by
    intro i j hij
    exact heterogeneousFiniteSum_query_peer_noise_indep_worker_noise
      A x0 workerBatchLaw hBatchLaw k i j hij
  let P := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
  let localP := finiteSumLocalProblem A.problem
  let workerNoise := fun i : Worker n =>
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      ((path k).2.1 i, (path k).2.2 i)
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (workerBatchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hWorkerNoiseLaw : ∀ i : Worker n,
      Measure.map (workerNoise i) P =
        (workerBatchLaw k i).prod A.quantizer.law := by
    intro i
    calc
      Measure.map (workerNoise i) P =
          Measure.map
            (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              (z.2.1 i, z.2.2 i))
            (Measure.map
              (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
                path k) P) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · fun_prop
          · exact measurable_pi_apply k
      _ = Measure.map
            (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              (z.2.1 i, z.2.2 i))
            (heterogeneousFiniteSumRoundLaw A
              (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)) := by
          rw [heterogeneousFiniteSumPathLaw_round_marginal
            A workerBatchLaw hBatchLaw k]
      _ = (workerBatchLaw k i).prod A.quantizer.law := by
        unfold heterogeneousFiniteSumRoundLaw
        rw [show Measure.map
            (fun z : Bool ×
              (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
                (z.2.1 i, z.2.2 i))
            ((refreshLaw A.refreshProbability A.refresh_admissible).prod
              ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                (workerCompressionLaw A.quantizer))) =
            Measure.map
              (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
                (z.1 i, z.2 i))
              ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                (workerCompressionLaw A.quantizer)) by
              calc
                _ = Measure.map
                    (fun z : HeterogeneousFiniteSumBatch n m b0 ×
                      (Worker n → Ξ) => (z.1 i, z.2 i))
                    (Measure.map Prod.snd
                      ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                        ((heterogeneousFiniteSumIndependentBatchLaw
                          workerBatchLaw k).prod
                          (workerCompressionLaw A.quantizer)))) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · fun_prop
                      · exact measurable_snd
                _ = _ := by
                  rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]]
        calc
          Measure.map
              (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
                (z.1 i, z.2 i))
              ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                (workerCompressionLaw A.quantizer)) =
            (Measure.map (fun batch : HeterogeneousFiniteSumBatch n m b0 =>
                batch i)
                (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)).prod
              (Measure.map (fun q : Worker n → Ξ => q i)
                (workerCompressionLaw A.quantizer)) := by
                  simpa [Prod.map] using
                    (MeasureTheory.Measure.map_prod_map
                      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)
                      (workerCompressionLaw A.quantizer)
                      (measurable_pi_apply i) (measurable_pi_apply i)).symm
          _ = (workerBatchLaw k i).prod A.quantizer.law := by
            rw [heterogeneousFiniteSumIndependentBatchLaw_worker_marginal
              workerBatchLaw hBatchLaw k i,
              workerCompressionLaw_component_marginal A.quantizer i]
  have hWorkerCross : ∀ {i j : Worker n}, i ≠ j →
      (∫ path,
        ⟪heterogeneousFiniteSumWorkerInnovation A x0 k i path,
          heterogeneousFiniteSumWorkerInnovation A x0 k j path⟫_ℝ ∂P) = 0 := by
    intro i j hij
    let query0 := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      ((run (k + 1) path).x, (run k path).x)
    let Query := Set.range query0
    let query : (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) → Query :=
      fun path => ⟨query0 path, ⟨path, rfl⟩⟩
    let innovation := fun (q : Worker n) (z : Query)
        (s : HeterogeneousFiniteSumWorkerBatch m (b0 q) × Ξ) =>
      A.quantizer.apply
          (finiteSumWorkerBatchDifference A.problem s.1 q z.1.1 z.1.2) s.2 -
        localGradientDifference localP q z.1.1 z.1.2
    let param := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      (query path, workerNoise j path)
    let residual := fun w : Query ×
        (HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ) =>
      fun s : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ =>
        innovation i w.1 s
    let direction := fun w : Query ×
        (HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ) =>
      innovation j w.1 w.2
    let ν := (workerBatchLaw k i).prod A.quantizer.law
    have hquery0 : Measurable query0 := by
      have hk := (heterogeneousFiniteSumProcess_strictPast_measurable
        (b0 := b0) A x0 k).mono
          (heterogeneousFiniteSumStrictPast_le
            (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
      have hks := (heterogeneousFiniteSumProcess_strictPast_measurable
        (b0 := b0) A x0 (k + 1)).mono
          (heterogeneousFiniteSumStrictPast_le
            (n := n) (m := m) (b0 := b0) (Ξ := Ξ) (k + 1)) le_rfl
      exact ((measurable_state_x d).comp hks).prodMk
        ((measurable_state_x d).comp hk)
    have hquery : Measurable query := Measurable.subtype_mk hquery0
    have hnoise : ∀ q : Worker n, Measurable (workerNoise q) := by
      intro q
      dsimp [workerNoise]
      fun_prop
    have hinnovation : ∀ q : Worker n,
        Measurable (Function.uncurry (innovation q)) := by
      intro q
      have hpair : Measurable
          (fun p : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 q) × Ξ) =>
            ((p.1.1, p.2.1) :
              (Point d × Point d) × FiniteSumWorkerBatch m (b0 q))) :=
        (measurable_subtype_coe.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd)
      have hdiff := (finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0 q) A.problem q).comp hpair
      have hquantized := A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk (measurable_snd.comp measurable_snd))
      have hmean : Measurable
          (fun p : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 q) × Ξ) =>
            localGradientDifference localP q p.1.1.1 p.1.1.2) := by
        unfold localGradientDifference
        exact ((measurable_localGradient localP q).comp
          (measurable_fst.comp
            (measurable_subtype_coe.comp measurable_fst))).sub
          ((measurable_localGradient localP q).comp
            (measurable_snd.comp
              (measurable_subtype_coe.comp measurable_fst)))
      simpa [innovation, Function.uncurry] using hquantized.sub hmean
    have hparam : Measurable param := hquery.prodMk (hnoise j)
    have hindepRaw := hWorkerFresh (i := i) (j := j) hij
    have hindep : ProbabilityTheory.IndepFun param (workerNoise i) P := by
      let raw := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (query0 path, workerNoise j path)
      have hraw_comap : Measurable[MeasurableSpace.comap raw inferInstance] raw :=
        measurable_iff_comap_le.mpr le_rfl
      have hparam_comap : Measurable[MeasurableSpace.comap raw inferInstance]
          param := by
        have hq : Measurable[MeasurableSpace.comap raw inferInstance] query :=
          Measurable.subtype_mk (measurable_fst.comp hraw_comap)
        exact hq.prodMk (measurable_snd.comp hraw_comap)
      have hraw_sigma : ProbabilityTheory.Indep
          (MeasurableSpace.comap raw inferInstance)
          (MeasurableSpace.comap (workerNoise i) inferInstance) P := by
        simpa [raw, query0, workerNoise, run,
          ProbabilityTheory.IndepFun_iff_Indep] using hindepRaw
      exact indepFun_of_measurable_left_of_indep_comap hparam_comap hraw_sigma
    have hresidual : Measurable
        (fun p : (Query ×
            (HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ)) ×
            (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
          residual p.1 p.2) := by
      have harg : Measurable
          (fun p : (Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ)) ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
            (p.1.1, p.2)) :=
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
      simpa only [residual] using (hinnovation i).comp harg
    have hdirection : Measurable direction := by
      have harg : Measurable
          (fun w : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ) =>
            (w.1, w.2)) := measurable_fst.prodMk measurable_snd
      simpa only [direction] using (hinnovation j).comp harg
    have hfixed : ∀ w : Query ×
        (HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ),
        Integrable (residual w) ν ∧ ∫ s, residual w s ∂ν = 0 := by
      intro w
      rcases w with ⟨⟨z, hz⟩, ws⟩
      rcases hz with ⟨path, rfl⟩
      have hw := heterogeneous_finite_sum_fixed_worker_innovation_centered_second_moment
        A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k i path
      constructor
      · apply integrable_of_integrable_norm_sq
          ((hinnovation i).comp (measurable_const.prodMk measurable_id)
            |>.aestronglyMeasurable)
        simpa [residual, innovation, ν, query0, run,
          heterogeneousFiniteSumBatchDifference] using hw.1
      · simpa [residual, innovation, ν, query0, run,
          heterogeneousFiniteSumBatchDifference] using hw.2.1
    have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      P ν param (workerNoise i) residual direction hresidual hdirection hparam
        (hnoise i) hindep (hWorkerNoiseLaw i)
        (fun w => (hfixed w).1) (fun w => (hfixed w).2)
    simpa [P, param, query, query0, workerNoise, residual, direction,
      innovation, run, localP, heterogeneousFiniteSumWorkerInnovation,
      heterogeneousFiniteSumBatchDifference, real_inner_comm] using hzero
  have hWorkerAverage :
      Integrable (fun path => ‖average (fun i : Worker n =>
          heterogeneousFiniteSumWorkerInnovation A x0 k i path)‖ ^ 2) P ∧
      (∫ path, ‖average (fun i : Worker n =>
          heterogeneousFiniteSumWorkerInnovation A x0 k i path)‖ ^ 2 ∂P) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run P k := by
    let eps := fun i : Worker n =>
      heterogeneousFiniteSumWorkerInnovation (b0 := b0) A x0 k i
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      P (Finset.univ : Finset (Worker n)) eps
      (fun i _ => (hWorkerMoment i).1.aestronglyMeasurable)
      (fun i _ => (hWorkerMoment i).2.1)
      (fun i _ j _ hij => by simpa [eps] using hWorkerCross hij)
    have havg_int : Integrable
        (fun path => ‖average (fun i : Worker n => eps i path)‖ ^ 2) P := by
      apply integrable_sq_norm_centeredMiniBatchAverage P
        (Finset.univ : Finset (Worker n)) n.1 eps
        (fun path => average (fun i : Worker n => eps i path))
      · intro i _
        exact (hWorkerMoment i).1.aestronglyMeasurable
      · intro i _
        exact (hWorkerMoment i).2.1
      · funext path
        simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
    refine ⟨by simpa [eps] using havg_int, ?_⟩
    have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    calc
      (∫ path, ‖average (fun i : Worker n =>
          heterogeneousFiniteSumWorkerInnovation A x0 k i path)‖ ^ 2 ∂P) =
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
            (ω * (Llocal i) ^ 2 +
              (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
              stepMoment run P k := by
        gcongr with i
        exact (hWorkerMoment i).2.2.2
      _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run P k := by
        have hmean_nonneg : 0 ≤ meanSquare Llocal := by
          unfold meanSquare average SOptLib.finiteUniformAverage
          positivity
        have hrms : (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
          unfold rootMeanSquare
          exact Real.sq_sqrt hmean_nonneg
        rw [hrms, ← Finset.sum_mul]
        unfold meanSquare heterogeneousFiniteBatchSmoothnessTerm average
          SOptLib.finiteUniformAverage
        simp only [smul_eq_mul, Fintype.card_fin]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [show (∑ i : Worker n,
            (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) =
            (1 + ω) * ∑ i : Worker n, (ℒlocal i) ^ 2 / (b0 i).1 by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring]
        field_simp [hn]
  refine ⟨(hL2 (k + 1)).2.2.1, (hL2 k).2.2.1, (hL2 k).2.2.2, ?_⟩
  let residual := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (run k path).g - globalGradient localP (run k path).x
  let innovation := fun i : Worker n =>
    heterogeneousFiniteSumWorkerInnovation (b0 := b0) A x0 k i
  have hstateK : Measurable (run k) :=
    (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
      (heterogeneousFiniteSumStrictPast_le
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
  have hresidual_meas : AEStronglyMeasurable residual P := by
    exact (((measurable_state_g d).comp hstateK).sub
      ((measurable_gradient (globalObjective localP)).comp
        ((measurable_state_x d).comp hstateK))).aestronglyMeasurable
  have hresidual_sq : Integrable (fun path => ‖residual path‖ ^ 2) P := by
    simpa [residual, EstimatorErrorMomentWellDefined, run, localP, P] using
      (hL2 k).2.2.1
  have hResidualWorkerCross : ∀ i : Worker n,
      (∫ path, ⟪residual path, innovation i path⟫_ℝ ∂P) = 0 := by
    intro i
    let query0 := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      run k path
    let Query := Set.range query0
    let query : (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) → Query :=
      fun path => ⟨query0 path, ⟨path, rfl⟩⟩
    let sample := workerNoise i
    let centered := fun (z : Query)
        (s : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
      let xNext := primalStep A.stepSize z.1
      A.quantizer.apply
          (finiteSumWorkerBatchDifference A.problem s.1 i xNext z.1.x) s.2 -
        localGradientDifference localP i xNext z.1.x
    let direction := fun z : Query =>
      z.1.g - globalGradient localP z.1.x
    let ν := (workerBatchLaw k i).prod A.quantizer.law
    have hquery0_past : Measurable[heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] query0 := by
      simpa [query0, run] using
        heterogeneousFiniteSumProcess_strictPast_measurable
          (b0 := b0) A x0 k
    have hquery0 : Measurable query0 := hquery0_past.mono
      (heterogeneousFiniteSumStrictPast_le
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
    have hquery : Measurable query := Measurable.subtype_mk hquery0
    have hsample : Measurable sample := by
      dsimp [sample, workerNoise]
      fun_prop
    have hindep0 : ProbabilityTheory.IndepFun query0 sample P := by
      let round := fun t
          (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) => path t
      have hroundMeas : ∀ t, Measurable (round t) :=
        fun t => measurable_pi_apply t
      have hroundIndep : ProbabilityTheory.iIndepFun round P := by
        dsimp [round, P]
        unfold heterogeneousFiniteSumPathLaw
        exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
      have hstrict : heterogeneousFiniteSumStrictPast
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
          (⨆ t ∈ ({t : ℕ | t < k} : Set ℕ),
            MeasurableSpace.comap (round t) inferInstance) := by
        refine iSup_le fun j => ?_
        exact le_iSup_of_le (j : ℕ)
          (le_iSup_of_le (show (j : ℕ) < k from j.2) le_rfl)
      have hdisjoint : Disjoint ({t : ℕ | t < k} : Set ℕ)
          ({k} : Set ℕ) := by
        rw [Set.disjoint_left]
        intro t ht htk
        exact (Nat.ne_of_lt ht) htk
      have hqueryRound : ProbabilityTheory.IndepFun query0 (round k) P :=
        SOptLib.iIndepFun_indepFun_strictPast_singleton
          round P hroundMeas hroundIndep
          (heterogeneousFiniteSumStrictPast
            (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
          ({t : ℕ | t < k} : Set ℕ) k hquery0_past hdisjoint hstrict
      have h := hqueryRound.comp measurable_id
        (show Measurable
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (z.2.1 i, z.2.2 i)) by fun_prop)
      simpa [round, sample, workerNoise, Function.comp_def] using h
    have hindep : ProbabilityTheory.IndepFun query sample P := by
      have hquery_comap : Measurable[MeasurableSpace.comap query0 inferInstance]
          query := Measurable.subtype_mk (measurable_iff_comap_le.mpr le_rfl)
      have hsigma : ProbabilityTheory.Indep
          (MeasurableSpace.comap query0 inferInstance)
          (MeasurableSpace.comap sample inferInstance) P := by
        simpa [ProbabilityTheory.IndepFun_iff_Indep] using hindep0
      exact indepFun_of_measurable_left_of_indep_comap hquery_comap hsigma
    have hcentered : Measurable (Function.uncurry centered) := by
      have hnext : Measurable
          (fun p : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
            primalStep A.stepSize p.1.1) :=
        (measurable_primalStep A.stepSize).comp
          (measurable_subtype_coe.comp measurable_fst)
      have hx : Measurable
          (fun p : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) => p.1.1.x) :=
        (measurable_state_x d).comp
          (measurable_subtype_coe.comp measurable_fst)
      have hpair : Measurable
          (fun p : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
            (((primalStep A.stepSize p.1.1, p.1.1.x), p.2.1) :
              (Point d × Point d) × FiniteSumWorkerBatch m (b0 i))) :=
        (hnext.prodMk hx).prodMk (measurable_fst.comp measurable_snd)
      have hdiff := (finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0 i) A.problem i).comp hpair
      have hquantized := A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk (measurable_snd.comp measurable_snd))
      have hmean : Measurable
          (fun p : Query ×
              (HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ) =>
            localGradientDifference localP i
              (primalStep A.stepSize p.1.1) p.1.1.x) := by
        unfold localGradientDifference
        exact ((measurable_localGradient localP i).comp hnext).sub
          ((measurable_localGradient localP i).comp hx)
      simpa [centered, Function.uncurry] using hquantized.sub hmean
    have hdirection : Measurable direction := by
      have hs : Measurable (fun z : Query => z.1) := measurable_subtype_coe
      exact ((measurable_state_g d).comp hs).sub
        ((measurable_gradient (globalObjective localP)).comp
          ((measurable_state_x d).comp hs))
    have hfixed : ∀ z : Query,
        Integrable (centered z) ν ∧ ∫ s, centered z s ∂ν = 0 := by
      intro z
      rcases z with ⟨z, ⟨path, rfl⟩⟩
      have hw := heterogeneous_finite_sum_fixed_worker_innovation_centered_second_moment
        A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k i path
      have hmeas : AEStronglyMeasurable
          (centered ⟨query0 path, ⟨path, rfl⟩⟩) ν :=
        (hcentered.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      constructor
      · apply integrable_of_integrable_norm_sq hmeas
        simpa [centered, ν, query0, run, heterogeneousFiniteSumProcess,
          SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep,
          heterogeneousFiniteSumBatchDifference] using hw.1
      · simpa [centered, ν, query0, run, heterogeneousFiniteSumProcess,
          SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep,
          heterogeneousFiniteSumBatchDifference] using hw.2.1
    have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      P ν query sample centered direction hcentered hdirection hquery hsample
        hindep (by simpa [sample] using hWorkerNoiseLaw i)
        (fun z => (hfixed z).1) (fun z => (hfixed z).2)
    simpa [P, query, query0, sample, centered, direction, residual,
      innovation, run, localP, workerNoise,
      heterogeneousFiniteSumWorkerInnovation,
      heterogeneousFiniteSumProcess, SOptLib.recursiveIterateProcess,
      heterogeneousFiniteSumStep, heterogeneousFiniteSumBatchDifference] using hzero
  have hResidualAverageCross :
      (∫ path, ⟪residual path,
          average (fun i : Worker n => innovation i path)⟫_ℝ ∂P) = 0 := by
    have h := pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
      P (Finset.univ : Finset (Worker n)) n.1 residual innovation
      hresidual_meas (fun i _ => (hWorkerMoment i).1.aestronglyMeasurable)
      hresidual_sq (fun i _ => (hWorkerMoment i).2.1)
      (fun i _ => hResidualWorkerCross i)
    simpa [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin] using h
  let avgInnovation := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    average (fun i : Worker n => innovation i path)
  have havg_meas : AEStronglyMeasurable avgInnovation P := by
    dsimp [avgInnovation]
    unfold average SOptLib.finiteUniformAverage
    have h := (Finset.aestronglyMeasurable_sum (s := Finset.univ)
      (fun i _ => (hWorkerMoment i).1.aestronglyMeasurable)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro path
    simp [innovation, Finset.sum_apply]
  have havg_sq : Integrable (fun path => ‖avgInnovation path‖ ^ 2) P := by
    simpa [avgInnovation, innovation] using hWorkerAverage.1
  have hnonrefresh_sq : Integrable
      (fun path => ‖residual path + avgInnovation path‖ ^ 2) P :=
    integrable_sq_norm_add hresidual_meas havg_meas hresidual_sq havg_sq
  have hnonrefresh_eq :
      (∫ path, ‖residual path + avgInnovation path‖ ^ 2 ∂P) =
        (∫ path, ‖residual path‖ ^ 2 ∂P) +
          ∫ path, ‖avgInnovation path‖ ^ 2 ∂P := by
    let pair : Bool →
        (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) → Point d :=
      fun b => if b then avgInnovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      P (Finset.univ : Finset Bool) pair
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
      (∫ path, ‖residual path + avgInnovation path‖ ^ 2 ∂P) ≤
        estimatorErrorMoment localP run P k +
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run P k := by
    rw [hnonrefresh_eq]
    change estimatorErrorMoment localP run P k +
        (∫ path, ‖avgInnovation path‖ ^ 2 ∂P) ≤ _
    exact add_le_add_right (by
      simpa [avgInnovation, innovation] using hWorkerAverage.2) _
  let branch := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (path k).1
  let nextResidual :=
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      (run (k + 1) path).g - globalGradient localP (run (k + 1) path).x
  have hbranch_decomp : ∀ path,
      nextResidual path = if branch path then 0
        else residual path + avgInnovation path := by
    intro path
    let s := run k path
    let xNext := primalStep A.stepSize s
    let q := fun i : Worker n =>
      A.quantizer.apply
        (heterogeneousFiniteSumBatchDifference A.problem b0
          (path k).2.1 i xNext s.x) ((path k).2.2 i)
    have hgradAvg : average (fun i : Worker n =>
        localGradient localP i xNext) = globalGradient localP xNext := by
      simpa [averageLocalGradient] using
        (globalGradient_eq_averageLocalGradient localP hSmooth.1 xNext).symm
    have hdiffAvg : average (fun i : Worker n =>
        localGradientDifference localP i xNext s.x) =
        globalGradient localP xNext - globalGradient localP s.x := by
      rw [globalGradient_eq_averageLocalGradient localP hSmooth.1 xNext,
        globalGradient_eq_averageLocalGradient localP hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : avgInnovation path =
        average q - average (fun i : Worker n =>
          localGradientDifference localP i xNext s.x) := by
      dsimp [avgInnovation, innovation, heterogeneousFiniteSumWorkerInnovation,
        q, xNext, s, run, localP, heterogeneousFiniteSumProcess,
        SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep]
      unfold average SOptLib.finiteUniformAverage
        heterogeneousFiniteSumBatchDifference
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n =>
          heterogeneousFiniteSumWorkerEstimator A (path k) s i) -
          globalGradient localP xNext := by
      rfl
    cases h : (path k).1 with
    | false =>
        simp only [branch, h, Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [heterogeneousFiniteSumWorkerEstimator, h, if_false]
        change average (fun i : Worker n => s.g + q i) -
            globalGradient localP xNext = residual path + avgInnovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s, run, localP]
        abel
    | true =>
        simp only [branch, h, if_true]
        rw [hnext]
        simp only [heterogeneousFiniteSumWorkerEstimator, h, if_true]
        change average (fun i : Worker n => localGradient localP i xNext) -
            globalGradient localP xNext = 0
        rw [hgradAvg]
        simp
  let nonrefreshSq :=
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      ‖residual path + avgInnovation path‖ ^ 2
  have hrefresh_indep : ProbabilityTheory.IndepFun nonrefreshSq branch P := by
    let pastBlock :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        fun j : Fin k => path j.1
    let current :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => path k
    let rest := fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ => z.2
    let branchRound :=
      fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ => z.1
    let restPath :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => (path k).2
    let joined :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (pastBlock path, restPath path)
    let Z := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      (pastBlock path, current path)
    let prefixLaw := Measure.map pastBlock P
    let restLaw :=
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
        (workerCompressionLaw (n := n) A.quantizer)
    let roundLaw := heterogeneousFiniteSumRoundLaw A
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)
    let leftProd := fun z :
        (Fin k → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) ×
          HeterogeneousFiniteSumRoundNoise n m b0 Ξ => (z.1, rest z.2)
    let rightProd := fun z :
        (Fin k → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) ×
          HeterogeneousFiniteSumRoundNoise n m b0 Ξ => branchRound z.2
    have hpastBlock : Measurable pastBlock := by
      refine measurable_pi_lambda _ fun j => ?_
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
      simpa [Z, pastBlock, current, prefixLaw, roundLaw, P,
        heterogeneousFiniteSumPathLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun t : ℕ => heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) k)
    have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
      have h := (ProbabilityTheory.indepFun_prod
        (μ := refreshLaw A.refreshProbability A.refresh_admissible)
        (ν := restLaw) measurable_id measurable_id).symm
      simpa [roundLaw, heterogeneousFiniteSumRoundLaw, restLaw, rest,
        branchRound] using h
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
            Measure.map (fun z => (leftProd z, rightProd z))
              (Measure.map Z P) := by
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
              _ = Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
              _ = Measure.map joined P := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · exact hleftProd
                · exact hZ]
          rw [show Measure.map rightProd (prefixLaw.prod roundLaw) =
              Measure.map branch P by
            calc
              _ = Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
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
    have hstrict_le : heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
        MeasurableSpace.comap joined inferInstance := by
      refine iSup_le fun j => ?_
      exact ((measurable_pi_apply j).comp hpast_meas).comap_le
    have hstate : Measurable[MeasurableSpace.comap joined inferInstance]
        (run k) :=
      (heterogeneousFiniteSumProcess_strictPast_measurable
        (b0 := b0) A x0 k).mono hstrict_le le_rfl
    have hres : Measurable[MeasurableSpace.comap joined inferInstance]
        residual :=
      ((measurable_state_g d).comp hstate).sub
        ((measurable_gradient (globalObjective localP)).comp
          ((measurable_state_x d).comp hstate))
    have hinn : ∀ i : Worker n,
        Measurable[MeasurableSpace.comap joined inferInstance]
          (innovation i) := by
      intro i
      have hnext := (measurable_primalStep A.stepSize).comp hstate
      have hx := (measurable_state_x d).comp hstate
      have hbatch : Measurable[MeasurableSpace.comap joined inferInstance]
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (path k).2.1 i) := by
        exact (measurable_pi_apply i).comp
          (measurable_fst.comp hrest_meas)
      have hsample : Measurable[MeasurableSpace.comap joined inferInstance]
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (path k).2.2 i) := by
        exact (measurable_pi_apply i).comp
          (measurable_snd.comp hrest_meas)
      have hpair : Measurable[MeasurableSpace.comap joined inferInstance]
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (((primalStep A.stepSize (run k path), (run k path).x),
              (path k).2.1 i) :
              (Point d × Point d) × FiniteSumWorkerBatch m (b0 i))) :=
        (hnext.prodMk hx).prodMk hbatch
      have hdiff := (finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0 i) A.problem i).comp hpair
      have hquantized := A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk hsample)
      have hmean : Measurable[MeasurableSpace.comap joined inferInstance]
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            localGradientDifference localP i
              (primalStep A.stepSize (run k path)) (run k path).x) := by
        unfold localGradientDifference
        exact ((measurable_localGradient localP i).comp hnext).sub
          ((measurable_localGradient localP i).comp hx)
      simpa [innovation, heterogeneousFiniteSumWorkerInnovation, run, localP,
        heterogeneousFiniteSumProcess, SOptLib.recursiveIterateProcess,
        heterogeneousFiniteSumStep, heterogeneousFiniteSumBatchDifference] using
          hquantized.sub hmean
    have havg : Measurable[MeasurableSpace.comap joined inferInstance]
        avgInnovation := by
      dsimp [avgInnovation]
      unfold average SOptLib.finiteUniformAverage
      exact (Finset.measurable_sum Finset.univ (fun i _ => hinn i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    have hsq : Measurable[MeasurableSpace.comap joined inferInstance]
        nonrefreshSq := by
      have hsum : Measurable[MeasurableSpace.comap joined inferInstance]
          (fun path => residual path + avgInnovation path) := hres.add havg
      have hnorm : Measurable[MeasurableSpace.comap joined inferInstance]
          (fun path => ‖residual path + avgInnovation path‖) :=
        continuous_norm.measurable.comp hsum
      exact hnorm.pow_const 2
    have hjoined_indep : ProbabilityTheory.Indep
        (MeasurableSpace.comap joined inferInstance)
        (MeasurableSpace.comap branch inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpull
    exact indepFun_of_measurable_left_of_indep_comap hsq hjoined_indep
  have hbranch_meas : Measurable branch := by
    dsimp [branch]
    fun_prop
  have hbranch_law : Measure.map branch P =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch P = Measure.map Prod.fst
          (Measure.map
            (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => path k)
            P) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact measurable_fst
        · exact measurable_pi_apply k
      _ = Measure.map Prod.fst
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)) := by
        rw [heterogeneousFiniteSumPathLaw_round_marginal
          A workerBatchLaw hBatchLaw k]
      _ = refreshLaw A.refreshProbability A.refresh_admissible := by
        simp [heterogeneousFiniteSumRoundLaw]
  have hfalse_mass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({false} : Set Bool) = 1 - A.refreshProbability := by
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
      (fun path => phi (nonrefreshSq path) (branch path)) P := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranch_meas (measurableSet_singleton false)
    have hpiece := Integrable.piecewise hs
      hnonrefresh_sq.integrableOn (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phi, Set.piecewise, nonrefreshSq] using hpiece
  have hbudget_int : Integrable (fun path => budget (nonrefreshSq path)) P := by
    simpa [budget, nonrefreshSq] using
      hnonrefresh_sq.const_mul (1 - A.refreshProbability)
  have hfixed : ∀ z : ℝ,
      (∫ b, phi z b ∂refreshLaw A.refreshProbability A.refresh_admissible) ≤
        budget z := by
    intro z
    rw [MeasureTheory.integral_fintype]
    · simp [Fintype.sum_bool, phi, budget, hfalse_mass]
    · exact Integrable.of_finite
  have hgate :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := P) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (φ := phi) (B := budget) (X := nonrefreshSq) (Y := branch)
      hphi.aestronglyMeasurable hbudget.aestronglyMeasurable
      hnonrefresh_sq.aestronglyMeasurable.aemeasurable hbranch_meas.aemeasurable
      hrefresh_indep hbranch_law hgate_int hbudget_int hfixed
  have hnext_gate : estimatorErrorMoment localP run P (k + 1) =
      ∫ path, phi (nonrefreshSq path) (branch path) ∂P := by
    apply integral_congr_ae
    filter_upwards [] with path
    rw [show (run (k + 1) path).g - globalGradient localP (run (k + 1) path).x =
      nextResidual path by rfl, hbranch_decomp]
    by_cases hb : branch path
    · simp [hb, phi]
    · simp [hb, phi, nonrefreshSq]
  have hrefresh_bound : estimatorErrorMoment localP run P (k + 1) ≤
      (1 - A.refreshProbability) * (∫ path, nonrefreshSq path ∂P) := by
    rw [hnext_gate]
    calc
      _ ≤ ∫ path, budget (nonrefreshSq path) ∂P := hgate
      _ = _ := by simp [budget, integral_const_mul]
  calc
    estimatorErrorMoment localP run P (k + 1) ≤
        (1 - A.refreshProbability) * (∫ path, nonrefreshSq path ∂P) :=
      hrefresh_bound
    _ ≤ (1 - A.refreshProbability) *
        (estimatorErrorMoment localP run P k +
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run P k) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [nonrefreshSq] using hnonrefresh_bound
      · exact sub_nonneg.mpr A.refresh_admissible.2
    _ = (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run P k +
        (1 - A.refreshProbability) * estimatorErrorMoment localP run P k := by
      ring

/-- Theorem 3.1 specialized to Remark D.1's canonical worker-product
heterogeneous minibatches and exact heterogeneous Eq. (33). -/
theorem Theorem_D1_heterogeneous_finite_sum_VR_nonconvex
    {d n m K : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    Integrable (fun z =>
        ‖globalGradient (finiteSumLocalProblem A.problem)
          (uniformOutput (K := K)
            (heterogeneousFiniteSumProcess (b0 := b0) A x0) z)‖ ^ 2)
      (uniformOutputExperimentLaw
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) K) ∧
    (∫ z, ‖globalGradient (finiteSumLocalProblem A.problem)
        (uniformOutput (K := K)
          (heterogeneousFiniteSumProcess (b0 := b0) A x0) z)‖ ^ 2
      ∂uniformOutputExperimentLaw
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) K) ≤
      2 * (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) /
        (A.stepSize * K.1) := by
  have hEq33 (k : ℕ) :=
    heterogeneous_finite_sum_estimator_recurrence_33
      A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k
  classical
  let P := finiteSumLocalProblem A.problem
  let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
  let law := heterogeneousFiniteSumPathLaw A (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (workerBatchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability workerBatchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    exact (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (heterogeneousFiniteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (heterogeneous_finite_sum_process_l2_invariant
        A x0 workerBatchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq33 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq33 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, heterogeneousFiniteSumProcess, SOptLib.recursiveIterateProcess,
        heterogeneousFiniteSumStep, primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq33 k).2.2.2
    dsimp [E, D, a, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hS : 0 ≤ heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0 := by
    unfold heterogeneousFiniteBatchSmoothnessTerm average SOptLib.finiteUniformAverage
    positivity
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact heterogeneous_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hS hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hrec0 :
        E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using
      (online_vr_nonconvex_lyapunov_step
        (V := 0) F E G D k hγ hp hDnonneg hCoeff (hDescent k) hrec0)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤ Φ 0 - Φ N := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        nlinarith
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient (finiteSumLocalProblem A.problem) x0 -
        globalGradient (finiteSumLocalProblem A.problem) x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable
        (fun _ : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => fStar) law :=
      integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    simp only [mul_zero, add_zero] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
        field_simp [ne_of_gt hγ, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (finiteSumLocalProblem A.problem)
            (uniformOutput (K := K) (heterogeneousFiniteSumProcess (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (heterogeneousFiniteSumPathLaw A (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ] using hAverageBound



/-- `book/MARINA/MARINA.json#/key_lemmas/15`, Remark D.1: the complete
heterogeneous generated process retains Theorem 3.1's convergence, iteration,
workerwise oracle, and communication conclusions with
`n⁻¹∑ᵢ ℒᵢ²/b⁰ᵢ` in the complexity bracket.  Its worker minibatches are
assembled by the canonical product law required by the source proof's
fixed-iterate independence step. -/
theorem Remark_D1_heterogeneous_finite_batches
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    let P := finiteSumLocalProblem A.problem
    let law := heterogeneousFiniteSumPathLaw A
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
    let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    (∀ K : Count,
      Integrable (fun z =>
        ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
        (uniformOutputExperimentLaw law K) ∧
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) ≤
          2 * Δ / (A.stepSize * K.1)) ∧
    ∃ K : Accuracy → Count,
      (∀ ε, NonconvexAccuracy (K ε) P run law ε) ∧
      AccuracyIterationBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) ∧
      (∀ i, AccuracyBigO
        (fun ε => heterogeneousFiniteSumOracleCallCount m (K ε) b0
          A.refreshProbability i)
        (fun ε => m.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * m.1 +
            (1 - A.refreshProbability) * (b0 i).1))) ∧
      AccuracyBigO
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  dsimp
  constructor
  · intro K
    exact Theorem_D1_heterogeneous_finite_sum_VR_nonconvex
      (K := K) A x0 workerBatchLaw Llocal ℒlocal ω fStar hLower hSmooth
        hBatchLaw hAverageSmooth hQuantizer hStep
  · -- Only the endpoint schedule/cost algebra remains.  The source
    -- convergence assertion now consumes the proved D.1 consumer above,
    -- whose recurrence supplier is the formula-level heterogeneous Eq. (33).
    let ζ : ℝ := expectedDensity A.quantizer
    let Δ : ℝ :=
      globalObjective (finiteSumLocalProblem A.problem) x0 - fStar
    let bracket : ℝ := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    have hGapNonneg : 0 ≤ Δ := by
      dsimp [Δ]
      exact sub_nonneg.mpr (hLower x0)
    have hp : 0 < A.refreshProbability := A.refresh_admissible.1
    have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
    have hζ : 0 ≤ ζ := by
      dsimp [ζ]
      exact expectedDensity_nonneg_of_unbiased hQuantizer
    have hBracketNonneg : 0 ≤ bracket := by
      dsimp [bracket]
      exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hGapEq :
          globalObjective (finiteSumLocalProblem A.problem) x0 - fStar = 0 := by
        simpa [Δ] using hGapZero.symm
      have hΔzero : Δ = 0 := hGapZero.symm
      refine ⟨fun _ => K₁, ?_, ?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD1 := Theorem_D1_heterogeneous_finite_sum_VR_nonconvex
          (K := K₁) A x0 workerBatchLaw Llocal ℒlocal ω fStar hLower hSmooth
            hBatchLaw hAverageSmooth hQuantizer hStep
        refine ⟨hD1.1, hD1.2.trans ?_⟩
        rw [hGapEq]
        simpa using (sq_nonneg (ε : ℝ))
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change Δ / (ε : ℝ) ^ 2 * bracket = 0
          rw [hΔzero]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · intro i
        unfold AccuracyBigO
        have hmne : (m.1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt m.2)
        rw [show (fun ε : Accuracy => (m.1 : ℝ) +
            Δ / (ε : ℝ) ^ 2 * bracket *
              (A.refreshProbability * m.1 +
                (1 - A.refreshProbability) * (b0 i).1)) =
            (fun _ : Accuracy => (m.1 : ℝ)) by
              funext ε
              rw [hΔzero]
              ring]
        simpa [heterogeneousFiniteSumOracleCallCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((m.1 : ℝ) + (A.refreshProbability * m.1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
            hmne accuracyToZero)
      · unfold AccuracyBigO
        have hdne : (d.1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt d.2)
        rw [show (fun ε : Accuracy => (d.1 : ℝ) +
            Δ / (ε : ℝ) ^ 2 * bracket *
              (A.refreshProbability * d.1 +
                (1 - A.refreshProbability) * ζ)) =
            (fun _ : Accuracy => (d.1 : ℝ)) by
              funext ε
              rw [hΔzero]
              ring]
        simpa [allWorkerCommunicationCount, K₁, ζ] using
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) + (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))
            hdne accuracyToZero)
    · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
      · let K₁ : Count := ⟨1, by norm_num⟩
        have hBracketEq : bracket = 0 := hBracketZero.symm
        have hLzero : rootMeanSquare Llocal = 0 := by
          have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
          have hsqrt : 0 ≤ Real.sqrt
              ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
                (ω * rootMeanSquare Llocal ^ 2 +
                  (1 + ω) *
                    heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)) :=
            Real.sqrt_nonneg _
          dsimp [bracket] at hBracketEq
          nlinarith
        have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
          (finiteSumLocalProblem A.problem) Llocal fStar hLower hSmooth hLzero
        refine ⟨fun _ => K₁, ?_, ?_, ?_, ?_⟩
        · intro ε
          unfold NonconvexAccuracy
          have hD1 := Theorem_D1_heterogeneous_finite_sum_VR_nonconvex
            (K := K₁) A x0 workerBatchLaw Llocal ℒlocal ω fStar hLower hSmooth
              hBatchLaw hAverageSmooth hQuantizer hStep
          refine ⟨hD1.1, ?_⟩
          have heq : (fun z =>
              ‖globalGradient (finiteSumLocalProblem A.problem)
                (uniformOutput (K := K₁)
                  (heterogeneousFiniteSumProcess (b0 := b0) A x0) z)‖ ^ 2) =
              (fun _ => (0 : ℝ)) := by
            funext z
            rw [hGradZero]
            norm_num
          rw [heq, integral_zero]
          positivity
        · refine Or.inl ⟨?_, ?_⟩
          · intro ε
            change Δ / (ε : ℝ) ^ 2 * bracket = 0
            rw [hBracketEq]
            ring
          · unfold AccuracyBigO
            simpa [K₁] using
              (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
                accuracyToZero)
        · intro i
          unfold AccuracyBigO
          have hmne : (m.1 : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt m.2)
          rw [show (fun ε : Accuracy => (m.1 : ℝ) +
              Δ / (ε : ℝ) ^ 2 * bracket *
                (A.refreshProbability * m.1 +
                  (1 - A.refreshProbability) * (b0 i).1)) =
              (fun _ : Accuracy => (m.1 : ℝ)) by
                funext ε
                rw [hBracketEq]
                ring]
          simpa [heterogeneousFiniteSumOracleCallCount, K₁] using
            (Asymptotics.isBigO_const_const
              ((m.1 : ℝ) + (A.refreshProbability * m.1 +
                2 * (1 - A.refreshProbability) * (b0 i).1))
              hmne accuracyToZero)
        · unfold AccuracyBigO
          have hdne : (d.1 : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt d.2)
          rw [show (fun ε : Accuracy => (d.1 : ℝ) +
              Δ / (ε : ℝ) ^ 2 * bracket *
                (A.refreshProbability * d.1 +
                  (1 - A.refreshProbability) * ζ)) =
              (fun _ : Accuracy => (d.1 : ℝ)) by
                funext ε
                rw [hBracketEq]
                ring]
          simpa [allWorkerCommunicationCount, K₁, ζ] using
            (Asymptotics.isBigO_const_const
              ((d.1 : ℝ) + (A.refreshProbability * d.1 +
                (1 - A.refreshProbability) * expectedDensity A.quantizer))
              hdne accuracyToZero)
      · let K : Accuracy → Count := fun ε =>
          ⟨max 1 (Nat.ceil (2 * Δ /
            ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
        have hScalar := positive_inverse_square_ceiling_schedule
          Δ (A.stepSize : ℝ) bracket hGapPos A.stepSize.property hBracketPos
        have hKBound : ∀ ε : Accuracy,
            2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
              (ε : ℝ) ^ 2 := by
          intro ε
          simpa [K] using hScalar.1 ε
        have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
            (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
          simpa [K] using hScalar.2
        have hScaleNonneg :
            ∀ᶠ ε : Accuracy in accuracyToZero,
              0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by
          filter_upwards [] with ε
          positivity
        refine ⟨K, ?_, Or.inr hKBigO, ?_, ?_⟩
        · intro ε
          unfold NonconvexAccuracy
          have hD1 := Theorem_D1_heterogeneous_finite_sum_VR_nonconvex
            (K := K ε) A x0 workerBatchLaw Llocal ℒlocal ω fStar hLower hSmooth
              hBatchLaw hAverageSmooth hQuantizer hStep
          refine ⟨hD1.1, hD1.2.trans ?_⟩
          simpa [Δ] using hKBound ε
        · intro i
          let oraclePayload : ℝ := A.refreshProbability * m.1 +
              2 * (1 - A.refreshProbability) * (b0 i).1
          let targetPayload : ℝ := A.refreshProbability * m.1 +
              (1 - A.refreshProbability) * (b0 i).1
          have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
          have hmpos : 0 < (m.1 : ℝ) := by exact_mod_cast m.2
          have hPMPos : 0 < A.refreshProbability * (m.1 : ℝ) :=
            mul_pos hp hmpos
          have hQBNonneg : 0 ≤
              (1 - A.refreshProbability) * ((b0 i).1 : ℝ) :=
            mul_nonneg hOneSub (by positivity)
          have hOraclePayloadNonneg : 0 ≤ oraclePayload := by
            dsimp [oraclePayload]
            positivity
          have hTargetPayloadPos : 0 < targetPayload := by
            dsimp [targetPayload]
            exact add_pos_of_pos_of_nonneg hPMPos hQBNonneg
          have hPayloadComparison : oraclePayload ≤ 2 * targetPayload := by
            dsimp [oraclePayload, targetPayload]
            nlinarith [hPMPos.le, hQBNonneg]
          have hOracle := accuracyBigO_affine_cost_of_schedule
            (K := fun ε => ((K ε).1 : ℝ))
            (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
            (init := (m.1 : ℝ))
            (actualPayload := oraclePayload)
            (targetPayload := targetPayload)
            (payloadFactor := 2)
            hKBigO hmpos hOraclePayloadNonneg hTargetPayloadPos
              (by norm_num) hPayloadComparison hScaleNonneg
          change AccuracyBigO
            (fun ε => (m.1 : ℝ) + ((K ε).1 : ℝ) * oraclePayload)
            (fun ε => (m.1 : ℝ) +
              (Δ / (ε : ℝ) ^ 2 * bracket) * targetPayload)
          exact hOracle
        · let commPayload : ℝ := A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ
          have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
          have hCommPayloadPos : 0 < commPayload := by
            dsimp [commPayload]
            exact add_pos_of_pos_of_nonneg
              (mul_pos hp hdpos)
              (mul_nonneg (sub_nonneg.mpr hp1) hζ)
          have hComm := accuracyBigO_affine_cost_of_schedule
            (K := fun ε => ((K ε).1 : ℝ))
            (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
            (init := (d.1 : ℝ))
            (actualPayload := commPayload)
            (targetPayload := commPayload)
            (payloadFactor := 1)
            hKBigO hdpos hCommPayloadPos.le hCommPayloadPos
              zero_lt_one (by simp) hScaleNonneg
          change AccuracyBigO
            (fun ε => (d.1 : ℝ) + ((K ε).1 : ℝ) * commPayload)
            (fun ε => (d.1 : ℝ) +
              (Δ / (ε : ℝ) ^ 2 * bracket) * commPayload)
          exact hComm

/-- Deprecated compatibility boundary for the arbitrary joint batch law used
by the former Lean statement of Remark D.1.  The equality premise is the exact
sampling guard that was missing there: it identifies the supplied joint law
with the source's independently sampled worker product.  Without such a guard,
`remark_D1_arbitrary_joint_batchLaw_counterexample` shows that the `1 / n`
variance reduction in Eq. (33) is false even for centered unit-variance worker
innovations.  New code should use `Remark_D1_heterogeneous_finite_batches`,
whose canonical product law makes this sampling semantics definitional. -/
@[deprecated Remark_D1_heterogeneous_finite_batches (since := "2026-10-24")]
theorem Remark_D1_heterogeneous_finite_batches_of_product_guard
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : HeterogeneousFiniteSumBatchLaw n m b0)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hProduct : batchLaw =
      heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      batchLaw (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    let P := finiteSumLocalProblem A.problem
    let law := heterogeneousFiniteSumPathLaw A batchLaw
    let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    (∀ K : Count,
      Integrable (fun z =>
        ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
        (uniformOutputExperimentLaw law K) ∧
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) ≤
          2 * Δ / (A.stepSize * K.1)) ∧
    ∃ K : Accuracy → Count,
      (∀ ε, NonconvexAccuracy (K ε) P run law ε) ∧
      AccuracyIterationBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) ∧
      (∀ i, AccuracyBigO
        (fun ε => heterogeneousFiniteSumOracleCallCount m (K ε) b0
          A.refreshProbability i)
        (fun ε => m.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * m.1 +
            (1 - A.refreshProbability) * (b0 i).1))) ∧
      AccuracyBigO
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  subst batchLaw
  exact Remark_D1_heterogeneous_finite_batches
    A x0 workerBatchLaw Llocal ℒlocal ω fStar hLower hSmooth
      hWorkerBatchLaw hAverageSmooth hQuantizer hStep

/-! ## Heterogeneous online scalar recurrence: direct source-stage attempt -/

/-- Every coordinate of the canonical heterogeneous Algorithm 3 proof-exact
path has the complete heterogeneous round law.  This is the first freshness
identity needed by the direct workerwise proof of the heterogeneous Eq. (46),
not a caller-supplied stochastic regularity premise. -/
theorem heterogeneousOnlineProofExactPathLaw_round_marginal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) :
    Measure.map
        (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => path k)
        (heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A) =
      heterogeneousOnlineRoundLaw A := by
  classical
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  simpa [heterogeneousOnlineProofExactPathLaw] using
    SOptLib.iidStreamLaw_map_eval
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) k

/-- The exact-gradient initialization supplies the two base scalar moment
certificates for the direct heterogeneous Eq. (46) induction. -/
theorem heterogeneousOnlineProofExactProcess_initial_scalar_moments
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := heterogeneousOnlineCorrectedProofExactProcess
      (b := b) (b0 := b0) A hE x0
    let law := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law 0 ∧
      StepMomentWellDefined run law 0 := by
  classical
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  dsimp only
  constructor
  · simpa [EstimatorErrorMomentWellDefined,
      heterogeneousOnlineCorrectedProofExactProcess,
      SOptLib.recursiveIterateProcess] using
      (integrable_const
        (μ := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A)
        (c := (0 : ℝ)))
  · simpa [StepMomentWellDefined,
      heterogeneousOnlineCorrectedProofExactProcess,
      SOptLib.recursiveIterateProcess, heterogeneousOnlineStep, primalStep_eq]
      using
        (integrable_const
          (μ := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A)
          (c := ‖(-(A.stepSize : ℝ)) •
            globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0‖ ^ 2))

/- Prefix extensionality for the canonical heterogeneous proof-exact process.
It is private realization machinery used by the direct Eq. (46) construction. -/
theorem heterogeneousOnlineCorrectedProofExactProcess_congr_prefix
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (k : ℕ)
    {path path' : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ}
    (hpath : ∀ t < k, path t = path' t) :
    heterogeneousOnlineCorrectedProofExactProcess A hE x0 k path =
      heterogeneousOnlineCorrectedProofExactProcess A hE x0 k path' := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show heterogeneousOnlineCorrectedProofExactProcess A hE x0 (k + 1) path =
          heterogeneousOnlineStep A (path k)
            (heterogeneousOnlineCorrectedProofExactProcess A hE x0 k path) by rfl,
        show heterogeneousOnlineCorrectedProofExactProcess A hE x0 (k + 1) path' =
          heterogeneousOnlineStep A (path' k)
            (heterogeneousOnlineCorrectedProofExactProcess A hE x0 k path') by rfl]
      have hprev : ∀ t < k, path t = path' t :=
        fun t ht => hpath t (Nat.lt_trans ht (Nat.lt_succ_self k))
      rw [ih hprev, hpath k (Nat.lt_succ_self k)]

/- The fixed-query refresh calculation for the worker-dependent batch law.
It is kept private because its only source-facing role is the refresh branch
of heterogeneous Eq. (46) below. -/
theorem heterogeneousOnline_fixed_refresh_average_second_moment
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x : Point d) (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let μ := heterogeneousOnlineBatchLaw A.problem b
    Integrable (fun batch =>
        ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient P x‖ ^ 2) μ ∧
      (∫ batch,
        ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient P x‖ ^ 2 ∂μ) ≤
        heterogeneousOnlineVarianceTerm σ b := by
  classical
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let μ := heterogeneousOnlineBatchLaw A.problem b
  let rowLaw (i : Worker n) : Measure (Fin (b i).1 → Sample i) :=
    Measure.infinitePi (fun _ : Fin (b i).1 => A.problem.sampleLaw i)
  let target (i : Worker n) : Point d := localGradient P i x
  let residual (i : Worker n) (xi : Sample i) : Point d :=
    stochasticGradient A.problem i xi x - target i
  let rowResidual (i : Worker n) (row : Fin (b i).1 → Sample i) : Point d :=
    average (fun j : Fin (b i).1 => residual i (row j))
  let workerResidual (i : Worker n)
      (batch : HeterogeneousOnlineBatch n Sample b) : Point d :=
    rowResidual i (batch i)
  dsimp only
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  letI (i : Worker n) : IsProbabilityMeasure (rowLaw i) := by
    dsimp [rowLaw]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, heterogeneousOnlineBatchLaw]
    infer_instance
  have hcoord (i : Worker n) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i) μ =
        rowLaw i := by
    simpa [μ, rowLaw] using
      heterogeneous_online_batch_law_worker_marginal A.problem b i
  have hsample (i : Worker n) (j : Fin (b i).1) :
      Measure.map (fun row : Fin (b i).1 → Sample i => row j) (rowLaw i) =
        A.problem.sampleLaw i := by
    dsimp [rowLaw]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin (b i).1 => A.problem.sampleLaw i) j)
  have hresidual_int (i : Worker n) :
      Integrable (residual i) (A.problem.sampleLaw i) := by
    rcases hVariance.1.2 i x with ⟨hgrad, _hres2, _hmean, _hsecond⟩
    exact hgrad.sub (integrable_const (c := target i))
  have hresidual_mean (i : Worker n) :
      (∫ xi, residual i xi ∂A.problem.sampleLaw i) = 0 := by
    rcases hVariance.1.2 i x with ⟨hgrad, _hres2, hmean, _hsecond⟩
    dsimp [residual, target, P]
    rw [integral_sub hgrad (integrable_const
      (c := localGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i x))]
    have hmean' :
        (∫ ξ, stochasticGradient A.problem i ξ x ∂A.problem.sampleLaw i) =
          localGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i x := by
      simpa [onlineLocalProblemCorrected_eq_onlineLocalProblem] using hmean
    rw [hmean']
    simp
  have hrow_term_int (i : Worker n) (j : Fin (b i).1) :
      Integrable (fun row : Fin (b i).1 → Sample i => residual i (row j))
        (rowLaw i) := by
    have hm : Integrable (residual i)
        (Measure.map (fun row : Fin (b i).1 → Sample i => row j) (rowLaw i)) := by
      rw [hsample i j]
      exact hresidual_int i
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).mp hm
  have hrow_term_mean (i : Worker n) (j : Fin (b i).1) :
      (∫ row : Fin (b i).1 → Sample i, residual i (row j) ∂rowLaw i) = 0 := by
    have hm : AEStronglyMeasurable (residual i)
        (Measure.map (fun row : Fin (b i).1 → Sample i => row j) (rowLaw i)) := by
      rw [hsample i j]
      exact (hresidual_int i).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := rowLaw i) (φ := fun row : Fin (b i).1 → Sample i => row j)
      (measurable_pi_apply j).aemeasurable hm
    rw [hsample i j, hresidual_mean i] at hmap
    exact hmap.symm
  have hrow_int (i : Worker n) : Integrable (rowResidual i) (rowLaw i) := by
    dsimp [rowResidual, average, SOptLib.finiteUniformAverage]
    have hsum := MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _ => hrow_term_int i j)
    simpa [Pi.smul_apply] using hsum.smul (((b i).1 : ℝ)⁻¹)
  have hrow_mean (i : Worker n) :
      (∫ row, rowResidual i row ∂rowLaw i) = 0 := by
    dsimp [rowResidual, average, SOptLib.finiteUniformAverage]
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _ => hrow_term_int i j)]
    simp [hrow_term_mean]
  have hcenter (i : Worker n) (row : Fin (b i).1 → Sample i) :
      average (fun j : Fin (b i).1 =>
          stochasticGradient A.problem i (row j) x) - target i =
        rowResidual i row := by
    dsimp [rowResidual, residual]
    unfold average
    simpa [SOptLib.finiteUniformAverage] using
      (miniBatchAverage_sub_target_eq_average_residual
        (Finset.univ : Finset (Fin (b i).1)) (b i).1 (by simp) (b i).2
        (fun j => stochasticGradient A.problem i (row j) x) (target i))
  have hdiag (i : Worker n) :
      Integrable (fun batch => ‖workerResidual i batch‖ ^ 2) μ ∧
        (∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) ≤
          (σ i) ^ 2 / (b i).1 := by
    have h := heterogeneousOnline_refresh_secondMoment_le
      A.problem σ b hVariance i x
    have hsquare (batch : HeterogeneousOnlineBatch n Sample b) :
        ‖workerResidual i batch‖ ^ 2 =
          ‖average (fun j : Fin (b i).1 =>
              stochasticGradient A.problem i (batch i j) x) -
            localGradient (onlineLocalProblem A.problem) i x‖ ^ 2 := by
      change ‖rowResidual i (batch i)‖ ^ 2 = _
      rw [← hcenter i (batch i)]
      simp [target, P, onlineLocalProblemCorrected_eq_onlineLocalProblem]
    constructor
    · apply h.1.congr
      exact Filter.Eventually.of_forall (fun batch => (hsquare batch).symm)
    · calc
        (∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) =
            ∫ batch,
              ‖average (fun j : Fin (b i).1 =>
                  stochasticGradient A.problem i (batch i j) x) -
                localGradient (onlineLocalProblem A.problem) i x‖ ^ 2 ∂μ := by
              exact integral_congr_ae (Filter.Eventually.of_forall hsquare)
        _ ≤ (σ i) ^ 2 / (b i).1 := by simpa [μ] using h.2
  have hworker_int (i : Worker n) : Integrable (workerResidual i) μ := by
    have hm : Integrable (rowResidual i)
        (Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i) μ) := by
      rw [hcoord i]
      exact hrow_int i
    have hpull := (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).mp hm
    exact integrable_of_integrable_norm_sq hpull.aestronglyMeasurable (hdiag i).1
  have hiIndep : ProbabilityTheory.iIndepFun
      (fun i (batch : HeterogeneousOnlineBatch n Sample b) => batch i) μ := by
    dsimp [μ, heterogeneousOnlineBatchLaw]
    exact ProbabilityTheory.iIndepFun_infinitePi (fun _ : Worker n => measurable_id)
  have hcross (i j : Worker n) (hij : i ≠ j) :
      (∫ batch, ⟪workerResidual i batch, workerResidual j batch⟫_ℝ ∂μ) = 0 := by
    have hkernel : AEStronglyMeasurable
        (fun p : (Fin (b i).1 → Sample i) × (Fin (b j).1 → Sample j) =>
          inner ℝ (rowResidual i p.1) (rowResidual j p.2))
        ((Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i) μ).prod
          (rowLaw j)) := by
      rw [hcoord i]
      exact (hrow_int i).aestronglyMeasurable.comp_fst.inner
        (hrow_int j).aestronglyMeasurable.comp_snd
    have hinner : Integrable
        (fun batch => ⟪workerResidual i batch, workerResidual j batch⟫_ℝ) μ :=
      integrable_inner_of_integrable_sq_norm
        (hworker_int i).aestronglyMeasurable (hworker_int j).aestronglyMeasurable
        (hdiag i).1 (hdiag j).1
    have hfixed : ∀ a : Fin (b i).1 → Sample i,
        (∫ z, inner ℝ (rowResidual i a) (rowResidual j z) ∂rowLaw j) = 0 := by
      intro a
      have hlin := ContinuousLinearMap.integral_comp_comm
        (L := (innerSL ℝ) (rowResidual i a)) (hrow_int j)
      exact hlin.trans (by rw [hrow_mean j]; simp)
    exact integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := μ) (ν := rowLaw j)
      (φ := fun a z => inner ℝ (rowResidual i a) (rowResidual j z))
      (X := fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
      (Y := fun batch : HeterogeneousOnlineBatch n Sample b => batch j)
      hkernel (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable (hiIndep.indepFun hij)
      (hcoord j) hinner hfixed
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    μ (Finset.univ : Finset (Worker n)) workerResidual
    (fun i _ => (hworker_int i).aestronglyMeasurable)
    (fun i _ => (hdiag i).1)
    (fun i _ j _ hij => hcross i j hij)
  have havg_int : Integrable
      (fun batch => ‖average (fun i : Worker n => workerResidual i batch)‖ ^ 2) μ := by
    apply integrable_sq_norm_centeredMiniBatchAverage μ
      (Finset.univ : Finset (Worker n)) n.1 workerResidual
      (fun batch => average (fun i : Worker n => workerResidual i batch))
    · intro i _
      exact (hworker_int i).aestronglyMeasurable
    · intro i _
      exact (hdiag i).1
    · funext batch
      simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
  have hglobal := globalGradient_eq_averageLocalGradient P hSmooth.1 x
  have hpointwise (batch : HeterogeneousOnlineBatch n Sample b) :
      ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
          stochasticGradient A.problem i (batch i j) x)) - globalGradient P x‖ ^ 2 =
        ‖average (fun i : Worker n => workerResidual i batch)‖ ^ 2 := by
    apply congrArg (fun v : Point d => ‖v‖ ^ 2)
    rw [hglobal]
    unfold averageLocalGradient
    dsimp [workerResidual, target]
    unfold average SOptLib.finiteUniformAverage
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    simpa [average, SOptLib.finiteUniformAverage] using hcenter i (batch i)
  constructor
  · apply havg_int.congr
    exact Filter.Eventually.of_forall (fun batch => (hpointwise batch).symm)
  · calc
      (∫ batch,
        ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient P x‖ ^ 2 ∂μ) =
          ∫ batch, ‖average (fun i : Worker n => workerResidual i batch)‖ ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpointwise)
      _ = ((n.1 : ℝ)⁻¹) ^ 2 *
          ∫ batch, ‖Finset.sum Finset.univ
            (fun i : Worker n => workerResidual i batch)‖ ^ 2 ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with batch
        unfold average SOptLib.finiteUniformAverage
        simp only [Fintype.card_fin]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring
      _ = ((n.1 : ℝ)⁻¹) ^ 2 *
          ∑ i : Worker n, ∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ := by
        rw [hsum]
      _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
          ∑ i : Worker n, (σ i) ^ 2 / (b i).1 := by
        gcongr with i
        exact (hdiag i).2
      _ = heterogeneousOnlineVarianceTerm σ b := by
        unfold heterogeneousOnlineVarianceTerm average SOptLib.finiteUniformAverage
        have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
        simp only [Fintype.card_fin, smul_eq_mul]
        field_simp

/- Fixed-query nonrefresh aggregation for Remark D.2.  This is private
realization machinery: the worker-dependent batch law is the paper's
canonical product law, and all moment premises are discharged from Assumption
3.2 before the result is consumed by the adaptive Eq. (46) induction below. -/
theorem heterogeneousOnline_fixed_nonrefresh_average_second_moment
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (xNext x : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hAverageFiber : ∀ i : Worker n,
      let delta := localGradientDifference
        (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
      let D := fun batch =>
        heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x
      Integrable D (heterogeneousOnlineBatchLaw A.problem b0) ∧
        Integrable (fun batch => ‖D batch - delta‖ ^ 2)
          (heterogeneousOnlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂heterogeneousOnlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂heterogeneousOnlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let law := (heterogeneousOnlineBatchLaw A.problem b0).prod
      (workerCompressionLaw (n := n) A.quantizer)
    let innovation := fun i : Worker n =>
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 q.1 i xNext x)
            (q.2 i) -
          localGradientDifference (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
            i xNext x
    Integrable (fun q => average (fun i : Worker n => innovation i q)) law ∧
      (∫ q, average (fun i : Worker n => innovation i q) ∂law) = 0 ∧
      Integrable (fun q => ‖average (fun i : Worker n => innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n => innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let law := batchLaw.prod compressionLaw
  let source := fun i : Worker n =>
    fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
      (q.1 i, q.2 i)
  let rowLaw := fun i : Worker n =>
    (Measure.infinitePi (fun _ : Fin (b0 i).1 => A.problem.sampleLaw i)).prod
      A.quantizer.law
  let localInnovation := fun i : Worker n =>
    fun q : (Fin (b0 i).1 → Sample i) × Ξ =>
      A.quantizer.apply
          (average (fun j : Fin (b0 i).1 =>
            stochasticGradient A.problem i (q.1 j) xNext -
              stochasticGradient A.problem i (q.1 j) x)) q.2 -
        localGradientDifference
          (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
  let innovation := fun i : Worker n =>
    fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
      localInnovation i (source i q)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hsource : ∀ i : Worker n, Measurable (source i) := by
    intro i
    dsimp [source]
    fun_prop
  have hmap : ∀ i : Worker n, Measure.map (source i) law = rowLaw i := by
    intro i
    dsimp [source, law, rowLaw, batchLaw, compressionLaw]
    calc
      Measure.map
          (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
            (q.1 i, q.2 i))
          ((heterogeneousOnlineBatchLaw A.problem b0).prod
            (workerCompressionLaw A.quantizer)) =
          (Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b0 => batch i)
            (heterogeneousOnlineBatchLaw A.problem b0)).prod
            (Measure.map (fun q : Worker n → Ξ => q i)
              (workerCompressionLaw A.quantizer)) := by
                symm
                simpa [Prod.map] using
                  (MeasureTheory.Measure.map_prod_map
                    (heterogeneousOnlineBatchLaw A.problem b0)
                    (workerCompressionLaw (n := n) A.quantizer)
                    (measurable_pi_apply i) (measurable_pi_apply i))
      _ = _ := by
        rw [heterogeneous_online_batch_law_worker_marginal A.problem b0 i,
          workerCompressionLaw_component_marginal A.quantizer i]
  have hLocalFiber : ∀ i : Worker n,
      Integrable (localInnovation i) (rowLaw i) ∧
      Integrable (fun q => ‖localInnovation i q‖ ^ 2) (rowLaw i) ∧
      (∫ q, localInnovation i q ∂rowLaw i) = 0 ∧
      (∫ q, ‖localInnovation i q‖ ^ 2 ∂rowLaw i) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
    intro i
    let scalarBatchLaw := onlineBatchLaw A.problem (b0 i)
    let heteroRow := fun batch : HeterogeneousOnlineBatch n Sample b0 => batch i
    let scalarRow := fun batch : (w : Worker n) → Fin (b0 i).1 → Sample w => batch i
    let localD := fun row : Fin (b0 i).1 → Sample i =>
      average (fun j : Fin (b0 i).1 =>
        stochasticGradient A.problem i (row j) xNext -
          stochasticGradient A.problem i (row j) x)
    let delta := localGradientDifference
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
    let rows := Measure.infinitePi
      (fun _ : Fin (b0 i).1 => A.problem.sampleLaw i)
    haveI : IsProbabilityMeasure scalarBatchLaw := by
      unfold scalarBatchLaw onlineBatchLaw
      infer_instance
    have hHetMap : Measure.map heteroRow batchLaw = rows := by
      simpa [heteroRow, batchLaw, rows] using
        heterogeneous_online_batch_law_worker_marginal A.problem b0 i
    have hScalarMap : Measure.map scalarRow scalarBatchLaw = rows := by
      simpa [scalarRow, scalarBatchLaw, rows] using
        onlineBatchLaw_worker_marginal A.problem i
    have hgrad (j : Fin (b0 i).1) (z : Point d) : AEStronglyMeasurable
        (fun row : Fin (b0 i).1 → Sample i =>
          stochasticGradient A.problem i (row j) z) rows := by
      have hcoord : Measure.map
          (fun row : Fin (b0 i).1 → Sample i => row j) rows =
          A.problem.sampleLaw i := by
        dsimp [rows]
        simpa using
          (MeasureTheory.Measure.infinitePi_map_eval
            (μ := fun _ : Fin (b0 i).1 => A.problem.sampleLaw i) j)
      have honMap : AEStronglyMeasurable
          (fun xi => stochasticGradient A.problem i xi z)
          (Measure.map (fun row : Fin (b0 i).1 → Sample i => row j) rows) := by
        rw [hcoord]
        exact (hVariance.1.2 i z).1.aestronglyMeasurable
      exact honMap.comp_aemeasurable (measurable_pi_apply j).aemeasurable
    have hlocalD : AEStronglyMeasurable localD rows := by
      unfold localD average SOptLib.finiteUniformAverage
      have hs := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => (hgrad j xNext).sub (hgrad j x))).const_smul
          ((Fintype.card (Fin (b0 i).1) : ℝ)⁻¹)
      refine hs.congr (Filter.Eventually.of_forall ?_)
      intro row
      simp [Finset.sum_apply]
    have hlocalResidual : AEStronglyMeasurable
        (fun row => ‖localD row - delta‖ ^ 2) rows := by
      have hconst : AEStronglyMeasurable
          (fun _ : Fin (b0 i).1 → Sample i => delta) rows :=
        aestronglyMeasurable_const
      have hv := hlocalD.sub hconst
      simpa [pow_two] using hv.norm.mul hv.norm
    have hFiber := hAverageFiber i
    have hDrow : Integrable localD rows := by
      rw [← hHetMap]
      apply (MeasureTheory.integrable_map_measure (by
        rw [hHetMap]
        exact hlocalD) (measurable_pi_apply i).aemeasurable).mpr
      simpa [localD, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw] using hFiber.1
    have hResidualRow : Integrable (fun row => ‖localD row - delta‖ ^ 2) rows := by
      rw [← hHetMap]
      apply (MeasureTheory.integrable_map_measure (by
        rw [hHetMap]
        exact hlocalResidual) (measurable_pi_apply i).aemeasurable).mpr
      simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw] using hFiber.2.1
    have hMeanRow : (∫ row, localD row ∂rows) = delta := by
      rw [← hHetMap, MeasureTheory.integral_map
        (measurable_pi_apply i).aemeasurable
        (by rw [hHetMap]; exact hlocalD)]
      simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw] using hFiber.2.2.1
    have hSecondRow : (∫ row, ‖localD row - delta‖ ^ 2 ∂rows) ≤
        (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
      rw [← hHetMap, MeasureTheory.integral_map
        (measurable_pi_apply i).aemeasurable
        (by rw [hHetMap]; exact hlocalResidual)]
      simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw] using hFiber.2.2.2
    have hHomogeneousFiber :
        let delta' := localGradientDifference
          (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x
        let D := fun batch => onlineBatchDifference A.problem batch i xNext x
        Integrable D scalarBatchLaw ∧
          Integrable (fun batch => ‖D batch - delta'‖ ^ 2) scalarBatchLaw ∧
          (∫ batch, D batch ∂scalarBatchLaw) = delta' ∧
          (∫ batch, ‖D batch - delta'‖ ^ 2 ∂scalarBatchLaw) ≤
            (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
      dsimp only
      have hD : Integrable (localD ∘ scalarRow) scalarBatchLaw :=
        (MeasureTheory.integrable_map_measure (by
          rw [hScalarMap]
          exact hlocalD) (measurable_pi_apply i).aemeasurable).mp
          (by rw [hScalarMap]; exact hDrow)
      have hR : Integrable ((fun row => ‖localD row - delta‖ ^ 2) ∘ scalarRow)
          scalarBatchLaw :=
        (MeasureTheory.integrable_map_measure (by
          rw [hScalarMap]
          exact hlocalResidual) (measurable_pi_apply i).aemeasurable).mp
          (by rw [hScalarMap]; exact hResidualRow)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [localD, scalarRow, onlineBatchDifference, scalarBatchLaw] using hD
      · simpa [localD, delta, scalarRow, onlineBatchDifference, scalarBatchLaw]
          using hR
      · calc
          (∫ batch, onlineBatchDifference A.problem batch i xNext x
              ∂scalarBatchLaw) =
              ∫ batch, localD (scalarRow batch) ∂scalarBatchLaw := by rfl
          _ = ∫ row, localD row ∂Measure.map scalarRow scalarBatchLaw := by
            rw [MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
              (by rw [hScalarMap]; exact hlocalD)]
          _ = ∫ row, localD row ∂rows := by rw [hScalarMap]
          _ = delta := hMeanRow
      · calc
          (∫ batch,
              ‖onlineBatchDifference A.problem batch i xNext x -
                localGradientDifference
                  (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i xNext x‖ ^ 2
              ∂scalarBatchLaw) =
              ∫ batch, ‖localD (scalarRow batch) - delta‖ ^ 2
                ∂scalarBatchLaw := by rfl
          _ = ∫ row, ‖localD row - delta‖ ^ 2
                ∂Measure.map scalarRow scalarBatchLaw := by
            rw [MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
              (by rw [hScalarMap]; exact hlocalResidual)]
          _ = ∫ row, ‖localD row - delta‖ ^ 2 ∂rows := by rw [hScalarMap]
          _ ≤ _ := hSecondRow
    simpa [localInnovation, rowLaw, rows] using
      (online_corrected_fixed_nonrefresh_worker_local_moment
        (b0 := b0 i) A hE xNext x i Llocal ℒlocal σ ω hSmooth hVariance
          hHomogeneousFiber hQuantizer)
  have hWhole : Measure.map
      (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
        fun i => source i q) law = Measure.infinitePi rowLaw := by
    let α := fun i : Worker n => Fin (b0 i).1 → Sample i
    let β := fun _ : Worker n => Ξ
    let μ := fun i : Worker n =>
      Measure.infinitePi (fun _ : Fin (b0 i).1 => A.problem.sampleLaw i)
    let ν := fun _ : Worker n => A.quantizer.law
    have hmp := measurePreserving_dependentArrowProdMeasurableEquiv α β μ ν
    have hinv := MeasurePreserving.symm
      (dependentArrowProdMeasurableEquiv α β) hmp
    simpa [law, batchLaw, compressionLaw, heterogeneousOnlineBatchLaw,
      workerCompressionLaw, source, rowLaw, α, β, μ, ν,
      MeasureTheory.Measure.infinitePi_eq_pi] using hinv.map_eq
  have hindep : ProbabilityTheory.iIndepFun source law := by
    apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i => hsource i)).2
    rw [hWhole]
    congr 1
    funext i
    exact (hmap i).symm
  have hdiag : ∀ i : Worker n,
      Integrable (fun q => ‖innovation i q‖ ^ 2) law ∧
      (∫ q, ‖innovation i q‖ ^ 2 ∂law) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
    intro i
    have hsq : AEStronglyMeasurable (fun q => ‖localInnovation i q‖ ^ 2)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hLocalFiber i).2.1.aestronglyMeasurable
    constructor
    · exact (MeasureTheory.integrable_map_measure hsq (hsource i).aemeasurable).mp
        (by simpa [hmap i] using (hLocalFiber i).2.1)
    · rw [show (∫ q, ‖innovation i q‖ ^ 2 ∂law) =
          ∫ q, ‖localInnovation i q‖ ^ 2 ∂Measure.map (source i) law by
            rw [MeasureTheory.integral_map (hsource i).aemeasurable hsq],
        hmap i]
      exact (hLocalFiber i).2.2.2
  have hvec : ∀ i : Worker n,
      Integrable (innovation i) law ∧ (∫ q, innovation i q ∂law) = 0 := by
    intro i
    have hm : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hLocalFiber i).1.aestronglyMeasurable
    constructor
    · exact (MeasureTheory.integrable_map_measure hm (hsource i).aemeasurable).mp
        (by simpa [hmap i] using (hLocalFiber i).1)
    · rw [show (∫ q, innovation i q ∂law) =
          ∫ q, localInnovation i q ∂Measure.map (source i) law by
            rw [MeasureTheory.integral_map (hsource i).aemeasurable hm],
        hmap i]
      exact (hLocalFiber i).2.2.1
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) = 0 := by
    intro i j hij
    let fi := localInnovation i
    let fj := localInnovation j
    let fiMk := (hLocalFiber i).1.aestronglyMeasurable.mk fi
    let fjMk := (hLocalFiber j).1.aestronglyMeasurable.mk fj
    have hfiMk : Measurable fiMk :=
      (hLocalFiber i).1.aestronglyMeasurable.measurable_mk
    have hfjMk : Measurable fjMk :=
      (hLocalFiber j).1.aestronglyMeasurable.measurable_mk
    have hfi_ae : fi =ᵐ[rowLaw i] fiMk :=
      (hLocalFiber i).1.aestronglyMeasurable.ae_eq_mk
    have hfj_ae : fj =ᵐ[rowLaw j] fjMk :=
      (hLocalFiber j).1.aestronglyMeasurable.ae_eq_mk
    have hqmpi : Measure.QuasiMeasurePreserving (source i) law (rowLaw i) :=
      ⟨hsource i, by rw [hmap i]⟩
    have hqmpj : Measure.QuasiMeasurePreserving (source j) law (rowLaw j) :=
      ⟨hsource j, by rw [hmap j]⟩
    have hfi_global : innovation i =ᵐ[law] fiMk ∘ source i := by
      exact hqmpi.tendsto_ae hfi_ae
    have hfj_global : innovation j =ᵐ[law] fjMk ∘ source j := by
      exact hqmpj.tendsto_ae hfj_ae
    have hfixed_int : ∀ _ : (Fin (b0 j).1 → Sample j) × Ξ,
        Integrable (fun s => fiMk s) (rowLaw i) := by
      intro _
      exact (hLocalFiber i).1.congr hfi_ae
    have hfixed_zero : ∀ _ : (Fin (b0 j).1 → Sample j) × Ξ,
        (∫ s, fiMk s ∂rowLaw i) = 0 := by
      intro _
      rw [← integral_congr_ae hfi_ae]
      exact (hLocalFiber i).2.2.1
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
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (innovation i) law :=
    fun i => (hvec i).1.aestronglyMeasurable
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    law (Finset.univ : Finset (Worker n)) innovation
      (fun i _ => hmeas i) (fun i _ => (hdiag i).1)
      (fun i _ j _ hij => hcross hij)
  have havgSq : Integrable
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
  have havg : Integrable
      (fun q => average (fun i : Worker n => innovation i q)) law := by
    unfold average SOptLib.finiteUniformAverage
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ => (hvec i).1)).smul ((n.1 : ℝ)⁻¹)
  have havgZero : (∫ q, average (fun i : Worker n => innovation i q) ∂law) = 0 := by
    unfold average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun i _ => (hvec i).1)]
    simp [hvec]
  refine ⟨by simpa [innovation, law] using havg,
    by simpa [innovation, law] using havgZero,
    by simpa [innovation, law] using havgSq, ?_⟩
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
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
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 * ∑ i : Worker n,
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
      have hmean_nonneg : 0 ≤ meanSquare Llocal := by
        unfold meanSquare average SOptLib.finiteUniformAverage
        positivity
      have hrms : (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
        unfold rootMeanSquare
        exact Real.sq_sqrt hmean_nonneg
      rw [hrms, ← Finset.sum_mul]
      unfold meanSquare heterogeneousFiniteBatchSmoothnessTerm average
        SOptLib.finiteUniformAverage
      simp only [smul_eq_mul, Fintype.card_fin]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ i : Worker n,
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) =
          (1 + ω) * ∑ i : Worker n, (ℒlocal i) ^ 2 / (b0 i).1 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
      field_simp [hn]

/- The simultaneous invariant used internally by heterogeneous Eq. (46).
Unlike the retired guarded probe, this declaration is a dependency of the
source recurrence and records the recurrence history needed by its projection.
The only remaining proof leaf is the generated successor calculation itself. -/
theorem heterogeneousOnlineProofExactProcess_scalar_recurrence_components
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : HeterogeneousOnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩
      (heterogeneousOnlineCorrectedProofExactProcess
        (b := b) (b0 := b0) A hE x0) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := heterogeneousOnlineCorrectedProofExactProcess
      (b := b) (b0 := b0) A hE x0
    let law := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A
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
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := heterogeneousOnlineCorrectedProofExactProcess
    (b := b) (b0 := b0) A hE x0
  let law := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
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
                (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
    intro t
    induction t with
    | zero =>
        have hx : AEStronglyMeasurable (fun path => (run 0 path).x) law := by
          simpa [run, heterogeneousOnlineCorrectedProofExactProcess,
            SOptLib.recursiveIterateProcess] using
            (aestronglyMeasurable_const : AEStronglyMeasurable
              (fun _ : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => x0) law)
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
          exact integrable_const _
        have hgl2 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) law := by
          have heq : (fun path => ‖(run 0 path).g‖ ^ 2) =
              (fun _ => ‖globalGradient P x0‖ ^ 2) := by
            funext path
            rfl
          rw [heq]
          exact integrable_const _
        have hBase := heterogeneousOnlineProofExactProcess_initial_scalar_moments
          (b := b) (b0 := b0) A hE x0
        refine ⟨hx, hr, hxl2, hgl2, ?_, ?_, ?_⟩
        · simpa [P, run, law] using hBase.1
        · simpa [P, run, law] using hBase.2
        · intro j hj
          exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        let residualNext := fun path :
            ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
          (run (t + 1) path).g - globalGradient P (run (t + 1) path).x
        have hgrad : AEStronglyMeasurable
            (fun path => globalGradient P (run t path).x) law :=
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            ih.1.aemeasurable).aestronglyMeasurable
        have hg : AEStronglyMeasurable (fun path => (run t path).g) law := by
          have hsum := ih.2.1.add hgrad
          refine hsum.congr (Filter.Eventually.of_forall ?_)
          intro path
          simp
        have hxNext : AEStronglyMeasurable
            (fun path => (run (t + 1) path).x) law := by
          have hstep := ih.1.sub (hg.const_smul (A.stepSize : ℝ))
          simpa [run, heterogeneousOnlineCorrectedProofExactProcess,
            SOptLib.recursiveIterateProcess, heterogeneousOnlineStep,
            primalStep_eq] using hstep
        have hxL2Succ : Integrable
            (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
          have h := integrable_sq_norm_sub_smul_sub_const_of_l2
            (fun path => (run t path).x) (fun path => (run t path).g)
            x0 (A.stepSize : ℝ) ih.1 hg ih.2.2.1 ih.2.2.2.1
          simpa [run, heterogeneousOnlineCorrectedProofExactProcess,
            SOptLib.recursiveIterateProcess, heterogeneousOnlineStep,
            primalStep_eq] using h
        have hglobalSucc : Integrable
            (fun path => ‖globalGradient P (run (t + 1) path).x‖ ^ 2) law := by
          have hGlobal := GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
          apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
            x0 (globalGradient P) (rootMeanSquare Llocal)
              (fun path => (run (t + 1) path).x) hxNext
          · simpa [norm_sub_rev] using hxL2Succ
          · intro x y
            exact hGlobal.2 y x
        /- The only stochastic successor obligation left after deterministic
        component closure.  A direct proof must split the current iid round,
        establish the heterogeneous refresh and nonrefresh moments (including
        peer-worker covariance cancellation), and recombine the Boolean gate.
        The recurrence component is deliberately at this exact source-formula
        granularity; no full-State regularity or caller premise is introduced. -/
        have hStochastic :
            AEStronglyMeasurable residualNext law ∧
            EstimatorErrorMomentWellDefined P run law (t + 1) ∧
            estimatorErrorMoment P run law (t + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
                  stepMoment run law t +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law t +
                A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
          have hRefreshFixed (z : Point d) :
              Integrable (fun batch =>
                  ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                      stochasticGradient A.problem i (batch i j) z)) -
                    globalGradient P z‖ ^ 2)
                (heterogeneousOnlineBatchLaw A.problem b) ∧
              (∫ batch,
                  ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                      stochasticGradient A.problem i (batch i j) z)) -
                    globalGradient P z‖ ^ 2
                ∂heterogeneousOnlineBatchLaw A.problem b) ≤
                  heterogeneousOnlineVarianceTerm σ b := by
            simpa [P] using
              (heterogeneousOnline_fixed_refresh_average_second_moment
                A hE z Llocal σ hSmooth hVariance)
          /- `hRefreshFixed` closes the complete fixed-query worker covariance
          calculation.  What remains is its strict-prefix/current-round
          transport together with the analogous compressed-difference branch
          and Boolean recombination. -/
          have hAdaptiveBranchTransport
              (hRefreshFiber : ∀ z : Point d,
                Integrable (fun batch =>
                    ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                        stochasticGradient A.problem i (batch i j) z)) -
                      globalGradient P z‖ ^ 2)
                  (heterogeneousOnlineBatchLaw A.problem b) ∧
                (∫ batch,
                    ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                        stochasticGradient A.problem i (batch i j) z)) -
                      globalGradient P z‖ ^ 2
                  ∂heterogeneousOnlineBatchLaw A.problem b) ≤
                    heterogeneousOnlineVarianceTerm σ b) :
              AEStronglyMeasurable residualNext law ∧
              EstimatorErrorMomentWellDefined P run law (t + 1) ∧
              estimatorErrorMoment P run law (t + 1) ≤
                (1 - A.refreshProbability) / n.1 *
                    (ω * (rootMeanSquare Llocal) ^ 2 +
                      (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
                    stepMoment run law t +
                  (1 - A.refreshProbability) * estimatorErrorMoment P run law t +
                  A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
            let prefixMap := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              fun j : Fin t => path j.1
            let prefixLaw := Measure.map prefixMap law
            let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
            let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
              Classical.choice (nonempty_of_isProbabilityMeasure law)
            let extend := fun pref : Fin t →
                HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              fun j => if hj : j < t then pref ⟨j, hj⟩ else fallback j
            let prefixState := fun pref : Fin t →
                HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              run t (extend pref)
            let queryPrefix := fun pref : Fin t →
                HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              primalStep A.stepSize (prefixState pref)
            let query := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              (run (t + 1) path).x
            let refreshBatch := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              (path t).2.1.1
            let batchLaw := heterogeneousOnlineBatchLaw A.problem b
            let refreshError := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                stochasticGradient A.problem i (refreshBatch path i j)
                  (query path))) - globalGradient P (query path)
            have hprefix : Measurable prefixMap := by
              dsimp [prefixMap]
              exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
            haveI : IsProbabilityMeasure prefixLaw :=
              Measure.isProbabilityMeasure_map hprefix.aemeasurable
            have hstatePrefix (path) : prefixState (prefixMap path) = run t path := by
              dsimp [prefixState, prefixMap]
              apply heterogeneousOnlineCorrectedProofExactProcess_congr_prefix
                A hE x0 t
              intro j hj
              simp [extend, hj]
            have hqueryEq (path) : queryPrefix (prefixMap path) = query path := by
              dsimp [queryPrefix, query]
              rw [hstatePrefix path]
              rfl
            have hqueryPrefix : AEStronglyMeasurable queryPrefix prefixLaw := by
              have hcomp : AEStronglyMeasurable
                  (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                    queryPrefix (prefixMap path)) law := by
                refine hxNext.congr (Filter.Eventually.of_forall ?_)
                intro path
                exact (hqueryEq path).symm
              have hfinite := aestronglyMeasurable_prefix_of_comp_general
                roundLaw t queryPrefix (by
                  simpa [law, roundLaw, heterogeneousOnlineProofExactPathLaw]
                    using hcomp)
              have hprefixLaw : prefixLaw =
                  Measure.infinitePi (fun _ : Fin t => roundLaw) := by
                simpa [prefixLaw, prefixMap, law, roundLaw,
                  heterogeneousOnlineProofExactPathLaw] using
                    iidStream_prefix_map_eq_infinitePi roundLaw t
              rw [hprefixLaw]
              exact hfinite
            let current := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => path t
            have hcurrent : Measurable current := measurable_pi_apply t
            have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
              apply indepFun_of_map_prod_eq_prod_laws
                (P := law) (Z := fun path => (prefixMap path, current path))
                (mu := prefixLaw) (nu := roundLaw)
              · exact (hprefix.prodMk hcurrent).aemeasurable
              · simpa [prefixMap, current, prefixLaw, roundLaw, law,
                  heterogeneousOnlineProofExactPathLaw] using
                    (infinitePi_prefix_current_map_eq_prod
                      (fun _ : ℕ =>
                        heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) t)
            have hrefreshBatchMeas : Measurable refreshBatch := by
              dsimp [refreshBatch]
              fun_prop
            have hpastRefresh : ProbabilityTheory.IndepFun
                prefixMap refreshBatch law := by
              have hselector : Measurable
                  (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                    z.2.1.1) := by fun_prop
              simpa [refreshBatch, current, Function.comp_def] using
                hpastCurrent.comp measurable_id hselector
            let queryMk := hqueryPrefix.mk queryPrefix
            have hqueryMk : Measurable queryMk := hqueryPrefix.measurable_mk
            have hqueryMkAE :
                (fun path => queryMk (prefixMap path)) =ᵐ[law]
                  (fun path => queryPrefix (prefixMap path)) := by
              have hqmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
                ⟨hprefix, by rfl⟩
              exact hqmp.tendsto_ae hqueryPrefix.ae_eq_mk.symm
            have hqueryRefreshMk : ProbabilityTheory.IndepFun
                (fun path => queryMk (prefixMap path)) refreshBatch law := by
              simpa [Function.comp_def] using
                hpastRefresh.comp hqueryMk measurable_id
            have hqueryRefresh : ProbabilityTheory.IndepFun query refreshBatch law := by
              apply hqueryRefreshMk.congr
              · filter_upwards [hqueryMkAE] with path hp
                rw [hp, hqueryEq path]
              · exact Filter.Eventually.of_forall fun _ => rfl
            have hrefreshBatchLaw : Measure.map refreshBatch law = batchLaw := by
              calc
                Measure.map refreshBatch law = Measure.map
                    (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                      z.2.1.1)
                    (Measure.map current law) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · fun_prop
                      · exact hcurrent
                _ = Measure.map
                    (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                      z.2.1.1) roundLaw := by
                      rw [show Measure.map current law = roundLaw by
                        simpa [current, law, roundLaw,
                          heterogeneousOnlineProofExactPathLaw] using
                            SOptLib.iidStreamLaw_map_eval roundLaw t]
                _ = batchLaw := by
                      dsimp [roundLaw]
                      unfold heterogeneousOnlineRoundLaw
                      let restLaw : Measure
                          ((HeterogeneousOnlineBatch n Sample b ×
                            HeterogeneousOnlineBatch n Sample b0) ×
                              (Worker n → Ξ)) :=
                        ((heterogeneousOnlineBatchLaw A.problem b).prod
                          (heterogeneousOnlineBatchLaw A.problem b0)).prod
                            (workerCompressionLaw (n := n) A.quantizer)
                      calc
                        Measure.map
                            (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                              z.2.1.1)
                            ((refreshLaw A.refreshProbability
                              A.refresh_admissible).prod restLaw) =
                            Measure.map (fun r => r.1.1) restLaw := by
                              rw [show (fun z :
                                  Bool × ((HeterogeneousOnlineBatch n Sample b ×
                                    HeterogeneousOnlineBatch n Sample b0) ×
                                      (Worker n → Ξ)) => z.2.1.1) =
                                  (fun r => r.1.1) ∘ Prod.snd by rfl]
                              calc
                                Measure.map ((fun r => r.1.1) ∘ Prod.snd)
                                    ((refreshLaw A.refreshProbability
                                      A.refresh_admissible).prod restLaw) =
                                    Measure.map (fun r => r.1.1)
                                      (Measure.map Prod.snd
                                        ((refreshLaw A.refreshProbability
                                          A.refresh_admissible).prod restLaw)) := by
                                            rw [MeasureTheory.Measure.map_map]
                                            · fun_prop
                                            · exact measurable_snd
                                _ = Measure.map (fun r => r.1.1) restLaw := by
                                      rw [MeasureTheory.Measure.map_snd_prod,
                                        measure_univ, one_smul]
                        _ = Measure.map Prod.fst
                            ((heterogeneousOnlineBatchLaw A.problem b).prod
                              (heterogeneousOnlineBatchLaw A.problem b0)) := by
                              dsimp [restLaw]
                              rw [show (fun r :
                                  (HeterogeneousOnlineBatch n Sample b ×
                                    HeterogeneousOnlineBatch n Sample b0) ×
                                      (Worker n → Ξ) => r.1.1) =
                                  Prod.fst ∘ Prod.fst by rfl]
                              calc
                                Measure.map (Prod.fst ∘ Prod.fst)
                                    (((heterogeneousOnlineBatchLaw A.problem b).prod
                                      (heterogeneousOnlineBatchLaw A.problem b0)).prod
                                        (workerCompressionLaw (n := n) A.quantizer)) =
                                    Measure.map Prod.fst
                                      (Measure.map Prod.fst
                                        (((heterogeneousOnlineBatchLaw A.problem b).prod
                                          (heterogeneousOnlineBatchLaw A.problem b0)).prod
                                            (workerCompressionLaw (n := n)
                                              A.quantizer))) := by
                                                rw [MeasureTheory.Measure.map_map]
                                                · exact measurable_fst
                                                · exact measurable_fst
                                _ = Measure.map Prod.fst
                                    ((heterogeneousOnlineBatchLaw A.problem b).prod
                                      (heterogeneousOnlineBatchLaw A.problem b0)) := by
                                      rw [MeasureTheory.Measure.map_fst_prod,
                                        measure_univ, one_smul]
                        _ = batchLaw := by
                              dsimp [batchLaw]
                              rw [MeasureTheory.Measure.map_fst_prod,
                                measure_univ, one_smul]
            have hcoord (i : Worker n) (j : Fin (b i).1) :
                Measure.map
                    (fun batch : HeterogeneousOnlineBatch n Sample b => batch i j)
                    batchLaw = A.problem.sampleLaw i := by
              calc
                Measure.map
                    (fun batch : HeterogeneousOnlineBatch n Sample b => batch i j)
                    batchLaw = Measure.map (fun row : Fin (b i).1 → Sample i => row j)
                      (Measure.map
                        (fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
                        batchLaw) := by
                          rw [MeasureTheory.Measure.map_map]
                          · rfl
                          · exact measurable_pi_apply j
                          · exact measurable_pi_apply i
                _ = Measure.map (fun row : Fin (b i).1 → Sample i => row j)
                    (Measure.infinitePi
                      (fun _ : Fin (b i).1 => A.problem.sampleLaw i)) := by
                      rw [show Measure.map
                          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
                          batchLaw = Measure.infinitePi
                            (fun _ : Fin (b i).1 => A.problem.sampleLaw i) by
                        simpa [batchLaw] using
                          heterogeneous_online_batch_law_worker_marginal
                            A.problem b i]
                _ = A.problem.sampleLaw i := by
                      simpa using
                        (MeasureTheory.Measure.infinitePi_map_eval
                          (μ := fun _ : Fin (b i).1 => A.problem.sampleLaw i) j)
            have hsampleDiff (i : Worker n) (j : Fin (b i).1) :
                ∀ᵐ batch ∂batchLaw,
                  Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
              let coord := fun batch : HeterogeneousOnlineBatch n Sample b => batch i j
              have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
                  (A.problem.sampleLaw i) :=
                ⟨(by dsimp [coord]; fun_prop), by
                  rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
                    simpa [coord] using hcoord i j]⟩
              exact hqmp.tendsto_ae (hVariance.2 i)
            have hsampleLossInt (i : Worker n) (j : Fin (b i).1)
                (z : Point d) : Integrable
                  (fun batch : HeterogeneousOnlineBatch n Sample b =>
                    A.problem.sampleLoss i (batch i j) z) batchLaw := by
              let coord := fun batch : HeterogeneousOnlineBatch n Sample b => batch i j
              have hm : Integrable (fun xi => A.problem.sampleLoss i xi z)
                  (Measure.map coord batchLaw) := by
                rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
                  simpa [coord] using hcoord i j]
                exact A.problem.sampleLoss_integrable i z
              exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
                (by
                  dsimp [coord]
                  exact ((measurable_pi_apply j).comp
                    (measurable_pi_apply i)).aemeasurable)).mp hm
            have hgrad (i : Worker n) (j : Fin (b i).1) :
                AEStronglyMeasurable
                  (fun p : Point d × HeterogeneousOnlineBatch n Sample b =>
                    stochasticGradient A.problem i (p.2 i j) p.1)
                  ((Measure.map query law).prod batchLaw) := by
              exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
                A.problem i (Measure.map query law) batchLaw id
                (fun batch => batch i j)
                stronglyMeasurable_id.aestronglyMeasurable
                (hsampleDiff i j) (hsampleLossInt i j)
            have hworker (i : Worker n) : AEStronglyMeasurable
                (fun p : Point d × HeterogeneousOnlineBatch n Sample b =>
                  average (fun j : Fin (b i).1 =>
                    stochasticGradient A.problem i (p.2 i j) p.1))
                ((Measure.map query law).prod batchLaw) := by
              unfold average SOptLib.finiteUniformAverage
              have hs := (Finset.aestronglyMeasurable_sum Finset.univ
                (fun j _ => hgrad i j)).const_smul
                  ((Fintype.card (Fin (b i).1) : ℝ)⁻¹)
              refine hs.congr (Filter.Eventually.of_forall ?_)
              intro p
              simp [Finset.sum_apply]
            have havg : AEStronglyMeasurable
                (fun p : Point d × HeterogeneousOnlineBatch n Sample b =>
                  average (fun i : Worker n => average (fun j : Fin (b i).1 =>
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
                (fun p : Point d × HeterogeneousOnlineBatch n Sample b =>
                  globalGradient P p.1)
                ((Measure.map query law).prod batchLaw) :=
              ((measurable_gradient (globalObjective P)).comp
                measurable_fst).aestronglyMeasurable
            have hrefreshKernel : AEStronglyMeasurable
                (fun p : Point d × HeterogeneousOnlineBatch n Sample b =>
                  average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                    stochasticGradient A.problem i (p.2 i j) p.1)) -
                    globalGradient P p.1)
                ((Measure.map query law).prod batchLaw) := havg.sub hglobal
            have hrefreshKernelSq : AEStronglyMeasurable
                (fun p : Point d × HeterogeneousOnlineBatch n Sample b =>
                  ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                    stochasticGradient A.problem i (p.2 i j) p.1)) -
                    globalGradient P p.1‖ ^ 2)
                ((Measure.map query law).prod batchLaw) := by
              simpa [pow_two] using hrefreshKernel.norm.mul hrefreshKernel.norm
            have hRefreshInt : Integrable (fun path => ‖refreshError path‖ ^ 2) law := by
              have hcomp :=
                integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
                  (P := law) (ν := batchLaw) (X := query) (Y := refreshBatch)
                  (C := heterogeneousOnlineVarianceTerm σ b)
                  hrefreshKernelSq hxNext.aemeasurable
                  hrefreshBatchMeas.aemeasurable hqueryRefresh
                  hrefreshBatchLaw (fun _ _ => sq_nonneg _)
                  (fun z => (hRefreshFiber z).1)
                  (fun z => (hRefreshFiber z).2)
              simpa [refreshError, query, refreshBatch] using hcomp
            have hRefreshBound :
                (∫ path, ‖refreshError path‖ ^ 2 ∂law) ≤
                  heterogeneousOnlineVarianceTerm σ b := by
              have hbound :=
                integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
                  (P := law) (ν := batchLaw) (X := query) (Y := refreshBatch)
                  hrefreshKernelSq hxNext.aemeasurable
                  hrefreshBatchMeas.aemeasurable hqueryRefresh
                  hrefreshBatchLaw
                  (by simpa [refreshError, query, refreshBatch] using hRefreshInt)
                  (fun z => (hRefreshFiber z).2)
              simpa [refreshError, query, refreshBatch] using hbound
            have hRefreshMeas : AEStronglyMeasurable refreshError law := by
              have hcomp := aestronglyMeasurable_comp_of_indep_product_law
                hxNext.aemeasurable hrefreshBatchMeas.aemeasurable
                (inferInstance : SigmaFinite (Measure.map query law))
                (inferInstance : SigmaFinite (Measure.map refreshBatch law))
                hqueryRefresh (by
                  rw [hrefreshBatchLaw]
                  simpa using hrefreshKernel)
              simpa [refreshError, query, refreshBatch] using hcomp
            let xPrefix := fun pref => (prefixState pref).x
            let direction := fun pref =>
              (prefixState pref).g - globalGradient P (prefixState pref).x
            let noise := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              ((path t).2.1.2, (path t).2.2)
            let noiseLaw := (heterogeneousOnlineBatchLaw A.problem b0).prod
              (workerCompressionLaw (n := n) A.quantizer)
            let innovationKernel := fun
                (pref : Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)
                (q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
              average (fun i : Worker n =>
                A.quantizer.apply
                    (heterogeneousOnlineBatchDifference A.problem b0 q.1 i
                      (queryPrefix pref) (xPrefix pref)) (q.2 i) -
                  localGradientDifference P i (queryPrefix pref) (xPrefix pref))
            let C := (1 / (n.1 : ℝ)) *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
            let B := fun pref => C * ‖queryPrefix pref - xPrefix pref‖ ^ 2
            have hxPrefix : AEStronglyMeasurable xPrefix prefixLaw := by
              have hcomp : AEStronglyMeasurable
                  (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                    xPrefix (prefixMap path)) law := by
                refine ih.1.congr (Filter.Eventually.of_forall ?_)
                intro path
                simpa [xPrefix] using congrArg State.x (hstatePrefix path).symm
              have hfinite := aestronglyMeasurable_prefix_of_comp_general
                roundLaw t xPrefix (by
                  simpa [law, roundLaw, heterogeneousOnlineProofExactPathLaw]
                    using hcomp)
              have hprefixLaw : prefixLaw =
                  Measure.infinitePi (fun _ : Fin t => roundLaw) := by
                simpa [prefixLaw, prefixMap, law, roundLaw,
                  heterogeneousOnlineProofExactPathLaw] using
                    iidStream_prefix_map_eq_infinitePi roundLaw t
              rw [hprefixLaw]
              exact hfinite
            have hdirection : AEStronglyMeasurable direction prefixLaw := by
              have hcomp : AEStronglyMeasurable
                  (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                    direction (prefixMap path)) law := by
                refine ih.2.1.congr (Filter.Eventually.of_forall ?_)
                intro path
                simpa [direction] using congrArg
                  (fun s : State d => s.g - globalGradient P s.x)
                  (hstatePrefix path).symm
              have hfinite := aestronglyMeasurable_prefix_of_comp_general
                roundLaw t direction (by
                  simpa [law, roundLaw, heterogeneousOnlineProofExactPathLaw]
                    using hcomp)
              have hprefixLaw : prefixLaw =
                  Measure.infinitePi (fun _ : Fin t => roundLaw) := by
                simpa [prefixLaw, prefixMap, law, roundLaw,
                  heterogeneousOnlineProofExactPathLaw] using
                    iidStream_prefix_map_eq_infinitePi roundLaw t
              rw [hprefixLaw]
              exact hfinite
            haveI : IsProbabilityMeasure noiseLaw := by
              unfold noiseLaw
              infer_instance
            have hcoord0 (i : Worker n) (j : Fin (b0 i).1) :
                Measure.map
                    (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
                      q.1 i j) noiseLaw = A.problem.sampleLaw i := by
              calc
                _ = Measure.map
                    (fun batch : HeterogeneousOnlineBatch n Sample b0 => batch i j)
                    (Measure.map Prod.fst noiseLaw) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · fun_prop
                      · exact measurable_fst
                _ = Measure.map
                    (fun batch : HeterogeneousOnlineBatch n Sample b0 => batch i j)
                    (heterogeneousOnlineBatchLaw A.problem b0) := by
                      rw [show Measure.map Prod.fst noiseLaw =
                          heterogeneousOnlineBatchLaw A.problem b0 by
                        dsimp [noiseLaw]
                        rw [MeasureTheory.Measure.map_fst_prod, measure_univ,
                          one_smul]]
                _ = A.problem.sampleLaw i := by
                      calc
                        _ = Measure.map (fun row : Fin (b0 i).1 → Sample i => row j)
                            (Measure.map
                              (fun batch : HeterogeneousOnlineBatch n Sample b0 =>
                                batch i)
                              (heterogeneousOnlineBatchLaw A.problem b0)) := by
                                rw [MeasureTheory.Measure.map_map]
                                · rfl
                                · exact measurable_pi_apply j
                                · exact measurable_pi_apply i
                        _ = Measure.map (fun row : Fin (b0 i).1 → Sample i => row j)
                            (Measure.infinitePi
                              (fun _ : Fin (b0 i).1 => A.problem.sampleLaw i)) := by
                                rw [heterogeneous_online_batch_law_worker_marginal
                                  A.problem b0 i]
                        _ = _ := by
                          simpa using MeasureTheory.Measure.infinitePi_map_eval
                            (μ := fun _ : Fin (b0 i).1 => A.problem.sampleLaw i) j
            have hsampleDiff0 (i : Worker n) (j : Fin (b0 i).1) :
                ∀ᵐ q ∂noiseLaw,
                  Differentiable ℝ (A.problem.sampleLoss i (q.1 i j)) := by
              let coord := fun q : HeterogeneousOnlineBatch n Sample b0 ×
                  (Worker n → Ξ) => q.1 i j
              have hqmp : Measure.QuasiMeasurePreserving coord noiseLaw
                  (A.problem.sampleLaw i) :=
                ⟨(by dsimp [coord]; fun_prop), by
                  rw [show Measure.map coord noiseLaw = A.problem.sampleLaw i by
                    simpa [coord] using hcoord0 i j]⟩
              exact hqmp.tendsto_ae (hVariance.2 i)
            have hsampleInt0 (i : Worker n) (j : Fin (b0 i).1)
                (z : Point d) : Integrable
                  (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) =>
                    A.problem.sampleLoss i (q.1 i j) z) noiseLaw := by
              let coord := fun q : HeterogeneousOnlineBatch n Sample b0 ×
                  (Worker n → Ξ) => q.1 i j
              have hm : Integrable (fun xi => A.problem.sampleLoss i xi z)
                  (Measure.map coord noiseLaw) := by
                rw [show Measure.map coord noiseLaw = A.problem.sampleLaw i by
                  simpa [coord] using hcoord0 i j]
                exact A.problem.sampleLoss_integrable i z
              exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
                (by dsimp [coord]; fun_prop)).mp hm
            have hworker0 (i : Worker n) : AEStronglyMeasurable
                (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                    (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
                  A.quantizer.apply
                      (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                        (queryPrefix p.1) (xPrefix p.1)) (p.2.2 i) -
                    localGradientDifference P i (queryPrefix p.1) (xPrefix p.1))
                (prefixLaw.prod noiseLaw) := by
              have hnext (j : Fin (b0 i).1) : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
                    stochasticGradient A.problem i (p.2.1 i j) (queryPrefix p.1))
                  (prefixLaw.prod noiseLaw) :=
                stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
                  A.problem i prefixLaw noiseLaw queryPrefix (fun q => q.1 i j)
                  hqueryPrefix (hsampleDiff0 i j) (hsampleInt0 i j)
              have hcur (j : Fin (b0 i).1) : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
                    stochasticGradient A.problem i (p.2.1 i j) (xPrefix p.1))
                  (prefixLaw.prod noiseLaw) :=
                stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
                  A.problem i prefixLaw noiseLaw xPrefix (fun q => q.1 i j)
                  hxPrefix (hsampleDiff0 i j) (hsampleInt0 i j)
              have hD : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
                    heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                      (queryPrefix p.1) (xPrefix p.1))
                  (prefixLaw.prod noiseLaw) := by
                unfold heterogeneousOnlineBatchDifference average
                  SOptLib.finiteUniformAverage
                have hs := (Finset.aestronglyMeasurable_sum Finset.univ
                  (fun j _ => (hnext j).sub (hcur j))).const_smul
                    ((Fintype.card (Fin (b0 i).1) : ℝ)⁻¹)
                refine hs.congr (Filter.Eventually.of_forall ?_)
                intro p
                simp [Finset.sum_apply, Finset.sum_sub_distrib]
              have hq : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
                    A.quantizer.apply
                      (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                        (queryPrefix p.1) (xPrefix p.1)) (p.2.2 i))
                  (prefixLaw.prod noiseLaw) :=
                (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
                  (hD.aemeasurable.prodMk
                    ((measurable_pi_apply i).comp
                      (measurable_snd.comp measurable_snd)).aemeasurable))
                    |>.aestronglyMeasurable
              have hdelta : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) =>
                    localGradientDifference P i (queryPrefix p.1) (xPrefix p.1))
                  (prefixLaw.prod noiseLaw) := by
                unfold localGradientDifference
                exact (((measurable_localGradient P i).comp_aemeasurable
                  hqueryPrefix.aemeasurable).aestronglyMeasurable.comp_fst).sub
                  (((measurable_localGradient P i).comp_aemeasurable
                    hxPrefix.aemeasurable).aestronglyMeasurable.comp_fst)
              exact hq.sub hdelta
            have hkernel : AEStronglyMeasurable
                (fun p => innovationKernel p.1 p.2)
                (prefixLaw.prod noiseLaw) := by
              unfold innovationKernel average SOptLib.finiteUniformAverage
              have hs := (Finset.aestronglyMeasurable_sum Finset.univ
                (fun i _ => hworker0 i)).const_smul
                  ((Fintype.card (Worker n) : ℝ)⁻¹)
              refine hs.congr (Filter.Eventually.of_forall ?_)
              intro p
              simp [Finset.sum_apply]
            have hfixed (pref) :=
              heterogeneousOnline_fixed_nonrefresh_average_second_moment
                A hE (queryPrefix pref) (xPrefix pref) Llocal ℒlocal σ ω
                hSmooth hVariance (fun i => by
                  simpa [queryPrefix, xPrefix, prefixState,
                    heterogeneousOnlineCorrectedProofExactProcess,
                    SOptLib.recursiveIterateProcess, heterogeneousOnlineStep]
                    using hAverageSmooth.2 t i (extend pref)) hQuantizer
            have hStepPrefix : Integrable
                (fun pref => ‖queryPrefix pref - xPrefix pref‖ ^ 2) prefixLaw := by
              have hcomp : Integrable
                  (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                    ‖queryPrefix (prefixMap path) - xPrefix (prefixMap path)‖ ^ 2)
                  law := by
                refine ih.2.2.2.2.2.1.congr (Filter.Eventually.of_forall ?_)
                intro path
                dsimp [StepMomentWellDefined]
                congr 2
                rw [show xPrefix (prefixMap path) = (run t path).x by
                  simpa [xPrefix] using congrArg State.x (hstatePrefix path)]
                rw [show queryPrefix (prefixMap path) = (run (t + 1) path).x by
                  simpa [query] using hqueryEq path]
              have hfinite := integrable_prefix_of_comp_general roundLaw t
                (fun pref => ‖queryPrefix pref - xPrefix pref‖ ^ 2) (by
                  simpa [law, roundLaw, heterogeneousOnlineProofExactPathLaw]
                    using hcomp)
              have hprefixLaw : prefixLaw =
                  Measure.infinitePi (fun _ : Fin t => roundLaw) := by
                simpa [prefixLaw, prefixMap, law, roundLaw,
                  heterogeneousOnlineProofExactPathLaw] using
                    iidStream_prefix_map_eq_infinitePi roundLaw t
              rw [hprefixLaw]
              exact hfinite
            have hB : Integrable B prefixLaw := by
              simpa [B] using hStepPrefix.const_mul C
            have hkernelSq : AEStronglyMeasurable
                (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
                (prefixLaw.prod noiseLaw) := by
              simpa [pow_two] using hkernel.norm.mul hkernel.norm
            have hproductSq : Integrable
                (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
                (prefixLaw.prod noiseLaw) := by
              rw [integrable_prod_iff hkernelSq]
              refine ⟨Filter.Eventually.of_forall (fun pref => (hfixed pref).2.2.1), ?_⟩
              refine Integrable.mono hB (hkernelSq.norm.integral_prod_right')
                (Filter.Eventually.of_forall ?_)
              intro pref
              have hb := (hfixed pref).2.2.2
              have hBnonneg : 0 ≤ B pref :=
                (integral_nonneg fun _ => sq_nonneg _).trans hb
              have hnorm : (fun q => ‖‖innovationKernel pref q‖ ^ 2‖) =
                  (fun q => ‖innovationKernel pref q‖ ^ 2) := by
                funext q
                exact Real.norm_of_nonneg (sq_nonneg _)
              rw [hnorm, Real.norm_of_nonneg hBnonneg,
                Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
              simpa [B, C] using hb
            let noiseOfRound := fun z :
                HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              (z.2.1.2, z.2.2)
            have hnoiseOfRound : Measurable noiseOfRound := by
              dsimp [noiseOfRound]
              fun_prop
            have hfreshPrefix : ProbabilityTheory.IndepFun prefixMap noise law := by
              simpa [noise, current, noiseOfRound, Function.comp_def] using
                hpastCurrent.comp measurable_id hnoiseOfRound
            have hnoise : AEMeasurable noise law := by
              dsimp [noise]
              fun_prop
            have hnoiseLaw : Measure.map noise law = noiseLaw := by
              calc
                Measure.map noise law = Measure.map noiseOfRound
                    (Measure.map current law) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · exact hnoiseOfRound
                      · exact hcurrent
                _ = Measure.map noiseOfRound roundLaw := by
                      rw [show Measure.map current law = roundLaw by
                        simpa [current, law, roundLaw,
                          heterogeneousOnlineProofExactPathLaw] using
                            SOptLib.iidStreamLaw_map_eval roundLaw t]
                _ = noiseLaw := by
                      let batches :=
                        (heterogeneousOnlineBatchLaw A.problem b).prod
                          (heterogeneousOnlineBatchLaw A.problem b0)
                      let compressions := workerCompressionLaw (n := n) A.quantizer
                      let selectNoise := fun r :
                          (HeterogeneousOnlineBatch n Sample b ×
                            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                        (r.1.2, r.2)
                      have hselectNoise : Measurable selectNoise := by
                        dsimp [selectNoise]
                        fun_prop
                      change Measure.map (selectNoise ∘ Prod.snd)
                          ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                            (batches.prod compressions)) = noiseLaw
                      calc
                        _ = Measure.map selectNoise
                            (Measure.map Prod.snd
                              ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                                (batches.prod compressions))) := by
                              exact (MeasureTheory.Measure.map_map hselectNoise
                                measurable_snd).symm
                        _ = Measure.map selectNoise (batches.prod compressions) := by
                              rw [MeasureTheory.Measure.map_snd_prod, measure_univ,
                                one_smul]
                        _ = noiseLaw := by
                              simpa [selectNoise, batches, compressions, noiseLaw,
                                Prod.map] using
                                (MeasureTheory.Measure.map_prod_map batches compressions
                                  measurable_snd measurable_id).symm
            let innovation := fun path =>
              innovationKernel (prefixMap path) (noise path)
            have hInnovationSq : Integrable
                (fun path => ‖innovation path‖ ^ 2) law := by
              have honMap : Integrable
                  (fun p => ‖innovationKernel p.1 p.2‖ ^ 2)
                  (Measure.map (fun path => (prefixMap path, noise path)) law) := by
                rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                  hprefix.aemeasurable hnoise).mp hfreshPrefix, hnoiseLaw]
                exact hproductSq
              have hcomp := (MeasureTheory.integrable_map_measure
                (by
                  rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                    hprefix.aemeasurable hnoise).mp hfreshPrefix, hnoiseLaw]
                  exact hkernelSq)
                (hprefix.aemeasurable.prodMk hnoise)).mp honMap
              simpa [innovation, Function.comp_def] using hcomp
            have hInnovationMeas : AEStronglyMeasurable innovation law := by
              have hk : AEStronglyMeasurable
                  (fun p => innovationKernel p.1 p.2)
                  ((Measure.map prefixMap law).prod (Measure.map noise law)) := by
                rw [hnoiseLaw]
                simpa [prefixLaw] using hkernel
              simpa [innovation, Function.comp_def] using
                (aestronglyMeasurable_comp_of_indep_product_law
                  hprefix.aemeasurable hnoise
                  (inferInstance : SigmaFinite (Measure.map prefixMap law))
                  (inferInstance : SigmaFinite (Measure.map noise law))
                  hfreshPrefix hk)
            let residual := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              (run t path).g - globalGradient P (run t path).x
            have hResidualSq : Integrable (fun path => ‖residual path‖ ^ 2) law := by
              simpa [residual, EstimatorErrorMomentWellDefined] using
                ih.2.2.2.2.1
            have hInnerInt : Integrable
                (fun path => ⟪residual path, innovation path⟫_ℝ) law :=
              integrable_inner_of_integrable_sq_norm ih.2.1 hInnovationMeas
                hResidualSq hInnovationSq
            have hfixedInnerZero (pref) :
                (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) = 0 := by
              have hlin := ContinuousLinearMap.integral_comp_comm
                (L := (innerSL ℝ) (direction pref)) (hfixed pref).1
              calc
                _ = (innerSL ℝ) (direction pref)
                    (∫ q, innovationKernel pref q ∂noiseLaw) := hlin
                _ = 0 := by rw [(hfixed pref).2.1]; simp
            have hCross :
                (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
              have hscalar : AEStronglyMeasurable
                  (fun p => ⟪direction p.1, innovationKernel p.1 p.2⟫_ℝ)
                  (prefixLaw.prod noiseLaw) := hdirection.comp_fst.inner hkernel
              have hcompInt : Integrable
                  (fun path => ⟪direction (prefixMap path),
                    innovationKernel (prefixMap path) (noise path)⟫_ℝ) law := by
                apply hInnerInt.congr
                filter_upwards [] with path
                dsimp [direction, residual, innovation]
                rw [hstatePrefix path]
              have hzero :=
                integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
                  (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
                  (φ := fun pref q => ⟪direction pref, innovationKernel pref q⟫_ℝ)
                  (by simpa [prefixLaw] using hscalar)
                  hprefix.aemeasurable hnoise hfreshPrefix hnoiseLaw hcompInt
                  hfixedInnerZero
              rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
                  ∫ path, ⟪direction (prefixMap path),
                    innovationKernel (prefixMap path) (noise path)⟫_ℝ ∂law by
                apply integral_congr_ae
                filter_upwards [] with path
                dsimp [direction, residual, innovation]
                rw [hstatePrefix path]]
              exact hzero
            have hNonrefreshInt : Integrable
                (fun path => ‖residual path + innovation path‖ ^ 2) law :=
              integrable_sq_norm_add ih.2.1 hInnovationMeas
                hResidualSq hInnovationSq
            have hNonrefreshEq :
                (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
                  (∫ path, ‖residual path‖ ^ 2 ∂law) +
                    ∫ path, ‖innovation path‖ ^ 2 ∂law := by
              let pair : Bool →
                  (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) → Point d :=
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
            have hBComp : Integrable (fun path => B (prefixMap path)) law := by
              have hs := ih.2.2.2.2.2.1.const_mul C
              apply hs.congr
              filter_upwards [] with path
              dsimp [B]
              rw [hqueryEq path]
              rw [show xPrefix (prefixMap path) = (run t path).x by
                simpa [xPrefix] using congrArg State.x (hstatePrefix path)]
            have hInnovationBound :
                (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
                  C * stepMoment run law t := by
              have hbound :=
                integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
                  (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
                  (φ := fun pref q => ‖innovationKernel pref q‖ ^ 2) (B := B)
                  (by simpa [prefixLaw] using hkernelSq) hB.aestronglyMeasurable
                  hprefix.aemeasurable hnoise hfreshPrefix hnoiseLaw
                  hInnovationSq hBComp
                  (fun pref => by simpa [B, C] using (hfixed pref).2.2.2)
              calc
                _ ≤ ∫ path, B (prefixMap path) ∂law := by
                  simpa [innovation] using hbound
                _ = C * stepMoment run law t := by
                  unfold stepMoment
                  rw [← integral_const_mul]
                  apply integral_congr_ae
                  filter_upwards [] with path
                  dsimp [B]
                  rw [hqueryEq path]
                  rw [show xPrefix (prefixMap path) = (run t path).x by
                    simpa [xPrefix] using congrArg State.x (hstatePrefix path)]
            have hNonrefreshBound :
                (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
                  estimatorErrorMoment P run law t + C * stepMoment run law t := by
              rw [hNonrefreshEq]
              change estimatorErrorMoment P run law t +
                (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ _
              exact add_le_add_right hInnovationBound _
            have hdecomp : ∀ path, residualNext path =
                if (path t).1 then refreshError path
                else residual path + innovation path := by
              intro path
              let s := run t path
              let xN := primalStep A.stepSize s
              let q := fun i : Worker n =>
                A.quantizer.apply
                  (heterogeneousOnlineBatchDifference A.problem b0
                    (path t).2.1.2 i xN s.x) ((path t).2.2 i)
              have hdiffAvg : average (fun i : Worker n =>
                  localGradientDifference P i xN s.x) =
                  globalGradient P xN - globalGradient P s.x := by
                rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
                  globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
                unfold averageLocalGradient localGradientDifference average
                  SOptLib.finiteUniformAverage
                rw [Finset.sum_sub_distrib, smul_sub]
              have hinn : innovation path =
                  average q - average (fun i : Worker n =>
                    localGradientDifference P i xN s.x) := by
                dsimp [innovation, innovationKernel, noise]
                rw [hqueryEq path]
                rw [show xPrefix (prefixMap path) = (run t path).x by
                  simpa [xPrefix] using congrArg State.x (hstatePrefix path)]
                change average (fun i : Worker n => q i -
                    localGradientDifference P i xN s.x) =
                  average q - average (fun i : Worker n =>
                    localGradientDifference P i xN s.x)
                unfold average SOptLib.finiteUniformAverage
                rw [Finset.sum_sub_distrib, smul_sub]
              have hnext : residualNext path =
                  average (fun i : Worker n =>
                    if (path t).1 then average (fun j : Fin (b i).1 =>
                      stochasticGradient A.problem i ((path t).2.1.1 i j) xN)
                    else s.g + q i) - globalGradient P xN := by
                rfl
              cases h : (path t).1 with
              | false =>
                  simp only [h, Bool.false_eq_true, if_false]
                  rw [hnext]
                  simp only [h, if_false]
                  change average (fun i : Worker n => s.g + q i) -
                      globalGradient P xN = residual path + innovation path
                  rw [average_const_add, hinn, hdiffAvg]
                  dsimp [residual, s]
                  abel
              | true =>
                  simp only [h, if_true]
                  rw [hnext]
                  simp only [h, if_true]
                  rfl
            let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
            let restLaw := ((heterogeneousOnlineBatchLaw A.problem b).prod
              (heterogeneousOnlineBatchLaw A.problem b0)).prod
                (workerCompressionLaw (n := n) A.quantizer)
            haveI : IsProbabilityMeasure restLaw := by
              dsimp [restLaw]
              infer_instance
            let projectNoise := fun r :
                ((HeterogeneousOnlineBatch n Sample b ×
                  HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
              (r.1.2, r.2)
            let nonrefreshKernel := fun pref r =>
              ‖direction pref + innovationKernel pref (projectNoise r)‖ ^ 2
            have hprojectNoise : Measurable projectNoise := by
              dsimp [projectNoise]
              fun_prop
            have hprojectNoiseLaw : Measure.map projectNoise restLaw = noiseLaw := by
              dsimp [projectNoise, restLaw, noiseLaw]
              let batches := (heterogeneousOnlineBatchLaw A.problem b).prod
                (heterogeneousOnlineBatchLaw A.problem b0)
              simpa [batches, Prod.map] using
                (MeasureTheory.Measure.map_prod_map batches
                  (workerCompressionLaw (n := n) A.quantizer)
                  measurable_snd measurable_id).symm
            have hNonrefreshKernel : AEStronglyMeasurable
                (Function.uncurry nonrefreshKernel) (prefixLaw.prod restLaw) := by
              let pull := fun p :
                  (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                    ((HeterogeneousOnlineBatch n Sample b ×
                      HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
                (p.1, projectNoise p.2)
              have hpull : Measurable pull := by dsimp [pull]; fun_prop
              have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
                  prefixLaw.prod noiseLaw := by
                have hm := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
                  measurable_id hprojectNoise
                rw [Measure.map_id, hprojectNoiseLaw] at hm
                simpa [pull] using hm.symm
              have hbase : AEStronglyMeasurable
                  (fun p => ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
                  (prefixLaw.prod noiseLaw) := by
                have hv := hdirection.comp_fst.add hkernel
                simpa [pow_two] using hv.norm.mul hv.norm
              have hqmp : Measure.QuasiMeasurePreserving pull
                  (prefixLaw.prod restLaw) (prefixLaw.prod noiseLaw) :=
                ⟨hpull, by rw [hpullLaw]⟩
              simpa [nonrefreshKernel, Function.uncurry, pull] using
                hbase.comp_quasiMeasurePreserving hqmp
            have hNonrefreshIndep : ProbabilityTheory.IndepFun
                (fun path => ‖residual path + innovation path‖ ^ 2)
                (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                  (path t).1) law := by
              have hi := iidStream_prefix_current_snd_kernel_indep_fst
                coinLaw restLaw t nonrefreshKernel (by
                  have hp : prefixLaw =
                      Measure.infinitePi (fun _ : Fin t => coinLaw.prod restLaw) := by
                    simpa [prefixLaw, prefixMap, law, roundLaw, coinLaw, restLaw,
                      heterogeneousOnlineProofExactPathLaw,
                      heterogeneousOnlineRoundLaw] using
                        iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) t
                  rw [← hp]
                  exact hNonrefreshKernel)
              apply hi.congr (Filter.Eventually.of_forall ?_)
                (Filter.Eventually.of_forall fun _ => rfl)
              intro path
              change ‖direction (prefixMap path) +
                  innovationKernel (prefixMap path) (noise path)‖ ^ 2 =
                ‖residual path + innovation path‖ ^ 2
              dsimp [direction, residual]
              rw [hstatePrefix path]
            let refreshKernelRest := fun pref
                (r : (HeterogeneousOnlineBatch n Sample b ×
                  HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
              ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                  stochasticGradient A.problem i (r.1.1 i j) (queryPrefix pref))) -
                globalGradient P (queryPrefix pref)‖ ^ 2
            have hRefreshPrefixBatch : AEStronglyMeasurable
                (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                    HeterogeneousOnlineBatch n Sample b =>
                  ‖average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                      stochasticGradient A.problem i (p.2 i j) (queryPrefix p.1))) -
                    globalGradient P (queryPrefix p.1)‖ ^ 2)
                (prefixLaw.prod batchLaw) := by
              have hgradPrefix (i : Worker n) (j : Fin (b i).1) :
                  AEStronglyMeasurable
                    (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                        HeterogeneousOnlineBatch n Sample b =>
                      stochasticGradient A.problem i (p.2 i j) (queryPrefix p.1))
                    (prefixLaw.prod batchLaw) :=
                stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
                  A.problem i prefixLaw batchLaw queryPrefix (fun batch => batch i j)
                  hqueryPrefix (hsampleDiff i j) (hsampleLossInt i j)
              have hworkerPrefix (i : Worker n) : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      HeterogeneousOnlineBatch n Sample b =>
                    average (fun j : Fin (b i).1 =>
                      stochasticGradient A.problem i (p.2 i j) (queryPrefix p.1)))
                  (prefixLaw.prod batchLaw) := by
                unfold average SOptLib.finiteUniformAverage
                have hs := (Finset.aestronglyMeasurable_sum Finset.univ
                  (fun j _ => hgradPrefix i j)).const_smul
                    ((Fintype.card (Fin (b i).1) : ℝ)⁻¹)
                refine hs.congr (Filter.Eventually.of_forall ?_)
                intro p
                simp [Finset.sum_apply]
              have havgPrefix : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      HeterogeneousOnlineBatch n Sample b =>
                    average (fun i : Worker n => average (fun j : Fin (b i).1 =>
                      stochasticGradient A.problem i (p.2 i j) (queryPrefix p.1))))
                  (prefixLaw.prod batchLaw) := by
                unfold average SOptLib.finiteUniformAverage
                have hs := (Finset.aestronglyMeasurable_sum Finset.univ
                  (fun i _ => hworkerPrefix i)).const_smul
                    ((Fintype.card (Worker n) : ℝ)⁻¹)
                refine hs.congr (Filter.Eventually.of_forall ?_)
                intro p
                simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
              have hglobalPrefix : AEStronglyMeasurable
                  (fun p : (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                      HeterogeneousOnlineBatch n Sample b =>
                    globalGradient P (queryPrefix p.1))
                  (prefixLaw.prod batchLaw) :=
                (((measurable_gradient (globalObjective P)).comp_aemeasurable
                  hqueryPrefix.aemeasurable).aestronglyMeasurable.comp_fst)
              have hv := havgPrefix.sub hglobalPrefix
              simpa [pow_two] using hv.norm.mul hv.norm
            have hRefreshKernelRest : AEStronglyMeasurable
                (Function.uncurry refreshKernelRest) (prefixLaw.prod restLaw) := by
              let pull := fun p :
                  (Fin t → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ×
                    ((HeterogeneousOnlineBatch n Sample b ×
                      HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
                (p.1, p.2.1.1)
              have hpull : Measurable pull := by dsimp [pull]; fun_prop
              have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
                  prefixLaw.prod batchLaw := by
                let projectBatch := fun r :
                    (HeterogeneousOnlineBatch n Sample b ×
                      HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                  r.1.1
                have hpb : Measurable projectBatch := by dsimp [projectBatch]; fun_prop
                have hpbl : Measure.map projectBatch restLaw = batchLaw := by
                  dsimp [projectBatch, restLaw, batchLaw]
                  calc
                    _ = Measure.map Prod.fst
                        (Measure.map Prod.fst restLaw) := by
                          rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
                          rfl
                    _ = Measure.map Prod.fst
                        ((heterogeneousOnlineBatchLaw A.problem b).prod
                          (heterogeneousOnlineBatchLaw A.problem b0)) := by
                            rw [show Measure.map Prod.fst restLaw =
                                (heterogeneousOnlineBatchLaw A.problem b).prod
                                  (heterogeneousOnlineBatchLaw A.problem b0) by
                              dsimp [restLaw]
                              rw [MeasureTheory.Measure.map_fst_prod, measure_univ,
                                one_smul]]
                    _ = _ := by rw [MeasureTheory.Measure.map_fst_prod,
                      measure_univ, one_smul]
                have hm := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
                  measurable_id hpb
                rw [hpbl] at hm
                simpa [pull, projectBatch] using hm.symm
              have hqmp : Measure.QuasiMeasurePreserving pull
                  (prefixLaw.prod restLaw) (prefixLaw.prod batchLaw) :=
                ⟨hpull, by rw [hpullLaw]⟩
              simpa [refreshKernelRest, Function.uncurry, pull] using
                hRefreshPrefixBatch.comp_quasiMeasurePreserving hqmp
            have hRefreshIndep : ProbabilityTheory.IndepFun
                (fun path => ‖refreshError path‖ ^ 2)
                (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
                  (path t).1) law := by
              have hi := iidStream_prefix_current_snd_kernel_indep_fst
                coinLaw restLaw t refreshKernelRest (by
                  have hp : prefixLaw =
                      Measure.infinitePi (fun _ : Fin t => coinLaw.prod restLaw) := by
                    simpa [prefixLaw, prefixMap, law, roundLaw, coinLaw, restLaw,
                      heterogeneousOnlineProofExactPathLaw,
                      heterogeneousOnlineRoundLaw] using
                        iidStream_prefix_map_eq_infinitePi (coinLaw.prod restLaw) t
                  rw [← hp]
                  exact hRefreshKernelRest)
              apply hi.congr (Filter.Eventually.of_forall ?_)
                (Filter.Eventually.of_forall fun _ => rfl)
              intro path
              change refreshKernelRest (prefixMap path) (path t).2 =
                ‖refreshError path‖ ^ 2
              dsimp [refreshKernelRest, refreshError, refreshBatch]
              rw [hqueryEq path]
            let branch := fun path :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              (path t).1
            have hbranch : Measurable branch := by dsimp [branch]; fun_prop
            have hbranchLaw : Measure.map branch law = coinLaw := by
              calc
                Measure.map branch law = Measure.map Prod.fst
                    (Measure.map current law) := by
                      rw [MeasureTheory.Measure.map_map]
                      · rfl
                      · exact measurable_fst
                      · exact hcurrent
                _ = Measure.map Prod.fst roundLaw := by
                      rw [show Measure.map current law = roundLaw by
                        simpa [current, law, roundLaw,
                          heterogeneousOnlineProofExactPathLaw] using
                            SOptLib.iidStreamLaw_map_eval roundLaw t]
                _ = coinLaw := by
                      dsimp [coinLaw, roundLaw]
                      unfold heterogeneousOnlineRoundLaw
                      rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
            have htrueMass : coinLaw.real ({true} : Set Bool) =
                A.refreshProbability := by
              rw [measureReal_def]
              dsimp [coinLaw]
              unfold refreshLaw
              rw [PMF.toMeasure_apply_singleton _ true
                (measurableSet_singleton true)]
              simp [PMF.bernoulli_apply]
            have hfalseMass : coinLaw.real ({false} : Set Bool) =
                1 - A.refreshProbability := by
              rw [measureReal_def]
              dsimp [coinLaw]
              unfold refreshLaw
              rw [PMF.toMeasure_apply_singleton _ false
                (measurableSet_singleton false)]
              simp only [PMF.bernoulli_apply, Bool.cond_false]
              let pNN : NNReal :=
                ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
              have hpNN : pNN ≤ (1 : NNReal) := by
                exact_mod_cast A.refresh_admissible.2
              change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
              rw [NNReal.coe_sub hpNN]
              rfl
            let refreshSq := fun path => ‖refreshError path‖ ^ 2
            let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
            have hRefreshGate :
                (∫ path, if branch path = true then refreshSq path else 0 ∂law) ≤
                  A.refreshProbability * ∫ path, refreshSq path ∂law :=
              integral_independent_bool_gate_le law coinLaw true
                A.refreshProbability refreshSq branch
                (by simpa [refreshSq] using hRefreshInt) hbranch
                (by simpa [refreshSq, branch] using hRefreshIndep)
                hbranchLaw htrueMass
            have hNonrefreshGate :
                (∫ path, if branch path = false then nonrefreshSq path else 0 ∂law) ≤
                  (1 - A.refreshProbability) *
                    ∫ path, nonrefreshSq path ∂law :=
              integral_independent_bool_gate_le law coinLaw false
                (1 - A.refreshProbability) nonrefreshSq branch
                (by simpa [nonrefreshSq] using hNonrefreshInt) hbranch
                (by simpa [nonrefreshSq, branch] using hNonrefreshIndep)
                hbranchLaw hfalseMass
            have hRefreshGateInt : Integrable
                (fun path => if branch path = true then refreshSq path else 0) law := by
              have hs : MeasurableSet {path | branch path = true} :=
                hbranch (measurableSet_singleton true)
              simpa [refreshSq, Set.piecewise] using Integrable.piecewise hs
                hRefreshInt.integrableOn (integrable_const (c := (0 : ℝ))).integrableOn
            have hNonrefreshGateInt : Integrable
                (fun path => if branch path = false then nonrefreshSq path else 0) law := by
              have hs : MeasurableSet {path | branch path = false} :=
                hbranch (measurableSet_singleton false)
              simpa [nonrefreshSq, Set.piecewise] using Integrable.piecewise hs
                hNonrefreshInt.integrableOn (integrable_const (c := (0 : ℝ))).integrableOn
            have hNextError : EstimatorErrorMomentWellDefined P run law (t + 1) := by
              let s : Set (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) :=
                {path | branch path = true}
              have hs : MeasurableSet s := hbranch (measurableSet_singleton true)
              have hp := Integrable.piecewise hs hRefreshInt.integrableOn
                hNonrefreshInt.integrableOn
              have heq : s.piecewise refreshSq nonrefreshSq =
                  (fun path => ‖residualNext path‖ ^ 2) := by
                funext path
                by_cases hb : branch path = true
                · simp [s, Set.piecewise, hb, refreshSq, nonrefreshSq,
                    hdecomp path, branch]
                · have hf : branch path = false := Bool.eq_false_of_not_eq_true hb
                  simp [s, Set.piecewise, hb, hf, refreshSq, nonrefreshSq,
                    hdecomp path, branch]
              rw [EstimatorErrorMomentWellDefined, ← heq]
              exact hp
            have hResidualMeas : AEStronglyMeasurable residualNext law := by
              let s : Set (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) :=
                {path | branch path = true}
              have hs : MeasurableSet s := hbranch (measurableSet_singleton true)
              have hn : AEStronglyMeasurable
                  (fun path => residual path + innovation path) law :=
                ih.2.1.add hInnovationMeas
              have hp := (hRefreshMeas.mono_measure Measure.restrict_le_self).piecewise hs
                (hn.mono_measure Measure.restrict_le_self)
              refine hp.congr (Filter.Eventually.of_forall ?_)
              intro path
              by_cases hb : branch path = true
              · simp [s, Set.piecewise, hb, hdecomp path, branch]
              · have hf : branch path = false := Bool.eq_false_of_not_eq_true hb
                simp [s, Set.piecewise, hb, hf, hdecomp path, branch]
            have hNextSplit : estimatorErrorMoment P run law (t + 1) =
                (∫ path, if branch path = true then refreshSq path else 0 ∂law) +
                  ∫ path, if branch path = false then nonrefreshSq path else 0 ∂law := by
              unfold estimatorErrorMoment
              rw [← integral_add hRefreshGateInt hNonrefreshGateInt]
              apply integral_congr_ae
              filter_upwards [] with path
              rw [show (run (t + 1) path).g -
                  globalGradient P (run (t + 1) path).x = residualNext path by rfl,
                hdecomp path]
              by_cases hb : branch path = true
              · simp [hb, branch, refreshSq, nonrefreshSq]
              · have hf : branch path = false := Bool.eq_false_of_not_eq_true hb
                simp [hb, hf, branch, refreshSq, nonrefreshSq]
            refine ⟨hResidualMeas, hNextError, ?_⟩
            rw [hNextSplit]
            calc
              _ ≤ A.refreshProbability * (∫ path, refreshSq path ∂law) +
                    (1 - A.refreshProbability) *
                      (∫ path, nonrefreshSq path ∂law) :=
                add_le_add hRefreshGate hNonrefreshGate
              _ ≤ A.refreshProbability * heterogeneousOnlineVarianceTerm σ b +
                    (1 - A.refreshProbability) *
                      (estimatorErrorMoment P run law t + C * stepMoment run law t) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left
                    (by simpa [refreshSq] using hRefreshBound)
                    (le_of_lt A.refresh_admissible.1)
                · exact mul_le_mul_of_nonneg_left
                    (by simpa [nonrefreshSq] using hNonrefreshBound)
                    (sub_nonneg.mpr A.refresh_admissible.2)
              _ = _ := by dsimp [C]; ring
          exact hAdaptiveBranchTransport hRefreshFixed
        have hgL2Succ : Integrable
            (fun path => ‖(run (t + 1) path).g‖ ^ 2) law := by
          have hgradMeas : AEStronglyMeasurable
              (fun path => globalGradient P (run (t + 1) path).x) law :=
            ((measurable_gradient (globalObjective P)).comp_aemeasurable
              hxNext.aemeasurable).aestronglyMeasurable
          have hadd := integrable_sq_norm_add hStochastic.1 hgradMeas
            (by simpa [residualNext, EstimatorErrorMomentWellDefined] using
              hStochastic.2.1)
            hglobalSucc
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          dsimp [residualNext]
          abel
        have hStepSucc : StepMomentWellDefined run law (t + 1) := by
          have hscaled := integrable_sq_norm_const_smul
            (-(A.stepSize : ℝ)) hgL2Succ
          simpa [StepMomentWellDefined, run,
            heterogeneousOnlineCorrectedProofExactProcess,
            SOptLib.recursiveIterateProcess, heterogeneousOnlineStep,
            primalStep_eq] using hscaled
        refine ⟨hxNext, hStochastic.1, hxL2Succ, hgL2Succ,
          hStochastic.2.1, hStepSucc, ?_⟩
        intro j hj
        by_cases hjt : j < t
        · exact ih.2.2.2.2.2.2 j hjt
        · have hEq : j = t := by omega
          subst j
          exact hStochastic.2.2
  exact hScalarComponents k

/-- `book/MARINA/MARINA.json#/key_lemmas/7`, Eq. (46), with the exact
worker-dependent coefficients specified in Remark D.2.  The proof projects
the private simultaneous scalar/component induction above. -/
theorem heterogeneous_online_estimator_recurrence_46_proof_exact_literal_source_boundary
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : HeterogeneousOnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩
      (heterogeneousOnlineCorrectedProofExactProcess
        (b := b) (b0 := b0) A hE x0) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := heterogeneousOnlineCorrectedProofExactProcess
      (b := b) (b0 := b0) A hE x0
    let law := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
        A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
  rcases heterogeneousOnlineProofExactProcess_scalar_recurrence_components
    A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hAverageSmooth k with
    ⟨_hxk, _hresidualk, _hxL2k, _hgL2k, hErrorK, hStepK, _hHistoryK⟩
  rcases heterogeneousOnlineProofExactProcess_scalar_recurrence_components
    A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hAverageSmooth (k + 1) with
    ⟨_hxNext, _hresidualNext, _hxL2Next, _hgL2Next, hErrorNext,
      _hStepNext, hHistoryNext⟩
  exact ⟨hErrorNext, hErrorK, hStepK,
    hHistoryNext k (Nat.lt_succ_self k)⟩

theorem Theorem_D3_heterogeneous_online_VR_nonconvex_corrected
    {d n K : Count} {b b0 : Worker n → Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : HeterogeneousOnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩
      (heterogeneousOnlineCorrectedProofExactProcess
        (b := b) (b0 := b0) A hE x0) ℒlocal)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    Integrable (fun z =>
        ‖globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
          (uniformOutput (K := K)
            (heterogeneousOnlineCorrectedProofExactProcess (b := b) (b0 := b0) A hE x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw
          (heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A) K) ∧
      (∫ z,
          ‖globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
            (uniformOutput (K := K)
              (heterogeneousOnlineCorrectedProofExactProcess (b := b) (b0 := b0) A hE x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A) K) ≤
        2 * (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
            (A.stepSize * K.1) + heterogeneousOnlineVarianceTerm σ b := by
  have hEq46 (k : ℕ) :=
    heterogeneous_online_estimator_recurrence_46_proof_exact_literal_source_boundary
      A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hAverageSmooth k
  classical
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := heterogeneousOnlineCorrectedProofExactProcess (b := b) (b0 := b0) A hE x0
  let law := heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  let V : ℝ := heterogeneousOnlineVarianceTerm σ b
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  have hComponents (k : ℕ) :=
    heterogeneousOnlineProofExactProcess_scalar_recurrence_components
      A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hAverageSmooth k
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law := by
    simpa [P, run, law] using (hComponents k).1
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp_aemeasurable
        (hxMeas k).aemeasurable).aestronglyMeasurable
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, EstimatorErrorMomentWellDefined] using
      (hComponents k).2.2.2.2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, StepMomentWellDefined] using
      (hComponents k).2.2.2.2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, heterogeneousOnlineCorrectedProofExactProcess,
        SOptLib.recursiveIterateProcess, heterogeneousOnlineStep, primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V := by
    have hrec := (hEq46 k).2.2.2
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hS : 0 ≤ heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0 := by
    unfold heterogeneousFiniteBatchSmoothnessTerm average SOptLib.finiteUniformAverage
    positivity
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact heterogeneous_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hS hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k + γ / 2 * V := by
    have hDnonneg : 0 ≤ D k := by
      exact integral_nonneg fun path => sq_nonneg _
    simpa [Φ] using online_vr_nonconvex_lyapunov_step F E G D k hγ hp
      hDnonneg hCoeff (hDescent k) (hRecurrence k)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤
        Φ 0 - Φ N + (N : ℝ) * (γ / 2) * V := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) + γ / 2 * V := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
        globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable (fun _ : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
        fStar) law := integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := by
    exact integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar + (K.1 : ℝ) * (γ / 2) * V := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    simp only [mul_zero, add_zero] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) + V := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar + (K.1 : ℝ) * (γ / 2) * V) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) + V := by
        field_simp [ne_of_gt hγ, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
            (uniformOutput (K := K)
              (heterogeneousOnlineCorrectedProofExactProcess (b := b) (b0 := b0) A hE x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (heterogeneousOnlineProofExactPathLaw (b := b) (b0 := b0) A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ, V] using hAverageBound

/-- `book/MARINA/MARINA.json#/key_lemmas/20`, Remark D.2: "the statement of
Theorem 3.2 remains the same" with worker-dependent batches and the requirement
`n⁻²∑ᵢσᵢ²/bᵢ=Θ(ε²)`.  The supplied family is the source's asymptotic
representative; the generated algorithm executes its common ceiling inflation,
which preserves that order and enforces the pointwise Eq. (41) half-budget. -/
theorem Remark_D2_heterogeneous_online_batches_corrected
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (b : Accuracy → Worker n → Count)
    (b0 : Worker n → Count) (Llocal ℒlocal σ : Worker n → ℝ)
    (ω fStar : ℝ)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε i, (b0 i).1 < (b ε i).1)
    (hAverageSmooth : ∀ ε,
      HeterogeneousOnlineAverageSmoothnessCorrected (b0 := b0)
        ⟨A.problem, hE⟩
        (heterogeneousOnlineCorrectedProofExactProcess
          (b := heterogeneousOnlineBatchScheduleFromBase σ b ε)
          (b0 := b0) A hE x0) ℒlocal)
    (hBatchOrder : AccuracyTheta
      (fun ε => heterogeneousOnlineVarianceTerm σ (b ε))
      (fun ε => (ε : ℝ) ^ 2))
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    let chosenBatch := heterogeneousOnlineBatchScheduleFromBase σ b
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    (∀ (ε : Accuracy) (K : Count),
      Integrable (fun z => ‖globalGradient P
        (uniformOutput (K := K)
          (heterogeneousOnlineCorrectedProofExactProcess
            (b := chosenBatch ε) (b0 := b0) A hE x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw
          (heterogeneousOnlineProofExactPathLaw (A := A)) K) ∧
      (∫ z, ‖globalGradient P
        (uniformOutput (K := K)
          (heterogeneousOnlineCorrectedProofExactProcess
            (b := chosenBatch ε) (b0 := b0) A hE x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (heterogeneousOnlineProofExactPathLaw (A := A)) K) ≤
        2 * Δ / (A.stepSize * K.1) +
          heterogeneousOnlineVarianceTerm σ (chosenBatch ε)) ∧
    ∃ K : Accuracy → Count,
      (∀ ε, NonconvexAccuracy (K ε) P
        (heterogeneousOnlineCorrectedProofExactProcess
          (b := chosenBatch ε) (b0 := b0) A hE x0)
        (heterogeneousOnlineProofExactPathLaw (A := A)) ε) ∧
      AccuracyIterationBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) ∧
      (∀ i, AccuracyBigO
        (fun ε => heterogeneousOnlineOracleCallCount (chosenBatch ε) b0 (K ε)
          A.refreshProbability i)
        (fun ε => (chosenBatch ε i).1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * (chosenBatch ε i).1 +
            (1 - A.refreshProbability) * (b0 i).1))) ∧
      AccuracyBigO
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  dsimp
  have hChosenBatch : ∀ ε i,
      (b0 i).1 <
        (heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 :=
    fun ε i => heterogeneousOnlineBatchScheduleFromBase_admissible
      σ b b0 hBatch ε i
  have hChosenFloor : ∀ ε,
      heterogeneousOnlineVarianceTerm σ
          (heterogeneousOnlineBatchScheduleFromBase σ b ε) ≤
        (ε : ℝ) ^ 2 / 2 :=
    heterogeneousOnlineBatchScheduleFromBase_variance_floor σ b
  have hChosenOrder : AccuracyTheta
      (fun ε => heterogeneousOnlineVarianceTerm σ
        (heterogeneousOnlineBatchScheduleFromBase σ b ε))
      (fun ε => (ε : ℝ) ^ 2) :=
    heterogeneousOnlineBatchScheduleFromBase_accuracyTheta σ b hBatchOrder
  let chosenBatch := heterogeneousOnlineBatchScheduleFromBase σ b
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal + Real.sqrt
    ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
  have hGapNonneg : 0 ≤ Δ := by
    dsimp [Δ, P]
    exact sub_nonneg.mpr (hLower x0)
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  constructor
  · intro ε K
    simpa [P, Δ, chosenBatch] using
      (Theorem_D3_heterogeneous_online_VR_nonconvex_corrected
        (b := chosenBatch ε) (b0 := b0) (K := K)
        A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
          hQuantizer (hAverageSmooth ε) hStep)
  · rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hΔzero : Δ = 0 := hGapZero.symm
      refine ⟨fun _ => K₁, ?_, ?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD3 :=
          Theorem_D3_heterogeneous_online_VR_nonconvex_corrected
            (b := chosenBatch ε) (b0 := b0) (K := K₁)
            A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
              hQuantizer (hAverageSmooth ε) hStep
        refine ⟨hD3.1, hD3.2.trans ?_⟩
        have hsum := hChosenFloor ε
        change 2 * Δ / (A.stepSize * K₁.1) +
            heterogeneousOnlineVarianceTerm σ (chosenBatch ε) ≤
          (ε : ℝ) ^ 2
        rw [hΔzero]
        simpa using hsum.trans (by
          nlinarith [sq_nonneg (ε : ℝ)])
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change Δ / (ε : ℝ) ^ 2 * bracket = 0
          rw [hΔzero]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · intro i
        unfold AccuracyBigO
        rw [Asymptotics.isBigO_iff]
        refine ⟨4, Filter.Eventually.of_forall ?_⟩
        intro ε
        let B : ℝ := (chosenBatch ε i).1
        let B0 : ℝ := (b0 i).1
        have hB : 0 < B := by
          dsimp [B]
          exact_mod_cast (chosenBatch ε i).2
        have hB0 : 0 < B0 := by
          dsimp [B0]
          exact_mod_cast (b0 i).2
        have hB0B : B0 < B := by
          dsimp [B0, B, chosenBatch]
          exact_mod_cast hChosenBatch ε i
        have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
        have hActualNonneg : 0 ≤
            B + (A.refreshProbability * B + 2 * (1 - A.refreshProbability) * B0) := by
          positivity
        have hB' : 0 <
            ((heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 : ℝ) := by
          simpa [B, chosenBatch] using hB
        have hB0' : 0 < ((b0 i).1 : ℝ) := by simpa [B0] using hB0
        have hB0B' : ((b0 i).1 : ℝ) <
            (heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 := by
          simpa [B0, B, chosenBatch] using hB0B
        have hActualNonneg' : 0 ≤
            ((heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 : ℝ) +
              (A.refreshProbability *
                  (heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 +
                2 * (1 - A.refreshProbability) * (b0 i).1) := by
          simpa [B, B0, chosenBatch] using hActualNonneg
        simp only [heterogeneousOnlineOracleCallCount, K₁, Nat.cast_one,
          one_mul]
        rw [show globalObjective
            (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar = 0 by
          simpa [Δ, P] using hΔzero]
        simp only [zero_div, zero_mul]
        simp only [add_zero]
        rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg',
          Real.norm_eq_abs, abs_of_pos hB']
        nlinarith [mul_nonneg hp.le hB'.le,
          mul_nonneg hOneSub hB0'.le]
      · unfold AccuracyBigO
        have hdne : (d.1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt d.2)
        have hGapRaw :
            globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
              fStar = 0 := by
          simpa [Δ, P] using hΔzero
        rw [show (fun ε : Accuracy => (d.1 : ℝ) +
            (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
              fStar) / (ε : ℝ) ^ 2 *
              (rootMeanSquare Llocal + Real.sqrt
                ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
                  (ω * rootMeanSquare Llocal ^ 2 +
                    (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))) *
              (A.refreshProbability * d.1 +
                (1 - A.refreshProbability) * ζ)) =
            (fun _ : Accuracy => (d.1 : ℝ)) by
              funext ε
              rw [hGapRaw]
              ring]
        simpa [allWorkerCommunicationCount, K₁, ζ] using
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) + (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))
            hdne accuracyToZero)
    · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
      · let K₁ : Count := ⟨1, by norm_num⟩
        have hBracketEq : bracket = 0 := hBracketZero.symm
        have hLzero : rootMeanSquare Llocal = 0 := by
          have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
          have hsqrt : 0 ≤ Real.sqrt
              ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
                (ω * rootMeanSquare Llocal ^ 2 +
                  (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)) :=
            Real.sqrt_nonneg _
          dsimp [bracket] at hBracketEq
          nlinarith
        have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
          P Llocal fStar hLower hSmooth hLzero
        refine ⟨fun _ => K₁, ?_, ?_, ?_, ?_⟩
        · intro ε
          unfold NonconvexAccuracy
          have hD3 :=
            Theorem_D3_heterogeneous_online_VR_nonconvex_corrected
              (b := chosenBatch ε) (b0 := b0) (K := K₁)
              A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
                hQuantizer (hAverageSmooth ε) hStep
          refine ⟨hD3.1, ?_⟩
          have heq : (fun z => ‖globalGradient P
              (uniformOutput (K := K₁)
                (heterogeneousOnlineCorrectedProofExactProcess
                  (b := chosenBatch ε) (b0 := b0) A hE x0) z)‖ ^ 2) =
              (fun _ => (0 : ℝ)) := by
            funext z
            rw [hGradZero]
            norm_num
          rw [heq, integral_zero]
          positivity
        · refine Or.inl ⟨?_, ?_⟩
          · intro ε
            change Δ / (ε : ℝ) ^ 2 * bracket = 0
            rw [hBracketEq]
            ring
          · unfold AccuracyBigO
            simpa [K₁] using
              (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
                accuracyToZero)
        · intro i
          unfold AccuracyBigO
          rw [Asymptotics.isBigO_iff]
          refine ⟨4, Filter.Eventually.of_forall ?_⟩
          intro ε
          let B : ℝ := (chosenBatch ε i).1
          let B0 : ℝ := (b0 i).1
          have hB : 0 < B := by
            dsimp [B]
            exact_mod_cast (chosenBatch ε i).2
          have hB0 : 0 < B0 := by
            dsimp [B0]
            exact_mod_cast (b0 i).2
          have hB0B : B0 < B := by
            dsimp [B0, B, chosenBatch]
            exact_mod_cast hChosenBatch ε i
          have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
          have hActualNonneg : 0 ≤
              B + (A.refreshProbability * B +
                2 * (1 - A.refreshProbability) * B0) := by
            positivity
          have hB' : 0 <
              ((heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 : ℝ) := by
            simpa [B, chosenBatch] using hB
          have hB0' : 0 < ((b0 i).1 : ℝ) := by simpa [B0] using hB0
          have hActualNonneg' : 0 ≤
              ((heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 : ℝ) +
                (A.refreshProbability *
                    (heterogeneousOnlineBatchScheduleFromBase σ b ε i).1 +
                  2 * (1 - A.refreshProbability) * (b0 i).1) := by
            simpa [B, B0, chosenBatch] using hActualNonneg
          simp only [heterogeneousOnlineOracleCallCount, K₁, Nat.cast_one,
            one_mul]
          rw [show rootMeanSquare Llocal + Real.sqrt
              ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
                (ω * rootMeanSquare Llocal ^ 2 +
                  (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)) = 0 by
            simpa [bracket] using hBracketEq]
          simp only [mul_zero, zero_mul, add_zero]
          rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg',
            Real.norm_eq_abs, abs_of_pos hB']
          nlinarith [mul_nonneg hp.le hB'.le,
            mul_nonneg hOneSub hB0'.le]
        · unfold AccuracyBigO
          have hdne : (d.1 : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt d.2)
          have hBracketRaw : rootMeanSquare Llocal + Real.sqrt
              ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
                (ω * rootMeanSquare Llocal ^ 2 +
                  (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)) = 0 := by
            simpa [bracket] using hBracketEq
          rw [show (fun ε : Accuracy => (d.1 : ℝ) +
              (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
                fStar) / (ε : ℝ) ^ 2 *
                (rootMeanSquare Llocal + Real.sqrt
                  ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
                    (ω * rootMeanSquare Llocal ^ 2 +
                      (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))) *
                (A.refreshProbability * d.1 +
                  (1 - A.refreshProbability) * ζ)) =
              (fun _ : Accuracy => (d.1 : ℝ)) by
                funext ε
                rw [hBracketRaw]
                ring]
          simpa [allWorkerCommunicationCount, K₁, ζ] using
            (Asymptotics.isBigO_const_const
              ((d.1 : ℝ) + (A.refreshProbability * d.1 +
                (1 - A.refreshProbability) * expectedDensity A.quantizer))
              hdne accuracyToZero)
      · let K : Accuracy → Count := fun ε =>
          ⟨max 1 (Nat.ceil (2 * Δ /
            (((A.stepSize : ℝ) / 2) * (ε : ℝ) ^ 2))), by omega⟩
        have hHalfStep : 0 < (A.stepSize : ℝ) / 2 :=
          div_pos A.stepSize.property (by norm_num)
        have hScalar := positive_inverse_square_ceiling_schedule
          Δ ((A.stepSize : ℝ) / 2) bracket hGapPos hHalfStep hBracketPos
        have hKHalfBound : ∀ ε : Accuracy,
            2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
              (ε : ℝ) ^ 2 / 2 := by
          intro ε
          have h := mul_le_mul_of_nonneg_left (hScalar.1 ε)
            (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          have hKpos : 0 < ((K ε).1 : ℝ) := by
            exact_mod_cast (K ε).2
          have h' : (1 / 2 : ℝ) *
              (2 * Δ / (((A.stepSize : ℝ) / 2) * ((K ε).1 : ℝ))) ≤
                (1 / 2 : ℝ) * (ε : ℝ) ^ 2 := by
            simpa [K] using h
          calc
            2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) =
                (1 / 2 : ℝ) *
                  (2 * Δ / (((A.stepSize : ℝ) / 2) * ((K ε).1 : ℝ))) := by
                    field_simp [ne_of_gt A.stepSize.property, ne_of_gt hKpos]
                    <;> ring
            _ ≤ (1 / 2 : ℝ) * (ε : ℝ) ^ 2 := h'
            _ = (ε : ℝ) ^ 2 / 2 := by ring
        have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
            (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
          simpa [K] using hScalar.2
        have hScaleNonneg : ∀ᶠ ε : Accuracy in accuracyToZero,
            0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by
          filter_upwards [] with ε
          positivity
        refine ⟨K, ?_, Or.inr hKBigO, ?_, ?_⟩
        · intro ε
          unfold NonconvexAccuracy
          have hD3 :=
            Theorem_D3_heterogeneous_online_VR_nonconvex_corrected
              (b := chosenBatch ε) (b0 := b0) (K := K ε)
              A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
                hQuantizer (hAverageSmooth ε) hStep
          refine ⟨hD3.1, hD3.2.trans ?_⟩
          have hsum := add_le_add (hKHalfBound ε) (hChosenFloor ε)
          simpa [Δ] using hsum
        · intro i
          unfold AccuracyBigO at hKBigO ⊢
          rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
          rw [Asymptotics.isBigO_iff']
          refine ⟨1 + 2 * C, by positivity, ?_⟩
          filter_upwards [hKC.bound] with ε hKc
          let scale : ℝ := Δ / (ε : ℝ) ^ 2 * bracket
          let B : ℝ := (chosenBatch ε i).1
          let B0 : ℝ := (b0 i).1
          let payload : ℝ := A.refreshProbability * B +
            2 * (1 - A.refreshProbability) * B0
          let target : ℝ := A.refreshProbability * B +
            (1 - A.refreshProbability) * B0
          have hB : 0 < B := by
            dsimp [B]
            exact_mod_cast (chosenBatch ε i).2
          have hB0 : 0 < B0 := by
            dsimp [B0]
            exact_mod_cast (b0 i).2
          have hscale : 0 < scale := by
            dsimp [scale]
            exact mul_pos (div_pos hGapPos (sq_pos_of_pos ε.property))
              hBracketPos
          have htarget : 0 < target := by
            dsimp [target]
            exact add_pos_of_pos_of_nonneg (mul_pos hp hB)
              (mul_nonneg (sub_nonneg.mpr hp1) hB0.le)
          have hpayload : 0 ≤ payload := by
            dsimp [payload]
            exact add_nonneg (mul_nonneg hp.le hB.le)
              (mul_nonneg
                (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1)) hB0.le)
          have hPayloadComparison : payload ≤ 2 * target := by
            dsimp [payload, target]
            have htail : 0 ≤ (1 - A.refreshProbability) * B0 :=
              mul_nonneg (sub_nonneg.mpr hp1) hB0.le
            have hhead : 0 ≤ A.refreshProbability * B := mul_nonneg hp.le hB.le
            nlinarith
          have hKn : ((K ε).1 : ℝ) ≤ C * scale := by
            change ‖((K ε).1 : ℝ)‖ ≤ C * ‖scale‖ at hKc
            simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
              0 ≤ ((K ε).1 : ℝ)), abs_of_pos hscale] using hKc
          have hround : ((K ε).1 : ℝ) * payload ≤
              2 * C * (scale * target) := by
            calc
              ((K ε).1 : ℝ) * payload ≤ (C * scale) * payload :=
                mul_le_mul_of_nonneg_right hKn hpayload
              _ ≤ (C * scale) * (2 * target) :=
                mul_le_mul_of_nonneg_left hPayloadComparison (by positivity)
              _ = 2 * C * (scale * target) := by ring
          change ‖B + ((K ε).1 : ℝ) * payload‖ ≤
            (1 + 2 * C) * ‖B + scale * target‖
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
              0 ≤ B + ((K ε).1 : ℝ) * payload),
            Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hB
              (mul_nonneg hscale.le htarget.le))]
          nlinarith
        · let commPayload : ℝ := A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ
          have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
          have hCommPayloadPos : 0 < commPayload := by
            dsimp [commPayload]
            exact add_pos_of_pos_of_nonneg
              (mul_pos hp hdpos)
              (mul_nonneg (sub_nonneg.mpr hp1) hζ)
          have hComm := accuracyBigO_affine_cost_of_schedule
            (K := fun ε => ((K ε).1 : ℝ))
            (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
            (init := (d.1 : ℝ))
            (actualPayload := commPayload)
            (targetPayload := commPayload)
            (payloadFactor := 1)
            hKBigO hdpos hCommPayloadPos.le hCommPayloadPos
              zero_lt_one (by simp) hScaleNonneg
          change AccuracyBigO
            (fun ε => (d.1 : ℝ) + ((K ε).1 : ℝ) * commPayload)
            (fun ε => (d.1 : ℝ) +
              (Δ / (ε : ℝ) ^ 2 * bracket) * commPayload)
          exact hComm

end MARINA
