import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Martingale
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Telescope
import Algorithms.Unverified.TimeVaryingPushPull.Part002
import Algorithms.Unverified.TimeVaryingPushPull.Part003.Part003

/-!
# Time-varying push-pull: object layer

This file records the canonical objects from the time-varying push-pull paper:
the finite-average objective, the sampled gradient table `G_t`, the one-step
push-pull recursion, and the generated iterate process. The recurrence is not a
field of `Setup`; it is a definition built from the paper data and a noise
sample path.
-/

open scoped BigOperators
open scoped Gradient
open scoped InnerProductSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open scoped ComplexConjugate

open MeasureTheory
open ProbabilityTheory
open Filter

namespace Algorithms.Unverified.TimeVaryingPushPull

universe uΩ

variable {Node E : Type*}
variable [Fintype Node] [Nonempty Node]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

namespace Setup

variable (setup : Setup Node E)

/-- Appendix C.1 initial-boundary input comparison at the source bridge
interface.

The initial restricted boundary coordinate is deterministic and independent of
`alpha`; therefore the only alpha-dependence in the projected stable input is
the Riesz projection `P(alpha)`.  Local Lipschitz control of `P` gives the
required alpha-small comparison with the alpha-zero cancelling input. -/
theorem quadraticRestrictedStableComplement_initial_input_alpha_absolute_bound
    (quad : Setup Node ℝ) (i0 : Node)
    (alpha0 deltaP LP : ℝ)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (halpha0_pos : 0 < alpha0)
    (hdeltaP_pos : 0 < deltaP)
    (hLP_nonneg : 0 ≤ LP)
    (hP_lip :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ deltaP →
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixSub
              (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha) (P 0)) ≤
          LP * alpha) :
    ∃ Cinit alphaInit : ℝ,
      0 ≤ Cinit ∧ 0 < alphaInit ∧ alphaInit ≤ alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInit →
          ∀ noise : NoisePath Node ℝ,
            let zα : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState noise 0,
                    (quad.withStepsize alpha).trackerErrorZeroSum noise 0))
            let zbase : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize 0).primalState noise 0,
                    (quad.withStepsize 0).trackerErrorZeroSum noise 0))
            rowEuclideanNorm
              (Node := Sum Node {i : Node // i ≠ i0})
              (fun a => zα a - zbase a) ≤ Cinit * alpha := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let zinit : RowVector Idx := fun a =>
    match a with
    | Sum.inl _ => quad.x0
    | Sum.inr _ => 0
  let Cinit : ℝ := LP * rowEuclideanNorm (Node := Idx) zinit
  let alphaInit : ℝ := min alpha0 deltaP
  have halphaInit_pos : 0 < alphaInit := by
    dsimp [alphaInit]
    exact lt_min halpha0_pos hdeltaP_pos
  have halphaInit_le_alpha0 : alphaInit ≤ alpha0 := by
    dsimp [alphaInit]
    exact min_le_left _ _
  have halphaInit_le_deltaP : alphaInit ≤ deltaP := by
    dsimp [alphaInit]
    exact min_le_right _ _
  have hCinit_nonneg : 0 ≤ Cinit := by
    dsimp [Cinit]
    exact mul_nonneg hLP_nonneg
      (by
        simpa [rowEuclideanNorm] using
          Real.sqrt_nonneg (rowNormSq (Node := Idx) zinit))
  refine ⟨Cinit, alphaInit, hCinit_nonneg, halphaInit_pos,
    halphaInit_le_alpha0, ?_⟩
  intro alpha halpha_pos halpha_le noise
  have halpha_le_deltaP : alpha ≤ deltaP :=
    le_trans halpha_le halphaInit_le_deltaP
  have hsub_op :
      matrixEuclideanOperatorNorm (Node := Idx)
          (matrixSub (Node := Idx) (P 0) (P alpha)) ≤
        LP * alpha :=
    matrixEuclideanOperatorNorm_matrixSub_comm_le
      (Node := Idx) (P alpha) (P 0)
      (hP_lip alpha halpha_pos.le halpha_le_deltaP)
  let zα : RowVector Idx :=
    spectralStableComplementVector (Node := Idx) (P alpha)
      (restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize alpha).primalState noise 0,
          (quad.withStepsize alpha).trackerErrorZeroSum noise 0))
  let zbase : RowVector Idx :=
    spectralStableComplementVector (Node := Idx) (P 0)
      (restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize 0).primalState noise 0,
          (quad.withStepsize 0).trackerErrorZeroSum noise 0))
  have hzalpha_const :
      restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize alpha).primalState noise 0,
          (quad.withStepsize alpha).trackerErrorZeroSum noise 0) =
        zinit := by
    funext a
    cases a with
    | inl i =>
        simp [zinit, restrictedStateToCoord, withStepsize, primalState_zero,
          initialPrimal]
    | inr j =>
        simp [zinit, restrictedStateToCoord, withStepsize,
          trackerErrorZeroSum, trackerError, trackerState_zero, oracleTable]
  have hzbase_const :
      restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize 0).primalState noise 0,
          (quad.withStepsize 0).trackerErrorZeroSum noise 0) =
        zinit := by
    funext a
    cases a with
    | inl i =>
        simp [zinit, restrictedStateToCoord, withStepsize, primalState_zero,
          initialPrimal]
    | inr j =>
        simp [zinit, restrictedStateToCoord, withStepsize,
          trackerErrorZeroSum, trackerError, trackerState_zero, oracleTable]
  have hdiff_eq :
      (fun a : Idx => zα a - zbase a) =
        matrixMulVector (Node := Idx)
          (matrixSub (Node := Idx) (P 0) (P alpha)) zinit := by
    funext a
    simp only [zα, zbase, spectralStableComplementVector, hzalpha_const,
      hzbase_const, Pi.sub_apply, matrixMulVector, matrixSub, sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  calc
    rowEuclideanNorm (Node := Idx) (fun a => zα a - zbase a) =
        rowEuclideanNorm (Node := Idx)
          (matrixMulVector (Node := Idx)
            (matrixSub (Node := Idx) (P 0) (P alpha)) zinit) := by
          rw [hdiff_eq]
    _ ≤ matrixEuclideanOperatorNorm (Node := Idx)
          (matrixSub (Node := Idx) (P 0) (P alpha)) *
        rowEuclideanNorm (Node := Idx) zinit :=
          rowEuclideanNorm_matrixMulVector_le
            (Node := Idx) (matrixSub (Node := Idx) (P 0) (P alpha)) zinit
    _ ≤ (LP * alpha) * rowEuclideanNorm (Node := Idx) zinit :=
          mul_le_mul_of_nonneg_right hsub_op
            (by
              simpa [rowEuclideanNorm] using
                Real.sqrt_nonneg (rowNormSq (Node := Idx) zinit))
    _ = Cinit * alpha := by
          dsimp [Cinit]
          ring

/-- Appendix C.1 raw finite-window noise envelope for one period.

The PDF states the stable noise output bound against
`sum_{j<t} ||epsilon_j||`.  At period boundaries this is the corresponding
single-period source envelope. -/
noncomputable def quadraticRestrictedPeriodNoiseWindowEnvelope
    (quad : Setup Node ℝ) (noise : NoisePath Node ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range quad.period) (fun r =>
    rowEuclideanNorm (Node := Node) (noise (k * quad.period + r)))

theorem quadraticRestrictedPeriodNoiseWindowEnvelope_nonneg
    (quad : Setup Node ℝ) (noise : NoisePath Node ℝ) (k : ℕ) :
    0 ≤ quadraticRestrictedPeriodNoiseWindowEnvelope
      (Node := Node) quad noise k := by
  classical
  unfold quadraticRestrictedPeriodNoiseWindowEnvelope
  exact Finset.sum_nonneg fun r _hr => by
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg (rowNormSq (Node := Node)
        (noise (k * quad.period + r)))

/-- One term in the source period-window envelope is bounded by the whole
window envelope. -/
theorem quadraticRestrictedPeriodNoiseWindowEnvelope_single_le
    (quad : Setup Node ℝ) (noise : NoisePath Node ℝ) (k r : ℕ)
    (hr : r < quad.period) :
    rowEuclideanNorm (Node := Node) (noise (k * quad.period + r)) ≤
      quadraticRestrictedPeriodNoiseWindowEnvelope
        (Node := Node) quad noise k := by
  classical
  have hsingle :
      rowEuclideanNorm (Node := Node) (noise (k * quad.period + r)) ≤
        ∑ s ∈ Finset.range quad.period,
          rowEuclideanNorm (Node := Node) (noise (k * quad.period + s)) :=
    Finset.single_le_sum
      (s := Finset.range quad.period)
      (a := r)
      (f := fun s =>
        rowEuclideanNorm (Node := Node) (noise (k * quad.period + s)))
      (fun s _hs => by
        simpa [rowEuclideanNorm] using
          Real.sqrt_nonneg (rowNormSq (Node := Node)
            (noise (k * quad.period + s))))
      (Finset.mem_range.mpr hr)
  simpa [quadraticRestrictedPeriodNoiseWindowEnvelope] using hsingle

/-- Exact iid second moment of one raw node-noise row.

This is the stochastic primitive behind the Appendix C.1 source envelope:
the Euclidean row norm squares to the finite sum of node-coordinate squares,
and the exact iid oracle law gives variance `sigma^2` at every coordinate. -/
theorem noiseRowEuclideanNorm_sq_integral_eq
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (t : ℕ) :
    (∫ ω,
      rowEuclideanNorm (Node := Node) (oracle.noise ω t) ^ 2 ∂μ) =
      (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 := by
  classical
  have hexact_var := hnoise.2.2.2.2.2
  rw [show
      (fun ω : Ω =>
        rowEuclideanNorm (Node := Node) (oracle.noise ω t) ^ 2) =
      (fun ω : Ω => rowNormSq (Node := Node) (oracle.noise ω t)) by
        funext ω
        exact rowEuclideanNorm_sq_eq_rowNormSq
          (Node := Node) (oracle.noise ω t)]
  unfold rowNormSq
  rw [MeasureTheory.integral_finset_sum]
  · have hcoord :
        ∀ i : Node,
          (∫ ω, oracle.noise ω t i ^ 2 ∂μ) = quad.sigma ^ 2 := by
        intro i
        simpa [Real.norm_eq_abs, sq_abs] using hexact_var t i
    calc
      Finset.sum Finset.univ
          (fun i : Node => ∫ ω, oracle.noise ω t i ^ 2 ∂μ) =
          Finset.sum Finset.univ (fun _i : Node => quad.sigma ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hcoord i
      _ = (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 := by
            simp [nodeCount, Finset.sum_const, Finset.card_univ]
  · intro i _hi
    have hmem :
        MemLp (fun ω : Ω => oracle.noise ω t i) 2 μ :=
      quad.nodeNoise_memLp_two μ oracle hnoise.1 t i
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm
        hmem.aestronglyMeasurable).1 hmem

/-- Uniform second-moment bound for the raw one-period noise-window envelope.

This is the stochastic half of Appendix C.1 step 5 for the source-shaped
stable impulse route.  It does not mention the stable projection or any
retired response-relative helper; it is just Cauchy--Schwarz over the finite
period window plus the exact iid row-noise variance. -/
theorem quadraticRestrictedPeriodNoiseWindowEnvelope_secondMoment_bound
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ Cwin : ℝ, 0 ≤ Cwin ∧
      ∀ k : ℕ,
        (∫ ω,
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤ Cwin := by
  classical
  let Crow : ℝ := (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2
  let Cwin : ℝ := (quad.period : ℝ) * ((quad.period : ℝ) * Crow)
  have hCrow_nonneg : 0 ≤ Crow := by
    dsimp [Crow]
    positivity
  have hCwin_nonneg : 0 ≤ Cwin := by
    dsimp [Cwin]
    positivity
  refine ⟨Cwin, hCwin_nonneg, ?_⟩
  intro k
  have hrow_int :
      ∀ r : ℕ,
        Integrable
          (fun ω : Ω =>
            rowEuclideanNorm (Node := Node)
              (oracle.noise ω (k * quad.period + r)) ^ 2) μ := by
    intro r
    exact
      rowEuclideanNorm_sq_integrable_of_coordinate_memLp
        (Node := Node)
        (fun i =>
          quad.nodeNoise_memLp_two μ oracle hnoise.1
            (k * quad.period + r) i)
  have hright_int :
      Integrable
        (fun ω : Ω =>
          (quad.period : ℝ) *
            Finset.sum (Finset.range quad.period) (fun r =>
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2)) μ := by
    exact
      (integrable_finset_sum (Finset.range quad.period)
        (fun r _hr => hrow_int r)).const_mul (quad.period : ℝ)
  have hleft_nonneg :
      0 ≤ᵐ[μ]
        (fun ω : Ω =>
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2) :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hpointwise :
      (fun ω : Ω =>
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2) ≤ᵐ[μ]
        (fun ω : Ω =>
          (quad.period : ℝ) *
            Finset.sum (Finset.range quad.period) (fun r =>
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [quadraticRestrictedPeriodNoiseWindowEnvelope] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range quad.period)
        (f := fun r : ℕ =>
          rowEuclideanNorm (Node := Node)
            (oracle.noise ω (k * quad.period + r))))
  have hmono :
      (∫ ω,
        quadraticRestrictedPeriodNoiseWindowEnvelope
          (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤
        ∫ ω,
          (quad.period : ℝ) *
            Finset.sum (Finset.range quad.period) (fun r =>
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2) ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hleft_nonneg hright_int hpointwise
  have hsum_bound :
      Finset.sum (Finset.range quad.period) (fun r =>
          ∫ ω,
            rowEuclideanNorm (Node := Node)
              (oracle.noise ω (k * quad.period + r)) ^ 2 ∂μ) ≤
        (quad.period : ℝ) * Crow := by
    have hsum_eq :
        Finset.sum (Finset.range quad.period) (fun r =>
            ∫ ω,
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2 ∂μ) =
          (quad.period : ℝ) * Crow := by
      calc
        Finset.sum (Finset.range quad.period) (fun r =>
            ∫ ω,
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2 ∂μ) =
            Finset.sum (Finset.range quad.period) (fun _r => Crow) := by
              apply Finset.sum_congr rfl
              intro r _hr
              simpa [Crow] using
                noiseRowEuclideanNorm_sq_integral_eq
                  (Node := Node) quad μ oracle hnoise
                  (k * quad.period + r)
        _ = (quad.period : ℝ) * Crow := by
              simp [Finset.sum_const, Nat.cast_mul]
    exact le_of_eq hsum_eq
  calc
    (∫ ω,
      quadraticRestrictedPeriodNoiseWindowEnvelope
        (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤
        ∫ ω,
          (quad.period : ℝ) *
            Finset.sum (Finset.range quad.period) (fun r =>
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2) ∂μ := hmono
    _ =
        (quad.period : ℝ) *
          Finset.sum (Finset.range quad.period) (fun r =>
            ∫ ω,
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2 ∂μ) := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_finset_sum]
          exact fun r _hr => hrow_int r
    _ ≤ (quad.period : ℝ) * ((quad.period : ℝ) * Crow) :=
          mul_le_mul_of_nonneg_left hsum_bound (Nat.cast_nonneg _)
    _ = Cwin := by rfl

/-- The raw one-period noise-window envelope has an integrable square at each
fixed period block. -/
theorem quadraticRestrictedPeriodNoiseWindowEnvelope_sq_integrable
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (k : ℕ) :
    Integrable
      (fun ω =>
        quadraticRestrictedPeriodNoiseWindowEnvelope
          (Node := Node) quad (oracle.noise ω) k ^ 2) μ := by
  classical
  have hrow_int :
      ∀ r : ℕ,
        Integrable
          (fun ω : Ω =>
            rowEuclideanNorm (Node := Node)
              (oracle.noise ω (k * quad.period + r)) ^ 2) μ := by
    intro r
    exact
      rowEuclideanNorm_sq_integrable_of_coordinate_memLp
        (Node := Node)
        (fun i =>
          quad.nodeNoise_memLp_two μ oracle hnoise.1
            (k * quad.period + r) i)
  have hrow_aesm :
      ∀ r : ℕ,
        AEStronglyMeasurable
          (fun ω : Ω =>
            rowEuclideanNorm (Node := Node)
              (oracle.noise ω (k * quad.period + r))) μ := by
    intro r
    exact
      AEStronglyMeasurable.of_integrable_sq_of_nonneg
        (hrow_int r)
        (Filter.Eventually.of_forall fun ω => by
          simpa [rowEuclideanNorm] using
            Real.sqrt_nonneg
              (rowNormSq (Node := Node)
                (oracle.noise ω (k * quad.period + r))))
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω : Ω =>
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2) μ := by
    have henv_aesm :
        AEStronglyMeasurable
          (fun ω : Ω =>
            quadraticRestrictedPeriodNoiseWindowEnvelope
              (Node := Node) quad (oracle.noise ω) k) μ := by
      unfold quadraticRestrictedPeriodNoiseWindowEnvelope
      exact
        Finset.aestronglyMeasurable_fun_sum
          (Finset.range quad.period)
          (fun r _hr => hrow_aesm r)
    exact henv_aesm.pow 2
  have hright_int :
      Integrable
        (fun ω : Ω =>
          (quad.period : ℝ) *
            Finset.sum (Finset.range quad.period) (fun r =>
              rowEuclideanNorm (Node := Node)
                (oracle.noise ω (k * quad.period + r)) ^ 2)) μ := by
    exact
      (integrable_finset_sum (Finset.range quad.period)
        (fun r _hr => hrow_int r)).const_mul (quad.period : ℝ)
  refine Integrable.mono' hright_int hleft_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hpointwise :
      quadraticRestrictedPeriodNoiseWindowEnvelope
          (Node := Node) quad (oracle.noise ω) k ^ 2 ≤
        (quad.period : ℝ) *
          Finset.sum (Finset.range quad.period) (fun r =>
            rowEuclideanNorm (Node := Node)
              (oracle.noise ω (k * quad.period + r)) ^ 2) := by
    simpa [quadraticRestrictedPeriodNoiseWindowEnvelope] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range quad.period)
        (f := fun r : ℕ =>
          rowEuclideanNorm (Node := Node)
            (oracle.noise ω (k * quad.period + r))))
  have hright_nonneg :
      0 ≤
        (quad.period : ℝ) *
          Finset.sum (Finset.range quad.period) (fun r =>
            rowEuclideanNorm (Node := Node)
              (oracle.noise ω (k * quad.period + r)) ^ 2) := by
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun r _hr => sq_nonneg _)
  change
    |quadraticRestrictedPeriodNoiseWindowEnvelope
        (Node := Node) quad (oracle.noise ω) k ^ 2| ≤
      (quad.period : ℝ) *
        Finset.sum (Finset.range quad.period) (fun r =>
          rowEuclideanNorm (Node := Node)
            (oracle.noise ω (k * quad.period + r)) ^ 2)
  rw [abs_of_nonneg (sq_nonneg
    (quadraticRestrictedPeriodNoiseWindowEnvelope
      (Node := Node) quad (oracle.noise ω) k))]
  exact hpointwise

/-- Scalar square-geometric summation for the source stable-output impulse
envelope.

This is the deterministic half of Appendix C.1 step 5: once the stable output
is bounded by `alpha` times this impulse envelope, the squared envelope has a
finite-horizon budget consisting of a deterministic initial contribution plus
the finite sum of squared period-window inputs. -/
theorem geometric_impulse_envelope_square_sum_bound
    {theta A : ℝ}
    (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hA_nonneg : 0 ≤ A)
    (window : ℕ → ℝ) (hwindow_nonneg : ∀ k : ℕ, 0 ≤ window k)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
        (theta ^ t * A +
          Finset.sum (Finset.range t) (fun j =>
            theta ^ (t - 1 - j) * window j)) ^ 2) ≤
      (2 / (1 - theta ^ 2)) * A ^ 2 +
        (2 / (1 - theta) ^ 2) *
          Finset.sum (Finset.range N) (fun j => window j ^ 2) := by
  classical
  let u : ℕ → ℝ := fun t =>
    theta ^ t * A +
      Finset.sum (Finset.range t) (fun j =>
        theta ^ (t - 1 - j) * window j)
  let z : ℕ → ℝ := window
  have htheta_nonneg : 0 ≤ theta := htheta_pos.le
  have hu_nonneg : ∀ t : ℕ, 0 ≤ u t := by
    intro t
    dsimp [u]
    exact add_nonneg
      (mul_nonneg (pow_nonneg htheta_nonneg t) hA_nonneg)
      (Finset.sum_nonneg fun j _hj =>
        mul_nonneg (pow_nonneg htheta_nonneg (t - 1 - j))
          (hwindow_nonneg j))
  have hz_nonneg : ∀ t : ℕ, 0 ≤ z t := by
    intro t
    exact hwindow_nonneg t
  have hrec :
      ∀ t : ℕ,
        u t ≤ 1 * theta ^ t * u 0 +
          Finset.sum (Finset.range t) (fun j =>
            1 * theta ^ (t - 1 - j) * z j) := by
    intro t
    dsimp [u, z]
    simp
  have hconv :=
    SquareSummableGeometricConvolution
      (u := u) (z := z) (M := 1) (r := theta)
      hu_nonneg hz_nonneg (by norm_num) htheta_pos htheta_lt_one
      hrec N
  simpa [u, z, pow_two] using hconv

/-- Pointwise squared stable-output budget from a geometric impulse envelope.

This is the non-stochastic part of Appendix C.1 step 5 after the impulse
estimate has already been proved: square the `O(alpha)` envelope and sum it
over the finite horizon. -/
theorem stable_output_square_sum_bound_of_geometric_impulse
    {C theta A alpha : ℝ}
    (hC_nonneg : 0 ≤ C) (halpha_nonneg : 0 ≤ alpha)
    (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hA_nonneg : 0 ≤ A)
    (window : ℕ → ℝ) (hwindow_nonneg : ∀ k : ℕ, 0 ≤ window k)
    (out : ℕ → ℝ)
    (hout :
      ∀ t : ℕ,
        |out t| ≤
          C * alpha *
            (theta ^ t * A +
              Finset.sum (Finset.range t) (fun j =>
                theta ^ (t - 1 - j) * window j)))
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t => |out t| ^ 2) ≤
      (C ^ 2 * alpha ^ 2) *
        ((2 / (1 - theta ^ 2)) * A ^ 2 +
          (2 / (1 - theta) ^ 2) *
            Finset.sum (Finset.range N) (fun j => window j ^ 2)) := by
  classical
  let env : ℕ → ℝ := fun t =>
    theta ^ t * A +
      Finset.sum (Finset.range t) (fun j =>
        theta ^ (t - 1 - j) * window j)
  have htheta_nonneg : 0 ≤ theta := htheta_pos.le
  have henv_nonneg : ∀ t : ℕ, 0 ≤ env t := by
    intro t
    dsimp [env]
    exact add_nonneg
      (mul_nonneg (pow_nonneg htheta_nonneg t) hA_nonneg)
      (Finset.sum_nonneg fun j _hj =>
        mul_nonneg (pow_nonneg htheta_nonneg (t - 1 - j))
          (hwindow_nonneg j))
  have hcoef_nonneg : 0 ≤ C ^ 2 * alpha ^ 2 :=
    mul_nonneg (sq_nonneg C) (sq_nonneg alpha)
  have hpoint :
      ∀ t ∈ Finset.range (N + 1),
        |out t| ^ 2 ≤ (C ^ 2 * alpha ^ 2) * env t ^ 2 := by
    intro t _ht
    have hscale_nonneg : 0 ≤ C * alpha :=
      mul_nonneg hC_nonneg halpha_nonneg
    have hrhs_nonneg : 0 ≤ C * alpha * env t :=
      mul_nonneg hscale_nonneg (henv_nonneg t)
    have hle : |out t| ≤ C * alpha * env t := by
      simpa [env] using hout t
    calc
      |out t| ^ 2 ≤ (C * alpha * env t) ^ 2 := by
        nlinarith [hle, abs_nonneg (out t), hrhs_nonneg]
      _ = (C ^ 2 * alpha ^ 2) * env t ^ 2 := by ring
  have hsum_env :=
    geometric_impulse_envelope_square_sum_bound
      (theta := theta) (A := A)
      htheta_pos htheta_lt_one hA_nonneg window hwindow_nonneg N
  calc
    Finset.sum (Finset.range (N + 1)) (fun t => |out t| ^ 2) ≤
        Finset.sum (Finset.range (N + 1)) (fun t =>
          (C ^ 2 * alpha ^ 2) * env t ^ 2) :=
          Finset.sum_le_sum hpoint
    _ = (C ^ 2 * alpha ^ 2) *
          Finset.sum (Finset.range (N + 1)) (fun t => env t ^ 2) := by
          rw [Finset.mul_sum]
    _ ≤
        (C ^ 2 * alpha ^ 2) *
          ((2 / (1 - theta ^ 2)) * A ^ 2 +
            (2 / (1 - theta) ^ 2) *
              Finset.sum (Finset.range N) (fun j => window j ^ 2)) :=
          mul_le_mul_of_nonneg_left (by simpa [env] using hsum_env)
            hcoef_nonneg

/-- Finite aggregation of a uniform period-window square-moment budget. -/
theorem quadraticRestrictedPeriodNoiseWindowEnvelope_integral_sum_le
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ)
    {Cwin : ℝ}
    (hwin_bound :
      ∀ k : ℕ,
        (∫ ω,
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤ Cwin)
    (T : ℕ) :
    Finset.sum (Finset.range T) (fun k =>
        ∫ ω,
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤
      (T : ℝ) * Cwin := by
  classical
  calc
    Finset.sum (Finset.range T) (fun k =>
        ∫ ω,
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤
        Finset.sum (Finset.range T) (fun _k : ℕ => Cwin) := by
          exact Finset.sum_le_sum fun k _hk => hwin_bound k
    _ = (T : ℝ) * Cwin := by
          simp [Finset.sum_const, Nat.cast_mul]

/-- Integrated finite-horizon version of the geometric impulse square budget.

This is the measure-theoretic lift used in Appendix C.1 step 5: once the
stable output is pointwise dominated by a square-geometric impulse envelope,
finite-sum integrability lets the deterministic square summation be integrated
and the raw period-window square moment substituted. -/
theorem stable_output_square_integral_sum_bound_of_geometric_impulse
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {C theta A alpha Cwin : ℝ}
    (hC_nonneg : 0 ≤ C) (halpha_nonneg : 0 ≤ alpha)
    (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hA_nonneg : 0 ≤ A) (hCwin_nonneg : 0 ≤ Cwin)
    (window : Ω → ℕ → ℝ)
    (hwindow_nonneg : ∀ ω k, 0 ≤ window ω k)
    (out : Ω → ℕ → ℝ)
    (hout :
      ∀ ω t,
        |out ω t| ≤
          C * alpha *
            (theta ^ t * A +
              Finset.sum (Finset.range t) (fun j =>
                theta ^ (t - 1 - j) * window ω j)))
    (hout_int : ∀ t : ℕ, Integrable (fun ω => |out ω t| ^ 2) μ)
    (hwindow_sq_int :
      ∀ k : ℕ, Integrable (fun ω => window ω k ^ 2) μ)
    (hwindow_sum_bound :
      ∀ N : ℕ,
        Finset.sum (Finset.range N) (fun k =>
          ∫ ω, window ω k ^ 2 ∂μ) ≤ (N : ℝ) * Cwin)
    (T : ℕ) (hT : 1 ≤ T) :
    Finset.sum (Finset.range T) (fun t =>
        ∫ ω, |out ω t| ^ 2 ∂μ) ≤
      (C ^ 2 * alpha ^ 2) *
        ((2 / (1 - theta ^ 2)) * A ^ 2 +
          (2 / (1 - theta) ^ 2) * ((T : ℝ) * Cwin)) := by
  classical
  let N : ℕ := T - 1
  have hT_pos_nat : 0 < T := Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hT_eq : N + 1 = T := by
    dsimp [N]
    exact Nat.succ_pred_eq_of_pos hT_pos_nat
  have hpoint :
      ∀ ω : Ω,
        Finset.sum (Finset.range T) (fun t => |out ω t| ^ 2) ≤
          (C ^ 2 * alpha ^ 2) *
            ((2 / (1 - theta ^ 2)) * A ^ 2 +
              (2 / (1 - theta) ^ 2) *
                Finset.sum (Finset.range N) (fun j => window ω j ^ 2)) := by
    intro ω
    have hsq :=
      stable_output_square_sum_bound_of_geometric_impulse
        (C := C) (theta := theta) (A := A) (alpha := alpha)
        hC_nonneg halpha_nonneg htheta_pos htheta_lt_one hA_nonneg
        (fun k => window ω k) (fun k => hwindow_nonneg ω k)
        (fun t => out ω t) (fun t => hout ω t) N
    simpa [hT_eq] using hsq
  have hleft_int :
      Integrable
        (fun ω : Ω =>
          Finset.sum (Finset.range T) (fun t => |out ω t| ^ 2)) μ := by
    exact integrable_finset_sum (Finset.range T)
      (fun t _ht => hout_int t)
  have hwindow_sum_int :
      Integrable
        (fun ω : Ω =>
          Finset.sum (Finset.range N) (fun j => window ω j ^ 2)) μ := by
    exact integrable_finset_sum (Finset.range N)
      (fun j _hj => hwindow_sq_int j)
  have hright_int :
      Integrable
        (fun ω : Ω =>
          (C ^ 2 * alpha ^ 2) *
            ((2 / (1 - theta ^ 2)) * A ^ 2 +
              (2 / (1 - theta) ^ 2) *
                Finset.sum (Finset.range N) (fun j => window ω j ^ 2))) μ := by
    exact
      ((integrable_const ((2 / (1 - theta ^ 2)) * A ^ 2)).add
        (hwindow_sum_int.const_mul (2 / (1 - theta) ^ 2))).const_mul
          (C ^ 2 * alpha ^ 2)
  have hmono :
      (∫ ω,
        Finset.sum (Finset.range T) (fun t => |out ω t| ^ 2) ∂μ) ≤
        ∫ ω,
          (C ^ 2 * alpha ^ 2) *
            ((2 / (1 - theta ^ 2)) * A ^ 2 +
              (2 / (1 - theta) ^ 2) *
                Finset.sum (Finset.range N) (fun j => window ω j ^ 2)) ∂μ := by
    exact MeasureTheory.integral_mono_ae hleft_int hright_int
      (Filter.Eventually.of_forall hpoint)
  have hcoef_nonneg : 0 ≤ 2 / (1 - theta) ^ 2 := by
    have hden_pos : 0 < (1 - theta) ^ 2 := by
      apply sq_pos_of_ne_zero
      linarith
    positivity
  have hwindow_N_le_T :
      Finset.sum (Finset.range N) (fun k =>
          ∫ ω, window ω k ^ 2 ∂μ) ≤ (T : ℝ) * Cwin := by
    have hN := hwindow_sum_bound N
    have hN_le_T : (N : ℝ) * Cwin ≤ (T : ℝ) * Cwin := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le T 1) hCwin_nonneg
    exact le_trans hN hN_le_T
  have hinside_le :
      (2 / (1 - theta ^ 2)) * A ^ 2 +
          (2 / (1 - theta) ^ 2) *
            Finset.sum (Finset.range N) (fun k =>
              ∫ ω, window ω k ^ 2 ∂μ) ≤
        (2 / (1 - theta ^ 2)) * A ^ 2 +
          (2 / (1 - theta) ^ 2) * ((T : ℝ) * Cwin) := by
    have hmul :
        (2 / (1 - theta) ^ 2) *
            Finset.sum (Finset.range N) (fun k =>
              ∫ ω, window ω k ^ 2 ∂μ) ≤
          (2 / (1 - theta) ^ 2) * ((T : ℝ) * Cwin) :=
      mul_le_mul_of_nonneg_left hwindow_N_le_T hcoef_nonneg
    exact add_le_add (le_refl ((2 / (1 - theta ^ 2)) * A ^ 2)) hmul
  calc
    Finset.sum (Finset.range T) (fun t =>
        ∫ ω, |out ω t| ^ 2 ∂μ) =
        ∫ ω, Finset.sum (Finset.range T) (fun t => |out ω t| ^ 2) ∂μ := by
          rw [MeasureTheory.integral_finset_sum]
          exact fun t _ht => hout_int t
    _ ≤ ∫ ω,
          (C ^ 2 * alpha ^ 2) *
            ((2 / (1 - theta ^ 2)) * A ^ 2 +
              (2 / (1 - theta) ^ 2) *
                Finset.sum (Finset.range N) (fun j => window ω j ^ 2)) ∂μ :=
          hmono
    _ =
        (C ^ 2 * alpha ^ 2) *
          ((2 / (1 - theta ^ 2)) * A ^ 2 +
            (2 / (1 - theta) ^ 2) *
              Finset.sum (Finset.range N) (fun j =>
                ∫ ω, window ω j ^ 2 ∂μ)) := by
          rw [MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const]
            rw [MeasureTheory.integral_const_mul]
            rw [MeasureTheory.integral_finset_sum]
            · simp
            · exact fun j _hj => hwindow_sq_int j
          · exact integrable_const _
          · exact hwindow_sum_int.const_mul (2 / (1 - theta) ^ 2)
    _ ≤
        (C ^ 2 * alpha ^ 2) *
          ((2 / (1 - theta ^ 2)) * A ^ 2 +
            (2 / (1 - theta) ^ 2) * ((T : ℝ) * Cwin)) := by
          exact mul_le_mul_of_nonneg_left hinside_le
            (mul_nonneg (sq_nonneg C) (sq_nonneg alpha))

/-- A linear scalar recursion with nonnegative coefficients has the expected
finite-window deterministic budget. -/
theorem scalar_ar_abs_convolution_bound
    {gamma r : ℝ} (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_r : gamma ≤ r) (hr_nonneg : 0 ≤ r)
    (err eta : ℕ → ℝ)
    (hrec : ∀ k : ℕ, err (k + 1) = gamma * err k + eta k) :
    ∀ t : ℕ,
      |err t| ≤
        r ^ t * |err 0| +
          Finset.sum (Finset.range t) fun j =>
            r ^ (t - 1 - j) * |eta j| := by
  classical
  intro t
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have hstep_abs :
          |err (t + 1)| ≤ gamma * |err t| + |eta t| := by
        rw [hrec t]
        calc
          |gamma * err t + eta t| ≤ |gamma * err t| + |eta t| :=
            abs_add_le _ _
          _ = gamma * |err t| + |eta t| := by
            rw [abs_mul, abs_of_nonneg hgamma_nonneg]
      have hgamma_to_r :
          gamma * |err t| ≤ r * |err t| :=
        mul_le_mul_of_nonneg_right hgamma_le_r (abs_nonneg _)
      have hsum_succ :
          (Finset.range (t + 1)).sum (fun j =>
              r ^ (t + 1 - 1 - j) * |eta j|) =
            r * (Finset.range t).sum (fun j =>
                r ^ (t - 1 - j) * |eta j|) + |eta t| := by
        have hprefix :
            (Finset.range t).sum (fun j =>
                r ^ (t + 1 - 1 - j) * |eta j|) =
              r * (Finset.range t).sum (fun j =>
                  r ^ (t - 1 - j) * |eta j|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hj_lt : j < t := Finset.mem_range.mp hj
          have hexp : t + 1 - 1 - j = (t - 1 - j) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [Finset.sum_range_succ, hprefix]
        simp
      calc
        |err (t + 1)| ≤ gamma * |err t| + |eta t| := hstep_abs
        _ ≤ r * |err t| + |eta t| :=
            add_le_add hgamma_to_r le_rfl
        _ ≤
            r * (r ^ t * |err 0| +
              (Finset.range t).sum (fun j =>
                r ^ (t - 1 - j) * |eta j|)) + |eta t| := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left ih hr_nonneg) le_rfl
        _ =
            r ^ (t + 1) * |err 0| +
              (Finset.range (t + 1)).sum (fun j =>
                r ^ (t + 1 - 1 - j) * |eta j|) := by
              rw [hsum_succ]
              ring

/-- Deterministic square-sum bound for a scalar AR error recursion.

This is the reusable Duhamel core of Appendix C.1 step 6.  A later stochastic
wrapper only has to integrate this bound and substitute the projected/scalar
block-input second-moment estimate. -/
theorem scalar_ar_difference_square_sum_bound_of_contract
    {gamma r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_r : gamma ≤ r)
    (err eta : ℕ → ℝ)
    (hrec : ∀ k : ℕ, err (k + 1) = gamma * err k + eta k)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t => |err t| ^ 2) ≤
      (2 / (1 - r ^ 2)) * |err 0| ^ 2 +
        (2 / (1 - r) ^ 2) *
          Finset.sum (Finset.range N) (fun j => |eta j| ^ 2) := by
  classical
  have hconv :
      ∀ t : ℕ,
        |err t| ≤
          1 * r ^ t * |err 0| +
            Finset.sum (Finset.range t) fun j =>
              1 * r ^ (t - 1 - j) * |eta j| := by
    intro t
    have hbase :=
      scalar_ar_abs_convolution_bound
        hgamma_nonneg hgamma_le_r hr_pos.le err eta hrec t
    simpa [mul_assoc] using hbase
  have hsquare :=
    SquareSummableGeometricConvolution
      (u := fun t : ℕ => |err t|)
      (z := fun t : ℕ => |eta t|)
      (M := (1 : ℝ)) (r := r)
          (fun t => abs_nonneg (err t))
      (fun t => abs_nonneg (eta t))
      (by norm_num) hr_pos hr_lt_one hconv N
  simpa using hsquare

/-- Integrated finite-horizon lift of the scalar AR Duhamel square-sum core.

This is the stochastic wrapper for Appendix C.1 step 6 at block boundaries:
after the projected/scalar slow-coordinate error has a scalar AR recursion,
the deterministic Duhamel estimate can be integrated and the forcing square
moments substituted. -/
theorem scalar_ar_difference_square_integral_sum_bound_of_contract
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {gamma r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_r : gamma ≤ r)
    (err eta : Ω → ℕ → ℝ)
    (hrec : ∀ ω : Ω, ∀ k : ℕ,
      err ω (k + 1) = gamma * err ω k + eta ω k)
    (herr_int : ∀ t : ℕ, Integrable (fun ω : Ω => |err ω t| ^ 2) μ)
    (heta_int : ∀ k : ℕ, Integrable (fun ω : Ω => |eta ω k| ^ 2) μ)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
        ∫ ω, |err ω t| ^ 2 ∂μ) ≤
      (2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ) +
        (2 / (1 - r) ^ 2) *
          Finset.sum (Finset.range N) (fun j =>
            ∫ ω, |eta ω j| ^ 2 ∂μ) := by
  classical
  let A : ℝ := 2 / (1 - r ^ 2)
  let B : ℝ := 2 / (1 - r) ^ 2
  have hpoint :
      ∀ ω : Ω,
        Finset.sum (Finset.range (N + 1)) (fun t => |err ω t| ^ 2) ≤
          A * |err ω 0| ^ 2 +
            B * Finset.sum (Finset.range N) (fun j => |eta ω j| ^ 2) := by
    intro ω
    simpa [A, B] using
      scalar_ar_difference_square_sum_bound_of_contract
        hr_pos hr_lt_one hgamma_nonneg hgamma_le_r
        (fun t => err ω t) (fun k => eta ω k) (hrec ω) N
  have hleft_int :
      Integrable
        (fun ω : Ω =>
          Finset.sum (Finset.range (N + 1))
            (fun t => |err ω t| ^ 2)) μ := by
    exact integrable_finset_sum (Finset.range (N + 1))
      (fun t _ht => herr_int t)
  have heta_sum_int :
      Integrable
        (fun ω : Ω =>
          Finset.sum (Finset.range N) (fun j => |eta ω j| ^ 2)) μ := by
    exact integrable_finset_sum (Finset.range N)
      (fun j _hj => heta_int j)
  have hright_int :
      Integrable
        (fun ω : Ω =>
          A * |err ω 0| ^ 2 +
            B * Finset.sum (Finset.range N)
              (fun j => |eta ω j| ^ 2)) μ := by
    exact (herr_int 0).const_mul A |>.add (heta_sum_int.const_mul B)
  have hmono :
      (∫ ω : Ω,
        Finset.sum (Finset.range (N + 1))
          (fun t => |err ω t| ^ 2) ∂μ) ≤
        ∫ ω : Ω,
          A * |err ω 0| ^ 2 +
            B * Finset.sum (Finset.range N)
              (fun j => |eta ω j| ^ 2) ∂μ := by
    exact MeasureTheory.integral_mono_ae hleft_int hright_int
      (Filter.Eventually.of_forall hpoint)
  calc
    Finset.sum (Finset.range (N + 1)) (fun t =>
        ∫ ω, |err ω t| ^ 2 ∂μ) =
        ∫ ω : Ω,
          Finset.sum (Finset.range (N + 1))
            (fun t => |err ω t| ^ 2) ∂μ := by
          rw [MeasureTheory.integral_finset_sum]
          exact fun t _ht => herr_int t
    _ ≤ ∫ ω : Ω,
          A * |err ω 0| ^ 2 +
            B * Finset.sum (Finset.range N)
              (fun j => |eta ω j| ^ 2) ∂μ := hmono
    _ =
        A * (∫ ω, |err ω 0| ^ 2 ∂μ) +
          B * Finset.sum (Finset.range N) (fun j =>
            ∫ ω, |eta ω j| ^ 2 ∂μ) := by
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul]
            rw [MeasureTheory.integral_const_mul]
            rw [MeasureTheory.integral_finset_sum]
            · exact fun j _hj => by
                simpa [sq_abs] using heta_int j
          · exact (herr_int 0).const_mul A
          · exact heta_sum_int.const_mul B
    _ =
      (2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ) +
        (2 / (1 - r) ^ 2) *
          Finset.sum (Finset.range N) (fun j =>
            ∫ ω, |eta ω j| ^ 2 ∂μ) := by
        simp [A, B]

/-- Average `L²` bound for the slow scalar AR comparison.

This is the source-sized Appendix C.1 step-6 Duhamel normalization: the
integrated finite-horizon AR estimate is used with
`r = 1 - cGamma * alpha`; an `O(alpha²)` initial boundary error and an
`O(alpha⁴)` forcing budget give an averaged `O(alpha²)` error whenever
`alpha * T >= 1`. -/
theorem slow_ar_difference_average_l2_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {alpha cGamma Cinit Ceta gamma : ℝ}
    (halpha_pos : 0 < alpha) (hcGamma_pos : 0 < cGamma)
    (hr_pos : 0 < 1 - cGamma * alpha)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_r : gamma ≤ 1 - cGamma * alpha)
    (hCinit_nonneg : 0 ≤ Cinit) (hCeta_nonneg : 0 ≤ Ceta)
    (err eta : Ω → ℕ → ℝ)
    (hrec : ∀ ω : Ω, ∀ k : ℕ,
      err ω (k + 1) = gamma * err ω k + eta ω k)
    (herr_int : ∀ t : ℕ, Integrable (fun ω : Ω => |err ω t| ^ 2) μ)
    (heta_int : ∀ k : ℕ, Integrable (fun ω : Ω => |eta ω k| ^ 2) μ)
    (hinit_bound :
      (∫ ω, |err ω 0| ^ 2 ∂μ) ≤ Cinit * alpha ^ 2)
    (heta_sum_bound :
      ∀ N : ℕ,
        Finset.sum (Finset.range N) (fun k =>
          ∫ ω, |eta ω k| ^ 2 ∂μ) ≤
          Ceta * alpha ^ 4 * (N : ℝ)) :
    let C : ℝ := 2 * Cinit / cGamma + 2 * Ceta / cGamma ^ 2 + 1
    0 < C ∧
      ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
        ((T : ℝ)⁻¹) *
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω, |err ω t| ^ 2 ∂μ) ≤
          C * alpha ^ 2 := by
  classical
  let r : ℝ := 1 - cGamma * alpha
  let C : ℝ := 2 * Cinit / cGamma + 2 * Ceta / cGamma ^ 2 + 1
  have hcAlpha_pos : 0 < cGamma * alpha := mul_pos hcGamma_pos halpha_pos
  have hr_lt_one : r < 1 := by
    dsimp [r]
    nlinarith
  have hden1_pos : 0 < 1 - r ^ 2 := by
    have hr_sq_lt_one : r ^ 2 < 1 := by
      have hmul := mul_lt_mul_of_pos_left hr_lt_one hr_pos
      nlinarith
    nlinarith
  have hden1_ge : cGamma * alpha ≤ 1 - r ^ 2 := by
    dsimp [r]
    nlinarith [hcAlpha_pos, hr_pos]
  have hA_le : 2 / (1 - r ^ 2) ≤ 2 / (cGamma * alpha) :=
    div_le_div_of_nonneg_left (by norm_num) hcAlpha_pos hden1_ge
  have hA_nonneg : 0 ≤ 2 / (1 - r ^ 2) :=
    div_nonneg (by norm_num) hden1_pos.le
  have hB_eq : 2 / (1 - r) ^ 2 = 2 / (cGamma * alpha) ^ 2 := by
    dsimp [r]
    ring
  have hB_nonneg : 0 ≤ 2 / (1 - r) ^ 2 := by
    rw [hB_eq]
    positivity
  have hC_pos : 0 < C := by
    have hterm1_nonneg : 0 ≤ 2 * Cinit / cGamma := by positivity
    have hterm2_nonneg : 0 ≤ 2 * Ceta / cGamma ^ 2 := by positivity
    dsimp [C]
    nlinarith
  refine ⟨hC_pos, ?_⟩
  intro T halphaT
  have hprod_pos : 0 < alpha * (T : ℝ) :=
    lt_of_lt_of_le zero_lt_one halphaT
  have hT_pos : 0 < (T : ℝ) :=
    pos_of_mul_pos_right hprod_pos (le_of_lt halpha_pos)
  have hT_nat_pos : 0 < T := by exact_mod_cast hT_pos
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hT_pos.le
  have hTinv_le_alpha : (T : ℝ)⁻¹ ≤ alpha := by
    have hdiv : (1 : ℝ) / (T : ℝ) ≤ alpha := by
      exact (div_le_iff₀ hT_pos).mpr (by simpa [one_mul] using halphaT)
    simpa [one_div] using hdiv
  have hsum_contract :
      Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |err ω t| ^ 2 ∂μ) ≤
        (2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ) +
          (2 / (1 - r) ^ 2) *
            Finset.sum (Finset.range (T - 1)) (fun j =>
              ∫ ω, |eta ω j| ^ 2 ∂μ) := by
    have hbase :=
      scalar_ar_difference_square_integral_sum_bound_of_contract
        (μ := μ) (gamma := gamma) (r := r)
        hr_pos hr_lt_one hgamma_nonneg hgamma_le_r
        err eta hrec herr_int heta_int (T - 1)
    have hT_pred : T - 1 + 1 = T :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hT_nat_pos)
    rw [hT_pred] at hbase
    simpa [sq_abs] using hbase
  have hI0_nonneg : 0 ≤ ∫ ω, |err ω 0| ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg fun ω => sq_nonneg |err ω 0|
  have hinit_term :
      ((T : ℝ)⁻¹) *
          ((2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ)) ≤
        (2 * Cinit / cGamma) * alpha ^ 2 := by
    have hmul_bound :
        (2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ) ≤
          (2 / (cGamma * alpha)) * (Cinit * alpha ^ 2) := by
      exact mul_le_mul hA_le hinit_bound hI0_nonneg
        (div_nonneg (by norm_num) hcAlpha_pos.le)
    calc
      ((T : ℝ)⁻¹) *
          ((2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ)) ≤
          ((T : ℝ)⁻¹) *
            ((2 / (cGamma * alpha)) * (Cinit * alpha ^ 2)) :=
            mul_le_mul_of_nonneg_left hmul_bound hTinv_nonneg
      _ = (2 * Cinit / cGamma) * alpha * (T : ℝ)⁻¹ := by
            field_simp [ne_of_gt hcGamma_pos, ne_of_gt halpha_pos]
      _ ≤ (2 * Cinit / cGamma) * alpha * alpha := by
            exact mul_le_mul_of_nonneg_left hTinv_le_alpha
              (mul_nonneg
                (div_nonneg (mul_nonneg (by norm_num) hCinit_nonneg)
                  hcGamma_pos.le)
                (le_of_lt halpha_pos))
      _ = (2 * Cinit / cGamma) * alpha ^ 2 := by ring
  have heta_sum_nonneg :
      0 ≤ Finset.sum (Finset.range (T - 1)) (fun j =>
        ∫ ω, |eta ω j| ^ 2 ∂μ) := by
    exact Finset.sum_nonneg fun j _hj =>
      MeasureTheory.integral_nonneg fun ω => sq_nonneg |eta ω j|
  have hpred_le_T : ((T - 1 : ℕ) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast Nat.sub_le T 1
  have heta_sum_le_T :
      Finset.sum (Finset.range (T - 1)) (fun j =>
          ∫ ω, |eta ω j| ^ 2 ∂μ) ≤
        Ceta * alpha ^ 4 * (T : ℝ) := by
    calc
      Finset.sum (Finset.range (T - 1)) (fun j =>
          ∫ ω, |eta ω j| ^ 2 ∂μ) ≤
          Ceta * alpha ^ 4 * ((T - 1 : ℕ) : ℝ) :=
          heta_sum_bound (T - 1)
      _ ≤ Ceta * alpha ^ 4 * (T : ℝ) := by
          exact mul_le_mul_of_nonneg_left hpred_le_T
            (mul_nonneg hCeta_nonneg (pow_nonneg (le_of_lt halpha_pos) 4))
  have heta_term :
      ((T : ℝ)⁻¹) *
          ((2 / (1 - r) ^ 2) *
            Finset.sum (Finset.range (T - 1)) (fun j =>
              ∫ ω, |eta ω j| ^ 2 ∂μ)) ≤
        (2 * Ceta / cGamma ^ 2) * alpha ^ 2 := by
    calc
      ((T : ℝ)⁻¹) *
          ((2 / (1 - r) ^ 2) *
            Finset.sum (Finset.range (T - 1)) (fun j =>
              ∫ ω, |eta ω j| ^ 2 ∂μ)) =
          ((T : ℝ)⁻¹) *
            ((2 / (cGamma * alpha) ^ 2) *
              Finset.sum (Finset.range (T - 1)) (fun j =>
                ∫ ω, |eta ω j| ^ 2 ∂μ)) := by
            rw [hB_eq]
      _ ≤ ((T : ℝ)⁻¹) *
            ((2 / (cGamma * alpha) ^ 2) *
              (Ceta * alpha ^ 4 * (T : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left heta_sum_le_T (by positivity))
              hTinv_nonneg
      _ = (2 * Ceta / cGamma ^ 2) * alpha ^ 2 := by
            field_simp [hT_ne, ne_of_gt hcGamma_pos, ne_of_gt halpha_pos]
  calc
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |err ω t| ^ 2 ∂μ) ≤
        ((T : ℝ)⁻¹) *
          ((2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ) +
            (2 / (1 - r) ^ 2) *
              Finset.sum (Finset.range (T - 1)) (fun j =>
                ∫ ω, |eta ω j| ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_left hsum_contract hTinv_nonneg
    _ =
        ((T : ℝ)⁻¹) *
          ((2 / (1 - r ^ 2)) * (∫ ω, |err ω 0| ^ 2 ∂μ)) +
        ((T : ℝ)⁻¹) *
          ((2 / (1 - r) ^ 2) *
            Finset.sum (Finset.range (T - 1)) (fun j =>
              ∫ ω, |eta ω j| ^ 2 ∂μ)) := by ring
    _ ≤
        (2 * Cinit / cGamma) * alpha ^ 2 +
          (2 * Ceta / cGamma ^ 2) * alpha ^ 2 :=
        add_le_add hinit_term heta_term
    _ ≤ C * alpha ^ 2 := by
        have hsq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
        dsimp [C]
        nlinarith

theorem real_abs_add_sq_le_two_sq (a b : ℝ) :
    |a + b| ^ 2 ≤ 2 * |a| ^ 2 + 2 * |b| ^ 2 := by
  have hle : |a + b| ≤ |a| + |b| := abs_add_le a b
  have hsum_nonneg : 0 ≤ |a| + |b| :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hsq_le : |a + b| ^ 2 ≤ (|a| + |b|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg (a + b)) hle 2
  have hcross : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg (|a| - |b|)
  nlinarith

/-- Finite-horizon forcing budget for the projected/scalar slow AR
comparison.

If the multiplier error is `O(alpha²)`, the scalar boundary square moments
have a linear finite-horizon budget, and the projected/scalar block-input
difference has an `O(alpha⁴)` budget, then the combined forcing
`(gamma-Gamma) * scalar + inputDiff` has the source `O(alpha⁴ * N)` budget. -/
theorem slow_ar_difference_forcing_square_sum_bound_of_parts
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {alpha Cmul Cscalar Cinput gamma Gamma : ℝ}
    (hCscalar_nonneg : 0 ≤ Cscalar)
    (hCinput_nonneg : 0 ≤ Cinput)
    (hcoeff_bound : |gamma - Gamma| ≤ Cmul * alpha ^ 2)
    (scalar inputDiff : Ω → ℕ → ℝ)
    (hscalar_sq_int :
      ∀ k : ℕ, Integrable (fun ω : Ω => |scalar ω k| ^ 2) μ)
    (hinput_sq_int :
      ∀ k : ℕ, Integrable (fun ω : Ω => |inputDiff ω k| ^ 2) μ)
    (hforcing_sq_int :
      ∀ k : ℕ,
        Integrable
          (fun ω : Ω =>
            |(gamma - Gamma) * scalar ω k + inputDiff ω k| ^ 2) μ)
    (hscalar_sum_bound :
      ∀ N : ℕ,
        Finset.sum (Finset.range N) (fun k =>
          ∫ ω, |scalar ω k| ^ 2 ∂μ) ≤
          Cscalar * (N : ℝ))
    (hinput_sum_bound :
      ∀ N : ℕ,
        Finset.sum (Finset.range N) (fun k =>
          ∫ ω, |inputDiff ω k| ^ 2 ∂μ) ≤
          Cinput * alpha ^ 4 * (N : ℝ)) :
    ∀ N : ℕ,
      Finset.sum (Finset.range N) (fun k =>
        ∫ ω,
          |(gamma - Gamma) * scalar ω k + inputDiff ω k| ^ 2 ∂μ) ≤
        (2 * Cmul ^ 2 * Cscalar + 2 * Cinput) *
          alpha ^ 4 * (N : ℝ) := by
  classical
  let coeff : ℝ := gamma - Gamma
  have hcoeff_sq :
      coeff ^ 2 ≤ Cmul ^ 2 * alpha ^ 4 := by
    have hsq :=
      pow_le_pow_left₀ (abs_nonneg coeff)
        (by simpa [coeff] using hcoeff_bound) 2
    calc
      coeff ^ 2 = |coeff| ^ 2 := by rw [sq_abs]
      _ ≤ (Cmul * alpha ^ 2) ^ 2 := hsq
      _ = Cmul ^ 2 * alpha ^ 4 := by ring
  have hcoeff_sq_nonneg : 0 ≤ coeff ^ 2 := sq_nonneg coeff
  have hcoeff_budget_nonneg : 0 ≤ Cmul ^ 2 * alpha ^ 4 := by positivity
  intro N
  have hterm_bound :
      ∀ k : ℕ,
        (∫ ω,
          |coeff * scalar ω k + inputDiff ω k| ^ 2 ∂μ) ≤
          2 * coeff ^ 2 *
              (∫ ω, |scalar ω k| ^ 2 ∂μ) +
            2 * (∫ ω, |inputDiff ω k| ^ 2 ∂μ) := by
    intro k
    let upper : Ω → ℝ := fun ω =>
      2 * coeff ^ 2 * |scalar ω k| ^ 2 +
        2 * |inputDiff ω k| ^ 2
    have hupper_int : Integrable upper μ := by
      exact ((hscalar_sq_int k).const_mul (2 * coeff ^ 2)).add
        ((hinput_sq_int k).const_mul 2)
    have hmono :
        (∫ ω,
          |coeff * scalar ω k + inputDiff ω k| ^ 2 ∂μ) ≤
          ∫ ω, upper ω ∂μ := by
      exact MeasureTheory.integral_mono_ae (hforcing_sq_int k) hupper_int
        (Filter.Eventually.of_forall fun ω => by
          have hbasic :=
            real_abs_add_sq_le_two_sq (coeff * scalar ω k)
              (inputDiff ω k)
          have hmul :
              |coeff * scalar ω k| ^ 2 =
                coeff ^ 2 * |scalar ω k| ^ 2 := by
            rw [abs_mul, mul_pow, sq_abs]
          dsimp [upper]
          rw [hmul] at hbasic
          nlinarith)
    calc
      (∫ ω,
        |coeff * scalar ω k + inputDiff ω k| ^ 2 ∂μ) ≤
          ∫ ω, upper ω ∂μ := hmono
      _ =
          2 * coeff ^ 2 *
              (∫ ω, |scalar ω k| ^ 2 ∂μ) +
            2 * (∫ ω, |inputDiff ω k| ^ 2 ∂μ) := by
        dsimp [upper]
        rw [MeasureTheory.integral_add]
        · rw [MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_const_mul]
        · exact (hscalar_sq_int k).const_mul (2 * coeff ^ 2)
        · exact (hinput_sq_int k).const_mul 2
  have hsum_terms :
      Finset.sum (Finset.range N) (fun k =>
        ∫ ω,
          |coeff * scalar ω k + inputDiff ω k| ^ 2 ∂μ) ≤
        2 * coeff ^ 2 *
            Finset.sum (Finset.range N) (fun k =>
              ∫ ω, |scalar ω k| ^ 2 ∂μ) +
          2 * Finset.sum (Finset.range N) (fun k =>
              ∫ ω, |inputDiff ω k| ^ 2 ∂μ) := by
    calc
      Finset.sum (Finset.range N) (fun k =>
          ∫ ω,
            |coeff * scalar ω k + inputDiff ω k| ^ 2 ∂μ) ≤
          Finset.sum (Finset.range N) (fun k =>
            2 * coeff ^ 2 *
                (∫ ω, |scalar ω k| ^ 2 ∂μ) +
              2 * (∫ ω, |inputDiff ω k| ^ 2 ∂μ)) :=
        Finset.sum_le_sum fun k _hk => hterm_bound k
      _ =
        2 * coeff ^ 2 *
            Finset.sum (Finset.range N) (fun k =>
              ∫ ω, |scalar ω k| ^ 2 ∂μ) +
          2 * Finset.sum (Finset.range N) (fun k =>
              ∫ ω, |inputDiff ω k| ^ 2 ∂μ) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hscalar_sum_nonneg :
      0 ≤ Finset.sum (Finset.range N) (fun k =>
        ∫ ω, |scalar ω k| ^ 2 ∂μ) := by
    exact Finset.sum_nonneg fun k _hk =>
      MeasureTheory.integral_nonneg fun ω => sq_nonneg |scalar ω k|
  have hinput_sum_nonneg :
      0 ≤ Finset.sum (Finset.range N) (fun k =>
        ∫ ω, |inputDiff ω k| ^ 2 ∂μ) := by
    exact Finset.sum_nonneg fun k _hk =>
      MeasureTheory.integral_nonneg fun ω => sq_nonneg |inputDiff ω k|
  have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have hscalar_part :
      2 * coeff ^ 2 *
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω, |scalar ω k| ^ 2 ∂μ) ≤
        2 * Cmul ^ 2 * Cscalar * alpha ^ 4 * (N : ℝ) := by
    calc
      2 * coeff ^ 2 *
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω, |scalar ω k| ^ 2 ∂μ) ≤
          2 * (Cmul ^ 2 * alpha ^ 4) *
            (Cscalar * (N : ℝ)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hcoeff_sq (by norm_num))
          (hscalar_sum_bound N) hscalar_sum_nonneg
          (mul_nonneg (by norm_num) hcoeff_budget_nonneg)
      _ = 2 * Cmul ^ 2 * Cscalar * alpha ^ 4 * (N : ℝ) := by ring
  have hinput_part :
      2 * Finset.sum (Finset.range N) (fun k =>
          ∫ ω, |inputDiff ω k| ^ 2 ∂μ) ≤
        2 * Cinput * alpha ^ 4 * (N : ℝ) := by
    calc
      2 * Finset.sum (Finset.range N) (fun k =>
          ∫ ω, |inputDiff ω k| ^ 2 ∂μ) ≤
          2 * (Cinput * alpha ^ 4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hinput_sum_bound N) (by norm_num)
      _ = 2 * Cinput * alpha ^ 4 * (N : ℝ) := by ring
  calc
    Finset.sum (Finset.range N) (fun k =>
        ∫ ω,
          |(gamma - Gamma) * scalar ω k + inputDiff ω k| ^ 2 ∂μ) =
        Finset.sum (Finset.range N) (fun k =>
          ∫ ω,
            |coeff * scalar ω k + inputDiff ω k| ^ 2 ∂μ) := by
          simp [coeff]
    _ ≤
        2 * coeff ^ 2 *
            Finset.sum (Finset.range N) (fun k =>
              ∫ ω, |scalar ω k| ^ 2 ∂μ) +
          2 * Finset.sum (Finset.range N) (fun k =>
              ∫ ω, |inputDiff ω k| ^ 2 ∂μ) := hsum_terms
    _ ≤
        2 * Cmul ^ 2 * Cscalar * alpha ^ 4 * (N : ℝ) +
          2 * Cinput * alpha ^ 4 * (N : ℝ) :=
        add_le_add hscalar_part hinput_part
    _ =
        (2 * Cmul ^ 2 * Cscalar + 2 * Cinput) *
          alpha ^ 4 * (N : ℝ) := by ring

/-- Exact error recursion obtained by subtracting two scalar AR recursions.

This is the algebraic identification used at Appendix C.1 block boundaries:
the projected slow scalar and the paper scalar process have different
multipliers and different block inputs, so their difference has forcing
`(gamma - Gamma) * scalar + (projectedInput - scalarInput)`. -/
theorem scalar_ar_difference_recursion_of_two_recursions
    {gamma Gamma : ℝ}
    (slow scalar projectedInput scalarInput : ℕ → ℝ)
    (hslow :
      ∀ k : ℕ, slow (k + 1) = gamma * slow k + projectedInput k)
    (hscalar :
      ∀ k : ℕ, scalar (k + 1) = Gamma * scalar k + scalarInput k) :
    ∀ k : ℕ,
      slow (k + 1) - scalar (k + 1) =
        gamma * (slow k - scalar k) +
          ((gamma - Gamma) * scalar k +
            (projectedInput k - scalarInput k)) := by
  intro k
  rw [hslow k, hscalar k]
  ring

def finiteWindowLinearBudget (M C : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => M * finiteWindowLinearBudget M C n + C

theorem finiteWindowLinearBudget_nonneg
    {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) :
    ∀ n : ℕ, 0 ≤ finiteWindowLinearBudget M C n := by
  intro n
  induction n with
  | zero =>
      simp [finiteWindowLinearBudget]
  | succ n ih =>
      simp [finiteWindowLinearBudget]
      exact add_nonneg (mul_nonneg hM ih) hC

theorem finiteWindowLinearBudget_le_sum
    {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (m n : ℕ) (hn : n ≤ m) :
    finiteWindowLinearBudget M C n ≤
      Finset.sum (Finset.range (m + 1))
        (fun r => finiteWindowLinearBudget M C r) := by
  classical
  have hmem : n ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
  exact Finset.single_le_sum
    (fun r _hr => finiteWindowLinearBudget_nonneg hM hC r) hmem

theorem finiteWindowLinearBudget_bound
    {M C E : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (Y : ℕ → ℝ)
    (hY0 : Y 0 ≤ 0)
    (hrec : ∀ n : ℕ, Y (n + 1) ≤ M * Y n + C * E) :
    ∀ n : ℕ, Y n ≤ finiteWindowLinearBudget M C n * E := by
  intro n
  induction n with
  | zero =>
      simpa [finiteWindowLinearBudget] using hY0
  | succ n ih =>
      calc
        Y (n + 1) ≤ M * Y n + C * E := hrec n
        _ ≤ M * (finiteWindowLinearBudget M C n * E) + C * E := by
          simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left ih hM) (C * E)
        _ = finiteWindowLinearBudget M C (n + 1) * E := by
          simp [finiteWindowLinearBudget]
          ring

theorem finiteWindowLinearBudget_bound_upto
    {M C E : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (Y : ℕ → ℝ)
    (hY0 : Y 0 ≤ 0)
    (hrec : ∀ n : ℕ, n < m → Y (n + 1) ≤ M * Y n + C * E) :
    ∀ n : ℕ, n ≤ m → Y n ≤ finiteWindowLinearBudget M C n * E := by
  intro n hn
  induction n with
  | zero =>
      simpa [finiteWindowLinearBudget] using hY0
  | succ n ih =>
      have hn_lt : n < m := Nat.lt_of_succ_le hn
      have hn_le : n ≤ m := Nat.le_of_lt hn_lt
      calc
        Y (n + 1) ≤ M * Y n + C * E := hrec n hn_lt
        _ ≤ M * (finiteWindowLinearBudget M C n * E) + C * E := by
          simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left (ih hn_le) hM) (C * E)
        _ = finiteWindowLinearBudget M C (n + 1) * E := by
          simp [finiteWindowLinearBudget]
          ring

/-- Uniform alpha-zero one-step homogeneous operator bound for the restricted
C.1 coordinates. -/
theorem quadraticRestrictedOneStepMatrix_zero_uniform_operator_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧
      ∀ k n : ℕ, n < quad.period →
        matrixEuclideanOperatorNorm
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda 0 i0
            (k * quad.period + n)) ≤ M0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let B : ℝ := 2 * |lambda| + 2
  let M0 : ℝ :=
    (((nodeCount (Node := Idx) : ℝ) ^ 2) *
        Real.sqrt (nodeCount (Node := Idx) : ℝ)) * B
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨M0, ?_, ?_⟩
  · dsimp [M0]
    positivity
  intro k n _hn
  have hR_entry_le_one :
      ∀ i j : Node, quad.R (k * quad.period + n) i j ≤ 1 := by
    intro i j
    have hsingle :
        quad.R (k * quad.period + n) i j ≤
          ∑ x : Node, quad.R (k * quad.period + n) i x :=
      Finset.single_le_sum
        (fun x _hx => quad.R_entry_nonneg (k * quad.period + n) i x)
        (Finset.mem_univ j)
    simpa [quad.R_row_sum (k * quad.period + n) i] using hsingle
  have hC_entry_le_one :
      ∀ i j : Node, quad.C (k * quad.period + n) i j ≤ 1 := by
    intro i j
    have hsingle :
        quad.C (k * quad.period + n) i j ≤
          ∑ x : Node, quad.C (k * quad.period + n) x j :=
      Finset.single_le_sum
        (fun x _hx => quad.C_entry_nonneg (k * quad.period + n) x j)
        (Finset.mem_univ i)
    simpa [quad.C_column_sum (k * quad.period + n) j] using hsingle
  have hentry :
      ∀ a b : Idx,
        |quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda 0 i0
          (k * quad.period + n) a b| ≤ B := by
    intro a b
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            have hR_nonneg :
                0 ≤ quad.R (k * quad.period + n) i j :=
              quad.R_entry_nonneg (k * quad.period + n) i j
            have hR_le : quad.R (k * quad.period + n) i j ≤ 1 :=
              hR_entry_le_one i j
            calc
              |quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0
                  (k * quad.period + n) (Sum.inl i) (Sum.inl j)| =
                  |quad.R (k * quad.period + n) i j| := by
                    by_cases hij : i = j <;>
                      simp [quadraticRestrictedOneStepMatrix, identityMatrix, hij]
              _ ≤ 1 := by
                    rw [abs_of_nonneg hR_nonneg]
                    exact hR_le
              _ ≤ B := by
                    dsimp [B]
                    nlinarith [abs_nonneg lambda]
        | inr j =>
            calc
              |quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0
                  (k * quad.period + n) (Sum.inl i) (Sum.inr j)| = 0 := by
                    simp [quadraticRestrictedOneStepMatrix]
              _ ≤ B := hB_nonneg
    | inr i =>
        cases b with
        | inl j =>
            have hC_nonneg :
                0 ≤ quad.C (k * quad.period + n) i.1 j :=
              quad.C_entry_nonneg (k * quad.period + n) i.1 j
            have hC_le : quad.C (k * quad.period + n) i.1 j ≤ 1 :=
              hC_entry_le_one i.1 j
            have hid_nonneg :
                0 ≤ identityMatrix (Node := Node) i.1 j := by
              by_cases hij : i.1 = j <;> simp [identityMatrix, hij]
            have hid_le_one :
                identityMatrix (Node := Node) i.1 j ≤ 1 := by
              by_cases hij : i.1 = j <;> simp [identityMatrix, hij]
            have habs :
                |quad.C (k * quad.period + n) i.1 j -
                    identityMatrix (Node := Node) i.1 j| ≤ 2 := by
              have htri :
                  |quad.C (k * quad.period + n) i.1 j -
                      identityMatrix (Node := Node) i.1 j| ≤
                    quad.C (k * quad.period + n) i.1 j +
                      identityMatrix (Node := Node) i.1 j := by
                refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
              exact le_trans htri (by nlinarith)
            calc
              |quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0
                  (k * quad.period + n) (Sum.inr i) (Sum.inl j)| =
                  |lambda| *
                    |quad.C (k * quad.period + n) i.1 j -
                      identityMatrix (Node := Node) i.1 j| := by
                    simp [quadraticRestrictedOneStepMatrix, abs_mul]
              _ ≤ |lambda| * 2 := by
                    exact mul_le_mul_of_nonneg_left habs (abs_nonneg lambda)
              _ ≤ B := by
                    dsimp [B]
                    nlinarith [abs_nonneg lambda]
        | inr j =>
            have hCij_nonneg :
                0 ≤ quad.C (k * quad.period + n) i.1 j.1 :=
              quad.C_entry_nonneg (k * quad.period + n) i.1 j.1
            have hCi0_nonneg :
                0 ≤ quad.C (k * quad.period + n) i.1 i0 :=
              quad.C_entry_nonneg (k * quad.period + n) i.1 i0
            have hCij_le : quad.C (k * quad.period + n) i.1 j.1 ≤ 1 :=
              hC_entry_le_one i.1 j.1
            have hCi0_le : quad.C (k * quad.period + n) i.1 i0 ≤ 1 :=
              hC_entry_le_one i.1 i0
            have habs :
                |quad.C (k * quad.period + n) i.1 j.1 -
                    quad.C (k * quad.period + n) i.1 i0| ≤ 2 := by
              have htri :
                  |quad.C (k * quad.period + n) i.1 j.1 -
                      quad.C (k * quad.period + n) i.1 i0| ≤
                    quad.C (k * quad.period + n) i.1 j.1 +
                      quad.C (k * quad.period + n) i.1 i0 := by
                refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
              exact le_trans htri (by nlinarith)
            calc
              |quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0
                  (k * quad.period + n) (Sum.inr i) (Sum.inr j)| =
                  |quad.C (k * quad.period + n) i.1 j.1 -
                    quad.C (k * quad.period + n) i.1 i0| := by
                    simp [quadraticRestrictedOneStepMatrix]
              _ ≤ 2 := habs
              _ ≤ B := by
                    dsimp [B]
                    nlinarith [abs_nonneg lambda]
  simpa [M0, Idx] using
    matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound
      (Node := Idx)
      (quadraticRestrictedOneStepMatrix
        (Node := Node) quad lambda 0 i0 (k * quad.period + n))
      B hB_nonneg hentry

/-- The restricted one-step homogeneous matrix is alpha-Lipschitz at zero. -/
theorem quadraticRestrictedOneStepMatrix_sub_zero_operator_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) :
    ∃ Lstep : ℝ, 0 ≤ Lstep ∧
      ∀ alpha : ℝ, 0 ≤ alpha →
        ∀ k n : ℕ, n < quad.period →
          matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixSub
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedOneStepMatrix
                (Node := Node) quad lambda alpha i0
                (k * quad.period + n))
              (quadraticRestrictedOneStepMatrix
                (Node := Node) quad lambda 0 i0
                (k * quad.period + n))) ≤ Lstep * alpha := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let B : ℝ := |lambda| + 1
  let Lstep : ℝ :=
    (((nodeCount (Node := Idx) : ℝ) ^ 2) *
        Real.sqrt (nodeCount (Node := Idx) : ℝ)) * B
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Lstep, ?_, ?_⟩
  · dsimp [Lstep]
    positivity
  intro alpha halpha_nonneg k n _hn
  have hentry :
      ∀ a b : Idx,
                  |matrixSub (Node := Idx)
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0
            (k * quad.period + n))
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda 0 i0
            (k * quad.period + n)) a b| ≤ B * alpha := by
    intro a b
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            by_cases hij : i = j
            · subst j
              calc
                |matrixSub (Node := Idx)
                    (quadraticRestrictedOneStepMatrix
                      (Node := Node) quad lambda alpha i0
                      (k * quad.period + n))
                    (quadraticRestrictedOneStepMatrix
                      (Node := Node) quad lambda 0 i0
                      (k * quad.period + n)) (Sum.inl i) (Sum.inl i)| =
                    |-(alpha * lambda)| := by
                      simp [matrixSub, quadraticRestrictedOneStepMatrix,
                        identityMatrix]
                _ = alpha * |lambda| := by
                      simp [abs_mul, abs_of_nonneg halpha_nonneg]
                _ ≤ B * alpha := by
                      dsimp [B]
                      nlinarith [halpha_nonneg, abs_nonneg lambda]
            · calc
                |matrixSub (Node := Idx)
                    (quadraticRestrictedOneStepMatrix
                      (Node := Node) quad lambda alpha i0
                      (k * quad.period + n))
                    (quadraticRestrictedOneStepMatrix
                      (Node := Node) quad lambda 0 i0
                      (k * quad.period + n)) (Sum.inl i) (Sum.inl j)| = 0 := by
                      simp [matrixSub, quadraticRestrictedOneStepMatrix,
                        identityMatrix, hij]
                _ ≤ B * alpha := mul_nonneg hB_nonneg halpha_nonneg
        | inr j =>
            have hcoeff := restrictedTrackerCoordCoeff_abs_le_one
              (Node := Node) i0 i j
            calc
              |matrixSub (Node := Idx)
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda alpha i0
                    (k * quad.period + n))
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda 0 i0
                    (k * quad.period + n)) (Sum.inl i) (Sum.inr j)| =
                  alpha *
                    |restrictedTrackerCoordCoeff (Node := Node) i0 i j| := by
                    simp [matrixSub, quadraticRestrictedOneStepMatrix,
                      abs_mul, abs_of_nonneg halpha_nonneg]
              _ ≤ alpha * 1 := mul_le_mul_of_nonneg_left hcoeff halpha_nonneg
              _ ≤ B * alpha := by
                    dsimp [B]
                    nlinarith [halpha_nonneg, abs_nonneg lambda]
    | inr i =>
        cases b with
        | inl j =>
            calc
              |matrixSub (Node := Idx)
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda alpha i0
                    (k * quad.period + n))
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda 0 i0
                    (k * quad.period + n)) (Sum.inr i) (Sum.inl j)| = 0 := by
                    simp [matrixSub, quadraticRestrictedOneStepMatrix]
              _ ≤ B * alpha := mul_nonneg hB_nonneg halpha_nonneg
        | inr j =>
            calc
              |matrixSub (Node := Idx)
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda alpha i0
                    (k * quad.period + n))
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda 0 i0
                    (k * quad.period + n)) (Sum.inr i) (Sum.inr j)| = 0 := by
                    simp [matrixSub, quadraticRestrictedOneStepMatrix]
              _ ≤ B * alpha := mul_nonneg hB_nonneg halpha_nonneg
  have hBalpha_nonneg : 0 ≤ B * alpha := mul_nonneg hB_nonneg halpha_nonneg
  have hraw :=
    matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound
      (Node := Idx)
      (matrixSub (Node := Idx)
        (quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0
          (k * quad.period + n))
        (quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda 0 i0
          (k * quad.period + n)))
      (B * alpha) hBalpha_nonneg hentry
  calc
    matrixEuclideanOperatorNorm (Node := Idx)
        (matrixSub (Node := Idx)
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0
            (k * quad.period + n))
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda 0 i0
            (k * quad.period + n))) ≤
        (((nodeCount (Node := Idx) : ℝ) ^ 2) *
            Real.sqrt (nodeCount (Node := Idx) : ℝ)) * (B * alpha) := hraw
    _ = Lstep * alpha := by
        dsimp [Lstep]
        ring

/-- Pathwise source-envelope bound for a single restricted C.1 noise channel.

This is the deterministic formula-level form of
`N_t(alpha) epsilon_t = (-alpha epsilon_t, (C_t-I)epsilon_t)`: on a bounded
stepsize interval every restricted coordinate is bounded by the current raw
node-noise norm. -/
theorem quadraticRestrictedNoiseInnovationCoord_norm_le_noise
    (quad : Setup Node ℝ) (alphaBound : ℝ) (i0 : Node)
    (halphaBound_nonneg : 0 ≤ alphaBound) :
    ∃ Ceta : ℝ, 0 ≤ Ceta ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alphaBound →
        ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
          rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise t) ≤
            Ceta * rowEuclideanNorm (Node := Node) (noise t) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let B : ℝ := alphaBound + 2 * (nodeCount (Node := Node) : ℝ)
  let Ceta : ℝ := (nodeCount (Node := Idx) : ℝ) * B
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Ceta, ?_, ?_⟩
  · dsimp [Ceta]
    positivity
  intro alpha halpha_nonneg halpha_le noise t
  let eta : RowVector Idx :=
    quadraticRestrictedNoiseInnovationCoord
      (Node := Node) quad alpha i0 noise t
  let Nnorm : ℝ := rowEuclideanNorm (Node := Node) (noise t)
  have hNnorm_nonneg : 0 ≤ Nnorm := by
    dsimp [Nnorm]
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg (rowNormSq (Node := Node) (noise t))
  have hcoord : ∀ a : Idx, |eta a| ≤ B * Nnorm := by
    intro a
    cases a with
    | inl i =>
        have hcoord_noise :
            |noise t i| ≤ Nnorm := by
          simpa [Nnorm] using
            rowVector_coordinate_abs_le_rowEuclideanNorm
              (Node := Node) (noise t) i
        calc
          |eta (Sum.inl i)| = alpha * |noise t i| := by
              simp [eta, quadraticRestrictedNoiseInnovationCoord,
                restrictedStateToCoord, abs_mul, abs_of_nonneg halpha_nonneg]
          _ ≤ alphaBound * Nnorm :=
              mul_le_mul halpha_le hcoord_noise (abs_nonneg _) halphaBound_nonneg
          _ ≤ B * Nnorm := by
              exact mul_le_mul_of_nonneg_right (by dsimp [B]; linarith)
                hNnorm_nonneg
    | inr i =>
        have hterm :
            ∀ j : Node,
              |(quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                  noise t j| ≤ 2 * Nnorm := by
          intro j
          have hC_nonneg : 0 ≤ quad.C t i.1 j :=
            quad.C_entry_nonneg t i.1 j
          have hC_le_one : quad.C t i.1 j ≤ 1 := by
            have hsingle :
                quad.C t i.1 j ≤ ∑ x : Node, quad.C t x j :=
              Finset.single_le_sum
                (fun x _hx => quad.C_entry_nonneg t x j)
                (Finset.mem_univ i.1)
            simpa [quad.C_column_sum t j] using hsingle
          have hid_nonneg :
              0 ≤ identityMatrix (Node := Node) i.1 j := by
            by_cases hij : i.1 = j <;> simp [identityMatrix, hij]
          have hid_le_one :
              identityMatrix (Node := Node) i.1 j ≤ 1 := by
            by_cases hij : i.1 = j <;> simp [identityMatrix, hij]
          have hcoeff :
              |quad.C t i.1 j - identityMatrix (Node := Node) i.1 j| ≤
                2 := by
            have htri :
                |quad.C t i.1 j - identityMatrix (Node := Node) i.1 j| ≤
                  quad.C t i.1 j + identityMatrix (Node := Node) i.1 j := by
              refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith
            exact le_trans htri (by nlinarith)
          have hnoise_coord :
              |noise t j| ≤ Nnorm := by
            simpa [Nnorm] using
              rowVector_coordinate_abs_le_rowEuclideanNorm
                (Node := Node) (noise t) j
          calc
            |(quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                noise t j| =
                |quad.C t i.1 j - identityMatrix (Node := Node) i.1 j| *
                  |noise t j| := by rw [abs_mul]
            _ ≤ 2 * Nnorm :=
                mul_le_mul hcoeff hnoise_coord (abs_nonneg _)
                  (by norm_num : (0 : ℝ) ≤ 2)
        have hsum :
            |∑ j : Node,
                (quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                  noise t j| ≤
              ∑ _j : Node, 2 * Nnorm := by
          calc
            |∑ j : Node,
                (quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                  noise t j| ≤
                ∑ j : Node,
                  |(quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                    noise t j| := by
                  exact Finset.abs_sum_le_sum_abs (s := Finset.univ)
                    (fun j : Node =>
                      (quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                        noise t j)
            _ ≤ ∑ _j : Node, 2 * Nnorm :=
                Finset.sum_le_sum (fun j _hj => hterm j)
        calc
          |eta (Sum.inr i)| =
              |∑ j : Node,
                (quad.C t i.1 j - identityMatrix (Node := Node) i.1 j) *
                  noise t j| := by
                simp [eta, quadraticRestrictedNoiseInnovationCoord,
                  restrictedStateToCoord, leftMul, matrixSub]
          _ ≤ ∑ _j : Node, 2 * Nnorm := hsum
          _ = (nodeCount (Node := Node) : ℝ) * (2 * Nnorm) := by
                simp [nodeCount]
          _ = (2 * (nodeCount (Node := Node) : ℝ)) * Nnorm := by ring
          _ ≤ B * Nnorm := by
                exact mul_le_mul_of_nonneg_right (by dsimp [B]; linarith)
                  hNnorm_nonneg
  have hBtimes_nonneg : 0 ≤ B * Nnorm := mul_nonneg hB_nonneg hNnorm_nonneg
  calc
    rowEuclideanNorm (Node := Idx) eta ≤
        (nodeCount (Node := Idx) : ℝ) * (B * Nnorm) :=
      rowEuclideanNorm_le_card_mul_of_abs_le
        (Node := Idx) eta hBtimes_nonneg hcoord
    _ = Ceta * Nnorm := by
        dsimp [Ceta]
        ring

/-- The alpha-dependent part of one restricted noise channel is only the
primal block, hence it is pathwise `O(alpha)` against the raw node-noise norm. -/
theorem quadraticRestrictedNoiseInnovationCoord_sub_zero_norm_le_noise
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    (halpha_nonneg : 0 ≤ alpha)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (fun a =>
          quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise t a -
            quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad 0 i0 noise t a) ≤
      (nodeCount (Node := Sum Node {i : Node // i ≠ i0}) : ℝ) *
        alpha * rowEuclideanNorm (Node := Node) (noise t) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let B : ℝ := alpha * rowEuclideanNorm (Node := Node) (noise t)
  have hnoise_norm_nonneg :
      0 ≤ rowEuclideanNorm (Node := Node) (noise t) := by
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg (rowNormSq (Node := Node) (noise t))
  have hB_nonneg : 0 ≤ B := mul_nonneg halpha_nonneg hnoise_norm_nonneg
  have hcoord :
      ∀ a : Idx,
        |quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise t a -
            quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad 0 i0 noise t a| ≤ B := by
    intro a
    cases a with
    | inl i =>
        have hcoord_noise :
            |noise t i| ≤ rowEuclideanNorm (Node := Node) (noise t) :=
          rowVector_coordinate_abs_le_rowEuclideanNorm
            (Node := Node) (noise t) i
        calc
          |quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise t (Sum.inl i) -
            quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad 0 i0 noise t (Sum.inl i)| =
              alpha * |noise t i| := by
                simp [quadraticRestrictedNoiseInnovationCoord,
                  restrictedStateToCoord, abs_mul,
                  abs_of_nonneg halpha_nonneg]
          _ ≤ B := by
              dsimp [B]
              exact mul_le_mul_of_nonneg_left hcoord_noise
                (show 0 ≤ alpha from halpha_nonneg)
      | inr i =>
          simpa [quadraticRestrictedNoiseInnovationCoord, restrictedStateToCoord]
            using hB_nonneg
  calc
    rowEuclideanNorm (Node := Idx)
        (fun a =>
          quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise t a -
            quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad 0 i0 noise t a) ≤
        (nodeCount (Node := Idx) : ℝ) * B :=
      rowEuclideanNorm_le_card_mul_of_abs_le
        (Node := Idx)
        (fun a =>
          quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise t a -
            quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad 0 i0 noise t a)
        hB_nonneg hcoord
    _ =
        (nodeCount (Node := Idx) : ℝ) * alpha *
          rowEuclideanNorm (Node := Node) (noise t) := by
        dsimp [B]
        ring

/-- Raw Appendix C.1 finite-period source-envelope estimate before applying
the stable projection `(I-P)`.

This is the source-facing coefficient recursion required by the stable impulse
supplier: the true alpha-period innovation differs from the alpha-zero
tracker-only period innovation by `O(alpha)` times the one-period raw noise
window, while the alpha-zero period innovation itself is bounded by the same
window. -/
theorem quadraticRestrictedPeriodNoiseInnovationCoord_raw_source_envelope_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alpha0 deltaP : ℝ)
    (halpha0_pos : 0 < alpha0)
    (hdeltaP_pos : 0 < deltaP) :
    ∃ Craw Mraw alphaRaw : ℝ,
      0 ≤ Craw ∧ 0 ≤ Mraw ∧ 0 < alphaRaw ∧
        alphaRaw ≤ alpha0 ∧ alphaRaw ≤ deltaP ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaRaw →
            ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
              let rawα : RowVector (Sum Node {i : Node // i ≠ i0}) :=
                quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 noise k
              let raw0 : RowVector (Sum Node {i : Node // i ≠ i0}) :=
                quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda 0 i0 noise k
              rowEuclideanNorm
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (fun a => rawα a - raw0 a) ≤
                Craw * alpha *
                  quadraticRestrictedPeriodNoiseWindowEnvelope
                    (Node := Node) quad noise k ∧
              rowEuclideanNorm
                  (Node := Sum Node {i : Node // i ≠ i0}) raw0 ≤
                Mraw *
                  quadraticRestrictedPeriodNoiseWindowEnvelope
                    (Node := Node) quad noise k := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let alphaRaw : ℝ := min alpha0 deltaP
  have halphaRaw_pos : 0 < alphaRaw := by
    dsimp [alphaRaw]
    exact lt_min halpha0_pos hdeltaP_pos
  have halphaRaw_nonneg : 0 ≤ alphaRaw := halphaRaw_pos.le
  have halphaRaw_le_alpha0 : alphaRaw ≤ alpha0 := by
    dsimp [alphaRaw]
    exact min_le_left _ _
  have halphaRaw_le_deltaP : alphaRaw ≤ deltaP := by
    dsimp [alphaRaw]
    exact min_le_right _ _
  obtain ⟨Mstep, hMstep_nonneg, hMstep_bound⟩ :=
    quadraticRestrictedOneStepMatrix_uniform_operator_bound_on_Icc
      (Node := Node) quad lambda alphaRaw i0 halphaRaw_pos
  obtain ⟨M0step, hM0step_nonneg, hM0step_bound⟩ :=
    quadraticRestrictedOneStepMatrix_zero_uniform_operator_bound
      (Node := Node) quad lambda i0
  obtain ⟨Lstep, hLstep_nonneg, hLstep_bound⟩ :=
    quadraticRestrictedOneStepMatrix_sub_zero_operator_bound
      (Node := Node) quad lambda i0
  obtain ⟨Ceta, hCeta_nonneg, heta_bound⟩ :=
    quadraticRestrictedNoiseInnovationCoord_norm_le_noise
      (Node := Node) quad alphaRaw i0 halphaRaw_nonneg
  let Cdiff : ℝ := (nodeCount (Node := Idx) : ℝ)
  have hCdiff_nonneg : 0 ≤ Cdiff := by
    dsimp [Cdiff]
    positivity
  let Mraw : ℝ :=
    Finset.sum (Finset.range (quad.period + 1))
      (fun n => finiteWindowLinearBudget M0step Ceta n)
  have hMraw_nonneg : 0 ≤ Mraw := by
    dsimp [Mraw]
    exact Finset.sum_nonneg (fun n _hn =>
      finiteWindowLinearBudget_nonneg hM0step_nonneg hCeta_nonneg n)
  let Cstep : ℝ := Lstep * Mraw + Cdiff
  have hCstep_nonneg : 0 ≤ Cstep := by
    dsimp [Cstep]
    exact add_nonneg (mul_nonneg hLstep_nonneg hMraw_nonneg) hCdiff_nonneg
  let Craw : ℝ :=
    Finset.sum (Finset.range (quad.period + 1))
      (fun n => finiteWindowLinearBudget Mstep Cstep n)
  have hCraw_nonneg : 0 ≤ Craw := by
    dsimp [Craw]
    exact Finset.sum_nonneg (fun n _hn =>
      finiteWindowLinearBudget_nonneg hMstep_nonneg hCstep_nonneg n)
  refine ⟨Craw, Mraw, alphaRaw, hCraw_nonneg, hMraw_nonneg,
    halphaRaw_pos, halphaRaw_le_alpha0, halphaRaw_le_deltaP, ?_⟩
  intro alpha halpha_pos halpha_le noise k
  let E : ℝ :=
    quadraticRestrictedPeriodNoiseWindowEnvelope (Node := Node) quad noise k
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact quadraticRestrictedPeriodNoiseWindowEnvelope_nonneg
      (Node := Node) quad noise k
  have halpha_nonneg : 0 ≤ alpha := halpha_pos.le
  have halphaE_nonneg : 0 ≤ alpha * E := mul_nonneg halpha_nonneg hE_nonneg
  let Y0 : ℕ → ℝ := fun n =>
    rowEuclideanNorm (Node := Idx)
      (quadraticRestrictedConsecutiveNoiseInnovationCoord
        (Node := Node) quad lambda 0 i0 noise (k * quad.period) n)
  have hY0_bound :
      ∀ n : ℕ, n ≤ quad.period →
        Y0 n ≤ finiteWindowLinearBudget M0step Ceta n * E := by
    apply finiteWindowLinearBudget_bound_upto
      (M := M0step) (C := Ceta) (E := E) (m := quad.period)
      hM0step_nonneg hCeta_nonneg hE_nonneg Y0
    · simp [Y0, quadraticRestrictedConsecutiveNoiseInnovationCoord,
        rowEuclideanNorm, rowNormSq]
    · intro n hn
      have hnoise_single :
          rowEuclideanNorm (Node := Node)
              (noise (k * quad.period + n)) ≤ E :=
        by
          dsimp [E]
          exact quadraticRestrictedPeriodNoiseWindowEnvelope_single_le
            (Node := Node) quad noise k n hn
      have heta0 :
          rowEuclideanNorm (Node := Idx)
              (quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad 0 i0 noise (k * quad.period + n)) ≤
            Ceta * E := by
        have h1 :
            rowEuclideanNorm (Node := Idx)
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad 0 i0 noise (k * quad.period + n)) ≤
              Ceta *
                rowEuclideanNorm (Node := Node)
                  (noise (k * quad.period + n)) :=
          heta_bound 0 le_rfl (by simpa using halphaRaw_nonneg) noise
            (k * quad.period + n)
        have h2 :
            Ceta *
                rowEuclideanNorm (Node := Node)
                  (noise (k * quad.period + n)) ≤
              Ceta * E :=
          mul_le_mul_of_nonneg_left hnoise_single
            (show 0 ≤ Ceta from hCeta_nonneg)
        exact le_trans h1 h2
      have hY0_succ :
          Y0 (n + 1) ≤ M0step * Y0 n + Ceta * E := by
        have hbase :
            Y0 (n + 1) ≤
              matrixEuclideanOperatorNorm (Node := Idx)
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda 0 i0
                    (k * quad.period + n)) * Y0 n +
                rowEuclideanNorm (Node := Idx)
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad 0 i0 noise (k * quad.period + n)) := by
          simpa [Y0] using
            quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_succ_le
              (Node := Node) quad lambda 0 i0 noise (k * quad.period) n
        have hstep :
            matrixEuclideanOperatorNorm (Node := Idx)
                (quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0
                  (k * quad.period + n)) * Y0 n +
              rowEuclideanNorm (Node := Idx)
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad 0 i0 noise (k * quad.period + n)) ≤
            M0step * Y0 n +
              rowEuclideanNorm (Node := Idx)
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad 0 i0 noise (k * quad.period + n)) := by
          have hY0n_nonneg : 0 ≤ Y0 n := by
            dsimp [Y0]
            simpa [rowEuclideanNorm] using
              Real.sqrt_nonneg (rowNormSq (Node := Idx)
                (quadraticRestrictedConsecutiveNoiseInnovationCoord
                  (Node := Node) quad lambda 0 i0 noise
                  (k * quad.period) n))
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (hM0step_bound k n hn) hY0n_nonneg) le_rfl
        have heta_step :
            M0step * Y0 n +
              rowEuclideanNorm (Node := Idx)
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad 0 i0 noise (k * quad.period + n)) ≤
            M0step * Y0 n + Ceta * E := by
          exact add_le_add le_rfl heta0
        exact le_trans hbase (le_trans hstep heta_step)
      exact hY0_succ
  have hY0_Mraw :
      ∀ n : ℕ, n ≤ quad.period → Y0 n ≤ Mraw * E := by
    intro n hn
    have hbudget_le :
        finiteWindowLinearBudget M0step Ceta n ≤ Mraw :=
      by
        dsimp [Mraw]
        exact finiteWindowLinearBudget_le_sum hM0step_nonneg hCeta_nonneg
          quad.period n hn
    calc
      Y0 n ≤ finiteWindowLinearBudget M0step Ceta n * E := hY0_bound n hn
      _ ≤ Mraw * E := mul_le_mul_of_nonneg_right hbudget_le hE_nonneg
  let D : ℕ → ℝ := fun n =>
    rowEuclideanNorm (Node := Idx)
      (fun a =>
        quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise (k * quad.period) n a -
          quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda 0 i0 noise (k * quad.period) n a)
  have hD_bound :
      ∀ n : ℕ, n ≤ quad.period →
        D n ≤ finiteWindowLinearBudget Mstep Cstep n * (alpha * E) := by
    apply finiteWindowLinearBudget_bound_upto
      (M := Mstep) (C := Cstep) (E := alpha * E) (m := quad.period)
      hMstep_nonneg hCstep_nonneg halphaE_nonneg D
    · simp [D, quadraticRestrictedConsecutiveNoiseInnovationCoord,
        rowEuclideanNorm, rowNormSq]
    · intro n hn
      let yα : RowVector Idx :=
        quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise (k * quad.period) n
      let y0 : RowVector Idx :=
        quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda 0 i0 noise (k * quad.period) n
      let Aα : NodeMatrix Idx :=
        quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 (k * quad.period + n)
      let A0 : NodeMatrix Idx :=
        quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda 0 i0 (k * quad.period + n)
      let etaα : RowVector Idx :=
        quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 noise (k * quad.period + n)
      let eta0 : RowVector Idx :=
        quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad 0 i0 noise (k * quad.period + n)
      let d : RowVector Idx := fun a => yα a - y0 a
      have hnoise_single :
          rowEuclideanNorm (Node := Node)
              (noise (k * quad.period + n)) ≤ E :=
        by
          dsimp [E]
          exact quadraticRestrictedPeriodNoiseWindowEnvelope_single_le
            (Node := Node) quad noise k n hn
      have hAα_bound :
          matrixEuclideanOperatorNorm (Node := Idx) Aα ≤ Mstep := by
        dsimp [Aα]
        exact hMstep_bound alpha halpha_pos halpha_le k n hn
      have hA_diff :
          matrixEuclideanOperatorNorm (Node := Idx)
              (matrixSub (Node := Idx) Aα A0) ≤ Lstep * alpha := by
        dsimp [Aα, A0]
        exact hLstep_bound alpha halpha_nonneg k n hn
      have hy0_bound : rowEuclideanNorm (Node := Idx) y0 ≤ Mraw * E := by
        dsimp [y0]
        exact hY0_Mraw n (Nat.le_of_lt hn)
      have heta_diff :
          rowEuclideanNorm (Node := Idx) (fun a => etaα a - eta0 a) ≤
            Cdiff * alpha * E := by
        calc
          rowEuclideanNorm (Node := Idx) (fun a => etaα a - eta0 a) ≤
              Cdiff * alpha *
                rowEuclideanNorm (Node := Node)
                  (noise (k * quad.period + n)) := by
            dsimp [etaα, eta0, Cdiff]
            simpa [mul_assoc] using
              quadraticRestrictedNoiseInnovationCoord_sub_zero_norm_le_noise
                (Node := Node) quad alpha i0 halpha_nonneg noise
                (k * quad.period + n)
          _ ≤ Cdiff * alpha * E := by
            have hcoef_nonneg : 0 ≤ Cdiff * alpha :=
              mul_nonneg hCdiff_nonneg halpha_nonneg
            exact mul_le_mul_of_nonneg_left hnoise_single hcoef_nonneg
      have hprop_d :
          rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx) Aα d) ≤
            Mstep * D n := by
        calc
          rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx) Aα d) ≤
              matrixEuclideanOperatorNorm (Node := Idx) Aα *
                rowEuclideanNorm (Node := Idx) d :=
            rowEuclideanNorm_matrixMulVector_le (Node := Idx) Aα d
          _ ≤ Mstep * D n := by
            have hd_nonneg : 0 ≤ rowEuclideanNorm (Node := Idx) d := by
              dsimp [d]
              simpa [rowEuclideanNorm] using
                Real.sqrt_nonneg (rowNormSq (Node := Idx)
                  (fun a => yα a - y0 a))
            exact mul_le_mul hAα_bound (by rfl) hd_nonneg hMstep_nonneg
      have hpert_y0 :
          rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx)
                (matrixSub (Node := Idx) Aα A0) y0) ≤
            Lstep * Mraw * alpha * E := by
        calc
          rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx)
                (matrixSub (Node := Idx) Aα A0) y0) ≤
              matrixEuclideanOperatorNorm (Node := Idx)
                  (matrixSub (Node := Idx) Aα A0) *
                rowEuclideanNorm (Node := Idx) y0 :=
            rowEuclideanNorm_matrixMulVector_le
              (Node := Idx) (matrixSub (Node := Idx) Aα A0) y0
          _ ≤ (Lstep * alpha) * (Mraw * E) :=
            mul_le_mul hA_diff hy0_bound
              (by
                dsimp [y0]
                simpa [rowEuclideanNorm] using
                  Real.sqrt_nonneg (rowNormSq (Node := Idx) y0))
              (mul_nonneg hLstep_nonneg halpha_nonneg)
          _ = Lstep * Mraw * alpha * E := by ring
      have hdecomp :
          (fun a : Idx =>
            quadraticRestrictedConsecutiveNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise
                (k * quad.period) (n + 1) a -
              quadraticRestrictedConsecutiveNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise
                (k * quad.period) (n + 1) a) =
            matrixMulVector (Node := Idx) Aα d +
              matrixMulVector (Node := Idx)
                (matrixSub (Node := Idx) Aα A0) y0 +
              (fun a : Idx => etaα a - eta0 a) := by
        funext a
        have hd_apply :
            matrixMulVector (Node := Idx) Aα d a =
              matrixMulVector (Node := Idx) Aα yα a -
                matrixMulVector (Node := Idx) Aα y0 a := by
          simpa [d] using
            congrFun (matrixMulVector_sub_vector (Node := Idx) Aα yα y0) a
        have hsub_apply :
            matrixMulVector (Node := Idx)
                (matrixSub (Node := Idx) Aα A0) y0 a =
              matrixMulVector (Node := Idx) Aα y0 a -
                matrixMulVector (Node := Idx) A0 y0 a := by
          simpa using
            congrFun (matrixMulVector_matrixSub (Node := Idx) Aα A0 y0) a
        simp [quadraticRestrictedConsecutiveNoiseInnovationCoord, yα, y0,
          Aα, A0, etaα, eta0]
        rw [hd_apply, hsub_apply]
        ring
      have htri :
          D (n + 1) ≤
            Mstep * D n + Cstep * (alpha * E) := by
          calc
            D (n + 1) =
                rowEuclideanNorm (Node := Idx)
                  (matrixMulVector (Node := Idx) Aα d +
                    (matrixMulVector (Node := Idx)
                      (matrixSub (Node := Idx) Aα A0) y0 +
                      (fun a : Idx => etaα a - eta0 a))) := by
                change
                  rowEuclideanNorm (Node := Idx)
                    (fun a : Idx =>
                      quadraticRestrictedConsecutiveNoiseInnovationCoord
                          (Node := Node) quad lambda alpha i0 noise
                          (k * quad.period) (n + 1) a -
                        quadraticRestrictedConsecutiveNoiseInnovationCoord
                          (Node := Node) quad lambda 0 i0 noise
                          (k * quad.period) (n + 1) a) =
                    rowEuclideanNorm (Node := Idx)
                      (matrixMulVector (Node := Idx) Aα d +
                        (matrixMulVector (Node := Idx)
                          (matrixSub (Node := Idx) Aα A0) y0 +
                          (fun a : Idx => etaα a - eta0 a)))
                rw [hdecomp]
                simp [Pi.add_apply, add_assoc]
          _ ≤
              rowEuclideanNorm (Node := Idx)
                  (matrixMulVector (Node := Idx) Aα d) +
                rowEuclideanNorm (Node := Idx)
                  (matrixMulVector (Node := Idx)
                    (matrixSub (Node := Idx) Aα A0) y0 +
                    (fun a : Idx => etaα a - eta0 a)) :=
              rowEuclideanNorm_add_le (Node := Idx) _ _
          _ ≤
              rowEuclideanNorm (Node := Idx)
                  (matrixMulVector (Node := Idx) Aα d) +
                (rowEuclideanNorm (Node := Idx)
                    (matrixMulVector (Node := Idx)
                      (matrixSub (Node := Idx) Aα A0) y0) +
                  rowEuclideanNorm (Node := Idx)
                    (fun a : Idx => etaα a - eta0 a)) := by
              exact add_le_add le_rfl (rowEuclideanNorm_add_le (Node := Idx) _ _)
          _ ≤ Mstep * D n +
                (Lstep * Mraw * alpha * E + Cdiff * alpha * E) :=
              add_le_add hprop_d (add_le_add hpert_y0 heta_diff)
          _ = Mstep * D n + Cstep * (alpha * E) := by
              dsimp [Cstep]
              ring
      exact htri
  have hraw0_period :
      rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda 0 i0 noise k) ≤
        Mraw * E := by
    simpa [quadraticRestrictedPeriodNoiseInnovationCoord, Y0, E, Idx] using
      hY0_Mraw quad.period le_rfl
  have hrawdiff_period :
      rowEuclideanNorm (Node := Idx)
          (fun a =>
            quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise k a -
              quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise k a) ≤
        Craw * alpha * E := by
    have hD_period := hD_bound quad.period le_rfl
    have hbudget_le :
        finiteWindowLinearBudget Mstep Cstep quad.period ≤ Craw := by
      dsimp [Craw]
      exact finiteWindowLinearBudget_le_sum hMstep_nonneg hCstep_nonneg
        quad.period quad.period le_rfl
    calc
      rowEuclideanNorm (Node := Idx)
          (fun a =>
            quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise k a -
              quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise k a) =
          D quad.period := by
            simp [D, quadraticRestrictedPeriodNoiseInnovationCoord, Idx]
      _ ≤ finiteWindowLinearBudget Mstep Cstep quad.period * (alpha * E) :=
          hD_period
      _ ≤ Craw * (alpha * E) :=
          mul_le_mul_of_nonneg_right hbudget_le halphaE_nonneg
      _ = Craw * alpha * E := by ring
  constructor
  · simpa [Idx, E] using hrawdiff_period
  · simpa [Idx, E] using hraw0_period

/-- Appendix C.1 period-innovation input comparison at the raw source envelope.

This replaces the retired relative route by the formula-level obligation
actually used in the paper's step-4 impulse estimate: the projected
alpha-period innovation is alpha-close to the alpha-zero tracker-only
innovation, and the alpha-zero input has a geometrically propagated orbit,
both against the finite window of raw node-noise norms. -/
theorem quadraticRestrictedStableComplement_periodInnovation_source_envelope_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alpha0 theta K deltaP LP : ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (halpha0_pos : 0 < alpha0)
    (hdeltaP_pos : 0 < deltaP)
    (hLP_nonneg : 0 ≤ LP)
    (hpower0 :
      ∀ j : ℕ,
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower
              (Node := Sum Node {i : Node // i ≠ i0})
              (F 0) j) ≤
          K * theta ^ j)
    (hP_lip :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ deltaP →
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixSub
              (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha) (P 0)) ≤
          LP * alpha) :
    ∃ Cxi Mxi alphaXi : ℝ,
      0 ≤ Cxi ∧ 0 ≤ Mxi ∧ 0 < alphaXi ∧ alphaXi ≤ alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
          ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
            let rawα : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise k
            let raw0 : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise k
            let xα : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P alpha) rawα
            let xbase : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P 0) raw0
            rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0})
                (fun a => xα a - xbase a) ≤
              Cxi * alpha *
                quadraticRestrictedPeriodNoiseWindowEnvelope
                  (Node := Node) quad noise k ∧
            ∀ n : ℕ,
              rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0})
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (matrixPower
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (F 0) n) xbase) ≤
                (K * theta ^ n) *
                  (Mxi *
                    quadraticRestrictedPeriodNoiseWindowEnvelope
                      (Node := Node) quad noise k) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hraw_period :
      ∃ Craw Mraw alphaRaw : ℝ,
        0 ≤ Craw ∧ 0 ≤ Mraw ∧ 0 < alphaRaw ∧
          alphaRaw ≤ alpha0 ∧ alphaRaw ≤ deltaP ∧
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaRaw →
              ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
                let rawα : RowVector Idx :=
                  quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0 noise k
                let raw0 : RowVector Idx :=
                  quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda 0 i0 noise k
                rowEuclideanNorm (Node := Idx) (fun a => rawα a - raw0 a) ≤
                    Craw * alpha *
                      quadraticRestrictedPeriodNoiseWindowEnvelope
                        (Node := Node) quad noise k ∧
                  rowEuclideanNorm (Node := Idx) raw0 ≤
                    Mraw *
                      quadraticRestrictedPeriodNoiseWindowEnvelope
                        (Node := Node) quad noise k := by
    simpa [Idx] using
      quadraticRestrictedPeriodNoiseInnovationCoord_raw_source_envelope_bound
        (Node := Node) quad lambda i0 alpha0 deltaP
        halpha0_pos hdeltaP_pos
  rcases hraw_period with
    ⟨Craw, Mraw, alphaRaw, hCraw_nonneg, hMraw_nonneg, halphaRaw_pos,
      halphaRaw_le_alpha0, halphaRaw_le_deltaP, hraw_period⟩
  let P0op : ℝ :=
    matrixEuclideanOperatorNorm (Node := Idx) (P 0)
  have hP0op_nonneg : 0 ≤ P0op := by
    dsimp [P0op]
    exact (matrixEuclideanOperatorNorm_spec (Node := Idx) (P 0)).1
  let stableP0op : ℝ := 1 + P0op
  have hstableP0op_nonneg : 0 ≤ stableP0op := by
    dsimp [stableP0op]
    positivity
  let projectedDiffGain : ℝ := 1 + P0op + LP * alphaRaw
  have hprojectedDiffGain_nonneg : 0 ≤ projectedDiffGain := by
    dsimp [projectedDiffGain]
    positivity
  let Cxi : ℝ := Craw * projectedDiffGain + LP * Mraw
  let Mxi : ℝ := stableP0op * Mraw
  let alphaXi : ℝ := alphaRaw
  have hCxi_nonneg : 0 ≤ Cxi := by
    dsimp [Cxi]
    exact add_nonneg
      (mul_nonneg hCraw_nonneg hprojectedDiffGain_nonneg)
      (mul_nonneg hLP_nonneg hMraw_nonneg)
  have hMxi_nonneg : 0 ≤ Mxi := by
    dsimp [Mxi]
    exact mul_nonneg hstableP0op_nonneg hMraw_nonneg
  refine ⟨Cxi, Mxi, alphaXi, hCxi_nonneg, hMxi_nonneg,
    halphaRaw_pos, halphaRaw_le_alpha0, ?_⟩
  intro alpha halpha_pos halpha_le noise k
  have halpha_le_deltaP : alpha ≤ deltaP :=
    le_trans halpha_le halphaRaw_le_deltaP
  let rawα : RowVector Idx :=
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 noise k
  let raw0 : RowVector Idx :=
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda 0 i0 noise k
  let xα : RowVector Idx :=
    spectralStableComplementVector (Node := Idx) (P alpha) rawα
  let xbase : RowVector Idx :=
    spectralStableComplementVector (Node := Idx) (P 0) raw0
  let E : ℝ :=
    quadraticRestrictedPeriodNoiseWindowEnvelope (Node := Node) quad noise k
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact quadraticRestrictedPeriodNoiseWindowEnvelope_nonneg
      (Node := Node) quad noise k
  have hraw := hraw_period alpha halpha_pos halpha_le noise k
  have hrawdiff :
      rowEuclideanNorm (Node := Idx) (fun a => rawα a - raw0 a) ≤
        Craw * alpha * E := by
    simpa [Idx, rawα, raw0, E] using hraw.1
  have hraw0 :
      rowEuclideanNorm (Node := Idx) raw0 ≤ Mraw * E := by
    simpa [Idx, raw0, E] using hraw.2
  have hPdiff :
      matrixEuclideanOperatorNorm (Node := Idx)
          (matrixSub (Node := Idx) (P 0) (P alpha)) ≤
        LP * alpha :=
    matrixEuclideanOperatorNorm_matrixSub_comm_le
      (Node := Idx) (P alpha) (P 0)
      (hP_lip alpha halpha_pos.le halpha_le_deltaP)
  have hxbase_norm :
      rowEuclideanNorm (Node := Idx) xbase ≤ Mxi * E := by
    have hP0raw :
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx) (P 0) raw0) ≤
          P0op * rowEuclideanNorm (Node := Idx) raw0 :=
      rowEuclideanNorm_matrixMulVector_le (Node := Idx) (P 0) raw0
    have hstable_raw :
        rowEuclideanNorm (Node := Idx) xbase ≤
          rowEuclideanNorm (Node := Idx) raw0 +
            rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx) (P 0) raw0) := by
      simpa [xbase, spectralStableComplementVector] using
        rowEuclideanNorm_sub_le
          (Node := Idx) raw0
          (matrixMulVector (Node := Idx) (P 0) raw0)
    calc
      rowEuclideanNorm (Node := Idx) xbase ≤
          rowEuclideanNorm (Node := Idx) raw0 +
            rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx) (P 0) raw0) := hstable_raw
      _ ≤ rowEuclideanNorm (Node := Idx) raw0 +
            P0op * rowEuclideanNorm (Node := Idx) raw0 :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hP0raw (rowEuclideanNorm (Node := Idx) raw0)
      _ = stableP0op * rowEuclideanNorm (Node := Idx) raw0 := by
          dsimp [stableP0op]
          ring
      _ ≤ stableP0op * (Mraw * E) :=
          mul_le_mul_of_nonneg_left hraw0 hstableP0op_nonneg
      _ = Mxi * E := by
          dsimp [Mxi]
          ring
  constructor
  · have hrawdiff_nonneg :
        0 ≤ rowEuclideanNorm (Node := Idx) (fun a => rawα a - raw0 a) := by
      simpa [rowEuclideanNorm] using
        Real.sqrt_nonneg (rowNormSq (Node := Idx)
          (fun a => rawα a - raw0 a))
    have hraw0_nonneg :
        0 ≤ rowEuclideanNorm (Node := Idx) raw0 := by
      simpa [rowEuclideanNorm] using
        Real.sqrt_nonneg (rowNormSq (Node := Idx) raw0)
    let d : RowVector Idx := fun a => rawα a - raw0 a
    have hP0d :
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx) (P 0) d) ≤
          P0op * rowEuclideanNorm (Node := Idx) d :=
      rowEuclideanNorm_matrixMulVector_le (Node := Idx) (P 0) d
    have hPdiffd :
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx)
              (matrixSub (Node := Idx) (P alpha) (P 0)) d) ≤
          LP * alpha * rowEuclideanNorm (Node := Idx) d := by
      calc
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx)
              (matrixSub (Node := Idx) (P alpha) (P 0)) d) ≤
            matrixEuclideanOperatorNorm (Node := Idx)
                (matrixSub (Node := Idx) (P alpha) (P 0)) *
              rowEuclideanNorm (Node := Idx) d :=
            rowEuclideanNorm_matrixMulVector_le
              (Node := Idx) (matrixSub (Node := Idx) (P alpha) (P 0)) d
        _ ≤ (LP * alpha) * rowEuclideanNorm (Node := Idx) d :=
            mul_le_mul_of_nonneg_right
              (hP_lip alpha halpha_pos.le halpha_le_deltaP)
              (by
                dsimp [d]
                simpa [rowEuclideanNorm] using
                  Real.sqrt_nonneg (rowNormSq (Node := Idx)
                    (fun a => rawα a - raw0 a)))
        _ = LP * alpha * rowEuclideanNorm (Node := Idx) d := by ring
    have hPalphad :
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx) (P alpha) d) ≤
          (P0op + LP * alphaRaw) *
            rowEuclideanNorm (Node := Idx) d := by
      have hdecomp :
          matrixMulVector (Node := Idx) (P alpha) d =
            matrixMulVector (Node := Idx) (P 0) d +
              matrixMulVector (Node := Idx)
                (matrixSub (Node := Idx) (P alpha) (P 0)) d := by
        funext a
        simp [matrixMulVector, matrixSub, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, add_mul, sub_mul]
      have htri :
          rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx) (P alpha) d) ≤
            rowEuclideanNorm (Node := Idx)
                (matrixMulVector (Node := Idx) (P 0) d) +
              rowEuclideanNorm (Node := Idx)
                (matrixMulVector (Node := Idx)
                  (matrixSub (Node := Idx) (P alpha) (P 0)) d) := by
        rw [hdecomp]
        exact rowEuclideanNorm_add_le (Node := Idx) _ _
      have hdiff_alphaRaw :
          LP * alpha * rowEuclideanNorm (Node := Idx) d ≤
            LP * alphaRaw * rowEuclideanNorm (Node := Idx) d := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left halpha_le hLP_nonneg)
          (by
            dsimp [d]
            simpa [rowEuclideanNorm] using
              Real.sqrt_nonneg (rowNormSq (Node := Idx)
                (fun a => rawα a - raw0 a)))
      calc
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx) (P alpha) d) ≤
            rowEuclideanNorm (Node := Idx)
                (matrixMulVector (Node := Idx) (P 0) d) +
              rowEuclideanNorm (Node := Idx)
                (matrixMulVector (Node := Idx)
                  (matrixSub (Node := Idx) (P alpha) (P 0)) d) := htri
        _ ≤ P0op * rowEuclideanNorm (Node := Idx) d +
              LP * alpha * rowEuclideanNorm (Node := Idx) d :=
            add_le_add hP0d hPdiffd
        _ ≤ P0op * rowEuclideanNorm (Node := Idx) d +
              LP * alphaRaw * rowEuclideanNorm (Node := Idx) d :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hdiff_alphaRaw
                  (P0op * rowEuclideanNorm (Node := Idx) d)
        _ = (P0op + LP * alphaRaw) *
              rowEuclideanNorm (Node := Idx) d := by ring
    have hstable_d :
        rowEuclideanNorm (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha) d) ≤
          projectedDiffGain * rowEuclideanNorm (Node := Idx) d := by
      have htri :
          rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha) d) ≤
            rowEuclideanNorm (Node := Idx) d +
              rowEuclideanNorm (Node := Idx)
                (matrixMulVector (Node := Idx) (P alpha) d) := by
        simpa [spectralStableComplementVector] using
          rowEuclideanNorm_sub_le
            (Node := Idx) d
            (matrixMulVector (Node := Idx) (P alpha) d)
      calc
        rowEuclideanNorm (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha) d) ≤
          rowEuclideanNorm (Node := Idx) d +
            rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx) (P alpha) d) := htri
        _ ≤ rowEuclideanNorm (Node := Idx) d +
              (P0op + LP * alphaRaw) *
                rowEuclideanNorm (Node := Idx) d :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hPalphad
                  (rowEuclideanNorm (Node := Idx) d)
        _ = projectedDiffGain * rowEuclideanNorm (Node := Idx) d := by
            dsimp [projectedDiffGain]
            ring
    have hsecond :
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx)
              (matrixSub (Node := Idx) (P 0) (P alpha)) raw0) ≤
          LP * Mraw * alpha * E := by
      calc
        rowEuclideanNorm (Node := Idx)
            (matrixMulVector (Node := Idx)
              (matrixSub (Node := Idx) (P 0) (P alpha)) raw0) ≤
            matrixEuclideanOperatorNorm (Node := Idx)
                (matrixSub (Node := Idx) (P 0) (P alpha)) *
              rowEuclideanNorm (Node := Idx) raw0 :=
            rowEuclideanNorm_matrixMulVector_le
              (Node := Idx) (matrixSub (Node := Idx) (P 0) (P alpha)) raw0
        _ ≤ (LP * alpha) * (Mraw * E) :=
            mul_le_mul hPdiff hraw0 hraw0_nonneg
              (mul_nonneg hLP_nonneg halpha_pos.le)
        _ = LP * Mraw * alpha * E := by ring
    have hdecomp :
        (fun a : Idx => xα a - xbase a) =
          spectralStableComplementVector (Node := Idx) (P alpha) d +
            matrixMulVector (Node := Idx)
              (matrixSub (Node := Idx) (P 0) (P alpha)) raw0 := by
      funext a
      have hsum_split :
          (∑ x : Idx, P alpha a x * (rawα x - raw0 x)) =
            (∑ x : Idx, P alpha a x * rawα x) -
              ∑ x : Idx, P alpha a x * raw0 x := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      simp [xα, xbase, d, spectralStableComplementVector, matrixMulVector,
        matrixSub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        add_mul, sub_mul]
      rw [hsum_split]
      ring
    have hdiff_bound :
        rowEuclideanNorm (Node := Idx) (fun a => xα a - xbase a) ≤
          projectedDiffGain * (Craw * alpha * E) +
            LP * Mraw * alpha * E := by
      calc
        rowEuclideanNorm (Node := Idx) (fun a => xα a - xbase a) =
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha) d +
                matrixMulVector (Node := Idx)
                  (matrixSub (Node := Idx) (P 0) (P alpha)) raw0) := by
              rw [hdecomp]
        _ ≤ rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha) d) +
            rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx)
                (matrixSub (Node := Idx) (P 0) (P alpha)) raw0) :=
            rowEuclideanNorm_add_le (Node := Idx) _ _
        _ ≤ projectedDiffGain * rowEuclideanNorm (Node := Idx) d +
              LP * Mraw * alpha * E :=
            add_le_add hstable_d hsecond
        _ ≤ projectedDiffGain * (Craw * alpha * E) +
              LP * Mraw * alpha * E :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right
                  (mul_le_mul_of_nonneg_left
                    (by simpa [d] using hrawdiff) hprojectedDiffGain_nonneg)
                  (LP * Mraw * alpha * E)
    calc
      rowEuclideanNorm (Node := Idx) (fun a => xα a - xbase a) ≤
          projectedDiffGain * (Craw * alpha * E) +
            LP * Mraw * alpha * E := hdiff_bound
      _ = Cxi * alpha * E := by
          dsimp [Cxi]
          ring
  · intro n
    exact matrixPower_action_norm_bound (Node := Idx) (F 0) xbase n
      (hpower0 n) hxbase_norm

/-- Same-interface source leaf for Appendix C.1's single propagated-input
stable-output envelope.

The preceding lemmas expose the source inputs at this granularity: alpha-zero
cancellation of the stable output, base stable powers, local Lipschitz control
of `P` and `F`, and geometric absorption.  The remaining missing bridge is the
input-comparison step that relates the true alpha-projected stable inputs to
the alpha-zero cancelling inputs without replacing the source object by the
retired response-relative operator. -/
theorem quadratic_restricted_stable_output_single_impulse_leaf
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alpha0 theta K theta1 Ageo deltaP LP deltaF LF : ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (halpha0_pos : 0 < alpha0)
    (hK_nonneg : 0 ≤ K)
    (htheta_pos : 0 < theta)
    (htheta1_nonneg : 0 ≤ theta1)
    (hAgeo_nonneg : 0 ≤ Ageo)
    (hdeltaP_pos : 0 < deltaP)
    (hLP_nonneg : 0 ≤ LP)
    (hdeltaF_pos : 0 < deltaF)
    (hLF_nonneg : 0 ≤ LF)
    (hzero_init :
      ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower
              (Node := Sum Node {i : Node // i ≠ i0}) (F 0) t)
            (spectralStableComplementVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize 0).primalState noise 0,
                  (quad.withStepsize 0).trackerErrorZeroSum noise 0)))) = 0)
    (hzero_xi :
      ∀ noise : NoisePath Node ℝ, ∀ k t : ℕ,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower
              (Node := Sum Node {i : Node // i ≠ i0}) (F 0) t)
            (spectralStableComplementVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise k))) = 0)
    (hpower_alpha :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 → ∀ j : ℕ,
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower
              (Node := Sum Node {i : Node // i ≠ i0})
              (F alpha) j) ≤
          K * theta ^ j)
    (hpower0 :
      ∀ j : ℕ,
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower
              (Node := Sum Node {i : Node // i ≠ i0})
              (F 0) j) ≤
          K * theta ^ j)
    (hP_lip :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ deltaP →
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixSub
              (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha) (P 0)) ≤
          LP * alpha)
    (hF_lip :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ deltaF →
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixSub
              (Node := Sum Node {i : Node // i ≠ i0})
              (F alpha) (F 0)) ≤
          LF * alpha)
    (hgeom_absorb :
      ∀ j : ℕ, ((j : ℝ) + 1) * theta ^ j ≤ Ageo * theta1 ^ j) :
    ∃ Csingle alphaSingle : ℝ,
      0 ≤ Csingle ∧ 0 < alphaSingle ∧ alphaSingle ≤ alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaSingle →
          ∀ noise : NoisePath Node ℝ,
            let z0 : RowVector (Sum Node {i : Node // i ≠ i0}) :=
              spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState noise 0,
                    (quad.withStepsize alpha).trackerErrorZeroSum
                      noise 0))
            let xi : ℕ → RowVector (Sum Node {i : Node // i ≠ i0}) := fun j =>
              spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 noise j)
            (∀ t : ℕ,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (matrixPower
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (F alpha) t) z0)| ≤
                Csingle * alpha *
                  (theta1 ^ t *
                    (1 +
                      rowEuclideanNorm
                        (Node := Sum Node {i : Node // i ≠ i0})
                        (restrictedStateToCoord (Node := Node) i0
                          ((quad.withStepsize alpha).primalState noise 0,
                            (quad.withStepsize alpha).trackerErrorZeroSum
                              noise 0))))) ∧
              (∀ t : ℕ, ∀ j : ℕ, j ∈ Finset.range t →
                |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                    (matrixMulVector
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (matrixPower
                        (Node := Sum Node {i : Node // i ≠ i0})
                        (F alpha) (t - 1 - j)) (xi j))| ≤
                  Csingle * alpha *
                    (theta1 ^ (t - 1 - j) *
                      quadraticRestrictedPeriodNoiseWindowEnvelope
                        (Node := Node) quad noise j)) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  obtain ⟨Cinit, alphaInit, hCinit_nonneg, halphaInit_pos,
      halphaInit_le, hinit_input⟩ :=
    quadraticRestrictedStableComplement_initial_input_alpha_absolute_bound
      (Node := Node) quad i0 alpha0 deltaP LP P halpha0_pos
      hdeltaP_pos hLP_nonneg hP_lip
  obtain ⟨Cxi, Mxi, alphaXi, hCxi_nonneg, hMxi_nonneg, halphaXi_pos,
      halphaXi_le, hxi_source⟩ :=
    quadraticRestrictedStableComplement_periodInnovation_source_envelope_bound
      (Node := Node) quad lambda i0 alpha0 theta K deltaP LP P F
      halpha0_pos hdeltaP_pos hLP_nonneg hpower0 hP_lip
  let Q0 : NodeMatrix Idx :=
    matrixSub (Node := Idx) (identityMatrix (Node := Idx)) (P 0)
  let Minit : ℝ := matrixEuclideanOperatorNorm (Node := Idx) Q0
  have hMinit_nonneg : 0 ≤ Minit := by
    dsimp [Minit]
    exact (matrixEuclideanOperatorNorm_spec (Node := Idx) Q0).1
  let CinitTransfer : ℝ :=
    ((K * Cinit + (K * K * LF * Minit) / theta) * Ageo)
  let CxiTransfer : ℝ :=
    ((K * Cxi + (K * K * LF * Mxi) / theta) * Ageo)
  let Csingle : ℝ := max CinitTransfer CxiTransfer
  let alphaSingle : ℝ := min alpha0 (min alphaInit (min alphaXi deltaF))
  have halphaSingle_pos : 0 < alphaSingle := by
    dsimp [alphaSingle]
    exact lt_min halpha0_pos
      (lt_min halphaInit_pos (lt_min halphaXi_pos hdeltaF_pos))
  have halphaSingle_le_alpha0 : alphaSingle ≤ alpha0 := by
    dsimp [alphaSingle]
    exact min_le_left _ _
  have halphaSingle_le_init : alphaSingle ≤ alphaInit := by
    dsimp [alphaSingle]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have halphaSingle_le_xi : alphaSingle ≤ alphaXi := by
    dsimp [alphaSingle]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have halphaSingle_le_deltaF : alphaSingle ≤ deltaF := by
    dsimp [alphaSingle]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hCinitTransfer_nonneg : 0 ≤ CinitTransfer := by
    have hdiv_nonneg : 0 ≤ (K * K * LF * Minit) / theta := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hK_nonneg hK_nonneg)
          hLF_nonneg) hMinit_nonneg) htheta_pos.le
    dsimp [CinitTransfer]
    exact mul_nonneg (add_nonneg (mul_nonneg hK_nonneg hCinit_nonneg) hdiv_nonneg)
      hAgeo_nonneg
  have hCxiTransfer_nonneg : 0 ≤ CxiTransfer := by
    have hdiv_nonneg : 0 ≤ (K * K * LF * Mxi) / theta := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hK_nonneg hK_nonneg)
          hLF_nonneg) hMxi_nonneg) htheta_pos.le
    dsimp [CxiTransfer]
    exact mul_nonneg (add_nonneg (mul_nonneg hK_nonneg hCxi_nonneg) hdiv_nonneg)
      hAgeo_nonneg
  have hCsingle_nonneg : 0 ≤ Csingle := by
    dsimp [Csingle]
    exact le_max_of_le_left hCinitTransfer_nonneg
  refine ⟨Csingle, alphaSingle, hCsingle_nonneg, halphaSingle_pos,
    halphaSingle_le_alpha0, ?_⟩
  intro alpha halpha_pos halpha_le noise
  have halpha_le_alpha0 : alpha ≤ alpha0 :=
    le_trans halpha_le halphaSingle_le_alpha0
  have halpha_le_init : alpha ≤ alphaInit :=
    le_trans halpha_le halphaSingle_le_init
  have halpha_le_xi : alpha ≤ alphaXi :=
    le_trans halpha_le halphaSingle_le_xi
  have halpha_le_deltaF : alpha ≤ deltaF :=
    le_trans halpha_le halphaSingle_le_deltaF
  constructor
  · intro t
    let zraw : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize alpha).primalState noise 0,
          (quad.withStepsize alpha).trackerErrorZeroSum noise 0)
    let zbaseRaw : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize 0).primalState noise 0,
          (quad.withStepsize 0).trackerErrorZeroSum noise 0)
    let zα : RowVector Idx :=
      spectralStableComplementVector (Node := Idx) (P alpha) zraw
    let zbase : RowVector Idx :=
      spectralStableComplementVector (Node := Idx) (P 0) zbaseRaw
    let Einit : ℝ := 1 + rowEuclideanNorm (Node := Idx) zraw
    have hEinit_nonneg : 0 ≤ Einit := by
      dsimp [Einit]
      have hnorm_nonneg : 0 ≤ rowEuclideanNorm (Node := Idx) zraw := by
        simpa [rowEuclideanNorm] using
          Real.sqrt_nonneg (rowNormSq (Node := Idx) zraw)
      linarith
    have hinit_lip :
        rowEuclideanNorm (Node := Idx) (fun a => zα a - zbase a) ≤
          Cinit * alpha * Einit := by
      have hraw := hinit_input alpha halpha_pos halpha_le_init noise
      have hcoef_nonneg : 0 ≤ Cinit * alpha :=
        mul_nonneg hCinit_nonneg halpha_pos.le
      have hone_le : 1 ≤ Einit := by
        dsimp [Einit]
        have hnorm_nonneg : 0 ≤ rowEuclideanNorm (Node := Idx) zraw := by
          simpa [rowEuclideanNorm] using
            Real.sqrt_nonneg (rowNormSq (Node := Idx) zraw)
        linarith
      calc
        rowEuclideanNorm (Node := Idx) (fun a => zα a - zbase a) ≤
            Cinit * alpha := by
              simpa [Idx, zα, zbase, zraw, zbaseRaw] using hraw
        _ = Cinit * alpha * 1 := by ring
        _ ≤ Cinit * alpha * Einit :=
            mul_le_mul_of_nonneg_left hone_le hcoef_nonneg
    have hzbase_input :
        rowEuclideanNorm (Node := Idx) zbase ≤ Minit * Einit := by
      have hzbase_eq :
          zbase =
            matrixMulVector (Node := Idx) Q0 zbaseRaw := by
        simpa [zbase, Q0] using
          spectralStableComplementVector_eq_matrixSub
            (Node := Idx) (P 0) zbaseRaw
      have hraw_eq : zbaseRaw = zraw := by
        funext a
        cases a with
        | inl i =>
            simp [zbaseRaw, zraw, restrictedStateToCoord, withStepsize,
              primalState_zero, initialPrimal]
        | inr j =>
            simp [zbaseRaw, zraw, restrictedStateToCoord, withStepsize,
              trackerErrorZeroSum, trackerError, trackerState_zero,
              oracleTable]
      have hnorm_zbase :
          rowEuclideanNorm (Node := Idx) zbase ≤
            Minit * rowEuclideanNorm (Node := Idx) zraw := by
        calc
          rowEuclideanNorm (Node := Idx) zbase =
              rowEuclideanNorm (Node := Idx)
                (matrixMulVector (Node := Idx) Q0 zbaseRaw) := by
                rw [hzbase_eq]
          _ ≤ Minit * rowEuclideanNorm (Node := Idx) zbaseRaw :=
                rowEuclideanNorm_matrixMulVector_le (Node := Idx) Q0 zbaseRaw
          _ = Minit * rowEuclideanNorm (Node := Idx) zraw := by rw [hraw_eq]
      have hnorm_le_E :
          rowEuclideanNorm (Node := Idx) zraw ≤ Einit := by
        dsimp [Einit]
        linarith [show 0 ≤ rowEuclideanNorm (Node := Idx) zraw by
          simpa [rowEuclideanNorm] using
            Real.sqrt_nonneg (rowNormSq (Node := Idx) zraw)]
      exact le_trans hnorm_zbase
        (mul_le_mul_of_nonneg_left hnorm_le_E hMinit_nonneg)
    have hbase_orbit :
        ∀ n : ℕ,
          rowEuclideanNorm (Node := Idx)
              (matrixMulVector (Node := Idx)
                (matrixPower (Node := Idx) (F 0) n) zbase) ≤
            (K * theta ^ n) * (Minit * Einit) := by
      intro n
      exact matrixPower_action_norm_bound (Node := Idx) (F 0) zbase n
        (hpower0 n) hzbase_input
    have htransfer :=
      quadraticRestrictedPrimalAverageOutput_single_input_geometric_of_lipschitz
        (Node := Node) i0 F zα zbase t
        (K := K) (theta := theta) (LF := LF) (LB := Cinit)
        (MB := Minit) (alpha := alpha) (theta1 := theta1)
        (Ageo := Ageo) (E := Einit)
        hK_nonneg htheta_pos hLF_nonneg hCinit_nonneg hMinit_nonneg
        halpha_pos.le htheta1_nonneg hEinit_nonneg hAgeo_nonneg
        (hpower_alpha alpha halpha_pos halpha_le_alpha0)
        (hF_lip alpha halpha_pos.le halpha_le_deltaF)
        hinit_lip hbase_orbit
        (by simpa [Idx, zbase, zbaseRaw] using hzero_init noise t)
        hgeom_absorb
    have htheta_term_nonneg : 0 ≤ theta1 ^ t :=
      pow_nonneg htheta1_nonneg t
    have hrawnorm_nonneg :
        0 ≤ rowEuclideanNorm (Node := Idx) zraw := by
      simpa [rowEuclideanNorm] using
        Real.sqrt_nonneg (rowNormSq (Node := Idx) zraw)
    have hcoef_le : CinitTransfer ≤ Csingle := le_max_left _ _
    have hfactor_nonneg :
        0 ≤ alpha * (theta1 ^ t *
          rowEuclideanNorm (Node := Idx) zraw) := by positivity
    calc
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx)
            (matrixPower (Node := Idx) (F alpha) t) zα)| ≤
          CinitTransfer * alpha * (theta1 ^ t * Einit) := by
            simpa [CinitTransfer, Idx] using htransfer
      _ ≤ Csingle * alpha * (theta1 ^ t * Einit) := by
            have hcoef_alpha :
                CinitTransfer * alpha ≤ Csingle * alpha :=
              mul_le_mul_of_nonneg_right hcoef_le halpha_pos.le
            exact mul_le_mul_of_nonneg_right hcoef_alpha
              (mul_nonneg htheta_term_nonneg hEinit_nonneg)
      _ ≤ Csingle * alpha *
            (theta1 ^ t *
              (1 + rowEuclideanNorm (Node := Idx) zraw)) := by rfl
      _ =
          Csingle * alpha *
            (theta1 ^ t *
              (1 + rowEuclideanNorm (Node := Idx) zraw)) := rfl
      _ = Csingle * alpha *
            (theta1 ^ t * Einit) := by rfl
      _ ≤ Csingle * alpha *
            (theta1 ^ t *
              (1 + rowEuclideanNorm (Node := Idx) zraw)) := by rfl
  · intro t j hj
    let rawα : RowVector Idx :=
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise j
    let raw0 : RowVector Idx :=
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda 0 i0 noise j
    let xα : RowVector Idx :=
      spectralStableComplementVector (Node := Idx) (P alpha) rawα
    let xbase : RowVector Idx :=
      spectralStableComplementVector (Node := Idx) (P 0) raw0
    let E : ℝ :=
      quadraticRestrictedPeriodNoiseWindowEnvelope (Node := Node) quad noise j
    have hxi := hxi_source alpha halpha_pos halpha_le_xi noise j
    have hE_nonneg : 0 ≤ E := by
      dsimp [E]
      exact quadraticRestrictedPeriodNoiseWindowEnvelope_nonneg
        (Node := Node) quad noise j
    have htransfer :=
      quadraticRestrictedPrimalAverageOutput_single_input_geometric_of_lipschitz
        (Node := Node) i0 F xα xbase (t - 1 - j)
        (K := K) (theta := theta) (LF := LF) (LB := Cxi)
        (MB := Mxi) (alpha := alpha) (theta1 := theta1)
        (Ageo := Ageo) (E := E)
        hK_nonneg htheta_pos hLF_nonneg hCxi_nonneg hMxi_nonneg
        halpha_pos.le htheta1_nonneg hE_nonneg hAgeo_nonneg
        (hpower_alpha alpha halpha_pos halpha_le_alpha0)
        (hF_lip alpha halpha_pos.le halpha_le_deltaF)
        (by simpa [Idx, rawα, raw0, xα, xbase, E] using hxi.1)
        (by simpa [Idx, rawα, raw0, xα, xbase, E] using hxi.2)
        (by simpa [Idx, raw0, xbase] using hzero_xi noise j (t - 1 - j))
        hgeom_absorb
    have hcoef_le : CxiTransfer ≤ Csingle := le_max_right _ _
    calc
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx)
            (matrixPower (Node := Idx) (F alpha) (t - 1 - j)) (xα))| ≤
          CxiTransfer * alpha * (theta1 ^ (t - 1 - j) * E) := by
            simpa [CxiTransfer, Idx] using htransfer
      _ ≤ Csingle * alpha * (theta1 ^ (t - 1 - j) * E) := by
            have htheta_pow_nonneg :
                0 ≤ theta1 ^ (t - 1 - j) :=
              pow_nonneg htheta1_nonneg (t - 1 - j)
            have hcoef_alpha :
                CxiTransfer * alpha ≤ Csingle * alpha :=
              mul_le_mul_of_nonneg_right hcoef_le halpha_pos.le
            exact mul_le_mul_of_nonneg_right hcoef_alpha
              (mul_nonneg htheta_pow_nonneg hE_nonneg)
      _ = Csingle * alpha * (theta1 ^ (t - 1 - j) *
            quadraticRestrictedPeriodNoiseWindowEnvelope
              (Node := Node) quad noise j) := by rfl

/-- Appendix C.1 source-granularity stable-output impulse bridge.

This is the paper's step-4 object, before the martingale `L²` summation: the
primal-average output of the restricted stable Duhamel response is
`O(alpha)` times a geometric impulse envelope.  Unlike the retired
response-relative leaf, this statement exposes the actual source envelope
coming from the initial boundary and period innovations. -/
theorem quadratic_restricted_stable_output_impulse_geometric_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hr0_nonneg : 0 ≤ r0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F) :
    ∃ C theta1 alphaImpulse : ℝ,
      0 ≤ C ∧ theta < theta1 ∧ theta1 < 1 ∧
        0 < alphaImpulse ∧ alphaImpulse ≤ alpha0 ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaImpulse →
            ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (quadraticRestrictedStableBoundaryResponse
                    (Node := Node) quad lambda i0 P F alpha noise t)| ≤
                C * alpha *
                  (theta1 ^ t *
                    (1 +
                      rowEuclideanNorm
                        (Node := Sum Node {i : Node // i ≠ i0})
                        (restrictedStateToCoord (Node := Node) i0
                          ((quad.withStepsize alpha).primalState noise 0,
                            (quad.withStepsize alpha).trackerErrorZeroSum
                              noise 0))) +
                    Finset.sum (Finset.range t) (fun j =>
                      theta1 ^ (t - 1 - j) *
                        quadraticRestrictedPeriodNoiseWindowEnvelope
                          (Node := Node) quad noise j)) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hzero :
      ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F 0 noise t) = 0 :=
    quadraticRestrictedPrimalAverageOutput_stableResponse_alpha_zero
      (Node := Node) quad lambda i0 r0 alpha0 theta K right left gamma P F
      hquad hP0 hright_top hleft_top hleft_bottom hsplitting
  rcases hsplitting with
    ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, _hgamma0,
      _hgamma_analytic, hP_analytic, _hderiv, hlocal⟩
  let theta1 : ℝ := (theta + 1) / 2
  have htheta_lt_theta1 : theta < theta1 := by
    dsimp [theta1]
    linarith
  have htheta1_lt_one : theta1 < 1 := by
    dsimp [theta1]
    linarith
  have htheta1_nonneg : 0 ≤ theta1 := by
    linarith [hr0_nonneg, hr0_theta, htheta_lt_theta1]
  have hbase_local :
      IsRieszProjectionAtEigenvalue (Node := Idx)
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda 0 i0) (gamma 0) (P 0) ∧
        quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0 =
          matrixAdd (Node := Idx) ((gamma 0) • P 0) (F 0) ∧
          matrixMul (Node := Idx) (P 0) (F 0) = 0 ∧
            matrixMul (Node := Idx) (F 0) (P 0) = 0 ∧
              ∀ j : ℕ,
                matrixEuclideanOperatorNorm (Node := Idx)
                    (matrixPower (Node := Idx) (F 0) j) ≤
                  K * theta ^ j := by
    simpa [Idx] using hlocal 0
      (by simpa [abs_of_nonneg halpha0_pos.le] using halpha0_pos.le)
  have hpower0 := hbase_local.2.2.2.2
  have hP0_analytic : AnalyticAt ℝ P 0 :=
    hP_analytic 0 (by simpa using halpha0_pos)
  obtain ⟨deltaP, LP, hdeltaP_pos, hLP_nonneg, hP_lip⟩ :=
    analyticAt_matrix_operator_norm_sub_le_mul_near_zero
      (Node := Idx) P hP0_analytic
  have hanalytic_restricted :
      RealAnalyticMatrixFamilyNear
        (Node := Idx)
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0) 1 :=
    quadraticRestrictedPeriodMatrix_analytic_near_zero
      (Node := Node) quad lambda i0
  obtain ⟨deltaF, LF, hdeltaF_pos, hLF_nonneg, hF_lip⟩ :
      ∃ δ LF : ℝ, 0 < δ ∧ 0 ≤ LF ∧
        ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δ →
          matrixEuclideanOperatorNorm
              (Node := Idx)
              (matrixSub (Node := Idx) (F alpha) (F 0)) ≤
            LF * alpha :=
    spectralSplitting_stableComplement_local_operator_lipschitz_at_zero
      (Node := Idx)
      (fun alpha : ℝ =>
        quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
      1 r0 alpha0 theta K right left gamma P F
      hanalytic_restricted
      ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, _hgamma0,
        _hgamma_analytic, hP_analytic, _hderiv, hlocal⟩
  have htheta_pos : 0 < theta := lt_of_le_of_lt hr0_nonneg hr0_theta
  obtain ⟨Ageo, hAgeo_nonneg, hgeom_absorb⟩ :=
    one_plus_nat_mul_geometric_absorb
      (theta := theta) (theta1 := theta1) htheta_pos htheta_lt_theta1
  have hsource_target :
      ∃ C theta1 alphaImpulse : ℝ,
        0 ≤ C ∧ theta < theta1 ∧ theta1 < 1 ∧
          0 < alphaImpulse ∧ alphaImpulse ≤ alpha0 ∧
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaImpulse →
              ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
                |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                    (quadraticRestrictedStableBoundaryResponse
                      (Node := Node) quad lambda i0 P F alpha noise t)| ≤
                  C * alpha *
                    (theta1 ^ t *
                      (1 +
                        rowEuclideanNorm (Node := Idx)
                          (restrictedStateToCoord (Node := Node) i0
                            ((quad.withStepsize alpha).primalState noise 0,
                              (quad.withStepsize alpha).trackerErrorZeroSum
                                noise 0))) +
                      Finset.sum (Finset.range t) (fun j =>
                        theta1 ^ (t - 1 - j) *
                        quadraticRestrictedPeriodNoiseWindowEnvelope
                          (Node := Node) quad noise j)) := by
    have hsingle_impulse_leaf :
        ∃ Csingle alphaSingle : ℝ,
          0 ≤ Csingle ∧ 0 < alphaSingle ∧ alphaSingle ≤ alpha0 ∧
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaSingle →
              ∀ noise : NoisePath Node ℝ,
                let z0 : RowVector Idx :=
                  spectralStableComplementVector (Node := Idx) (P alpha)
                    (restrictedStateToCoord (Node := Node) i0
                      ((quad.withStepsize alpha).primalState noise 0,
                        (quad.withStepsize alpha).trackerErrorZeroSum
                          noise 0))
                let xi : ℕ → RowVector Idx := fun j =>
                  spectralStableComplementVector (Node := Idx) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0 noise j)
                (∀ t : ℕ,
                  |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (matrixMulVector (Node := Idx)
                        (matrixPower (Node := Idx) (F alpha) t) z0)| ≤
                    Csingle * alpha *
                      (theta1 ^ t *
                        (1 +
                          rowEuclideanNorm (Node := Idx)
                            (restrictedStateToCoord (Node := Node) i0
                              ((quad.withStepsize alpha).primalState noise 0,
                                (quad.withStepsize alpha).trackerErrorZeroSum
                                  noise 0))))) ∧
                  (∀ t : ℕ, ∀ j : ℕ, j ∈ Finset.range t →
                    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                        (matrixMulVector (Node := Idx)
                          (matrixPower (Node := Idx) (F alpha)
                            (t - 1 - j)) (xi j))| ≤
                      Csingle * alpha *
                        (theta1 ^ (t - 1 - j) *
                          quadraticRestrictedPeriodNoiseWindowEnvelope
                            (Node := Node) quad noise j)) := by
      have hzero_init_single :
          ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (matrixPower
                  (Node := Sum Node {i : Node // i ≠ i0}) (F 0) t)
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize 0).primalState noise 0,
                      (quad.withStepsize 0).trackerErrorZeroSum noise 0)))) = 0 := by
        intro noise t
        exact
          quadraticRestrictedStableComplement_initial_single_output_alpha_zero
            (Node := Node) quad lambda i0 r0 alpha0 theta K
            right left gamma P F hP0 hright_top hleft_top hleft_bottom
            ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, _hgamma0,
              _hgamma_analytic, hP_analytic, _hderiv, hlocal⟩ noise t
      have hzero_xi_single :
          ∀ noise : NoisePath Node ℝ, ∀ k t : ℕ,
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (matrixPower
                  (Node := Sum Node {i : Node // i ≠ i0}) (F 0) t)
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda 0 i0 noise k))) = 0 := by
        intro noise k t
        exact
          quadraticRestrictedStableComplement_periodInnovation_single_output_alpha_zero
            (Node := Node) quad lambda i0 r0 alpha0 theta K
            right left gamma P F hP0 hright_top hleft_top hleft_bottom
            ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, _hgamma0,
              _hgamma_analytic, hP_analytic, _hderiv, hlocal⟩ noise k t
      have hpower_alpha :
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 → ∀ j : ℕ,
            matrixEuclideanOperatorNorm (Node := Idx)
                (matrixPower (Node := Idx) (F alpha) j) ≤
              K * theta ^ j := by
        intro alpha halpha_pos halpha_le j
        exact (hlocal alpha
          (by simpa [Idx, abs_of_nonneg halpha_pos.le] using halpha_le)).2.2.2.2 j
      simpa [Idx] using
        quadratic_restricted_stable_output_single_impulse_leaf
          (Node := Node) quad lambda i0 alpha0 theta K theta1 Ageo
          deltaP LP deltaF LF P F halpha0_pos hK_nonneg htheta_pos
          htheta1_nonneg hAgeo_nonneg hdeltaP_pos hLP_nonneg hdeltaF_pos hLF_nonneg
          hzero_init_single hzero_xi_single hpower_alpha hpower0 hP_lip hF_lip
          hgeom_absorb
    rcases hsingle_impulse_leaf with
      ⟨Csingle, alphaSingle, hCsingle_nonneg, halphaSingle_pos,
        halphaSingle_le, hsingle⟩
    refine ⟨Csingle, theta1, alphaSingle, hCsingle_nonneg,
      htheta_lt_theta1, htheta1_lt_one, halphaSingle_pos,
      halphaSingle_le, ?_⟩
    intro alpha halpha_pos halpha_le noise t
    let z0 : RowVector Idx :=
      spectralStableComplementVector (Node := Idx) (P alpha)
        (restrictedStateToCoord (Node := Node) i0
          ((quad.withStepsize alpha).primalState noise 0,
            (quad.withStepsize alpha).trackerErrorZeroSum noise 0))
    let xi : ℕ → RowVector Idx := fun j =>
      spectralStableComplementVector (Node := Idx) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise j)
    have hsingle_alpha := hsingle alpha halpha_pos halpha_le noise
    have hinit_single :
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx)
              (matrixPower (Node := Idx) (F alpha) t) z0)| ≤
          Csingle * alpha *
            (theta1 ^ t *
              (1 +
                rowEuclideanNorm (Node := Idx)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState noise 0,
                      (quad.withStepsize alpha).trackerErrorZeroSum
                        noise 0)))) := by
      simpa [Idx, z0] using hsingle_alpha.1 t
    have hxi_single :
        ∀ j : ℕ, j ∈ Finset.range t →
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Idx)
                (matrixPower (Node := Idx) (F alpha) (t - 1 - j))
                (xi j))| ≤
            Csingle * alpha *
              (theta1 ^ (t - 1 - j) *
                quadraticRestrictedPeriodNoiseWindowEnvelope
                  (Node := Node) quad noise j) := by
      intro j hj
      simpa [Idx, xi] using hsingle_alpha.2 t j hj
    have hassembled :=
      quadraticRestrictedPrimalAverageOutput_stableDuhamel_le_of_source_envelope
        (Node := Node) i0 (F alpha) z0 xi t
        (C := Csingle) (alpha := alpha) (theta1 := theta1)
        (E0 := 1 + rowEuclideanNorm (Node := Idx)
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState noise 0,
              (quad.withStepsize alpha).trackerErrorZeroSum noise 0)))
        (Exi := fun j =>
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad noise j)
        hCsingle_nonneg halpha_pos.le
        hinit_single hxi_single
    simpa [quadraticRestrictedStableBoundaryResponse, Idx, z0, xi] using
      hassembled
  exact hsource_target

/-- A vector projected by `(I-P)` lies in the kernel of the Riesz projection
whenever `P` is idempotent. -/
theorem spectralStableComplementVector_projection_kernel
    (P : NodeMatrix Node)
    (hidem : matrixMul (Node := Node) P P = P)
    (z : RowVector Node) :
    matrixMulVector (Node := Node) P
      (spectralStableComplementVector (Node := Node) P z) =
      fun _ : Node => 0 := by
  classical
  funext i
  unfold spectralStableComplementVector matrixMulVector
  calc
    ∑ j : Node, P i j * (z j - ∑ k : Node, P j k * z k) =
        ∑ j : Node, P i j * z j -
          ∑ j : Node, P i j * (∑ k : Node, P j k * z k) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ =
        ∑ j : Node, P i j * z j -
          ∑ k : Node, (∑ j : Node, P i j * P j k) * z k := by
          congr 1
          calc
            ∑ j : Node, P i j * (∑ k : Node, P j k * z k) =
                ∑ j : Node, ∑ k : Node, P i j * (P j k * z k) := by
                  simp [Finset.mul_sum]
            _ = ∑ k : Node, ∑ j : Node, P i j * (P j k * z k) :=
                  Finset.sum_comm
            _ = ∑ k : Node, (∑ j : Node, P i j * P j k) * z k := by
                  apply Finset.sum_congr rfl
                  intro k _hk
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro j _hj
                  ring
    _ =
        ∑ j : Node, P i j * z j -
          ∑ k : Node, P i k * z k := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          have hcoord := congrFun (congrFun hidem i) k
          simpa [matrixMul] using congrArg (fun x : ℝ => x * z k) hcoord
    _ = 0 := by
          rw [sub_eq_zero]

/-- If `P F = 0`, then one application of `F` lands in the kernel of `P`. -/
theorem matrixMulVector_projection_apply_F_eq_zero
    (P F : NodeMatrix Node) (hPF : matrixMul (Node := Node) P F = 0)
    (z : RowVector Node) :
    matrixMulVector (Node := Node) P
      (matrixMulVector (Node := Node) F z) =
      fun _ : Node => 0 := by
  classical
  have hmul :
      matrixMulVector (Node := Node) P
        (matrixMulVector (Node := Node) F z) =
        matrixMulVector (Node := Node) (matrixMul (Node := Node) P F) z := by
    rw [matrixMulVector_matrixMul]
  funext i
  have hcoord := congrFun hmul i
  rw [hcoord, hPF]
  simp [matrixMulVector]

/-- Powers of `F` preserve the kernel of `P` when `P F = 0`. -/
theorem matrixPower_preserves_projection_kernel
    (P F : NodeMatrix Node) (hPF : matrixMul (Node := Node) P F = 0) :
    ∀ m : ℕ, ∀ z : RowVector Node,
      matrixMulVector (Node := Node) P z = (fun _ : Node => 0) →
        matrixMulVector (Node := Node) P
          (matrixMulVector (Node := Node)
            (matrixPower (Node := Node) F m) z) =
          fun _ : Node => 0 := by
  classical
  intro m
  induction m with
  | zero =>
      intro z hz
      have hid :
          matrixMulVector (Node := Node) (identityMatrix (Node := Node)) z = z := by
        funext i
        simp [matrixMulVector, identityMatrix]
      simpa [matrixPower, hid] using hz
  | succ m ih =>
      intro z _hz
      rw [matrixPower, matrixMulVector_matrixMul]
      exact ih (matrixMulVector (Node := Node) F z)
        (matrixMulVector_projection_apply_F_eq_zero
          (Node := Node) P F hPF z)

/-- Matrix-vector multiplication is additive in the vector argument. -/
theorem matrixMulVector_add_vector_local
    (A : NodeMatrix Node) (x y : RowVector Node) :
    matrixMulVector (Node := Node) A (x + y) =
      matrixMulVector (Node := Node) A x +
        matrixMulVector (Node := Node) A y := by
  classical
  funext i
  simp [matrixMulVector, Finset.sum_add_distrib, mul_add]

/-- Matrix-vector multiplication distributes over finite row-vector sums. -/
theorem matrixMulVector_finset_sum_local
    (A : NodeMatrix Node) (s : Finset ℕ) (x : ℕ → RowVector Node) :
    matrixMulVector (Node := Node) A (∑ j ∈ s, x j) =
      ∑ j ∈ s, matrixMulVector (Node := Node) A (x j) := by
  classical
  refine Finset.induction_on s ?base ?step
  · funext i
    simp [matrixMulVector]
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has,
      matrixMulVector_add_vector_local, ih]

/-- One-step recurrence for the closed stable Duhamel response. -/
theorem stablePowerDuhamelClosedResponse_succ
    (F : NodeMatrix Node) (z0 : RowVector Node)
    (xi : ℕ → RowVector Node) (t : ℕ) :
    stablePowerDuhamelClosedResponse (Node := Node) F z0 xi (t + 1) =
      matrixMulVector (Node := Node) F
        (stablePowerDuhamelClosedResponse (Node := Node) F z0 xi t) +
        xi t := by
  classical
  unfold stablePowerDuhamelClosedResponse
  rw [Finset.sum_range_succ]
  have hpow :
      matrixMulVector (Node := Node)
          (matrixPower (Node := Node) F (t + 1)) z0 =
        matrixMulVector (Node := Node) F
          (matrixMulVector (Node := Node)
            (matrixPower (Node := Node) F t) z0) := by
    rw [matrixPower, matrixPower_mul_self_comm (Node := Node) F t,
      matrixMulVector_matrixMul]
  have hsum :
      (∑ j ∈ Finset.range t,
        matrixMulVector (Node := Node)
          (matrixPower (Node := Node) F (t + 1 - 1 - j)) (xi j)) =
        matrixMulVector (Node := Node) F
          (∑ j ∈ Finset.range t,
            matrixMulVector (Node := Node)
              (matrixPower (Node := Node) F (t - 1 - j)) (xi j)) := by
    rw [matrixMulVector_finset_sum_local]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < t := Finset.mem_range.mp hj
    have hexp : t + 1 - 1 - j = (t - 1 - j) + 1 := by omega
    rw [hexp, matrixPower,
      matrixPower_mul_self_comm (Node := Node) F (t - 1 - j),
      matrixMulVector_matrixMul]
  have hlast :
      matrixMulVector (Node := Node)
          (matrixPower (Node := Node) F (t + 1 - 1 - t)) (xi t) =
        xi t := by
    funext a
    simp [matrixPower, matrixMulVector, identityMatrix]
  rw [hpow, hsum, hlast, matrixMulVector_add_vector_local]
  abel

/-- Stable complements evolve through a split period map by the stable block
plus the stable complement of the innovation. -/
theorem spectralStableComplementVector_split_step
    (P F A : NodeMatrix Node) (gamma : ℝ)
    (hPP : matrixMul (Node := Node) P P = P)
    (hA : A = matrixAdd (Node := Node) (gamma • P) F)
    (hPF : matrixMul (Node := Node) P F = 0)
    (hFP : matrixMul (Node := Node) F P = 0)
    (y xi : RowVector Node) :
    spectralStableComplementVector (Node := Node) P
        (matrixMulVector (Node := Node) A y + xi) =
      matrixMulVector (Node := Node) F
          (spectralStableComplementVector (Node := Node) P y) +
        spectralStableComplementVector (Node := Node) P xi := by
  classical
  have hPA : matrixMul (Node := Node) P A = gamma • P := by
    subst A
    funext a b
    have hPP_ab := congrFun (congrFun hPP a) b
    have hPF_ab := congrFun (congrFun hPF a) b
    calc
      matrixMul (Node := Node) P
          (matrixAdd (Node := Node) (gamma • P) F) a b =
        gamma * matrixMul (Node := Node) P P a b +
          matrixMul (Node := Node) P F a b := by
          simp [matrixMul, matrixAdd, Finset.sum_add_distrib,
            Finset.mul_sum, mul_add, smul_eq_mul]
          ac_rfl
      _ = gamma * P a b + 0 := by
          simp [hPP_ab, hPF_ab]
      _ = (gamma • P) a b := by
          simp [smul_eq_mul]
  have hAy :
      matrixMulVector (Node := Node) A y =
        gamma • matrixMulVector (Node := Node) P y +
          matrixMulVector (Node := Node) F y := by
    subst A
    funext a
    simp [matrixMulVector, matrixAdd, Finset.sum_add_distrib,
      Finset.mul_sum, smul_eq_mul, mul_add]
    calc
      (∑ x : Node, (gamma * P a x + F a x) * y x) =
          ∑ x : Node, (gamma * (P a x * y x) + F a x * y x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
      _ = (∑ x : Node, gamma * (P a x * y x)) +
            ∑ x : Node, F a x * y x := by
          rw [Finset.sum_add_distrib]
  have hPAy :
      matrixMulVector (Node := Node) P
          (matrixMulVector (Node := Node) A y) =
        gamma • matrixMulVector (Node := Node) P y := by
    rw [← matrixMulVector_matrixMul (Node := Node) P A y, hPA]
    funext a
    simp [matrixMulVector, smul_eq_mul, Finset.mul_sum, mul_assoc,
      mul_left_comm, mul_comm]
  have hPadd :
      matrixMulVector (Node := Node) P
          (matrixMulVector (Node := Node) A y + xi) =
        matrixMulVector (Node := Node) P
          (matrixMulVector (Node := Node) A y) +
          matrixMulVector (Node := Node) P xi := by
    exact matrixMulVector_add_vector_local (Node := Node) P
      (matrixMulVector (Node := Node) A y) xi
  have hFstable :
      matrixMulVector (Node := Node) F
          (spectralStableComplementVector (Node := Node) P y) =
        matrixMulVector (Node := Node) F y := by
    funext a
    have hFP_ab : ∀ b : Node, (∑ c : Node, F a c * P c b) = 0 := by
      intro b
      simpa [matrixMul] using congrFun (congrFun hFP a) b
    simp [spectralStableComplementVector, matrixMulVector,
      Finset.sum_sub_distrib, Finset.mul_sum]
    have hzero :
        (∑ x : Node, F a x *
          (∑ x_1 : Node, P x x_1 * y x_1)) = 0 := by
      calc
        (∑ x : Node, F a x *
          (∑ x_1 : Node, P x x_1 * y x_1)) =
            ∑ x : Node, ∑ b : Node, F a x * (P x b * y b) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [Finset.mul_sum]
        _ = ∑ b : Node, ∑ x : Node, F a x * (P x b * y b) := by
            rw [Finset.sum_comm]
        _ = ∑ b : Node, (∑ x : Node, F a x * P x b) * y b := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _hx
            ring
        _ = 0 := by
            simp [hFP_ab]
    calc
      ∑ x : Node, F a x * (y x - ∑ x_1 : Node, P x x_1 * y x_1) =
          (∑ x : Node, F a x * y x) -
            ∑ x : Node, F a x * (∑ x_1 : Node, P x x_1 * y x_1) := by
          simp [mul_sub, Finset.sum_sub_distrib]
      _ = ∑ x : Node, F a x * y x := by
          rw [hzero]
          ring
  funext a
  simp only [spectralStableComplementVector, Pi.add_apply]
  rw [hPadd, hPAy, hAy, hFstable]
  simp [Pi.add_apply, Pi.smul_apply]
  ring

/-- The projected stable Duhamel response is in the kernel of the slow
projection `P`.  This records the stable-subspace algebra that the source
Appendix C.1 estimate uses before applying the alpha-small output functional. -/
theorem stablePowerDuhamelClosedResponse_projected_kernel
    (P F : NodeMatrix Node)
    (hidem : matrixMul (Node := Node) P P = P)
    (hPF : matrixMul (Node := Node) P F = 0)
    (z0 : RowVector Node) (xi : ℕ → RowVector Node) (t : ℕ) :
    matrixMulVector (Node := Node) P
      (stablePowerDuhamelClosedResponse (Node := Node) F
        (spectralStableComplementVector (Node := Node) P z0)
        (fun k => spectralStableComplementVector (Node := Node) P (xi k)) t) =
      fun _ : Node => 0 := by
  classical
  have hpreserve :=
    matrixPower_preserves_projection_kernel (Node := Node) P F hPF
  have hz0 :
      matrixMulVector (Node := Node) P
        (spectralStableComplementVector (Node := Node) P z0) =
        fun _ : Node => 0 :=
    spectralStableComplementVector_projection_kernel (Node := Node) P hidem z0
  have hxi :
      ∀ k : ℕ,
        matrixMulVector (Node := Node) P
          (spectralStableComplementVector (Node := Node) P (xi k)) =
          fun _ : Node => 0 := by
    intro k
    exact spectralStableComplementVector_projection_kernel (Node := Node) P hidem (xi k)
  have hinit_vec :=
    hpreserve t (spectralStableComplementVector (Node := Node) P z0) hz0
  have hsum_vec :
      matrixMulVector (Node := Node) P
        (∑ j ∈ Finset.range t,
          matrixMulVector (Node := Node)
            (matrixPower (Node := Node) F (t - 1 - j))
            (spectralStableComplementVector (Node := Node) P (xi j))) =
        fun _ : Node => 0 := by
    rw [matrixMulVector_finset_sum_local]
    funext a
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _hj
    have hj :=
      hpreserve (t - 1 - j)
        (spectralStableComplementVector (Node := Node) P (xi j)) (hxi j)
    exact congrFun hj a
  unfold stablePowerDuhamelClosedResponse
  rw [matrixMulVector_add_vector_local]
  funext i
  simp [congrFun hinit_vec i, congrFun hsum_vec i]

/-- Source-facing stable-subspace certificate for the canonical restricted
stable boundary response. -/
theorem quadraticRestrictedStableBoundaryResponse_projection_kernel
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    {alpha : ℝ} (halpha_abs : |alpha| ≤ alpha0)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
      (quadraticRestrictedStableBoundaryResponse
        (Node := Node) quad lambda i0 P F alpha noise t) =
      fun _ : Sum Node {i : Node // i ≠ i0} => 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hlocal := hsplitting.2.2.2.2.2.2.2.2 alpha halpha_abs
  have hidem : matrixMul (Node := Idx) (P alpha) (P alpha) = P alpha :=
    hlocal.1.1.1
  have hPF : matrixMul (Node := Idx) (P alpha) (F alpha) = 0 :=
    hlocal.2.2.1
  let z0 : RowVector Idx :=
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState noise 0,
        (quad.withStepsize alpha).trackerErrorZeroSum noise 0)
  let xi : ℕ → RowVector Idx := fun k =>
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 noise k
  simpa [quadraticRestrictedStableBoundaryResponse, Idx, z0, xi] using
    stablePowerDuhamelClosedResponse_projected_kernel
      (Node := Idx) (P alpha) (F alpha) hidem hPF z0 xi t

/-- The canonical stable boundary response is the stable complement of the
true restricted period-boundary state.

This is the block-start decomposition used before the remaining finite-phase
raw-time propagation: the projected slow coordinate plus this response
reconstruct the full restricted boundary coordinate. -/
theorem quadraticRestrictedStableBoundaryResponse_eq_boundary_stableComplement
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (hrestricted_period_boundary_recursion :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        let stepped := quad.withStepsize alpha
        restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise ((k + 1) * quad.period),
              stepped.trackerErrorZeroSum noise ((k + 1) * quad.period)) =
          matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
              (restrictedStateToCoord (Node := Node) i0
                (stepped.primalState noise (k * quad.period),
                  stepped.trackerErrorZeroSum noise (k * quad.period))) +
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k)
    {alpha : ℝ} (halpha_abs : |alpha| ≤ alpha0)
    (noise : NoisePath Node ℝ) :
    ∀ k : ℕ,
      quadraticRestrictedStableBoundaryResponse
          (Node := Node) quad lambda i0 P F alpha noise k =
        spectralStableComplementVector
          (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState noise (k * quad.period),
              (quad.withStepsize alpha).trackerErrorZeroSum noise
                (k * quad.period))) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hlocal := hsplitting.2.2.2.2.2.2.2.2 alpha halpha_abs
  have hidem : matrixMul (Node := Idx) (P alpha) (P alpha) = P alpha :=
    hlocal.1.1.1
  have hA :
      quadraticRestrictedPeriodMatrix (Node := Node) quad lambda alpha i0 =
        matrixAdd (Node := Idx) ((gamma alpha) • P alpha) (F alpha) :=
    hlocal.2.1
  have hPF : matrixMul (Node := Idx) (P alpha) (F alpha) = 0 :=
    hlocal.2.2.1
  have hFP : matrixMul (Node := Idx) (F alpha) (P alpha) = 0 :=
    hlocal.2.2.2.1
  intro k
  induction k with
  | zero =>
      simp [quadraticRestrictedStableBoundaryResponse,
        stablePowerDuhamelClosedResponse, matrixPower, Idx]
      funext a
      simp [matrixMulVector, identityMatrix]
  | succ k ih =>
      let stepped := quad.withStepsize alpha
      let yk : RowVector Idx :=
        restrictedStateToCoord (Node := Node) i0
          (stepped.primalState noise (k * quad.period),
            stepped.trackerErrorZeroSum noise (k * quad.period))
      let yNext : RowVector Idx :=
        restrictedStateToCoord (Node := Node) i0
          (stepped.primalState noise ((k + 1) * quad.period),
            stepped.trackerErrorZeroSum noise ((k + 1) * quad.period))
      let xi : ℕ → RowVector Idx := fun m =>
        quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise m
      have hyNext :
          yNext =
            matrixMulVector (Node := Idx)
                (quadraticRestrictedPeriodMatrix (Node := Node)
                  quad lambda alpha i0) yk +
              xi k := by
        simpa [Idx, stepped, yk, yNext, xi] using
          hrestricted_period_boundary_recursion alpha noise k
      have hstable_succ :
          quadraticRestrictedStableBoundaryResponse
              (Node := Node) quad lambda i0 P F alpha noise (k + 1) =
            matrixMulVector (Node := Idx) (F alpha)
              (quadraticRestrictedStableBoundaryResponse
                (Node := Node) quad lambda i0 P F alpha noise k) +
              spectralStableComplementVector (Node := Idx) (P alpha) (xi k) := by
        simpa [quadraticRestrictedStableBoundaryResponse, Idx, xi] using
          stablePowerDuhamelClosedResponse_succ
            (Node := Idx) (F alpha)
            (spectralStableComplementVector
              (Node := Idx) (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState noise 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum noise 0)))
            (fun m => spectralStableComplementVector (Node := Idx)
              (P alpha) (xi m)) k
      have hsplit :
          spectralStableComplementVector (Node := Idx) (P alpha) yNext =
            matrixMulVector (Node := Idx) (F alpha)
                (spectralStableComplementVector (Node := Idx) (P alpha) yk) +
              spectralStableComplementVector (Node := Idx) (P alpha) (xi k) := by
        rw [hyNext]
        exact
          spectralStableComplementVector_split_step
            (Node := Idx) (P alpha) (F alpha)
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
            (gamma alpha) hidem hA hPF hFP yk (xi k)
      rw [hstable_succ, ih, hsplit]

/-- At block starts, subtracting the canonical stable boundary response leaves
exactly the projected slow coordinate.

This is the executable block-start part of the finite-phase propagation bridge:
the all-time slow output agrees with the already-controlled projected/scalar
boundary quantity whenever the raw time is `k * period`. -/
theorem quadraticRestrictedSlowOutput_eq_projectedBoundary_at_block_start
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (hrestricted_period_boundary_recursion :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        let stepped := quad.withStepsize alpha
        restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise ((k + 1) * quad.period),
              stepped.trackerErrorZeroSum noise ((k + 1) * quad.period)) =
          matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
              (restrictedStateToCoord (Node := Node) i0
                (stepped.primalState noise (k * quad.period),
                  stepped.trackerErrorZeroSum noise (k * quad.period))) +
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k)
    {alpha : ℝ} (halpha_abs : |alpha| ≤ alpha0)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    (quad.withStepsize alpha).averageIterate noise (k * quad.period) -
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F alpha noise k) =
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState noise (k * quad.period),
              (quad.withStepsize alpha).trackerErrorZeroSum noise
                (k * quad.period)))) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let y : RowVector Idx :=
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState noise (k * quad.period),
        (quad.withStepsize alpha).trackerErrorZeroSum noise
          (k * quad.period))
  have hstable :
      quadraticRestrictedStableBoundaryResponse
          (Node := Node) quad lambda i0 P F alpha noise k =
        spectralStableComplementVector (Node := Idx) (P alpha) y := by
    simpa [Idx, y] using
      quadraticRestrictedStableBoundaryResponse_eq_boundary_stableComplement
        (Node := Node) quad lambda i0 r0 alpha0 theta K
        right left gamma P F hsplitting
        hrestricted_period_boundary_recursion halpha_abs noise k
  have havg :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0 y =
        (quad.withStepsize alpha).averageIterate noise (k * quad.period) := by
    simpa [Idx, y] using
      quadraticRestrictedPrimalAverageOutput_restrictedStateToCoord_eq_averageIterate
        (Node := Node) quad i0 alpha noise (k * quad.period)
  have houtput :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0 y -
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (spectralStableComplementVector (Node := Idx) (P alpha) y) =
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx) (P alpha) y) := by
    unfold quadraticRestrictedPrimalAverageOutput spectralStableComplementVector
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    ring
  simpa [Idx, y, hstable, havg] using houtput

/-- Block-start slow/scalar error decomposition with the stable-response
index-mismatch remainder exposed explicitly.

The active all-time theorem subtracts the stable boundary response at the raw
index `t`.  At a true block start `t = k * period`, the projected boundary
term is recovered with an additional finite-response remainder
`response k - response (k * period)`. -/
theorem quadraticRestrictedSlowOutput_block_start_error_sq_le_projectedBoundary_add_stable_remainder
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (hrestricted_period_boundary_recursion :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        let stepped := quad.withStepsize alpha
        restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise ((k + 1) * quad.period),
              stepped.trackerErrorZeroSum noise ((k + 1) * quad.period)) =
          matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
              (restrictedStateToCoord (Node := Node) i0
                (stepped.primalState noise (k * quad.period),
                  stepped.trackerErrorZeroSum noise (k * quad.period))) +
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k)
    {alpha : ℝ} (halpha_abs : |alpha| ≤ alpha0)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    |((quad.withStepsize alpha).averageIterate noise (k * quad.period) -
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (quadraticRestrictedStableBoundaryResponse
              (Node := Node) quad lambda i0 P F alpha noise
              (k * quad.period))) -
        quad.quadraticScalarComparisonProcess lambda alpha noise
          (k * quad.period)| ^ 2 ≤
      2 *
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState noise
                      (k * quad.period),
                    (quad.withStepsize alpha).trackerErrorZeroSum noise
                      (k * quad.period)))) -
            quad.quadraticScalarComparisonProcess lambda alpha noise
              (k * quad.period)| ^ 2 +
        2 *
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P F alpha noise k) -
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P F alpha noise
                  (k * quad.period))| ^ 2 := by
  classical
  let projected : ℝ :=
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
        (P alpha)
        (restrictedStateToCoord (Node := Node) i0
          ((quad.withStepsize alpha).primalState noise (k * quad.period),
            (quad.withStepsize alpha).trackerErrorZeroSum noise
              (k * quad.period))))
  let scalar : ℝ :=
    quad.quadraticScalarComparisonProcess lambda alpha noise
      (k * quad.period)
  let stableK : ℝ :=
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (quadraticRestrictedStableBoundaryResponse
        (Node := Node) quad lambda i0 P F alpha noise k)
  let stableRaw : ℝ :=
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (quadraticRestrictedStableBoundaryResponse
        (Node := Node) quad lambda i0 P F alpha noise
        (k * quad.period))
  have hbase :
      (quad.withStepsize alpha).averageIterate noise (k * quad.period) -
          stableK = projected := by
    simpa [projected, stableK] using
      quadraticRestrictedSlowOutput_eq_projectedBoundary_at_block_start
        (Node := Node) quad lambda i0 r0 alpha0 theta K
        right left gamma P F hsplitting
        hrestricted_period_boundary_recursion halpha_abs noise k
  have hdecomp :
      ((quad.withStepsize alpha).averageIterate noise (k * quad.period) -
            stableRaw) - scalar =
        (projected - scalar) + (stableK - stableRaw) := by
    nlinarith
  calc
    |((quad.withStepsize alpha).averageIterate noise (k * quad.period) -
          stableRaw) - scalar| ^ 2 =
        |(projected - scalar) + (stableK - stableRaw)| ^ 2 := by
          rw [hdecomp]
    _ ≤
        2 * |projected - scalar| ^ 2 +
          2 * |stableK - stableRaw| ^ 2 :=
          real_abs_add_sq_le_two_sq (projected - scalar)
            (stableK - stableRaw)

/-- The initial restricted boundary coordinate is deterministic for every
stepsize.

Appendix C.1 starts from the common initialization `X_0 = 1 x_0` and zero
tracker error.  This sharpened form avoids treating the initial boundary
moment as a stochastic source obligation. -/
theorem quadraticRestrictedInitialBoundaryCoord_eq_const
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) :
    restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize alpha).primalState noise 0,
          (quad.withStepsize alpha).trackerErrorZeroSum noise 0) =
      fun a : Sum Node {i : Node // i ≠ i0} =>
        match a with
        | Sum.inl _ => quad.x0
        | Sum.inr _ => 0 := by
  classical
  funext a
  cases a with
  | inl i =>
      simp [restrictedStateToCoord, withStepsize, primalState_zero, initialPrimal]
  | inr j =>
      simp [restrictedStateToCoord, withStepsize, trackerErrorZeroSum,
        trackerError, trackerState_zero, oracleTable]

/-- Appendix C.1 projected initial-boundary second-moment supplier.

The initial restricted coordinate is deterministic.  After shrinking the
spectral radius, the analytic Riesz projection is continuous on a compact
stepsize interval, so the projected initial stable energy has a uniform finite
bound. -/
theorem quadratic_restricted_projected_initial_second_moment_source_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ) :
    ∃ alphaInit Cz0 : ℝ,
      0 < alphaInit ∧ alphaInit ≤ alpha0 ∧ 0 ≤ Cz0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInit →
          (∫ ω,
            rowEuclideanNorm
              (Node := Sum Node {i : Node // i ≠ i0})
              (spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState
                      (oracle.noise ω) 0,
                    (quad.withStepsize alpha).trackerErrorZeroSum
                      (oracle.noise ω) 0))) ^ 2 ∂μ) ≤ Cz0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  rcases hsplitting with
    ⟨halpha0_pos, _hr0_theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      _hgamma_analytic, hP_analytic, _hderiv, _hlocal⟩
  let alphaInit : ℝ := alpha0 / 2
  have halphaInit_pos : 0 < alphaInit := by
    dsimp [alphaInit]
    linarith
  have halphaInit_le : alphaInit ≤ alpha0 := by
    dsimp [alphaInit]
    linarith
  have halphaInit_lt : alphaInit < alpha0 := by
    dsimp [alphaInit]
    linarith
  let zinit : RowVector Idx := fun a =>
    match a with
    | Sum.inl _ => quad.x0
    | Sum.inr _ => 0
  let energy : ℝ → ℝ := fun alpha =>
    rowEuclideanNorm (Node := Idx)
      (spectralStableComplementVector (Node := Idx) (P alpha) zinit) ^ 2
  have hP_cont_sym :
      ContinuousOn P (Set.Icc (-alphaInit) alphaInit) :=
    analytic_matrixFamily_continuousOn_Icc_of_lt
      (Node := Idx) P alphaInit alpha0 hP_analytic halphaInit_lt
  have hP_cont :
      ContinuousOn P (Set.Icc (0 : ℝ) alphaInit) := by
    refine hP_cont_sym.mono ?_
    intro alpha halpha
    exact ⟨by linarith [halpha.1], halpha.2⟩
  have hP_entry_cont :
      ∀ a b : Idx, ContinuousOn (fun alpha : ℝ => P alpha a b)
        (Set.Icc (0 : ℝ) alphaInit) := by
    intro a b
    exact (continuous_apply b).comp_continuousOn
      ((continuous_apply a).comp_continuousOn hP_cont)
  have hcoord_cont :
      ∀ a : Idx,
        ContinuousOn
          (fun alpha : ℝ =>
            spectralStableComplementVector (Node := Idx) (P alpha) zinit a)
          (Set.Icc (0 : ℝ) alphaInit) := by
    intro a
    dsimp [spectralStableComplementVector, matrixMulVector]
    exact continuousOn_const.sub
      (continuousOn_finset_sum Finset.univ (fun b _hb =>
        (hP_entry_cont a b).mul continuousOn_const))
  have henergy_cont : ContinuousOn energy (Set.Icc (0 : ℝ) alphaInit) := by
    dsimp [energy]
    rw [show
      (fun alpha : ℝ =>
        rowEuclideanNorm (Node := Idx)
          (spectralStableComplementVector (Node := Idx) (P alpha) zinit) ^ 2) =
        (fun alpha : ℝ =>
          rowNormSq (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha) zinit)) by
        funext alpha
        exact rowEuclideanNorm_sq_eq_rowNormSq (Node := Idx)
          (spectralStableComplementVector (Node := Idx) (P alpha) zinit)]
    unfold rowNormSq
    exact continuousOn_finset_sum Finset.univ (fun a _ha =>
      (hcoord_cont a).pow 2)
  obtain ⟨Cz0, hCz0_nonneg, hCz0_bound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      energy isCompact_Icc henergy_cont
  refine ⟨alphaInit, Cz0, halphaInit_pos, halphaInit_le,
    hCz0_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_mem : alpha ∈ Set.Icc (0 : ℝ) alphaInit :=
    ⟨halpha_pos.le, halpha_le⟩
  have henergy_nonneg : 0 ≤ energy alpha := by
    dsimp [energy]
    positivity
  have henergy_bound : energy alpha ≤ Cz0 := by
    have hbound := hCz0_bound alpha halpha_mem
    simpa [Real.norm_eq_abs, abs_of_nonneg henergy_nonneg] using hbound
  have hconst :
      (fun ω : Ω =>
        rowEuclideanNorm (Node := Idx)
          (spectralStableComplementVector (Node := Idx) (P alpha)
            (restrictedStateToCoord (Node := Node) i0
              ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
                (quad.withStepsize alpha).trackerErrorZeroSum
                  (oracle.noise ω) 0))) ^ 2) =
        fun _ : Ω => energy alpha := by
    funext ω
    have hz :=
      quadraticRestrictedInitialBoundaryCoord_eq_const
        (Node := Node) quad alpha i0 (oracle.noise ω)
    rw [hz]
    rfl
  calc
    (∫ ω,
        rowEuclideanNorm (Node := Idx)
          (spectralStableComplementVector (Node := Idx) (P alpha)
            (restrictedStateToCoord (Node := Node) i0
              ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
                (quad.withStepsize alpha).trackerErrorZeroSum
                  (oracle.noise ω) 0))) ^ 2 ∂μ) =
        energy alpha := by
          rw [hconst, MeasureTheory.integral_const]
          simp
    _ ≤ Cz0 := henergy_bound

/-- Appendix C.1 projected period-innovation second-moment supplier.

This is the exact same-granularity stochastic leaf requested by the route
arbiter: expand the finite period innovation, use the iid exact-variance law
for same-time node-noise rows and cross-time orthogonality, then use finite
periodicity and the compact small-stepsize interval to choose a uniform bound. -/
theorem quadratic_restricted_projected_innovation_second_moment_source_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ alphaXi Cxi : ℝ,
      0 < alphaXi ∧ alphaXi ≤ alpha0 ∧ 0 ≤ Cxi ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
          ∀ k : ℕ,
            (∫ ω,
              rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0})
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) k)) ^ 2 ∂μ) ≤ Cxi := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  rcases hsplitting with
    ⟨halpha0_pos, _hr0_theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      _hgamma_analytic, hP_analytic, _hderiv, _hlocal⟩
  let alphaXi : ℝ := alpha0 / 2
  have halphaXi_pos : 0 < alphaXi := by
    dsimp [alphaXi]
    linarith
  have halphaXi_le : alphaXi ≤ alpha0 := by
    dsimp [alphaXi]
    linarith
  have halphaXi_lt : alphaXi < alpha0 := by
    dsimp [alphaXi]
    linarith
  have hP_cont_sym :
      ContinuousOn P (Set.Icc (-alphaXi) alphaXi) :=
    analytic_matrixFamily_continuousOn_Icc_of_lt
      (Node := Idx) P alphaXi alpha0 hP_analytic halphaXi_lt
  have hP_cont :
      ContinuousOn P (Set.Icc (0 : ℝ) alphaXi) := by
    refine hP_cont_sym.mono ?_
    intro alpha halpha
    exact ⟨by linarith [halpha.1], halpha.2⟩
  have hP_entry_cont :
      ∀ a b : Idx, ContinuousOn (fun alpha : ℝ => P alpha a b)
        (Set.Icc (0 : ℝ) alphaXi) := by
    intro a b
    exact (continuous_apply b).comp_continuousOn
      ((continuous_apply a).comp_continuousOn hP_cont)
  have hxi_coord_memLp :
      ∀ alpha : ℝ, ∀ k : ℕ, ∀ a : Idx,
        MemLp
          (fun ω =>
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 (oracle.noise ω) k a)
          2 μ := by
    intro alpha k a
    exact
      quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
        (Node := Node) quad lambda alpha i0 μ oracle hnoise k a
  have hprojected_coord_memLp :
      ∀ alpha : ℝ, ∀ k : ℕ, ∀ a : Idx,
        MemLp
          (fun ω =>
            spectralStableComplementVector (Node := Idx) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) k) a)
          2 μ := by
    intro alpha k a
    unfold spectralStableComplementVector matrixMulVector
    have hproj :
        MemLp
          (fun ω =>
            ∑ b : Idx, P alpha a b *
              quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) k b) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro b _hb
      exact (hxi_coord_memLp alpha k b).const_smul (P alpha a b)
    exact (hxi_coord_memLp alpha k a).sub hproj
  have hprojected_norm_sq_integrable :
      ∀ alpha : ℝ, ∀ k : ℕ,
        Integrable
          (fun ω =>
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0
                  (oracle.noise ω) k)) ^ 2) μ := by
    intro alpha k
    exact
      rowEuclideanNorm_sq_integrable_of_coordinate_memLp
        (Node := Idx) (hprojected_coord_memLp alpha k)
  have hfinite_period_exact_variance_uniform_bound :
      ∃ Cxi : ℝ, 0 ≤ Cxi ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
          ∀ k : ℕ,
            (∫ ω,
              rowEuclideanNorm (Node := Idx)
                (spectralStableComplementVector (Node := Idx) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) k)) ^ 2 ∂μ) ≤ Cxi := by
    obtain ⟨Ceta, hCeta_nonneg, heta_bound⟩ :=
      quadraticRestrictedNoiseInnovationCoord_secondMoment_uniform_bound
        (Node := Node) quad alphaXi i0 μ oracle hnoise
    have hperiod_window_step_sq :
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
          ∀ k n : ℕ, ∀ noise : NoisePath Node ℝ,
            rowEuclideanNorm (Node := Idx)
                (quadraticRestrictedConsecutiveNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 noise
                  (k * quad.period) (n + 1)) ^ 2 ≤
              2 *
                (matrixEuclideanOperatorNorm (Node := Idx)
                  (quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda alpha i0
                    (k * quad.period + n)) ^
                  2 *
                rowEuclideanNorm (Node := Idx)
                  (quadraticRestrictedConsecutiveNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0 noise
                    (k * quad.period) n) ^ 2) +
              2 *
                rowEuclideanNorm (Node := Idx)
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise
                    (k * quad.period + n)) ^ 2 := by
      intro alpha _halpha_pos _halpha_le k n noise
      simpa [Idx] using
        quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_sq_succ_le
          (Node := Node) quad lambda alpha i0 noise
          (k * quad.period) n
    have hperiod_window_step_sq_of_operator_bound :
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
          ∀ k n : ℕ, ∀ noise : NoisePath Node ℝ, ∀ Mstep : ℝ,
            0 ≤ Mstep →
            matrixEuclideanOperatorNorm (Node := Idx)
                (quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda alpha i0
                  (k * quad.period + n)) ≤ Mstep →
            rowEuclideanNorm (Node := Idx)
                (quadraticRestrictedConsecutiveNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 noise
                  (k * quad.period) (n + 1)) ^ 2 ≤
              2 *
                (Mstep ^ 2 *
                rowEuclideanNorm (Node := Idx)
                  (quadraticRestrictedConsecutiveNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0 noise
                    (k * quad.period) n) ^ 2) +
              2 *
                rowEuclideanNorm (Node := Idx)
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise
                    (k * quad.period + n)) ^ 2 := by
      intro alpha _halpha_pos _halpha_le k n noise Mstep hMstep_nonneg hstep_bound
      simpa [Idx] using
        quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_sq_succ_le_of_operator_bound
          (Node := Node) quad lambda alpha i0 noise
          (k * quad.period) n hMstep_nonneg hstep_bound
    have hperiod_window_l2_bound_of_uniform_step :
        ∀ Mstep : ℝ, 0 ≤ Mstep →
          (∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
            ∀ k n : ℕ, n < quad.period →
              matrixEuclideanOperatorNorm (Node := Idx)
                (quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda alpha i0
                  (k * quad.period + n)) ≤ Mstep) →
          ∃ Cwin : ℝ, 0 ≤ Cwin ∧
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaXi →
              ∀ k : ℕ,
                (∫ ω,
                  rowEuclideanNorm (Node := Idx)
                    (quadraticRestrictedConsecutiveNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0
                      (oracle.noise ω) (k * quad.period)
                      quad.period) ^ 2 ∂μ) ≤ Cwin := by
      intro Mstep hMstep_nonneg hstep_bound
      exact
        quadraticRestrictedConsecutiveNoiseInnovationCoord_period_l2_bound_of_uniform_step
          (Node := Node) quad lambda alphaXi i0 μ oracle hnoise
          hMstep_nonneg hCeta_nonneg hstep_bound heta_bound
    /- Remaining deterministic finite-period induction leaf.  The stochastic
    source step is now consumed by `heta_bound`: every one-step canonical C.1
    innovation has a uniform second moment obtained from
    `sameTime_weightedNoise_secondMoment_eq_exact` and the exact iid variance
    field of `hnoise`.  The deterministic one-step squared recursion is also
    now compiled as `hperiod_window_step_sq` and its uniform-operator version
    `hperiod_window_step_sq_of_operator_bound`; the fixed-length `L²`
    induction is packaged and consumed in
    `hperiod_window_l2_bound_of_uniform_step`.  Finish by bounding the
    finitely many homogeneous one-step maps and the stable projection on
    `Set.Icc 0 alphaXi`, then apply the packaged period-window estimate and
    one uniform `(I-P alpha)` operator bound. -/
    obtain ⟨Mstep, hMstep_nonneg, hstep_bound⟩ :=
      quadraticRestrictedOneStepMatrix_uniform_operator_bound_on_Icc
        (Node := Node) quad lambda alphaXi i0 halphaXi_pos
    obtain ⟨Cwin, hCwin_nonneg, hCwin_bound⟩ :=
      hperiod_window_l2_bound_of_uniform_step
        Mstep hMstep_nonneg hstep_bound
    obtain ⟨Mproj, hMproj_nonneg, hproj_bound⟩ :=
      spectralStableComplementVector_uniform_operator_bound_on_Icc
        (Node := Idx) P alphaXi hP_entry_cont
    let Cxi : ℝ := Mproj ^ 2 * Cwin
    refine ⟨Cxi, ?_, ?_⟩
    · dsimp [Cxi]
      exact mul_nonneg (sq_nonneg Mproj) hCwin_nonneg
    intro alpha halpha_pos halpha_le k
    let xi : Ω → RowVector Idx := fun ω =>
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 (oracle.noise ω) k
    have hxi_int :
        Integrable
          (fun ω =>
            rowEuclideanNorm (Node := Idx) (xi ω) ^ 2) μ := by
      dsimp [xi]
      exact
        rowEuclideanNorm_sq_integrable_of_coordinate_memLp
          (Node := Idx)
          (quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
            (Node := Node) quad lambda alpha i0 μ oracle hnoise k)
    have hproj_int :
        Integrable
          (fun ω =>
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (xi ω)) ^ 2) μ :=
      hprojected_norm_sq_integrable alpha k
    have hpointwise :
        (fun ω =>
          rowEuclideanNorm (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha)
              (xi ω)) ^ 2) ≤ᵐ[μ]
          (fun ω =>
            Mproj ^ 2 * rowEuclideanNorm (Node := Idx) (xi ω) ^ 2) := by
      exact Filter.Eventually.of_forall fun ω =>
        hproj_bound alpha halpha_pos halpha_le (xi ω)
    have hrhs_int :
        Integrable
          (fun ω =>
            Mproj ^ 2 * rowEuclideanNorm (Node := Idx) (xi ω) ^ 2) μ :=
      hxi_int.const_mul (Mproj ^ 2)
    have hmono :
        (∫ ω,
          rowEuclideanNorm (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha)
              (xi ω)) ^ 2 ∂μ) ≤
        ∫ ω, Mproj ^ 2 *
          rowEuclideanNorm (Node := Idx) (xi ω) ^ 2 ∂μ :=
      MeasureTheory.integral_mono_ae hproj_int hrhs_int hpointwise
    have hxi_bound :
        (∫ ω,
          rowEuclideanNorm (Node := Idx) (xi ω) ^ 2 ∂μ) ≤ Cwin := by
      simpa [xi, quadraticRestrictedPeriodNoiseInnovationCoord, Idx] using
        hCwin_bound alpha halpha_pos halpha_le k
    have hscale_nonneg : 0 ≤ Mproj ^ 2 := sq_nonneg Mproj
    calc
      (∫ ω,
          rowEuclideanNorm (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) k)) ^ 2 ∂μ) =
          (∫ ω,
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (xi ω)) ^ 2 ∂μ) := by
            rfl
      _ ≤ ∫ ω, Mproj ^ 2 *
          rowEuclideanNorm (Node := Idx) (xi ω) ^ 2 ∂μ := hmono
      _ = Mproj ^ 2 *
          (∫ ω, rowEuclideanNorm (Node := Idx) (xi ω) ^ 2 ∂μ) := by
            rw [MeasureTheory.integral_const_mul]
      _ ≤ Mproj ^ 2 * Cwin :=
            mul_le_mul_of_nonneg_left hxi_bound hscale_nonneg
      _ = Cxi := by rfl
  obtain ⟨Cxi, hCxi_nonneg, hCxi_bound⟩ :=
    hfinite_period_exact_variance_uniform_bound
  refine ⟨alphaXi, Cxi, halphaXi_pos, halphaXi_le, hCxi_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le k
  exact hCxi_bound alpha halpha_pos halpha_le k

/-- Appendix C.1 averaged projected stable-response `L²` budget.

This is the source-granularity stochastic bridge after the deterministic
projected Duhamel square-sum estimate.  The two remaining stochastic inputs
are exactly the projected initial-boundary and projected period-innovation
second-moment bounds; the theorem performs the finite-horizon integration and
geometric-budget assembly, without routing through a uniform per-boundary
stable-state helper. -/
theorem quadratic_restricted_projected_stable_average_duhamel_l2_budget
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alpha0 : ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {A B Cz0 Cxi : ℝ}
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hCz0_nonneg : 0 ≤ Cz0) (hCxi_nonneg : 0 ≤ Cxi)
    (hdeterministic_duhamel :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ noise : NoisePath Node ℝ, ∀ N : ℕ,
          Finset.sum (Finset.range (N + 1)) (fun t =>
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedStableBoundaryResponse
                (Node := Node) quad lambda i0 P F alpha noise t) ^ 2) ≤
            A *
              rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState noise 0,
                      (quad.withStepsize alpha).trackerErrorZeroSum noise 0))) ^ 2 +
            B *
              Finset.sum (Finset.range N) (fun k =>
                rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                  (spectralStableComplementVector
                    (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0 noise k)) ^ 2))
    (hz0_second_moment :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        (∫ ω,
          rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
            (spectralStableComplementVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) 0))) ^ 2 ∂μ) ≤ Cz0)
    (hxi_second_moment :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ k : ℕ,
          (∫ ω,
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0
                  (oracle.noise ω) k)) ^ 2 ∂μ) ≤ Cxi) :
    ∃ Cduh : ℝ, 0 ≤ Cduh ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ T : ℕ, 1 ≤ T →
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P F alpha
                  (oracle.noise ω) t) ^ 2 ∂μ) ≤
            Cduh * (T : ℝ) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let Cduh : ℝ := A * Cz0 + B * Cxi + 1
  refine ⟨Cduh, ?_, ?_⟩
  · have hAC : 0 ≤ A * Cz0 := mul_nonneg hA_nonneg hCz0_nonneg
    have hBC : 0 ≤ B * Cxi := mul_nonneg hB_nonneg hCxi_nonneg
    dsimp [Cduh]
    linarith
  intro alpha halpha_pos halpha_le T hT
  let z0 : Ω → RowVector Idx := fun ω =>
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
        (quad.withStepsize alpha).trackerErrorZeroSum
          (oracle.noise ω) 0)
  let xi : ℕ → Ω → RowVector Idx := fun k ω =>
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 (oracle.noise ω) k
  let response : Ω → ℕ → RowVector Idx := fun ω t =>
    quadraticRestrictedStableBoundaryResponse
      (Node := Node) quad lambda i0 P F alpha (oracle.noise ω) t
  have hT_pos_nat : 0 < T := Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
  have hT_ge_one_real : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hpred_succ : T - 1 + 1 = T := Nat.sub_add_cancel hT
  have hz0_coord : ∀ a : Idx, MemLp (fun ω => z0 ω a) 2 μ := by
    intro a
    exact
      quadraticRestrictedInitialBoundaryCoord_coordinate_memLp
        (Node := Node) quad alpha i0 μ oracle hnoise a
  have hz0_stable_coord :
      ∀ a : Idx,
        MemLp
          (fun ω =>
            spectralStableComplementVector (Node := Idx) (P alpha)
              (z0 ω) a) 2 μ := by
    intro a
    unfold spectralStableComplementVector matrixMulVector
    have hproj :
        MemLp (fun ω => ∑ b : Idx, P alpha a b * z0 ω b) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro b _hb
      exact (hz0_coord b).const_smul (P alpha a b)
    exact (hz0_coord a).sub hproj
  have hz0_int :
      Integrable
        (fun ω =>
          rowEuclideanNorm (Node := Idx)
            (spectralStableComplementVector (Node := Idx) (P alpha)
              (z0 ω)) ^ 2) μ :=
    rowEuclideanNorm_sq_integrable_of_coordinate_memLp
      (Node := Idx) hz0_stable_coord
  have hxi_coord :
      ∀ k : ℕ, ∀ a : Idx, MemLp (fun ω => xi k ω a) 2 μ := by
    intro k a
    exact
      quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
        (Node := Node) quad lambda alpha i0 μ oracle hnoise k a
  have hxi_stable_coord :
      ∀ k : ℕ, ∀ a : Idx,
        MemLp
          (fun ω =>
            spectralStableComplementVector (Node := Idx) (P alpha)
              (xi k ω) a) 2 μ := by
    intro k a
    unfold spectralStableComplementVector matrixMulVector
    have hproj :
        MemLp (fun ω => ∑ b : Idx, P alpha a b * xi k ω b) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro b _hb
      exact (hxi_coord k b).const_smul (P alpha a b)
    exact (hxi_coord k a).sub hproj
  have hxi_int :
      ∀ k : ℕ,
        Integrable
          (fun ω =>
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (xi k ω)) ^ 2) μ := by
    intro k
    exact
      rowEuclideanNorm_sq_integrable_of_coordinate_memLp
        (Node := Idx) (hxi_stable_coord k)
  have hresponse_int :
      ∀ t ∈ Finset.range T,
        Integrable
          (fun ω =>
            rowEuclideanNorm (Node := Idx) (response ω t) ^ 2) μ := by
    intro t _ht
    simpa [Idx, response] using
      quadraticRestrictedStableBoundaryResponse_norm_sq_integrable
        (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
  have hleft_sum_int :
      Integrable
        (fun ω =>
          Finset.sum (Finset.range T) (fun t =>
            rowEuclideanNorm (Node := Idx) (response ω t) ^ 2)) μ :=
    integrable_finset_sum (Finset.range T) hresponse_int
  have hxi_sum_int :
      Integrable
        (fun ω =>
          Finset.sum (Finset.range (T - 1)) (fun k =>
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (xi k ω)) ^ 2)) μ :=
    integrable_finset_sum (Finset.range (T - 1)) (fun k _hk => hxi_int k)
  have hright_int :
      Integrable
        (fun ω =>
          A *
              rowEuclideanNorm (Node := Idx)
                (spectralStableComplementVector (Node := Idx) (P alpha)
                  (z0 ω)) ^ 2 +
            B *
              Finset.sum (Finset.range (T - 1)) (fun k =>
                rowEuclideanNorm (Node := Idx)
                  (spectralStableComplementVector (Node := Idx) (P alpha)
                    (xi k ω)) ^ 2)) μ :=
    (hz0_int.const_mul A).add (hxi_sum_int.const_mul B)
  have hpointwise :
      (fun ω =>
          Finset.sum (Finset.range T) (fun t =>
            rowEuclideanNorm (Node := Idx) (response ω t) ^ 2)) ≤ᵐ[μ]
        (fun ω =>
          A *
              rowEuclideanNorm (Node := Idx)
                (spectralStableComplementVector (Node := Idx) (P alpha)
                  (z0 ω)) ^ 2 +
            B *
              Finset.sum (Finset.range (T - 1)) (fun k =>
                rowEuclideanNorm (Node := Idx)
                  (spectralStableComplementVector (Node := Idx) (P alpha)
                    (xi k ω)) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hdet :=
      hdeterministic_duhamel alpha halpha_pos halpha_le
        (oracle.noise ω) (T - 1)
    simpa [Idx, response, z0, xi, hpred_succ] using hdet
  have hmono :
      (∫ ω,
          Finset.sum (Finset.range T) (fun t =>
            rowEuclideanNorm (Node := Idx) (response ω t) ^ 2) ∂μ) ≤
        ∫ ω,
          A *
              rowEuclideanNorm (Node := Idx)
                (spectralStableComplementVector (Node := Idx) (P alpha)
                  (z0 ω)) ^ 2 +
            B *
              Finset.sum (Finset.range (T - 1)) (fun k =>
                rowEuclideanNorm (Node := Idx)
                  (spectralStableComplementVector (Node := Idx) (P alpha)
                    (xi k ω)) ^ 2) ∂μ := by
    exact MeasureTheory.integral_mono_ae hleft_sum_int hright_int hpointwise
  have hxi_sum_bound :
      Finset.sum (Finset.range (T - 1)) (fun k =>
          ∫ ω,
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (xi k ω)) ^ 2 ∂μ) ≤
        Cxi * ((T - 1 : ℕ) : ℝ) := by
    calc
      Finset.sum (Finset.range (T - 1)) (fun k =>
          ∫ ω,
            rowEuclideanNorm (Node := Idx)
              (spectralStableComplementVector (Node := Idx) (P alpha)
                (xi k ω)) ^ 2 ∂μ) ≤
          Finset.sum (Finset.range (T - 1)) (fun _k => Cxi) := by
            exact Finset.sum_le_sum fun k _hk =>
              by simpa [Idx, xi] using
                hxi_second_moment alpha halpha_pos halpha_le k
      _ = Cxi * ((T - 1 : ℕ) : ℝ) := by simp [mul_comm]
  have hduh_integral_bound :
      Finset.sum (Finset.range T) (fun t =>
          ∫ ω, rowEuclideanNorm (Node := Idx) (response ω t) ^ 2 ∂μ) ≤
        A * Cz0 + B * (Cxi * ((T - 1 : ℕ) : ℝ)) := by
    calc
      Finset.sum (Finset.range T) (fun t =>
          ∫ ω, rowEuclideanNorm (Node := Idx) (response ω t) ^ 2 ∂μ) =
          ∫ ω,
            Finset.sum (Finset.range T) (fun t =>
              rowEuclideanNorm (Node := Idx) (response ω t) ^ 2) ∂μ := by
            rw [MeasureTheory.integral_finset_sum]
            exact hresponse_int
      _ ≤
          ∫ ω,
            A *
                rowEuclideanNorm (Node := Idx)
                  (spectralStableComplementVector (Node := Idx) (P alpha)
                    (z0 ω)) ^ 2 +
              B *
                Finset.sum (Finset.range (T - 1)) (fun k =>
                  rowEuclideanNorm (Node := Idx)
                    (spectralStableComplementVector (Node := Idx) (P alpha)
                      (xi k ω)) ^ 2) ∂μ := hmono
      _ =
          A *
              (∫ ω,
                rowEuclideanNorm (Node := Idx)
                  (spectralStableComplementVector (Node := Idx) (P alpha)
                    (z0 ω)) ^ 2 ∂μ) +
            B *
              Finset.sum (Finset.range (T - 1)) (fun k =>
                ∫ ω,
                  rowEuclideanNorm (Node := Idx)
                    (spectralStableComplementVector (Node := Idx) (P alpha)
                      (xi k ω)) ^ 2 ∂μ) := by
            rw [MeasureTheory.integral_add (hz0_int.const_mul A)
              (hxi_sum_int.const_mul B)]
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_const_mul,
              MeasureTheory.integral_finset_sum]
            exact fun k _hk => hxi_int k
      _ ≤ A * Cz0 + B * (Cxi * ((T - 1 : ℕ) : ℝ)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (by simpa [Idx, z0] using
                  hz0_second_moment alpha halpha_pos halpha_le)
                hA_nonneg)
              (mul_le_mul_of_nonneg_left hxi_sum_bound hB_nonneg)
  have hAC_nonneg : 0 ≤ A * Cz0 := mul_nonneg hA_nonneg hCz0_nonneg
  have hBC_nonneg : 0 ≤ B * Cxi := mul_nonneg hB_nonneg hCxi_nonneg
  have hpred_le_T : ((T - 1 : ℕ) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast Nat.sub_le T 1
  calc
    Finset.sum (Finset.range T) (fun t =>
        ∫ ω,
          rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedStableBoundaryResponse
              (Node := Node) quad lambda i0 P F alpha
              (oracle.noise ω) t) ^ 2 ∂μ) =
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, rowEuclideanNorm (Node := Idx) (response ω t) ^ 2 ∂μ) := by
          simp [Idx, response]
    _ ≤ A * Cz0 + B * (Cxi * ((T - 1 : ℕ) : ℝ)) :=
          hduh_integral_bound
    _ ≤ (A * Cz0 + B * Cxi + 1) * (T : ℝ) := by
          nlinarith [hT_nonneg, hT_ge_one_real, hpred_le_T,
            hAC_nonneg, hBC_nonneg]
    _ = Cduh * (T : ℝ) := by rfl

/-- Averaging algebra for Appendix C.1 stable-output square sums.

The source work in step 5 is to obtain the unaveraged finite-horizon estimate
`sum_t E |r_t^st|^2 <= C alpha^2 T` from the geometric impulse envelope and
iid noise.  This helper performs only the final normalization by `T`; it keeps
the stochastic envelope summation as the explicit source leaf. -/
theorem quadratic_restricted_stable_output_average_l2_from_sum_bound
    (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (response :
      ℝ → Ω → ℕ → RowVector (Sum Node {i : Node // i ≠ i0}))
    {alpha0 Csum : ℝ}
    (halpha0_pos : 0 < alpha0)
    (hCsum_nonneg : 0 ≤ Csum)
    (houtput_sum_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ T : ℕ, 1 ≤ T →
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (response alpha ω t)| ^ 2 ∂μ) ≤
            Csum * alpha ^ 2 * (T : ℝ)) :
    ∃ C alphaStable : ℝ,
      0 < C ∧ 0 < alphaStable ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaStable →
          ∀ T : ℕ, 1 ≤ T →
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (response alpha ω t)| ^ 2 ∂μ) ≤
              C * alpha ^ 2 := by
  classical
  let C : ℝ := Csum + 1
  refine ⟨C, alpha0, ?_, halpha0_pos, ?_⟩
  · dsimp [C]
    linarith
  intro alpha halpha_pos halpha_le T hT
  have hT_pos_nat : 0 < T := Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT_pos_nat
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hT_pos.le
  have hsum := houtput_sum_bound alpha halpha_pos halpha_le T hT
  calc
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (response alpha ω t)| ^ 2 ∂μ) ≤
        ((T : ℝ)⁻¹) * (Csum * alpha ^ 2 * (T : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum hTinv_nonneg
    _ = Csum * alpha ^ 2 := by
          field_simp [hT_ne]
    _ ≤ C * alpha ^ 2 := by
          have hsq : 0 ≤ alpha ^ 2 := sq_nonneg alpha
          dsimp [C]
          nlinarith

/-- The repeated-period contraction base is below the midpoint radius used for
the stable disk. -/
theorem contractionRate_pow_period_lt_mid
    (quad : Setup Node ℝ)
    (hr_nonneg : 0 ≤ quad.contractionRate)
    (hr_lt_one : quad.contractionRate < 1) :
    quad.contractionRate ^ quad.period <
      (quad.contractionRate + 1) / 2 := by
  classical
  rcases Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt quad.period_pos) with ⟨k, hk⟩
  rw [hk]
  have hpow_le_one : quad.contractionRate ^ k ≤ 1 :=
    pow_le_one₀ hr_nonneg hr_lt_one.le
  have hpow_le_rate :
      quad.contractionRate ^ (k + 1) ≤ quad.contractionRate := by
    calc
      quad.contractionRate ^ (k + 1) =
          quad.contractionRate ^ k * quad.contractionRate := by
            rw [pow_succ]
      _ ≤ 1 * quad.contractionRate := by
            exact mul_le_mul_of_nonneg_right hpow_le_one hr_nonneg
      _ = quad.contractionRate := by ring
  have hrate_lt_mid :
      quad.contractionRate < (quad.contractionRate + 1) / 2 := by
    linarith
  exact lt_of_le_of_lt hpow_le_rate hrate_lt_mid

/-- If a real state is fixed by the phase-zero one-period push product, it is
fixed by every integer number of periods. -/
theorem pushLiftProduct_leftMul_fixed_iterate
    (quad : Setup Node ℝ) (X : State Node ℝ)
    (hX :
      leftMul (Node := Node) (E := ℝ)
        (quad.pushLiftProduct 0 quad.period) X = X) :
    ∀ m : ℕ,
      leftMul (Node := Node) (E := ℝ)
        (quad.pushLiftProduct 0 (m * quad.period)) X = X := by
  classical
  intro m
  induction m with
  | zero =>
      simp [pushLiftProduct, leftMul_identity]
  | succ m ih =>
      calc
        leftMul (Node := Node) (E := ℝ)
            (quad.pushLiftProduct 0 ((m + 1) * quad.period)) X =
          leftMul (Node := Node) (E := ℝ)
            (quad.pushLiftProduct 0 (m * quad.period + quad.period)) X := by
              rw [Nat.succ_mul]
        _ =
          leftMul (Node := Node) (E := ℝ)
            (matrixMul (Node := Node)
              (quad.pushLiftProduct (0 + m * quad.period) quad.period)
              (quad.pushLiftProduct 0 (m * quad.period))) X := by
              rw [pushLiftProduct_add_source]
        _ =
          leftMul (Node := Node) (E := ℝ)
            (quad.pushLiftProduct (m * quad.period) quad.period)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pushLiftProduct 0 (m * quad.period)) X) := by
              rw [leftMul_matrixMul]
              simp
        _ =
          leftMul (Node := Node) (E := ℝ)
            (quad.pushLiftProduct 0 quad.period) X := by
              rw [ih]
              rw [pushLiftProduct_periodic_start_mul]
        _ = X := hX

/-- Periodicity of pull-product start phases iterated to any multiple of the
period. -/
theorem pullLiftProduct_periodic_start_mul
    (quad : Setup Node ℝ) (m j : ℕ) :
    quad.pullLiftProduct (m * quad.period) j =
      quad.pullLiftProduct 0 j := by
  classical
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        quad.pullLiftProduct ((m + 1) * quad.period) j =
            quad.pullLiftProduct (m * quad.period + quad.period) j := by
              rw [Nat.succ_mul]
        _ = quad.pullLiftProduct (m * quad.period) j := by
              rw [quad.pullLiftProduct_periodic_start]
        _ = quad.pullLiftProduct 0 j := ih

/-- If a zero-sum tracker state is fixed by the phase-zero one-period pull
product, it is fixed by every integer number of periods. -/
theorem pullLiftProduct_leftMul_fixed_iterate
    (quad : Setup Node ℝ) (W : State Node ℝ)
    (hW :
      leftMul (Node := Node) (E := ℝ)
        (quad.pullLiftProduct 0 quad.period) W = W) :
    ∀ m : ℕ,
      leftMul (Node := Node) (E := ℝ)
        (quad.pullLiftProduct 0 (m * quad.period)) W = W := by
  classical
  intro m
  induction m with
  | zero =>
      simp [pullLiftProduct, leftMul_identity]
  | succ m ih =>
      calc
        leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 ((m + 1) * quad.period)) W =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 (m * quad.period + quad.period)) W := by
              rw [Nat.succ_mul]
        _ =
          leftMul (Node := Node) (E := ℝ)
            (matrixMul (Node := Node)
              (quad.pullLiftProduct (0 + m * quad.period) quad.period)
              (quad.pullLiftProduct 0 (m * quad.period))) W := by
              rw [quad.pullLiftProduct_add]
        _ =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct (m * quad.period) quad.period)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) W) := by
              rw [leftMul_matrixMul]
              simp
        _ =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 quad.period) W := by
              rw [ih]
              rw [pullLiftProduct_periodic_start_mul]
        _ = W := hW

/-- A real distributed state with zero Frobenius norm is pointwise zero. -/
theorem state_eq_zero_of_stateFrobeniusNorm_eq_zero
    (X : State Node ℝ)
    (hX : stateFrobeniusNorm (Node := Node) (E := ℝ) X = 0) :
    X = 0 := by
  classical
  funext i
  have hle := norm_apply_le_stateFrobeniusNorm
    (Node := Node) (E := ℝ) X i
  rw [hX] at hle
  have hnorm : ‖X i‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact norm_eq_zero.mp hnorm

/-- Complex scalar multiplication scales the Frobenius norm of a complex
distributed state by the complex modulus. -/
theorem stateFrobeniusNorm_complex_smul
    (a : ℂ) (Z : State Node ℂ) :
    stateFrobeniusNorm (Node := Node) (E := ℂ) (a • Z) =
      ‖a‖ * stateFrobeniusNorm (Node := Node) (E := ℂ) Z := by
  rw [stateFrobeniusNorm_eq_piLp_norm,
    stateFrobeniusNorm_eq_piLp_norm]
  change ‖a • (WithLp.toLp 2 Z : PiLp 2 (fun _ : Node => ℂ))‖ = _
  rw [norm_smul]

/-- The Frobenius norm of a complex state is the combined Frobenius norm of
its real and imaginary parts. -/
theorem stateFrobeniusNorm_complex_re_im
    (X Y : State Node ℝ) :
    stateFrobeniusNorm (Node := Node) (E := ℂ)
        (fun i : Node => (X i : ℂ) + (Y i : ℂ) * Complex.I) =
      Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ) X ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ) Y ^ 2) := by
  have hsq :
      stateFrobeniusNorm (Node := Node) (E := ℂ)
          (fun i : Node => (X i : ℂ) + (Y i : ℂ) * Complex.I) ^ 2 =
        (Real.sqrt
          (stateFrobeniusNorm (Node := Node) (E := ℝ) X ^ 2 +
            stateFrobeniusNorm (Node := Node) (E := ℝ) Y ^ 2)) ^ 2 := by
    rw [stateFrobeniusNorm_sq]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [stateFrobeniusNorm_sq, stateFrobeniusNorm_sq]
    unfold frobeniusNormSq
    have hpoint :
        ∀ i : Node,
          ‖(X i : ℂ) + (Y i : ℂ) * Complex.I‖ ^ 2 =
            ‖X i‖ ^ 2 + ‖Y i‖ ^ 2 := by
      intro i
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    calc
      (∑ i : Node, ‖(X i : ℂ) + (Y i : ℂ) * Complex.I‖ ^ 2) =
          ∑ i : Node, (‖X i‖ ^ 2 + ‖Y i‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hpoint i
      _ =
          (∑ i : Node, ‖X i‖ ^ 2) +
            ∑ i : Node, ‖Y i‖ ^ 2 := by
          rw [Finset.sum_add_distrib]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · have hleft_nonneg :
        0 ≤ stateFrobeniusNorm (Node := Node) (E := ℂ)
          (fun i : Node => (X i : ℂ) + (Y i : ℂ) * Complex.I) :=
      Real.sqrt_nonneg _
    have hright_nonneg :
        0 ≤ Real.sqrt
          (stateFrobeniusNorm (Node := Node) (E := ℝ) X ^ 2 +
            stateFrobeniusNorm (Node := Node) (E := ℝ) Y ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith

/-- Free-coordinate equality for zero-sum real/imaginary tracker pairs gives
the corresponding scaled equality of their combined Frobenius norms. -/
theorem zero_sum_complex_tracker_combined_norm_scaled
    (i0 : Node)
    (Xre Xim Yre Yim : ZeroSumState Node ℝ) (a : ℂ)
    (hre :
      ∀ j : {i : Node // i ≠ i0},
        Xre.1 j.1 =
          (a * ((Yre.1 j.1 : ℂ) + (Yim.1 j.1 : ℂ) * Complex.I)).re)
    (him :
      ∀ j : {i : Node // i ≠ i0},
        Xim.1 j.1 =
          (a * ((Yre.1 j.1 : ℂ) + (Yim.1 j.1 : ℂ) * Complex.I)).im) :
    Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ) Xre.1 ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ) Xim.1 ^ 2) =
      ‖a‖ *
        Real.sqrt
          (stateFrobeniusNorm (Node := Node) (E := ℝ) Yre.1 ^ 2 +
            stateFrobeniusNorm (Node := Node) (E := ℝ) Yim.1 ^ 2) := by
  classical
  have hcomplex_eq :
      (fun i : Node => (Xre.1 i : ℂ) + (Xim.1 i : ℂ) * Complex.I) =
        a • (fun i : Node => (Yre.1 i : ℂ) + (Yim.1 i : ℂ) * Complex.I) :=
    zero_sum_complex_tracker_ext_of_free_coords
      (Node := Node) i0 Xre Xim Yre Yim a hre him
  calc
    Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ) Xre.1 ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ) Xim.1 ^ 2) =
        stateFrobeniusNorm (Node := Node) (E := ℂ)
          (fun i : Node => (Xre.1 i : ℂ) + (Xim.1 i : ℂ) * Complex.I) := by
        rw [stateFrobeniusNorm_complex_re_im]
    _ =
        stateFrobeniusNorm (Node := Node) (E := ℂ)
          (a •
            (fun i : Node => (Yre.1 i : ℂ) + (Yim.1 i : ℂ) * Complex.I)) := by
        rw [hcomplex_eq]
    _ =
        ‖a‖ * stateFrobeniusNorm (Node := Node) (E := ℂ)
          (fun i : Node => (Yre.1 i : ℂ) + (Yim.1 i : ℂ) * Complex.I) := by
        rw [stateFrobeniusNorm_complex_smul]
    _ =
        ‖a‖ *
          Real.sqrt
            (stateFrobeniusNorm (Node := Node) (E := ℝ) Yre.1 ^ 2 +
              stateFrobeniusNorm (Node := Node) (E := ℝ) Yim.1 ^ 2) := by
        rw [stateFrobeniusNorm_complex_re_im]

/-- The complex state assembled from real and imaginary consensus errors is
the consensus error of the assembled complex state. -/
theorem complex_arithmeticAverage_ofReal
    (X : State Node ℝ) :
    arithmeticAverage (Node := Node) (E := ℂ)
        (fun i : Node => (X i : ℂ)) =
      (arithmeticAverage (Node := Node) (E := ℝ) X : ℂ) := by
  unfold arithmeticAverage
  rw [← Complex.ofReal_sum]
  exact ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).map_smul
    ((nodeCount (Node := Node) : ℝ)⁻¹) (∑ i : Node, X i)).symm

theorem complex_consensusError_ofReal
    (X : State Node ℝ) :
    (fun i : Node =>
        (consensusError (Node := Node) (E := ℝ) X i : ℂ)) =
      consensusError (Node := Node) (E := ℂ)
        (fun i : Node => (X i : ℂ)) := by
  funext i
  unfold consensusError
  rw [complex_arithmeticAverage_ofReal]
  simp

/-- Complex scalar multiplication commutes with the arithmetic consensus-error
projection on complex node states. -/
theorem complex_consensusError_smul
    (a : ℂ) (Z : State Node ℂ) :
    consensusError (Node := Node) (E := ℂ) (a • Z) =
      a • consensusError (Node := Node) (E := ℂ) Z := by
  classical
  have havg :
      arithmeticAverage (Node := Node) (E := ℂ) (a • Z) =
        a • arithmeticAverage (Node := Node) (E := ℂ) Z := by
    unfold arithmeticAverage
    simp_rw [Pi.smul_apply]
    rw [← Finset.smul_sum]
    exact smul_comm ((nodeCount (Node := Node) : ℝ)⁻¹) a (∑ i : Node, Z i)
  funext i
  unfold consensusError
  rw [havg]
  simp only [Pi.smul_apply, smul_sub]

theorem complex_consensusError_re_im
    (X Y : State Node ℝ) :
    (fun i : Node =>
        ((consensusError (Node := Node) (E := ℝ) X i : ℂ) +
          (consensusError (Node := Node) (E := ℝ) Y i : ℂ) * Complex.I)) =
      consensusError (Node := Node) (E := ℂ)
        (fun i : Node => (X i : ℂ) + (Y i : ℂ) * Complex.I) := by
  classical
  let Xc : State Node ℂ := fun i : Node => (X i : ℂ)
  let Yc : State Node ℂ := fun i : Node => (Y i : ℂ)
  have hX :
      (fun i : Node =>
          (consensusError (Node := Node) (E := ℝ) X i : ℂ)) =
        consensusError (Node := Node) (E := ℂ) Xc := by
    simpa [Xc] using complex_consensusError_ofReal (Node := Node) X
  have hY :
      (fun i : Node =>
          (consensusError (Node := Node) (E := ℝ) Y i : ℂ)) =
        consensusError (Node := Node) (E := ℂ) Yc := by
    simpa [Yc] using complex_consensusError_ofReal (Node := Node) Y
  have hassembled :
      (fun i : Node => (X i : ℂ) + (Y i : ℂ) * Complex.I) =
        Xc + Complex.I • Yc := by
    funext i
    simp [Xc, Yc, Pi.add_apply, Pi.smul_apply]
    ring
  calc
    (fun i : Node =>
        ((consensusError (Node := Node) (E := ℝ) X i : ℂ) +
          (consensusError (Node := Node) (E := ℝ) Y i : ℂ) * Complex.I)) =
        consensusError (Node := Node) (E := ℂ) Xc +
          Complex.I • consensusError (Node := Node) (E := ℂ) Yc := by
          rw [← hX, ← hY]
          funext i
          simp [Pi.add_apply, Pi.smul_apply]
          ring
    _ =
        consensusError (Node := Node) (E := ℂ) Xc +
          consensusError (Node := Node) (E := ℂ) (Complex.I • Yc) := by
          rw [complex_consensusError_smul]
    _ =
        consensusError (Node := Node) (E := ℂ)
          (Xc + Complex.I • Yc) := by
          rw [consensusError_add_state]
    _ =
        consensusError (Node := Node) (E := ℂ)
          (fun i : Node => (X i : ℂ) + (Y i : ℂ) * Complex.I) := by
          rw [hassembled]

/-- Pointwise complex scalar multiplication scales the combined real/imaginary
Frobenius norm after applying the consensus-error projector. -/
theorem complex_consensus_error_combined_norm_scaled
    (Xre Xim Yre Yim : State Node ℝ) (a : ℂ)
    (hXY :
      (fun i : Node => (Xre i : ℂ) + (Xim i : ℂ) * Complex.I) =
        a • (fun i : Node => (Yre i : ℂ) + (Yim i : ℂ) * Complex.I)) :
    Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xim) ^ 2) =
      ‖a‖ *
        Real.sqrt
          (stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
            stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) := by
  classical
  let Xc : State Node ℂ :=
    fun i : Node => (Xre i : ℂ) + (Xim i : ℂ) * Complex.I
  let Yc : State Node ℂ :=
    fun i : Node => (Yre i : ℂ) + (Yim i : ℂ) * Complex.I
  have hXc : Xc = a • Yc := by
    simpa [Xc, Yc] using hXY
  calc
    Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xim) ^ 2) =
        stateFrobeniusNorm (Node := Node) (E := ℂ)
          (fun i : Node =>
            ((consensusError (Node := Node) (E := ℝ) Xre i : ℂ) +
              (consensusError (Node := Node) (E := ℝ) Xim i : ℂ) *
                Complex.I)) := by
        rw [stateFrobeniusNorm_complex_re_im]
    _ =
        stateFrobeniusNorm (Node := Node) (E := ℂ)
          (consensusError (Node := Node) (E := ℂ) Xc) := by
        rw [complex_consensusError_re_im]
    _ =
        stateFrobeniusNorm (Node := Node) (E := ℂ)
          (consensusError (Node := Node) (E := ℂ) (a • Yc)) := by
        rw [hXc]
    _ =
        stateFrobeniusNorm (Node := Node) (E := ℂ)
          (a • consensusError (Node := Node) (E := ℂ) Yc) := by
        rw [complex_consensusError_smul]
    _ =
        ‖a‖ *
          stateFrobeniusNorm (Node := Node) (E := ℂ)
            (consensusError (Node := Node) (E := ℂ) Yc) := by
        rw [stateFrobeniusNorm_complex_smul]
    _ =
        ‖a‖ *
          stateFrobeniusNorm (Node := Node) (E := ℂ)
            (fun i : Node =>
              ((consensusError (Node := Node) (E := ℝ) Yre i : ℂ) +
                (consensusError (Node := Node) (E := ℝ) Yim i : ℂ) *
                  Complex.I)) := by
        rw [complex_consensusError_re_im]
    _ =
        ‖a‖ *
          Real.sqrt
            (stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) := by
        rw [stateFrobeniusNorm_complex_re_im]

/-- A nonzero nonunit complex eigenvector of the alpha-zero push period has
nonzero primal consensus error in its real/imaginary parts. -/
theorem complex_push_nonunit_eigen_consensus_error_norm_pos
    (quad : Setup Node ℝ)
    (gamma : ℂ) (X : ComplexRowVector Node)
    (hX_ne : X ≠ 0)
    (hX :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period) X =
        gamma • X)
    (hgamma_ne_one : gamma ≠ (1 : ℂ)) :
    let Xre : State Node ℝ := fun i : Node => (X i).re
    let Xim : State Node ℝ := fun i : Node => (X i).im
    0 < Real.sqrt
      (stateFrobeniusNorm (Node := Node) (E := ℝ)
          (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 +
        stateFrobeniusNorm (Node := Node) (E := ℝ)
          (consensusError (Node := Node) (E := ℝ) Xim) ^ 2) := by
  classical
  intro Xre Xim
  refine Real.sqrt_pos.2 ?_
  by_contra hnot_pos
  have hsum_le :
      stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xim) ^ 2 ≤ 0 :=
    le_of_not_gt hnot_pos
  have hre_sq_nonneg :
      0 ≤ stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 :=
    sq_nonneg _
  have him_sq_nonneg :
      0 ≤ stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xim) ^ 2 :=
    sq_nonneg _
  have hre_sq_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ)
          (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 = 0 := by
    nlinarith
  have him_sq_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ)
          (consensusError (Node := Node) (E := ℝ) Xim) ^ 2 = 0 := by
    nlinarith
  have hre_norm_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ)
          (consensusError (Node := Node) (E := ℝ) Xre) = 0 := by
    nlinarith [hre_sq_zero]
  have him_norm_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ)
          (consensusError (Node := Node) (E := ℝ) Xim) = 0 := by
    nlinarith [him_sq_zero]
  have hCEre_zero :
      consensusError (Node := Node) (E := ℝ) Xre = 0 :=
    state_eq_zero_of_stateFrobeniusNorm_eq_zero
      (Node := Node)
      (consensusError (Node := Node) (E := ℝ) Xre) hre_norm_zero
  have hCEim_zero :
      consensusError (Node := Node) (E := ℝ) Xim = 0 :=
    state_eq_zero_of_stateFrobeniusNorm_eq_zero
      (Node := Node)
      (consensusError (Node := Node) (E := ℝ) Xim) him_norm_zero
  obtain ⟨cre, hXre_const⟩ :
      ∃ c : ℝ, Xre = fun _ : Node => c := by
    refine ⟨arithmeticAverage (Node := Node) (E := ℝ) Xre, ?_⟩
    funext i
    have hi := congrFun hCEre_zero i
    unfold consensusError at hi
    exact sub_eq_zero.mp hi
  obtain ⟨cim, hXim_const⟩ :
      ∃ c : ℝ, Xim = fun _ : Node => c := by
    refine ⟨arithmeticAverage (Node := Node) (E := ℝ) Xim, ?_⟩
    funext i
    have hi := congrFun hCEim_zero i
    unfold consensusError at hi
    exact sub_eq_zero.mp hi
  let c : ℂ := (cre : ℂ) + (cim : ℂ) * Complex.I
  have hX_const : X = fun _ : Node => c := by
    funext i
    apply Complex.ext
    · have hre := congrFun hXre_const i
      simpa [Xre, c] using hre
    · have him := congrFun hXim_const i
      simpa [Xim, c] using him
  have hc_ne : c ≠ 0 := by
    intro hc
    apply hX_ne
    rw [hX_const]
    funext i
    simpa [hc]
  let P : NodeMatrix Node := quad.pushLiftProduct 0 quad.period
  have hrow : RowStochastic (Node := Node) P :=
    (quad.pushLiftProduct_network_spec 0 quad.period).1
  have hleft_const :
      complexMatrixMulVector (Node := Node) P X = fun _ : Node => c := by
    funext i
    calc
      complexMatrixMulVector (Node := Node) P X i =
          ∑ j : Node, (P i j : ℂ) * c := by
            simp [complexMatrixMulVector, hX_const]
      _ = ((∑ j : Node, P i j : ℝ) : ℂ) * c := by
            simp [Finset.sum_mul]
      _ = c := by
            have hrowsum : ∑ j : Node, P i j = 1 := hrow.2 i
            rw [hrowsum]
            simp
  have heq_const :
      (fun _ : Node => c) = gamma • (fun _ : Node => c) := by
    calc
      (fun _ : Node => c) =
          complexMatrixMulVector (Node := Node) P X := hleft_const.symm
      _ = gamma • X := by simpa [P] using hX
      _ = gamma • (fun _ : Node => c) := by rw [hX_const]
  obtain ⟨i0⟩ := ‹Nonempty Node›
  have hi := congrFun heq_const i0
  have hgamma_c : gamma * c = c := by
    simpa [Pi.smul_apply, smul_eq_mul] using hi.symm
  have hgamma_one : gamma = 1 := by
    have hgamma_c_eq : gamma * c = (1 : ℂ) * c := by
      simpa [one_mul] using hgamma_c
    exact (mul_left_inj' hc_ne).mp hgamma_c_eq
  exact hgamma_ne_one hgamma_one

/-- Combine two nonnegative component bounds under an Euclidean two-component
root. -/
theorem sqrt_sq_add_sq_le_mul_sqrt_sq_add_sq
    {K a b x y : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y)
    (hx : x ≤ K * a) (hy : y ≤ K * b) :
    Real.sqrt (x ^ 2 + y ^ 2) ≤
      K * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hright_nonneg : 0 ≤ K * Real.sqrt (a ^ 2 + b ^ 2) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hright_nonneg).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  rw [mul_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hxa : x ^ 2 ≤ (K * a) ^ 2 :=
    (sq_le_sq₀ hx_nonneg (mul_nonneg hK ha)).2 hx
  have hyb : y ^ 2 ≤ (K * b) ^ 2 :=
    (sq_le_sq₀ hy_nonneg (mul_nonneg hK hb)).2 hy
  nlinarith

/-- A zero-sum tracker fixed by one alpha-zero pull period must vanish.

This is the tracker diagonal analogue of
`real_push_period_fixed_point_is_consensus`: repeat the period equation, apply
the source pull contraction to arbitrary period tails, and let the geometric
majorant tend to zero. -/
theorem real_pull_period_fixed_point_is_zero
    (quad : Setup Node ℝ)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (W : ZeroSumState Node ℝ)
    (hW :
      leftMul (Node := Node) (E := ℝ)
        (quad.pullLiftProduct 0 quad.period) W.1 = W.1) :
    W.1 = 0 := by
  classical
  let wNorm : ℝ := stateFrobeniusNorm (Node := Node) (E := ℝ) W.1
  have hfixed_iter :
      ∀ m : ℕ,
        leftMul (Node := Node) (E := ℝ)
          (quad.pullLiftProduct 0 (m * quad.period)) W.1 = W.1 :=
    pullLiftProduct_leftMul_fixed_iterate (Node := Node) quad W.1 hW
  have hwNorm_nonneg : 0 ≤ wNorm := by
    dsimp [wNorm]
    exact Real.sqrt_nonneg _
  have hcol_nonneg : 0 ≤ quad.columnContractionConstant := by
    dsimp [Setup.columnContractionConstant]
    exact div_nonneg (Real.sqrt_nonneg _) quad.contractionDelta_pos.le
  have hM_nonneg : 0 ≤ quad.columnContractionConstant * wNorm :=
    mul_nonneg hcol_nonneg hwNorm_nonneg
  have hq_nonneg : 0 ≤ quad.contractionRate ^ quad.period :=
    pow_nonneg hstable.1 quad.period
  have hq_lt_one : quad.contractionRate ^ quad.period < 1 := by
    exact pow_lt_one₀ hstable.1 hstable.2.1
      (Nat.ne_of_gt quad.period_pos)
  have htail :
      ∀ N : ℕ,
        ‖(wNorm : ℂ)‖ ≤
          (1 : ℝ) *
            ((quad.columnContractionConstant * wNorm) *
              (quad.contractionRate ^ quad.period) ^ (N + 1)) := by
    intro N
    have hcontract :=
      hstable.2.2.1 0 ((N + 1) * quad.period) W
    have hfixed := hfixed_iter (N + 1)
    have hraw :
        wNorm ≤
          quad.columnContractionConstant *
            quad.contractionRate ^ ((N + 1) * quad.period) *
              wNorm := by
      simpa [wNorm, hfixed] using hcontract
    have hnorm_cast : ‖(wNorm : ℂ)‖ = wNorm := by
      simpa [Complex.normSq, Real.norm_eq_abs,
        abs_of_nonneg hwNorm_nonneg] using
        (Complex.normSq_apply (wNorm : ℂ))
    calc
      ‖(wNorm : ℂ)‖ = wNorm := hnorm_cast
      _ ≤ quad.columnContractionConstant *
            quad.contractionRate ^ ((N + 1) * quad.period) *
              wNorm := hraw
      _ = (1 : ℝ) *
            ((quad.columnContractionConstant * wNorm) *
              (quad.contractionRate ^ quad.period) ^ (N + 1)) := by
            have hp :
                quad.contractionRate ^ ((N + 1) * quad.period) =
                  (quad.contractionRate ^ quad.period) ^ (N + 1) := by
              rw [Nat.mul_comm, pow_mul]
            rw [hp]
            ring
  have hwNorm_complex_zero :
      (wNorm : ℂ) = 0 :=
    zero_center_norm_le_geometric_tail_for_all_N_forces_eq_zero
      (R := (1 : ℝ))
      (M := quad.columnContractionConstant * wNorm)
      (q := quad.contractionRate ^ quad.period)
      (D := (wNorm : ℂ))
      zero_lt_one hM_nonneg hq_nonneg hq_lt_one htail
  have hwNorm_zero : wNorm = 0 :=
    Complex.ofReal_eq_zero.mp hwNorm_complex_zero
  exact
    state_eq_zero_of_stateFrobeniusNorm_eq_zero
      (Node := Node) W.1 hwNorm_zero

/-- A real fixed point of the alpha-zero primal period block is consensus.

The proof is the source C.1 argument for the top block: repeat the period
equation, apply the push consensus-error contraction for arbitrary tails, and
let the geometric majorant tend to zero. -/
theorem real_push_period_fixed_point_is_consensus
    (quad : Setup Node ℝ)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (X : State Node ℝ)
    (hX :
      leftMul (Node := Node) (E := ℝ)
        (quad.pushLiftProduct 0 quad.period) X = X) :
    ∃ c : ℝ, X = fun _ : Node => c := by
  classical
  let CE : State Node ℝ := consensusError (Node := Node) (E := ℝ) X
  let ceNorm : ℝ := stateFrobeniusNorm (Node := Node) (E := ℝ) CE
  have hfixed_iter :
      ∀ m : ℕ,
        leftMul (Node := Node) (E := ℝ)
          (quad.pushLiftProduct 0 (m * quad.period)) X = X :=
    pushLiftProduct_leftMul_fixed_iterate (Node := Node) quad X hX
  have hceNorm_nonneg : 0 ≤ ceNorm := by
    dsimp [ceNorm]
    exact Real.sqrt_nonneg _
  have hrow_nonneg : 0 ≤ quad.rowContractionConstant := by
    dsimp [Setup.rowContractionConstant]
    exact div_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      quad.contractionDelta_pos.le
  have hM_nonneg : 0 ≤ quad.rowContractionConstant * ceNorm :=
    mul_nonneg hrow_nonneg hceNorm_nonneg
  have hq_nonneg : 0 ≤ quad.contractionRate ^ quad.period :=
    pow_nonneg hstable.1 quad.period
  have hq_lt_one : quad.contractionRate ^ quad.period < 1 := by
    exact pow_lt_one₀ hstable.1 hstable.2.1
      (Nat.ne_of_gt quad.period_pos)
  have htail :
      ∀ N : ℕ,
        ‖(ceNorm : ℂ)‖ ≤
          (1 : ℝ) *
            ((quad.rowContractionConstant * ceNorm) *
              (quad.contractionRate ^ quad.period) ^ (N + 1)) := by
    intro N
    have hcontract :=
      hstable.2.2.2 0 ((N + 1) * quad.period) X
    have hfixed := hfixed_iter (N + 1)
    have hraw :
        ceNorm ≤
          quad.rowContractionConstant *
            quad.contractionRate ^ ((N + 1) * quad.period) *
              ceNorm := by
      simpa [CE, ceNorm, hfixed] using hcontract
    have hnorm_cast : ‖(ceNorm : ℂ)‖ = ceNorm := by
      simpa [Complex.normSq, Real.norm_eq_abs,
        abs_of_nonneg hceNorm_nonneg] using
        (Complex.normSq_apply (ceNorm : ℂ))
    calc
      ‖(ceNorm : ℂ)‖ = ceNorm := hnorm_cast
      _ ≤ quad.rowContractionConstant *
            quad.contractionRate ^ ((N + 1) * quad.period) *
              ceNorm := hraw
      _ = (1 : ℝ) *
            ((quad.rowContractionConstant * ceNorm) *
              (quad.contractionRate ^ quad.period) ^ (N + 1)) := by
            have hp :
                quad.contractionRate ^ ((N + 1) * quad.period) =
                  (quad.contractionRate ^ quad.period) ^ (N + 1) := by
              rw [Nat.mul_comm, pow_mul]
            rw [hp]
            ring
  have hceNorm_complex_zero :
      (ceNorm : ℂ) = 0 :=
    zero_center_norm_le_geometric_tail_for_all_N_forces_eq_zero
      (R := (1 : ℝ))
      (M := quad.rowContractionConstant * ceNorm)
      (q := quad.contractionRate ^ quad.period)
      (D := (ceNorm : ℂ))
      zero_lt_one hM_nonneg hq_nonneg hq_lt_one htail
  have hceNorm_zero : ceNorm = 0 :=
    Complex.ofReal_eq_zero.mp hceNorm_complex_zero
  have hCE_zero : CE = 0 :=
    state_eq_zero_of_stateFrobeniusNorm_eq_zero
      (Node := Node) CE hceNorm_zero
  refine ⟨arithmeticAverage (Node := Node) (E := ℝ) X, ?_⟩
  funext i
  have hi := congrFun hCE_zero i
  dsimp [CE] at hi
  unfold consensusError at hi
  exact sub_eq_zero.mp hi

/-- Complex fixed points of the alpha-zero primal period block are complex
consensus states, by applying the real consensus helper to real and imaginary
parts. -/
theorem complex_push_period_fixed_point_is_consensus
    (quad : Setup Node ℝ)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (X : ComplexRowVector Node)
    (hX :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period) X =
        (1 : ℂ) • X) :
    ∃ c : ℂ, X = fun _ : Node => c := by
  classical
  let Xre : State Node ℝ := fun i : Node => (X i).re
  let Xim : State Node ℝ := fun i : Node => (X i).im
  have hre_fixed :
      leftMul (Node := Node) (E := ℝ)
        (quad.pushLiftProduct 0 quad.period) Xre = Xre := by
    funext i
    have hi := congrFun hX i
    have hire := congrArg Complex.re hi
    simpa [Xre, complexMatrixMulVector, leftMul, smul_eq_mul] using hire
  have him_fixed :
      leftMul (Node := Node) (E := ℝ)
        (quad.pushLiftProduct 0 quad.period) Xim = Xim := by
    funext i
    have hi := congrFun hX i
    have hiim := congrArg Complex.im hi
    simpa [Xim, complexMatrixMulVector, leftMul, smul_eq_mul] using hiim
  obtain ⟨cre, hcre⟩ :=
    real_push_period_fixed_point_is_consensus
      (Node := Node) quad hstable Xre hre_fixed
  obtain ⟨cim, hcim⟩ :=
    real_push_period_fixed_point_is_consensus
      (Node := Node) quad hstable Xim him_fixed
  refine ⟨(cre : ℂ) + (cim : ℂ) * Complex.I, ?_⟩
  funext i
  have hre := congrFun hcre i
  have him := congrFun hcim i
  apply Complex.ext
  · simpa [hre, him]
  · simpa [hre, him]

/-- A unit fixed vector of the alpha-zero restricted period map with zero
primal coordinates is zero.

This is the tracker-uniqueness half of the Appendix C.1 span proof.  The
restricted coordinate representation converts the real and imaginary tracker
parts into zero-sum states, the homogeneous orbit bridge identifies one period
with the pull product, and the pull contraction forces both parts to vanish. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_fixed_top_zero_eq_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}))
    (hv :
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda 0 i0) v =
        (1 : ℂ) • v)
    (htop_zero : ∀ i : Node, v (Sum.inl i) = 0) :
    v = 0 := by
  classical
  let A0 : NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
    quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
  obtain ⟨Wre, hWre_free⟩ :=
    exists_zeroSumState_with_free_coords (Node := Node) i0
      (fun j : {i : Node // i ≠ i0} => (v (Sum.inr j)).re)
  let Sre : State Node ℝ × ZeroSumState Node ℝ :=
    ((fun _ : Node => (0 : ℝ)), Wre)
  have hcoord_re :
      restrictedStateToCoord (Node := Node) i0 Sre =
        fun a : Sum Node {i : Node // i ≠ i0} => (v a).re := by
    funext a
    cases a with
    | inl i =>
        simp [Sre, restrictedStateToCoord, htop_zero i]
    | inr j =>
        simp [Sre, restrictedStateToCoord, hWre_free j]
  have hv_re :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0
          (fun a : Sum Node {i : Node // i ≠ i0} => (v a).re) =
        fun a : Sum Node {i : Node // i ≠ i0} => (v a).re := by
    funext a
    have ha := congrFun hv a
    have hare := congrArg Complex.re ha
    simpa [A0, complexMatrixMulVector, matrixMulVector, smul_eq_mul] using hare
  have hfixed_re_coord :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0
          (restrictedStateToCoord (Node := Node) i0 Sre) =
        restrictedStateToCoord (Node := Node) i0 Sre := by
    rw [hcoord_re]
    exact hv_re
  have hrepr_re :=
    quadraticRestrictedPeriodMatrix_represents_period
      (Node := Node) quad lambda 0 i0 Sre
  have hcoord_orbit_re :
      restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda 0 0 quad.period Sre) =
        restrictedStateToCoord (Node := Node) i0 Sre := by
    calc
      restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda 0 0 quad.period Sre) =
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0
            (restrictedStateToCoord (Node := Node) i0 Sre) := by
            simpa [A0] using hrepr_re.symm
      _ = restrictedStateToCoord (Node := Node) i0 Sre := hfixed_re_coord
  have horbit_re :
      quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda 0 0 quad.period Sre = Sre :=
    restrictedStateToCoord_injective (Node := Node) i0 hcoord_orbit_re
  have htracker_orbit_re :=
    quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
      (Node := Node) quad lambda 0 quad.period Wre
  have hpull_pair_re :
      ((fun _ : Node => (0 : ℝ)),
          ⟨leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 quad.period) Wre.1,
            quad.pullLiftProduct_leftMul_zeroSum 0 quad.period Wre⟩) =
        Sre := by
    exact htracker_orbit_re.symm.trans horbit_re
  have hpull_fixed_re :
      leftMul (Node := Node) (E := ℝ)
        (quad.pullLiftProduct 0 quad.period) Wre.1 = Wre.1 := by
    exact congrArg Subtype.val (congrArg Prod.snd hpull_pair_re)
  have hWre_zero :
      Wre.1 = 0 :=
    real_pull_period_fixed_point_is_zero
      (Node := Node) quad hstable Wre hpull_fixed_re
  obtain ⟨Wim, hWim_free⟩ :=
    exists_zeroSumState_with_free_coords (Node := Node) i0
      (fun j : {i : Node // i ≠ i0} => (v (Sum.inr j)).im)
  let Sim : State Node ℝ × ZeroSumState Node ℝ :=
    ((fun _ : Node => (0 : ℝ)), Wim)
  have hcoord_im :
      restrictedStateToCoord (Node := Node) i0 Sim =
        fun a : Sum Node {i : Node // i ≠ i0} => (v a).im := by
    funext a
    cases a with
    | inl i =>
        simp [Sim, restrictedStateToCoord, htop_zero i]
    | inr j =>
        simp [Sim, restrictedStateToCoord, hWim_free j]
  have hv_im :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0
          (fun a : Sum Node {i : Node // i ≠ i0} => (v a).im) =
        fun a : Sum Node {i : Node // i ≠ i0} => (v a).im := by
    funext a
    have ha := congrFun hv a
    have haim := congrArg Complex.im ha
    simpa [A0, complexMatrixMulVector, matrixMulVector, smul_eq_mul] using haim
  have hfixed_im_coord :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0
          (restrictedStateToCoord (Node := Node) i0 Sim) =
        restrictedStateToCoord (Node := Node) i0 Sim := by
    rw [hcoord_im]
    exact hv_im
  have hrepr_im :=
    quadraticRestrictedPeriodMatrix_represents_period
      (Node := Node) quad lambda 0 i0 Sim
  have hcoord_orbit_im :
      restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda 0 0 quad.period Sim) =
        restrictedStateToCoord (Node := Node) i0 Sim := by
    calc
      restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda 0 0 quad.period Sim) =
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0
            (restrictedStateToCoord (Node := Node) i0 Sim) := by
            simpa [A0] using hrepr_im.symm
      _ = restrictedStateToCoord (Node := Node) i0 Sim := hfixed_im_coord
  have horbit_im :
      quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda 0 0 quad.period Sim = Sim :=
    restrictedStateToCoord_injective (Node := Node) i0 hcoord_orbit_im
  have htracker_orbit_im :=
    quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
      (Node := Node) quad lambda 0 quad.period Wim
  have hpull_pair_im :
      ((fun _ : Node => (0 : ℝ)),
          ⟨leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 quad.period) Wim.1,
            quad.pullLiftProduct_leftMul_zeroSum 0 quad.period Wim⟩) =
        Sim := by
    exact htracker_orbit_im.symm.trans horbit_im
  have hpull_fixed_im :
      leftMul (Node := Node) (E := ℝ)
        (quad.pullLiftProduct 0 quad.period) Wim.1 = Wim.1 := by
    exact congrArg Subtype.val (congrArg Prod.snd hpull_pair_im)
  have hWim_zero :
      Wim.1 = 0 :=
    real_pull_period_fixed_point_is_zero
      (Node := Node) quad hstable Wim hpull_fixed_im
  have hre_zero :
      ∀ a : Sum Node {i : Node // i ≠ i0}, (v a).re = 0 := by
    intro a
    cases a with
    | inl i =>
        simp [htop_zero i]
    | inr j =>
        have hz := congrFun hWre_zero j.1
        rw [← hWre_free j]
        simpa using hz
  have him_zero :
      ∀ a : Sum Node {i : Node // i ≠ i0}, (v a).im = 0 := by
    intro a
    cases a with
    | inl i =>
        simp [htop_zero i]
    | inr j =>
        have hz := congrFun hWim_zero j.1
        rw [← hWim_free j]
        simpa using hz
  funext a
  apply Complex.ext
  · exact hre_zero a
  · exact him_zero a

/-- In the top-zero branch, a nonzero complex restricted vector has a nonzero
real/imaginary zero-sum tracker component.

This is the Appendix C.1 coordinate bookkeeping needed before applying the
pull-product contraction to the tracker diagonal block. -/
theorem complex_top_zero_tracker_real_imag_zeroSum_norm_pos
    (i0 : Node)
    (v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}))
    (hv_ne_zero : v ≠ 0)
    (htop_zero : ∀ i : Node, v (Sum.inl i) = 0) :
    ∃ Wre : ZeroSumState Node ℝ, ∃ Wim : ZeroSumState Node ℝ,
      (∀ j : {i : Node // i ≠ i0}, Wre.1 j.1 = (v (Sum.inr j)).re) ∧
      (∀ j : {i : Node // i ≠ i0}, Wim.1 j.1 = (v (Sum.inr j)).im) ∧
      0 < Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2) := by
  classical
  obtain ⟨Wre, hWre_free⟩ :=
    exists_zeroSumState_with_free_coords (Node := Node) i0
      (fun j : {i : Node // i ≠ i0} => (v (Sum.inr j)).re)
  obtain ⟨Wim, hWim_free⟩ :=
    exists_zeroSumState_with_free_coords (Node := Node) i0
      (fun j : {i : Node // i ≠ i0} => (v (Sum.inr j)).im)
  refine ⟨Wre, Wim, hWre_free, hWim_free, ?_⟩
  refine Real.sqrt_pos.2 ?_
  by_contra hnot_pos
  have hsum_le :
      stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2 ≤ 0 :=
    le_of_not_gt hnot_pos
  have hre_sq_nonneg :
      0 ≤ stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 :=
    sq_nonneg _
  have him_sq_nonneg :
      0 ≤ stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2 :=
    sq_nonneg _
  have hre_sq_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 = 0 := by
    nlinarith
  have him_sq_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2 = 0 := by
    nlinarith
  have hre_norm_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 = 0 := by
    nlinarith [hre_sq_zero]
  have him_norm_zero :
      stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 = 0 := by
    nlinarith [him_sq_zero]
  have hWre_zero : Wre.1 = 0 :=
    state_eq_zero_of_stateFrobeniusNorm_eq_zero
      (Node := Node) Wre.1 hre_norm_zero
  have hWim_zero : Wim.1 = 0 :=
    state_eq_zero_of_stateFrobeniusNorm_eq_zero
      (Node := Node) Wim.1 him_norm_zero
  have hv_zero : v = 0 := by
    funext a
    cases a with
    | inl i =>
        simp [htop_zero i]
    | inr j =>
        apply Complex.ext
        · have hz := congrFun hWre_zero j.1
          rw [← hWre_free j]
          simpa using hz
        · have hz := congrFun hWim_zero j.1
          rw [← hWim_free j]
          simpa using hz
  exact hv_ne_zero hv_zero

/-- The nonzero zero-sum tracker steady response driven by a consensus
quadratic gradient in the alpha-zero Appendix C.1 system.

If `X_t = 1`, then `Z_t = lambda * 1`.  Writing
`V_t = W_t + lambda * 1`, the tracker recurrence becomes
`V_{t+1} = C_t V_t`; hence the periodic solution with zero-sum `W_t` is
`W_t = lambda * n * v_t - lambda * 1`, where `v_t` is the pull Perron vector
normalized to have sum one. -/
noncomputable def quadraticRestrictedAlphaZeroSteadyTracker
    (quad : Setup Node ℝ) (lambda : ℝ) (t : ℕ) :
    ZeroSumState Node ℝ :=
  by
    classical
    refine ⟨fun i : Node =>
        lambda * (nodeCount (Node := Node) : ℝ) * quad.perronRight t i -
          lambda, ?_⟩
    calc
      (∑ i : Node,
          (lambda * (nodeCount (Node := Node) : ℝ) *
              quad.perronRight t i - lambda)) =
          lambda * (nodeCount (Node := Node) : ℝ) *
              (∑ i : Node, quad.perronRight t i) -
            lambda * (nodeCount (Node := Node) : ℝ) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            simp [nodeCount, Finset.sum_const, nsmul_eq_mul, mul_assoc]
            ring
      _ = 0 := by
            have hsum : ∑ i : Node, quad.perronRight t i = 1 := by
              simpa [rowSum] using quad.perronRight_sum t
            rw [hsum]
            ring

/-- Phase-`t` right unit vector for the alpha-zero restricted period dynamics.

The primal component is the consensus vector.  The tracker component is the
steady zero-sum response from
`quadraticRestrictedAlphaZeroSteadyTracker`; it is generally nonzero. -/
noncomputable def quadraticRestrictedAlphaZeroRightVector
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (t : ℕ) :
    RowVector (Sum Node {i : Node // i ≠ i0}) :=
  restrictedStateToCoord (Node := Node) i0
    (fun _ : Node => (1 : ℝ),
      quadraticRestrictedAlphaZeroSteadyTracker (Node := Node) quad lambda t)

/-- The explicit alpha-zero steady state is transported by one homogeneous
C.1 step from phase `t` to phase `t+1`. -/
theorem quadraticRestrictedAlphaZeroSteadyState_step
    (quad : Setup Node ℝ) (lambda : ℝ) (t : ℕ) :
    quadraticRestrictedHomogeneousStep (Node := Node)
        quad lambda 0 t
        (fun _ : Node => (1 : ℝ),
          quadraticRestrictedAlphaZeroSteadyTracker (Node := Node)
            quad lambda t) =
      (fun _ : Node => (1 : ℝ),
        quadraticRestrictedAlphaZeroSteadyTracker (Node := Node)
          quad lambda (t + 1)) := by
  classical
  apply Prod.ext
  · funext i
    simp [quadraticRestrictedHomogeneousStep, leftMul, quad.R_row_sum,
      smul_eq_mul]
  · apply Subtype.ext
    funext i
    simp [quadraticRestrictedHomogeneousStep,
      quadraticRestrictedAlphaZeroSteadyTracker, leftMul_sub_identity,
      leftMul_add_state, leftMul_sub_state, leftMul_smul_state_local,
      leftMul, matrixMulVector, smul_eq_mul]
    have hperron := quad.C_mul_perronRight t i
    simp [matrixMulVector, smul_eq_mul] at hperron
    calc
      (∑ x : Node,
            quad.C t i x *
              (lambda * (nodeCount (Node := Node) : ℝ) *
                quad.perronRight t x - lambda)) +
          (∑ x : Node, quad.C t i x * lambda - lambda) =
          lambda * (nodeCount (Node := Node) : ℝ) *
            (∑ x : Node, quad.C t i x * quad.perronRight t x) -
            lambda := by
            have hsplit :
                (∑ x : Node,
                  quad.C t i x *
                    (lambda * (nodeCount (Node := Node) : ℝ) *
                      quad.perronRight t x - lambda)) =
                ∑ x : Node,
                  ((lambda * (nodeCount (Node := Node) : ℝ)) *
                      (quad.C t i x * quad.perronRight t x) -
                    quad.C t i x * lambda) := by
              apply Finset.sum_congr rfl
              intro x _hx
              ring
            rw [hsplit, Finset.sum_sub_distrib]
            have hfirst :
                (∑ x : Node,
                  (lambda * (nodeCount (Node := Node) : ℝ)) *
                    (quad.C t i x * quad.perronRight t x)) =
                  lambda * (nodeCount (Node := Node) : ℝ) *
                    (∑ x : Node, quad.C t i x * quad.perronRight t x) := by
              rw [Finset.mul_sum]
            rw [hfirst]
            ring
      _ = lambda * (nodeCount (Node := Node) : ℝ) *
            quad.perronRight (t + 1) i - lambda := by
            rw [hperron]

/-- Iterating the alpha-zero steady-state one-step identity gives the
phase-indexed steady response after any finite window. -/
theorem quadraticRestrictedAlphaZeroSteadyState_orbit
    (quad : Setup Node ℝ) (lambda : ℝ) (start : ℕ) :
    ∀ n : ℕ,
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 start n
        (fun _ : Node => (1 : ℝ),
          quadraticRestrictedAlphaZeroSteadyTracker (Node := Node)
            quad lambda start) =
        (fun _ : Node => (1 : ℝ),
          quadraticRestrictedAlphaZeroSteadyTracker (Node := Node)
            quad lambda (start + n)) := by
  classical
  intro n
  induction n with
  | zero =>
      simp [quadraticRestrictedHomogeneousOrbit]
  | succ n ih =>
      simp [quadraticRestrictedHomogeneousOrbit, ih]
      simpa [Nat.add_assoc] using
        quadraticRestrictedAlphaZeroSteadyState_step
          (Node := Node) quad lambda (start + n)

/-- The phase-zero explicit steady response is fixed by the true restricted
one-period alpha-zero matrix. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_right_steady
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) :
    matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0)
        (quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0) =
      quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0 := by
  classical
  rw [quadraticRestrictedAlphaZeroRightVector]
  rw [quadraticRestrictedPeriodMatrix_represents_period]
  rw [quadraticRestrictedAlphaZeroSteadyState_orbit]
  apply congrArg (restrictedStateToCoord (Node := Node) i0)
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext i
    have hper_i :
        quad.perronRight quad.period i = quad.perronRight 0 i := by
      simpa using congrFun (quad.perronRight_periodic 0) i
    simp [quadraticRestrictedAlphaZeroSteadyTracker,
      hper_i]

/-- The left unit eigenvector in the alpha-zero restricted C.1 block system is
the primal Perron row with zero tracker component.

This is the proved half of the eigentriple construction; the corresponding
right eigenvector still needs the source-described zero-sum tracker steady
response rather than a zero tracker component. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_left_perron_eigenvector
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) :
    IsLeftUnitEigenvector
      (Node := Sum Node {i : Node // i ≠ i0})
      (quadraticRestrictedPeriodMatrix (Node := Node)
        quad lambda 0 i0)
      (fun a =>
        match a with
        | Sum.inl i => quad.perronLeft 0 i
        | Sum.inr _ => 0) := by
  classical
  constructor
  · intro hzero
    obtain ⟨i⟩ := (inferInstance : Nonempty Node)
    have hi := congrFun hzero (Sum.inl i)
    simp at hi
    exact (ne_of_gt (quad.perronLeft_pos 0 i)) hi
  · funext a
    cases a with
    | inl j =>
        have hstat :=
          quad.competitor_phase_stationary
            quad.perronSequences quad.perronSequences_spec.1
            quad.perronSequences_spec.2.1
        have hpush :
            rowMulMatrix (Node := Node) (quad.perronLeft 0)
                (quad.pushLiftProduct 0 quad.period) j =
              quad.perronLeft 0 j :=
          congrFun (hstat.1 0) j
        simpa [rowMulMatrix,
          quadraticRestrictedPeriodMatrix_alpha_zero_top_left] using hpush
    | inr j =>
        simp [rowMulMatrix,
          quadraticRestrictedPeriodMatrix_alpha_zero_top_right]

/-- Source-sized alpha-zero eigentriple leaf for Appendix C.1.

At `alpha = 0`, the period matrix is block lower triangular.  The left unit
vector is the primal Perron row with zero tracker component; the right unit
vector has the primal consensus component together with the unique zero-sum
tracker steady response driven by the lower-left block. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_unit_eigentriple
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∃ right left : RowVector (Sum Node {i : Node // i ≠ i0}),
      IsRightUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right ∧
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) left ∧
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left right = 1 := by
  classical
  have htop_right :
      ∀ (i : Node) (j : {i : Node // i ≠ i0}),
        quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
          (Sum.inl i) (Sum.inr j) = 0 :=
    quadraticRestrictedPeriodMatrix_alpha_zero_top_right
      (Node := Node) quad lambda i0
  have htop_left :
      ∀ (i j : Node),
        quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
          (Sum.inl i) (Sum.inl j) =
            quad.pushLiftProduct 0 quad.period i j :=
    quadraticRestrictedPeriodMatrix_alpha_zero_top_left
      (Node := Node) quad lambda i0
  have hleft_perron :
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0)
        (fun a =>
          match a with
          | Sum.inl i => quad.perronLeft 0 i
          | Sum.inr _ => 0) :=
    quadraticRestrictedPeriodMatrix_alpha_zero_left_perron_eigenvector
      (Node := Node) quad lambda i0
  -- Exact C.1 eigentriple leaf: solve the block-lower-triangular fixed
  -- equations using the Perron period mode and the unique zero-sum tracker
  -- steady response.  The tracker component of `right` is not zero in general.
  refine ⟨quadraticRestrictedAlphaZeroRightVector
      (Node := Node) quad lambda i0 0,
    (fun a =>
      match a with
      | Sum.inl i => quad.perronLeft 0 i
      | Sum.inr _ => 0), ?_, hleft_perron, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro hzero
      obtain ⟨i⟩ := (inferInstance : Nonempty Node)
      have hi := congrFun hzero (Sum.inl i)
      simp [quadraticRestrictedAlphaZeroRightVector,
        restrictedStateToCoord] at hi
    · exact
        quadraticRestrictedPeriodMatrix_alpha_zero_right_steady
          (Node := Node) quad lambda i0
  · simp [quadraticRestrictedAlphaZeroRightVector, restrictedStateToCoord,
      rowDot]
    simpa [rowSum] using quad.perronLeft_sum 0

/-- Generic algebraic-simplicity bridge for the custom complex row-vector API.

Once the unit eigenspace is known to be spanned by the normalized right
eigenvector, the no-Jordan-chain clause follows by pairing the generalized
residual against a normalized left unit eigenvector.  This isolates the
linear-algebra part from the Appendix C.1 contraction argument that proves the
span statement for the restricted period map. -/
theorem unitEigenvalueAlgebraicallySimple_of_eigenspace_span_and_left
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (hspan :
      ∀ v : ComplexRowVector Node,
        complexMatrixMulVector (Node := Node) A0 v = (1 : ℂ) • v →
          ∃ c : ℂ, v = c • complexOfRealRow (Node := Node) right)
    (hleft : IsLeftUnitEigenvector (Node := Node) A0 left)
    (hnormalized : rowDot (Node := Node) left right = 1) :
    UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right := by
  classical
  refine ⟨hspan, ?_⟩
  intro v hvres
  let r : ComplexRowVector Node :=
    complexUnitEigenResidual (Node := Node) A0 v
  have hr_eigen :
      complexMatrixMulVector (Node := Node) A0 r = (1 : ℂ) • r := by
    simpa [r] using hvres
  obtain ⟨c, hc⟩ := hspan r hr_eigen
  have hleft_eq : rowMulMatrix (Node := Node) left A0 = left := hleft.2
  have hpair_Av :
      (∑ i : Node, (left i : ℂ) *
          complexMatrixMulVector (Node := Node) A0 v i) =
        ∑ i : Node, (left i : ℂ) * v i := by
    calc
      (∑ i : Node, (left i : ℂ) *
          complexMatrixMulVector (Node := Node) A0 v i) =
          ∑ j : Node, (rowMulMatrix (Node := Node) left A0 j : ℂ) *
            v j := by
            exact complex_rowDot_matrixMulVector_eq_rowMulMatrix_rowDot
              (Node := Node) left v A0
      _ = ∑ j : Node, (left j : ℂ) * v j := by
            rw [hleft_eq]
  have hdot_r_zero :
      (∑ i : Node, (left i : ℂ) * r i) = 0 := by
    unfold r complexUnitEigenResidual
    simp only [Pi.sub_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [hpair_Av]
    ring
  have hnormalized_complex :
      (∑ i : Node, (left i : ℂ) * (right i : ℂ)) = 1 := by
    have hcast := congrArg Complex.ofReal hnormalized
    simpa [rowDot] using hcast
  have hdot_r_eq_c :
      (∑ i : Node, (left i : ℂ) * r i) = c := by
    rw [hc]
    simp only [Pi.smul_apply, complexOfRealRow, smul_eq_mul]
    calc
      (∑ i : Node, (left i : ℂ) * (c * (right i : ℂ))) =
          c * ∑ i : Node, (left i : ℂ) * (right i : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = c := by rw [hnormalized_complex, mul_one]
  have hc_zero : c = 0 := by
    rw [← hdot_r_eq_c, hdot_r_zero]
  have hr_zero : r = 0 := by
    rw [hc, hc_zero]
    simp
  have hresidual_zero :
      complexUnitEigenResidual (Node := Node) A0 v = 0 := by
    simpa [r] using hr_zero
  have hAv : complexMatrixMulVector (Node := Node) A0 v = v := by
    simpa [complexUnitEigenResidual] using
      (sub_eq_zero.mp hresidual_zero)
  simpa [one_smul] using hAv

/-- Exact remaining unit-eigenspace span leaf for the Appendix C.1 restricted
alpha-zero period map.

This is the contraction/invertibility part of the source proof: the top
push-product equation forces the primal component to be the consensus mode,
and the zero-sum pull block then has a unique tracker response.  The statement
is deliberately smaller than `UnitEigenvalueAlgebraicallySimple`; the generic
left-eigenvector pairing above discharges the no-Jordan clause once this span
is available. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_unit_eigenspace_span
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (heigen :
      IsRightUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right ∧
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) left ∧
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left right = 1) :
    ∀ v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}),
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda 0 i0) v =
        (1 : ℂ) • v →
        ∃ c : ℂ, v = c • complexOfRealRow
          (Node := Sum Node {i : Node // i ≠ i0}) right := by
  classical
  intro v hv
  let A0 : NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
    quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
  have htop :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period)
          (fun i : Node => v (Sum.inl i)) =
        (1 : ℂ) • (fun i : Node => v (Sum.inl i)) := by
    exact
      quadraticRestrictedPeriodMatrix_alpha_zero_complex_top_eigen_equation
        (Node := Node) quad lambda i0 (1 : ℂ) v hv
  have hright_fixed := heigen.1.2
  have hleft_fixed := heigen.2.1.2
  have hnormalized := heigen.2.2
  have _hsource_contraction := hstable
  have _hunit_top_equation := htop
  have _hright_fixed := hright_fixed
  have _hleft_fixed := hleft_fixed
  have _hnormalized := hnormalized
  -- Exact C.1 span leaf: use the repeated push consensus-error contraction
  -- to show the top component of `v` is consensus, then use the repeated
  -- zero-sum pull contraction to identify the unique tracker response with
  -- the tracker coordinates of `right`.
  obtain ⟨c_top, hc_top⟩ :=
    complex_push_period_fixed_point_is_consensus
      (Node := Node) quad hstable (fun i : Node => v (Sum.inl i)) htop
  have _hprimal_consensus : (fun i : Node => v (Sum.inl i)) =
      fun _ : Node => c_top := hc_top
  have hright_complex_fixed :
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda 0 i0)
          (complexOfRealRow
            (Node := Sum Node {i : Node // i ≠ i0}) right) =
        (1 : ℂ) •
          complexOfRealRow
            (Node := Sum Node {i : Node // i ≠ i0}) right := by
    funext a
    have ha := congrArg Complex.ofReal (congrFun hright_fixed a)
    simpa [complexMatrixMulVector, complexOfRealRow, matrixMulVector] using ha
  have hright_top :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period)
          (fun i : Node =>
            complexOfRealRow
              (Node := Sum Node {i : Node // i ≠ i0}) right
              (Sum.inl i)) =
        (1 : ℂ) •
          (fun i : Node =>
            complexOfRealRow
              (Node := Sum Node {i : Node // i ≠ i0}) right
              (Sum.inl i)) := by
    exact
      quadraticRestrictedPeriodMatrix_alpha_zero_complex_top_eigen_equation
        (Node := Node) quad lambda i0 (1 : ℂ)
        (complexOfRealRow
          (Node := Sum Node {i : Node // i ≠ i0}) right)
        hright_complex_fixed
  obtain ⟨c_right, hc_right_top⟩ :=
    complex_push_period_fixed_point_is_consensus
      (Node := Node) quad hstable
      (fun i : Node =>
        complexOfRealRow
          (Node := Sum Node {i : Node // i ≠ i0}) right
          (Sum.inl i))
      hright_top
  have _hright_primal_consensus :
      (fun i : Node =>
        complexOfRealRow
          (Node := Sum Node {i : Node // i ≠ i0}) right
          (Sum.inl i)) =
        fun _ : Node => c_right := hc_right_top
  have hright_top_nonzero : c_right ≠ 0 := by
    intro hc_right_zero
    have hright_top_zero :
        ∀ i : Node,
          complexOfRealRow
              (Node := Sum Node {i : Node // i ≠ i0}) right
              (Sum.inl i) = 0 := by
      intro i
      rw [congrFun hc_right_top i, hc_right_zero]
    have hright_zero_complex :
        complexOfRealRow
            (Node := Sum Node {i : Node // i ≠ i0}) right = 0 :=
      quadraticRestrictedPeriodMatrix_alpha_zero_fixed_top_zero_eq_zero
        (Node := Node) quad lambda i0 hstable
        (complexOfRealRow
          (Node := Sum Node {i : Node // i ≠ i0}) right)
        hright_complex_fixed hright_top_zero
    have hright_zero : right = 0 := by
      funext a
      have ha := congrFun hright_zero_complex a
      exact Complex.ofReal_eq_zero.mp
        (by simpa [complexOfRealRow] using ha)
    exact heigen.1.1 hright_zero
  let c : ℂ := c_top / c_right
  let z : ComplexRowVector (Sum Node {i : Node // i ≠ i0}) :=
    v - c • complexOfRealRow
      (Node := Sum Node {i : Node // i ≠ i0}) right
  have hvA :
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) A0 v =
        (1 : ℂ) • v := by
    simpa [A0] using hv
  have hrA :
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) A0
          (complexOfRealRow
            (Node := Sum Node {i : Node // i ≠ i0}) right) =
        (1 : ℂ) •
          complexOfRealRow
            (Node := Sum Node {i : Node // i ≠ i0}) right := by
    simpa [A0] using hright_complex_fixed
  have hz_fixed :
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) A0 z =
        (1 : ℂ) • z := by
    funext a
    have hv_a := congrFun hvA a
    have hr_a := congrFun hrA a
    calc
      complexMatrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) A0 z a =
          complexMatrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) A0 v a -
            c *
              complexMatrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0}) A0
                (complexOfRealRow
                  (Node := Sum Node {i : Node // i ≠ i0}) right) a := by
            simp [z, complexMatrixMulVector, Finset.sum_sub_distrib,
              Finset.mul_sum, mul_sub, mul_comm, mul_left_comm, mul_assoc,
              smul_eq_mul]
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ = v a -
            c *
              complexOfRealRow
                (Node := Sum Node {i : Node // i ≠ i0}) right a := by
            rw [hv_a, hr_a]
            simp [smul_eq_mul]
      _ = ((1 : ℂ) • z) a := by
            simp [z, smul_eq_mul]
  have hz_top_zero : ∀ i : Node, z (Sum.inl i) = 0 := by
    intro i
    have hv_i := congrFun hc_top i
    have hr_i := congrFun hc_right_top i
    dsimp [z, c]
    rw [hv_i, hr_i]
    rw [div_mul_cancel₀ c_top hright_top_nonzero]
    ring
  have hz_zero :
      z = 0 :=
    quadraticRestrictedPeriodMatrix_alpha_zero_fixed_top_zero_eq_zero
      (Node := Node) quad lambda i0 hstable z
      (by simpa [A0] using hz_fixed) hz_top_zero
  refine ⟨c, ?_⟩
  funext a
  have ha := congrFun hz_zero a
  dsimp [z] at ha
  exact sub_eq_zero.mp ha

/-- Source-sized alpha-zero algebraic-simplicity leaf for Appendix C.1.

This is the no-Jordan-chain and one-dimensional-unit-eigenspace part of the
block-triangular argument.  It uses invertibility of `I - pull period` on the
zero-sum tracker block and contraction of the primal disagreement block. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_unit_algebraicallySimple
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (heigen :
      IsRightUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right ∧
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) left ∧
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left right = 1) :
    UnitEigenvalueAlgebraicallySimple
      (Node := Sum Node {i : Node // i ≠ i0})
      (quadraticRestrictedPeriodMatrix (Node := Node)
        quad lambda 0 i0) right := by
  classical
  let A0 : NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
    quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
  have hunit_top_equation :
      ∀ v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}),
        complexMatrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) A0 v =
          (1 : ℂ) • v →
        complexMatrixMulVector (Node := Node)
            (quad.pushLiftProduct 0 quad.period)
            (fun i : Node => v (Sum.inl i)) =
          (1 : ℂ) • (fun i : Node => v (Sum.inl i)) := by
    intro v hv
    exact
      quadraticRestrictedPeriodMatrix_alpha_zero_complex_top_eigen_equation
        (Node := Node) quad lambda i0 (1 : ℂ) v
        (by simpa [A0] using hv)
  have hgeneralized_residual_top_equation :
      ∀ v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}),
        complexMatrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
            A0 (complexUnitEigenResidual
              (Node := Sum Node {i : Node // i ≠ i0}) A0 v) =
          (1 : ℂ) •
            complexUnitEigenResidual
              (Node := Sum Node {i : Node // i ≠ i0}) A0 v →
        complexMatrixMulVector (Node := Node)
            (quad.pushLiftProduct 0 quad.period)
            (fun i : Node =>
              complexUnitEigenResidual
                (Node := Sum Node {i : Node // i ≠ i0}) A0 v (Sum.inl i)) =
          (1 : ℂ) •
            (fun i : Node =>
              complexUnitEigenResidual
                (Node := Sum Node {i : Node // i ≠ i0}) A0 v (Sum.inl i)) := by
    intro v hgen
    exact
      quadraticRestrictedPeriodMatrix_alpha_zero_complex_top_eigen_equation
        (Node := Node) quad lambda i0 (1 : ℂ)
        (complexUnitEigenResidual
          (Node := Sum Node {i : Node // i ≠ i0}) A0 v)
        (by simpa [A0] using hgen)
  have _hunit_top_equation_used := hunit_top_equation
  have _hgeneralized_residual_top_equation_used :=
    hgeneralized_residual_top_equation
  have hspan :
      ∀ v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}),
        complexMatrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) A0 v =
          (1 : ℂ) • v →
          ∃ c : ℂ, v = c • complexOfRealRow
            (Node := Sum Node {i : Node // i ≠ i0}) right := by
    intro v hv
    exact
      quadraticRestrictedPeriodMatrix_alpha_zero_unit_eigenspace_span
        (Node := Node) quad lambda i0 _hquad hstable right left heigen v
        (by simpa [A0] using hv)
  exact
    unitEigenvalueAlgebraicallySimple_of_eigenspace_span_and_left
      (Node := Sum Node {i : Node // i ≠ i0}) A0 right left hspan
      (by simpa [A0] using heigen.2.1)
      heigen.2.2

/-- Exact eigenvector-level stable-radius leaf for the Appendix C.1 alpha-zero
restricted period map.

The surrounding theorem only packages the radius.  This leaf exposes the
actual spectral-radius conversion target: a non-unit complex eigenvector of
the block-lower-triangular alpha-zero period map must have multiplier bounded
by the midpoint radius `(contractionRate + 1) / 2`, using the repeated
push-disagreement and pull-zero-sum contraction estimates. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_nonunit_eigenvector_mod_le
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (gamma : ℂ) (v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}))
    (hv_ne_zero : v ≠ 0)
    (hv :
      complexMatrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) v =
        gamma • v)
    (hgamma_ne_one : gamma ≠ (1 : ℂ)) :
    ‖gamma‖ ≤ (quad.contractionRate + 1) / 2 := by
  classical
  have htop :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period)
          (fun i : Node => v (Sum.inl i)) =
        gamma • (fun i : Node => v (Sum.inl i)) := by
    exact
      quadraticRestrictedPeriodMatrix_alpha_zero_complex_top_eigen_equation
        (Node := Node) quad lambda i0 gamma v hv
  have _hsource_contraction := hstable
  have _hnonzero := hv_ne_zero
  have _hnonunit := hgamma_ne_one
  have _htop_equation := htop
  -- Exact C.1 stable-spectrum leaf: split on whether the primal component is
  -- zero.  In the nonzero top branch, repeated push consensus-error
  -- contraction bounds the multiplier.  In the zero top branch, the restricted
  -- tracker component is nonzero and the tracker-only orbit bridge reduces the
  -- claim to repeated pull contraction on the zero-sum block.
  let Xtop : ComplexRowVector Node := fun i : Node => v (Sum.inl i)
  have htopX :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period) Xtop =
        gamma • Xtop := by
    simpa [Xtop] using htop
  have hperiod_rate_mid :
      quad.contractionRate ^ quad.period <
        (quad.contractionRate + 1) / 2 :=
    contractionRate_pow_period_lt_mid
      (Node := Node) quad hstable.1 hstable.2.1
  by_cases htop_zero : ∀ i : Node, Xtop i = 0
  · have htop_zero_v : ∀ i : Node, v (Sum.inl i) = 0 := by
      intro i
      simpa [Xtop] using htop_zero i
    have hperiod_rate_nonneg :
        0 ≤ quad.contractionRate ^ quad.period :=
      pow_nonneg hstable.1 quad.period
    -- Remaining tracker branch: reconstruct the real and imaginary zero-sum
    -- tracker states from the free restricted coordinates, identify all
    -- repeated restricted-period iterates with pull products, then feed the
    -- resulting all-powers estimate to
    -- `scalar_pow_le_geometric_for_all_forces_base_le` with
    -- `hperiod_rate_mid`.
    obtain ⟨Wre, Wim, hWre_free, hWim_free, hc_pos_raw⟩ :=
      complex_top_zero_tracker_real_imag_zeroSum_norm_pos
        (Node := Node) i0 v hv_ne_zero htop_zero_v
    let c : ℝ :=
      Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2)
    have hc_pos : 0 < c := by
      simpa [c] using hc_pos_raw
    let A0 : NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
      quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
    have hrestricted_iter :
        ∀ m : ℕ,
          complexMatrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m) v =
            gamma ^ m • v :=
      complex_matrixPower_eigen_iterate
        (Node := Sum Node {i : Node // i ≠ i0}) A0 gamma v (by
          simpa [A0] using hv)
    have hbound :
        ∀ N : ℕ,
          ‖gamma‖ ^ (N + 1) * c ≤
            quad.columnContractionConstant *
              (quad.contractionRate ^ quad.period) ^ (N + 1) * c := by
      intro N
      -- Remaining bridge: use `hrestricted_iter (N+1)` plus
      -- `quadraticRestrictedPeriodMatrix_represents_period` and
      -- `quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only` to
      -- identify these powered restricted coordinates with
      -- `quad.pullLiftProduct 0 ((N+1) * quad.period)` on `Wre` and `Wim`,
      -- then combine the two real pull-contraction estimates from
      -- `hstable.2.2.1`.
      let m : ℕ := N + 1
      let Sre : State Node ℝ × ZeroSumState Node ℝ :=
        ((fun _ : Node => (0 : ℝ)), Wre)
      let Sim : State Node ℝ × ZeroSumState Node ℝ :=
        ((fun _ : Node => (0 : ℝ)), Wim)
      have hcoord_re :
          restrictedStateToCoord (Node := Node) i0 Sre =
            fun a : Sum Node {i : Node // i ≠ i0} => (v a).re := by
        funext a
        cases a with
        | inl i =>
            simp [Sre, restrictedStateToCoord, htop_zero_v i]
        | inr j =>
            simp [Sre, restrictedStateToCoord, hWre_free j]
      have hcoord_im :
          restrictedStateToCoord (Node := Node) i0 Sim =
            fun a : Sum Node {i : Node // i ≠ i0} => (v a).im := by
        funext a
        cases a with
        | inl i =>
            simp [Sim, restrictedStateToCoord, htop_zero_v i]
        | inr j =>
            simp [Sim, restrictedStateToCoord, hWim_free j]
      have hpower_re :
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (restrictedStateToCoord (Node := Node) i0 Sre) =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).re := by
        calc
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (restrictedStateToCoord (Node := Node) i0 Sre) =
            matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (fun a : Sum Node {i : Node // i ≠ i0} => (v a).re) := by
              rw [hcoord_re]
          _ =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).re := by
              funext a
              have ha := congrFun (hrestricted_iter m) a
              have hare := congrArg Complex.re ha
              simpa [complexMatrixMulVector, matrixMulVector, smul_eq_mul]
                using hare
      have hpower_im :
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (restrictedStateToCoord (Node := Node) i0 Sim) =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).im := by
        calc
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (restrictedStateToCoord (Node := Node) i0 Sim) =
            matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (fun a : Sum Node {i : Node // i ≠ i0} => (v a).im) := by
              rw [hcoord_im]
          _ =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).im := by
              funext a
              have ha := congrFun (hrestricted_iter m) a
              have haim := congrArg Complex.im ha
              simpa [complexMatrixMulVector, matrixMulVector, smul_eq_mul]
                using haim
      have horbit_coord_re :
          restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit
                (Node := Node) quad lambda 0 0 (m * quad.period) Sre) =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).re := by
        calc
          restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit
                (Node := Node) quad lambda 0 0 (m * quad.period) Sre) =
            matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (restrictedStateToCoord (Node := Node) i0 Sre) := by
              simpa [A0] using
                (quadraticRestrictedPeriodMatrix_power_represents_period_orbit
                  (Node := Node) quad lambda 0 i0 m Sre).symm
          _ =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).re := hpower_re
      have horbit_coord_im :
          restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit
                (Node := Node) quad lambda 0 0 (m * quad.period) Sim) =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).im := by
        calc
          restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit
                (Node := Node) quad lambda 0 0 (m * quad.period) Sim) =
            matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A0 m)
              (restrictedStateToCoord (Node := Node) i0 Sim) := by
              simpa [A0] using
                (quadraticRestrictedPeriodMatrix_power_represents_period_orbit
                  (Node := Node) quad lambda 0 i0 m Sim).symm
          _ =
            fun a : Sum Node {i : Node // i ≠ i0} =>
              ((gamma ^ m • v) a).im := hpower_im
      have htracker_orbit_re :=
        quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
          (Node := Node) quad lambda 0 (m * quad.period) Wre
      have htracker_orbit_im :=
        quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
          (Node := Node) quad lambda 0 (m * quad.period) Wim
      have hpull_free_re :
          ∀ j : {i : Node // i ≠ i0},
            leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct 0 (m * quad.period)) Wre.1 j.1 =
              ((gamma ^ m) * v (Sum.inr j)).re := by
        intro j
        have hcoord :
            restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)),
                  ⟨leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wre.1,
                    quad.pullLiftProduct_leftMul_zeroSum 0
                      (m * quad.period) Wre⟩) =
              fun a : Sum Node {i : Node // i ≠ i0} =>
                ((gamma ^ m • v) a).re := by
          rw [← htracker_orbit_re]
          exact horbit_coord_re
        have hj := congrFun hcoord (Sum.inr j)
        simpa [restrictedStateToCoord, smul_eq_mul] using hj
      have hpull_free_im :
          ∀ j : {i : Node // i ≠ i0},
            leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct 0 (m * quad.period)) Wim.1 j.1 =
              ((gamma ^ m) * v (Sum.inr j)).im := by
        intro j
        have hcoord :
            restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)),
                  ⟨leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wim.1,
                    quad.pullLiftProduct_leftMul_zeroSum 0
                      (m * quad.period) Wim⟩) =
              fun a : Sum Node {i : Node // i ≠ i0} =>
                ((gamma ^ m • v) a).im := by
          rw [← htracker_orbit_im]
          exact horbit_coord_im
        have hj := congrFun hcoord (Sum.inr j)
        simpa [restrictedStateToCoord, smul_eq_mul] using hj
      have hpull_contract_re :
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct 0 (m * quad.period)) Wre.1) ≤
            quad.columnContractionConstant *
              quad.contractionRate ^ (m * quad.period) *
              stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 :=
        hstable.2.2.1 0 (m * quad.period) Wre
      have hpull_contract_im :
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct 0 (m * quad.period)) Wim.1) ≤
            quad.columnContractionConstant *
              quad.contractionRate ^ (m * quad.period) *
              stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 :=
        hstable.2.2.1 0 (m * quad.period) Wim
      have hm : m = N + 1 := rfl
      have hpow_period :
          quad.contractionRate ^ (m * quad.period) =
            (quad.contractionRate ^ quad.period) ^ (N + 1) := by
        rw [hm, Nat.mul_comm, pow_mul]
      have hcol_nonneg : 0 ≤ quad.columnContractionConstant := by
        dsimp [Setup.columnContractionConstant]
        exact div_nonneg (Real.sqrt_nonneg _) quad.contractionDelta_pos.le
      have hfactor_nonneg :
          0 ≤ quad.columnContractionConstant *
            quad.contractionRate ^ (m * quad.period) :=
        mul_nonneg hcol_nonneg (pow_nonneg hstable.1 _)
      have hcombined_contract_raw :
          Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wre.1) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wim.1) ^ 2) ≤
            (quad.columnContractionConstant *
              quad.contractionRate ^ (m * quad.period)) *
              Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2) :=
        sqrt_sq_add_sq_le_mul_sqrt_sq_add_sq
          (K := quad.columnContractionConstant *
            quad.contractionRate ^ (m * quad.period))
          (a := stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1)
          (b := stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1)
          (x := stateFrobeniusNorm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) Wre.1))
          (y := stateFrobeniusNorm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) Wim.1))
          hfactor_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          hpull_contract_re hpull_contract_im
      have hcombined_contract :
          Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wre.1) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wim.1) ^ 2) ≤
            quad.columnContractionConstant *
              (quad.contractionRate ^ quad.period) ^ (N + 1) * c := by
        simpa [c, hpow_period, mul_assoc] using hcombined_contract_raw
      have hcombined_lower :
          ‖gamma‖ ^ (N + 1) * c ≤
            Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wre.1) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (leftMul (Node := Node) (E := ℝ)
                      (quad.pullLiftProduct 0 (m * quad.period)) Wim.1) ^ 2) := by
        let Yre : ZeroSumState Node ℝ :=
          ⟨leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) Wre.1,
            quad.pullLiftProduct_leftMul_zeroSum 0
              (m * quad.period) Wre⟩
        let Yim : ZeroSumState Node ℝ :=
          ⟨leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) Wim.1,
            quad.pullLiftProduct_leftMul_zeroSum 0
              (m * quad.period) Wim⟩
        have hscaled_free_re :
            ∀ j : {i : Node // i ≠ i0},
              Yre.1 j.1 =
                ((gamma ^ m) *
                  ((Wre.1 j.1 : ℂ) + (Wim.1 j.1 : ℂ) * Complex.I)).re := by
          intro j
          have hvj :
              v (Sum.inr j) =
                ((Wre.1 j.1 : ℂ) + (Wim.1 j.1 : ℂ) * Complex.I) := by
            apply Complex.ext
            · simpa using (hWre_free j).symm
            · simpa using (hWim_free j).symm
          rw [← hvj]
          simpa [Yre] using hpull_free_re j
        have hscaled_free_im :
            ∀ j : {i : Node // i ≠ i0},
              Yim.1 j.1 =
                ((gamma ^ m) *
                  ((Wre.1 j.1 : ℂ) + (Wim.1 j.1 : ℂ) * Complex.I)).im := by
          intro j
          have hvj :
              v (Sum.inr j) =
                ((Wre.1 j.1 : ℂ) + (Wim.1 j.1 : ℂ) * Complex.I) := by
            apply Complex.ext
            · simpa using (hWre_free j).symm
            · simpa using (hWim_free j).symm
          rw [← hvj]
          simpa [Yim] using hpull_free_im j
        have hnorm_scaled :
            Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ) Yre.1 ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ) Yim.1 ^ 2) =
              ‖gamma ^ m‖ *
                Real.sqrt
                  (stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 +
                    stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2) :=
          zero_sum_complex_tracker_combined_norm_scaled
            (Node := Node) i0 Yre Yim Wre Wim (gamma ^ m)
            hscaled_free_re hscaled_free_im
        have hnorm_eq :
            Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ)
                      (leftMul (Node := Node) (E := ℝ)
                        (quad.pullLiftProduct 0 (m * quad.period)) Wre.1) ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ)
                      (leftMul (Node := Node) (E := ℝ)
                        (quad.pullLiftProduct 0 (m * quad.period)) Wim.1) ^ 2) =
              ‖gamma‖ ^ (N + 1) * c := by
          calc
            Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ)
                      (leftMul (Node := Node) (E := ℝ)
                        (quad.pullLiftProduct 0 (m * quad.period)) Wre.1) ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ)
                      (leftMul (Node := Node) (E := ℝ)
                        (quad.pullLiftProduct 0 (m * quad.period)) Wim.1) ^ 2) =
                Real.sqrt
                  (stateFrobeniusNorm (Node := Node) (E := ℝ) Yre.1 ^ 2 +
                    stateFrobeniusNorm (Node := Node) (E := ℝ) Yim.1 ^ 2) := by
                rfl
            _ =
                ‖gamma ^ m‖ *
                  Real.sqrt
                    (stateFrobeniusNorm (Node := Node) (E := ℝ) Wre.1 ^ 2 +
                      stateFrobeniusNorm (Node := Node) (E := ℝ) Wim.1 ^ 2) :=
                hnorm_scaled
            _ = ‖gamma‖ ^ (N + 1) * c := by
                rw [norm_pow, hm]
        exact le_of_eq hnorm_eq.symm
      exact hcombined_lower.trans hcombined_contract
    exact
      scalar_pow_le_geometric_for_all_forces_base_le
        (a := ‖gamma‖)
        (q := quad.contractionRate ^ quad.period)
        (theta := (quad.contractionRate + 1) / 2)
        (M := quad.columnContractionConstant)
        (c := c)
        (norm_nonneg gamma) hperiod_rate_nonneg hc_pos
        hperiod_rate_mid hbound
  · have hXtop_ne : Xtop ≠ 0 := by
      intro hXtop_zero
      apply htop_zero
      intro i
      exact congrFun hXtop_zero i
    have hiter :
        ∀ m : ℕ,
          complexMatrixMulVector (Node := Node)
              (quad.pushLiftProduct 0 (m * quad.period)) Xtop =
            gamma ^ m • Xtop :=
      complex_pushLiftProduct_period_eigen_iterate
        (Node := Node) quad gamma Xtop htopX
    have hperiod_rate_nonneg :
        0 ≤ quad.contractionRate ^ quad.period :=
      pow_nonneg hstable.1 quad.period
    -- Remaining push branch: show the complex consensus-error norm of `Xtop`
    -- is nonzero using `hgamma_ne_one`, then combine the repeated eigen
    -- equation `hiter` with the all-length push contraction and the scalar
    -- helper to bound `‖gamma‖`.
    let Xre : State Node ℝ := fun i : Node => (Xtop i).re
    let Xim : State Node ℝ := fun i : Node => (Xtop i).im
    let c : ℝ :=
      Real.sqrt
        (stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 +
          stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xim) ^ 2)
    have hc_pos : 0 < c := by
      simpa [c, Xre, Xim] using
        complex_push_nonunit_eigen_consensus_error_norm_pos
          (Node := Node) quad gamma Xtop hXtop_ne htopX hgamma_ne_one
    have hbound :
        ∀ N : ℕ,
          ‖gamma‖ ^ (N + 1) * c ≤
            quad.rowContractionConstant *
              (quad.contractionRate ^ quad.period) ^ (N + 1) * c := by
      intro N
      let m : ℕ := N + 1
      let Yre : State Node ℝ :=
        leftMul (Node := Node) (E := ℝ)
          (quad.pushLiftProduct 0 (m * quad.period)) Xre
      let Yim : State Node ℝ :=
        leftMul (Node := Node) (E := ℝ)
          (quad.pushLiftProduct 0 (m * quad.period)) Xim
      have hXY :
          (fun i : Node => (Yre i : ℂ) + (Yim i : ℂ) * Complex.I) =
            (gamma ^ m) •
              (fun i : Node => (Xre i : ℂ) + (Xim i : ℂ) * Complex.I) := by
        funext i
        have hi := congrFun (hiter m) i
        have hre_fun :=
          congrFun
            (complexMatrixMulVector_re_eq_leftMul
              (Node := Node)
              (quad.pushLiftProduct 0 (m * quad.period)) Xtop) i
        have him_fun :=
          congrFun
            (complexMatrixMulVector_im_eq_leftMul
              (Node := Node)
              (quad.pushLiftProduct 0 (m * quad.period)) Xtop) i
        apply Complex.ext
        · have hire := congrArg Complex.re hi
          rw [hre_fun] at hire
          simpa [Yre, Xre, Xim, smul_eq_mul] using hire
        · have hiim := congrArg Complex.im hi
          rw [him_fun] at hiim
          simpa [Yim, Xre, Xim, smul_eq_mul] using hiim
      have hnorm_scaled :
          Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) =
            ‖gamma ^ m‖ * c := by
        simpa [c] using
          complex_consensus_error_combined_norm_scaled
            (Node := Node) Yre Yim Xre Xim (gamma ^ m) hXY
      have hpush_contract_re :
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ) Yre) ≤
            quad.rowContractionConstant *
              quad.contractionRate ^ (m * quad.period) *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) Xre) := by
        simpa [Yre] using hstable.2.2.2 0 (m * quad.period) Xre
      have hpush_contract_im :
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ) Yim) ≤
            quad.rowContractionConstant *
              quad.contractionRate ^ (m * quad.period) *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) Xim) := by
        simpa [Yim] using hstable.2.2.2 0 (m * quad.period) Xim
      have hm : m = N + 1 := rfl
      have hpow_period :
          quad.contractionRate ^ (m * quad.period) =
            (quad.contractionRate ^ quad.period) ^ (N + 1) := by
        rw [hm, Nat.mul_comm, pow_mul]
      have hrow_nonneg : 0 ≤ quad.rowContractionConstant := by
        dsimp [Setup.rowContractionConstant]
        exact div_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          quad.contractionDelta_pos.le
      have hfactor_nonneg :
          0 ≤ quad.rowContractionConstant *
            quad.contractionRate ^ (m * quad.period) :=
        mul_nonneg hrow_nonneg (pow_nonneg hstable.1 _)
      have hcombined_contract_raw :
          Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) ≤
            (quad.rowContractionConstant *
              quad.contractionRate ^ (m * quad.period)) *
              Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (consensusError (Node := Node) (E := ℝ) Xre) ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (consensusError (Node := Node) (E := ℝ) Xim) ^ 2) :=
        sqrt_sq_add_sq_le_mul_sqrt_sq_add_sq
          (K := quad.rowContractionConstant *
            quad.contractionRate ^ (m * quad.period))
          (a := stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xre))
          (b := stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Xim))
          (x := stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Yre))
          (y := stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ) Yim))
          hfactor_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          hpush_contract_re hpush_contract_im
      have hcombined_contract :
          Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) ≤
            quad.rowContractionConstant *
              (quad.contractionRate ^ quad.period) ^ (N + 1) * c := by
        simpa [c, hpow_period, mul_assoc] using hcombined_contract_raw
      have hcombined_lower :
          ‖gamma‖ ^ (N + 1) * c ≤
            Real.sqrt
              (stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
                stateFrobeniusNorm (Node := Node) (E := ℝ)
                  (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) := by
        have hnorm_eq :
            Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) =
              ‖gamma‖ ^ (N + 1) * c := by
          calc
            Real.sqrt
                (stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (consensusError (Node := Node) (E := ℝ) Yre) ^ 2 +
                  stateFrobeniusNorm (Node := Node) (E := ℝ)
                    (consensusError (Node := Node) (E := ℝ) Yim) ^ 2) =
                ‖gamma ^ m‖ * c := hnorm_scaled
            _ = ‖gamma‖ ^ (N + 1) * c := by
                rw [norm_pow, hm]
        exact le_of_eq hnorm_eq.symm
      exact hcombined_lower.trans hcombined_contract
    exact
      scalar_pow_le_geometric_for_all_forces_base_le
        (a := ‖gamma‖)
        (q := quad.contractionRate ^ quad.period)
        (theta := (quad.contractionRate + 1) / 2)
        (M := quad.rowContractionConstant)
        (c := c)
        (norm_nonneg gamma) hperiod_rate_nonneg hc_pos
        hperiod_rate_mid hbound

/-- Source-sized alpha-zero stable-disk leaf for Appendix C.1.

The proof chooses `r0 < 1` from the asymptotic geometric contraction of the
primal-disagreement and zero-sum tracker diagonal blocks, then uses the
block-lower-triangular eigen-equations to put every non-unit eigenvalue in
`|z| ≤ r0`. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_stable_disk
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X)))
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (_heigen :
      IsRightUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right ∧
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) left ∧
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left right = 1) :
    ∃ r0 : ℝ,
      0 ≤ r0 ∧ r0 < 1 ∧
        ∀ gamma : ℂ,
          IsComplexRightEigenvalue
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda 0 i0) gamma →
            gamma ≠ (1 : ℂ) → ‖gamma‖ ≤ r0 := by
  classical
  let r0 : ℝ := (quad.contractionRate + 1) / 2
  have hr0_nonneg : 0 ≤ r0 := by
    dsimp [r0]
    linarith [hstable.1]
  have hr0_lt_one : r0 < 1 := by
    dsimp [r0]
    linarith [hstable.2.1]
  refine ⟨r0, hr0_nonneg, hr0_lt_one, ?_⟩
  intro gamma hgamma hgamma_ne_one
  rcases hgamma with ⟨v, hv_ne_zero, hv⟩
  dsimp [r0]
  exact
    quadraticRestrictedPeriodMatrix_alpha_zero_nonunit_eigenvector_mod_le
      (Node := Node) quad lambda i0 _hquad hstable gamma v hv_ne_zero hv
      hgamma_ne_one

/-- The remaining Appendix C.1 alpha-zero spectral certificate for the true
restricted period matrix.

At `alpha = 0`, the period map is block lower triangular.  The top diagonal
block is the push product with one consensus unit mode, the bottom diagonal
block is the pull product on the zero-sum tracker coordinates, and both
non-slow blocks are stable by `PeriodicProductContraction`.  The right unit
eigenvector may have a nonzero tracker component, determined by the unique
zero-sum steady response. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_spectrum
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hstable :
      0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
        (∀ (t j : ℕ) (W : ZeroSumState Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pullLiftProduct t j) W.1) ≤
            quad.columnContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
        (∀ (t j : ℕ) (X : State Node ℝ),
          stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ)
                (leftMul (Node := Node) (E := ℝ)
                  (quad.pushLiftProduct t j) X)) ≤
            quad.rowContractionConstant * quad.contractionRate ^ j *
              stateFrobeniusNorm (Node := Node) (E := ℝ)
                (consensusError (Node := Node) (E := ℝ) X))) :
    ∃ r0 right left,
      right =
          quadraticRestrictedAlphaZeroRightVector
            (Node := Node) quad lambda i0 0 ∧
      left =
          (fun a =>
            match a with
            | Sum.inl i => quad.perronLeft 0 i
            | Sum.inr _ => 0) ∧
      SimpleIsolatedUnitEigenvalueStableSpectrum
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) r0 right left := by
  classical
  let right : RowVector (Sum Node {i : Node // i ≠ i0}) :=
    quadraticRestrictedAlphaZeroRightVector
      (Node := Node) quad lambda i0 0
  let left : RowVector (Sum Node {i : Node // i ≠ i0}) :=
    fun a =>
      match a with
      | Sum.inl i => quad.perronLeft 0 i
      | Sum.inr _ => 0
  have hright :
      IsRightUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right := by
    refine ⟨?_, ?_⟩
    · intro hzero
      obtain ⟨i⟩ := (inferInstance : Nonempty Node)
      have hi := congrFun hzero (Sum.inl i)
      simp [right, quadraticRestrictedAlphaZeroRightVector,
        restrictedStateToCoord] at hi
    · simpa [right] using
        quadraticRestrictedPeriodMatrix_alpha_zero_right_steady
          (Node := Node) quad lambda i0
  have hleft :
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) left := by
    simpa [left] using
      quadraticRestrictedPeriodMatrix_alpha_zero_left_perron_eigenvector
        (Node := Node) quad lambda i0
  have hnormalized :
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left right = 1 := by
    simp [left, right, quadraticRestrictedAlphaZeroRightVector,
      restrictedStateToCoord, rowDot]
    simpa [rowSum] using quad.perronLeft_sum 0
  have heigen :
      IsRightUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right ∧
      IsLeftUnitEigenvector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) left ∧
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left right = 1 :=
    ⟨hright, hleft, hnormalized⟩
  have halgebraic :
      UnitEigenvalueAlgebraicallySimple
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) right :=
    quadraticRestrictedPeriodMatrix_alpha_zero_unit_algebraicallySimple
      (Node := Node) quad lambda i0 _hquad hstable right left heigen
  obtain ⟨r0, hr0_nonneg, hr0_lt_one, hstable_disk⟩ :=
    quadraticRestrictedPeriodMatrix_alpha_zero_stable_disk
      (Node := Node) quad lambda i0 _hquad hstable right left heigen
  exact ⟨r0, right, left, rfl, rfl, hr0_nonneg, hr0_lt_one, hright, hleft,
    hnormalized, halgebraic, hstable_disk⟩

/-- Source-facing C.1 spectral supplier: instantiate Appendix A Lemma A.1
(`PeriodicSpectralDecomposition`) for the true restricted one-period
homogeneous quadratic propagator. -/
theorem quadraticRestrictedPeriodMatrix_periodic_spectral_splitting
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∃ r0 right left alpha0 theta K gamma P F,
      0 ≤ r0 ∧ alpha0 ≤ 1 ∧
        P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j) ∧
        right =
          quadraticRestrictedAlphaZeroRightVector
            (Node := Node) quad lambda i0 0 ∧
        (∀ i : Node, right (Sum.inl i) = 1) ∧
        (∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i) ∧
        (∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0) ∧
        PeriodicSpectralSplitting
          (Node := Sum Node {i : Node // i ≠ i0})
          (fun alpha : ℝ =>
            quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
          r0 alpha0 theta K right left gamma P F := by
  classical
  have hstableAll :=
    quadratic_restricted_all_lengths_stable_blocks (Node := Node) quad
  obtain ⟨r0, right, left, hright_explicit, hleft_explicit,
      hspectrum⟩ :=
    quadraticRestrictedPeriodMatrix_alpha_zero_spectrum
      (Node := Node) quad lambda i0 hquad hstableAll
  have hanalytic :=
    quadraticRestrictedPeriodMatrix_analytic_near_zero
      (Node := Node) quad lambda i0
  obtain ⟨alpha0, theta, K, gamma, P, F, halpha0_le, hP0, hsplitting⟩ :=
    PeriodicSpectralDecomposition_with_base_projection
      (Node := Sum Node {i : Node // i ≠ i0})
      (fun alpha : ℝ =>
        quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
      1 r0 hanalytic right left hspectrum
  have hright_top :
      ∀ i : Node, right (Sum.inl i) = 1 := by
    intro i
    rw [hright_explicit]
    simp [quadraticRestrictedAlphaZeroRightVector, restrictedStateToCoord]
  have hleft_top :
      ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i := by
    intro i
    simpa [hleft_explicit]
  have hleft_bottom :
      ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0 := by
    intro j
    simpa [hleft_explicit]
  exact ⟨r0, right, left, alpha0, theta, K, gamma, P, F,
    hspectrum.1, halpha0_le, hP0, hright_explicit, hright_top, hleft_top,
    hleft_bottom, hsplitting⟩

/-- The unconstrained infimum of the homogeneous quadratic average objective is
zero.  This is the source `f_* = 0` step used when rewriting the scalar bias
constant in terms of `Delta`. -/
theorem homogeneousQuadratic_objectiveInfimum_eq_zero
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    quad.objectiveInfimum = 0 := by
  have hobjective :=
    homogeneousQuadratic_objective_eq (Node := Node) quad lambda hquad
  unfold objectiveInfimum SOptLib.objectiveInfimumValue
  apply (show IsLeast (quad.objective '' Set.univ) 0 by
    constructor
    · exact ⟨0, Set.mem_univ 0, by rw [hobjective 0]; ring⟩
    · rintro y ⟨x, _hx, rfl⟩
      rw [hobjective x]
      have hlambda_nonneg : 0 ≤ lambda := le_of_lt hquad.1
      nlinarith [mul_nonneg hlambda_nonneg (sq_nonneg x)]).csInf_eq

/-- Source-derived identity for homogeneous quadratic data:
`x_0^2 = 2 Delta / lambda`.  Appendix C.2 uses this to rewrite the
deterministic bias sum in terms of the problem gap. -/
theorem homogeneousQuadratic_x0_sq_eq_twoDelta_div_lambda
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    quad.x0 ^ 2 = 2 * quad.Delta / lambda := by
  have hobjective :=
    homogeneousQuadratic_objective_eq (Node := Node) quad lambda hquad quad.x0
  have hinf :=
    homogeneousQuadratic_objectiveInfimum_eq_zero
      (Node := Node) quad lambda hquad
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hquad.1
  unfold Delta
  rw [hobjective, hinf]
  field_simp [hlambda_ne]
  ring

/-- Algebraic normalization of the Appendix C.2 deterministic bias term.
After the source rewrite `x_0^2 = 2 Delta / lambda`, the bias error is exactly
the leading scale multiplied by the remaining dimensionless geometric quotient
error. -/
theorem quadraticScalarBiasBlockAverage_delta_factor
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (halpha_ne : alpha ≠ 0) {K : ℕ} (hK : 1 ≤ K) :
    let S : ℝ :=
      ∑ r : Fin quad.period,
        quadraticScalarWithinPeriodMultiplier (Node := Node)
          quad lambda alpha r.1 ^ 2
    let Gamma : ℝ :=
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
    let T : ℝ := ((K * quad.period : ℕ) : ℝ)
    quadraticScalarBiasBlockAverage (Node := Node) quad lambda alpha K -
        quad.Delta / (quad.influenceGain * alpha * T) =
      (quad.Delta / (quad.influenceGain * alpha * T)) *
        (2 * lambda * quad.influenceGain * alpha * S *
            ((1 - Gamma ^ (2 * K)) / (1 - Gamma ^ 2)) - 1) := by
  dsimp
  unfold quadraticScalarBiasBlockAverage
  rw [homogeneousQuadratic_x0_sq_eq_twoDelta_div_lambda
    (Node := Node) quad lambda hquad]
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hquad.1
  have hinfluence_ne : quad.influenceGain ≠ 0 :=
    ne_of_gt quad.influenceGain_pos
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hperiod_ne_nat : quad.period ≠ 0 := Nat.ne_of_gt quad.period_pos
  have hKperiod_ne_nat : K * quad.period ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hK_pos) hperiod_ne_nat
  have hKperiod_ne : ((K * quad.period : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hKperiod_ne_nat
  field_simp [hlambda_ne, hinfluence_ne, halpha_ne, hKperiod_ne]
  rw [Nat.cast_mul]
  ring

/-- Appendix C.2 small-stepsize squeeze for the period multiplier:
`1-c₂ alpha <= Gamma(alpha) <= 1-c₁ alpha`, together with positivity of
`1-Gamma(alpha)^2`.  This is the geometric-tail input for the bias and
variance summations. -/
theorem quadraticScalarPeriodMultiplier_smallAlpha_squeeze
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∃ alpha0 c1 c2 : ℝ,
      0 < alpha0 ∧ 0 < c1 ∧ 0 < c2 ∧ c1 ≤ c2 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          1 - c2 * alpha ≤
              quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ∧
            quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ≤ 1 - c1 * alpha ∧
              0 < 1 -
                quadraticScalarPeriodMultiplier (Node := Node)
                  quad lambda alpha ^ 2 := by
  classical
  let a : ℝ := lambda * (quad.period : ℝ) * quad.influenceGain
  have hGammaO :=
    quadraticScalarPeriodMultiplier_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  have hdenCoeff_pos :=
    quadraticScalarPeriodDenominator_linearCoefficient_pos
      (Node := Node) quad lambda hquad
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith [hdenCoeff_pos]
  obtain ⟨C, hC_pos, hCbig⟩ := hGammaO.exists_pos
  have hbound_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha -
            (1 - alpha * a)‖ ≤ C * ‖alpha ^ 2‖ := by
    simpa [a, mul_assoc] using
      (Asymptotics.isBigOWith_iff.mp hCbig)
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually
  let c1 : ℝ := a / 2
  let c2 : ℝ := 3 * a / 2
  let alpha0 : ℝ := min (eps / 2) (min (a / (2 * C)) (1 / c2))
  have hc1_pos : 0 < c1 := by
    dsimp [c1]
    nlinarith
  have hc2_pos : 0 < c2 := by
    dsimp [c2]
    nlinarith
  have hc1_le_c2 : c1 ≤ c2 := by
    dsimp [c1, c2]
    nlinarith
  have ha_div_pos : 0 < a / (2 * C) := by
    positivity
  have hinv_c2_pos : 0 < 1 / c2 := by
    positivity
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (half_pos heps_pos) (lt_min ha_div_pos hinv_c2_pos)
  refine ⟨alpha0, c1, c2, halpha0_pos, hc1_pos, hc2_pos, hc1_le_c2, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_eps_half : alpha ≤ eps / 2 := by
    exact le_trans halpha_le (min_le_left _ _)
  have halpha_lt_eps : alpha < eps := by nlinarith
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_eps
  have hraw_bound := hbound_eps hdist
  have herror_abs :
      |quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha -
          (1 - alpha * a)| ≤ C * alpha ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg alpha)] using hraw_bound
  have halpha_le_a_div : alpha ≤ a / (2 * C) := by
    exact le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hC_alpha_le : C * alpha ≤ a / 2 := by
    calc
      C * alpha ≤ C * (a / (2 * C)) :=
        mul_le_mul_of_nonneg_left halpha_le_a_div (le_of_lt hC_pos)
      _ = a / 2 := by
        field_simp [ne_of_gt hC_pos]
  have hrem_le : C * alpha ^ 2 ≤ (a / 2) * alpha := by
    have hmul :=
      mul_le_mul_of_nonneg_right hC_alpha_le halpha_nonneg
    nlinarith
  have herror_le :
      |quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha -
          (1 - alpha * a)| ≤ (a / 2) * alpha :=
    le_trans herror_abs hrem_le
  have htwo := abs_le.mp herror_le
  have hlower :
      1 - c2 * alpha ≤
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha := by
    dsimp [c2]
    nlinarith [htwo.1]
  have hupper :
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ≤
          1 - c1 * alpha := by
    dsimp [c1]
    nlinarith [htwo.2]
  have halpha_le_inv_c2 : alpha ≤ 1 / c2 := by
    exact le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hc2_alpha_le_one : c2 * alpha ≤ 1 := by
    calc
      c2 * alpha ≤ c2 * (1 / c2) :=
        mul_le_mul_of_nonneg_left halpha_le_inv_c2 (le_of_lt hc2_pos)
      _ = 1 := by
        field_simp [ne_of_gt hc2_pos]
  have hGamma_nonneg :
      0 ≤ quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha := by
    have hnonneg_lower : 0 ≤ 1 - c2 * alpha := by nlinarith
    exact le_trans hnonneg_lower hlower
  have hGamma_lt_one :
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha < 1 := by
    have hc1alpha_pos : 0 < c1 * alpha := mul_pos hc1_pos halpha_pos
    nlinarith
  have hGamma_sq_le :
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 ≤
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha := by
    nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hGamma_lt_one) hGamma_nonneg]
  have hden_pos :
      0 < 1 -
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 := by
    nlinarith
  exact ⟨hlower, hupper, hden_pos⟩

/-- Real exponential domination of a nonnegative contraction power.  This is
the deterministic tail estimate used in Appendix C.2 after squeezing the
period multiplier by `1-c alpha`. -/
theorem real_nonneg_pow_le_exp_neg_mul_of_le_one_sub
    {gamma x : ℝ} (n : ℕ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1 - x) :
    gamma ^ n ≤ Real.exp (-(x * (n : ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hgamma_zero : gamma = 0
  · subst gamma
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp [hnpos.ne']
    exact Real.exp_nonneg _
  have hgamma_pos : 0 < gamma :=
    lt_of_le_of_ne hgamma_nonneg (Ne.symm hgamma_zero)
  have hbase_pos : 0 < 1 - x :=
    lt_of_lt_of_le hgamma_pos hgamma_le
  have hlog_gamma_le_base : Real.log gamma ≤ Real.log (1 - x) :=
    Real.log_le_log hgamma_pos hgamma_le
  have hlog_base_le : Real.log (1 - x) ≤ -x := by
    have h := Real.log_le_sub_one_of_pos hbase_pos
    nlinarith
  have hlog_gamma_le : Real.log gamma ≤ -x :=
    le_trans hlog_gamma_le_base hlog_base_le
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_pow_le : Real.log (gamma ^ n) ≤ -(x * (n : ℝ)) := by
    rw [Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_left hlog_gamma_le hn_nonneg
    nlinarith
  have hpow_pos : 0 < gamma ^ n := pow_pos hgamma_pos n
  have hexp_pos : 0 < Real.exp (-(x * (n : ℝ))) := Real.exp_pos _
  exact (Real.log_le_log_iff hpow_pos hexp_pos).mp
    (by simpa [Real.log_exp] using hlog_pow_le)

/-- Appendix C.2 geometric tail from the small-stepsize squeeze:
`Gamma(alpha)^(2K) <= exp(-c alpha Kp)`, after an internal shrink of the
positive stepsize interval. -/
theorem quadraticScalarPeriodMultiplier_power_tail_le_exp
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∃ alpha0 c : ℝ, 0 < alpha0 ∧ 0 < c ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ K : ℕ,
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^
              (2 * K) ≤
            Real.exp (-(c * alpha * ((K * quad.period : ℕ) : ℝ))) := by
  classical
  obtain ⟨alphaS, c1, c2, halphaS_pos, hc1_pos, hc2_pos, _hc12,
      hsqueeze⟩ :=
    quadraticScalarPeriodMultiplier_smallAlpha_squeeze
      (Node := Node) quad lambda hquad
  let alpha0 : ℝ := min alphaS (1 / (2 * c2))
  let c : ℝ := c1 / (quad.period : ℝ)
  have hperiod_pos : 0 < (quad.period : ℝ) := by
    exact_mod_cast quad.period_pos
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaS_pos (by positivity)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨alpha0, c, halpha0_pos, hc_pos, ?_⟩
  intro alpha halpha_pos halpha_le K
  have halpha_le_s : alpha ≤ alphaS :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_le_small : alpha ≤ 1 / (2 * c2) :=
    le_trans halpha_le (min_le_right _ _)
  have hs := hsqueeze alpha halpha_pos halpha_le_s
  have hGamma_lower := hs.1
  have hGamma_upper := hs.2.1
  have hsmall : c2 * alpha ≤ 1 / 2 := by
    calc
      c2 * alpha ≤ c2 * (1 / (2 * c2)) :=
        mul_le_mul_of_nonneg_left halpha_le_small (le_of_lt hc2_pos)
      _ = 1 / 2 := by
        field_simp [ne_of_gt hc2_pos]
  have hGamma_nonneg :
      0 ≤ quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha := by
    have hnonneg : 0 ≤ 1 - c2 * alpha := by nlinarith
    exact le_trans hnonneg hGamma_lower
  have hpow :=
    real_nonneg_pow_le_exp_neg_mul_of_le_one_sub
      (gamma := quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
      (x := c1 * alpha) (2 * K) hGamma_nonneg hGamma_upper
  have hexponent :
      -(c1 * alpha * ((2 * K : ℕ) : ℝ)) ≤
        -(c * alpha * ((K * quad.period : ℕ) : ℝ)) := by
    have hright :
        c * alpha * ((K * quad.period : ℕ) : ℝ) =
          c1 * alpha * (K : ℝ) := by
      dsimp [c]
      rw [Nat.cast_mul]
      field_simp [ne_of_gt hperiod_pos]
    rw [hright, Nat.cast_mul]
    norm_num
    have hK_nonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    have hK_le_twoK : (K : ℝ) ≤ (2 : ℝ) * (K : ℝ) := by
      nlinarith
    have hcoef_nonneg : 0 ≤ c1 * alpha :=
      mul_nonneg (le_of_lt hc1_pos) (le_of_lt halpha_pos)
    have hmul :
        c1 * alpha * (K : ℝ) ≤ c1 * alpha * ((2 : ℝ) * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left hK_le_twoK hcoef_nonneg
    nlinarith
  exact le_trans hpow (Real.exp_le_exp.mpr hexponent)

/-- Appendix C.2 block innovation variance:
`E|eta_k|^2 = alpha^2 sigma^2 p q + O(alpha^3)`.  The theorem is stated for
each block because the iid exact-variance assumptions make the expansion
uniform in the block index. -/
theorem quadraticScalarBlockInnovationSecondMoment_expansion
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ k : ℕ,
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          quadraticScalarBlockInnovationSecondMoment (Node := Node)
              quad lambda alpha μ oracle k -
            alpha ^ 2 * quad.sigma ^ 2 *
              (quad.period : ℝ) * quad.influenceSecondMoment)
        (fun alpha : ℝ => alpha ^ 3) := by
  intro k
  let coeffSum : ℝ → ℝ := fun alpha =>
    (Finset.range quad.period).sum fun r =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart k) quad.period r ^ 2 *
        rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
        quad.sigma ^ 2
  have hcoeff :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          coeffSum alpha -
            quad.sigma ^ 2 * (quad.period : ℝ) *
              quad.influenceSecondMoment)
        (fun alpha : ℝ => alpha) := by
    simpa [coeffSum] using
      quadraticScalarWindowNoiseCoeffSqVarianceSum_isBigO_linear
        (Node := Node) quad lambda k
  have hsq :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => alpha ^ 2) (fun alpha : ℝ => alpha ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hprod := hsq.mul hcoeff
  refine hprod.congr ?_ ?_
  · intro alpha
    rw [quadraticScalarBlockInnovationSecondMoment_eq_alpha_sq_finset_sum
      (Node := Node) quad lambda alpha μ oracle hnoise k]
    dsimp [coeffSum]
    ring
  · intro alpha
    ring

/-- The block innovation second moment is periodic in the block index.  This
is the typed uniformity bridge needed by the complete-period scalar moment
assembly, whose constant cannot depend on the terminal block count `K`. -/
theorem quadraticScalarBlockInnovationSecondMoment_eq_zeroBlock
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    quadraticScalarBlockInnovationSecondMoment (Node := Node)
        quad lambda alpha μ oracle k =
      quadraticScalarBlockInnovationSecondMoment (Node := Node)
        quad lambda alpha μ oracle 0 := by
  rw [quadraticScalarBlockInnovationSecondMoment_eq_alpha_sq_finset_sum
      (Node := Node) quad lambda alpha μ oracle hnoise k,
    quadraticScalarBlockInnovationSecondMoment_eq_alpha_sq_finset_sum
      (Node := Node) quad lambda alpha μ oracle hnoise 0]
  rw [quadraticScalarWindowNoiseCoeffSqVarianceSum_block_eq_zero
    (Node := Node) quad lambda alpha k]

/-- Uniform version of the Appendix C.2 block innovation expansion.  Unlike
the pointwise `IsBigO` statement, this exposes one small-stepsize radius and
one constant valid for every block index, which is exactly what the
complete-period finite-horizon average needs. -/
theorem quadraticScalarBlockInnovationSecondMoment_expansion_uniform
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, |alpha| < alpha0 →
        ∀ k : ℕ,
          |quadraticScalarBlockInnovationSecondMoment (Node := Node)
              quad lambda alpha μ oracle k -
            alpha ^ 2 * quad.sigma ^ 2 *
              (quad.period : ℝ) * quad.influenceSecondMoment| ≤
          C * |alpha| ^ 3 := by
  classical
  have hpoint :=
    quadraticScalarBlockInnovationSecondMoment_expansion
      (Node := Node) quad lambda μ oracle hnoise 0
  obtain ⟨C, hC_pos, hCbig⟩ := hpoint.exists_pos
  have hevent :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖quadraticScalarBlockInnovationSecondMoment (Node := Node)
              quad lambda alpha μ oracle 0 -
            alpha ^ 2 * quad.sigma ^ 2 *
              (quad.period : ℝ) * quad.influenceSecondMoment‖ ≤
          C * ‖alpha ^ 3‖ := by
    exact Asymptotics.isBigOWith_iff.mp hCbig
  obtain ⟨eps, heps_pos, heps⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨eps, C, heps_pos, hC_pos.le, ?_⟩
  intro alpha halpha k
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq] using halpha
  have hbase := heps hdist
  have hsame :=
    quadraticScalarBlockInnovationSecondMoment_eq_zeroBlock
      (Node := Node) quad lambda alpha μ oracle hnoise k
  simpa [Real.norm_eq_abs, abs_pow, hsame] using hbase

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
