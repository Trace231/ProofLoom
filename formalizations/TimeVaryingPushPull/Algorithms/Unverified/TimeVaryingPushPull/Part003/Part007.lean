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
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.NetworkMatrix
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope
import Algorithms.Unverified.TimeVaryingPushPull.Part002
import Algorithms.Unverified.TimeVaryingPushPull.Part003.Part006

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

/-- Appendix C.3 step 1: testing the near minimizer at the balancing
stepsize gives an eventual `O(T^{-1/2})` upper bound on its value. -/
theorem near_minimizer_value_upper_inv_sqrt_of_scalar_expansion
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hslow : QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle)
    (hscalarExp : QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle)
    (alphaNearOpt : ℕ → ℝ)
    (hnear_value : ∀ T : ℕ, 1 ≤ T →
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤
        sInf { value : ℝ |
          ∃ alpha : ℝ, 0 ≤ alpha ∧
            value =
              quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha } +
        (T : ℝ)⁻¹) :
    ∃ C T0, 0 ≤ C ∧ ∀ T : ℕ, T0 ≤ T →
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤ C * (Real.sqrt (T : ℝ))⁻¹ := by
  classical
  -- Source step: instantiate (8.7) at the balancing test stepsize and then
  -- use the slow-comparison transfer to bound the true quadratic functional.
  rcases hscalarExp with
    ⟨alphaExp, cExp, Cexp, halphaExp_pos, hcExp_pos, hCexp_nonneg,
      hscalar_bound⟩
  rcases
    quadraticLowerBoundStationarityFunctional_le_scalarMoment_add_slowError
      (Node := Node) quad lambda μ oracle hquad hnoise hslow with
    ⟨Cslow, alphaSlow, hCslow_nonneg, halphaSlow_pos, hslow_bound⟩
  let A : ℝ :=
    2 * quad.Delta /
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment)
  let alphaStar : ℕ → ℝ := fun T =>
    Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹
  have hA_pos : 0 < A := by
    have hlambda_pos : 0 < lambda := hquad.1
    have hsigma_pos : 0 < quad.sigma := hnoise.2.1
    have hq_pos : 0 < quad.influenceSecondMoment :=
      quad.influenceSecondMoment_pos
    have hDelta_pos : 0 < quad.Delta := quad.Delta_positive
    dsimp [A]
    positivity
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have halphaStar_pos :
      ∀ᶠ T : ℕ in Filter.atTop, 0 < alphaStar T := by
    have hlarge : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
      Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
    filter_upwards [hlarge] with T hT
    have hT_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    dsimp [alphaStar]
    positivity
  have halphaStar_tendsto :
      Filter.Tendsto alphaStar Filter.atTop (nhds 0) := by
    have hsqrt_atTop :
        Filter.Tendsto (fun T : ℕ => Real.sqrt (T : ℝ))
          Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hinv_sqrt_zero :
        Filter.Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)
          Filter.atTop (nhds 0) :=
      hsqrt_atTop.inv_tendsto_atTop
    simpa [alphaStar] using
      (Filter.Tendsto.const_mul (Real.sqrt A) hinv_sqrt_zero)
  have hprod_tendsto :
      Filter.Tendsto (fun T : ℕ => alphaStar T * (T : ℝ))
        Filter.atTop Filter.atTop := by
    have hsqrt_atTop :
        Filter.Tendsto (fun T : ℕ => Real.sqrt (T : ℝ))
          Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hscaled :
        Filter.Tendsto (fun T : ℕ => Real.sqrt A * Real.sqrt (T : ℝ))
          Filter.atTop Filter.atTop :=
      hsqrt_atTop.const_mul_atTop hsqrtA_pos
    refine hscaled.congr' ?_
    have hlarge : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
      Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
    filter_upwards [hlarge] with T hT
    have hT_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    have hsqrt_ne : Real.sqrt (T : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hT_pos)
    have hsqrt_sq :
        Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
      Real.sq_sqrt (le_of_lt hT_pos)
    dsimp [alphaStar]
    field_simp [hsqrt_ne]
    exact hsqrt_sq
  have hsmall_exp :
      ∀ᶠ T : ℕ in Filter.atTop, alphaStar T ≤ alphaExp := by
    have hdist :
        ∀ᶠ T : ℕ in Filter.atTop, dist (alphaStar T) 0 < alphaExp :=
      (Metric.tendsto_nhds.mp halphaStar_tendsto) alphaExp halphaExp_pos
    filter_upwards [hdist] with T hT
    have habs : |alphaStar T| < alphaExp := by
      simpa [Real.dist_eq] using hT
    exact le_trans (le_abs_self _) (le_of_lt habs)
  have hsmall_slow :
      ∀ᶠ T : ℕ in Filter.atTop, alphaStar T ≤ alphaSlow := by
    have hdist :
        ∀ᶠ T : ℕ in Filter.atTop, dist (alphaStar T) 0 < alphaSlow :=
      (Metric.tendsto_nhds.mp halphaStar_tendsto) alphaSlow halphaSlow_pos
    filter_upwards [hdist] with T hT
    have habs : |alphaStar T| < alphaSlow := by
      simpa [Real.dist_eq] using hT
    exact le_trans (le_abs_self _) (le_of_lt habs)
  have hprod_ge_one :
      ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ alphaStar T * (T : ℝ) :=
    hprod_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  have hT_ge_one : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  let B : ℝ :=
    lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
  let leadingC : ℝ :=
    |quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A)| +
      |B * Real.sqrt A|
  let remFactor : ℝ := 1 + A + (Real.sqrt A)⁻¹
  let C : ℝ := 2 * (leadingC + Cexp * remFactor) + Cslow * A + 1
  have hremFactor_nonneg : 0 ≤ remFactor := by
    dsimp [remFactor]
    positivity
  have hleadingC_nonneg : 0 ≤ leadingC := by
    dsimp [leadingC]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have htail :
      ∀ᶠ T : ℕ in Filter.atTop,
        0 < alphaStar T ∧ alphaStar T ≤ alphaExp ∧
          alphaStar T ≤ alphaSlow ∧
          1 ≤ alphaStar T * (T : ℝ) ∧ 1 ≤ T := by
    filter_upwards [halphaStar_pos, hsmall_exp, hsmall_slow,
      hprod_ge_one, hT_ge_one] with T hpos hExp hSlow hprod hT
    exact ⟨hpos, hExp, hSlow, hprod, hT⟩
  rcases Filter.eventually_atTop.1 htail with ⟨T0, hT0⟩
  refine ⟨C, T0, hC_nonneg, ?_⟩
  intro T hT_ge
  rcases hT0 T hT_ge with
    ⟨halpha_pos, halpha_le_exp, halpha_le_slow, hprod_ge, hT_one⟩
  let s : ℝ := Real.sqrt (T : ℝ)
  let invs : ℝ := (Real.sqrt (T : ℝ))⁻¹
  have hTreal_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT_one)
  have hs_pos : 0 < Real.sqrt (T : ℝ) :=
    Real.sqrt_pos.2 hTreal_pos
  have hs_ne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hs_pos
  have hinvs_nonneg : 0 ≤ invs := by
    dsimp [invs]
    positivity
  have hnear_test :=
    quadraticLowerBound_near_value_le_test_value_add_inv
      (Node := Node) quad μ oracle alphaNearOpt hnear_value T hT_one
      (alphaStar T) halpha_pos.le
  have hslowT :=
    hslow_bound (alphaStar T) halpha_pos halpha_le_slow T hprod_ge
  have hscalar_abs :=
    hscalar_bound (alphaStar T) halpha_pos halpha_le_exp T hT_one
  have hscalar_upper :
      quad.quadraticScalarMomentFunctional lambda (alphaStar T) μ oracle T ≤
        (quad.Delta /
            ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
          B * alphaStar T) +
        Cexp * ((T : ℝ)⁻¹ + (alphaStar T) ^ 2 +
          Real.exp (-(cExp * alphaStar T * (T : ℝ))) /
            (alphaStar T * (T : ℝ))) := by
    have hright := (abs_sub_le_iff.mp hscalar_abs).1
    dsimp [B]
    linarith
  have halphaT_eq :
      alphaStar T * (T : ℝ) = Real.sqrt A * Real.sqrt (T : ℝ) := by
    have hs_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
      Real.sq_sqrt hTreal_pos.le
    dsimp [alphaStar]
    field_simp [hs_ne]
    exact hs_sq.symm
  have hlead1_eq :
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) =
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A)) * invs := by
    have hgain_ne : (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) ≠ 0 :=
      ne_of_gt quad.influenceGain_pos
    have hsqrtA_ne : Real.sqrt A ≠ 0 := ne_of_gt hsqrtA_pos
    calc
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) =
          quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * (alphaStar T * (T : ℝ))) := by
        ring_nf
      _ = quad.Delta /
          ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * (Real.sqrt A * Real.sqrt (T : ℝ))) := by
        rw [halphaT_eq]
      _ = (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A)) * invs := by
        dsimp [invs]
        field_simp [hgain_ne, hsqrtA_ne, hs_ne]
  have hlead2_eq :
      B * alphaStar T = (B * Real.sqrt A) * invs := by
    dsimp [alphaStar, invs]
    ring
  have hcenter_bound :
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
          B * alphaStar T ≤
        leadingC * invs := by
    have h1 :
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A)) * invs ≤
          |quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A)| * invs :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hinvs_nonneg
    have h2 : (B * Real.sqrt A) * invs ≤
          |B * Real.sqrt A| * invs :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hinvs_nonneg
    rw [hlead1_eq, hlead2_eq]
    dsimp [leadingC]
    linarith
  have hTinv_bound :
      (T : ℝ)⁻¹ ≤ invs := by
    dsimp [invs]
    exact real_nat_inv_le_inv_sqrt_of_one_le hT_one
  have halpha_sq_bound :
      (alphaStar T) ^ 2 ≤ A * invs := by
    dsimp [alphaStar, invs]
    exact real_balancing_alpha_sq_le_inv_sqrt hA_pos hT_one
  have hrest_bound :
      (T : ℝ)⁻¹ + (alphaStar T) ^ 2 +
          Real.exp (-(cExp * alphaStar T * (T : ℝ))) /
            (alphaStar T * (T : ℝ)) ≤
        remFactor * invs := by
    dsimp [alphaStar, remFactor, invs]
    exact real_balancing_remainder_le_inv_sqrt hA_pos hcExp_pos.le hT_one
  have hrem_bound :
      Cexp * ((T : ℝ)⁻¹ + (alphaStar T) ^ 2 +
          Real.exp (-(cExp * alphaStar T * (T : ℝ))) /
            (alphaStar T * (T : ℝ))) ≤
        (Cexp * remFactor) * invs := by
    have hmul :=
      mul_le_mul_of_nonneg_left hrest_bound hCexp_nonneg
    calc
      Cexp * ((T : ℝ)⁻¹ + (alphaStar T) ^ 2 +
          Real.exp (-(cExp * alphaStar T * (T : ℝ))) /
            (alphaStar T * (T : ℝ))) ≤
          Cexp * (remFactor * invs) := hmul
      _ = (Cexp * remFactor) * invs := by ring
  have hscalar_rate :
      quad.quadraticScalarMomentFunctional lambda (alphaStar T) μ oracle T ≤
        (leadingC + Cexp * remFactor) * invs := by
    calc
      quad.quadraticScalarMomentFunctional lambda (alphaStar T) μ oracle T ≤
          (quad.Delta /
              ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
            B * alphaStar T) +
          Cexp * ((T : ℝ)⁻¹ + (alphaStar T) ^ 2 +
            Real.exp (-(cExp * alphaStar T * (T : ℝ))) /
              (alphaStar T * (T : ℝ))) := hscalar_upper
      _ ≤ leadingC * invs + (Cexp * remFactor) * invs :=
        add_le_add hcenter_bound hrem_bound
      _ = (leadingC + Cexp * remFactor) * invs := by ring
  have hslow_rate :
      Cslow * (alphaStar T) ^ 2 ≤ (Cslow * A) * invs := by
    have hmul :=
      mul_le_mul_of_nonneg_left halpha_sq_bound hCslow_nonneg
    calc
      Cslow * (alphaStar T) ^ 2 ≤ Cslow * (A * invs) := hmul
      _ = (Cslow * A) * invs := by ring
  have hnear_rate :
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤
        (2 * (leadingC + Cexp * remFactor) + Cslow * A + 1) * invs := by
    calc
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
            (alphaStar T) + (T : ℝ)⁻¹ := hnear_test
      _ ≤ (2 * quad.quadraticScalarMomentFunctional lambda
            (alphaStar T) μ oracle T + Cslow * (alphaStar T) ^ 2) +
            (T : ℝ)⁻¹ := by
        exact add_le_add hslowT le_rfl
      _ ≤ (2 * ((leadingC + Cexp * remFactor) * invs) +
            (Cslow * A) * invs) + invs := by
        have hscalar2 :=
          mul_le_mul_of_nonneg_left hscalar_rate (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add (add_le_add hscalar2 hslow_rate) hTinv_bound
      _ = (2 * (leadingC + Cexp * remFactor) + Cslow * A + 1) * invs := by
        ring
  simpa [C, invs] using hnear_rate

/-- Route-local copy of deterministic left-multiplication measurability, placed
before the fresh-noise floor so the current frontier can build adapted past
scalars without depending on later public infrastructure. -/
theorem leftMul_comp_measurable_before_fresh_floor
    (setup : Setup Node E)
    {Omega : Type*} {m : MeasurableSpace Omega} [MeasurableSpace E] [BorelSpace E]
    (A : NodeMatrix Node) {X : Omega → State Node E}
    (hX : Measurable[m] X) :
    Measurable[m] (fun omega => leftMul (Node := Node) (E := E) A (X omega)) := by
  classical
  refine measurable_pi_lambda _ ?_
  intro i
  unfold leftMul
  apply Finset.measurable_sum Finset.univ
  intro j _hj
  exact ((measurable_pi_apply j).comp hX).const_smul (A i j)

/-- Route-local copy of deterministic component-gradient-table measurability,
placed before the fresh-noise floor. -/
theorem gradientTable_comp_measurable_before_fresh_floor
    (setup : Setup Node E)
    {Omega : Type*} {m : MeasurableSpace Omega} [MeasurableSpace E]
    [BorelSpace E] {X : Omega → State Node E}
    (hX : Measurable[m] X) :
    Measurable[m] (fun omega => setup.gradientTable (X omega)) := by
  let KL : NNReal := ⟨setup.L, setup.L_pos.le⟩
  refine measurable_pi_lambda _ ?_
  intro i
  have hlip : LipschitzWith KL (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  exact hlip.continuous.measurable.comp ((measurable_pi_apply i).comp hX)

/-- Route-local strict-past adaptedness for the generated push-pull states.
The primal state at time `t` depends only on noises before `t`; the tracker
state at time `t` is visible one step later because it contains the time-`t`
oracle table. -/
theorem generated_primal_tracker_strictPastMeasurable_before_fresh_floor
    (setup : Setup Node E)
    {Omega : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [BorelSpace E]
    (oracle : OracleNoiseProcess Omega Node E) :
    ∀ t : ℕ,
      Measurable[oracle.strictPastMeasurableSpace t]
          (fun omega => setup.primalState (oracle.noise omega) t) ∧
        Measurable[oracle.strictPastMeasurableSpace (t + 1)]
          (fun omega => setup.trackerState (oracle.noise omega) t) := by
  classical
  intro t
  induction t with
  | zero =>
      constructor
      · simpa only [setup.primalState_zero] using
          (measurable_const : Measurable[oracle.strictPastMeasurableSpace 0]
            (fun _ : Omega => setup.initialPrimal))
      · have hnoise : Measurable[oracle.strictPastMeasurableSpace 1]
            (oracle.noiseStream 0) := by
          exact SOptLib.measurable_sample_of_lt_prefixFiltration
            oracle.noiseStream oracle.noiseStream_measurable (by omega)
        have hgrad : Measurable[oracle.strictPastMeasurableSpace 1]
            (fun _ : Omega => setup.gradientTable setup.initialPrimal) :=
          measurable_const
        have hsum := hgrad.add hnoise
        simpa only [setup.trackerState_zero, oracleTable, sampledGradient,
          setup.primalState_zero, OracleNoiseProcess.noiseStream_apply] using hsum
  | succ t ih =>
      have hFt_Fsucc : oracle.strictPastMeasurableSpace t ≤
          oracle.strictPastMeasurableSpace (t + 1) :=
        (oracle.naturalFiltration).mono (Nat.le_succ t)
      have hFsucc_Fsuccsucc : oracle.strictPastMeasurableSpace (t + 1) ≤
          oracle.strictPastMeasurableSpace (t + 1 + 1) :=
        (oracle.naturalFiltration).mono (Nat.le_succ (t + 1))
      have hXcur_succ : Measurable[oracle.strictPastMeasurableSpace (t + 1)]
          (fun omega => setup.primalState (oracle.noise omega) t) :=
        ih.1.mono hFt_Fsucc le_rfl
      have hXnext : Measurable[oracle.strictPastMeasurableSpace (t + 1)]
          (fun omega => setup.primalState (oracle.noise omega) (t + 1)) := by
        have hraw :=
          (leftMul_comp_measurable_before_fresh_floor (Node := Node) (E := E)
            setup (setup.R t) hXcur_succ).sub
            (ih.2.const_smul setup.alpha)
        simpa only [setup.primalState_succ] using hraw
      refine ⟨hXnext, ?_⟩
      have hYcur : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (fun omega => setup.trackerState (oracle.noise omega) t) :=
        ih.2.mono hFsucc_Fsuccsucc le_rfl
      have hXnext' : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (fun omega => setup.primalState (oracle.noise omega) (t + 1)) :=
        hXnext.mono hFsucc_Fsuccsucc le_rfl
      have hXcur' : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (fun omega => setup.primalState (oracle.noise omega) t) :=
        hXcur_succ.mono hFsucc_Fsuccsucc le_rfl
      have hnoise_next : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (oracle.noiseStream (t + 1)) := by
        exact SOptLib.measurable_sample_of_lt_prefixFiltration
          oracle.noiseStream oracle.noiseStream_measurable (by omega)
      have hnoise_cur : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (oracle.noiseStream t) := by
        exact SOptLib.measurable_sample_of_lt_prefixFiltration
          oracle.noiseStream oracle.noiseStream_measurable (by omega)
      have hGnext :=
        (gradientTable_comp_measurable_before_fresh_floor
          (Node := Node) (E := E) setup hXnext').add hnoise_next
      have hGcur :=
        (gradientTable_comp_measurable_before_fresh_floor
          (Node := Node) (E := E) setup hXcur').add hnoise_cur
      have hraw :=
        ((leftMul_comp_measurable_before_fresh_floor (Node := Node) (E := E)
          setup (setup.C t) hYcur).add hGnext).sub hGcur
      simpa only [setup.trackerState_succ, oracleTable, sampledGradient,
        OracleNoiseProcess.noiseStream_apply] using hraw

/-- Real `L²` algebra for the fresh-noise split: after the cross term
vanishes, the scaled fresh component gives a lower bound and the past-square
term is nonnegative. -/
theorem real_integral_sq_sub_scaled_lower_of_cross_zero
    {Omega : Type} [MeasurableSpace Omega] (μ : Measure Omega)
    (lambda alpha : ℝ) {P N : Omega → ℝ}
    (hP : MemLp P 2 μ) (hN : MemLp N 2 μ)
    (hcross : (∫ omega, P omega * N omega ∂μ) = 0) :
    lambda ^ 2 * alpha ^ 2 * (∫ omega, |N omega| ^ 2 ∂μ) ≤
      ∫ omega, ‖lambda * (P omega - alpha * N omega)‖ ^ 2 ∂μ := by
  simpa [smul_eq_mul, Real.norm_eq_abs, mul_pow, sq_abs, mul_sub, mul_assoc] using
    (integral_sq_smul_sub_ge_of_cross_integral_eq_zero
      μ lambda (lambda * alpha) hP hN
        (by change (∫ omega, N omega * P omega ∂μ) = 0; simpa [mul_comm] using hcross))

/-- The arithmetic average of a same-time fresh noise vector has exact
variance `sigma^2 / n`.  This is the stochastic diagonal input used in
Appendix C.3 equation (8.9). -/
theorem arithmeticAverage_freshNoise_secondMoment_eq_exact
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (t : ℕ) :
    (∫ ω,
        |((nodeCount (Node := Node) : ℝ)⁻¹) *
          weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
            (oracle.noise ω t)| ^ 2 ∂μ) =
      quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ) := by
  classical
  let n : ℝ := nodeCount (Node := Node)
  have hn_ne : n ≠ 0 := by
    dsimp [n]
    exact ne_of_gt (by exact_mod_cast (nodeCount_pos (Node := Node)) : 0 < (nodeCount (Node := Node) : ℝ))
  have hrow :
      rowNormSq (Node := Node) (fun _ : Node => (1 : ℝ)) =
        nodeCount (Node := Node) := by
    simp [rowNormSq, nodeCount]
  have hbase :=
    sameTime_weightedNoise_secondMoment_eq_exact
      (Node := Node) quad μ oracle hnoise t (fun _ : Node => (1 : ℝ))
  calc
    (∫ ω,
        |((nodeCount (Node := Node) : ℝ)⁻¹) *
          weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
            (oracle.noise ω t)| ^ 2 ∂μ) =
        ((nodeCount (Node := Node) : ℝ)⁻¹) ^ 2 *
          (∫ ω,
            |weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
              (oracle.noise ω t)| ^ 2 ∂μ) := by
      have hfun :
          (fun ω : Ω =>
            |((nodeCount (Node := Node) : ℝ)⁻¹) *
              weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
                (oracle.noise ω t)| ^ 2) =
          (fun ω : Ω =>
            ((nodeCount (Node := Node) : ℝ)⁻¹) ^ 2 *
              |weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
                (oracle.noise ω t)| ^ 2) := by
        funext ω
        simp [abs_mul, mul_pow, sq_abs, mul_assoc]
      rw [hfun, MeasureTheory.integral_const_mul]
    _ = ((nodeCount (Node := Node) : ℝ)⁻¹) ^ 2 *
          (rowNormSq (Node := Node) (fun _ : Node => (1 : ℝ)) *
            quad.sigma ^ 2) := by
      rw [hbase]
    _ = quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ) := by
      rw [hrow]
      dsimp [n] at hn_ne
      field_simp [hn_ne]

/-- A strict-past scalar multiplier is orthogonal to any same-time weighted
fresh noise.  This is the martingale cancellation behind Appendix C.3 (8.9). -/
theorem strictPast_scalar_weightedNoise_integral_eq_zero
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (horacle : quad.StochasticOracleAssumptions μ oracle)
    (t : ℕ) (w : RowVector Node) (A : Ω → ℝ)
    (hA_meas : Measurable[oracle.strictPastMeasurableSpace t] A)
    (hA_mem : MemLp A 2 μ) :
    (∫ ω, A ω *
      weightedState (Node := Node) (E := ℝ) w (oracle.noise ω t) ∂μ) = 0 := by
  classical
  let hm := strictPastMeasurableSpace_le (Node := Node) (E := ℝ) oracle t
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace t) (μ.trim hm) :=
    strictPastMeasurableSpace_trim_sigmaFinite (Node := Node) (E := ℝ) μ oracle t
  simpa [weightedState, smul_eq_mul] using
    (integral_scalar_mul_finset_weighted_sum_eq_zero_of_condExp_eq_zero
      (mu := μ) hm Finset.univ w A (fun i ω => oracle.noise ω t i)
      hA_meas hA_mem
      (fun i _hi => quad.conditionalMeanZero_condExp μ oracle horacle t i)
      (fun i _hi => quad.conditionalMeanZero_integrable μ oracle horacle t i)
      (fun i _hi => quad.nodeNoise_memLp_two μ oracle horacle t i))

/-- Pathwise successor split for Appendix C.3: the average iterate at `t+1`
is a strict-past part plus the arithmetic average of the current fresh noise. -/
theorem homogeneous_averageIterate_succ_fresh_noise_split
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    let stepped := quad.withStepsize alpha
    stepped.averageIterate noise (t + 1) =
      (((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ i : Node,
            leftMul (Node := Node) (E := ℝ) (stepped.R t)
              (stepped.primalState noise t) i) -
        alpha * (((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ i : Node, lambda * stepped.primalState noise t i) -
        alpha * (((nodeCount (Node := Node) : ℝ)⁻¹) *
          weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
            (noise t)) := by
  classical
  let stepped := quad.withStepsize alpha
  have horacle :
      stepped.oracleTable noise t =
        (fun i : Node => lambda * stepped.primalState noise t i) + noise t := by
    simpa [stepped] using
      homogeneousQuadratic_oracleTable_eq_linear_add_noise
        (Node := Node) quad lambda alpha hquad noise t
  have htracker_sum :
      ∑ i : Node, stepped.trackerState noise t i =
        (∑ i : Node, lambda * stepped.primalState noise t i) +
          ∑ i : Node, noise t i := by
    calc
      ∑ i : Node, stepped.trackerState noise t i =
          ∑ i : Node, stepped.oracleTable noise t i := by
        exact stepped.trackerState_sum_eq_oracleTable_sum noise t
      _ =
          ∑ i : Node,
            ((fun j : Node => lambda * stepped.primalState noise t j) +
              noise t) i := by
        rw [horacle]
      _ =
          (∑ i : Node, lambda * stepped.primalState noise t i) +
            ∑ i : Node, noise t i := by
        simp [Finset.sum_add_distrib]
  calc
    stepped.averageIterate noise (t + 1) =
        ((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ i : Node, stepped.primalState noise (t + 1) i := by
      rw [stepped.averageIterate_eq_arithmeticAverage noise (t + 1)]
      simp [smul_eq_mul]
    _ =
        ((nodeCount (Node := Node) : ℝ)⁻¹) *
          (∑ i : Node,
            leftMul (Node := Node) (E := ℝ) (stepped.R t)
              (stepped.primalState noise t) i -
            alpha * ∑ i : Node, stepped.trackerState noise t i) := by
      rw [stepped.primalState_succ noise t]
      congr 1
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib]
      congr 1
      calc
        ∑ i : Node, (stepped.alpha : ℝ) • stepped.trackerState noise t i =
            ∑ i : Node, alpha * stepped.trackerState noise t i := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp [stepped, withStepsize, smul_eq_mul]
        _ = alpha * ∑ i : Node, stepped.trackerState noise t i := by
          rw [Finset.mul_sum]
    _ =
      (((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ i : Node,
            leftMul (Node := Node) (E := ℝ) (stepped.R t)
              (stepped.primalState noise t) i) -
        alpha * (((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ i : Node, lambda * stepped.primalState noise t i) -
        alpha * (((nodeCount (Node := Node) : ℝ)⁻¹) *
          weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
            (noise t)) := by
      rw [htracker_sum]
      simp only [weightedState, one_smul]
      ring

/-- One-step form of Appendix C.3 equation (8.9): at every successor time,
the current fresh arithmetic-average noise contributes the exact variance
floor to the expected squared stationarity measure. -/
theorem homogeneous_averageIterate_succ_fresh_noise_secondMoment_floor
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ)
    (havg_linear : ∀ x : ℝ, quad.averageGradient x = lambda * x)
    (hfresh_average :
      ∀ t : ℕ,
        (∫ ω,
            |((nodeCount (Node := Node) : ℝ)⁻¹) *
              weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
                (oracle.noise ω t)| ^ 2 ∂μ) =
          quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ))
    (t : ℕ) :
    (∫ ω,
      ‖quad.averageGradient
        ((quad.withStepsize alpha).averageIterate (oracle.noise ω) (t + 1))‖ ^ 2 ∂μ) ≥
      lambda ^ 2 * alpha ^ 2 * quad.sigma ^ 2 /
        (nodeCount (Node := Node) : ℝ) := by
  classical
  let stepped := quad.withStepsize alpha
  let n : ℝ := nodeCount (Node := Node)
  let P : Ω → ℝ := fun ω =>
    (n⁻¹) *
        ∑ i : Node,
          leftMul (Node := Node) (E := ℝ) (stepped.R t)
            (stepped.primalState (oracle.noise ω) t) i -
      alpha * ((n⁻¹) *
        ∑ i : Node, lambda * stepped.primalState (oracle.noise ω) t i)
  let N : Ω → ℝ := fun ω =>
    n⁻¹ * weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
      (oracle.noise ω t)
  have hsplit : ∀ ω : Ω,
      stepped.averageIterate (oracle.noise ω) (t + 1) =
        P ω - alpha * N ω := by
    intro ω
    have hraw :=
      homogeneous_averageIterate_succ_fresh_noise_split
        (Node := Node) quad lambda alpha hquad (oracle.noise ω) t
    dsimp [P, N, n, stepped]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_comm, mul_left_comm] using hraw
  have hstepped_oracle :
      stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, StochasticOracleAssumptions, withStepsize]
      using hnoise.1
  have hgenerated :=
    stepped.generated_pushpull_coordinate_memLp μ oracle hstepped_oracle t
  have hX_meas : Measurable[oracle.strictPastMeasurableSpace t]
      (fun ω : Ω => stepped.primalState (oracle.noise ω) t) :=
    (generated_primal_tracker_strictPastMeasurable_before_fresh_floor
      (Node := Node) (E := ℝ) stepped oracle t).1
  have hleft_meas : Measurable[oracle.strictPastMeasurableSpace t]
      (fun ω : Ω =>
        leftMul (Node := Node) (E := ℝ) (stepped.R t)
          (stepped.primalState (oracle.noise ω) t)) :=
    leftMul_comp_measurable_before_fresh_floor
      (Node := Node) (E := ℝ) stepped (stepped.R t) hX_meas
  have hleft_sum_meas : Measurable[oracle.strictPastMeasurableSpace t]
      (fun ω : Ω =>
        ∑ i : Node,
          leftMul (Node := Node) (E := ℝ) (stepped.R t)
            (stepped.primalState (oracle.noise ω) t) i) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    exact (measurable_pi_apply i).comp hleft_meas
  have hgrad_sum_meas : Measurable[oracle.strictPastMeasurableSpace t]
      (fun ω : Ω =>
        ∑ i : Node, lambda * stepped.primalState (oracle.noise ω) t i) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    exact ((measurable_pi_apply i).comp hX_meas).const_mul lambda
  have hP_meas : Measurable[oracle.strictPastMeasurableSpace t] P := by
    have hraw :=
      (hleft_sum_meas.const_mul n⁻¹).sub
        ((hgrad_sum_meas.const_mul n⁻¹).const_mul alpha)
    simpa [P, smul_eq_mul, mul_assoc] using hraw
  have hleft_sum_mem : MemLp
      (fun ω : Ω =>
        ∑ i : Node,
          leftMul (Node := Node) (E := ℝ) (stepped.R t)
            (stepped.primalState (oracle.noise ω) t) i) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i _hi
    unfold leftMul
    apply memLp_finset_sum Finset.univ
    intro j _hj
    exact (hgenerated.1 j).const_smul (stepped.R t i j)
  have hgrad_sum_mem : MemLp
      (fun ω : Ω =>
        ∑ i : Node, lambda * stepped.primalState (oracle.noise ω) t i) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact (hgenerated.1 i).const_smul lambda
  have hP_mem : MemLp P 2 μ := by
    have hraw :=
      (hleft_sum_mem.const_smul n⁻¹).sub
        ((hgrad_sum_mem.const_smul n⁻¹).const_smul alpha)
    simpa [P, smul_eq_mul, mul_assoc] using hraw
  have hN_mem : MemLp N 2 μ := by
    have hweighted :
        MemLp
          (fun ω : Ω =>
            weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
              (oracle.noise ω t)) 2 μ :=
      quad.weightedNoise_memLp_two μ oracle hnoise.1 t (fun _ : Node => 1)
    simpa [N, n, smul_eq_mul] using hweighted.const_smul n⁻¹
  have hcross : (∫ ω, P ω * N ω ∂μ) = 0 := by
    have hzero :=
      strictPast_scalar_weightedNoise_integral_eq_zero
        (Node := Node) quad μ oracle hnoise.1 t (fun _ : Node => 1)
        P hP_meas hP_mem
    have hfun :
        (fun ω : Ω => P ω * N ω) =
          fun ω : Ω =>
            n⁻¹ *
              (P ω *
                weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
                  (oracle.noise ω t)) := by
      funext ω
      dsimp [N, n]
      ring
    rw [hfun, integral_const_mul, hzero, mul_zero]
  have hN_second :
      (∫ ω, |N ω| ^ 2 ∂μ) =
        quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ) := by
    simpa [N, n] using hfresh_average t
  simpa [havg_linear, smul_eq_mul, Real.norm_eq_abs, div_eq_mul_inv,
    mul_assoc] using
    (integral_sq_next_ge_scaled_innovation_of_predictable_split
      μ (fun ω => stepped.averageIterate (oracle.noise ω) (t + 1)) P N
      lambda alpha (quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ))
      (Filter.Eventually.of_forall fun ω => by
        simpa [smul_eq_mul] using hsplit ω) hP_mem hN_mem
      (by simpa [mul_comm] using hcross)
      (by simpa [Real.norm_eq_abs] using hN_second))

/-- Finite-horizon algebra for the fresh-noise floor: a nonnegative first
term and a uniform lower bound on all successor terms give the normalized
`(T-1)/T` lower bound. -/
theorem stationarityAverage_tail_floor_of_succ_floor
    (T : ℕ) (hT : 2 ≤ T) (term : ℕ → ℝ) (c : ℝ)
    (hterm_nonneg : ∀ u : ℕ, 0 ≤ term u)
    (hsucc : ∀ t : ℕ, c ≤ term (t + 1)) :
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) term ≥
      (((T : ℝ) - 1) / (T : ℝ)) * c := by
  classical
  have hT_pos_nat : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hT_ne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hT_pos_nat)
  have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  have hsum_tail :
      ((T - 1 : ℕ) : ℝ) * c ≤
        Finset.sum (Finset.range (T - 1)) (fun t => term (t + 1)) := by
    calc
      ((T - 1 : ℕ) : ℝ) * c =
          Finset.sum (Finset.range (T - 1)) (fun _ : ℕ => c) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Finset.sum (Finset.range (T - 1)) (fun t => term (t + 1)) := by
            exact Finset.sum_le_sum fun t _ht => hsucc t
  have hsum_split :
      Finset.sum (Finset.range T) term =
        term 0 + Finset.sum (Finset.range (T - 1)) (fun t => term (t + 1)) := by
    have hsucc_eq : (T - 1) + 1 = T := Nat.sub_add_cancel (le_trans (by norm_num) hT)
    calc
      Finset.sum (Finset.range T) term =
          Finset.sum (Finset.range ((T - 1) + 1)) term := by rw [hsucc_eq]
      _ = Finset.sum (Finset.range (T - 1)) (fun t => term (t + 1)) + term 0 := by
          rw [Finset.sum_range_succ']
      _ = term 0 + Finset.sum (Finset.range (T - 1)) (fun t => term (t + 1)) := by
          ring
  have hsum_lower :
      ((T - 1 : ℕ) : ℝ) * c ≤ Finset.sum (Finset.range T) term := by
    rw [hsum_split]
    linarith [hterm_nonneg 0, hsum_tail]
  have hmul :
      (T : ℝ)⁻¹ * (((T - 1 : ℕ) : ℝ) * c) ≤
        (T : ℝ)⁻¹ * Finset.sum (Finset.range T) term :=
    mul_le_mul_of_nonneg_left hsum_lower hTinv_nonneg
  have hcast_pred : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    have h1 : 1 ≤ T := le_trans (by norm_num) hT
    have hsucc : T - 1 + 1 = T := Nat.sub_add_cancel h1
    have hsucc_real : ((T - 1 : ℕ) : ℝ) + 1 = (T : ℝ) := by
      exact_mod_cast hsucc
    linarith
  calc
    (((T : ℝ) - 1) / (T : ℝ)) * c =
        (T : ℝ)⁻¹ * (((T - 1 : ℕ) : ℝ) * c) := by
          rw [hcast_pred]
          field_simp [hT_ne]
    _ ≤ (T : ℝ)⁻¹ * Finset.sum (Finset.range T) term := hmul

/-- Appendix C.3 equation (8.9): every nonnegative stepsize has a fresh-noise
quadratic floor in the true stationarity functional. -/
theorem quadraticLowerBoundStationarityFunctional_fresh_noise_floor
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ T : ℕ, ∀ alpha : ℝ, 2 ≤ T → 0 ≤ alpha →
      quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha ≥
        (((T : ℝ) - 1) / (T : ℝ)) *
          (lambda ^ 2 * quad.sigma ^ 2 /
            (nodeCount (Node := Node) : ℝ)) * alpha ^ 2 := by
  classical
  -- Source step: expose the one-step recursion, condition before the current
  -- noise draw, and use exact iid variance for the arithmetic-average noise.
  intro T alpha hT hAlpha
  have havg_linear :
      ∀ x : ℝ, quad.averageGradient x = lambda * x :=
    homogeneousQuadratic_averageGradient_eq_linear
      (Node := Node) quad lambda hquad
  have hfresh_average :
      ∀ t : ℕ,
        (∫ ω,
            |((nodeCount (Node := Node) : ℝ)⁻¹) *
              weightedState (Node := Node) (E := ℝ) (fun _ : Node => 1)
                (oracle.noise ω t)| ^ 2 ∂μ) =
          quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ) := by
    intro t
    exact arithmeticAverage_freshNoise_secondMoment_eq_exact
      (Node := Node) quad μ oracle hnoise t
  let stepped := quad.withStepsize alpha
  let term : ℕ → ℝ := fun u =>
    ∫ ω,
      ‖quad.averageGradient
        (stepped.averageIterate (oracle.noise ω) u)‖ ^ 2 ∂μ
  let c : ℝ :=
    lambda ^ 2 * alpha ^ 2 * quad.sigma ^ 2 /
      (nodeCount (Node := Node) : ℝ)
  have hterm_nonneg : ∀ u : ℕ, 0 ≤ term u := by
    intro u
    dsimp [term]
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hsucc : ∀ t : ℕ, c ≤ term (t + 1) := by
    intro t
    have hstep :=
      homogeneous_averageIterate_succ_fresh_noise_secondMoment_floor
        (Node := Node) quad lambda μ oracle hquad hnoise alpha
        havg_linear hfresh_average t
    simpa [term, c, stepped] using hstep
  have htail :=
    stationarityAverage_tail_floor_of_succ_floor
      T hT term c hterm_nonneg hsucc
  calc
    quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) term := by
          unfold quadraticLowerBoundStationarityFunctional stationarityAverage
            expectedGradientNormSq randomAverageIterate
          congr 1
    _ ≥ (((T : ℝ) - 1) / (T : ℝ)) * c := htail
    _ =
        (((T : ℝ) - 1) / (T : ℝ)) *
          (lambda ^ 2 * quad.sigma ^ 2 /
            (nodeCount (Node := Node) : ℝ)) * alpha ^ 2 := by
          dsimp [c]
          ring

/-- Source-neutral Jensen endpoint for Appendix C.3 step 3.

If the squared mean of the arithmetic average has a finite-horizon lower
floor, then the true quadratic stationarity functional has the same floor.
The proof uses the homogeneous identity `∇f(\bar x)=lambda*\bar x` and the
probability-space inequality `(E Z)^2 <= E Z^2` at each time. -/
theorem stationarity_functional_floor_of_average_iterate_mean_square
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (T : ℕ) (alpha c : ℝ)
    (hmean_floor :
      c ≤ ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          lambda ^ 2 *
            |∫ ω,
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t ∂μ| ^ 2)) :
    c ≤ quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
  classical
  let stepped := quad.withStepsize alpha
  have havg_linear :
      ∀ x : ℝ, quad.averageGradient x = lambda * x :=
    homogeneousQuadratic_averageGradient_eq_linear
      (Node := Node) quad lambda hquad
  have hstepped_oracle :
      stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, StochasticOracleAssumptions, withStepsize]
      using hnoise.1
  have hpoint :
      ∀ t : ℕ,
        lambda ^ 2 *
            |∫ ω,
              stepped.averageIterate (oracle.noise ω) t ∂μ| ^ 2 ≤
          ∫ ω,
            ‖quad.averageGradient
              (stepped.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ := by
    intro t
    let actual : Ω → ℝ := fun ω =>
      stepped.averageIterate (oracle.noise ω) t
    have hgenerated :=
      stepped.generated_pushpull_coordinate_memLp μ oracle
        hstepped_oracle t
    have hactual_mem : MemLp actual 2 μ := by
      have hsum :
          MemLp
            (fun ω : Ω =>
              ∑ i : Node,
                stepped.primalState (oracle.noise ω) t i) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro i _hi
        exact hgenerated.1 i
      simpa [actual, stepped, averageIterate, arithmeticAverage] using
        hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
    have hactual_sq_int : Integrable (fun ω : Ω => actual ω ^ 2) μ := by
      simpa [sq_abs] using real_abs_sq_integrable_of_memLp_two hactual_mem
    have hactual_meas : AEStronglyMeasurable actual μ :=
      hactual_mem.aestronglyMeasurable
    have hjensen :
        (∫ ω, actual ω ∂μ) ^ 2 ≤
          ∫ ω, actual ω ^ 2 ∂μ :=
      sq_integral_le_integral_sq hactual_meas hactual_sq_int
    have hscaled :
        lambda ^ 2 * (∫ ω, actual ω ∂μ) ^ 2 ≤
          lambda ^ 2 * ∫ ω, actual ω ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left hjensen (sq_nonneg lambda)
    have hright :
        ∫ ω,
            ‖quad.averageGradient (actual ω)‖ ^ 2 ∂μ =
          lambda ^ 2 * ∫ ω, actual ω ^ 2 ∂μ := by
      calc
        ∫ ω, ‖quad.averageGradient (actual ω)‖ ^ 2 ∂μ =
            ∫ ω, |lambda * actual ω| ^ 2 ∂μ := by
              congr 1
              ext ω
              rw [havg_linear]
              simp [Real.norm_eq_abs]
        _ = ∫ ω, lambda ^ 2 * actual ω ^ 2 ∂μ := by
              congr 1
              ext ω
              simp [abs_mul, mul_pow, sq_abs]
        _ = lambda ^ 2 * ∫ ω, actual ω ^ 2 ∂μ := by
              rw [MeasureTheory.integral_const_mul]
    calc
      lambda ^ 2 *
          |∫ ω, stepped.averageIterate (oracle.noise ω) t ∂μ| ^ 2 =
          lambda ^ 2 * (∫ ω, actual ω ∂μ) ^ 2 := by
            simp [actual, sq_abs]
      _ ≤ lambda ^ 2 * ∫ ω, actual ω ^ 2 ∂μ := hscaled
      _ = ∫ ω,
            ‖quad.averageGradient
              (stepped.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ := by
            simpa [actual] using hright.symm
  have hsum :
      Finset.sum (Finset.range T) (fun t =>
          lambda ^ 2 *
            |∫ ω,
              stepped.averageIterate (oracle.noise ω) t ∂μ| ^ 2) ≤
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            ‖quad.averageGradient
              (stepped.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) := by
    exact Finset.sum_le_sum fun t _ht => hpoint t
  have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  have hmean_to_stationarity :
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          lambda ^ 2 *
            |∫ ω,
              stepped.averageIterate (oracle.noise ω) t ∂μ| ^ 2) ≤
        quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
    calc
      ((T : ℝ)⁻¹) *
          Finset.sum (Finset.range T) (fun t =>
            lambda ^ 2 *
              |∫ ω,
                stepped.averageIterate (oracle.noise ω) t ∂μ| ^ 2) ≤
          ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                ‖quad.averageGradient
                  (stepped.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) := by
            exact mul_le_mul_of_nonneg_left hsum hTinv_nonneg
      _ =
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
            unfold quadraticLowerBoundStationarityFunctional stationarityAverage
              expectedGradientNormSq randomAverageIterate
            rfl
  exact le_trans hmean_floor hmean_to_stationarity

/-
Noncurrent route-history endpoint for `c3_all_raw_upper_half_mean_persistence_route`.
The active compiled finite counting endpoint is
`average_iterate_mean_square_floor_of_positive_density_abs_lower`.

/-- Finite-horizon endpoint for the C.3 mean-persistence argument.

If the arithmetic-average mean is bounded below on the upper half of the
horizon, then the averaged squared mean has a positive floor.  This isolates
the finite counting step from the spectral persistence proof. -/
theorem average_iterate_mean_square_floor_of_upper_half_abs_lower
    (signal : ℕ → ℝ) (lambda cmean : ℝ) (T : ℕ)
    (hT : 2 ≤ T)
    (hcmean_nonneg : 0 ≤ cmean)
    (htail : ∀ t : ℕ, T / 2 ≤ t → t < T → cmean ≤ |signal t|) :
    lambda ^ 2 * cmean ^ 2 / 4 ≤
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          lambda ^ 2 * |signal t| ^ 2) := by
  classical
  let tail : Finset ℕ := Finset.Ico (T / 2) T
  let A : ℝ := lambda ^ 2 * cmean ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sq_nonneg lambda) (sq_nonneg cmean)
  have htail_subset : tail ⊆ Finset.range T := by
    intro t ht
    simp [tail] at ht ⊢
    exact ht.2
  have hterm_nonneg :
      ∀ t ∈ Finset.range T, 0 ≤ lambda ^ 2 * |signal t| ^ 2 := by
    intro t ht
    exact mul_nonneg (sq_nonneg lambda) (sq_nonneg |signal t|)
  have htail_point :
      ∀ t ∈ tail, A ≤ lambda ^ 2 * |signal t| ^ 2 := by
    intro t ht
    have ht' : T / 2 ≤ t ∧ t < T := by
      simpa [tail] using ht
    have hlower := htail t ht'.1 ht'.2
    have hsquare : cmean ^ 2 ≤ |signal t| ^ 2 := by
      nlinarith [hcmean_nonneg, abs_nonneg (signal t), hlower]
    dsimp [A]
    exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg lambda)
  have htail_sum_lower :
      (tail.card : ℝ) * A ≤
        Finset.sum tail (fun t => lambda ^ 2 * |signal t| ^ 2) := by
    have hconst :
        Finset.sum tail (fun _t => A) ≤
          Finset.sum tail (fun t => lambda ^ 2 * |signal t| ^ 2) :=
      Finset.sum_le_sum htail_point
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hconst
  have htail_sum_le_total :
      Finset.sum tail (fun t => lambda ^ 2 * |signal t| ^ 2) ≤
        Finset.sum (Finset.range T) (fun t => lambda ^ 2 * |signal t| ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg htail_subset
      (by
        intro t _ht_range _ht_not_tail
        exact hterm_nonneg t (by simpa using _ht_range))
  have hcard_lower_nat : T / 2 ≤ tail.card := by
    dsimp [tail]
    simpa using (show T / 2 ≤ T - T / 2 by omega)
  have hT_le_four_tail_nat : T ≤ 4 * tail.card := by
    have hT_le_four_half : T ≤ 4 * (T / 2) := by omega
    exact le_trans hT_le_four_half (Nat.mul_le_mul_left 4 hcard_lower_nat)
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hT)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hquarter_le_tail_ratio :
      (1 / 4 : ℝ) ≤ (T : ℝ)⁻¹ * (tail.card : ℝ) := by
    have hcast : (T : ℝ) ≤ 4 * (tail.card : ℝ) := by
      exact_mod_cast hT_le_four_tail_nat
    field_simp [hT_ne]
    nlinarith
  have hfloor_to_tail :
      A / 4 ≤ (T : ℝ)⁻¹ * ((tail.card : ℝ) * A) := by
    calc
      A / 4 = (1 / 4 : ℝ) * A := by ring
      _ ≤ ((T : ℝ)⁻¹ * (tail.card : ℝ)) * A :=
          mul_le_mul_of_nonneg_right hquarter_le_tail_ratio hA_nonneg
      _ = (T : ℝ)⁻¹ * ((tail.card : ℝ) * A) := by ring
  calc
    lambda ^ 2 * cmean ^ 2 / 4 = A / 4 := by rfl
    _ ≤ (T : ℝ)⁻¹ * ((tail.card : ℝ) * A) := hfloor_to_tail
    _ ≤ (T : ℝ)⁻¹ *
          Finset.sum tail (fun t => lambda ^ 2 * |signal t| ^ 2) :=
        mul_le_mul_of_nonneg_left htail_sum_lower
          (inv_nonneg.mpr (Nat.cast_nonneg T))
    _ ≤ (T : ℝ)⁻¹ *
          Finset.sum (Finset.range T) (fun t =>
            lambda ^ 2 * |signal t| ^ 2) :=
        mul_le_mul_of_nonneg_left htail_sum_le_total
          (inv_nonneg.mpr (Nat.cast_nonneg T))

-/

/-- Finite positive-density endpoint for the C.3 mean-persistence argument.

If a deterministic lower bound holds on any finite subset occupying a fixed
positive fraction of the horizon, then the averaged squared mean has the
corresponding floor.  This is the source-facing counting endpoint for block
boundary or other positive-density selections. -/
theorem average_iterate_mean_square_floor_of_positive_density_abs_lower
    (signal : ℕ → ℝ) (lambda cmean density : ℝ) (T : ℕ) (S : Finset ℕ)
    (hT_pos : 0 < T)
    (hcmean_nonneg : 0 ≤ cmean)
    (hdensity_nonneg : 0 ≤ density)
    (hS_subset : S ⊆ Finset.range T)
    (hcard_lower : density * (T : ℝ) ≤ (S.card : ℝ))
    (hlower : ∀ t ∈ S, cmean ≤ |signal t|) :
    lambda ^ 2 * cmean ^ 2 * density ≤
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          lambda ^ 2 * |signal t| ^ 2) := by
  classical
  let A : ℝ := lambda ^ 2 * cmean ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sq_nonneg lambda) (sq_nonneg cmean)
  have hterm_nonneg :
      ∀ t ∈ Finset.range T, 0 ≤ lambda ^ 2 * |signal t| ^ 2 := by
    intro t _ht
    exact mul_nonneg (sq_nonneg lambda) (sq_nonneg |signal t|)
  have hS_point :
      ∀ t ∈ S, A ≤ lambda ^ 2 * |signal t| ^ 2 := by
    intro t ht
    have hsquare : cmean ^ 2 ≤ |signal t| ^ 2 := by
      nlinarith [hcmean_nonneg, abs_nonneg (signal t), hlower t ht]
    dsimp [A]
    exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg lambda)
  have hS_sum_lower :
      (S.card : ℝ) * A ≤
        Finset.sum S (fun t => lambda ^ 2 * |signal t| ^ 2) := by
    have hconst :
        Finset.sum S (fun _t => A) ≤
          Finset.sum S (fun t => lambda ^ 2 * |signal t| ^ 2) :=
      Finset.sum_le_sum hS_point
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hconst
  have hS_sum_le_total :
      Finset.sum S (fun t => lambda ^ 2 * |signal t| ^ 2) ≤
        Finset.sum (Finset.range T) (fun t => lambda ^ 2 * |signal t| ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS_subset
      (by
        intro t ht_range _ht_not_S
        exact hterm_nonneg t ht_range)
  have hT_real_pos : 0 < (T : ℝ) := by exact_mod_cast hT_pos
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_real_pos
  have hdensity_le_ratio :
      density ≤ (T : ℝ)⁻¹ * (S.card : ℝ) := by
    calc
      density = (T : ℝ)⁻¹ * (density * (T : ℝ)) := by
        field_simp [hT_ne]
      _ ≤ (T : ℝ)⁻¹ * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard_lower
          (inv_nonneg.mpr (le_of_lt hT_real_pos))
  have hfloor_to_subset :
      A * density ≤ (T : ℝ)⁻¹ * ((S.card : ℝ) * A) := by
    calc
      A * density ≤ A * ((T : ℝ)⁻¹ * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hdensity_le_ratio hA_nonneg
      _ = (T : ℝ)⁻¹ * ((S.card : ℝ) * A) := by ring
  calc
    lambda ^ 2 * cmean ^ 2 * density = A * density := by rfl
    _ ≤ (T : ℝ)⁻¹ * ((S.card : ℝ) * A) := hfloor_to_subset
    _ ≤ (T : ℝ)⁻¹ *
          Finset.sum S (fun t => lambda ^ 2 * |signal t| ^ 2) :=
        mul_le_mul_of_nonneg_left hS_sum_lower
          (inv_nonneg.mpr (le_of_lt hT_real_pos))
    _ ≤ (T : ℝ)⁻¹ *
          Finset.sum (Finset.range T) (fun t =>
            lambda ^ 2 * |signal t| ^ 2) :=
        mul_le_mul_of_nonneg_left hS_sum_le_total
          (inv_nonneg.mpr (le_of_lt hT_real_pos))

/-- Zero-stepsize endpoint for Appendix C.3.

With `alpha = 0`, the common primal initialization is invariant under the
row-stochastic push matrices, hence every arithmetic-average iterate is
exactly `x0`.  This proves the endpoint branch of the bounded
scaled-stepsize slow-floor argument, leaving only the positive-stepsize
spectral persistence leaf. -/
theorem homogeneous_zero_stepsize_averageIterate_eq_x0
    (quad : Setup Node ℝ) (noise : NoisePath Node ℝ) (t : ℕ) :
    (quad.withStepsize 0).averageIterate noise t = quad.x0 := by
  classical
  let stepped := quad.withStepsize 0
  have hprimal : ∀ t : ℕ, ∀ i : Node,
      stepped.primalState noise t i = quad.x0 := by
    intro t
    induction t with
    | zero =>
        intro i
        simp [stepped, withStepsize, primalState_zero, initialPrimal]
    | succ t ih =>
        intro i
        have hsum :
            (∑ j : Node, quad.R t i j * quad.x0) = quad.x0 := by
          rw [← Finset.sum_mul]
          simpa [rowSum] using congrArg (fun y : ℝ => y * quad.x0)
            (quad.R_row_sum t i)
        calc
          stepped.primalState noise (t + 1) i =
              leftMul (Node := Node) (E := ℝ) (quad.R t)
                  (stepped.primalState noise t) i -
                (0 : ℝ) • stepped.trackerState noise t i := by
                simpa [stepped, withStepsize] using
                  congrFun (stepped.primalState_succ noise t) i
          _ = ∑ j : Node, quad.R t i j * quad.x0 := by
                simp [leftMul, ih, smul_eq_mul]
          _ = quad.x0 := hsum
  calc
    stepped.averageIterate noise t =
        ((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ i : Node, stepped.primalState noise t i := by
          rw [stepped.averageIterate_eq_arithmeticAverage noise t]
          simp [smul_eq_mul]
    _ =
        ((nodeCount (Node := Node) : ℝ)⁻¹) *
          ∑ _i : Node, quad.x0 := by
          simp [hprimal t]
    _ = quad.x0 := by
          simp [nodeCount]

/-- Scalar lower companion to the usual contraction exponential estimate.

For `0 <= x <= 1/2`, the finite power `(1 - x)^n` is bounded below by
`exp (-2*x*n)`.  This is the ordered-real core of Appendix C.3's
`(1-C alpha)^(T/p) >= exp(-2CM/p)` step. -/
theorem real_exp_neg_two_mul_le_one_sub_pow
    (x : ℝ) (n : ℕ)
    (hx_nonneg : 0 ≤ x) (hx_half : x ≤ 1 / 2) :
    Real.exp (-(2 * x * (n : ℝ))) ≤ (1 - x) ^ n := by
  exact Real.exp_neg_two_mul_le_one_sub_pow x n hx_nonneg hx_half

/-- Appendix C.3 slow-multiplier power persistence.

The restricted slow multiplier lower envelope `gamma(alpha) >= 1-c alpha`
implies a uniform positive lower bound for every power whose index is within a
bounded scaled-stepsize horizon.  This is the first concrete source-component
supplier feeding the C.3 tail-mean proof. -/
theorem restricted_gamma_power_lower_of_bounded_scaled_stepsize
    (gamma : ℝ → ℝ) (M : ℝ) (hM_nonneg : 0 ≤ M)
    (hgamma_lower :
      ∃ alphaGammaLower cGammaLower : ℝ,
        0 < alphaGammaLower ∧ 0 < cGammaLower ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGammaLower →
            0 ≤ gamma alpha ∧ 1 - cGammaLower * alpha ≤ gamma alpha) :
    ∃ alpha0 cgam : ℝ, 0 < alpha0 ∧ 0 < cgam ∧
      cgam ≤ 1 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, ∀ k : ℕ,
        0 < alpha → alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          k ≤ T → cgam ≤ gamma alpha ^ k := by
  exact
    exists_uniform_power_lower_of_one_sub_linear_lower_and_scaled_horizon
      gamma M hM_nonneg (by aesop)

/-- Scalar probability `L²` to mean bound.

This is the Jensen/Cauchy endpoint needed by the C.3 block-start route: a
single-time square-moment bound controls the absolute deterministic mean. -/
theorem abs_integral_le_sqrt_of_sq_integral_le
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) {B : ℝ}
    (hZ_meas : AEStronglyMeasurable Z μ)
    (hZ_sq_int : Integrable (fun ω => Z ω ^ 2) μ)
    (hB_nonneg : 0 ≤ B)
    (hZ_sq_bound : (∫ ω, Z ω ^ 2 ∂μ) ≤ B) :
    |∫ ω, Z ω ∂μ| ≤ Real.sqrt B := by
  exact abs_integral_le_sqrt_of_integral_sq_le μ Z B hZ_meas hZ_sq_int hZ_sq_bound

/-- Extract a single-time mean bound from a finite `L²` sum budget. -/
theorem abs_integral_le_sqrt_of_sq_integral_finset_sum_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (out : Ω → ℕ → ℝ) {T t : ℕ} {B : ℝ}
    (hout_mem : ∀ s : ℕ, MemLp (fun ω => out ω s) 2 μ)
    (hB_nonneg : 0 ≤ B)
    (ht : t ∈ Finset.range T)
    (hsum :
      Finset.sum (Finset.range T) (fun s =>
        ∫ ω, |out ω s| ^ 2 ∂μ) ≤ B) :
    |∫ ω, out ω t ∂μ| ≤ Real.sqrt B := by
  exact abs_integral_le_sqrt_of_finset_sum_integral_sq_le
    μ (Finset.range T) out t B (hout_mem t) ht (by simpa [sq_abs] using hsum)

/-- Two-output Jensen/Cauchy endpoint for a single-time transport estimate.

If the squared difference between two scalar observables is bounded in `L²`,
then the difference of their means is bounded by the square root of the same
budget.  This is the endpoint needed after the C.3 raw-time transport is reduced
to a square-integral bound. -/
theorem abs_integral_sub_integral_le_sqrt_of_sq_integral_le
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (actual projected : Ω → ℝ) {B : ℝ}
    (hactual_int : Integrable actual μ)
    (hprojected_int : Integrable projected μ)
    (hdiff_meas : AEStronglyMeasurable (fun ω => actual ω - projected ω) μ)
    (hdiff_sq_int :
      Integrable (fun ω => (actual ω - projected ω) ^ 2) μ)
    (hB_nonneg : 0 ≤ B)
    (hdiff_sq_bound :
      (∫ ω, (actual ω - projected ω) ^ 2 ∂μ) ≤ B) :
    |(∫ ω, actual ω ∂μ) - (∫ ω, projected ω ∂μ)| ≤ Real.sqrt B := by
  exact abs_integral_sub_integral_le_sqrt_of_integral_sq_sub_le
    μ actual projected B hactual_int hprojected_int hdiff_sq_int hdiff_sq_bound

/-- Source-neutral endpoint for C.3 mean persistence.

If a stochastic arithmetic-average mean is close to a deterministic slow-mode
signal and that signal dominates the allowed error plus the desired floor,
then the stochastic mean has the desired absolute lower bound. -/
theorem abs_integral_lower_of_close_to_deterministic_signal
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (actual : Ω → ℝ) (target c err : ℝ)
    (hclose : |(∫ ω, actual ω ∂μ) - target| ≤ err)
    (hbudget : c + err ≤ |target|) :
    c ≤ |∫ ω, actual ω ∂μ| := by
  exact le_abs_of_abs_sub_le_of_add_le_abs (∫ ω, actual ω ∂μ) target c err hclose hbudget

theorem geometric_convolution_const_le_inv_one_sub
    {theta L : ℝ} (htheta_nonneg : 0 ≤ theta)
    (htheta_lt_one : theta < 1) (hL_nonneg : 0 ≤ L) :
    ∀ t : ℕ,
      Finset.sum (Finset.range t) (fun j =>
          theta ^ (t - 1 - j) * L) ≤ L / (1 - theta) := by
  exact fun t =>
    sum_range_geometric_reverse_mul_le_div_one_sub
      theta L t htheta_nonneg htheta_lt_one hL_nonneg

/-- Uniform `L¹` budget for the raw period-window envelope. -/
theorem quadraticRestrictedPeriodNoiseWindowEnvelope_integral_bound
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ CwinL1 : ℝ, 0 ≤ CwinL1 ∧
      ∀ k : ℕ,
        Integrable
          (fun ω =>
            quadraticRestrictedPeriodNoiseWindowEnvelope
              (Node := Node) quad (oracle.noise ω) k) μ ∧
        (∫ ω,
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ∂μ) ≤ CwinL1 := by
  classical
  obtain ⟨Cwin, hCwin_nonneg, hwin_bound⟩ :=
    quadraticRestrictedPeriodNoiseWindowEnvelope_secondMoment_bound
      (Node := Node) quad μ oracle hnoise
  let CwinL1 : ℝ := Cwin + 1
  refine ⟨CwinL1, ?_, ?_⟩
  · dsimp [CwinL1]
    linarith
  intro k
  have hsq_int :
      Integrable
        (fun ω =>
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k ^ 2) μ :=
    quadraticRestrictedPeriodNoiseWindowEnvelope_sq_integrable
      (Node := Node) quad μ oracle hnoise k
  have hnonneg :
      ∀ᵐ ω ∂μ,
        0 ≤
          quadraticRestrictedPeriodNoiseWindowEnvelope
            (Node := Node) quad (oracle.noise ω) k :=
    Filter.Eventually.of_forall fun ω =>
      quadraticRestrictedPeriodNoiseWindowEnvelope_nonneg
        (Node := Node) quad (oracle.noise ω) k
  have hL1 :=
    integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
      (μ := μ) (Z := fun ω =>
        quadraticRestrictedPeriodNoiseWindowEnvelope
          (Node := Node) quad (oracle.noise ω) k)
      (C := Cwin) hsq_int hnonneg (hwin_bound k)
  exact ⟨hL1.1, by simpa [CwinL1] using hL1.2⟩

/-- Appendix C.3 stable-output mean domination.

The geometric impulse estimate gives an `alpha` factor pathwise.  The raw
period-window envelope has a uniform first-moment bound, so direct integration
of the geometric convolution gives a pointwise-in-time mean bound. -/
theorem quadratic_restricted_stable_boundary_output_mean_abs_le_linear_stepsize
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alphaRestricted theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hr0_nonneg : 0 ≤ r0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alphaRestricted theta K right left gamma P F)
    (hstable_impulse :
      ∃ C theta1 alphaImpulse : ℝ,
        0 ≤ C ∧ theta < theta1 ∧ theta1 < 1 ∧
          0 < alphaImpulse ∧ alphaImpulse ≤ alphaRestricted ∧
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
                            (Node := Node) quad noise j)))
    (hstable_output_memLp :
      ∀ alpha : ℝ, ∀ k : ℕ,
        MemLp
          (fun ω : Ω =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (quadraticRestrictedStableBoundaryResponse
                (Node := Node) quad lambda i0 P F alpha
                (oracle.noise ω) k)) 2 μ) :
    ∃ Cstable alphaStable : ℝ,
      0 ≤ Cstable ∧ 0 < alphaStable ∧ alphaStable ≤ alphaRestricted ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaStable →
          ∀ k : ℕ,
            |∫ ω,
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P F alpha
                  (oracle.noise ω) k) ∂μ| ≤
              Cstable * alpha := by
  classical
  obtain ⟨C, theta1, alphaImpulse, hC_nonneg, htheta_lt_theta1,
      htheta1_lt_one, halphaImpulse_pos, halphaImpulse_le_restricted,
      himpulse⟩ := hstable_impulse
  obtain ⟨CwinL1, hCwinL1_nonneg, hwinL1⟩ :=
    quadraticRestrictedPeriodNoiseWindowEnvelope_integral_bound
      (Node := Node) quad μ oracle hnoise
  let Idx := Sum Node {i : Node // i ≠ i0}
  let A0 : ℝ :=
    1 +
      rowEuclideanNorm (Node := Idx)
        (fun a : Idx =>
          match a with
          | Sum.inl _ => quad.x0
          | Sum.inr _ => 0)
  let Cenv : ℝ := A0 + CwinL1 / (1 - theta1)
  let Cstable : ℝ := C * Cenv
  have htheta_pos : 0 < theta :=
    lt_of_le_of_lt hr0_nonneg hsplitting.2.1
  have htheta1_pos : 0 < theta1 :=
    lt_trans htheta_pos htheta_lt_theta1
  have htheta1_nonneg : 0 ≤ theta1 := htheta1_pos.le
  have htheta1_le_one : theta1 ≤ 1 := le_of_lt htheta1_lt_one
  have hden_pos : 0 < 1 - theta1 := by linarith
  have hA0_nonneg : 0 ≤ A0 := by
    have hnorm_nonneg :
        0 ≤ rowEuclideanNorm (Node := Idx)
          (fun a : Idx =>
            match a with
            | Sum.inl _ => quad.x0
            | Sum.inr _ => 0) := by
      simpa [rowEuclideanNorm] using
        Real.sqrt_nonneg
          (rowNormSq (Node := Idx)
            (fun a : Idx =>
              match a with
              | Sum.inl _ => quad.x0
              | Sum.inr _ => 0))
    dsimp [A0]
    linarith
  have hCenv_nonneg : 0 ≤ Cenv := by
    dsimp [Cenv]
    exact add_nonneg hA0_nonneg
      (div_nonneg hCwinL1_nonneg hden_pos.le)
  have hCstable_nonneg : 0 ≤ Cstable := by
    dsimp [Cstable]
    exact mul_nonneg hC_nonneg hCenv_nonneg
  refine ⟨Cstable, alphaImpulse, hCstable_nonneg, halphaImpulse_pos,
    halphaImpulse_le_restricted, ?_⟩
  intro alpha halpha_pos halpha_le k
  let out : Ω → ℝ := fun ω =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (quadraticRestrictedStableBoundaryResponse
        (Node := Node) quad lambda i0 P F alpha
        (oracle.noise ω) k)
  have hout_int : Integrable out μ :=
    (hstable_output_memLp alpha k).integrable (by norm_num)
  have hpoint : ∀ ω : Ω,
      |out ω| ≤ C * alpha *
        (theta1 ^ k * A0 +
          Finset.sum (Finset.range k) (fun j =>
            theta1 ^ (k - 1 - j) *
              quadraticRestrictedPeriodNoiseWindowEnvelope
                (Node := Node) quad (oracle.noise ω) j)) := by
    intro ω
    have h := himpulse alpha halpha_pos halpha_le (oracle.noise ω) k
    have hinit_eq :=
      quadraticRestrictedInitialBoundaryCoord_eq_const
        (Node := Node) quad alpha i0 (oracle.noise ω)
    simpa [out, A0, Idx, hinit_eq] using h
  have hbound :=
    abs_integral_le_linear_scale_of_geometric_convolution_envelope
      μ out
      (fun ω j =>
        quadraticRestrictedPeriodNoiseWindowEnvelope
          (Node := Node) quad (oracle.noise ω) j)
      (C * alpha) theta1 A0 CwinL1 k hout_int
      (fun j _ => (hwinL1 j).1) (mul_nonneg hC_nonneg halpha_pos.le)
      htheta1_nonneg htheta1_lt_one hA0_nonneg hCwinL1_nonneg
      (fun j _ => (hwinL1 j).2) (Filter.Eventually.of_forall hpoint)
  calc
    |∫ ω,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F alpha
            (oracle.noise ω) k) ∂μ| = |∫ ω, out ω ∂μ| := by rfl
    _ ≤ (C * alpha) * (A0 + CwinL1 / (1 - theta1)) := hbound
    _ = Cstable * alpha := by
      dsimp [Cstable, Cenv]
      ring

/-- Appendix C.3 initial slow-coordinate mean margin.

The projected initial slow coordinate is `x0 + O(alpha)` in mean because the
already proved initial projected/scalar `L²` error is `O(alpha²)` and the scalar
comparison process starts exactly at `x0`. -/
theorem quadratic_restricted_projected_initial_boundary_mean_abs_lower
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alphaRestricted theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} =>
        right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alphaRestricted theta K right left gamma P F)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hx0_abs_pos : 0 < |quad.x0|) :
    ∃ alphaInitMean : ℝ,
      0 < alphaInitMean ∧ alphaInitMean ≤ alphaRestricted ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInitMean →
          |quad.x0| / 2 ≤
            |∫ ω,
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState
                        (oracle.noise ω) 0,
                      (quad.withStepsize alpha).trackerErrorZeroSum
                        (oracle.noise ω) 0))) ∂μ| := by
  classical
  obtain ⟨Cinit, alphaInit, hCinit_nonneg, halphaInit_pos,
      halphaInit_le_restricted, hinit_l2⟩ :=
    quadratic_restricted_projected_scalar_initial_error_l2_alpha2_bound
      (Node := Node) quad lambda i0 r0 alphaRestricted theta K
      right left gamma P F hP0 hright_top hleft_top hleft_bottom
      hsplitting μ oracle
  let Idx := Sum Node {i : Node // i ≠ i0}
  let initVec : RowVector Idx := fun a =>
    match a with
    | Sum.inl _ => quad.x0
    | Sum.inr _ => 0
  let actual : ℝ → Ω → ℝ := fun alpha ω =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha)
        (restrictedStateToCoord (Node := Node) i0
          ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
            (quad.withStepsize alpha).trackerErrorZeroSum
              (oracle.noise ω) 0)))
  let actualConst : ℝ → ℝ := fun alpha =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha) initVec)
  have hactual_eq_const :
      ∀ alpha : ℝ, actual alpha = fun _ω : Ω => actualConst alpha := by
    intro alpha
    funext ω
    have hinit_eq :=
      quadraticRestrictedInitialBoundaryCoord_eq_const
        (Node := Node) quad alpha i0 (oracle.noise ω)
    dsimp [actual, actualConst]
    rw [hinit_eq]
    rfl
  have hactual_int :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInit → Integrable (actual alpha) μ := by
    intro alpha _halpha_pos _halpha_le
    rw [hactual_eq_const alpha]
    exact integrable_const _
  have hdiff_sq_int :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInit →
        Integrable (fun ω : Ω => (actual alpha ω - quad.x0) ^ 2) μ := by
    intro alpha _halpha_pos _halpha_le
    rw [hactual_eq_const alpha]
    exact integrable_const _
  have hdiff_sq_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInit →
        (∫ ω, (actual alpha ω - quad.x0) ^ 2 ∂μ) ≤
          Cinit * alpha ^ 2 := by
    intro alpha halpha_pos halpha_le
    have hraw := hinit_l2 alpha halpha_pos halpha_le
    simpa [actual, sq_abs, quadraticScalarComparisonProcess_zero] using hraw
  obtain ⟨alphaInitMean, halphaInitMean_pos, halphaInitMean_le_init,
      hlower⟩ :=
    exists_small_parameter_abs_integral_ge_half_of_l2_error_le_mul_sq
      μ actual quad.x0 Cinit alphaInit hx0_abs_pos hCinit_nonneg
      halphaInit_pos hactual_int hdiff_sq_int hdiff_sq_bound
  refine ⟨alphaInitMean, halphaInitMean_pos,
    le_trans halphaInitMean_le_init halphaInit_le_restricted, ?_⟩
  intro alpha halpha_pos halpha_le
  simpa [actual] using hlower alpha halpha_pos halpha_le

/-- Block-boundary representatives occupy a fixed positive fraction of any
large horizon.

This is the finite counting part of the Appendix C.3 replacement route.  It
selects complete-period block starts `k * p` and records both their membership
in `range T` and their density lower bound. -/
theorem block_boundary_positive_density_subset
    (p T : ℕ) (hp : 0 < p) (hT : 2 * p ≤ T) :
    ∃ S : Finset ℕ,
      S ⊆ Finset.range T ∧
        ((1 : ℝ) / (2 * (p : ℝ))) * (T : ℝ) ≤ (S.card : ℝ) ∧
          ∀ t ∈ S, ∃ k : ℕ, k < T / p ∧ t = k * p := by
  classical
  let S : Finset ℕ := (Finset.range (T / p)).image (fun k : ℕ => k * p)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro t ht
    dsimp [S] at ht
    rcases Finset.mem_image.mp ht with ⟨k, hk, rfl⟩
    simp at hk ⊢
    have hk_succ : k + 1 ≤ T / p := Nat.succ_le_of_lt hk
    have hmul_le : (k + 1) * p ≤ (T / p) * p :=
      Nat.mul_le_mul_right p hk_succ
    have hdiv_mul_le : (T / p) * p ≤ T := Nat.div_mul_le_self T p
    have hk_mul_lt : k * p < (k + 1) * p :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) hp
    exact lt_of_lt_of_le hk_mul_lt (le_trans hmul_le hdiv_mul_le)
  · have hcard : S.card = T / p := by
      dsimp [S]
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b h
        exact Nat.mul_right_cancel hp h
    have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp
    let qR : ℝ := ((T / p : ℕ) : ℝ)
    have hq_ge_two_nat : 2 ≤ T / p := by
      rw [Nat.le_div_iff_mul_le hp]
      simpa [mul_comm] using hT
    have hq_ge_one_real : 1 ≤ qR := by
      dsimp [qR]
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hq_ge_two_nat)
    have hT_le_succ_nat : T ≤ p * (T / p + 1) :=
      le_of_lt (Nat.lt_mul_div_succ T hp)
    have hT_real_le : (T : ℝ) ≤ (qR + 1) * (p : ℝ) := by
      have hcast : (T : ℝ) ≤ (p * (T / p + 1) : ℕ) := by
        exact_mod_cast hT_le_succ_nat
      dsimp [qR]
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm,
        mul_left_comm, mul_assoc] using hcast
    have hq_succ_le_two_q : qR + 1 ≤ 2 * qR := by
      linarith
    have hT_over_bound : (T : ℝ) / (2 * (p : ℝ)) ≤ qR := by
      have hden_pos : 0 < 2 * (p : ℝ) := by positivity
      calc
        (T : ℝ) / (2 * (p : ℝ)) ≤
            ((qR + 1) * (p : ℝ)) / (2 * (p : ℝ)) := by
          exact div_le_div_of_nonneg_right hT_real_le (le_of_lt hden_pos)
        _ = (qR + 1) / 2 := by
          field_simp [ne_of_gt hp_real_pos]
        _ ≤ qR := by linarith
    rw [hcard]
    dsimp [qR] at hT_over_bound
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hT_over_bound
  · intro t ht
    dsimp [S] at ht
    rcases Finset.mem_image.mp ht with ⟨k, hk, hkt⟩
    refine ⟨k, ?_, ?_⟩
    · simpa using hk
    · exact hkt.symm

/-- Pure scalar absorption for the block-boundary lower bound.

If the projected mean is at least `B / 2` in absolute value and the stable
mean has size at most `B / 4`, then their sum has size at least `B / 4`. -/
theorem scalar_block_boundary_mean_lower_of_projected_lower_and_stable_upper
    {A P S B : ℝ} (hA : A = P + S)
    (hP : B / 2 ≤ |P|) (hS : |S| ≤ B / 4) (hB : 0 ≤ B) :
    B / 4 ≤ |A| := by
  have hP_eq : P = A + -S := by
    rw [hA]
    ring
  have htri : |P| ≤ |A| + |S| := by
    have h := abs_add_le A (-S)
    simpa [hP_eq, abs_neg] using h
  nlinarith

/-- Projected block-boundary slow means obey the homogeneous slow recursion.

This is the expectation-level Appendix C.3 persistence bridge: after applying
the Riesz projection to the restricted period recursion, the period innovation
has zero mean, so the projected slow boundary mean is multiplied by
`gamma alpha` at each complete block. -/
theorem quadratic_restricted_projected_boundary_mean_eq_initial_mul_gamma_pow
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alphaRestricted theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alphaRestricted theta K right left gamma P F)
    (alpha : ℝ) (halpha_abs : |alpha| ≤ alphaRestricted) :
    ∀ k : ℕ,
      (∫ ω,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (P alpha)
            (restrictedStateToCoord (Node := Node) i0
              ((quad.withStepsize alpha).primalState
                  (oracle.noise ω) (k * quad.period),
                (quad.withStepsize alpha).trackerErrorZeroSum
                  (oracle.noise ω) (k * quad.period)))) ∂μ) =
        (∫ ω,
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω) 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) 0))) ∂μ) *
          gamma alpha ^ k := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let stepped := quad.withStepsize alpha
  let projectedBoundary : Ω → ℕ → ℝ := fun ω m =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha)
        (restrictedStateToCoord (Node := Node) i0
          (stepped.primalState (oracle.noise ω) (m * quad.period),
            stepped.trackerErrorZeroSum (oracle.noise ω)
              (m * quad.period))))
  let projectedInput : Ω → ℕ → ℝ := fun ω m =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 (oracle.noise ω) m))
  have hrestricted_period_boundary_recursion :
      ∀ noise : NoisePath Node ℝ, ∀ m : ℕ,
        let stepped := quad.withStepsize alpha
        restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise ((m + 1) * quad.period),
              stepped.trackerErrorZeroSum noise ((m + 1) * quad.period)) =
          matrixMulVector
              (Node := Idx)
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
              (restrictedStateToCoord (Node := Node) i0
                (stepped.primalState noise (m * quad.period),
                  stepped.trackerErrorZeroSum noise (m * quad.period))) +
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise m := by
    intro noise m
    simpa [Idx] using
      quadratic_restricted_period_inhomogeneous_recursion
        (Node := Node) quad lambda alpha i0 hquad noise m
  have hboundary_rec :
      ∀ ω : Ω, ∀ m : ℕ,
        projectedBoundary ω (m + 1) =
          gamma alpha * projectedBoundary ω m + projectedInput ω m := by
    intro ω m
    let yk : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState (oracle.noise ω) (m * quad.period),
          stepped.trackerErrorZeroSum (oracle.noise ω)
            (m * quad.period))
    let yNext : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState (oracle.noise ω) ((m + 1) * quad.period),
          stepped.trackerErrorZeroSum (oracle.noise ω)
            ((m + 1) * quad.period))
    let xi : RowVector Idx :=
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 (oracle.noise ω) m
    have hlocal := hsplitting.2.2.2.2.2.2.2.2 alpha halpha_abs
    have hyNext :
        yNext =
          matrixMulVector (Node := Idx)
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) yk + xi := by
      simpa [Idx, stepped, yk, yNext, xi] using
        hrestricted_period_boundary_recursion (oracle.noise ω) m
    simpa [projectedBoundary, projectedInput, Idx, stepped, yk, yNext, xi]
      using
        quadratic_restricted_projected_slow_boundary_recursion
          (Node := Node) i0 (gamma alpha) (P alpha) (F alpha)
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
          hlocal.1.1.1 hlocal.2.1 hlocal.2.2.1
          yk xi yNext hyNext
  have hboundary_memLp :
      ∀ m : ℕ, MemLp (fun ω : Ω => projectedBoundary ω m) 2 μ := by
    intro m
    let coord : Ω → RowVector Idx := fun ω =>
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState (oracle.noise ω) (m * quad.period),
          stepped.trackerErrorZeroSum (oracle.noise ω)
            (m * quad.period))
    have hcoord :
        ∀ a : Idx, MemLp (fun ω : Ω => coord ω a) 2 μ := by
      intro a
      simpa [Idx, stepped, coord] using
        quadraticRestrictedBoundaryCoord_coordinate_memLp
          (Node := Node) quad alpha i0 μ oracle hnoise
          (m * quad.period) a
    have hprojected_coord :
        ∀ i : Node,
          MemLp
            (fun ω : Ω =>
              matrixMulVector (Node := Idx) (P alpha) (coord ω)
                (Sum.inl i)) 2 μ := by
      intro i
      unfold matrixMulVector
      apply memLp_finset_sum Finset.univ
      intro a _ha
      exact (hcoord a).const_smul (P alpha (Sum.inl i) a)
    have hprojected_sum :
        MemLp
          (fun ω : Ω =>
            ∑ i : Node,
              matrixMulVector (Node := Idx) (P alpha) (coord ω)
                (Sum.inl i)) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact hprojected_coord i
    dsimp [projectedBoundary]
    simpa [quadraticRestrictedPrimalAverageOutput, Idx, stepped, coord] using
      hprojected_sum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hinput_memLp :
      ∀ m : ℕ, MemLp (fun ω : Ω => projectedInput ω m) 2 μ := by
    intro m
    have hxi_coord :
        ∀ a : Idx,
          MemLp
            (fun ω : Ω =>
              quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) m a)
            2 μ := by
      intro a
      exact
        quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
          (Node := Node) quad lambda alpha i0 μ oracle hnoise m a
    have hprojected_coord :
        ∀ i : Node,
          MemLp
            (fun ω : Ω =>
              matrixMulVector (Node := Idx) (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 (oracle.noise ω) m)
                (Sum.inl i)) 2 μ := by
      intro i
      unfold matrixMulVector
      apply memLp_finset_sum Finset.univ
      intro a _ha
      exact (hxi_coord a).const_smul (P alpha (Sum.inl i) a)
    have hprojected_sum :
        MemLp
          (fun ω : Ω =>
            ∑ i : Node,
              matrixMulVector (Node := Idx) (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 (oracle.noise ω) m)
                (Sum.inl i)) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact hprojected_coord i
    dsimp [projectedInput]
    simpa [quadraticRestrictedPrimalAverageOutput, Idx] using
      hprojected_sum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hboundary_int :
      ∀ m : ℕ, Integrable (fun ω : Ω => projectedBoundary ω m) μ := by
    intro m
    exact (hboundary_memLp m).integrable (by norm_num)
  have hinput_int :
      ∀ m : ℕ, Integrable (fun ω : Ω => projectedInput ω m) μ := by
    intro m
    exact (hinput_memLp m).integrable (by norm_num)
  have hinput_zero :
      ∀ m : ℕ, (∫ ω, projectedInput ω m ∂μ) = 0 := by
    intro m
    simpa [projectedInput, Idx] using
      quadratic_restricted_projected_period_input_integral_eq_zero
        (Node := Node) quad lambda i0 P μ oracle hnoise alpha m
  intro k
  induction k with
  | zero =>
      simp [projectedBoundary]
  | succ k ih =>
      have ih_projected :
          (∫ ω, projectedBoundary ω k ∂μ) =
            (∫ ω, projectedBoundary ω 0 ∂μ) * gamma alpha ^ k := by
        simpa [projectedBoundary, Idx, stepped] using ih
      calc
        (∫ ω, projectedBoundary ω (k + 1) ∂μ) =
            ∫ ω, gamma alpha * projectedBoundary ω k +
              projectedInput ω k ∂μ := by
              congr with ω
              rw [hboundary_rec ω k]
        _ =
            (∫ ω, gamma alpha * projectedBoundary ω k ∂μ) +
              ∫ ω, projectedInput ω k ∂μ := by
              rw [MeasureTheory.integral_add]
              · exact (hboundary_int k).const_mul (gamma alpha)
              · exact hinput_int k
        _ =
            gamma alpha * (∫ ω, projectedBoundary ω k ∂μ) := by
              rw [MeasureTheory.integral_const_mul, hinput_zero k]
              ring
        _ =
            (∫ ω, projectedBoundary ω 0 ∂μ) *
              gamma alpha ^ (k + 1) := by
              rw [ih_projected]
              ring
        _ =
            (∫ ω,
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState
                        (oracle.noise ω) 0,
                      (quad.withStepsize alpha).trackerErrorZeroSum
                        (oracle.noise ω) 0))) ∂μ) *
              gamma alpha ^ (k + 1) := by
              simp [projectedBoundary, Idx, stepped]

/-
Route tombstone: `c3_all_raw_upper_half_mean_persistence_route`.

The all-raw upper-half mean-persistence supplier below is noncurrent and is
kept only as route-history text.  It is intentionally outside the compiled
proof surface so the Appendix C.3 public/source cone cannot depend on it.  The
active replacement is the positive-density/block-boundary route beginning at
`quadratic_restricted_positive_density_mean_abs_lower_of_bounded_scaled_stepsize`
and consumed by
`quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize`.

set_option maxHeartbeats 800000 in
/-- Appendix C.3 spectral tail-mean supplier at the source-component boundary.

This is the remaining slow-mode persistence leaf after the finite counting and
Jensen steps have been split off.  Its inputs are exactly the source components:
the restricted Riesz splitting, the scalar/restricted multiplier contraction,
the nonzero initial slow coefficient, the proved stable-output impulse bridge,
and the exact iid mean-zero noise law. -/
theorem legacy_noncurrent_c3_all_raw_upper_half_mean_abs_lower
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alphaRestricted theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} =>
        right i * left j))
    (hright_eq :
      right =
        quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0)
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hr0_nonneg : 0 ≤ r0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alphaRestricted theta K right left gamma P F)
    (hgamma_contract :
      ∃ alphaGamma cGamma Cmul : ℝ,
        0 < alphaGamma ∧ 0 < cGamma ∧ 0 < Cmul ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGamma →
            let Gamma :=
              quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
            0 ≤ Gamma ∧ Gamma ≤ 1 - cGamma * alpha ∧
              |gamma alpha - Gamma| ≤ Cmul * alpha ^ 2 ∧
                0 ≤ gamma alpha ∧ gamma alpha ≤ 1 - cGamma * alpha ∧
                  0 < 1 - cGamma * alpha)
    (hgamma_lower :
      ∃ alphaGammaLower cGammaLower : ℝ,
        0 < alphaGammaLower ∧ 0 < cGammaLower ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGammaLower →
            0 ≤ gamma alpha ∧ 1 - cGammaLower * alpha ≤ gamma alpha)
    (hx0_abs_pos : 0 < |quad.x0|)
    (hstable_impulse :
      ∃ C theta1 alphaImpulse : ℝ,
        0 ≤ C ∧ theta < theta1 ∧ theta1 < 1 ∧
          0 < alphaImpulse ∧ alphaImpulse ≤ alphaRestricted ∧
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
                            (Node := Node) quad noise j)))
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ cmean alpha0 T0, 0 < cmean ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          ∀ t : ℕ, T / 2 ≤ t → t < T →
            cmean ≤
              |∫ ω,
                (quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) t ∂μ| := by
  classical
  /- Exact remaining Appendix C.3 source leaf.

  The caller has already constructed:
  * `hgamma_contract`, giving the upper contraction envelope used by stable
    comparisons;
  * `hgamma_lower`, giving the lower slow multiplier persistence after
    combining the scalar squeeze with the restricted multiplier `O(alpha^2)`;
  * `hstable_impulse`, the proved Appendix C.1 step-4 geometric stable-output
    supplier;
  * `hx0_abs_pos`, the nonzero initial coefficient, and `hnoise`, the exact
    iid mean-zero law.

  What remains is the source proof that these components imply
  `|E \bar x_t|` stays uniformly positive on the upper half of every bounded
  scaled-stepsize horizon. -/
  have hrestricted_period_boundary_recursion :
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
              (Node := Node) quad lambda alpha i0 noise k := by
    intro alpha noise k
    exact
      quadratic_restricted_period_inhomogeneous_recursion
        (Node := Node) quad lambda alpha i0 hquad noise k
  have hrestricted_splitting_at :
      ∀ alpha : ℝ, |alpha| ≤ alphaRestricted →
        IsRieszProjectionAtEigenvalue
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
            (gamma alpha) (P alpha) ∧
          quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0 =
            matrixAdd (Node := Sum Node {i : Node // i ≠ i0})
              ((gamma alpha) • P alpha) (F alpha) ∧
            matrixMul (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha) (F alpha) = 0 ∧
              matrixMul (Node := Sum Node {i : Node // i ≠ i0})
                  (F alpha) (P alpha) = 0 ∧
                ∀ j : ℕ,
                  matrixEuclideanOperatorNorm
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (matrixPower (Node := Sum Node {i : Node // i ≠ i0})
                        (F alpha) j) ≤
                    K * theta ^ j := by
    intro alpha halpha_abs
    exact hsplitting.2.2.2.2.2.2.2.2 alpha halpha_abs
  have hgamma_power_lower :=
    restricted_gamma_power_lower_of_bounded_scaled_stepsize
      gamma M hM_nonneg hgamma_lower
  have hinitial_error :=
    quadratic_restricted_projected_scalar_initial_error_l2_alpha2_bound
      (Node := Node) quad lambda i0 r0 alphaRestricted theta K
      right left gamma P F hP0 hright_top hleft_top hleft_bottom
      hsplitting μ oracle
  rcases hgamma_power_lower with
    ⟨alphaGammaPower, cgam, halphaGammaPower_pos, hcgam_pos, hcgam_le_one,
      hgamma_power_lower_point⟩
  rcases hinitial_error with
    ⟨Cinit, alphaInit, hCinit_nonneg, halphaInit_pos,
      halphaInit_le_restricted, hprojected_scalar_initial_error⟩
  rcases hgamma_contract with
    ⟨alphaGammaContract, cGammaContract, Cmul,
      halphaGammaContract_pos, hcGammaContract_pos, hCmul_pos,
      hgamma_contract_point⟩
  let cmean : ℝ := |quad.x0| * cgam / 4
  let alphaAbsorb : ℝ :=
    min 1
      ((|quad.x0| * cgam) /
        (16 * (Real.sqrt Cinit + (M + 1) * Cmul * |quad.x0| + 1)))
  let alpha0 : ℝ :=
    min alphaGammaPower
      (min alphaInit (min alphaGammaContract alphaAbsorb))
  have hcmean_pos : 0 < cmean := by
    dsimp [cmean]
    positivity
  have halphaAbsorb_pos : 0 < alphaAbsorb := by
    have hden_pos :
        0 <
          16 * (Real.sqrt Cinit + (M + 1) * Cmul * |quad.x0| + 1) := by
      have hM1_pos : 0 < M + 1 := by linarith
      have hterm_nonneg : 0 ≤ (M + 1) * Cmul * |quad.x0| := by
        positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt Cinit := Real.sqrt_nonneg Cinit
      positivity
    dsimp [alphaAbsorb]
    exact lt_min zero_lt_one (div_pos (mul_pos hx0_abs_pos hcgam_pos) hden_pos)
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaGammaPower_pos
      (lt_min halphaInit_pos
        (lt_min halphaGammaContract_pos halphaAbsorb_pos))
  refine ⟨cmean, alpha0, 2, hcmean_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled t ht_half ht_lt
  rcases halpha_nonneg.eq_or_lt with halpha_zero | halpha_pos
  · subst alpha
    have hmean_eq :
        (∫ ω,
          (quad.withStepsize 0).averageIterate
            (oracle.noise ω) t ∂μ) = quad.x0 := by
      calc
        (∫ ω,
          (quad.withStepsize 0).averageIterate
            (oracle.noise ω) t ∂μ) =
            ∫ _ω : Ω, quad.x0 ∂μ := by
              congr with ω
              exact homogeneous_zero_stepsize_averageIterate_eq_x0
                (Node := Node) quad (oracle.noise ω) t
        _ = quad.x0 := by simp
    have hhalf : |quad.x0| * cgam / 4 ≤ |quad.x0| := by
      nlinarith [le_of_lt hx0_abs_pos, hcgam_pos.le, hcgam_le_one]
    simpa [cmean, hmean_eq] using hhalf
  · have halpha_le_gamma_power : alpha ≤ alphaGammaPower :=
      le_trans halpha_le (min_le_left _ _)
    have halpha_le_init : alpha ≤ alphaInit :=
      le_trans halpha_le
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have halpha_le_gamma_contract : alpha ≤ alphaGammaContract :=
      le_trans halpha_le
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
    have halpha_le_absorb : alpha ≤ alphaAbsorb :=
      le_trans halpha_le
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (min_le_right _ _)))
    have _hgamma_tail :
        ∀ k : ℕ, k ≤ T → cgam ≤ gamma alpha ^ k :=
      fun k hk =>
        hgamma_power_lower_point T alpha k halpha_pos
          halpha_le_gamma_power hscaled hk
    have _hinitial_error_alpha :=
      hprojected_scalar_initial_error alpha halpha_pos halpha_le_init
    have _hscalar_block_mean :
        ∀ k : ℕ,
          (∫ ω,
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) (k * quad.period) ∂μ) =
            quad.x0 *
              quadraticScalarPeriodMultiplier
                (Node := Node) quad lambda alpha ^ k :=
      quadraticScalarComparisonProcess_block_boundary_integral_eq_x0_mul_gamma_pow
        (Node := Node) quad lambda alpha μ oracle hnoise
    let k : ℕ := t / quad.period
    have halpha_le_restricted : alpha ≤ alphaRestricted :=
      le_trans halpha_le_init halphaInit_le_restricted
    have halpha_abs_restricted : |alpha| ≤ alphaRestricted := by
      simpa [abs_of_pos halpha_pos] using halpha_le_restricted
    have _hprojected_scalar_boundary_error_recursion :
        ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
          let stepped := quad.withStepsize alpha
          let projectedBoundary : ℕ → ℝ := fun m =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  (stepped.primalState noise
                      (m * quad.period),
                    stepped.trackerErrorZeroSum noise
                      (m * quad.period))))
          let scalarBoundary : ℕ → ℝ := fun m =>
            quad.quadraticScalarComparisonProcess lambda alpha
              noise (m * quad.period)
          let projectedInput : ℕ → ℝ := fun m =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0
                  noise m))
          let scalarInput : ℕ → ℝ := fun m =>
            quadraticScalarBlockNoiseInnovation (Node := Node)
              quad lambda alpha noise m
          projectedBoundary (k + 1) - scalarBoundary (k + 1) =
            gamma alpha * (projectedBoundary k - scalarBoundary k) +
              ((gamma alpha -
                  quadraticScalarPeriodMultiplier (Node := Node)
                    quad lambda alpha) *
                  scalarBoundary k +
                (projectedInput k - scalarInput k)) :=
      fun noise =>
        quadratic_restricted_projected_scalar_boundary_error_recursion
          (Node := Node) quad lambda i0 alphaRestricted theta K gamma P F
          hrestricted_period_boundary_recursion hrestricted_splitting_at
          alpha halpha_abs_restricted noise
    let target : ℝ := quad.x0 * gamma alpha ^ k
    let err : ℝ := |quad.x0| * cgam - cmean
    have hk_le_T : k ≤ T := by
      exact le_trans (Nat.div_le_self t quad.period) (Nat.le_of_lt ht_lt)
    have hgamma_k_lower : cgam ≤ gamma alpha ^ k :=
      _hgamma_tail k hk_le_T
    have hgamma_k_nonneg : 0 ≤ gamma alpha ^ k :=
      le_trans hcgam_pos.le hgamma_k_lower
    have htarget_floor : |quad.x0| * cgam ≤ |target| := by
      calc
        |quad.x0| * cgam ≤ |quad.x0| * (gamma alpha ^ k) :=
          mul_le_mul_of_nonneg_left hgamma_k_lower (abs_nonneg quad.x0)
        _ = |target| := by
          rw [abs_mul, abs_of_nonneg hgamma_k_nonneg]
    have hbudget : cmean + err ≤ |target| := by
      calc
        cmean + err = |quad.x0| * cgam := by
          dsimp [err]
          ring
        _ ≤ |target| := htarget_floor
    have hmean_close_to_restricted_slow :
        |(∫ ω,
            (quad.withStepsize alpha).averageIterate
              (oracle.noise ω) t ∂μ) - target| ≤ err := by
      have hprojected_input_scalar_diff_mean_zero :
          ∀ m : ℕ,
            (∫ ω,
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0
                      (oracle.noise ω) m)) -
                quadraticScalarBlockNoiseInnovation (Node := Node)
                  quad lambda alpha (oracle.noise ω) m ∂μ) = 0 := by
        intro m
        exact
          quadratic_restricted_projected_period_input_scalar_block_diff_integral_eq_zero
            (Node := Node) quad lambda i0 P μ oracle hnoise alpha m
      let projectedBoundary : Ω → ℕ → ℝ := fun ω m =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
            (restrictedStateToCoord (Node := Node) i0
              ((quad.withStepsize alpha).primalState
                  (oracle.noise ω) (m * quad.period),
                (quad.withStepsize alpha).trackerErrorZeroSum
                  (oracle.noise ω) (m * quad.period))))
      let scalarBoundary : Ω → ℕ → ℝ := fun ω m =>
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) (m * quad.period)
      let inputDiff : Ω → ℕ → ℝ := fun ω m =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) m)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) m
      let errSeq : Ω → ℕ → ℝ := fun ω m =>
        projectedBoundary ω m - scalarBoundary ω m
      have hboundary_err_rec :
          ∀ ω : Ω, ∀ m : ℕ,
            errSeq ω (m + 1) =
              gamma alpha * errSeq ω m +
                ((gamma alpha -
                    quadraticScalarPeriodMultiplier (Node := Node)
                      quad lambda alpha) *
                    scalarBoundary ω m +
                  inputDiff ω m) := by
        intro ω m
        simpa [errSeq, projectedBoundary, scalarBoundary, inputDiff] using
          _hprojected_scalar_boundary_error_recursion (oracle.noise ω) m
      have hboundary_err_memLp :
          ∀ m : ℕ, MemLp (fun ω : Ω => errSeq ω m) 2 μ := by
        intro m
        let Idx := Sum Node {i : Node // i ≠ i0}
        let stepped := quad.withStepsize alpha
        let coord : Ω → RowVector Idx := fun ω =>
          restrictedStateToCoord (Node := Node) i0
            (stepped.primalState (oracle.noise ω) (m * quad.period),
              stepped.trackerErrorZeroSum (oracle.noise ω)
                (m * quad.period))
        have hcoord :
            ∀ a : Idx, MemLp (fun ω : Ω => coord ω a) 2 μ := by
          intro a
          simpa [Idx, stepped, coord] using
            quadraticRestrictedBoundaryCoord_coordinate_memLp
              (Node := Node) quad alpha i0 μ oracle hnoise
              (m * quad.period) a
        have hprojected_coord :
            ∀ i : Node,
              MemLp
                (fun ω : Ω =>
                  matrixMulVector (Node := Idx) (P alpha) (coord ω)
                    (Sum.inl i)) 2 μ := by
          intro i
          unfold matrixMulVector
          apply memLp_finset_sum Finset.univ
          intro a _ha
          exact (hcoord a).const_smul (P alpha (Sum.inl i) a)
        have hprojected_sum :
            MemLp
              (fun ω : Ω =>
                ∑ i : Node,
                  matrixMulVector (Node := Idx) (P alpha) (coord ω)
                    (Sum.inl i)) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro i _hi
          exact hprojected_coord i
        have hprojected_mem :
            MemLp (fun ω : Ω => projectedBoundary ω m) 2 μ := by
          dsimp [projectedBoundary]
          simpa [quadraticRestrictedPrimalAverageOutput, Idx, stepped,
            coord] using
            hprojected_sum.const_smul
              ((nodeCount (Node := Node) : ℝ)⁻¹)
        have hscalar_mem :
            MemLp (fun ω : Ω => scalarBoundary ω m) 2 μ := by
          dsimp [scalarBoundary]
          exact
            quadraticScalarComparisonProcess_memLp_two
              (Node := Node) quad lambda alpha μ oracle hnoise.1
              (m * quad.period)
        have herr_mem :
            MemLp (fun ω : Ω => errSeq ω m) 2 μ := by
          simpa [errSeq] using hprojected_mem.sub hscalar_mem
        exact herr_mem
      have hboundary_err_int :
          ∀ m : ℕ, Integrable (fun ω : Ω => errSeq ω m) μ := by
        intro m
        exact (hboundary_err_memLp m).integrable (by norm_num)
      have hscalar_boundary_int :
          ∀ m : ℕ, Integrable (fun ω : Ω => scalarBoundary ω m) μ := by
        intro m
        have hscalar_mem :
            MemLp (fun ω : Ω => scalarBoundary ω m) 2 μ := by
          dsimp [scalarBoundary]
          exact
            quadraticScalarComparisonProcess_memLp_two
              (Node := Node) quad lambda alpha μ oracle hnoise.1
              (m * quad.period)
        exact hscalar_mem.integrable (by norm_num)
      have hinput_diff_int :
          ∀ m : ℕ, Integrable (fun ω : Ω => inputDiff ω m) μ := by
        intro m
        have hinput_mem :
            MemLp (fun ω : Ω => inputDiff ω m) 2 μ := by
          dsimp [inputDiff]
          exact
            quadratic_restricted_projected_period_input_scalar_block_diff_memLp_two
              (Node := Node) quad lambda i0 P μ oracle hnoise alpha m
        exact hinput_mem.integrable (by norm_num)
      have hinput_diff_zero :
          ∀ m : ℕ, (∫ ω, inputDiff ω m ∂μ) = 0 := by
        intro m
        simpa [inputDiff] using hprojected_input_scalar_diff_mean_zero m
      have hscalar_boundary_mean :
          ∀ m : ℕ,
            (∫ ω, scalarBoundary ω m ∂μ) =
              quad.x0 *
                quadraticScalarPeriodMultiplier
                  (Node := Node) quad lambda alpha ^ m := by
        intro m
        simpa [scalarBoundary] using _hscalar_block_mean m
      have _hboundary_mean_recursion :
          ∀ m : ℕ,
            (∫ ω, errSeq ω (m + 1) ∂μ) =
              gamma alpha * (∫ ω, errSeq ω m ∂μ) +
                (gamma alpha -
                    quadraticScalarPeriodMultiplier (Node := Node)
                      quad lambda alpha) *
                  (quad.x0 *
                    quadraticScalarPeriodMultiplier
                      (Node := Node) quad lambda alpha ^ m) :=
        scalar_ar_error_integral_recursion_of_input_mean_zero
          (μ := μ)
          (gamma := gamma alpha)
          (Gamma := quadraticScalarPeriodMultiplier (Node := Node)
            quad lambda alpha)
          (x0 := quad.x0)
          (err := errSeq) (scalar := scalarBoundary)
          (inputDiff := inputDiff) hboundary_err_rec hboundary_err_int
          hscalar_boundary_int hinput_diff_int hinput_diff_zero
          hscalar_boundary_mean
      let Gamma : ℝ :=
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
      have hgamma_contract_data :=
        hgamma_contract_point alpha halpha_pos halpha_le_gamma_contract
      have hGamma_nonneg : 0 ≤ Gamma := by
        simpa [Gamma] using hgamma_contract_data.1
      have hGamma_le_one : Gamma ≤ 1 := by
        have hle := hgamma_contract_data.2.1
        have hdrop : 1 - cGammaContract * alpha ≤ 1 := by
          have hprod_nonneg : 0 ≤ cGammaContract * alpha :=
            mul_nonneg hcGammaContract_pos.le halpha_pos.le
          linarith
        exact le_trans (by simpa [Gamma] using hle) hdrop
      have hGamma_abs_pow_le_one :
          ∀ m : ℕ, |Gamma ^ m| ≤ 1 := by
        intro m
        have hpow_nonneg : 0 ≤ Gamma ^ m :=
          pow_nonneg hGamma_nonneg m
        have hpow_le_one : Gamma ^ m ≤ 1 :=
          pow_le_one₀ hGamma_nonneg hGamma_le_one
        simpa [abs_of_nonneg hpow_nonneg] using hpow_le_one
      have hgamma_alpha_nonneg : 0 ≤ gamma alpha :=
        hgamma_contract_data.2.2.2.1
      have hgamma_alpha_le_one : gamma alpha ≤ 1 := by
        have hle := hgamma_contract_data.2.2.2.2.1
        have hdrop : 1 - cGammaContract * alpha ≤ 1 := by
          have hprod_nonneg : 0 ≤ cGammaContract * alpha :=
            mul_nonneg hcGammaContract_pos.le halpha_pos.le
          linarith
        exact le_trans hle hdrop
      have hcoeff :
          |gamma alpha - Gamma| ≤ Cmul * alpha ^ 2 := by
        simpa [Gamma] using hgamma_contract_data.2.2.1
      have hcoeff_nonneg : 0 ≤ Cmul * alpha ^ 2 :=
        mul_nonneg hCmul_pos.le (sq_nonneg alpha)
      let boundaryMeanErr : ℕ → ℝ := fun m =>
        ∫ ω, errSeq ω m ∂μ
      have hboundary_mean_rec :
          ∀ m : ℕ,
            boundaryMeanErr (m + 1) =
              gamma alpha * boundaryMeanErr m +
                (gamma alpha - Gamma) * (quad.x0 * Gamma ^ m) := by
        intro m
        simpa [boundaryMeanErr, Gamma] using
          _hboundary_mean_recursion m
      have hboundary_mean_error_linear_bound :
          |∫ ω, errSeq ω k ∂μ| ≤
            |∫ ω, errSeq ω 0 ∂μ| +
              (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) := by
        simpa [boundaryMeanErr] using
          scalar_ar_mean_error_abs_le_initial_add_linear_forcing
            (gamma := gamma alpha) (Gamma := Gamma) (x0 := quad.x0)
            (Cmul := Cmul) (alpha := alpha)
            hgamma_alpha_nonneg hgamma_alpha_le_one
            hGamma_abs_pow_le_one hcoeff hcoeff_nonneg
            boundaryMeanErr hboundary_mean_rec k
      have _hboundary_mean_error_linear_bound :=
        hboundary_mean_error_linear_bound
      have hinit_sq_int :
          Integrable (fun ω : Ω => errSeq ω 0 ^ 2) μ := by
        have hraw :
            Integrable (fun ω : Ω => ‖errSeq ω 0‖ ^ 2) μ :=
          (memLp_two_iff_integrable_sq_norm
            (hboundary_err_memLp 0).aestronglyMeasurable).1
            (hboundary_err_memLp 0)
        simpa [Real.norm_eq_abs, sq_abs] using hraw
      have hinit_sq_bound :
          (∫ ω, errSeq ω 0 ^ 2 ∂μ) ≤ Cinit * alpha ^ 2 := by
        simpa [errSeq, projectedBoundary, scalarBoundary, sq_abs] using
          _hinitial_error_alpha
      have hCinit_alpha_nonneg : 0 ≤ Cinit * alpha ^ 2 :=
        mul_nonneg hCinit_nonneg (sq_nonneg alpha)
      have hinit_mean_abs_sqrt :
          |∫ ω, errSeq ω 0 ∂μ| ≤ Real.sqrt (Cinit * alpha ^ 2) :=
        abs_integral_le_sqrt_of_sq_integral_le
          (μ := μ) (Z := fun ω : Ω => errSeq ω 0)
          (hboundary_err_memLp 0).aestronglyMeasurable hinit_sq_int
          hCinit_alpha_nonneg hinit_sq_bound
      have hsqrt_alpha :
          Real.sqrt (Cinit * alpha ^ 2) = Real.sqrt Cinit * alpha := by
        rw [Real.sqrt_mul hCinit_nonneg]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos halpha_pos]
      have hinit_mean_abs :
          |∫ ω, errSeq ω 0 ∂μ| ≤ Real.sqrt Cinit * alpha := by
        simpa [hsqrt_alpha] using hinit_mean_abs_sqrt
      have hscaled_k : alpha * (k : ℝ) ≤ M := by
        have hkT_real : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hk_le_T
        calc
          alpha * (k : ℝ) ≤ alpha * (T : ℝ) :=
            mul_le_mul_of_nonneg_left hkT_real halpha_pos.le
          _ ≤ M := hscaled
      have hboundary_err_abs :
          |∫ ω, errSeq ω k ∂μ| ≤
            (Real.sqrt Cinit + M * Cmul * |quad.x0|) * alpha := by
        have hforcing_le :
            (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) ≤
              M * Cmul * |quad.x0| * alpha := by
          have hnonneg : 0 ≤ Cmul * alpha * |quad.x0| := by
            positivity
          have hscaled_k' : (k : ℝ) * alpha ≤ M := by
            simpa [mul_comm] using hscaled_k
          calc
            (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) =
                ((k : ℝ) * alpha) * (Cmul * alpha * |quad.x0|) := by
                ring
            _ ≤ M * (Cmul * alpha * |quad.x0|) :=
                mul_le_mul_of_nonneg_right hscaled_k' hnonneg
            _ = M * Cmul * |quad.x0| * alpha := by ring
        calc
          |∫ ω, errSeq ω k ∂μ| ≤
              |∫ ω, errSeq ω 0 ∂μ| +
                (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) :=
            hboundary_mean_error_linear_bound
          _ ≤ Real.sqrt Cinit * alpha +
                M * Cmul * |quad.x0| * alpha := by
              exact add_le_add hinit_mean_abs hforcing_le
          _ = (Real.sqrt Cinit + M * Cmul * |quad.x0|) * alpha := by
              ring
      have hpow_diff :
          |Gamma ^ k - gamma alpha ^ k| ≤
            (k : ℝ) * (Cmul * alpha ^ 2) := by
        have hcoeff' : |Gamma - gamma alpha| ≤ Cmul * alpha ^ 2 := by
          simpa [abs_sub_comm, Gamma] using hcoeff
        calc
          |Gamma ^ k - gamma alpha ^ k| ≤
              (k : ℝ) * |Gamma - gamma alpha| :=
            real_abs_pow_sub_pow_le_nat_mul_abs_sub_of_nonneg_le_one
              hGamma_nonneg hGamma_le_one hgamma_alpha_nonneg
              hgamma_alpha_le_one k
          _ ≤ (k : ℝ) * (Cmul * alpha ^ 2) :=
              mul_le_mul_of_nonneg_left hcoeff' (Nat.cast_nonneg k)
      have hscalar_power_close :
          |quad.x0 * Gamma ^ k - target| ≤
            (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) := by
        calc
          |quad.x0 * Gamma ^ k - target| =
              |quad.x0| * |Gamma ^ k - gamma alpha ^ k| := by
                dsimp [target]
                rw [← mul_sub, abs_mul]
          _ ≤ |quad.x0| * ((k : ℝ) * (Cmul * alpha ^ 2)) :=
              mul_le_mul_of_nonneg_left hpow_diff (abs_nonneg quad.x0)
          _ = (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) := by ring
      have hprojected_mean_eq :
          (∫ ω, projectedBoundary ω k ∂μ) =
            (∫ ω, errSeq ω k ∂μ) +
              (∫ ω, scalarBoundary ω k ∂μ) := by
        calc
          (∫ ω, projectedBoundary ω k ∂μ) =
              ∫ ω, errSeq ω k + scalarBoundary ω k ∂μ := by
                congr with ω
                dsimp [errSeq]
                ring
          _ =
              (∫ ω, errSeq ω k ∂μ) +
                (∫ ω, scalarBoundary ω k ∂μ) := by
                rw [MeasureTheory.integral_add
                  (hboundary_err_int k) (hscalar_boundary_int k)]
      have hprojected_boundary_close :
          |(∫ ω, projectedBoundary ω k ∂μ) - target| ≤
            |∫ ω, errSeq ω k ∂μ| +
              |quad.x0 * Gamma ^ k - target| := by
        calc
          |(∫ ω, projectedBoundary ω k ∂μ) - target| =
              |(∫ ω, errSeq ω k ∂μ) +
                (quad.x0 * Gamma ^ k - target)| := by
                rw [hprojected_mean_eq, hscalar_boundary_mean k]
                congr 1
                simp [Gamma]
                ring
          _ ≤ |∫ ω, errSeq ω k ∂μ| +
                |quad.x0 * Gamma ^ k - target| :=
              abs_add_le _ _
      have hprojected_close_linear :
          |(∫ ω, projectedBoundary ω k ∂μ) - target| ≤
            (Real.sqrt Cinit + 2 * M * Cmul * |quad.x0|) * alpha := by
        have hforcing_le :
            (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) ≤
              M * Cmul * |quad.x0| * alpha := by
          have hnonneg : 0 ≤ Cmul * alpha * |quad.x0| := by
            positivity
          have hscaled_k' : (k : ℝ) * alpha ≤ M := by
            simpa [mul_comm] using hscaled_k
          calc
            (k : ℝ) * (Cmul * alpha ^ 2 * |quad.x0|) =
                ((k : ℝ) * alpha) * (Cmul * alpha * |quad.x0|) := by
                ring
            _ ≤ M * (Cmul * alpha * |quad.x0|) :=
                mul_le_mul_of_nonneg_right hscaled_k' hnonneg
            _ = M * Cmul * |quad.x0| * alpha := by ring
        calc
          |(∫ ω, projectedBoundary ω k ∂μ) - target| ≤
              |∫ ω, errSeq ω k ∂μ| +
                |quad.x0 * Gamma ^ k - target| :=
            hprojected_boundary_close
          _ ≤
              (Real.sqrt Cinit + M * Cmul * |quad.x0|) * alpha +
                M * Cmul * |quad.x0| * alpha := by
              exact add_le_add hboundary_err_abs
                (le_trans hscalar_power_close hforcing_le)
          _ = (Real.sqrt Cinit + 2 * M * Cmul * |quad.x0|) * alpha := by
              ring
      let Sabsorb : ℝ :=
        Real.sqrt Cinit + (M + 1) * Cmul * |quad.x0| + 1
      have hSabsorb_pos : 0 < Sabsorb := by
        dsimp [Sabsorb]
        positivity
      have halpha_absorb_bound :
          alpha * Sabsorb ≤ |quad.x0| * cgam / 16 := by
        have hle_div :
            alpha ≤
              (|quad.x0| * cgam) / (16 * Sabsorb) := by
          simpa [alphaAbsorb, Sabsorb] using
            le_trans halpha_le_absorb (min_le_right _ _)
        calc
          alpha * Sabsorb ≤
              ((|quad.x0| * cgam) / (16 * Sabsorb)) * Sabsorb :=
            mul_le_mul_of_nonneg_right hle_div hSabsorb_pos.le
          _ = |quad.x0| * cgam / 16 := by
            field_simp [ne_of_gt hSabsorb_pos]
      have hprojected_close_floor :
          |(∫ ω, projectedBoundary ω k ∂μ) - target| ≤
            |quad.x0| * cgam / 2 := by
        have hlinear_le_absorb :
            (Real.sqrt Cinit + 2 * M * Cmul * |quad.x0|) * alpha ≤
              8 * (alpha * Sabsorb) := by
          have hterm_nonneg : 0 ≤ Cmul * |quad.x0| := by positivity
          have hM_nonneg' : 0 ≤ M := hM_nonneg
          have hcoeff_le :
              Real.sqrt Cinit + 2 * M * (Cmul * |quad.x0|) ≤
                8 * Sabsorb := by
            dsimp [Sabsorb]
            nlinarith [Real.sqrt_nonneg Cinit, hterm_nonneg,
              hM_nonneg']
          calc
            (Real.sqrt Cinit + 2 * M * Cmul * |quad.x0|) * alpha =
                (Real.sqrt Cinit + 2 * M * (Cmul * |quad.x0|)) * alpha := by
                ring
            _ ≤ (8 * Sabsorb) * alpha :=
                mul_le_mul_of_nonneg_right hcoeff_le halpha_pos.le
            _ = 8 * (alpha * Sabsorb) := by ring
        calc
          |(∫ ω, projectedBoundary ω k ∂μ) - target| ≤
              (Real.sqrt Cinit + 2 * M * Cmul * |quad.x0|) * alpha :=
            hprojected_close_linear
          _ ≤ 8 * (alpha * Sabsorb) := hlinear_le_absorb
          _ ≤ 8 * (|quad.x0| * cgam / 16) :=
              mul_le_mul_of_nonneg_left halpha_absorb_bound (by norm_num)
          _ = |quad.x0| * cgam / 2 := by ring
      have hraw_mean_transport :
          |(∫ ω,
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t ∂μ) -
            (∫ ω, projectedBoundary ω k ∂μ)| ≤
              |quad.x0| * cgam / 4 := by
        let actualAt : Ω → ℝ := fun ω =>
          (quad.withStepsize alpha).averageIterate (oracle.noise ω) t
        let projectedAt : Ω → ℝ := fun ω => projectedBoundary ω k
        have hactual_mem :
            MemLp actualAt 2 μ := by
          let stepped := quad.withStepsize alpha
          have hstepped_oracle :
              stepped.StochasticOracleAssumptions μ oracle := by
            simpa [stepped, StochasticOracleAssumptions, withStepsize]
              using hnoise.1
          have hgenerated :=
            stepped.generated_pushpull_coordinate_memLp μ oracle
              hstepped_oracle t
          have hsum :
              MemLp
                (fun ω : Ω =>
                  ∑ i : Node,
                    stepped.primalState (oracle.noise ω) t i) 2 μ := by
            apply memLp_finset_sum Finset.univ
            intro i _hi
            exact hgenerated.1 i
          change
            MemLp
              (fun ω : Ω =>
                (quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) t) 2 μ
          simpa [stepped, averageIterate, arithmeticAverage] using
            hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
        have hprojected_mem :
            MemLp projectedAt 2 μ := by
          have hscalar_mem :
              MemLp (fun ω : Ω => scalarBoundary ω k) 2 μ := by
            dsimp [scalarBoundary]
            exact
              quadraticScalarComparisonProcess_memLp_two
                (Node := Node) quad lambda alpha μ oracle hnoise.1
                (k * quad.period)
          have hsum_mem :
              MemLp (fun ω : Ω => errSeq ω k + scalarBoundary ω k) 2 μ :=
            (hboundary_err_memLp k).add hscalar_mem
          simpa [projectedAt, errSeq, sub_eq_add_neg, add_assoc] using hsum_mem
        have hdiff_mem :
            MemLp (fun ω : Ω => actualAt ω - projectedAt ω) 2 μ :=
          hactual_mem.sub hprojected_mem
        have hactual_int : Integrable actualAt μ :=
          hactual_mem.integrable (by norm_num)
        have hprojected_int : Integrable projectedAt μ :=
          hprojected_mem.integrable (by norm_num)
        have hdiff_sq_int :
            Integrable (fun ω : Ω =>
              (actualAt ω - projectedAt ω) ^ 2) μ := by
          have hraw :
              Integrable (fun ω : Ω =>
                ‖actualAt ω - projectedAt ω‖ ^ 2) μ :=
            (memLp_two_iff_integrable_sq_norm
              hdiff_mem.aestronglyMeasurable).1 hdiff_mem
          simpa [Real.norm_eq_abs, sq_abs] using hraw
        have legacy_sq_transport_obligation :
            (∫ ω, (actualAt ω - projectedAt ω) ^ 2 ∂μ) ≤
              (|quad.x0| * cgam / 4) ^ 2 := by
          /- Remaining exact C.3 square-transport leaf.

          The mean endpoint is now compiled below.  The only source step left is
          the single-time square-integral raw transport bound from the actual
          arithmetic average to the projected block-boundary slow coordinate,
          using within-period propagation and stable-output domination. -/
          proof omitted from the noncurrent route-history note
        have hbudget_nonneg :
            0 ≤ (|quad.x0| * cgam / 4) ^ 2 := sq_nonneg _
        have htransport_sqrt :
            |(∫ ω, actualAt ω ∂μ) - (∫ ω, projectedAt ω ∂μ)| ≤
              Real.sqrt ((|quad.x0| * cgam / 4) ^ 2) :=
          abs_integral_sub_integral_le_sqrt_of_sq_integral_le
            (μ := μ) actualAt projectedAt hactual_int hprojected_int
            hdiff_mem.aestronglyMeasurable hdiff_sq_int hbudget_nonneg
            legacy_sq_transport_obligation
        have hsqrt_budget :
            Real.sqrt ((|quad.x0| * cgam / 4) ^ 2) =
              |quad.x0| * cgam / 4 := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg
            (div_nonneg (mul_nonneg (abs_nonneg quad.x0) hcgam_pos.le)
              (by norm_num))
        simpa [actualAt, projectedAt, hsqrt_budget] using htransport_sqrt
      calc
        |(∫ ω,
            (quad.withStepsize alpha).averageIterate
              (oracle.noise ω) t ∂μ) - target| ≤
            |(∫ ω,
                (quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) t ∂μ) -
              (∫ ω, projectedBoundary ω k ∂μ)| +
              |(∫ ω, projectedBoundary ω k ∂μ) - target| :=
          by
            have htri :=
              abs_add_le
                ((∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ) -
                    (∫ ω, projectedBoundary ω k ∂μ))
                ((∫ ω, projectedBoundary ω k ∂μ) - target)
            have hsum :
                ((∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ) -
                    (∫ ω, projectedBoundary ω k ∂μ)) +
                  ((∫ ω, projectedBoundary ω k ∂μ) - target) =
                (∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ) - target := by
              ring
            simpa [hsum] using htri
        _ ≤ |quad.x0| * cgam / 4 + |quad.x0| * cgam / 2 :=
            add_le_add hraw_mean_transport hprojected_close_floor
        _ = err := by
            dsimp [err, cmean]
            ring
    exact
      abs_integral_lower_of_close_to_deterministic_signal
        (μ := μ)
        (actual := fun ω : Ω =>
          (quad.withStepsize alpha).averageIterate
            (oracle.noise ω) t)
        (target := target) (c := cmean) (err := err)
        hmean_close_to_restricted_slow hbudget

/-- Appendix C.3 step 3 source supplier.

This is the source-granularity slow-mode persistence bridge requested by the
Phase 2b planner: it exposes the positive mean-square lower bound that comes
from the restricted spectral splitting, the scalar multiplier squeeze, the
nonzero initial slow coefficient, stable-transient domination, and mean-zero
noise.  The downstream stationarity theorem consumes only this supplier and
the proved Jensen endpoint above, so the remaining proof placeholder is the exact
spectral mean-persistence leaf rather than the whole lower-bound theorem. -/
theorem legacy_noncurrent_c3_mean_persistence_floor_of_upper_half_route
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              lambda ^ 2 *
                |∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ| ^ 2) := by
  classical
  have hx0_sq :=
    homogeneousQuadratic_x0_sq_eq_twoDelta_div_lambda
      (Node := Node) quad lambda hquad
  have hx0_sq_pos : 0 < quad.x0 ^ 2 := by
    have hright_pos : 0 < 2 * quad.Delta / lambda := by
      exact div_pos (mul_pos (by norm_num) quad.Delta_positive) hquad.1
    simpa [hx0_sq] using hright_pos
  have hx0_ne : quad.x0 ≠ 0 := by
    intro hx0_zero
    rw [hx0_zero] at hx0_sq_pos
    norm_num at hx0_sq_pos
  have hx0_abs_pos : 0 < |quad.x0| := abs_pos.mpr hx0_ne
  rcases
      quadraticScalarPeriodMultiplier_smallAlpha_squeeze
        (Node := Node) quad lambda hquad with
    ⟨alphaS, c1, c2, halphaS_pos, hc1_pos, hc2_pos, hc12, hsqueeze⟩
  let i0 : Node := Classical.choice (inferInstance : Nonempty Node)
  obtain ⟨r0_restricted, right_restricted, left_restricted,
      alpha_restricted, theta_restricted, K_restricted,
      gamma_restricted, P_restricted, F_restricted,
      hr0_restricted_nonneg, halpha_restricted_le_one,
      hP0_restricted, hright_restricted_eq, hright_restricted_top,
      hleft_restricted_top, hleft_restricted_bottom,
      hsplitting_restricted⟩ :=
    quadraticRestrictedPeriodMatrix_periodic_spectral_splitting
      (Node := Node) quad lambda i0 hquad
  have hstable_impulse :=
    quadratic_restricted_stable_output_impulse_geometric_bound
      (Node := Node) quad lambda i0
      r0_restricted alpha_restricted theta_restricted K_restricted
      right_restricted left_restricted gamma_restricted
      P_restricted F_restricted hquad hP0_restricted
      hright_restricted_top hleft_restricted_top hleft_restricted_bottom
      hr0_restricted_nonneg hsplitting_restricted
  have hmultO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          gamma_restricted alpha -
            quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
        (fun alpha : ℝ => alpha ^ 2) :=
    quadratic_restricted_slow_multiplier_matches_scalar_period_multiplier_isBigO_sq
      (Node := Node) quad lambda i0 r0_restricted alpha_restricted
      theta_restricted K_restricted right_restricted left_restricted
      gamma_restricted P_restricted F_restricted hsplitting_restricted
      hP0_restricted hright_restricted_eq hright_restricted_top
      hleft_restricted_top hleft_restricted_bottom
  obtain ⟨alphaGamma, cGamma, Cmul, halphaGamma_pos, hcGamma_pos,
      hCmul_pos, hgamma_contract⟩ :=
    restricted_gamma_smallAlpha_contract_from_scalar_squeeze
      (Node := Node) quad lambda i0 gamma_restricted hquad hmultO
  obtain ⟨alphaGammaLower, cGammaLower, halphaGammaLower_pos,
      hcGammaLower_pos, hgamma_lower⟩ :=
    restricted_gamma_smallAlpha_lower_from_scalar_squeeze
      (Node := Node) quad lambda i0 gamma_restricted hquad hmultO
  have hgamma_contract_pkg :
      ∃ alphaGamma cGamma Cmul : ℝ,
        0 < alphaGamma ∧ 0 < cGamma ∧ 0 < Cmul ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGamma →
            let Gamma :=
              quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
            0 ≤ Gamma ∧ Gamma ≤ 1 - cGamma * alpha ∧
              |gamma_restricted alpha - Gamma| ≤ Cmul * alpha ^ 2 ∧
                0 ≤ gamma_restricted alpha ∧
                  gamma_restricted alpha ≤ 1 - cGamma * alpha ∧
                    0 < 1 - cGamma * alpha :=
    ⟨alphaGamma, cGamma, Cmul, halphaGamma_pos, hcGamma_pos,
      hCmul_pos, hgamma_contract⟩
  have hgamma_lower_pkg :
      ∃ alphaGammaLower cGammaLower : ℝ,
        0 < alphaGammaLower ∧ 0 < cGammaLower ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGammaLower →
            0 ≤ gamma_restricted alpha ∧
              1 - cGammaLower * alpha ≤ gamma_restricted alpha :=
    ⟨alphaGammaLower, cGammaLower, halphaGammaLower_pos,
      hcGammaLower_pos, hgamma_lower⟩
  rcases
      legacy_noncurrent_c3_all_raw_upper_half_mean_abs_lower
        (Node := Node) quad lambda i0
        r0_restricted alpha_restricted theta_restricted K_restricted
        right_restricted left_restricted gamma_restricted
        P_restricted F_restricted μ oracle hquad hnoise
        hP0_restricted hright_restricted_eq hright_restricted_top
        hleft_restricted_top hleft_restricted_bottom
        hr0_restricted_nonneg hsplitting_restricted
        hgamma_contract_pkg hgamma_lower_pkg hx0_abs_pos hstable_impulse
        M hM_nonneg with
    ⟨cmean, alphaTail, Ttail, hcmean_pos, halphaTail_pos, htail_mean⟩
  let c : ℝ := lambda ^ 2 * cmean ^ 2 / 4
  let T0 : ℕ := max Ttail 2
  have hc_pos : 0 < c := by
    have hlambda_sq_pos : 0 < lambda ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hquad.1)
    have hcmean_sq_pos : 0 < cmean ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hcmean_pos)
    dsimp [c]
    positivity
  refine ⟨c, alphaTail, T0, hc_pos, halphaTail_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  have hTtail : Ttail ≤ T := le_trans (Nat.le_max_left Ttail 2) hT
  have hT_two : 2 ≤ T := le_trans (Nat.le_max_right Ttail 2) hT
  have htail_for_T :
      ∀ t : ℕ, T / 2 ≤ t → t < T →
        cmean ≤
          |∫ ω,
            (quad.withStepsize alpha).averageIterate
              (oracle.noise ω) t ∂μ| :=
    htail_mean T alpha hTtail halpha_nonneg halpha_le hscaled
  simpa [c] using
    average_iterate_mean_square_floor_of_upper_half_abs_lower
      (signal := fun t : ℕ =>
        ∫ ω,
          (quad.withStepsize alpha).averageIterate
            (oracle.noise ω) t ∂μ)
      (lambda := lambda) (cmean := cmean) (T := T)
      hT_two hcmean_pos.le htail_for_T

-/

/-- Appendix C.3 block-boundary slow-mode persistence source leaf.

This is the active source-boundary proof obligation after retiring the
all-raw upper-half route.  Its hypotheses are the C.1 restricted spectral
splitting, slow multiplier persistence, initial slow-coordinate nonvanishing,
stable-output impulse control, and iid mean-zero noise; its conclusion is only
the block-boundary mean lower bound needed for the positive-density endpoint. -/
theorem quadratic_restricted_block_boundary_mean_abs_lower_of_source_components
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alphaRestricted theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} =>
        right i * left j))
    (hright_eq :
      right =
        quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0)
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hr0_nonneg : 0 ≤ r0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alphaRestricted theta K right left gamma P F)
    (hgamma_contract :
      ∃ alphaGamma cGamma Cmul : ℝ,
        0 < alphaGamma ∧ 0 < cGamma ∧ 0 < Cmul ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGamma →
            let Gamma :=
              quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
            0 ≤ Gamma ∧ Gamma ≤ 1 - cGamma * alpha ∧
              |gamma alpha - Gamma| ≤ Cmul * alpha ^ 2 ∧
                0 ≤ gamma alpha ∧ gamma alpha ≤ 1 - cGamma * alpha ∧
                  0 < 1 - cGamma * alpha)
    (hgamma_lower :
      ∃ alphaGammaLower cGammaLower : ℝ,
        0 < alphaGammaLower ∧ 0 < cGammaLower ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGammaLower →
            0 ≤ gamma alpha ∧ 1 - cGammaLower * alpha ≤ gamma alpha)
    (hx0_abs_pos : 0 < |quad.x0|)
    (hstable_impulse :
      ∃ C theta1 alphaImpulse : ℝ,
        0 ≤ C ∧ theta < theta1 ∧ theta1 < 1 ∧
          0 < alphaImpulse ∧ alphaImpulse ≤ alphaRestricted ∧
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
                            (Node := Node) quad noise j)))
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ cmean alpha0 T0, 0 < cmean ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          ∀ k : ℕ, k < T / quad.period →
            cmean ≤
              |∫ ω,
                (quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) (k * quad.period) ∂μ| := by
  classical
  /- Source boundary for Appendix C.3, PDF lines 1700-1716.

  The block-boundary version no longer asks for all raw times.  The remaining
  proof is to combine the restricted slow multiplier lower bound, the
  `x0 + O(alpha)` initial slow coefficient, the `1 + O(alpha)` average output,
  and the stable-output impulse estimate to obtain a uniform lower bound at
  complete-period representatives. -/
  have hprojected_boundary_mean_rec :
      ∀ alpha : ℝ, |alpha| ≤ alphaRestricted →
        ∀ k : ℕ,
          (∫ ω,
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState
                      (oracle.noise ω) (k * quad.period),
                    (quad.withStepsize alpha).trackerErrorZeroSum
                      (oracle.noise ω) (k * quad.period)))) ∂μ) =
            (∫ ω,
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState
                        (oracle.noise ω) 0,
                      (quad.withStepsize alpha).trackerErrorZeroSum
                        (oracle.noise ω) 0))) ∂μ) *
              gamma alpha ^ k := by
    intro alpha halpha_abs k
    exact
      quadratic_restricted_projected_boundary_mean_eq_initial_mul_gamma_pow
        (Node := Node) quad lambda i0 r0 alphaRestricted theta K
        right left gamma P F μ oracle hquad hnoise hsplitting
        alpha halpha_abs k
  have hgamma_power_lower :=
    restricted_gamma_power_lower_of_bounded_scaled_stepsize
      gamma M hM_nonneg hgamma_lower
  have hstable_output_memLp :
      ∀ alpha : ℝ, ∀ k : ℕ,
        MemLp
          (fun ω : Ω =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (quadraticRestrictedStableBoundaryResponse
                (Node := Node) quad lambda i0 P F alpha
                (oracle.noise ω) k)) 2 μ := by
    intro alpha k
    exact
      quadraticRestrictedStableBoundaryResponse_output_memLp_two
        (Node := Node) quad lambda i0 P F μ oracle hnoise alpha k
  obtain ⟨Cstable, alphaStable, hCstable_nonneg, halphaStable_pos,
      halphaStable_le_restricted, hstable_mean_bound⟩ :=
    quadratic_restricted_stable_boundary_output_mean_abs_le_linear_stepsize
      (Node := Node) quad lambda i0 r0 alphaRestricted theta K
      right left gamma P F μ oracle hnoise hr0_nonneg hsplitting
      hstable_impulse hstable_output_memLp
  obtain ⟨alphaInitMean, halphaInitMean_pos,
      halphaInitMean_le_restricted, hinit_mean_lower⟩ :=
    quadratic_restricted_projected_initial_boundary_mean_abs_lower
      (Node := Node) quad lambda i0 r0 alphaRestricted theta K
      right left gamma P F hP0 hright_top hleft_top hleft_bottom
      hsplitting μ oracle hx0_abs_pos
  have hrestricted_period_boundary_recursion :
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
              (Node := Node) quad lambda alpha i0 noise k := by
    intro alpha noise k
    exact
      quadratic_restricted_period_inhomogeneous_recursion
        (Node := Node) quad lambda alpha i0 hquad noise k
  rcases hgamma_power_lower with
    ⟨alphaGammaPower, cgam, halphaGammaPower_pos, hcgam_pos,
      hcgam_le_one, hgamma_power_lower_point⟩
  let B : ℝ := |quad.x0| * cgam
  let cmean : ℝ := B / 4
  let alphaAbsorb : ℝ := (B / 4) / (Cstable + 1)
  let alpha0 : ℝ :=
    min alphaGammaPower
      (min alphaStable (min alphaInitMean alphaAbsorb))
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hB_nonneg : 0 ≤ B := le_of_lt hB_pos
  have hcmean_pos : 0 < cmean := by
    dsimp [cmean]
    positivity
  have hden_pos : 0 < Cstable + 1 := by
    linarith
  have halphaAbsorb_pos : 0 < alphaAbsorb := by
    dsimp [alphaAbsorb]
    exact div_pos hcmean_pos hden_pos
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaGammaPower_pos
      (lt_min halphaStable_pos
        (lt_min halphaInitMean_pos halphaAbsorb_pos))
  refine ⟨cmean, alpha0, 0, hcmean_pos, halpha0_pos, ?_⟩
  intro T alpha _hT halpha_nonneg halpha_le hscaled k hk
  rcases halpha_nonneg.eq_or_lt with halpha_zero | halpha_pos
  · subst alpha
    have hmean_eq :
        (∫ ω,
          (quad.withStepsize 0).averageIterate
            (oracle.noise ω) (k * quad.period) ∂μ) = quad.x0 := by
      calc
        (∫ ω,
          (quad.withStepsize 0).averageIterate
            (oracle.noise ω) (k * quad.period) ∂μ) =
            ∫ _ω : Ω, quad.x0 ∂μ := by
              congr with ω
              exact homogeneous_zero_stepsize_averageIterate_eq_x0
                (Node := Node) quad (oracle.noise ω) (k * quad.period)
        _ = quad.x0 := by simp
    have hmean_le_x0 : cmean ≤ |quad.x0| := by
      dsimp [cmean, B]
      nlinarith [le_of_lt hx0_abs_pos, hcgam_pos.le, hcgam_le_one]
    simpa [hmean_eq] using hmean_le_x0
  · have halpha_le_gamma_power : alpha ≤ alphaGammaPower :=
      le_trans halpha_le (min_le_left _ _)
    have halpha_le_stable : alpha ≤ alphaStable :=
      le_trans halpha_le
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have halpha_le_init : alpha ≤ alphaInitMean :=
      le_trans halpha_le
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
    have halpha_le_absorb : alpha ≤ alphaAbsorb :=
      le_trans halpha_le
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (min_le_right _ _)))
    have halpha_le_restricted : alpha ≤ alphaRestricted :=
      le_trans halpha_le_stable halphaStable_le_restricted
    have halpha_abs : |alpha| ≤ alphaRestricted := by
      simpa [abs_of_pos halpha_pos] using halpha_le_restricted
    have hk_le_T : k ≤ T :=
      le_trans (Nat.le_of_lt hk) (Nat.div_le_self T quad.period)
    have hgamma_k_lower : cgam ≤ gamma alpha ^ k :=
      hgamma_power_lower_point T alpha k halpha_pos
        halpha_le_gamma_power hscaled hk_le_T
    have hgamma_k_nonneg : 0 ≤ gamma alpha ^ k :=
      le_trans hcgam_pos.le hgamma_k_lower
    let actual : Ω → ℝ := fun ω =>
      (quad.withStepsize alpha).averageIterate
        (oracle.noise ω) (k * quad.period)
    let projected : Ω → ℝ := fun ω =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState
                (oracle.noise ω) (k * quad.period),
              (quad.withStepsize alpha).trackerErrorZeroSum
                (oracle.noise ω) (k * quad.period))))
    let projectedInit : Ω → ℝ := fun ω =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState
                (oracle.noise ω) 0,
              (quad.withStepsize alpha).trackerErrorZeroSum
                (oracle.noise ω) 0)))
    let stable : Ω → ℝ := fun ω =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (quadraticRestrictedStableBoundaryResponse
          (Node := Node) quad lambda i0 P F alpha (oracle.noise ω) k)
    let actualMean : ℝ := ∫ ω, actual ω ∂μ
    let projectedMean : ℝ := ∫ ω, projected ω ∂μ
    let stableMean : ℝ := ∫ ω, stable ω ∂μ
    let initMean : ℝ := ∫ ω, projectedInit ω ∂μ
    have hprojected_rec :
        projectedMean = initMean * gamma alpha ^ k := by
      simpa [projectedMean, projected, initMean, projectedInit] using
        hprojected_boundary_mean_rec alpha halpha_abs k
    have hinit_lower :
        |quad.x0| / 2 ≤ |initMean| := by
      simpa [initMean, projectedInit] using
        hinit_mean_lower alpha halpha_pos halpha_le_init
    have hprojected_lower :
        B / 2 ≤ |projectedMean| := by
      have hmul_lower :
          (|quad.x0| / 2) * cgam ≤ |initMean| * (gamma alpha ^ k) :=
        mul_le_mul hinit_lower hgamma_k_lower hcgam_pos.le
          (abs_nonneg initMean)
      have hproj_abs :
          |projectedMean| = |initMean| * (gamma alpha ^ k) := by
        rw [hprojected_rec, abs_mul, abs_of_nonneg hgamma_k_nonneg]
      calc
        B / 2 = (|quad.x0| / 2) * cgam := by
          dsimp [B]
          ring
        _ ≤ |initMean| * (gamma alpha ^ k) := hmul_lower
        _ = |projectedMean| := hproj_abs.symm
    have hstable_upper :
        |stableMean| ≤ B / 4 := by
      have hstable_raw :
          |stableMean| ≤ Cstable * alpha := by
        simpa [stableMean, stable] using
          hstable_mean_bound alpha halpha_pos halpha_le_stable k
      have hcoef_absorb :
          Cstable * alpha ≤ B / 4 := by
        calc
          Cstable * alpha ≤ (Cstable + 1) * alpha := by
            exact mul_le_mul_of_nonneg_right (by linarith) halpha_nonneg
          _ ≤ (Cstable + 1) * alphaAbsorb := by
            exact mul_le_mul_of_nonneg_left halpha_le_absorb hden_pos.le
          _ = B / 4 := by
            dsimp [alphaAbsorb]
            field_simp [ne_of_gt hden_pos]
      exact le_trans hstable_raw hcoef_absorb
    have hactual_int : Integrable actual μ := by
      let stepped := quad.withStepsize alpha
      have hstepped_oracle :
          stepped.StochasticOracleAssumptions μ oracle := by
        simpa [stepped, StochasticOracleAssumptions, withStepsize] using
          hnoise.1
      have hgenerated :=
        stepped.generated_pushpull_coordinate_memLp μ oracle
          hstepped_oracle (k * quad.period)
      have hsum :
          MemLp
            (fun ω : Ω =>
              ∑ i : Node,
                stepped.primalState (oracle.noise ω)
                  (k * quad.period) i) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro i _hi
        exact hgenerated.1 i
      have havg_mem :
          MemLp (fun ω : Ω => actual ω) 2 μ := by
        simpa [actual, stepped, averageIterate, arithmeticAverage] using
          hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
      exact havg_mem.integrable (by norm_num)
    have hstable_int : Integrable stable μ := by
      exact (hstable_output_memLp alpha k).integrable (by norm_num)
    have hmean_decomp :
        actualMean = projectedMean + stableMean := by
      have hsub_integral :
          actualMean - stableMean = projectedMean := by
        calc
          actualMean - stableMean =
              ∫ ω, actual ω - stable ω ∂μ := by
                exact (MeasureTheory.integral_sub hactual_int hstable_int).symm
          _ = ∫ ω, projected ω ∂μ := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun ω => by
                  simpa [actual, projected, stable] using
                    quadraticRestrictedSlowOutput_eq_projectedBoundary_at_block_start
                      (Node := Node) quad lambda i0 r0 alphaRestricted theta K
                      right left gamma P F hsplitting
                      hrestricted_period_boundary_recursion halpha_abs
                      (oracle.noise ω) k
          _ = projectedMean := by rfl
      dsimp [actualMean, stableMean, projectedMean] at hsub_integral ⊢
      nlinarith
    have hfinal :
        cmean ≤ |actualMean| := by
      dsimp [cmean]
      exact
        scalar_block_boundary_mean_lower_of_projected_lower_and_stable_upper
          hmean_decomp hprojected_lower hstable_upper hB_nonneg
    simpa [actualMean, actual] using hfinal

/-- Appendix C.3 positive-density slow-mode persistence source boundary.

This is the replacement source-facing interface for the bounded
scaled-stepsize slow branch: it asks for persistence on a finite subset of
times with uniformly positive density, covering block-boundary selections
without requiring an all-raw upper-half lower bound. -/
theorem quadratic_restricted_positive_density_mean_abs_lower_of_bounded_scaled_stepsize
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ cmean density alpha0 T0,
      0 < cmean ∧ 0 < density ∧ 0 < alpha0 ∧
        ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
          alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
            ∃ S : Finset ℕ,
              S ⊆ Finset.range T ∧
                density * (T : ℝ) ≤ (S.card : ℝ) ∧
                  ∀ t ∈ S,
                    cmean ≤
                      |∫ ω,
                        (quad.withStepsize alpha).averageIterate
                          (oracle.noise ω) t ∂μ| := by
  classical
  have hx0_sq :=
    homogeneousQuadratic_x0_sq_eq_twoDelta_div_lambda
      (Node := Node) quad lambda hquad
  have hx0_sq_pos : 0 < quad.x0 ^ 2 := by
    have hright_pos : 0 < 2 * quad.Delta / lambda := by
      exact div_pos (mul_pos (by norm_num) quad.Delta_positive) hquad.1
    simpa [hx0_sq] using hright_pos
  have hx0_ne : quad.x0 ≠ 0 := by
    intro hx0_zero
    rw [hx0_zero] at hx0_sq_pos
    norm_num at hx0_sq_pos
  have hx0_abs_pos : 0 < |quad.x0| := abs_pos.mpr hx0_ne
  let i0 : Node := Classical.choice (inferInstance : Nonempty Node)
  obtain ⟨r0_restricted, right_restricted, left_restricted,
      alpha_restricted, theta_restricted, K_restricted,
      gamma_restricted, P_restricted, F_restricted,
      hr0_restricted_nonneg, _halpha_restricted_le_one,
      hP0_restricted, hright_restricted_eq, hright_restricted_top,
      hleft_restricted_top, hleft_restricted_bottom,
      hsplitting_restricted⟩ :=
    quadraticRestrictedPeriodMatrix_periodic_spectral_splitting
      (Node := Node) quad lambda i0 hquad
  have hstable_impulse :=
    quadratic_restricted_stable_output_impulse_geometric_bound
      (Node := Node) quad lambda i0
      r0_restricted alpha_restricted theta_restricted K_restricted
      right_restricted left_restricted gamma_restricted
      P_restricted F_restricted hquad hP0_restricted
      hright_restricted_top hleft_restricted_top hleft_restricted_bottom
      hr0_restricted_nonneg hsplitting_restricted
  have hmultO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          gamma_restricted alpha -
            quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
        (fun alpha : ℝ => alpha ^ 2) :=
    quadratic_restricted_slow_multiplier_matches_scalar_period_multiplier_isBigO_sq
      (Node := Node) quad lambda i0 r0_restricted alpha_restricted
      theta_restricted K_restricted right_restricted left_restricted
      gamma_restricted P_restricted F_restricted hsplitting_restricted
      hP0_restricted hright_restricted_eq hright_restricted_top
      hleft_restricted_top hleft_restricted_bottom
  obtain ⟨alphaGamma, cGamma, Cmul, halphaGamma_pos, hcGamma_pos,
      hCmul_pos, hgamma_contract⟩ :=
    restricted_gamma_smallAlpha_contract_from_scalar_squeeze
      (Node := Node) quad lambda i0 gamma_restricted hquad hmultO
  obtain ⟨alphaGammaLower, cGammaLower, halphaGammaLower_pos,
      hcGammaLower_pos, hgamma_lower⟩ :=
    restricted_gamma_smallAlpha_lower_from_scalar_squeeze
      (Node := Node) quad lambda i0 gamma_restricted hquad hmultO
  have hgamma_contract_pkg :
      ∃ alphaGamma cGamma Cmul : ℝ,
        0 < alphaGamma ∧ 0 < cGamma ∧ 0 < Cmul ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGamma →
            let Gamma :=
              quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
            0 ≤ Gamma ∧ Gamma ≤ 1 - cGamma * alpha ∧
              |gamma_restricted alpha - Gamma| ≤ Cmul * alpha ^ 2 ∧
                0 ≤ gamma_restricted alpha ∧
                  gamma_restricted alpha ≤ 1 - cGamma * alpha ∧
                    0 < 1 - cGamma * alpha :=
    ⟨alphaGamma, cGamma, Cmul, halphaGamma_pos, hcGamma_pos,
      hCmul_pos, hgamma_contract⟩
  have hgamma_lower_pkg :
      ∃ alphaGammaLower cGammaLower : ℝ,
        0 < alphaGammaLower ∧ 0 < cGammaLower ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGammaLower →
            0 ≤ gamma_restricted alpha ∧
              1 - cGammaLower * alpha ≤ gamma_restricted alpha :=
    ⟨alphaGammaLower, cGammaLower, halphaGammaLower_pos,
      hcGammaLower_pos, hgamma_lower⟩
  rcases
      quadratic_restricted_block_boundary_mean_abs_lower_of_source_components
        (Node := Node) quad lambda i0
        r0_restricted alpha_restricted theta_restricted K_restricted
        right_restricted left_restricted gamma_restricted
        P_restricted F_restricted μ oracle hquad hnoise
        hP0_restricted hright_restricted_eq hright_restricted_top
        hleft_restricted_top hleft_restricted_bottom
        hr0_restricted_nonneg hsplitting_restricted
        hgamma_contract_pkg hgamma_lower_pkg hx0_abs_pos hstable_impulse
        M hM_nonneg with
    ⟨cmean, alphaBlock, Tblock, hcmean_pos, halphaBlock_pos, hblock_mean⟩
  let density : ℝ := (1 : ℝ) / (2 * (quad.period : ℝ))
  let T0 : ℕ := max Tblock (2 * quad.period)
  have hdensity_pos : 0 < density := by
    dsimp [density]
    have hperiod_pos : 0 < (quad.period : ℝ) := by
      exact_mod_cast quad.period_pos
    positivity
  refine ⟨cmean, density, alphaBlock, T0,
    hcmean_pos, hdensity_pos, halphaBlock_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  have hTblock : Tblock ≤ T := le_trans (Nat.le_max_left Tblock _) hT
  have hT_period : 2 * quad.period ≤ T :=
    le_trans (Nat.le_max_right Tblock _) hT
  rcases
      block_boundary_positive_density_subset
        quad.period T quad.period_pos hT_period with
    ⟨S, hS_subset, hcard_lower, hS_mem⟩
  refine ⟨S, hS_subset, ?_, ?_⟩
  · simpa [density] using hcard_lower
  · intro t ht
    rcases hS_mem t ht with ⟨k, hk, rfl⟩
    exact hblock_mean T alpha hTblock halpha_nonneg halpha_le hscaled k hk

/-- Appendix C.3 block-boundary/positive-density source supplier.

The only source-specific input is the positive-density absolute mean boundary
above; the finite subset counting endpoint converts it to the averaged
mean-square floor consumed by the stationarity Jensen endpoint. -/
theorem quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              lambda ^ 2 *
                |∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ| ^ 2) := by
  classical
  rcases
      quadratic_restricted_positive_density_mean_abs_lower_of_bounded_scaled_stepsize
        (Node := Node) quad lambda μ oracle hquad hnoise M hM_nonneg with
    ⟨cmean, density, alpha0, Tpd, hcmean_pos, hdensity_pos,
      halpha0_pos, hpd⟩
  let c : ℝ := lambda ^ 2 * cmean ^ 2 * density
  let T0 : ℕ := max Tpd 1
  have hc_pos : 0 < c := by
    have hlambda_sq_pos : 0 < lambda ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hquad.1)
    have hcmean_sq_pos : 0 < cmean ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hcmean_pos)
    dsimp [c]
    positivity
  refine ⟨c, alpha0, T0, hc_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  have hTpd : Tpd ≤ T := le_trans (Nat.le_max_left Tpd 1) hT
  have hT_one : 1 ≤ T := le_trans (Nat.le_max_right Tpd 1) hT
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT_one
  rcases hpd T alpha hTpd halpha_nonneg halpha_le hscaled with
    ⟨S, hS_subset, hcard_lower, hlower⟩
  simpa [c] using
    average_iterate_mean_square_floor_of_positive_density_abs_lower
      (signal := fun t : ℕ =>
        ∫ ω,
          (quad.withStepsize alpha).averageIterate
            (oracle.noise ω) t ∂μ)
      (lambda := lambda) (cmean := cmean) (density := density)
      (T := T) (S := S) hT_pos hcmean_pos.le hdensity_pos.le
      hS_subset hcard_lower hlower

/-- Appendix C.3 step 3 source supplier, migrated to the
block-boundary/positive-density route. -/
theorem quadratic_restricted_mean_persistence_floor_of_bounded_scaled_stepsize
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              lambda ^ 2 *
                |∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ| ^ 2) := by
  exact
    quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize
      (Node := Node) quad lambda μ oracle hquad hnoise M hM_nonneg

/-- Filter-level Appendix C.3 contradiction: a near-minimizer value bounded by
`O(T^{-1/2})` cannot stay in any bounded scaled-stepsize region once that
region has a positive source lower floor for `J_T`. -/
theorem near_minimizer_product_tendsto_atTop_of_upper_and_slow_floor
    (J : ℕ → ℝ → ℝ) (alphaSeq : ℕ → ℝ)
    (hnonneg : ∀ T : ℕ, 1 ≤ T → 0 ≤ alphaSeq T)
    (halpha_tendsto : Filter.Tendsto alphaSeq Filter.atTop (nhds 0))
    (hupper :
      ∃ C T0, 0 ≤ C ∧ ∀ T : ℕ, T0 ≤ T →
        J T (alphaSeq T) ≤ C * (Real.sqrt (T : ℝ))⁻¹)
    (hfloor :
      ∀ M : ℝ, 0 ≤ M →
        ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
          ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
            alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
              c ≤ J T alpha) :
    Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
      Filter.atTop Filter.atTop := by
  rcases hupper with ⟨C, Tupper, _hC_nonneg, hupper_bound⟩
  exact
    parameter_mul_natCast_tendsto_atTop_of_vanishing_upper_and_bounded_region_floor
      J alphaSeq (fun T => C * (Real.sqrt (T : ℝ))⁻¹)
      (Filter.eventually_atTop.2 ⟨1, fun T hT => hnonneg T hT⟩)
      halpha_tendsto
      (by
        simpa using Filter.Tendsto.const_mul C
          ((Real.tendsto_sqrt_atTop.comp
            tendsto_natCast_atTop_atTop).inv_tendsto_atTop))
      (Filter.eventually_atTop.2 ⟨Tupper, fun T hT => hupper_bound T hT⟩)
      hfloor

/-- Appendix C.3 step 3, source-derived slow-mode floor.  If the scaled
stepsize `alpha*T` is bounded while `alpha` is small, the deterministic slow
mode initialized by `x0` persists over a positive fraction of the horizon, so
Jensen gives a positive lower bound on the true stationarity functional. -/
theorem quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_bounded_scaled_stepsize
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hslow : QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
  classical
  rcases
      quadratic_restricted_mean_persistence_floor_of_bounded_scaled_stepsize
        (Node := Node) quad lambda μ oracle hquad hnoise M hM_nonneg with
    ⟨c, alpha0, T0, hc_pos, halpha0_pos, hmean_floor⟩
  refine ⟨c, alpha0, T0, hc_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  exact
    stationarity_functional_floor_of_average_iterate_mean_square
      (Node := Node) quad lambda μ oracle hquad hnoise T alpha c
      (hmean_floor T alpha hT halpha_nonneg halpha_le hscaled)

theorem all_stepsize_near_minimizer_exclusions_and_final_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (_hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hslow : QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle)
    (hscalarExp : QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle)
    (hscalarAsymp :
      QuadraticScalarMomentAsymptoticConsequence (Node := Node)
        quad lambda μ oracle)
    (alphaNearOpt : ℕ → ℝ)
    (hnear_nonneg : ∀ T : ℕ, 1 ≤ T → 0 ≤ alphaNearOpt T)
    (hnear_value : ∀ T : ℕ, 1 ≤ T →
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤
        sInf { value : ℝ |
          ∃ alpha : ℝ, 0 ≤ alpha ∧
            value =
              quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha } +
        (T : ℝ)⁻¹) :
    Filter.Tendsto alphaNearOpt Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun T : ℕ => alphaNearOpt T * (T : ℝ))
        Filter.atTop Filter.atTop ∧
        ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
          1 ≤ T ∧ 0 < alphaNearOpt T ∧
            quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T ≥
                quad.sigma *
                  Real.sqrt (2 * lambda * quad.Delta /
                    (quad.effectiveNodeCount * (T : ℝ))) := by
  have halpha_tendsto :
      Filter.Tendsto alphaNearOpt Filter.atTop (nhds 0) := by
    have hupper :=
      near_minimizer_value_upper_inv_sqrt_of_scalar_expansion
        (Node := Node) quad lambda μ oracle _hquad _hnoise hslow
        hscalarExp alphaNearOpt hnear_value
    have hfloor :=
      quadraticLowerBoundStationarityFunctional_fresh_noise_floor
        (Node := Node) quad lambda μ oracle _hquad _hnoise
    have hlt_delta :=
      near_minimizer_eventually_lt_delta_of_upper_and_fresh_floor
        (Node := Node) quad lambda μ oracle _hquad _hnoise
        alphaNearOpt hnear_nonneg hupper hfloor
    exact tendsto_zero_of_eventually_nonneg_and_lt_delta
      alphaNearOpt hnear_nonneg hlt_delta
  have hprod_tendsto :
      Filter.Tendsto (fun T : ℕ => alphaNearOpt T * (T : ℝ))
        Filter.atTop Filter.atTop := by
    have hupper :=
      near_minimizer_value_upper_inv_sqrt_of_scalar_expansion
        (Node := Node) quad lambda μ oracle _hquad _hnoise hslow
        hscalarExp alphaNearOpt hnear_value
    exact
      near_minimizer_product_tendsto_atTop_of_upper_and_slow_floor
        (J := fun T alpha =>
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha)
        alphaNearOpt hnear_nonneg halpha_tendsto hupper
        (quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_bounded_scaled_stepsize
          (Node := Node) quad lambda μ oracle _hquad _hnoise hslow)
  exact ⟨halpha_tendsto, hprod_tendsto,
    near_minimizer_eventual_amgm_bound_of_product_tendsto_atTop
      (Node := Node) quad lambda μ oracle _hquad _hnoise
      alphaNearOpt hnear_nonneg hprod_tendsto⟩

/-- Appendix C.3: all-stepsize trichotomy used to exclude non-balancing
constant stepsizes in the quadratic lower-bound proof. -/
theorem AllStepsizeTrichotomyForQuadraticLowerBound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (_hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (_hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    AllStepsizeTrichotomyStatement (Node := Node) quad lambda μ oracle := by
  classical
  unfold AllStepsizeTrichotomyStatement
  let alphaStar : ℕ → ℝ := fun T =>
    Real.sqrt (2 * quad.Delta /
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment * (T : ℝ)))
  have hslow :
      QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle :=
    QuadraticSlowComparisonDetails
      (Node := Node) quad lambda μ oracle _hquad _hnoise
  have hscalarPair :
      QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle ∧
        QuadraticScalarMomentAsymptoticConsequence (Node := Node)
          quad lambda μ oracle :=
    QuadraticPeriodicScalarMomentExpansion
      (Node := Node) quad lambda μ oracle _hquad _hnoise
  rcases hscalarPair with ⟨hscalarExp, hscalarAsymp⟩
  rcases exists_quadratic_lower_bound_near_sInf_sequence
      (Node := Node) quad μ oracle with
    ⟨alphaNearOpt, hnear_nonneg, hnear_value⟩
  have htail :=
    all_stepsize_near_minimizer_exclusions_and_final_bound
      (Node := Node) quad lambda μ oracle _hquad _hnoise
      hslow hscalarExp hscalarAsymp alphaNearOpt hnear_nonneg hnear_value
  exact ⟨alphaStar, alphaNearOpt,
    (by intro T hT; rfl),
    hnear_nonneg, hnear_value, htail.1, htail.2.1, htail.2.2⟩

theorem alpha_sq_isLittleO_scalar_scale
    {alphaSeq : ℕ → ℝ}
    (hpos : ∀ᶠ T in Filter.atTop, 0 < alphaSeq T)
    (halpha : Filter.Tendsto alphaSeq Filter.atTop (nhds 0))
    (hprod : Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
      Filter.atTop Filter.atTop) :
    Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ => alphaSeq T ^ 2)
      (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
  classical
  refine Asymptotics.IsLittleO.of_bound ?_
  intro eps heps
  have hsmall_dist :
      ∀ᶠ T : ℕ in Filter.atTop, dist (alphaSeq T) 0 < eps :=
    (Metric.tendsto_nhds.mp halpha) eps heps
  have hsmall :
      ∀ᶠ T : ℕ in Filter.atTop, alphaSeq T ≤ eps := by
    filter_upwards [hpos, hsmall_dist] with T hposT hdistT
    have habs : |alphaSeq T| < eps := by
      simpa [Real.dist_eq] using hdistT
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  have hprod_ge_one :
      ∀ᶠ T : ℕ in Filter.atTop, (1 : ℝ) ≤ alphaSeq T * (T : ℝ) :=
    hprod.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [hpos, hsmall, hprod_ge_one] with T hposT hsmallT hprodT
  have halpha_nonneg : 0 ≤ alphaSeq T := le_of_lt hposT
  have hprod_nonneg : 0 ≤ alphaSeq T * (T : ℝ) :=
    le_trans (by norm_num) hprodT
  have hinv_nonneg : 0 ≤ (alphaSeq T * (T : ℝ))⁻¹ :=
    inv_nonneg.mpr hprod_nonneg
  have hscale_nonneg :
      0 ≤ (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T :=
    add_nonneg hinv_nonneg halpha_nonneg
  have hsq_nonneg : 0 ≤ alphaSeq T ^ 2 := sq_nonneg _
  have hsq_le :
      alphaSeq T ^ 2 ≤
        eps * ((alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
    have halpha_le_scale :
        alphaSeq T ≤ (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T := by
      nlinarith [hinv_nonneg]
    have hmul :=
      mul_le_mul hsmallT halpha_le_scale halpha_nonneg heps.le
    nlinarith [hmul]
  have hleft_abs : |alphaSeq T ^ 2| = alphaSeq T ^ 2 :=
    abs_of_nonneg hsq_nonneg
  have hright_abs :
      |(alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T| =
        (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T :=
    abs_of_nonneg hscale_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hleft_abs, hright_abs]
  exact hsq_le

theorem quadratic_scalar_twoTerm_isBigO_scalar_scale
    (quad : Setup Node ℝ) (lambda : ℝ)
    {alphaSeq : ℕ → ℝ}
    (hpos : ∀ᶠ T in Filter.atTop, 0 < alphaSeq T)
    (hprod : Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
      Filter.atTop Filter.atTop) :
    Asymptotics.IsBigO Filter.atTop
      (fun T : ℕ =>
        quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaSeq T * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaSeq T)
      (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
  simpa only [div_div, mul_assoc] using
    Asymptotics.isBigO_const_mul_inv_add_mul_of_nonneg
      (quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
      (lambda * (quad.sigma ^ 2 * quad.influenceSecondMoment) /
        (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))))
      (fun T : ℕ => alphaSeq T * (T : ℝ)) alphaSeq
      (hpos.mono fun T hT => mul_nonneg hT.le (Nat.cast_nonneg T))
      (hpos.mono fun _ hT => hT.le)

theorem sqrt_mul_isLittleO_of_left_littleO_right_isBigO_nonneg_scale
    {f g scale : ℕ → ℝ}
    (hf : Asymptotics.IsLittleO Filter.atTop f scale)
    (hg : Asymptotics.IsBigO Filter.atTop g scale)
    (hscale_nonneg : ∀ᶠ T in Filter.atTop, 0 ≤ scale T) :
    Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ => Real.sqrt (f T * g T)) scale := by
  exact Asymptotics.IsLittleO.sqrt_mul_of_isBigO hf hg hscale_nonneg

theorem real_abs_sq_sub_sq_le_sq_sub_add_cross (x u : ℝ) :
    |(|x| ^ 2 - |u| ^ 2)| ≤ |x - u| ^ 2 + 2 * |x - u| * |u| := by
  have hsplit :
      |x| ^ 2 - |u| ^ 2 = (x - u) ^ 2 + 2 * u * (x - u) := by
    rw [sq_abs, sq_abs]
    ring
  calc
    |(|x| ^ 2 - |u| ^ 2)| =
        |(x - u) ^ 2 + 2 * u * (x - u)| := by rw [hsplit]
    _ ≤ |(x - u) ^ 2| + |2 * u * (x - u)| := abs_add_le _ _
    _ = |x - u| ^ 2 + 2 * |x - u| * |u| := by
      rw [abs_pow, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem integral_abs_mul_abs_le_sqrt_integral_abs_sq_mul_sqrt_integral_abs_sq
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, |f ω| * |g ω| ∂μ) ≤
      Real.sqrt (∫ ω, |f ω| ^ 2 ∂μ) *
        Real.sqrt (∫ ω, |g ω| ^ 2 ∂μ) := by
  simpa only [Real.norm_eq_abs] using
    (integral_norm_mul_norm_le_sqrt_integral_norm_sq_mul_sqrt_integral_norm_sq hf hg)

theorem abs_integral_abs_sq_sub_integral_abs_sq_le_l2_error_cross
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {x u : Ω → ℝ} (hx : MemLp x 2 μ) (hu : MemLp u 2 μ) :
    |(∫ ω, |x ω| ^ 2 ∂μ) - (∫ ω, |u ω| ^ 2 ∂μ)| ≤
      (∫ ω, |x ω - u ω| ^ 2 ∂μ) +
        2 * Real.sqrt (∫ ω, |x ω - u ω| ^ 2 ∂μ) *
          Real.sqrt (∫ ω, |u ω| ^ 2 ∂μ) := by
  simpa [Real.norm_eq_abs] using
    (abs_integral_sq_sub_integral_sq_le_integral_error_sq_add_cross (μ := μ) hx hu)

theorem finite_average_square_moment_abs_sub_le_l2_error_cross
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : ℕ) (x u : ℕ → Ω → ℝ)
    (hx : ∀ t : ℕ, MemLp (x t) 2 μ)
    (hu : ∀ t : ℕ, MemLp (u t) 2 μ) :
    |((T : ℝ)⁻¹ *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |x t ω| ^ 2 ∂μ)) -
      ((T : ℝ)⁻¹ *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |u t ω| ^ 2 ∂μ))| ≤
      ((T : ℝ)⁻¹ *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |x t ω - u t ω| ^ 2 ∂μ)) +
        2 * Real.sqrt
          (((T : ℝ)⁻¹ *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |x t ω - u t ω| ^ 2 ∂μ)) *
            ((T : ℝ)⁻¹ *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |u t ω| ^ 2 ∂μ))) := by
  simpa [Real.norm_eq_abs] using
    finite_average_integral_sq_abs_sub_le_average_error_sq_add_cross
      (μ := μ) T x u (fun t _ht => hx t) (fun t _ht => hu t)

theorem signed_difference_isLittleO_of_abs_le_l2_budget
    {f M U scale : ℕ → ℝ}
    (hbound :
      ∀ᶠ T in Filter.atTop,
        |f T| ≤ M T + 2 * Real.sqrt (M T * U T))
    (hbudget_nonneg :
      ∀ᶠ T in Filter.atTop,
        0 ≤ M T + 2 * Real.sqrt (M T * U T))
    (hM : Asymptotics.IsLittleO Filter.atTop M scale)
    (hcross :
      Asymptotics.IsLittleO Filter.atTop
        (fun T : ℕ => Real.sqrt (M T * U T)) scale) :
    Asymptotics.IsLittleO Filter.atTop f scale := by
  apply Asymptotics.isLittleO_of_abs_le_error_add_sqrt_cross ?_ hM hcross
  simpa only [Real.norm_eq_abs] using hbound

theorem quadraticLowerBoundStationarityFunctional_eq_lambda_average_iterate_square
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (T : ℕ) (alpha : ℝ) :
    quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha =
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            |lambda *
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t| ^ 2 ∂μ) := by
  classical
  have havg_linear :
      ∀ x : ℝ, quad.averageGradient x = lambda * x :=
    homogeneousQuadratic_averageGradient_eq_linear
      (Node := Node) quad lambda hquad
  unfold quadraticLowerBoundStationarityFunctional stationarityAverage
    expectedGradientNormSq randomAverageIterate
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t _ht
  refine integral_congr_ae ?_
  filter_upwards with ω
  have hgrad :
      (quad.withStepsize alpha).averageGradient
          ((quad.withStepsize alpha).averageIterate (oracle.noise ω) t) =
        lambda *
          (quad.withStepsize alpha).averageIterate (oracle.noise ω) t := by
    simpa [withStepsize] using
      havg_linear
        ((quad.withStepsize alpha).averageIterate (oracle.noise ω) t)
  rw [hgrad]
  simp [Real.norm_eq_abs]

/-- Appendix C.1/C.2 transfer for Theorem 8.1, equations (8.8) and the
printed `M_T/U_T` comparison.  This is the source-level bridge from the scalar
moment expansion to the true quadratic stationarity functional along any
small-stepsize, long-time sequence. -/
theorem quadraticLowerBoundStationarityFunctional_asymptotic_of_scalar_and_slow
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hslow : QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle)
    (hscalarAsymp :
      QuadraticScalarMomentAsymptoticConsequence (Node := Node)
        quad lambda μ oracle)
    (alphaSeq : ℕ → ℝ)
    (hpos : ∀ᶠ T in Filter.atTop, 0 < alphaSeq T)
    (halpha : Filter.Tendsto alphaSeq Filter.atTop (nhds 0))
    (hprod : Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
      Filter.atTop Filter.atTop) :
    Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ =>
        quad.quadraticLowerBoundStationarityFunctional μ oracle T
            (alphaSeq T) -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaSeq T * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaSeq T))
      (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
  classical
  let twoTerm : ℕ → ℝ := fun T =>
    quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaSeq T * (T : ℝ)) +
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
        (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaSeq T
  let scale : ℕ → ℝ := fun T => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T
  have hscalarLittle :
      Asymptotics.IsLittleO Filter.atTop
        (fun T : ℕ =>
          quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T -
            twoTerm T) scale := by
    simpa [twoTerm, scale] using
      hscalarAsymp alphaSeq hpos halpha hprod
  have htransferLittle :
      Asymptotics.IsLittleO Filter.atTop
        (fun T : ℕ =>
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaSeq T) -
            quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T)
        scale := by
    rcases hslow with ⟨C2, alpha0, hC2_pos, halpha0_pos, hslow_bound⟩
    have halphaSqLittle :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ => alphaSeq T ^ 2) scale := by
      simpa [scale] using
        alpha_sq_isLittleO_scalar_scale
          (alphaSeq := alphaSeq) hpos halpha hprod
    have hslowBudgetLittle :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ => C2 * alphaSeq T ^ 2) scale :=
      halphaSqLittle.const_mul_left C2
    have htwoTermBigO :
        Asymptotics.IsBigO Filter.atTop twoTerm scale := by
      simpa [twoTerm, scale] using
        quadratic_scalar_twoTerm_isBigO_scalar_scale
          (Node := Node) quad lambda (alphaSeq := alphaSeq) hpos hprod
    have hscalarBigO :
        Asymptotics.IsBigO Filter.atTop
          (fun T : ℕ =>
            quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T)
          scale := by
      have hsum := hscalarLittle.isBigO.add htwoTermBigO
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
    let Mlambda : ℕ → ℝ := fun T =>
      lambda ^ 2 *
        (((T : ℝ)⁻¹) *
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              |(quad.withStepsize (alphaSeq T)).averageIterate
                  (oracle.noise ω) t -
                quad.quadraticScalarComparisonProcess lambda (alphaSeq T)
                  (oracle.noise ω) t| ^ 2 ∂μ))
    have hsmall_alpha_abs :
        ∀ᶠ T : ℕ in Filter.atTop, dist (alphaSeq T) 0 < alpha0 :=
      (Metric.tendsto_nhds.mp halpha) alpha0 halpha0_pos
    have hsmall_alpha :
        ∀ᶠ T : ℕ in Filter.atTop, alphaSeq T ≤ alpha0 := by
      filter_upwards [hsmall_alpha_abs] with T hT
      have habs : |alphaSeq T| < alpha0 := by
        simpa [Real.dist_eq] using hT
      exact le_trans (le_abs_self (alphaSeq T)) (le_of_lt habs)
    have hprod_ge_one :
        ∀ᶠ T : ℕ in Filter.atTop, (1 : ℝ) ≤ alphaSeq T * (T : ℝ) :=
      hprod.eventually (Filter.eventually_ge_atTop (1 : ℝ))
    have hMlambdaBigO :
        Asymptotics.IsBigO Filter.atTop Mlambda
          (fun T : ℕ => C2 * alphaSeq T ^ 2) := by
      refine Asymptotics.IsBigO.of_bound (lambda ^ 2) ?_
      filter_upwards [hpos, hsmall_alpha, hprod_ge_one]
        with T hposT hsmallT hprodT
      let raw : ℝ :=
        ((T : ℝ)⁻¹) *
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              |(quad.withStepsize (alphaSeq T)).averageIterate
                  (oracle.noise ω) t -
                quad.quadraticScalarComparisonProcess lambda (alphaSeq T)
                  (oracle.noise ω) t| ^ 2 ∂μ)
      have hslowT : raw ≤ C2 * alphaSeq T ^ 2 := by
        simpa [raw] using
          hslow_bound (alphaSeq T) hposT hsmallT T hprodT
      have hraw_nonneg : 0 ≤ raw := by
        have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
          inv_nonneg.mpr (Nat.cast_nonneg T)
        have hsum_nonneg :
            0 ≤ Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                |(quad.withStepsize (alphaSeq T)).averageIterate
                    (oracle.noise ω) t -
                  quad.quadraticScalarComparisonProcess lambda (alphaSeq T)
                    (oracle.noise ω) t| ^ 2 ∂μ) := by
          refine Finset.sum_nonneg ?_
          intro t _ht
          exact integral_nonneg (fun ω => sq_nonneg _)
        dsimp [raw]
        exact mul_nonneg hTinv_nonneg hsum_nonneg
      have hbudget_nonneg : 0 ≤ C2 * alphaSeq T ^ 2 :=
        mul_nonneg hC2_pos.le (sq_nonneg _)
      have hM_nonneg : 0 ≤ Mlambda T := by
        dsimp [Mlambda, raw] at hraw_nonneg ⊢
        exact mul_nonneg (sq_nonneg lambda) hraw_nonneg
      have hM_le : Mlambda T ≤ lambda ^ 2 * (C2 * alphaSeq T ^ 2) := by
        dsimp [Mlambda, raw] at hslowT ⊢
        exact mul_le_mul_of_nonneg_left hslowT (sq_nonneg lambda)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hM_nonneg, abs_of_nonneg hbudget_nonneg]
      exact hM_le
    have hMlambdaLittle :
        Asymptotics.IsLittleO Filter.atTop Mlambda scale :=
      hMlambdaBigO.trans_isLittleO hslowBudgetLittle
    have hscale_nonneg :
        ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ scale T := by
      filter_upwards [hpos] with T hposT
      have halpha_nonneg : 0 ≤ alphaSeq T := le_of_lt hposT
      have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
      exact add_nonneg
        (inv_nonneg.mpr (mul_nonneg halpha_nonneg hT_nonneg))
        halpha_nonneg
    have hcrossLittle :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ =>
            Real.sqrt (Mlambda T *
              quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T))
          scale :=
      sqrt_mul_isLittleO_of_left_littleO_right_isBigO_nonneg_scale
        hMlambdaLittle hscalarBigO hscale_nonneg
    /- Remaining source transfer, from JSON Theorem 8.1 steps 9-10:
       use `hslow_bound` to get `M_T <= C2 * alpha_T^2`, derive
       `U_T = O(scale)` from `hscalarLittle` and the explicit two-term form,
       then prove
       `|J_T - U_T| <= lambda^2 * (M_T + 2 * sqrt (M_T * U_T))`
       by Cauchy--Schwarz over the averaged integrals. -/
    let U : ℕ → ℝ := fun T =>
      quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T
    have hbound :
        ∀ᶠ T in Filter.atTop,
          |quad.quadraticLowerBoundStationarityFunctional μ oracle T
                (alphaSeq T) -
              quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T| ≤
            Mlambda T + 2 * Real.sqrt (Mlambda T * U T) := by
      filter_upwards with T
      let alpha : ℝ := alphaSeq T
      let stepped := quad.withStepsize alpha
      let x : ℕ → Ω → ℝ := fun t ω =>
        lambda * stepped.averageIterate (oracle.noise ω) t
      let u : ℕ → Ω → ℝ := fun t ω =>
        lambda *
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) t
      have hstepped_oracle :
          stepped.StochasticOracleAssumptions μ oracle := by
        simpa [stepped, StochasticOracleAssumptions, withStepsize] using
          hnoise.1
      have hx : ∀ t : ℕ, MemLp (x t) 2 μ := by
        intro t
        have hgenerated :=
          stepped.generated_pushpull_coordinate_memLp μ oracle
            hstepped_oracle t
        have hsum :
            MemLp
              (fun ω : Ω =>
                ∑ i : Node,
                  stepped.primalState (oracle.noise ω) t i) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro i _hi
          exact hgenerated.1 i
        have havg :
            MemLp
              (fun ω : Ω =>
                stepped.averageIterate (oracle.noise ω) t) 2 μ := by
          simpa [stepped, averageIterate, arithmeticAverage] using
            hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
        simpa [x] using havg.const_smul lambda
      have hu : ∀ t : ℕ, MemLp (u t) 2 μ := by
        intro t
        have hscalar :
            MemLp
              (fun ω : Ω =>
                quad.quadraticScalarComparisonProcess lambda alpha
                  (oracle.noise ω) t) 2 μ :=
          quadraticScalarComparisonProcess_memLp_two
            (Node := Node) quad lambda alpha μ oracle hnoise.1 t
        simpa [u] using hscalar.const_smul lambda
      have hfinite :=
        finite_average_square_moment_abs_sub_le_l2_error_cross
          (μ := μ) T x u hx hu
      have hJ :
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha =
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |x t ω| ^ 2 ∂μ) := by
        have hbase :=
          quadraticLowerBoundStationarityFunctional_eq_lambda_average_iterate_square
            (Node := Node) quad lambda μ oracle hquad T alpha
        simpa [x, stepped] using hbase
      have hU :
          U T =
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |u t ω| ^ 2 ∂μ) := by
        dsimp [U, u, alpha]
        unfold quadraticScalarMomentFunctional
        rfl
      have hE :
          ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |x t ω - u t ω| ^ 2 ∂μ) =
            Mlambda T := by
        calc
          ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |x t ω - u t ω| ^ 2 ∂μ) =
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  lambda ^ 2 *
                    |stepped.averageIterate (oracle.noise ω) t -
                      quad.quadraticScalarComparisonProcess lambda alpha
                        (oracle.noise ω) t| ^ 2 ∂μ) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro t _ht
              refine integral_congr_ae ?_
              filter_upwards with ω
              dsimp [x, u]
              have hsub :
                  lambda * stepped.averageIterate (oracle.noise ω) t -
                      lambda *
                        quad.quadraticScalarComparisonProcess lambda alpha
                          (oracle.noise ω) t =
                    lambda *
                      (stepped.averageIterate (oracle.noise ω) t -
                        quad.quadraticScalarComparisonProcess lambda alpha
                          (oracle.noise ω) t) := by
                ring
              rw [hsub, abs_mul, mul_pow, sq_abs lambda]
          _ =
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                lambda ^ 2 *
                  (∫ ω,
                    |stepped.averageIterate (oracle.noise ω) t -
                      quad.quadraticScalarComparisonProcess lambda alpha
                        (oracle.noise ω) t| ^ 2 ∂μ)) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro t _ht
              rw [MeasureTheory.integral_const_mul]
          _ = Mlambda T := by
              dsimp [Mlambda, alpha, stepped]
              rw [← Finset.mul_sum]
              ring
      calc
        |quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaSeq T) -
            quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T| =
          |((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |x t ω| ^ 2 ∂μ) -
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |u t ω| ^ 2 ∂μ)| := by
            rw [show alphaSeq T = alpha by rfl, hJ]
            rw [show
                quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T =
                  U T by rfl, hU]
        _ ≤
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω, |x t ω - u t ω| ^ 2 ∂μ) +
              2 * Real.sqrt
                ((((T : ℝ)⁻¹) *
                    Finset.sum (Finset.range T) (fun t =>
                      ∫ ω, |x t ω - u t ω| ^ 2 ∂μ)) *
                  (((T : ℝ)⁻¹) *
                    Finset.sum (Finset.range T) (fun t =>
                      ∫ ω, |u t ω| ^ 2 ∂μ))) := hfinite
        _ = Mlambda T + 2 * Real.sqrt (Mlambda T * U T) := by
            rw [hE, ← hU]
    have hbudget_nonneg :
        ∀ᶠ T in Filter.atTop,
          0 ≤ Mlambda T + 2 * Real.sqrt (Mlambda T * U T) := by
      filter_upwards with T
      have hM_nonneg : 0 ≤ Mlambda T := by
        dsimp [Mlambda]
        have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
          inv_nonneg.mpr (Nat.cast_nonneg T)
        have hsum_nonneg :
            0 ≤ Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                |(quad.withStepsize (alphaSeq T)).averageIterate
                    (oracle.noise ω) t -
                  quad.quadraticScalarComparisonProcess lambda (alphaSeq T)
                    (oracle.noise ω) t| ^ 2 ∂μ) := by
          refine Finset.sum_nonneg ?_
          intro t _ht
          exact integral_nonneg (fun ω => sq_nonneg _)
        exact mul_nonneg (sq_nonneg lambda)
          (mul_nonneg hTinv_nonneg hsum_nonneg)
      have hsqrt_nonneg :
          0 ≤ Real.sqrt (Mlambda T * U T) :=
        Real.sqrt_nonneg _
      nlinarith
    have htransfer :=
      signed_difference_isLittleO_of_abs_le_l2_budget
        (f := fun T : ℕ =>
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaSeq T) -
            quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T)
        (M := Mlambda) (U := U) (scale := scale)
        hbound hbudget_nonneg hMlambdaLittle
        (by simpa [U] using hcrossLittle)
    simpa [U] using htransfer
  have hcombined := htransferLittle.add hscalarLittle
  simpa [twoTerm, scale, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using hcombined

theorem isLittleO_of_eventually_between
    {f lower upper scale : ℕ → ℝ}
    (hlower : Asymptotics.IsLittleO Filter.atTop lower scale)
    (hupper : Asymptotics.IsLittleO Filter.atTop upper scale)
    (hbetween : ∀ᶠ T in Filter.atTop, lower T ≤ f T ∧ f T ≤ upper T) :
    Asymptotics.IsLittleO Filter.atTop f scale := by
  exact Asymptotics.isLittleO_of_eventually_between hlower hupper hbetween

theorem nat_inv_isLittleO_inv_sqrt :
    Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ => (T : ℝ)⁻¹)
      (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) := by
  exact Asymptotics.isLittleO_natCast_inv_inv_sqrt

theorem scale_isBigO_of_value_upper_and_littleO_transfer
    {J twoTerm scale target : ℕ → ℝ}
    (hscale_two :
      ∃ Cscale : ℝ, 0 < Cscale ∧
        ∀ᶠ T in Filter.atTop, scale T ≤ Cscale * twoTerm T)
    (htransfer :
      Asymptotics.IsLittleO Filter.atTop
        (fun T : ℕ => J T - twoTerm T) scale)
    (hvalue_upper :
      ∃ Cvalue T0, 0 ≤ Cvalue ∧
        ∀ T : ℕ, T0 ≤ T → J T ≤ Cvalue * target T)
    (hscale_nonneg : ∀ᶠ T in Filter.atTop, 0 ≤ scale T)
    (htarget_nonneg : ∀ᶠ T in Filter.atTop, 0 ≤ target T) :
    Asymptotics.IsBigO Filter.atTop scale target := by
  rcases hvalue_upper with ⟨Cvalue, T0, _hCvalue_nonneg, hvalue_bound⟩
  apply Asymptotics.isBigO_of_le_leading_and_value_upper_and_littleO_sub
    (leading := twoTerm) hscale_two htransfer ?_ hscale_nonneg
  refine ⟨Cvalue, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop T0] with T hT
  exact hvalue_bound T hT

theorem quadratic_scalar_scale_le_const_twoTerm_eventually
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {alphaSeq : ℕ → ℝ}
    (hpos : ∀ᶠ T in Filter.atTop, 0 < alphaSeq T)
    (hprod : Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
      Filter.atTop Filter.atTop) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ T in Filter.atTop,
        (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T ≤
          C *
            (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaSeq T * (T : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaSeq T) := by
  classical
  have hlambda_pos : 0 < lambda := hquad.1
  have hsigma_pos : 0 < quad.sigma := hnoise.2.1
  let A : ℝ := quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))
  let B : ℝ :=
    lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos quad.Delta_positive quad.influenceGain_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact div_pos
      (mul_pos (mul_pos hlambda_pos (sq_pos_of_pos hsigma_pos))
        quad.influenceSecondMoment_pos)
      (mul_pos (by norm_num) quad.influenceGain_pos)
  refine ⟨A⁻¹ + B⁻¹, by positivity, ?_⟩
  have hprod_ge_one :
      ∀ᶠ T : ℕ in Filter.atTop, (1 : ℝ) ≤ alphaSeq T * (T : ℝ) :=
    hprod.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [hpos, hprod_ge_one] with T hposT hprodT
  let q : ℝ := alphaSeq T * (T : ℝ)
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hprodT
  have htwo_eq :
      A * q⁻¹ + B * alphaSeq T =
        quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaSeq T * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaSeq T := by
    dsimp [A, B, q]
    field_simp [ne_of_gt quad.influenceGain_pos]
  rw [← htwo_eq]
  simpa [q] using
    add_le_inv_add_inv_mul_weighted_add_of_pos A B q⁻¹ (alphaSeq T)
      hA_pos hB_pos (inv_nonneg.mpr hq_pos.le) hposT.le

theorem balancing_stepsize_eventually_eq_scaled_inv_sqrt
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {alphaStar : ℕ → ℝ}
    (hstar_eq : ∀ T : ℕ, 1 ≤ T →
      alphaStar T =
        Real.sqrt (2 * quad.Delta /
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment * (T : ℝ)))) :
    alphaStar =ᶠ[Filter.atTop] fun T : ℕ =>
      Real.sqrt (2 * quad.Delta /
        (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment)) *
        (Real.sqrt (T : ℝ))⁻¹ := by
  classical
  have hlambda_pos : 0 < lambda := hquad.1
  have hsigma_pos : 0 < quad.sigma := hnoise.2.1
  let A : ℝ :=
    2 * quad.Delta /
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) quad.Delta_positive.le)
      (mul_nonneg
        (mul_nonneg hlambda_pos.le (sq_pos_of_pos hsigma_pos).le)
        quad.influenceSecondMoment_pos.le)
  have hlarge : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  filter_upwards [hlarge] with T hT
  have hTreal_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hTreal_ne : (T : ℝ) ≠ 0 := ne_of_gt hTreal_pos
  have harg_eq :
      2 * quad.Delta /
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment * (T : ℝ)) =
        A * (T : ℝ)⁻¹ := by
    dsimp [A]
    field_simp [ne_of_gt hlambda_pos, ne_of_gt (sq_pos_of_pos hsigma_pos),
      ne_of_gt quad.influenceSecondMoment_pos, hTreal_ne]
  rw [hstar_eq T hT, harg_eq]
  rw [Real.sqrt_mul hA_nonneg, Real.sqrt_inv]

theorem balancing_stepsize_twoTerm_eq_matchingLeading_eventually
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {alphaStar : ℕ → ℝ}
    (hstar_eq : ∀ T : ℕ, 1 ≤ T →
      alphaStar T =
        Real.sqrt (2 * quad.Delta /
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment * (T : ℝ)))) :
    ∀ᶠ T : ℕ in Filter.atTop,
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaStar T =
        matchingQuadraticLeadingTerm (Node := Node) quad lambda T := by
  classical
  have hlambda_pos : 0 < lambda := hquad.1
  have hsigma_pos : 0 < quad.sigma := hnoise.2.1
  let A : ℝ :=
    2 * quad.Delta /
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment)
  let B : ℝ :=
    lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos
      (mul_pos (by norm_num : (0 : ℝ) < 2) quad.Delta_positive)
      (mul_pos
        (mul_pos hlambda_pos (sq_pos_of_pos hsigma_pos))
        quad.influenceSecondMoment_pos)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact div_pos
      (mul_pos
        (mul_pos hlambda_pos (sq_pos_of_pos hsigma_pos))
        quad.influenceSecondMoment_pos)
      (mul_pos (by norm_num : (0 : ℝ) < 2) quad.influenceGain_pos)
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have hstar_scaled :
      alphaStar =ᶠ[Filter.atTop] fun T : ℕ =>
        Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹ := by
    have hraw :=
      balancing_stepsize_eventually_eq_scaled_inv_sqrt
        (Node := Node) quad lambda μ oracle hquad hnoise hstar_eq
    simpa [A] using hraw
  have hcoeff_eq :
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A) +
          B * Real.sqrt A =
        quad.sigma *
          Real.sqrt (2 * lambda * quad.Delta / quad.effectiveNodeCount) := by
    have hleft_nonneg :
        0 ≤ quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A) +
            B * Real.sqrt A := by
      exact add_nonneg
        (div_nonneg quad.Delta_positive.le
          (mul_pos quad.influenceGain_pos hsqrtA_pos).le)
        (mul_nonneg hB_pos.le hsqrtA_pos.le)
    have hroot_arg_nonneg :
        0 ≤ 2 * lambda * quad.Delta / quad.effectiveNodeCount := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlambda_pos.le)
          quad.Delta_positive.le)
        quad.effectiveNodeCount_pos_and_le_nodeCount.1.le
    have hright_nonneg :
        0 ≤ quad.sigma *
          Real.sqrt (2 * lambda * quad.Delta / quad.effectiveNodeCount) := by
      exact mul_nonneg hsigma_pos.le (Real.sqrt_nonneg _)
    have hsquare :
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A) +
            B * Real.sqrt A) ^ 2 =
          (quad.sigma *
            Real.sqrt (2 * lambda * quad.Delta / quad.effectiveNodeCount)) ^ 2 := by
      rw [show
        (quad.sigma *
          Real.sqrt (2 * lambda * quad.Delta / quad.effectiveNodeCount)) ^ 2 =
            quad.sigma ^ 2 *
              (Real.sqrt (2 * lambda * quad.Delta / quad.effectiveNodeCount)) ^ 2 by ring]
      rw [Real.sq_sqrt hroot_arg_nonneg]
      field_simp [ne_of_gt hsqrtA_pos]
      rw [Real.sq_sqrt hA_pos.le]
      dsimp [A, B]
      unfold effectiveNodeCount
      field_simp [ne_of_gt hlambda_pos, ne_of_gt (sq_pos_of_pos hsigma_pos),
        ne_of_gt quad.influenceSecondMoment_pos, ne_of_gt quad.influenceGain_pos,
        ne_of_gt quad.Delta_positive]
      ring
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquare with heq | heq
    · exact heq
    · nlinarith
  have hlarge : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  filter_upwards [hstar_scaled, hlarge] with T hscaled hT
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hT_pos
  have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsqrtT_pos
  have hsqrtA_ne : Real.sqrt A ≠ 0 := ne_of_gt hsqrtA_pos
  let invs : ℝ := (Real.sqrt (T : ℝ))⁻¹
  have htwo_scaled :
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaStar T =
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Real.sqrt A) +
          B * Real.sqrt A) * invs := by
    have hsqrt_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
      Real.sq_sqrt hT_pos.le
    rw [hscaled]
    dsimp [B, invs]
    field_simp [hsqrtA_ne, hsqrtT_ne, ne_of_gt quad.influenceGain_pos]
    ring_nf
    rw [hsqrt_sq]
  have hlead_scaled :
      matchingQuadraticLeadingTerm (Node := Node) quad lambda T =
        (quad.sigma *
          Real.sqrt (2 * lambda * quad.Delta / quad.effectiveNodeCount)) *
          invs := by
    have hroot_arg_nonneg :
        0 ≤ 2 * lambda * quad.Delta / quad.effectiveNodeCount := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlambda_pos.le)
          quad.Delta_positive.le)
        quad.effectiveNodeCount_pos_and_le_nodeCount.1.le
    have hT_nonneg : 0 ≤ (T : ℝ) := hT_pos.le
    unfold matchingQuadraticLeadingTerm
    have harg_eq :
        2 * lambda * quad.Delta /
            (quad.effectiveNodeCount * (T : ℝ)) =
          (2 * lambda * quad.Delta / quad.effectiveNodeCount) *
            (T : ℝ)⁻¹ := by
      field_simp [ne_of_gt quad.effectiveNodeCount_pos_and_le_nodeCount.1,
        ne_of_gt hT_pos]
    rw [harg_eq, Real.sqrt_mul hroot_arg_nonneg, Real.sqrt_inv]
    dsimp [invs]
    ring
  rw [htwo_scaled, hlead_scaled, hcoeff_eq]

theorem infConstantStepsizeStationarity_le_quadraticLowerBoundStationarityFunctional_of_nonneg
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (T : ℕ) {alpha : ℝ} (halpha : 0 ≤ alpha) :
    quad.infConstantStepsizeStationarity μ oracle T ≤
      quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
  let valueSet : Set ℝ :=
    { value : ℝ |
      ∃ beta : ℝ, 0 ≤ beta ∧
        value = quad.quadraticLowerBoundStationarityFunctional μ oracle T beta }
  have hbddBelow : BddBelow valueSet := by
    refine ⟨0, ?_⟩
    intro value hvalue
    rcases hvalue with ⟨beta, _hbeta_nonneg, rfl⟩
    exact quadraticLowerBoundStationarityFunctional_nonneg
      (Node := Node) quad μ oracle T beta
  have hmem :
      quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha ∈
        valueSet := by
    exact ⟨alpha, halpha, rfl⟩
  change sInf valueSet ≤
    quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha
  exact csInf_le hbddBelow hmem

theorem quadraticLowerBound_near_value_sub_inv_le_infConstantStepsizeStationarity
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (alphaNearOpt : ℕ → ℝ)
    (hnear_value : ∀ T : ℕ, 1 ≤ T →
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤
        sInf { value : ℝ |
          ∃ alpha : ℝ, 0 ≤ alpha ∧
            value =
              quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha } +
        (T : ℝ)⁻¹)
    {T : ℕ} (hT : 1 ≤ T) :
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
        (alphaNearOpt T) - (T : ℝ)⁻¹ ≤
      quad.infConstantStepsizeStationarity μ oracle T := by
  let valueSet : Set ℝ :=
    { value : ℝ |
      ∃ alpha : ℝ, 0 ≤ alpha ∧
        value =
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha }
  have hnear := hnear_value T hT
  change
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
        (alphaNearOpt T) ≤
      sInf valueSet + (T : ℝ)⁻¹ at hnear
  change
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
        (alphaNearOpt T) - (T : ℝ)⁻¹ ≤
      sInf valueSet
  linarith

/-- Route-local Appendix C.3 squeeze: the near-minimizer lower comparison and
the balancing-stepsize upper comparison force the infimum residual to be
`o(T^{-1/2})`. -/
theorem infConstantStepsize_residual_squeeze_invSqrt
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {alphaStar alphaNearOpt : ℕ → ℝ}
    (hstar_eq : ∀ T : ℕ, 1 ≤ T →
      alphaStar T =
        Real.sqrt (2 * quad.Delta /
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment * (T : ℝ))))
    (hnear_value : ∀ T : ℕ, 1 ≤ T →
      quad.quadraticLowerBoundStationarityFunctional μ oracle T
          (alphaNearOpt T) ≤
        sInf { value : ℝ |
          ∃ alpha : ℝ, 0 ≤ alpha ∧
            value =
              quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha } +
        (T : ℝ)⁻¹)
    (htail :
      ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
        1 ≤ T ∧ 0 < alphaNearOpt T ∧
          quad.Delta /
              ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T ≥
              quad.sigma *
                Real.sqrt (2 * lambda * quad.Delta /
                  (quad.effectiveNodeCount * (T : ℝ))))
    (hstar_pos : ∀ᶠ T : ℕ in Filter.atTop, 0 < alphaStar T)
    (hnear_transfer_invSqrt :
      Asymptotics.IsLittleO Filter.atTop
        (fun T : ℕ =>
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaNearOpt T) -
            (quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T))
        (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹))
    (hstar_transfer_invSqrt :
      Asymptotics.IsLittleO Filter.atTop
        (fun T : ℕ =>
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaStar T) -
            (quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaStar T))
        (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ =>
        quad.infConstantStepsizeStationarity μ oracle T -
          matchingQuadraticLeadingTerm (Node := Node) quad lambda T)
      (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) := by
  classical
  let JNear : ℕ → ℝ := fun T =>
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
      (alphaNearOpt T)
  let twoNear : ℕ → ℝ := fun T =>
    quad.Delta /
        ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
        (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T
  let JStar : ℕ → ℝ := fun T =>
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
      (alphaStar T)
  let twoStar : ℕ → ℝ := fun T =>
    quad.Delta /
        ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
        (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaStar T
  refine isLittleO_of_eventually_between
    (f := fun T : ℕ =>
      quad.infConstantStepsizeStationarity μ oracle T -
        matchingQuadraticLeadingTerm (Node := Node) quad lambda T)
    (lower := fun T : ℕ => (JNear T - twoNear T) - (T : ℝ)⁻¹)
    (upper := fun T : ℕ => JStar T - twoStar T)
    (scale := fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)
    ?_ ?_ ?_
  · simpa [JNear, twoNear, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using
      hnear_transfer_invSqrt.sub nat_inv_isLittleO_inv_sqrt
  · simpa [JStar, twoStar] using hstar_transfer_invSqrt
  · rcases htail with ⟨T0, htail_bound⟩
    have htail_eventual : ∀ᶠ T : ℕ in Filter.atTop, T0 ≤ T :=
      Filter.eventually_atTop.2 ⟨T0, fun T hT => hT⟩
    have hstar_two_eq :
        ∀ᶠ T : ℕ in Filter.atTop,
          twoStar T =
            matchingQuadraticLeadingTerm (Node := Node) quad lambda T := by
      have hraw :=
        balancing_stepsize_twoTerm_eq_matchingLeading_eventually
          (Node := Node) quad lambda μ oracle hquad hnoise hstar_eq
      simpa [twoStar] using hraw
    filter_upwards [htail_eventual, hstar_pos, hstar_two_eq] with
      T htailT hstar_posT hstar_two_eqT
    rcases htail_bound T htailT with ⟨hT_one, _hnear_posT, htwoNear_ge⟩
    constructor
    · have hnear_inf :
          JNear T - (T : ℝ)⁻¹ ≤
            quad.infConstantStepsizeStationarity μ oracle T := by
        simpa [JNear] using
          quadraticLowerBound_near_value_sub_inv_le_infConstantStepsizeStationarity
            (Node := Node) quad μ oracle alphaNearOpt hnear_value hT_one
      have hlead_le_two :
          matchingQuadraticLeadingTerm (Node := Node) quad lambda T ≤
            twoNear T := by
        simpa [twoNear, matchingQuadraticLeadingTerm] using htwoNear_ge
      nlinarith
    · have hinf_le_star :
          quad.infConstantStepsizeStationarity μ oracle T ≤ JStar T := by
        exact
          infConstantStepsizeStationarity_le_quadraticLowerBoundStationarityFunctional_of_nonneg
            (Node := Node) quad μ oracle T (alpha := alphaStar T)
            hstar_posT.le
      nlinarith [hstar_two_eqT]

/-- Theorem 8.1: matching quadratic lower bound with leading constant
`sigma * sqrt(2 lambda Delta / (n_eff T))`. -/
theorem MatchingQuadraticLowerBound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (_hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ residual : ℕ → ℝ,
      LittleOInvSqrt residual ∧
        ∀ T : ℕ,
          quad.infConstantStepsizeStationarity μ oracle T =
            matchingQuadraticLeadingTerm (Node := Node) quad lambda T + residual T := by
  classical
  let residual : ℕ → ℝ := fun T =>
    quad.infConstantStepsizeStationarity μ oracle T -
      matchingQuadraticLeadingTerm (Node := Node) quad lambda T
  refine ⟨residual, ?_, ?_⟩
  · have htrich :
        AllStepsizeTrichotomyStatement (Node := Node) quad lambda μ oracle :=
      AllStepsizeTrichotomyForQuadraticLowerBound
        (Node := Node) quad lambda μ oracle hquad _hnoise
    have hslow :
        QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle :=
      QuadraticSlowComparisonDetails
        (Node := Node) quad lambda μ oracle hquad _hnoise
    have hscalarPair :
        QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle ∧
          QuadraticScalarMomentAsymptoticConsequence (Node := Node)
            quad lambda μ oracle :=
      QuadraticPeriodicScalarMomentExpansion
        (Node := Node) quad lambda μ oracle hquad _hnoise
    rcases hscalarPair with ⟨hscalarExp, hscalarAsymp⟩
    unfold LittleOInvSqrt
    change Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ =>
        quad.infConstantStepsizeStationarity μ oracle T -
          matchingQuadraticLeadingTerm (Node := Node) quad lambda T)
      (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)
    rcases htrich with
      ⟨alphaStar, alphaNearOpt, hstar_eq, hnear_nonneg, hnear_value,
        halpha_tendsto, hprod_tendsto, htail⟩
    have hnear_pos : ∀ᶠ T : ℕ in Filter.atTop, 0 < alphaNearOpt T := by
      rcases htail with ⟨T0, htail_bound⟩
      exact Filter.eventually_atTop.2
        ⟨T0, fun T hT => (htail_bound T hT).2.1⟩
    have hnear_transfer :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ =>
            quad.quadraticLowerBoundStationarityFunctional μ oracle T
                (alphaNearOpt T) -
              (quad.Delta /
                  ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
                (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T))
          (fun T : ℕ =>
            (alphaNearOpt T * (T : ℝ))⁻¹ + alphaNearOpt T) :=
      quadraticLowerBoundStationarityFunctional_asymptotic_of_scalar_and_slow
        (Node := Node) quad lambda μ oracle hquad _hnoise hslow hscalarAsymp
        alphaNearOpt hnear_pos halpha_tendsto hprod_tendsto
    have hnear_value_upper :
        ∃ C T0, 0 ≤ C ∧ ∀ T : ℕ, T0 ≤ T →
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaNearOpt T) ≤ C * (Real.sqrt (T : ℝ))⁻¹ :=
      near_minimizer_value_upper_inv_sqrt_of_scalar_expansion
        (Node := Node) quad lambda μ oracle hquad _hnoise hslow hscalarExp
        alphaNearOpt hnear_value
    have hnear_scale_two :
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ T in Filter.atTop,
            (alphaNearOpt T * (T : ℝ))⁻¹ + alphaNearOpt T ≤
              C *
                (quad.Delta /
                    ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
                  (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                    (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T) :=
      quadratic_scalar_scale_le_const_twoTerm_eventually
        (Node := Node) quad lambda μ oracle hquad _hnoise
        (alphaSeq := alphaNearOpt) hnear_pos hprod_tendsto
    have hnear_scale_nonneg :
        ∀ᶠ T : ℕ in Filter.atTop,
          0 ≤ (alphaNearOpt T * (T : ℝ))⁻¹ + alphaNearOpt T := by
      filter_upwards [hnear_pos] with T hposT
      exact add_nonneg
        (inv_nonneg.mpr
          (mul_nonneg hposT.le (by exact_mod_cast Nat.zero_le T)))
        hposT.le
    have hinvSqrt_nonneg :
        ∀ᶠ T : ℕ in Filter.atTop,
          0 ≤ (Real.sqrt (T : ℝ))⁻¹ := by
      filter_upwards with T
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hscaleNearBigO :
        Asymptotics.IsBigO Filter.atTop
          (fun T : ℕ =>
            (alphaNearOpt T * (T : ℝ))⁻¹ + alphaNearOpt T)
          (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) :=
      scale_isBigO_of_value_upper_and_littleO_transfer
        (J := fun T : ℕ =>
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
            (alphaNearOpt T))
        (twoTerm := fun T : ℕ =>
          quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T)
        (scale := fun T : ℕ =>
          (alphaNearOpt T * (T : ℝ))⁻¹ + alphaNearOpt T)
        (target := fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)
        hnear_scale_two hnear_transfer hnear_value_upper
        hnear_scale_nonneg hinvSqrt_nonneg
    have hnear_transfer_invSqrt :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ =>
            quad.quadraticLowerBoundStationarityFunctional μ oracle T
                (alphaNearOpt T) -
              (quad.Delta /
                  ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaNearOpt T * (T : ℝ)) +
                (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaNearOpt T))
          (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) :=
      hnear_transfer.trans_isBigO hscaleNearBigO
    have hstar_scaled :
        alphaStar =ᶠ[Filter.atTop] fun T : ℕ =>
          Real.sqrt (2 * quad.Delta /
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment)) *
            (Real.sqrt (T : ℝ))⁻¹ :=
      balancing_stepsize_eventually_eq_scaled_inv_sqrt
        (Node := Node) quad lambda μ oracle hquad _hnoise hstar_eq
    let A : ℝ :=
      2 * quad.Delta /
        (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment)
    have hstar_scaledA :
        alphaStar =ᶠ[Filter.atTop] fun T : ℕ =>
          Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹ := by
      simpa [A] using hstar_scaled
    have hA_pos : 0 < A := by
      have hlambda_pos : 0 < lambda := hquad.1
      have hsigma_pos : 0 < quad.sigma := _hnoise.2.1
      dsimp [A]
      exact div_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) quad.Delta_positive)
        (mul_pos
          (mul_pos hlambda_pos (sq_pos_of_pos hsigma_pos))
          quad.influenceSecondMoment_pos)
    have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
    rcases eventually_eq_pos_mul_inv_sqrt_rate_package
        (Real.sqrt A) alphaStar hsqrtA_pos hstar_scaledA with
      ⟨hstar_pos, hstar_tendsto, hstar_prod_tendsto, hstar_scale_bigO⟩
    have hstar_transfer :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ =>
            quad.quadraticLowerBoundStationarityFunctional μ oracle T
                (alphaStar T) -
              (quad.Delta /
                  ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
                (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaStar T))
          (fun T : ℕ =>
            (alphaStar T * (T : ℝ))⁻¹ + alphaStar T) :=
      quadraticLowerBoundStationarityFunctional_asymptotic_of_scalar_and_slow
        (Node := Node) quad lambda μ oracle hquad _hnoise hslow hscalarAsymp
        alphaStar hstar_pos hstar_tendsto hstar_prod_tendsto
    have hstar_transfer_invSqrt :
        Asymptotics.IsLittleO Filter.atTop
          (fun T : ℕ =>
            quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaStar T) -
            (quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaStar T * (T : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaStar T))
          (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) :=
      hstar_transfer.trans_isBigO hstar_scale_bigO
    exact
      infConstantStepsize_residual_squeeze_invSqrt
        (Node := Node) quad lambda μ oracle hquad _hnoise
        hstar_eq hnear_value htail hstar_pos
        hnear_transfer_invSqrt hstar_transfer_invSqrt
  · intro T
    simp [residual]

/-- Pure asymptotic comparison used at the end of Theorem 3.1.

If the conjectured residual and the matching lower-bound residual are both
`o(T^{-1/2})`, then any fixed positive coefficient gap eventually dominates
their difference. -/
private theorem originalLinearSpeedupResidual_sub_littleOInvSqrt_eventually_lt_gap
    {residual residual0 : ℕ → ℝ}
    (hresidual : OriginalLinearSpeedupResidualSmall residual)
    (hresidual0 : LittleOInvSqrt residual0)
    {gap : ℝ} (hgap : 0 < gap) :
    ∀ᶠ T : ℕ in Filter.atTop,
      residual T - residual0 T <
        gap * (Real.sqrt (T : ℝ))⁻¹ := by
  exact eventually_sub_lt_mul_of_tendsto_div_zero_and_isLittleO
    (hscale := by
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩] with T hT
      exact inv_pos.mpr (Real.sqrt_pos.2 (by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT))))
    (hresidual := by
      simpa [OriginalLinearSpeedupResidualSmall, div_eq_mul_inv, mul_comm] using hresidual)
    (by simpa only [LittleOInvSqrt] using hresidual0) hgap

/-- Epsilon selection for the two-node Theorem 3.1 counterexample.

The choice is small enough that the paper's minimum positive weight
`a = epsilon / 2` has inverse at least any prescribed numerical constant,
and it lies in the range where the Appendix A.1 slow/noise coefficients are
positive. -/
private theorem two_step_counterexample_exists_epsilon_for_constant
    (C : ℝ) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < 1 ∧ C ≤ (epsilon / 2)⁻¹ ∧
        0 < twoStepCounterexampleSpectralSlope epsilon ∧
          0 < twoStepCounterexampleNoiseCoefficient epsilon := by
  classical
  let M : ℝ := max C 0 + 2
  have hM_pos : 0 < M := by
    dsimp [M]
    linarith [le_max_right C 0]
  have hM_ge_C : C ≤ M := by
    dsimp [M]
    linarith [le_max_left C 0]
  refine ⟨M⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_pos.mpr hM_pos
  · rw [inv_lt_one₀ hM_pos]
    dsimp [M]
    linarith [le_max_right C 0]
  · have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have hinv_half : (M⁻¹ / 2)⁻¹ = 2 * M := by
      field_simp [hM_ne]
    rw [hinv_half]
    linarith
  · exact two_step_counterexample_spectral_slope_pos
      (M⁻¹) (inv_pos.mpr hM_pos) (by
        rw [inv_lt_one₀ hM_pos]
        dsimp [M]
        linarith [le_max_right C 0])
  · exact two_step_counterexample_noise_coefficient_pos
      (M⁻¹) (inv_pos.mpr hM_pos) (by
        rw [inv_lt_one₀ hM_pos]
        dsimp [M]
        linarith [le_max_right C 0])

/-- Bool-row Cauchy lower bound, specialized to the two-node coefficient
calculations. -/
private theorem rowSum_sq_le_two_rowNormSq_bool (w : RowVector Bool) :
    rowSum (Node := Bool) w ^ 2 ≤ 2 * rowNormSq (Node := Bool) w := by
  unfold rowSum rowNormSq
  simp
  nlinarith [sq_nonneg (w false - w true)]

/-- Coarse upper bound on the Appendix A.1 slow coefficient.  The source proof
uses the sharper `7.2 * epsilon`; this round only needs a clean constant. -/
private theorem two_step_counterexample_spectral_slope_le_eight_mul
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    twoStepCounterexampleSpectralSlope epsilon ≤ 8 * epsilon := by
  have hDpos :=
    two_step_counterexample_tail_denominator_pos
      epsilon hepsilon_pos hepsilon_lt
  have hDne :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  rw [two_step_counterexample_spectral_slope_formula epsilon hDne]
  have hepsilon_sq_lt : epsilon ^ 2 < epsilon := by
    calc
      epsilon ^ 2 = epsilon * epsilon := by ring
      _ < epsilon * 1 := mul_lt_mul_of_pos_left hepsilon_lt hepsilon_pos
      _ = epsilon := by ring
  have hmain :
      (2 * epsilon - 3) ^ 2 ≤
        16 * twoStepCounterexampleTailDenominator epsilon := by
    unfold twoStepCounterexampleTailDenominator
    nlinarith
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hDpos)]
  nlinarith [mul_le_mul_of_nonneg_left hmain hepsilon_pos.le]

/-- Coarse lower bound on the Appendix A.1 phase-noise coefficient.  It follows
from the phase-B row sum alone, so it avoids expanding the full `q_epsilon`
rational expression. -/
private theorem two_step_counterexample_noise_coefficient_ge_one_div_sixty_four
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    (1 / 64 : ℝ) ≤ twoStepCounterexampleNoiseCoefficient epsilon := by
  let wB : RowVector Bool := twoStepCounterexampleNoiseChannelB epsilon
  let D : ℝ := twoStepCounterexampleTailDenominator epsilon
  let N : ℝ := 8 * epsilon ^ 3 - 22 * epsilon ^ 2 + 15 * epsilon + 1
  have hDpos : 0 < D := by
    dsimp [D]
    exact two_step_counterexample_tail_denominator_pos
      epsilon hepsilon_pos hepsilon_lt
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hN_ge_D : D ≤ N := by
    dsimp [D, N]
    unfold twoStepCounterexampleTailDenominator
    have h0 : 0 ≤ epsilon := hepsilon_pos.le
    have h1 : 0 ≤ 1 - epsilon := by linarith
    have hbern :
        8 * epsilon ^ 3 - 22 * epsilon ^ 2 + 15 * epsilon + 1 -
            (5 / 8 + 5 / 4 * epsilon - epsilon ^ 2) =
          (3 / 8) * (1 - epsilon) ^ 3 +
            (119 / 8) * epsilon * (1 - epsilon) ^ 2 +
            (61 / 8) * epsilon ^ 2 * (1 - epsilon) +
            (9 / 8) * epsilon ^ 3 := by
      ring
    have hnonneg :
        0 ≤ 8 * epsilon ^ 3 - 22 * epsilon ^ 2 + 15 * epsilon + 1 -
            (5 / 8 + 5 / 4 * epsilon - epsilon ^ 2) := by
      rw [hbern]
      positivity
    linarith
  have hrow_ge : (1 / 4 : ℝ) ≤ rowSum (Node := Bool) wB := by
    dsimp [wB, D, N] at hDpos hDne hN_ge_D ⊢
    rw [two_step_counterexample_noise_channelB_rowSum_formula epsilon hDne]
    change (1 / 4 : ℝ) ≤ N / (4 * D)
    rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hDpos)]
    nlinarith
  have hrow_sq_ge : (1 / 16 : ℝ) ≤ rowSum (Node := Bool) wB ^ 2 := by
    nlinarith [sq_nonneg (rowSum (Node := Bool) wB - (1 / 4 : ℝ))]
  have hBnorm_ge : (1 / 32 : ℝ) ≤ rowNormSq (Node := Bool) wB := by
    have hrow_norm := rowSum_sq_le_two_rowNormSq_bool wB
    nlinarith
  have hAnorm_nonneg :
      0 ≤ rowNormSq (Node := Bool)
        (twoStepCounterexampleNoiseChannelA epsilon) :=
    rowNormSq_bool_nonneg (twoStepCounterexampleNoiseChannelA epsilon)
  unfold twoStepCounterexampleNoiseCoefficient
  dsimp [wB] at hBnorm_ge
  nlinarith

/-- The source ratio lower bound converted to the leading coefficient
comparison used in the final optimization step of Theorem 3.1. -/
private theorem two_step_counterexample_leading_coeff_lower
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    (32 * epsilon)⁻¹ ≤
      2 * Real.sqrt
        (twoStepCounterexampleNoiseCoefficient epsilon /
          twoStepCounterexampleSpectralSlope epsilon ^ 2) := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon_pos
  have hslope_pos :=
    two_step_counterexample_spectral_slope_pos
      epsilon hepsilon_pos hepsilon_lt
  have hnoise_ge :=
    two_step_counterexample_noise_coefficient_ge_one_div_sixty_four
      epsilon hepsilon_pos hepsilon_lt
  have hslope_le :=
    two_step_counterexample_spectral_slope_le_eight_mul
      epsilon hepsilon_pos hepsilon_lt
  have hsq_le :
      twoStepCounterexampleSpectralSlope epsilon ^ 2 ≤
        (8 * epsilon) ^ 2 := by
    have hleft :
        0 ≤ 8 * epsilon - twoStepCounterexampleSpectralSlope epsilon := by
      linarith
    have hright :
        0 ≤ 8 * epsilon + twoStepCounterexampleSpectralSlope epsilon := by
      positivity
    nlinarith [mul_nonneg hleft hright]
  have hratio :
      (4096 * epsilon ^ 2)⁻¹ ≤
        twoStepCounterexampleNoiseCoefficient epsilon /
          twoStepCounterexampleSpectralSlope epsilon ^ 2 := by
    have hden_big_pos : 0 < (8 * epsilon) ^ 2 := by positivity
    have hden_small_pos :
        0 < twoStepCounterexampleSpectralSlope epsilon ^ 2 := by
      positivity
    have hfirst :
        (4096 * epsilon ^ 2)⁻¹ ≤
          twoStepCounterexampleNoiseCoefficient epsilon / (8 * epsilon) ^ 2 := by
      have hconst :
          (4096 * epsilon ^ 2)⁻¹ = (1 / 64 : ℝ) / (8 * epsilon) ^ 2 := by
        field_simp [hepsilon_ne]
        ring
      rw [hconst]
      exact div_le_div_of_nonneg_right hnoise_ge hden_big_pos.le
    have hsecond :
        twoStepCounterexampleNoiseCoefficient epsilon / (8 * epsilon) ^ 2 ≤
          twoStepCounterexampleNoiseCoefficient epsilon /
            twoStepCounterexampleSpectralSlope epsilon ^ 2 := by
      exact div_le_div_of_nonneg_left
        (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 64) hnoise_ge)
        hden_small_pos
        hsq_le
    exact le_trans hfirst hsecond
  have hden_pos : 0 < 4096 * epsilon ^ 2 := by positivity
  have hden64_pos : 0 < 64 * epsilon := by positivity
  have hbase_nonneg : 0 ≤ (4096 * epsilon ^ 2)⁻¹ :=
    by positivity
  have hsqrt_base :
      Real.sqrt ((4096 * epsilon ^ 2)⁻¹) = (64 * epsilon)⁻¹ := by
    have hrhs_nonneg : 0 ≤ (64 * epsilon)⁻¹ :=
      inv_nonneg.mpr hden64_pos.le
    apply sq_eq_sq_iff_eq_or_eq_neg.mp ?_ |>.elim
      (fun h => h)
      (fun h => by nlinarith [Real.sqrt_nonneg ((4096 * epsilon ^ 2)⁻¹), hrhs_nonneg])
    rw [Real.sq_sqrt (inv_nonneg.mpr hden_pos.le)]
    field_simp [hepsilon_ne]
    ring
  calc
    (32 * epsilon)⁻¹ = 2 * (64 * epsilon)⁻¹ := by
      field_simp [hepsilon_ne]
      ring
    _ = 2 * Real.sqrt ((4096 * epsilon ^ 2)⁻¹) := by rw [hsqrt_base]
    _ ≤ 2 * Real.sqrt
        (twoStepCounterexampleNoiseCoefficient epsilon /
          twoStepCounterexampleSpectralSlope epsilon ^ 2) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio)
        (by norm_num : (0 : ℝ) ≤ 2)

/-- Strengthened epsilon selection for the two-node counterexample.

Besides making `(epsilon / 2)^{-1}` dominate the prescribed constant, this
chooses epsilon small enough that the source coefficient gap
`C < 2 sqrt(q_epsilon / s_epsilon^2)` is available independently of `T`. -/
private theorem two_step_counterexample_exists_epsilon_for_constant_and_gap
    (C : ℝ) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < 1 / 2 ∧ C ≤ (epsilon / 2)⁻¹ ∧
        C < 2 * Real.sqrt
          (twoStepCounterexampleNoiseCoefficient epsilon /
            twoStepCounterexampleSpectralSlope epsilon ^ 2) ∧
          0 < twoStepCounterexampleSpectralSlope epsilon ∧
            0 < twoStepCounterexampleNoiseCoefficient epsilon := by
  classical
  let M : ℝ := max C 0 + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    linarith [le_max_right C 0]
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    linarith [le_max_right C 0]
  have hC_lt_twentyM : C < 20 * M := by
    dsimp [M]
    have hC_le_max : C ≤ max C 0 := le_max_left C 0
    nlinarith
  have hC_lt_M : C < M := by
    dsimp [M]
    exact lt_of_le_of_lt (le_max_left C 0) (by linarith)
  let epsilon : ℝ := (200 * M)⁻¹
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilon_lt : epsilon < 1 := by
    dsimp [epsilon]
    rw [inv_lt_one₀]
    · nlinarith
    · positivity
  have hepsilon_lt_half : epsilon < 1 / 2 := by
    dsimp [epsilon]
    rw [inv_lt_comm₀]
    · nlinarith
    · positivity
    · norm_num
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon_pos
  refine ⟨epsilon, hepsilon_pos, hepsilon_lt_half, ?_, ?_, ?_, ?_⟩
  · have hinv_half : (epsilon / 2)⁻¹ = 400 * M := by
      dsimp [epsilon]
      field_simp [ne_of_gt hM_pos]
      ring
    rw [hinv_half]
    dsimp [M]
    nlinarith [le_max_left C 0]
  · have hcoeff_lower :=
      two_step_counterexample_leading_coeff_lower
        epsilon hepsilon_pos hepsilon_lt
    have hinv_coeff : (32 * epsilon)⁻¹ = (25 / 4) * M := by
      dsimp [epsilon]
      field_simp [ne_of_gt hM_pos]
      ring
    have hC_lt_coeff : C < (32 * epsilon)⁻¹ := by
      rw [hinv_coeff]
      nlinarith [hC_lt_M, hM_pos]
    exact lt_of_lt_of_le hC_lt_coeff hcoeff_lower
  · exact two_step_counterexample_spectral_slope_pos
      epsilon hepsilon_pos hepsilon_lt
  · exact two_step_counterexample_noise_coefficient_pos
      epsilon hepsilon_pos hepsilon_lt

/-- Raw finite-network facts for the two-node Theorem 3.1 matrices.

For `0 < epsilon < 1/2`, the paper matrices `R_epsilon`, `A_epsilon`, and
`B_epsilon` are stochastic in the required directions, have positive
diagonals, have every positive entry bounded below by `epsilon/2`, and their
positive-entry graphs are strongly connected. -/
private theorem two_node_counterexample_raw_network_specs
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) :
    RowStochastic (Node := Bool) (twoNodeCounterexamplePush epsilon) ∧
      ColumnStochastic (Node := Bool) (twoNodeCounterexamplePullA epsilon) ∧
      ColumnStochastic (Node := Bool) (twoNodeCounterexamplePullB epsilon) ∧
      PositiveDiagonal (Node := Bool) (twoNodeCounterexamplePush epsilon) ∧
      PositiveDiagonal (Node := Bool) (twoNodeCounterexamplePullA epsilon) ∧
      PositiveDiagonal (Node := Bool) (twoNodeCounterexamplePullB epsilon) ∧
      PositiveEntriesLowerBounded (Node := Bool) (epsilon / 2)
        (twoNodeCounterexamplePush epsilon) ∧
      PositiveEntriesLowerBounded (Node := Bool) (epsilon / 2)
        (twoNodeCounterexamplePullA epsilon) ∧
      PositiveEntriesLowerBounded (Node := Bool) (epsilon / 2)
        (twoNodeCounterexamplePullB epsilon) ∧
      StronglyConnectedPositiveGraph (Node := Bool)
        (twoNodeCounterexamplePush epsilon) ∧
      StronglyConnectedPositiveGraph (Node := Bool)
        (twoNodeCounterexamplePullA epsilon) ∧
      StronglyConnectedPositiveGraph (Node := Bool)
        (twoNodeCounterexamplePullB epsilon) := by
  classical
  have hepsilon_lt_one : epsilon < 1 := by linarith
  constructor
  · constructor
    · intro i j
      cases i <;> cases j <;>
        simp [twoNodeCounterexamplePush] <;> linarith
    · intro i
      cases i <;> simp [Fintype.sum_bool, twoNodeCounterexamplePush] <;> ring
  constructor
  · constructor
    · intro i j
      cases i <;> cases j <;>
        simp [twoNodeCounterexamplePullA] <;> linarith
    · intro j
      cases j <;> simp [Fintype.sum_bool, twoNodeCounterexamplePullA] <;> ring
  constructor
  · constructor
    · intro i j
      cases i <;> cases j <;>
        simp [twoNodeCounterexamplePullB] <;> linarith
    · intro j
      cases j <;> simp [Fintype.sum_bool, twoNodeCounterexamplePullB] <;> ring
  constructor
  · intro i
    cases i <;> simp [twoNodeCounterexamplePush] <;> linarith
  constructor
  · intro i
    cases i <;> simp [twoNodeCounterexamplePullA] <;> linarith
  constructor
  · intro i
    cases i <;> simp [twoNodeCounterexamplePullB] <;> linarith
  constructor
  · intro i j hij
    cases i <;> cases j <;>
      simp [twoNodeCounterexamplePush] at hij ⊢ <;> linarith
  constructor
  · intro i j hij
    cases i <;> cases j <;>
      simp [twoNodeCounterexamplePullA] at hij ⊢ <;> linarith
  constructor
  · intro i j hij
    cases i <;> cases j <;>
      simp [twoNodeCounterexamplePullB] at hij ⊢ <;> linarith
  constructor
  · intro i j
    exact Relation.ReflTransGen.single (by
      cases i <;> cases j <;>
        simp [twoNodeCounterexamplePush] <;> linarith)
  constructor
  · intro i j
    exact Relation.ReflTransGen.single (by
      cases i <;> cases j <;>
        simp [twoNodeCounterexamplePullA] <;> linarith)
  · intro i j
    exact Relation.ReflTransGen.single (by
      cases i <;> cases j <;>
        simp [twoNodeCounterexamplePullB] <;> linarith)

/-- Period two alternation of the two pull phases in the concrete
counterexample schedule. -/
private theorem two_node_counterexample_pull_schedule_periodic
    (epsilon : ℝ) :
    ∀ t : ℕ,
      (if (t + 2) % 2 = 0 then
          twoNodeCounterexamplePullA epsilon
        else
          twoNodeCounterexamplePullB epsilon) =
        (if t % 2 = 0 then
          twoNodeCounterexamplePullA epsilon
        else
          twoNodeCounterexamplePullB epsilon) := by
  intro t
  have hmod : (t + 2) % 2 = t % 2 := by omega
  rw [hmod]

/-- Concrete homogeneous quadratic setup for the two-node counterexample,
stopping before the Perron/influence coefficient calculation and stochastic
oracle realization. -/
private theorem two_step_counterexample_setup_core_exists
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) :
    ∃ inst : Setup Bool ℝ, ∃ lambda a : ℝ,
      FixedTwoNodeDeterministicPeriodicNetwork inst a ∧
        HomogeneousQuadraticComponents (Node := Bool) inst lambda ∧
          a = epsilon / 2 ∧ inst.L = 1 ∧ inst.Delta = 1 / 2 ∧
            inst.sigma = 1 ∧ lambda = 1 ∧ inst.period = 2 ∧
              inst.R = (fun _ => twoNodeCounterexamplePush epsilon) ∧
                (∀ t : ℕ,
                  inst.C t =
                    if t % 2 = 0 then
                      twoNodeCounterexamplePullA epsilon
                    else
                      twoNodeCounterexamplePullB epsilon) := by
  classical
  have hraw :=
    two_node_counterexample_raw_network_specs
      epsilon hepsilon_pos hepsilon_lt_half
  have hRrow := hraw.1
  have hAcol := hraw.2.1
  have hBcol := hraw.2.2.1
  have hRdiag := hraw.2.2.2.1
  have hAdiag := hraw.2.2.2.2.1
  have hBdiag := hraw.2.2.2.2.2.1
  have hRlower := hraw.2.2.2.2.2.2.1
  have hAlower := hraw.2.2.2.2.2.2.2.1
  have hBlower := hraw.2.2.2.2.2.2.2.2.1
  have hRconn := hraw.2.2.2.2.2.2.2.2.2.1
  have hAconn := hraw.2.2.2.2.2.2.2.2.2.2.1
  have hBconn := hraw.2.2.2.2.2.2.2.2.2.2.2
  let pullSchedule : ℕ → NodeMatrix Bool := fun t =>
    if t % 2 = 0 then
      twoNodeCounterexamplePullA epsilon
    else
      twoNodeCounterexamplePullB epsilon
  let inst : Setup Bool ℝ := {
    componentObjective := fun _ x => x ^ 2 / 2
    x0 := 1
    L := 1
    L_pos := by norm_num
    component_lsmooth := by
      intro i
      constructor
      · fun_prop
      · intro x y
        have hgradient :
            ∀ z : ℝ, ∇ (fun w : ℝ => w ^ 2 / 2) z = z := by
          intro z
          have h :=
            hasGradientAt_const_mul_norm_sub_sq_centered (E := ℝ) 1 0 z
          simpa [Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul,
            div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            h.gradient
        rw [hgradient x, hgradient y]
        simp
    objective_bddBelow := by
      refine ⟨0, ?_⟩
      rintro y ⟨x, rfl⟩
      simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
      positivity
    Delta_pos := by
      have hobjective :
          finiteAverageObjectiveOf (Node := Bool) (E := ℝ)
              (fun _ x => x ^ 2 / 2) = fun x : ℝ => x ^ 2 / 2 := by
        funext x
        simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
      have hinf :
          SOptLib.objectiveInfimumValue (Set.univ : Set ℝ)
              (fun x : ℝ => x ^ 2 / 2) = 0 := by
        unfold SOptLib.objectiveInfimumValue
        apply (show IsLeast ((fun x : ℝ => x ^ 2 / 2) '' Set.univ) 0 by
          constructor
          · exact ⟨0, Set.mem_univ 0, by norm_num⟩
          · rintro y ⟨x, _hx, rfl⟩
            positivity).csInf_eq
      rw [hobjective, hinf]
      norm_num
    sigma := 1
    sigma_nonneg := by norm_num
    alpha := 1
    period := 2
    period_pos := by norm_num
    minPositiveWeight := epsilon / 2
    minPositiveWeight_pos := by positivity
    R := fun _ => twoNodeCounterexamplePush epsilon
    C := pullSchedule
    R_periodic := by intro t; rfl
    C_periodic := by
      intro t
      dsimp [pullSchedule]
      exact two_node_counterexample_pull_schedule_periodic epsilon t
    R_rowStochastic := by intro t; exact hRrow
    C_columnStochastic := by
      intro t
      dsimp [pullSchedule]
      by_cases ht : t % 2 = 0
      · simp [ht, hAcol]
      · simp [ht, hBcol]
    R_positiveDiagonal := by intro t; exact hRdiag
    C_positiveDiagonal := by
      intro t
      dsimp [pullSchedule]
      by_cases ht : t % 2 = 0
      · simp [ht, hAdiag]
      · simp [ht, hBdiag]
    R_positiveEntriesLowerBounded := by intro t; exact hRlower
    C_positiveEntriesLowerBounded := by
      intro t
      dsimp [pullSchedule]
      by_cases ht : t % 2 = 0
      · simp [ht, hAlower]
      · simp [ht, hBlower]
    R_stronglyConnected := by intro t; exact hRconn
    C_stronglyConnected := by
      intro t
      dsimp [pullSchedule]
      by_cases ht : t % 2 = 0
      · simp [ht, hAconn]
      · simp [ht, hBconn] }
  have hfixed :
      FixedTwoNodeDeterministicPeriodicNetwork inst (epsilon / 2) := by
    constructor
    · rfl
    constructor
    · positivity
    constructor
    · norm_num
    constructor
    · intro t
      rfl
    · intro t
      dsimp [inst]
      exact two_node_counterexample_pull_schedule_periodic epsilon t
  have hquad :
      HomogeneousQuadraticComponents (Node := Bool) inst 1 := by
    constructor
    · norm_num
    constructor
    · rfl
    · intro i x
      simp [inst]
  have hDelta : inst.Delta = 1 / 2 := by
    have hobjective :
        inst.objective = fun x : ℝ => x ^ 2 / 2 := by
      funext x
      unfold Setup.objective finiteAverageObjectiveOf
      simp [inst, SOptLib.finiteUniformAverage]
    have hinf : inst.objectiveInfimum = 0 := by
      unfold Setup.objectiveInfimum SOptLib.objectiveInfimumValue
      rw [hobjective]
      apply (show IsLeast ((fun x : ℝ => x ^ 2 / 2) '' Set.univ) 0 by
        constructor
        · exact ⟨0, Set.mem_univ 0, by norm_num⟩
        · rintro y ⟨x, _hx, rfl⟩
          positivity).csInf_eq
    unfold Setup.Delta
    rw [hobjective, hinf]
    norm_num
  exact ⟨inst, 1, epsilon / 2, hfixed, hquad, rfl, rfl, hDelta, rfl, rfl,
    rfl, rfl, by intro t; rfl⟩

/-- If the two concrete period phases have the Appendix A.1 influence rows,
then the abstract period averages are exactly the printed `s_epsilon` and
`q_epsilon` coefficients. -/
private theorem two_step_counterexample_concrete_coefficients_from_phase_influence
    (epsilon : ℝ) (inst : Setup Bool ℝ)
    (hperiod : inst.period = 2)
    (hphase0 :
      inst.influence 0 = twoStepCounterexampleNoiseChannelA epsilon)
    (hphase1 :
      inst.influence 1 = twoStepCounterexampleNoiseChannelB epsilon) :
    (Finset.expect Finset.univ (fun r : Fin inst.period => rowSum (inst.influence r.1))) = twoStepCounterexampleSpectralSlope epsilon ∧
      inst.influenceSecondMoment =
        twoStepCounterexampleNoiseCoefficient epsilon := by
  constructor
  · unfold twoStepCounterexampleSpectralSlope
    rw [hperiod]
    simp [Fintype.expect_eq_sum_div_card, Fin.sum_univ_two, hphase0, hphase1]
  · unfold influenceSecondMoment twoStepCounterexampleNoiseCoefficient
    rw [hperiod]
    simp [Fin.sum_univ_two, hphase0, hphase1]
    ring

/-- The constant push matrix in the two-node counterexample has the printed
left Perron row in every phase. -/
private theorem two_step_counterexample_perronLeft_eq
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) (inst : Setup Bool ℝ)
    (hperiod : inst.period = 2)
    (hR : inst.R = (fun _ => twoNodeCounterexamplePush epsilon)) :
    ∀ t : ℕ,
      inst.perronLeft t = fun i : Bool => if i then 1 - epsilon else epsilon := by
  classical
  intro t
  let pi : RowVector Bool := fun i : Bool => if i then 1 - epsilon else epsilon
  have hepsilon_lt_one : epsilon < 1 := by linarith
  have hpi_pos : ∀ i : Bool, 0 < pi i := by
    intro i
    cases i <;> dsimp [pi] <;> linarith
  have hpi_sum : rowSum (Node := Bool) pi = 1 := by
    unfold rowSum
    simp [pi]
  have hpi_R :
      rowMulMatrix (Node := Bool) pi (twoNodeCounterexamplePush epsilon) = pi := by
    funext j
    cases j <;>
      simp [rowMulMatrix, twoNodeCounterexamplePush, pi, Fintype.sum_bool] <;>
        ring
  have hpi_stationary_period :
      rowMulMatrix (Node := Bool) pi (inst.pushLiftProduct t inst.period) = pi := by
    rw [hperiod]
    change rowMulMatrix (Node := Bool) pi (inst.pushLiftProduct t 2) = pi
    simp only [pushLiftProduct, hR]
    rw [← rowMulMatrix_matrixMul, hpi_R, matrixMul_identity_right]
    exact hpi_R
  have hperron_stationary_period :
      rowMulMatrix (Node := Bool) (inst.perronLeft t)
        (inst.pushLiftProduct t inst.period) = inst.perronLeft t :=
    (inst.competitor_phase_stationary inst.perronSequences
      inst.perronSequences_spec.1 inst.perronSequences_spec.2.1).1 t
  rcases inst.phase_stationary_vectors_direct.1 t with
    ⟨w, hw, hunique⟩
  have hpi_eq : pi = w :=
    hunique pi ⟨hpi_pos, hpi_sum, hpi_stationary_period⟩
  have hperron_eq : inst.perronLeft t = w :=
    hunique (inst.perronLeft t)
      ⟨inst.perronLeft_pos t, inst.perronLeft_sum t,
        hperron_stationary_period⟩
  exact hperron_eq.trans hpi_eq.symm

/-- Scalar corrected lift is homogeneous on real zero-sum states. -/
private theorem scalarCorrectedLift_smul_real
    (inst : Setup Bool ℝ) (t : ℕ) (c : ℝ) (W : ZeroSumState Bool ℝ) :
    inst.scalarCorrectedLift t
        ⟨fun i : Bool => c * W.1 i, by
          change ∑ i : Bool, c * W.1 i = 0
          rw [← Finset.mul_sum, W.2, mul_zero]⟩ =
      c * inst.scalarCorrectedLift t W := by
  simpa [FiniteNetwork.periodicCorrectedLift, scalarCorrectedLift,
    scalarCorrectedLiftSeriesTerm, weightedState, leftMul, smul_eq_mul] using
    (FiniteNetwork.periodicCorrectedLift_smul
      (leftWeight := inst.perronLeft)
      (transitionProduct := inst.pullLiftProduct) t c W)

/-- Scalar corrected-lift values for the four column innovations in the
period-two counterexample.  This is the finite two-phase Poisson system whose
solution gives the stable tracker tail coefficients `k_A,k_B`. -/
private theorem two_step_counterexample_scalarCorrectedLift_pullColumn_values
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) (inst : Setup Bool ℝ)
    (hperiod : inst.period = 2)
    (hR : inst.R = (fun _ => twoNodeCounterexamplePush epsilon))
    (hC :
      ∀ t : ℕ,
        inst.C t =
          if t % 2 = 0 then
            twoNodeCounterexamplePullA epsilon
          else
            twoNodeCounterexamplePullB epsilon) :
    inst.scalarCorrectedLift 1 (FiniteNetwork.normalizedCoordinateError (fun node => inst.C 0 node true) true (inst.C_column_sum 0 true)) =
        -((1 - 2 * epsilon) * twoStepCounterexampleTailA epsilon / 2) ∧
      inst.scalarCorrectedLift 1 (FiniteNetwork.normalizedCoordinateError (fun node => inst.C 0 node false) false (inst.C_column_sum 0 false)) =
        (1 - 2 * epsilon) * epsilon * twoStepCounterexampleTailA epsilon ∧
      inst.scalarCorrectedLift 2 (FiniteNetwork.normalizedCoordinateError (fun node => inst.C 1 node true) true (inst.C_column_sum 1 true)) =
        -((1 - 2 * epsilon) * twoStepCounterexampleTailB epsilon / 4) ∧
      inst.scalarCorrectedLift 2 (FiniteNetwork.normalizedCoordinateError (fun node => inst.C 1 node false) false (inst.C_column_sum 1 false)) =
        (1 - 2 * epsilon) * epsilon * twoStepCounterexampleTailB epsilon := by
  classical
  have hperron :=
    two_step_counterexample_perronLeft_eq
      epsilon hepsilon_pos hepsilon_lt_half inst hperiod hR
  let z : ℝ → ZeroSumState Bool ℝ := fun x =>
    ⟨fun i : Bool => if i then x else -x, by
      simp [Fintype.sum_bool]⟩
  have hz_smul (x : ℝ) :
      z x =
        (⟨fun i : Bool => x * (z 1).1 i, by
          change ∑ i : Bool, x * (z 1).1 i = 0
          rw [← Finset.mul_sum, (z 1).2, mul_zero]⟩ :
            ZeroSumState Bool ℝ) := by
    apply Subtype.ext
    funext i
    cases i <;> simp [z]
  have hC1_z (x : ℝ) :
      (⟨leftMul (Node := Bool) (E := ℝ) (inst.C 1) (z x).1,
          inst.C_leftMul_zeroSum_real 1 (z x)⟩ : ZeroSumState Bool ℝ) =
        z ((3 / 4 - epsilon) * x) := by
    apply Subtype.ext
    funext i
    cases i <;>
      simp [z, leftMul, hC, twoNodeCounterexamplePullB, Fintype.sum_bool] <;>
        ring
  have hC2_z (x : ℝ) :
      (⟨leftMul (Node := Bool) (E := ℝ) (inst.C 2) (z x).1,
          inst.C_leftMul_zeroSum_real 2 (z x)⟩ : ZeroSumState Bool ℝ) =
        z ((1 / 2 - epsilon) * x) := by
    apply Subtype.ext
    funext i
    cases i <;>
      simp [z, leftMul, hC, twoNodeCounterexamplePullA, Fintype.sum_bool] <;>
        ring
  have hweighted_z (t : ℕ) (x : ℝ) :
      weightedState (Node := Bool) (E := ℝ) (inst.perronLeft t) (z x).1 =
        (1 - 2 * epsilon) * x := by
    rw [hperron t]
    simp [z, weightedState, Fintype.sum_bool]
    ring
  have hperiod_scalar (W : ZeroSumState Bool ℝ) :
      inst.scalarCorrectedLift 3 W = inst.scalarCorrectedLift 1 W := by
    have h := inst.scalarCorrectedLift_periodic 1 W
    simpa [hperiod] using h
  have hLA_poisson (x : ℝ) :
      inst.scalarCorrectedLift 1 (z x) =
        (1 - 2 * epsilon) * x +
          ((3 / 4 - epsilon) * x) * inst.scalarCorrectedLift 2 (z 1) := by
    rw [inst.scalarCorrectedLift_poisson 1 (z x)]
    rw [hC1_z x, hweighted_z 2 x]
    rw [hz_smul ((3 / 4 - epsilon) * x)]
    rw [scalarCorrectedLift_smul_real
      inst 2 ((3 / 4 - epsilon) * x) (z 1)]
  have hLB_poisson (x : ℝ) :
      inst.scalarCorrectedLift 2 (z x) =
        (1 - 2 * epsilon) * x +
          ((1 / 2 - epsilon) * x) * inst.scalarCorrectedLift 1 (z 1) := by
    rw [inst.scalarCorrectedLift_poisson 2 (z x)]
    rw [hC2_z x, hweighted_z 3 x]
    rw [hperiod_scalar (z ((1 / 2 - epsilon) * x))]
    rw [hz_smul ((1 / 2 - epsilon) * x)]
    rw [scalarCorrectedLift_smul_real
      inst 1 ((1 / 2 - epsilon) * x) (z 1)]
  let LA : ℝ := inst.scalarCorrectedLift 1 (z 1)
  let LB : ℝ := inst.scalarCorrectedLift 2 (z 1)
  have hLA_eq : LA = (1 - 2 * epsilon) + (3 / 4 - epsilon) * LB := by
    simpa [LA, LB] using hLA_poisson 1
  have hLB_eq : LB = (1 - 2 * epsilon) + (1 / 2 - epsilon) * LA := by
    simpa [LA, LB] using hLB_poisson 1
  have hepsilon_lt_one : epsilon < 1 := by linarith
  have hDne :
      twoStepCounterexampleTailDenominator epsilon ≠ 0 :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt_one
  have hLA_val :
      LA = (1 - 2 * epsilon) * twoStepCounterexampleTailA epsilon := by
    unfold twoStepCounterexampleTailA
    field_simp [hDne]
    unfold twoStepCounterexampleTailDenominator at *
    nlinarith [hLA_eq, hLB_eq]
  have hLB_val :
      LB = (1 - 2 * epsilon) * twoStepCounterexampleTailB epsilon := by
    unfold twoStepCounterexampleTailB
    field_simp [hDne]
    unfold twoStepCounterexampleTailDenominator at *
    nlinarith [hLA_eq, hLB_eq]
  have hcolA_true :
      FiniteNetwork.normalizedCoordinateError (fun node => inst.C 0 node true) true (inst.C_column_sum 0 true) = z (-(1 / 2)) := by
    apply Subtype.ext
    funext i
    cases i <;>
      simp [FiniteNetwork.normalizedCoordinateError, hC, z, twoNodeCounterexamplePullA,
        identityMatrix] <;> ring
  have hcolA_false :
      FiniteNetwork.normalizedCoordinateError (fun node => inst.C 0 node false) false (inst.C_column_sum 0 false) = z epsilon := by
    apply Subtype.ext
    funext i
    cases i <;>
      simp [FiniteNetwork.normalizedCoordinateError, hC, z, twoNodeCounterexamplePullA,
        identityMatrix] <;> ring
  have hcolB_true :
      FiniteNetwork.normalizedCoordinateError (fun node => inst.C 1 node true) true (inst.C_column_sum 1 true) = z (-(1 / 4)) := by
    apply Subtype.ext
    funext i
    cases i <;>
      simp [FiniteNetwork.normalizedCoordinateError, hC, z, twoNodeCounterexamplePullB,
        identityMatrix] <;> ring
  have hcolB_false :
      FiniteNetwork.normalizedCoordinateError (fun node => inst.C 1 node false) false (inst.C_column_sum 1 false) = z epsilon := by
    apply Subtype.ext
    funext i
    cases i <;>
      simp [FiniteNetwork.normalizedCoordinateError, hC, z, twoNodeCounterexamplePullB,
        identityMatrix] <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcolA_true, hz_smul (-(1 / 2))]
    rw [scalarCorrectedLift_smul_real inst 1 (-(1 / 2)) (z 1)]
    dsimp [LA] at hLA_val
    rw [hLA_val]
    ring
  · rw [hcolA_false, hz_smul epsilon]
    rw [scalarCorrectedLift_smul_real inst 1 epsilon (z 1)]
    dsimp [LA] at hLA_val
    rw [hLA_val]
    ring
  · rw [hcolB_true, hz_smul (-(1 / 4))]
    rw [scalarCorrectedLift_smul_real inst 2 (-(1 / 4)) (z 1)]
    dsimp [LB] at hLB_val
    rw [hLB_val]
    ring
  · rw [hcolB_false, hz_smul epsilon]
    rw [scalarCorrectedLift_smul_real inst 2 epsilon (z 1)]
    dsimp [LB] at hLB_val
    rw [hLB_val]
    ring

/-- Concrete Appendix A.1 phase bridge from the `Setup.influence` API to the
printed period-two rows `b_A,b_B`. -/
private theorem two_step_counterexample_concrete_phase_influence_eq_noise_channels
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) (inst : Setup Bool ℝ)
    (hperiod : inst.period = 2)
    (hR : inst.R = (fun _ => twoNodeCounterexamplePush epsilon))
    (hC :
      ∀ t : ℕ,
        inst.C t =
          if t % 2 = 0 then
            twoNodeCounterexamplePullA epsilon
          else
            twoNodeCounterexamplePullB epsilon) :
    inst.influence 0 = twoStepCounterexampleNoiseChannelA epsilon ∧
      inst.influence 1 = twoStepCounterexampleNoiseChannelB epsilon := by
  classical
  have hperron :=
    two_step_counterexample_perronLeft_eq
      epsilon hepsilon_pos hepsilon_lt_half inst hperiod hR
  rcases
      two_step_counterexample_scalarCorrectedLift_pullColumn_values
        epsilon hepsilon_pos hepsilon_lt_half inst hperiod hR hC with
    ⟨hA_true, hA_false, hB_true, hB_false⟩
  constructor
  · funext i
    cases i
    · rw [inst.influence_apply_eq_perron_add_scalarCorrectedLift 0 false]
      simp only [Nat.zero_add]
      calc
        _ = inst.perronLeft 1 false +
            inst.scalarCorrectedLift 1
              (FiniteNetwork.normalizedCoordinateError
                (fun node => inst.C 0 node false) false
                (inst.C_column_sum 0 false)) := by
          congr 2
          apply Subtype.ext
          funext k
          cases k <;> simp [FiniteNetwork.normalizedCoordinateError]
        _ = _ := by
          rw [hA_false]
          simp [twoStepCounterexampleNoiseChannelA, hperron]
    · rw [inst.influence_apply_eq_perron_add_scalarCorrectedLift 0 true]
      simp only [Nat.zero_add]
      calc
        _ = inst.perronLeft 1 true +
            inst.scalarCorrectedLift 1
              (FiniteNetwork.normalizedCoordinateError
                (fun node => inst.C 0 node true) true
                (inst.C_column_sum 0 true)) := by
          congr 2
          apply Subtype.ext
          funext k
          cases k <;> simp [FiniteNetwork.normalizedCoordinateError]
        _ = _ := by
          rw [hA_true]
          simp [twoStepCounterexampleNoiseChannelA, hperron]
          ring
  · funext i
    cases i
    · rw [inst.influence_apply_eq_perron_add_scalarCorrectedLift 1 false]
      simp only [Nat.one_add]
      calc
        _ = inst.perronLeft 2 false +
            inst.scalarCorrectedLift 2
              (FiniteNetwork.normalizedCoordinateError
                (fun node => inst.C 1 node false) false
                (inst.C_column_sum 1 false)) := by
          congr 2
          apply Subtype.ext
          funext k
          cases k <;> simp [FiniteNetwork.normalizedCoordinateError]
        _ = _ := by
          rw [hB_false]
          simp [twoStepCounterexampleNoiseChannelB, hperron]
    · rw [inst.influence_apply_eq_perron_add_scalarCorrectedLift 1 true]
      simp only [Nat.one_add]
      calc
        _ = inst.perronLeft 2 true +
            inst.scalarCorrectedLift 2
              (FiniteNetwork.normalizedCoordinateError
                (fun node => inst.C 1 node true) true
                (inst.C_column_sum 1 true)) := by
          congr 2
          apply Subtype.ext
          funext k
          cases k <;> simp [FiniteNetwork.normalizedCoordinateError]
        _ = _ := by
          rw [hB_true]
          simp [twoStepCounterexampleNoiseChannelB, hperron]
          ring

/-- Concrete setup plus the Appendix A.1 influence coefficients.

This is the source bridge from the finite lifted two-step coefficient
calculation (`b_A,b_B`) to the abstract `Setup.influence*` API used by the
matching lower-bound theorem. -/
private theorem two_step_counterexample_setup_with_coefficients_exists
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) :
    ∃ inst : Setup Bool ℝ, ∃ lambda a : ℝ,
      FixedTwoNodeDeterministicPeriodicNetwork inst a ∧
        HomogeneousQuadraticComponents (Node := Bool) inst lambda ∧
          a = epsilon / 2 ∧ inst.L = 1 ∧ inst.Delta = 1 / 2 ∧
            inst.sigma = 1 ∧ lambda = 1 ∧
              inst.effectiveNodeCount =
                twoStepCounterexampleSpectralSlope epsilon ^ 2 /
                  twoStepCounterexampleNoiseCoefficient epsilon := by
  classical
  rcases two_step_counterexample_setup_core_exists
      epsilon hepsilon_pos hepsilon_lt_half with
    ⟨inst, lambda, a, hfixed, hquad, ha, hL, hDelta, hsigma, hlambda,
      hperiod, hR, hC⟩
  have hcoefficients :
      (Finset.expect Finset.univ (fun r : Fin inst.period => rowSum (inst.influence r.1))) = twoStepCounterexampleSpectralSlope epsilon ∧
        inst.influenceSecondMoment =
          twoStepCounterexampleNoiseCoefficient epsilon := by
    have hphase :=
      two_step_counterexample_concrete_phase_influence_eq_noise_channels
        epsilon hepsilon_pos hepsilon_lt_half inst hperiod hR hC
    exact
      two_step_counterexample_concrete_coefficients_from_phase_influence
        epsilon inst hperiod hphase.1 hphase.2
  have heff :
      inst.effectiveNodeCount =
        twoStepCounterexampleSpectralSlope epsilon ^ 2 /
          twoStepCounterexampleNoiseCoefficient epsilon := by
    unfold effectiveNodeCount
    rw [hcoefficients.1, hcoefficients.2]
  exact ⟨inst, lambda, a, hfixed, hquad, ha, hL, hDelta, hsigma, hlambda, heff⟩

/-- Final residual bookkeeping for Theorem 3.1.

Once the matching lower-bound expansion is available and the concrete
counterexample coefficients give a positive eventual leading-term gap, the
`o(T^{-1/2})` conjectured residual is eventually too small to close that gap. -/
private theorem noNetwork_residual_clause_of_matching_expansion_and_gap
    (C : ℝ) (inst : Setup Bool ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Bool ℝ)
    (hmatch :
      ∃ residual0 : ℕ → ℝ,
        LittleOInvSqrt residual0 ∧
          ∀ T : ℕ,
            inst.infConstantStepsizeStationarity μ oracle T =
              matchingQuadraticLeadingTerm (Node := Bool) inst lambda T +
                residual0 T)
    (hgap :
      ∃ gap : ℝ, 0 < gap ∧
        ∀ᶠ T : ℕ in Filter.atTop,
          1 ≤ T ∧
            C * inst.sigma *
                Real.sqrt (inst.L * inst.Delta /
                  ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
                gap * (Real.sqrt (T : ℝ))⁻¹ ≤
              matchingQuadraticLeadingTerm (Node := Bool) inst lambda T) :
    ∀ residual : ℕ → ℝ, OriginalLinearSpeedupResidualSmall residual →
      ∃ T : ℕ, 1 ≤ T ∧
        C * inst.sigma *
            Real.sqrt (inst.L * inst.Delta /
              ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
            residual T <
          inst.infConstantStepsizeStationarity μ oracle T := by
  classical
  intro residual hresidual
  rcases hmatch with ⟨residual0, hresidual0, hmatch_eq⟩
  rcases hgap with ⟨gap, hgap_pos, hgap_eventual⟩
  have hres_eventual :
      ∀ᶠ T : ℕ in Filter.atTop,
        residual T - residual0 T <
          gap * (Real.sqrt (T : ℝ))⁻¹ :=
    originalLinearSpeedupResidual_sub_littleOInvSqrt_eventually_lt_gap
      hresidual hresidual0 hgap_pos
  have hcombined :
      ∀ᶠ T : ℕ in Filter.atTop,
        1 ≤ T ∧
          C * inst.sigma *
              Real.sqrt (inst.L * inst.Delta /
                ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
              residual T <
            inst.infConstantStepsizeStationarity μ oracle T := by
    filter_upwards [hres_eventual, hgap_eventual] with T hresT hgapT
    rcases hgapT with ⟨hT, hleadT⟩
    constructor
    · exact hT
    · rw [hmatch_eq T]
      linarith
  rcases Filter.eventually_atTop.1 hcombined with ⟨T0, hT0⟩
  exact ⟨T0, hT0 T0 le_rfl⟩

/-- Scalar endgame for the two-node counterexample.

Once the concrete construction identifies the homogeneous quadratic constants
and `n_eff = s_epsilon^2/q_epsilon`, the strict coefficient inequality
`C < 2 sqrt(q_epsilon/s_epsilon^2)` gives a positive gap in front of
`T^{-1/2}`. -/
private theorem two_step_counterexample_matching_gap_from_coefficients
    (C epsilon : ℝ) (inst : Setup Bool ℝ) (lambda : ℝ)
    (hL : inst.L = 1) (hDelta : inst.Delta = 1 / 2)
    (hsigma : inst.sigma = 1) (hlambda : lambda = 1)
    (heff :
      inst.effectiveNodeCount =
        twoStepCounterexampleSpectralSlope epsilon ^ 2 /
          twoStepCounterexampleNoiseCoefficient epsilon)
    (hcoeff_gap :
      C < 2 * Real.sqrt
        (twoStepCounterexampleNoiseCoefficient epsilon /
          twoStepCounterexampleSpectralSlope epsilon ^ 2))
    (hslope_pos : 0 < twoStepCounterexampleSpectralSlope epsilon)
    (hnoiseCoeff_pos : 0 < twoStepCounterexampleNoiseCoefficient epsilon) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ᶠ T : ℕ in Filter.atTop,
        1 ≤ T ∧
          C * inst.sigma *
              Real.sqrt (inst.L * inst.Delta /
                ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
              gap * (Real.sqrt (T : ℝ))⁻¹ ≤
            matchingQuadraticLeadingTerm (Node := Bool) inst lambda T := by
  classical
  let s : ℝ := twoStepCounterexampleSpectralSlope epsilon
  let q : ℝ := twoStepCounterexampleNoiseCoefficient epsilon
  let coeff : ℝ := Real.sqrt (q / s ^ 2)
  let gap : ℝ := coeff - C / 2
  have hs_pos : 0 < s := by simpa [s] using hslope_pos
  have hq_pos : 0 < q := by simpa [q] using hnoiseCoeff_pos
  have hs_sq_pos : 0 < s ^ 2 := sq_pos_of_pos hs_pos
  have hratio_pos : 0 < q / s ^ 2 := div_pos hq_pos hs_sq_pos
  have hcoeff_pos : 0 < coeff := by
    dsimp [coeff]
    exact Real.sqrt_pos.2 hratio_pos
  have hgap_pos : 0 < gap := by
    dsimp [gap, coeff, s, q] at *
    linarith
  refine ⟨gap, hgap_pos, ?_⟩
  have hlarge : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  filter_upwards [hlarge] with T hT
  constructor
  · exact hT
  · have hT_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) :=
      Real.sqrt_pos.2 hT_pos
    have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsqrtT_pos
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    have hnode : (nodeCount (Node := Bool) : ℝ) = 2 := by
      simp [nodeCount]
    have hleft_sqrt :
        Real.sqrt (inst.L * inst.Delta /
            ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) =
          (1 / 2) * (Real.sqrt (T : ℝ))⁻¹ := by
      rw [hL, hDelta, hnode]
      have harg_nonneg : 0 ≤ (1 / 2 : ℝ) * (1 / 2) / (2 * (T : ℝ)) := by
        positivity
      apply sq_eq_sq_iff_eq_or_eq_neg.mp ?_ |>.elim
        (fun h => h)
        (fun h => by
          have hleft_nonneg :
              0 ≤ Real.sqrt ((1 : ℝ) * (1 / 2) / (2 * (T : ℝ))) :=
            Real.sqrt_nonneg _
          have hright_pos : 0 < (1 / 2 : ℝ) * (Real.sqrt (T : ℝ))⁻¹ := by
            positivity
          nlinarith)
      rw [Real.sq_sqrt]
      · field_simp [hsqrtT_ne]
        rw [Real.sq_sqrt hT_pos.le]
      · positivity
    have hmatch_sqrt :
        Real.sqrt (2 * lambda * inst.Delta /
            (inst.effectiveNodeCount * (T : ℝ))) =
          coeff * (Real.sqrt (T : ℝ))⁻¹ := by
      rw [hlambda, hDelta, heff]
      dsimp [coeff, s, q]
      apply sq_eq_sq_iff_eq_or_eq_neg.mp ?_ |>.elim
        (fun h => h)
        (fun h => by
          have hleft_nonneg :
              0 ≤ Real.sqrt (2 * (1 : ℝ) * (1 / 2) /
                ((s ^ 2 / q) * (T : ℝ))) :=
            Real.sqrt_nonneg _
          have hright_pos :
              0 < Real.sqrt (q / s ^ 2) * (Real.sqrt (T : ℝ))⁻¹ := by
            positivity
          nlinarith)
      rw [Real.sq_sqrt]
      · rw [mul_pow, Real.sq_sqrt hratio_pos.le]
        field_simp [hs_ne, hq_ne, hsqrtT_ne]
        rw [Real.sq_sqrt hT_pos.le]
        ring
      · positivity
    calc
      C * inst.sigma *
              Real.sqrt (inst.L * inst.Delta /
                ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
              gap * (Real.sqrt (T : ℝ))⁻¹ =
          coeff * (Real.sqrt (T : ℝ))⁻¹ := by
            rw [hsigma, hleft_sqrt]
            dsimp [gap]
            ring
      _ ≤ matchingQuadraticLeadingTerm (Node := Bool) inst lambda T := by
            unfold matchingQuadraticLeadingTerm
            rw [hmatch_sqrt, hsigma]
            simp

/-- The concrete encoding of `(time,node)` into the iid Bool stream is
injective. -/
private theorem pairIndex_injective_bool_time :
    Function.Injective
      (fun ti : ℕ × Bool => 2 * ti.1 + if ti.2 then 0 else 1) := by
  intro a b h
  rcases a with ⟨ta, ia⟩
  rcases b with ⟨tb, ib⟩
  cases ia <;> cases ib <;> simp at h ⊢ <;> omega

/-- Iid independence of the scaled half-Rademacher coordinates after the
two-node time/node encoding. -/
private theorem scaled_pairIndex_half_rademacher_iIndepFun :
    iIndepFun
      (fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
        (2 : ℝ) * canonicalHalfRademacherNoise ω
          ((fun q : ℕ × Bool => 2 * q.1 + if q.2 then 0 else 1) ti))
      canonicalHalfRademacherMeasure := by
  classical
  have hcoord :
      iIndepFun (fun n (ω : ℕ → Bool) => ω n)
        canonicalHalfRademacherMeasure := by
    simpa [canonicalHalfRademacherMeasure] using
      SOptLib.iidStreamLaw_iIndepFun_eval canonicalHalfRademacherMarginal
  have hscaled :
      iIndepFun
        (fun n : ℕ => fun ω : ℕ → Bool =>
          (2 : ℝ) * canonicalHalfRademacherNoise ω n)
        canonicalHalfRademacherMeasure := by
    have hmeas :
        ∀ n : ℕ,
          Measurable
            (fun b : Bool =>
              (2 : ℝ) * (if b then (1 / 2 : ℝ) else -(1 / 2))) :=
      fun _ => measurable_of_finite _
    simpa [canonicalHalfRademacherNoise, Function.comp_def] using
      hcoord.comp
        (fun _n : ℕ => fun b : Bool =>
          (2 : ℝ) * (if b then (1 / 2 : ℝ) else -(1 / 2)))
        hmeas
  simpa using
    hscaled.precomp pairIndex_injective_bool_time

/-- Any two scaled half-Rademacher stream coordinates have the same law. -/
private theorem scaled_half_rademacher_identDistrib (n m : ℕ) :
    IdentDistrib
      (fun ω : ℕ → Bool => (2 : ℝ) * canonicalHalfRademacherNoise ω n)
      (fun ω : ℕ → Bool => (2 : ℝ) * canonicalHalfRademacherNoise ω m)
      canonicalHalfRademacherMeasure canonicalHalfRademacherMeasure := by
  classical
  have hmap_n :
      Measure.map (fun ω : ℕ → Bool => ω n)
          canonicalHalfRademacherMeasure =
        canonicalHalfRademacherMarginal := by
    simpa [canonicalHalfRademacherMeasure] using
      SOptLib.iidStreamLaw_map_eval canonicalHalfRademacherMarginal n
  have hmap_m :
      Measure.map (fun ω : ℕ → Bool => ω m)
          canonicalHalfRademacherMeasure =
        canonicalHalfRademacherMarginal := by
    simpa [canonicalHalfRademacherMeasure] using
      SOptLib.iidStreamLaw_map_eval canonicalHalfRademacherMarginal m
  have hcoord :
      IdentDistrib (fun ω : ℕ → Bool => ω n)
        (fun ω : ℕ → Bool => ω m)
        canonicalHalfRademacherMeasure canonicalHalfRademacherMeasure := by
    refine ⟨(measurable_pi_apply n).aemeasurable,
      (measurable_pi_apply m).aemeasurable, ?_⟩
    rw [hmap_n, hmap_m]
  have hmeas :
      Measurable
        (fun b : Bool =>
          (2 : ℝ) * (if b then (1 / 2 : ℝ) else -(1 / 2))) :=
    measurable_of_finite _
  simpa [canonicalHalfRademacherNoise, Function.comp_def] using
    hcoord.comp hmeas

/-- The scaled half-Rademacher coordinate has mean zero. -/
private theorem scaled_half_rademacher_integral_eq_zero (n : ℕ) :
    (∫ ω : ℕ → Bool,
      (2 : ℝ) * canonicalHalfRademacherNoise ω n
        ∂canonicalHalfRademacherMeasure) = 0 := by
  classical
  let φ : Bool → ℝ :=
    fun b => (2 : ℝ) * (if b then (1 / 2 : ℝ) else -(1 / 2))
  have hmap :
      Measure.map (fun ω : ℕ → Bool => ω n)
          canonicalHalfRademacherMeasure =
        canonicalHalfRademacherMarginal := by
    simpa [canonicalHalfRademacherMeasure] using
      SOptLib.iidStreamLaw_map_eval canonicalHalfRademacherMarginal n
  have hmeas : AEMeasurable (fun ω : ℕ → Bool => ω n)
      canonicalHalfRademacherMeasure :=
    (measurable_pi_apply n).aemeasurable
  have hφ : AEStronglyMeasurable φ
      (Measure.map (fun ω : ℕ → Bool => ω n)
        canonicalHalfRademacherMeasure) := by
    exact (measurable_of_finite φ).aestronglyMeasurable
  calc
    (∫ ω : ℕ → Bool,
        (2 : ℝ) * canonicalHalfRademacherNoise ω n
          ∂canonicalHalfRademacherMeasure) =
        ∫ b : Bool, φ b
          ∂(Measure.map (fun ω : ℕ → Bool => ω n)
            canonicalHalfRademacherMeasure) := by
          change (∫ ω : ℕ → Bool, φ (ω n)
              ∂canonicalHalfRademacherMeasure) =
            ∫ b : Bool, φ b
              ∂(Measure.map (fun ω : ℕ → Bool => ω n)
                canonicalHalfRademacherMeasure)
          rw [← MeasureTheory.integral_map hmeas hφ]
    _ = ∫ b : Bool, φ b ∂canonicalHalfRademacherMarginal := by
          rw [hmap]
    _ = 0 := by
          rw [MeasureTheory.integral_fintype .of_finite]
          simp [φ, canonicalHalfRademacherMarginal,
            SOptLib.finiteBlockIndexLaw_singleton, Measure.real_def]

/-- The scaled half-Rademacher coordinate has unit second moment. -/
private theorem scaled_half_rademacher_second_moment_eq_one (n : ℕ) :
    (∫ ω : ℕ → Bool,
      ‖(2 : ℝ) * canonicalHalfRademacherNoise ω n‖ ^ 2
        ∂canonicalHalfRademacherMeasure) = 1 := by
  classical
  let φ : Bool → ℝ :=
    fun b => ‖(2 : ℝ) *
      (if b then (1 / 2 : ℝ) else -(1 / 2))‖ ^ 2
  have hmap :
      Measure.map (fun ω : ℕ → Bool => ω n)
          canonicalHalfRademacherMeasure =
        canonicalHalfRademacherMarginal := by
    simpa [canonicalHalfRademacherMeasure] using
      SOptLib.iidStreamLaw_map_eval canonicalHalfRademacherMarginal n
  have hmeas : AEMeasurable (fun ω : ℕ → Bool => ω n)
      canonicalHalfRademacherMeasure :=
    (measurable_pi_apply n).aemeasurable
  have hφ : AEStronglyMeasurable φ
      (Measure.map (fun ω : ℕ → Bool => ω n)
        canonicalHalfRademacherMeasure) := by
    exact (measurable_of_finite φ).aestronglyMeasurable
  calc
    (∫ ω : ℕ → Bool,
        ‖(2 : ℝ) * canonicalHalfRademacherNoise ω n‖ ^ 2
          ∂canonicalHalfRademacherMeasure) =
        ∫ b : Bool, φ b
          ∂(Measure.map (fun ω : ℕ → Bool => ω n)
            canonicalHalfRademacherMeasure) := by
          change (∫ ω : ℕ → Bool, φ (ω n)
              ∂canonicalHalfRademacherMeasure) =
            ∫ b : Bool, φ b
              ∂(Measure.map (fun ω : ℕ → Bool => ω n)
                canonicalHalfRademacherMeasure)
          rw [← MeasureTheory.integral_map hmeas hφ]
    _ = ∫ b : Bool, φ b ∂canonicalHalfRademacherMarginal := by
          rw [hmap]
    _ = 1 := by
          rw [MeasureTheory.integral_fintype .of_finite]
          simp [φ, canonicalHalfRademacherMarginal,
            SOptLib.finiteBlockIndexLaw_singleton, Measure.real_def,
            Real.norm_eq_abs]

/-- Pointwise unit squared norm of the scaled half-Rademacher coordinate. -/
private theorem scaled_half_rademacher_norm_sq_eq_one
    (ω : ℕ → Bool) (n : ℕ) :
    ‖(2 : ℝ) * canonicalHalfRademacherNoise ω n‖ ^ 2 = 1 := by
  cases h : ω n <;>
    simp [canonicalHalfRademacherNoise, h, Real.norm_eq_abs]

/-- The canonical two-node oracle strict past is generated by the scalar
time/node noise coordinates with earlier time index. -/
private theorem canonical_pair_oracle_strictPast_le_coordinate_past_iSup
    (oracle : OracleNoiseProcess (ℕ → Bool) Bool ℝ) (t : ℕ) :
    oracle.strictPastMeasurableSpace t ≤
      ⨆ q ∈ ({q : ℕ × Bool | q.1 < t} : Set (ℕ × Bool)),
        MeasurableSpace.comap
          (fun ω : ℕ → Bool => oracle.noise ω q.1 q.2) inferInstance := by
  simpa [OracleNoiseProcess.strictPastMeasurableSpace_eq,
    OracleNoiseProcess.noiseStream] using
      (pi_prefixMeasurableSpace_le_timeCoordinate_iSup
        (xi := oracle.noiseStream) t)

/-- A current canonical two-node oracle coordinate is independent of the
strict-past sigma-algebra generated by earlier noise tables. -/
private theorem canonical_pair_oracle_current_indep_strictPast
    (oracle : OracleNoiseProcess (ℕ → Bool) Bool ℝ)
    (μ : Measure (ℕ → Bool))
    (hraw_iIndep :
      iIndepFun
        (fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
          oracle.noise ω ti.1 ti.2) μ)
    (t : ℕ) (i : Bool) :
    Indep (oracle.strictPastMeasurableSpace t)
      (MeasurableSpace.comap
        (fun ω : ℕ → Bool => oracle.noise ω t i) inferInstance) μ := by
  refine
    SOptLib.iIndepFun_indep_strictPast_singleton
      (xi := fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
        oracle.noise ω ti.1 ti.2)
      (mu := μ)
      (strictPast := oracle.strictPastMeasurableSpace t)
      (pastSet := ({q : ℕ × Bool | q.1 < t} : Set (ℕ × Bool)))
      (current := (t, i))
      ?hxi_meas hraw_iIndep ?hpast_disj ?hstrict_le
  · intro q
    simpa using
      (measurable_pi_apply q.2).comp (oracle.noise_measurable q.1)
  · rw [Set.disjoint_left]
    intro q hq hcurrent
    rw [Set.mem_singleton_iff] at hcurrent
    subst q
    exact (Nat.lt_irrefl t hq)
  · simpa using
      canonical_pair_oracle_strictPast_le_coordinate_past_iSup oracle t

/-- A fresh event independent of the past has the constant event probability
as a paper conditional-probability version. -/
private theorem paper_conditional_probability_version_const_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 mfresh : MeasurableSpace Ω} {event : Set Ω}
    (hevent : @MeasurableSet Ω mΩ event)
    (hevent_fresh : @MeasurableSet Ω mfresh event)
    (hindep : Indep 𝓕 mfresh μ) :
    @PaperConditionalProbabilityVersion Ω mΩ μ _ 𝓕 event
      (fun _ : Ω => μ.real event) := by
  refine ⟨measurable_const, ?_, ?_⟩
  · filter_upwards with ω
    exact ⟨measureReal_nonneg, (measureReal_le_one : μ.real event ≤ 1)⟩
  · intro A hA
    have hInt :
        ∫ ω in A, event.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
          μ.real event * μ.real A := by
      exact @setIntegral_indicator_eq_prob_mul_of_indep Ω mΩ μ 𝓕 mfresh
        event A (μ.real event) hevent hevent_fresh hA hindep rfl
    have hIndicator :
        ∫ ω in A, event.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
          μ.real (A ∩ event) := by
      change ∫ ω, event.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.restrict A =
        μ.real (A ∩ event)
      calc
        ∫ ω, event.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.restrict A =
            (μ.restrict A).real event := by
              exact integral_indicator_one (μ := μ.restrict A) (s := event) hevent
        _ = μ.real (A ∩ event) := by
              rw [measureReal_restrict_apply hevent]
              rw [Set.inter_comm]
    calc
      (∫ ω in A, (fun _ : Ω => μ.real event) ω ∂μ) =
          μ.real event * μ.real A := by
            rw [MeasureTheory.integral_const]
            simp [measureReal_def]
            ring
      _ = μ.real (A ∩ event) := by
            rw [← hInt, hIndicator]

/-- Two sequential fresh-event factorizations give a constant conditional
probability version for a two-coordinate cylinder over `Bool`. -/
private theorem paper_conditional_probability_version_bool_pair_const_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 mtrue mfalse : MeasurableSpace Ω} {hitTrue hitFalse : Set Ω}
    (htrue : @MeasurableSet Ω mΩ hitTrue)
    (hfalse : @MeasurableSet Ω mΩ hitFalse)
    (htrue_fresh : @MeasurableSet Ω mtrue hitTrue)
    (hfalse_fresh : @MeasurableSet Ω mfalse hitFalse)
    (htrue_indep : Indep 𝓕 mtrue μ)
    (hfalse_indep : Indep (𝓕 ⊔ mtrue) mfalse μ) :
    @PaperConditionalProbabilityVersion Ω mΩ μ _ 𝓕 (hitFalse ∩ hitTrue)
      (fun _ : Ω => μ.real hitFalse * μ.real hitTrue) := by
  refine ⟨measurable_const, ?_, ?_⟩
  · filter_upwards with ω
    have hfalse_nonneg : 0 ≤ μ.real hitFalse := measureReal_nonneg
    have htrue_nonneg : 0 ≤ μ.real hitTrue := measureReal_nonneg
    have hfalse_le : μ.real hitFalse ≤ 1 :=
      (measureReal_le_one : μ.real hitFalse ≤ 1)
    have htrue_le : μ.real hitTrue ≤ 1 :=
      (measureReal_le_one : μ.real hitTrue ≤ 1)
    constructor
    · exact mul_nonneg hfalse_nonneg htrue_nonneg
    · have hmul :
          μ.real hitFalse * μ.real hitTrue ≤ (1 : ℝ) * 1 :=
        mul_le_mul hfalse_le htrue_le htrue_nonneg (by norm_num)
      simpa using hmul
  · intro A hA
    have htrueInt :
        ∫ ω in A, hitTrue.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
          μ.real hitTrue * μ.real A := by
      exact @setIntegral_indicator_eq_prob_mul_of_indep Ω mΩ μ 𝓕 mtrue
        hitTrue A (μ.real hitTrue) htrue htrue_fresh hA htrue_indep rfl
    have htrueIndicator :
        ∫ ω in A, hitTrue.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
          μ.real (A ∩ hitTrue) := by
      change ∫ ω, hitTrue.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.restrict A =
        μ.real (A ∩ hitTrue)
      calc
        ∫ ω, hitTrue.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.restrict A =
            (μ.restrict A).real hitTrue := by
              exact integral_indicator_one (μ := μ.restrict A) (s := hitTrue) htrue
        _ = μ.real (A ∩ hitTrue) := by
              rw [measureReal_restrict_apply htrue]
              rw [Set.inter_comm]
    have htrueMeasure :
        μ.real (A ∩ hitTrue) = μ.real hitTrue * μ.real A := by
      rw [← htrueIndicator, htrueInt]
    have hA_sup : @MeasurableSet Ω (𝓕 ⊔ mtrue) A :=
      (le_sup_left : 𝓕 ≤ 𝓕 ⊔ mtrue) A hA
    have hhitTrue_sup : @MeasurableSet Ω (𝓕 ⊔ mtrue) hitTrue :=
      (le_sup_right : mtrue ≤ 𝓕 ⊔ mtrue) hitTrue htrue_fresh
    have hAtrue_sup : @MeasurableSet Ω (𝓕 ⊔ mtrue) (A ∩ hitTrue) :=
      hA_sup.inter hhitTrue_sup
    have hfalseInt :
        ∫ ω in A ∩ hitTrue, hitFalse.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
          μ.real hitFalse * μ.real (A ∩ hitTrue) := by
      exact @setIntegral_indicator_eq_prob_mul_of_indep Ω mΩ μ
        (𝓕 ⊔ mtrue) mfalse hitFalse (A ∩ hitTrue)
        (μ.real hitFalse) hfalse hfalse_fresh hAtrue_sup hfalse_indep rfl
    have hfalseIndicator :
        ∫ ω in A ∩ hitTrue, hitFalse.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
          μ.real ((A ∩ hitTrue) ∩ hitFalse) := by
      change
        ∫ ω, hitFalse.indicator (fun _ : Ω => (1 : ℝ)) ω
            ∂μ.restrict (A ∩ hitTrue) =
          μ.real ((A ∩ hitTrue) ∩ hitFalse)
      calc
        ∫ ω, hitFalse.indicator (fun _ : Ω => (1 : ℝ)) ω
            ∂μ.restrict (A ∩ hitTrue) =
            (μ.restrict (A ∩ hitTrue)).real hitFalse := by
              exact integral_indicator_one (μ := μ.restrict (A ∩ hitTrue))
                (s := hitFalse) hfalse
        _ = μ.real ((A ∩ hitTrue) ∩ hitFalse) := by
              rw [measureReal_restrict_apply hfalse]
              rw [Set.inter_comm]
    have hfalseMeasure :
        μ.real ((A ∩ hitTrue) ∩ hitFalse) =
          μ.real hitFalse * μ.real (A ∩ hitTrue) := by
      rw [← hfalseIndicator, hfalseInt]
    have hsets :
        A ∩ (hitFalse ∩ hitTrue) = (A ∩ hitTrue) ∩ hitFalse := by
      ext ω
      constructor <;> intro hω
      · exact ⟨⟨hω.1, hω.2.2⟩, hω.2.1⟩
      · exact ⟨hω.1.1, ⟨hω.2, hω.1.2⟩⟩
    calc
      (∫ ω in A,
          (fun _ : Ω => μ.real hitFalse * μ.real hitTrue) ω ∂μ) =
          (μ.real hitFalse * μ.real hitTrue) * μ.real A := by
            rw [MeasureTheory.integral_const]
            simp [measureReal_def]
            ring
      _ = μ.real hitFalse * μ.real (A ∩ hitTrue) := by
            rw [htrueMeasure]
            ring
      _ = μ.real ((A ∩ hitTrue) ∩ hitFalse) := by
            rw [hfalseMeasure]
      _ = μ.real (A ∩ (hitFalse ∩ hitTrue)) := by
            rw [hsets]

/-- For the canonical pair-indexed oracle, the strict past together with one
same-time coordinate is independent of the other same-time coordinate. -/
private theorem canonical_pair_oracle_current_sup_peer_indep
    (oracle : OracleNoiseProcess (ℕ → Bool) Bool ℝ)
    (μ : Measure (ℕ → Bool))
    (hraw_iIndep :
      iIndepFun
        (fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
          oracle.noise ω ti.1 ti.2) μ)
    (t : ℕ) :
    Indep
      (oracle.strictPastMeasurableSpace t ⊔
        MeasurableSpace.comap
          (fun ω : ℕ → Bool => oracle.noise ω t true) inferInstance)
      (MeasurableSpace.comap
        (fun ω : ℕ → Bool => oracle.noise ω t false) inferInstance) μ := by
  refine
    SOptLib.iIndepFun_indep_strictPast_sup_coordinate_singleton
      (xi := fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
        oracle.noise ω ti.1 ti.2)
      (mu := μ)
      (strictPast := oracle.strictPastMeasurableSpace t)
      (pastSet := ({q : ℕ × Bool | q.1 < t} : Set (ℕ × Bool)))
      (peer := (t, true)) (current := (t, false))
      ?hxi_meas hraw_iIndep ?hleft_disj ?hstrict_le
  · intro q
    simpa using
      (measurable_pi_apply q.2).comp (oracle.noise_measurable q.1)
  · rw [Set.disjoint_left]
    intro q hleft hcurrent
    rw [Set.mem_singleton_iff] at hcurrent
    subst q
    rcases hleft with hpast | hpeer
    · exact Nat.lt_irrefl t hpast
    · rw [Set.mem_singleton_iff] at hpeer
      exact Bool.noConfusion (Prod.ext_iff.mp hpeer).2
  · simpa using
      canonical_pair_oracle_strictPast_le_coordinate_past_iSup oracle t

/-- The canonical iid pair oracle satisfies the paper same-time conditional
independence clause with constant node-event probabilities. -/
private theorem canonical_pair_oracle_sameTime_condIndep_given_strictPast
    (oracle : OracleNoiseProcess (ℕ → Bool) Bool ℝ)
    (hraw_iIndep :
      iIndepFun
        (fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
          oracle.noise ω ti.1 ti.2) canonicalHalfRademacherMeasure)
    (hcurrent_indep :
      ∀ t : ℕ, ∀ i : Bool,
        Indep (oracle.strictPastMeasurableSpace t)
          (MeasurableSpace.comap
            (fun ω : ℕ → Bool => oracle.noise ω t i) inferInstance)
          canonicalHalfRademacherMeasure)
    (t : ℕ) :
    PaperSameTimeNodeConditionallyIndependentGiven
      canonicalHalfRademacherMeasure (oracle.strictPastMeasurableSpace t)
      oracle t := by
  classical
  unfold PaperSameTimeNodeConditionallyIndependentGiven
  intro events hevents
  let μ : Measure (ℕ → Bool) := canonicalHalfRademacherMeasure
  let hit : Bool → Set (ℕ → Bool) :=
    fun i => {ω : ℕ → Bool | oracle.noise ω t i ∈ events i}
  let condProb : Bool → (ℕ → Bool) → ℝ :=
    fun i _ => μ.real (hit i)
  refine ⟨condProb, ?_, ?_⟩
  · intro i
    have hcoord : Measurable (fun ω : ℕ → Bool => oracle.noise ω t i) := by
      simpa using
        (measurable_pi_apply i).comp (oracle.noise_measurable t)
    refine
      paper_conditional_probability_version_const_of_indep
        (μ := μ)
        (𝓕 := oracle.strictPastMeasurableSpace t)
        (mfresh := MeasurableSpace.comap
          (fun ω : ℕ → Bool => oracle.noise ω t i) inferInstance)
        (event := hit i) ?_ ?_ ?_
    · exact (hevents i).preimage hcoord
    · dsimp [hit]
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨events i, hevents i, rfl⟩
    · simpa [μ] using hcurrent_indep t i
  · have hcoord_true :
        Measurable (fun ω : ℕ → Bool => oracle.noise ω t true) := by
      simpa using
        (measurable_pi_apply true).comp (oracle.noise_measurable t)
    have hcoord_false :
        Measurable (fun ω : ℕ → Bool => oracle.noise ω t false) := by
      simpa using
        (measurable_pi_apply false).comp (oracle.noise_measurable t)
    have htrue : MeasurableSet (hit true) :=
      (hevents true).preimage hcoord_true
    have hfalse : MeasurableSet (hit false) :=
      (hevents false).preimage hcoord_false
    have htrue_fresh :
        @MeasurableSet (ℕ → Bool)
          (MeasurableSpace.comap
            (fun ω : ℕ → Bool => oracle.noise ω t true) inferInstance)
          (hit true) := by
      dsimp [hit]
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨events true, hevents true, rfl⟩
    have hfalse_fresh :
        @MeasurableSet (ℕ → Bool)
          (MeasurableSpace.comap
            (fun ω : ℕ → Bool => oracle.noise ω t false) inferInstance)
          (hit false) := by
      dsimp [hit]
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨events false, hevents false, rfl⟩
    have hpair :
        @PaperConditionalProbabilityVersion (ℕ → Bool) _ μ _
          (oracle.strictPastMeasurableSpace t) (hit false ∩ hit true)
          (fun _ : ℕ → Bool => μ.real (hit false) * μ.real (hit true)) := by
      refine
        paper_conditional_probability_version_bool_pair_const_of_indep
          (μ := μ)
          (𝓕 := oracle.strictPastMeasurableSpace t)
          (mtrue := MeasurableSpace.comap
            (fun ω : ℕ → Bool => oracle.noise ω t true) inferInstance)
          (mfalse := MeasurableSpace.comap
            (fun ω : ℕ → Bool => oracle.noise ω t false) inferInstance)
          (hitTrue := hit true) (hitFalse := hit false)
          htrue hfalse htrue_fresh hfalse_fresh ?_ ?_
      · simpa [μ] using hcurrent_indep t true
      · simpa [μ] using
          canonical_pair_oracle_current_sup_peer_indep
            oracle canonicalHalfRademacherMeasure hraw_iIndep t
    have hjoint_set :
        {ω : ℕ → Bool | ∀ i : Bool, oracle.noise ω t i ∈ events i} =
          hit false ∩ hit true := by
      ext ω
      constructor
      · intro hω
        exact ⟨hω false, hω true⟩
      · intro hω i
        cases i
        · simpa [hit] using hω.1
        · simpa [hit] using hω.2
    have hprod_fun :
        (fun ω : ℕ → Bool => ∏ i : Bool, condProb i ω) =
          fun _ : ℕ → Bool => μ.real (hit false) * μ.real (hit true) := by
      funext ω
      simp [condProb]
      ring
    rw [hjoint_set, hprod_fun]
    exact hpair

/-- Concrete iid Rademacher oracle for the two-node quadratic instance.

The construction uses the canonical iid Bool stream and an injective encoding
of `(time,node)` into stream coordinates. The remaining proof obligation is the
bridge from this product law to the source-shaped strict-past oracle predicate
inside `ExactVarianceIidAdditiveNoise`. -/
private theorem two_step_counterexample_exact_iid_rademacher_oracle_exists
    (inst : Setup Bool ℝ) (hsigma : inst.sigma = 1) :
    ∃ Ω : Type, ∃ mΩ : MeasurableSpace Ω,
      letI : MeasurableSpace Ω := mΩ
      ∃ μ : Measure Ω, ∃ hprob : IsProbabilityMeasure μ,
        letI : IsProbabilityMeasure μ := hprob
        ∃ oracle : OracleNoiseProcess Ω Bool ℝ,
          inst.ExactVarianceIidAdditiveNoise μ oracle := by
  classical
  let pairIndex : ℕ × Bool → ℕ := fun ti => 2 * ti.1 + if ti.2 then 0 else 1
  let oracle : OracleNoiseProcess (ℕ → Bool) Bool ℝ := {
    noise := fun ω t i =>
      2 * canonicalHalfRademacherNoise ω (pairIndex (t, i))
    noise_measurable := by
      intro t
      refine measurable_pi_lambda
        (fun ω : ℕ → Bool => fun i : Bool =>
          2 * canonicalHalfRademacherNoise ω (pairIndex (t, i))) ?_
      intro i
      have hcoord : Measurable fun ω : ℕ → Bool => ω (pairIndex (t, i)) :=
        measurable_pi_apply (pairIndex (t, i))
      have hhalf :
          Measurable fun b : Bool => if b then (1 / 2 : ℝ) else -(1 / 2) :=
        measurable_of_finite _
      simpa [canonicalHalfRademacherNoise] using
        (hhalf.comp hcoord).const_mul 2 }
  have hraw_iid :
      iIndepFun
        (fun ti : ℕ × Bool => fun ω : ℕ → Bool =>
          oracle.noise ω ti.1 ti.2) canonicalHalfRademacherMeasure ∧
        (∀ t i s j,
          IdentDistrib (fun ω : ℕ → Bool => oracle.noise ω t i)
            (fun ω : ℕ → Bool => oracle.noise ω s j)
            canonicalHalfRademacherMeasure canonicalHalfRademacherMeasure) ∧
          (∀ t i,
            ∫ ω : ℕ → Bool, oracle.noise ω t i
              ∂canonicalHalfRademacherMeasure = 0) ∧
            ∀ t i,
              ∫ ω : ℕ → Bool, ‖oracle.noise ω t i‖ ^ 2
                ∂canonicalHalfRademacherMeasure = inst.sigma ^ 2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [oracle, pairIndex] using
        scaled_pairIndex_half_rademacher_iIndepFun
    · intro t i s j
      simpa [oracle, pairIndex] using
        scaled_half_rademacher_identDistrib (pairIndex (t, i))
          (pairIndex (s, j))
    · intro t i
      simpa [oracle, pairIndex] using
        scaled_half_rademacher_integral_eq_zero (pairIndex (t, i))
    · intro t i
      calc
        (∫ ω : ℕ → Bool, ‖oracle.noise ω t i‖ ^ 2
            ∂canonicalHalfRademacherMeasure) = 1 := by
              simpa [oracle, pairIndex] using
                scaled_half_rademacher_second_moment_eq_one
                  (pairIndex (t, i))
        _ = inst.sigma ^ 2 := by
              rw [hsigma]
              norm_num
  have hnoise :
      inst.ExactVarianceIidAdditiveNoise canonicalHalfRademacherMeasure oracle := by
    unfold ExactVarianceIidAdditiveNoise
    refine ⟨?hstoch, ?hsigma_pos, ?hraw_iid⟩
    · -- Product-coordinate independence should imply the source-shaped
      -- strict-past conditional mean, second-moment, and same-time
      -- conditional independence clauses.
      have hcurrent_indep :
          ∀ t : ℕ, ∀ i : Bool,
            Indep (oracle.strictPastMeasurableSpace t)
              (MeasurableSpace.comap
                (fun ω : ℕ → Bool => oracle.noise ω t i) inferInstance)
              canonicalHalfRademacherMeasure := by
        intro t i
        exact canonical_pair_oracle_current_indep_strictPast
          oracle canonicalHalfRademacherMeasure hraw_iid.1 t i
      have hunit_second :
          ∀ t : ℕ, ∀ i : Bool, ∀ ω : ℕ → Bool,
            ‖oracle.noise ω t i‖ ^ 2 = 1 := by
        intro t i ω
        simpa [oracle, pairIndex] using
          scaled_half_rademacher_norm_sq_eq_one ω (pairIndex (t, i))
      unfold StochasticOracleAssumptions
      refine ⟨?hmean, ?hsecond, ?hsame⟩
      · intro t i
        unfold PaperConditionalMeanZeroGiven
        let Y : (ℕ → Bool) → ℝ := fun ω => oracle.noise ω t i
        have hY_meas : Measurable Y := by
          simpa [Y] using
            (measurable_pi_apply i).comp (oracle.noise_measurable t)
        have hY_bound : ∀ ω : ℕ → Bool, ‖Y ω‖ ≤ (1 : ℝ) := by
          intro ω
          have hsq : ‖Y ω‖ ^ 2 = 1 := by
            simpa [Y] using hunit_second t i ω
          nlinarith [sq_nonneg (‖Y ω‖ - 1)]
        have hY_int : Integrable Y canonicalHalfRademacherMeasure :=
          integrable_of_measurable_bounded_real hY_meas hY_bound
        refine ⟨hY_int, ?_⟩
        intro A hA
        have hA_top : MeasurableSet A :=
          (strictPastMeasurableSpace_le (Node := Bool) (E := ℝ)
            oracle t) A hA
        let X : (ℕ → Bool) → ℝ :=
          fun ω => A.indicator (fun _ : ℕ → Bool => (1 : ℝ)) ω
        have hX_past :
            Measurable[oracle.strictPastMeasurableSpace t] X := by
          simpa [X] using
            (measurable_const :
              Measurable[oracle.strictPastMeasurableSpace t]
                (fun _ : ℕ → Bool => (1 : ℝ))).indicator hA
        have hX_meas : Measurable X := by
          simpa [X] using
            (measurable_const :
              Measurable (fun _ : ℕ → Bool => (1 : ℝ))).indicator hA_top
        have hXY_int :
            Integrable (fun ω : ℕ → Bool => X ω * Y ω)
              canonicalHalfRademacherMeasure := by
          refine integrable_of_measurable_bounded_real
            (hX_meas.mul hY_meas) (C := (1 : ℝ)) ?_
          intro ω
          have hX_bound : ‖X ω‖ ≤ (1 : ℝ) := by
            by_cases hω : ω ∈ A <;> simp [X, hω]
          calc
            ‖X ω * Y ω‖ = ‖X ω‖ * ‖Y ω‖ := by
              rw [norm_mul]
            _ ≤ (1 : ℝ) * 1 := by
              exact mul_le_mul hX_bound (hY_bound ω) (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        have hXY_indep : IndepFun X Y canonicalHalfRademacherMeasure :=
          indepFun_of_measurable_left_of_indep_comap hX_past
            (by simpa [Y] using hcurrent_indep t i)
        have hY_map_mean :
            (∫ y : ℝ, y ∂Measure.map Y canonicalHalfRademacherMeasure) = 0 := by
          calc
            (∫ y : ℝ, y ∂Measure.map Y canonicalHalfRademacherMeasure) =
                ∫ ω : ℕ → Bool, Y ω ∂canonicalHalfRademacherMeasure := by
              simpa using
                (MeasureTheory.integral_map hY_meas.aemeasurable
                  (measurable_id.aestronglyMeasurable :
                    AEStronglyMeasurable (fun y : ℝ => y)
                      (Measure.map Y canonicalHalfRademacherMeasure)))
            _ = 0 := by
              simpa [Y] using hraw_iid.2.2.1 t i
        have hfixed_zero :
            ∀ a : ℝ,
              (∫ y : ℝ, a * y
                ∂Measure.map Y canonicalHalfRademacherMeasure) = 0 := by
          intro a
          rw [integral_const_mul, hY_map_mean, mul_zero]
        have hcancel :
            (∫ ω : ℕ → Bool, X ω * Y ω
              ∂canonicalHalfRademacherMeasure) = 0 := by
          refine integral_comp_eq_zero_of_indep_fixed_integral_zero
            (P := canonicalHalfRademacherMeasure)
            (ν := Measure.map Y canonicalHalfRademacherMeasure)
            (φ := fun a : ℝ => fun y : ℝ => a * y)
            (X := X) (Y := Y)
            ?_ hX_meas hY_meas hXY_indep rfl hXY_int hfixed_zero
          change Measurable (fun p : ℝ × ℝ => p.1 * p.2)
          exact measurable_fst.mul measurable_snd
        rw [← MeasureTheory.integral_indicator hA_top]
        have hindicator_eq :
            (fun ω : ℕ → Bool => A.indicator Y ω) =
              fun ω : ℕ → Bool => X ω * Y ω := by
          funext ω
          by_cases hω : ω ∈ A <;> simp [X, Y, hω]
        rw [hindicator_eq]
        exact hcancel
      · intro t i
        unfold PaperConditionalSecondMomentBoundGiven
        refine ⟨?hint, ?hbound⟩
        · have hconst :
              (fun ω : ℕ → Bool => ‖oracle.noise ω t i‖ ^ 2) =
                fun _ : ℕ → Bool => (1 : ℝ) := by
            funext ω
            exact hunit_second t i ω
          rw [hconst]
          exact integrable_const (1 : ℝ)
        · intro A hA
          have hfun :
              (fun ω : ℕ → Bool => ‖oracle.noise ω t i‖ ^ 2) =
                fun ω : ℕ → Bool =>
                  (Set.univ : Set (ℕ → Bool)).indicator
                    (fun _ : ℕ → Bool => (1 : ℝ)) ω := by
            funext ω
            rw [hunit_second t i ω]
            simp
          rw [hfun]
          have hInt :
              ∫ ω in A,
                  (Set.univ : Set (ℕ → Bool)).indicator
                    (fun _ : ℕ → Bool => (1 : ℝ)) ω
                    ∂canonicalHalfRademacherMeasure =
                (1 : ℝ) * canonicalHalfRademacherMeasure.real A := by
            refine setIntegral_indicator_eq_prob_mul_of_indep
              (μ := canonicalHalfRademacherMeasure)
              (m := oracle.strictPastMeasurableSpace t)
              (mfresh := MeasurableSpace.comap
                (fun ω : ℕ → Bool => oracle.noise ω t i) inferInstance)
              (hit := (Set.univ : Set (ℕ → Bool))) (s := A)
              (p := (1 : ℝ)) ?_ ?_ hA (hcurrent_indep t i) ?_
            · exact MeasurableSet.univ
            · exact MeasurableSet.univ
            · simp [measureReal_def]
          rw [hInt, hsigma]
          norm_num
      · intro t
        exact canonical_pair_oracle_sameTime_condIndep_given_strictPast
          oracle hraw_iid.1 hcurrent_indep t
    · rw [hsigma]
      norm_num
    · -- Raw iid/identical distribution and the zero-mean/unit-variance
      -- clauses should follow from `canonicalHalfRademacherNoise_spec`,
      -- `SOptLib.iidStreamLaw_iIndepFun_eval`, and
      -- `SOptLib.iidStreamLaw_map_eval` after the `pairIndex` injection.
      exact hraw_iid
  refine ⟨ℕ → Bool, inferInstance, canonicalHalfRademacherMeasure,
    inferInstance, oracle, ?_⟩
  exact hnoise

/-- Source-specific witness package for Theorem 3.1, stopping exactly before
the generic residual bookkeeping.

This is the remaining concrete construction debt: the two-node
`R_epsilon,A_epsilon,B_epsilon` setup, a homogeneous quadratic instance, an
iid exact-variance oracle, and the leading-coefficient gap obtained from
`q_epsilon / s_epsilon^2`. -/
private theorem two_step_counterexample_witness_with_matching_gap
    (C : ℝ) :
    ∃ inst : Setup Bool ℝ, ∃ lambda a : ℝ,
      ∃ Ω : Type, ∃ mΩ : MeasurableSpace Ω,
        letI : MeasurableSpace Ω := mΩ
        ∃ μ : Measure Ω, ∃ hprob : IsProbabilityMeasure μ,
          letI : IsProbabilityMeasure μ := hprob
          ∃ oracle : OracleNoiseProcess Ω Bool ℝ,
            FixedTwoNodeDeterministicPeriodicNetwork inst a ∧
              HomogeneousQuadraticComponents (Node := Bool) inst lambda ∧
                inst.ExactVarianceIidAdditiveNoise μ oracle ∧
                  C ≤ a⁻¹ ∧
                    ∃ gap : ℝ, 0 < gap ∧
                      ∀ᶠ T : ℕ in Filter.atTop,
                        1 ≤ T ∧
                          C * inst.sigma *
                              Real.sqrt (inst.L * inst.Delta /
                                ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
                              gap * (Real.sqrt (T : ℝ))⁻¹ ≤
                            matchingQuadraticLeadingTerm (Node := Bool)
                              inst lambda T := by
  classical
  rcases two_step_counterexample_exists_epsilon_for_constant_and_gap C with
    ⟨epsilon, hepsilon_pos, hepsilon_lt_half, hC_le, hcoeff_gap,
      hslope_pos, hnoiseCoeff_pos⟩
  rcases two_step_counterexample_setup_with_coefficients_exists
      epsilon hepsilon_pos hepsilon_lt_half with
    ⟨inst, lambda, a, hfixed, hquad, ha, hL, hDelta, hsigma, hlambda, heff⟩
  have hC_le_a : C ≤ a⁻¹ := by
    rw [ha]
    exact hC_le
  have hgap :
      ∃ gap : ℝ, 0 < gap ∧
        ∀ᶠ T : ℕ in Filter.atTop,
          1 ≤ T ∧
            C * inst.sigma *
                Real.sqrt (inst.L * inst.Delta /
                  ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
                gap * (Real.sqrt (T : ℝ))⁻¹ ≤
              matchingQuadraticLeadingTerm (Node := Bool) inst lambda T :=
    two_step_counterexample_matching_gap_from_coefficients
      C epsilon inst lambda hL hDelta hsigma hlambda heff hcoeff_gap
      hslope_pos hnoiseCoeff_pos
  refine ⟨inst, lambda, a, ?_⟩
  rcases two_step_counterexample_exact_iid_rademacher_oracle_exists
      inst hsigma with
    ⟨Ω, mΩ, μ, hprob, oracle, hnoise⟩
  refine ⟨Ω, mΩ, μ, hprob, oracle, ?_⟩
  exact ⟨hfixed, hquad, hnoise, hC_le_a, hgap⟩

/-- Theorem 3.1: no network-independent numerical dominant constant can cover
the original linear-speedup conjecture; the required constant may grow like
`1/a` as the minimum positive network weight `a` degenerates. -/
theorem NoNetworkIndependentDominantConstant :
    ∀ C : ℝ, NetworkIndependentDominantConstantCounterexample C := by
  classical
  intro C
  have hmatching_visible :
      ∀ (inst : Setup Bool ℝ) (lambda : ℝ)
        {Ω : Type} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (oracle : OracleNoiseProcess Ω Bool ℝ),
          HomogeneousQuadraticComponents (Node := Bool) inst lambda →
            inst.ExactVarianceIidAdditiveNoise μ oracle →
              ∃ residual0 : ℕ → ℝ,
                LittleOInvSqrt residual0 ∧
                  ∀ T : ℕ,
                    inst.infConstantStepsizeStationarity μ oracle T =
                      matchingQuadraticLeadingTerm (Node := Bool)
                        inst lambda T + residual0 T := by
    intro inst lambda Ω _ μ _ oracle hquad hnoise
    exact
      MatchingQuadraticLowerBound
        (Node := Bool) inst lambda μ oracle hquad hnoise
  have htrichotomy_visible :
      ∀ (inst : Setup Bool ℝ) (lambda : ℝ)
        {Ω : Type} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (oracle : OracleNoiseProcess Ω Bool ℝ),
          HomogeneousQuadraticComponents (Node := Bool) inst lambda →
            inst.ExactVarianceIidAdditiveNoise μ oracle →
              AllStepsizeTrichotomyStatement
                (Node := Bool) inst lambda μ oracle := by
    intro inst lambda Ω _ μ _ oracle hquad hnoise
    exact
      AllStepsizeTrichotomyForQuadraticLowerBound
        (Node := Bool) inst lambda μ oracle hquad hnoise
  have hresidual_gap_visible :
      ∀ {residual residual0 : ℕ → ℝ} {gap : ℝ},
        OriginalLinearSpeedupResidualSmall residual →
          LittleOInvSqrt residual0 → 0 < gap →
            ∀ᶠ T : ℕ in Filter.atTop,
              residual T - residual0 T <
                gap * (Real.sqrt (T : ℝ))⁻¹ := by
    intro residual residual0 gap hresidual hresidual0 hgap
    exact
      originalLinearSpeedupResidual_sub_littleOInvSqrt_eventually_lt_gap
        hresidual hresidual0 hgap
  rcases two_step_counterexample_witness_with_matching_gap C with
    ⟨inst, lambda, a, Ω, mΩ, μ, hprob, oracle,
      hfixed, hquad, hnoise, hC_le, hgap⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hprob
  refine ⟨inst, lambda, a, Ω, mΩ, μ, hprob, oracle,
    hfixed, hquad, hnoise, hC_le, ?_⟩
  have hmatch :=
    hmatching_visible inst lambda μ oracle hquad hnoise
  exact
    noNetwork_residual_clause_of_matching_expansion_and_gap
      C inst lambda μ oracle hmatch hgap

/-- Common stepsize ceiling `alpha_max` from
`book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/15`
(`eq:alpha-max / (7.2)`), with zero-denominator terms explicitly interpreted
as non-constraining `+infty` terms as in the paper. -/
noncomputable def alphaMax : ℝ :=
  let a1 := minWithPaperInfinity setup.alphaStable 1
    (40 * setup.L * setup.blockGain)
  let a2 := minWithPaperInfinity a1
    (setup.period * setup.influenceSecondMoment)
    (40 * setup.L * setup.blockGain * setup.noiseTrackerFilterConstant)
  let a3 := minWithPaperInfinity a2
    (setup.period * setup.influenceSecondMoment * setup.blockGain)
    (21 * setup.randomFeedbackConstant * (nodeCount (Node := Node) : ℝ) * setup.L)
  minWithPaperInfinity a3 1
    (setup.L * Real.sqrt (42 * setup.stationaryFeedbackConstant))

/-- Source-derived positivity of the common stepsize ceiling. -/
theorem alphaMax_pos : 0 < setup.alphaMax := by
  have hperiod : 0 < (setup.period : ℝ) := by
    exact_mod_cast setup.period_pos
  have hnodeCount : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast (nodeCount_pos (Node := Node))
  unfold alphaMax
  apply minWithPaperInfinity_pos_of_pos_of_nonneg
  · apply minWithPaperInfinity_pos_of_pos_of_nonneg
    · apply minWithPaperInfinity_pos_of_pos_of_nonneg
      · apply minWithPaperInfinity_pos_of_pos_of_nonneg
        · exact setup.alphaStable_pos
        · norm_num
        · exact (mul_pos (mul_pos (by norm_num) setup.L_pos)
            setup.blockGain_pos).le
      · exact mul_pos hperiod setup.influenceSecondMoment_pos
      · exact mul_nonneg
          (mul_pos (mul_pos (by norm_num) setup.L_pos) setup.blockGain_pos).le
          setup.noiseTrackerFilterConstant_nonneg
    · exact mul_pos (mul_pos hperiod setup.influenceSecondMoment_pos)
        setup.blockGain_pos
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) setup.randomFeedbackConstant_nonneg)
          hnodeCount.le)
        setup.L_pos.le
  · norm_num
  · exact mul_nonneg setup.L_pos.le (Real.sqrt_nonneg _)

/-- The common ceiling is bounded by the Section 6 stability ceiling. -/
theorem alphaMax_le_alphaStable : setup.alphaMax ≤ setup.alphaStable := by
  unfold alphaMax
  exact (minWithPaperInfinity_le_current _ _ _).trans
    ((minWithPaperInfinity_le_current _ _ _).trans
      ((minWithPaperInfinity_le_current _ _ _).trans
        (minWithPaperInfinity_le_current _ _ _)))

/-- The five source-side consequences of `α ≤ α_max` used in the summed
Theorem 7.1 descent.  They are stated in multiplied form so the paper's
zero-denominator convention needs no artificial nonzero hypotheses. -/
theorem alphaMax_absorption_budget (alpha : ℝ)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaMax) :
    alpha ≤ setup.alphaStable ∧
      alpha * setup.L * setup.blockGain ≤ 1 / 40 ∧
        40 * setup.L * setup.blockGain * setup.noiseTrackerFilterConstant * alpha ≤
          (setup.period : ℝ) * setup.influenceSecondMoment ∧
        21 * setup.randomFeedbackConstant * (nodeCount (Node := Node) : ℝ) *
              setup.L * alpha ≤
          (setup.period : ℝ) * setup.influenceSecondMoment * setup.blockGain ∧
        42 * setup.stationaryFeedbackConstant * alpha ^ 2 * setup.L ^ 2 ≤ 1 := by
  let a1 := minWithPaperInfinity setup.alphaStable 1
    (40 * setup.L * setup.blockGain)
  let a2 := minWithPaperInfinity a1
    (setup.period * setup.influenceSecondMoment)
    (40 * setup.L * setup.blockGain * setup.noiseTrackerFilterConstant)
  let a3 := minWithPaperInfinity a2
    (setup.period * setup.influenceSecondMoment * setup.blockGain)
    (21 * setup.randomFeedbackConstant * (nodeCount (Node := Node) : ℝ) * setup.L)
  have halpha_a3 : alpha ≤ a3 := by
    exact halpha_le.trans (minWithPaperInfinity_le_current _ _ _)
  have halpha_a2 : alpha ≤ a2 := by
    exact halpha_a3.trans (minWithPaperInfinity_le_current _ _ _)
  have halpha_a1 : alpha ≤ a1 := by
    exact halpha_a2.trans (minWithPaperInfinity_le_current _ _ _)
  have hperiod : 0 ≤ (setup.period : ℝ) := by positivity
  have hnode : 0 ≤ (nodeCount (Node := Node) : ℝ) := by positivity
  have hdescent_mul : alpha * (40 * setup.L * setup.blockGain) ≤ 1 := by
    exact mul_denominator_le_of_le_minWithPaperInfinity (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) setup.L_pos.le) setup.blockGain_pos.le)
      halpha_a1
  have heta :
      alpha *
          (40 * setup.L * setup.blockGain * setup.noiseTrackerFilterConstant) ≤
        (setup.period : ℝ) * setup.influenceSecondMoment := by
    exact mul_denominator_le_of_le_minWithPaperInfinity
      (mul_nonneg hperiod setup.influenceSecondMoment_pos.le)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) setup.L_pos.le)
          setup.blockGain_pos.le)
        setup.noiseTrackerFilterConstant_nonneg)
      halpha_a2
  have hrandom :
      alpha *
          (21 * setup.randomFeedbackConstant * (nodeCount (Node := Node) : ℝ) *
            setup.L) ≤
        (setup.period : ℝ) * setup.influenceSecondMoment * setup.blockGain := by
    exact mul_denominator_le_of_le_minWithPaperInfinity
      (mul_nonneg (mul_nonneg hperiod setup.influenceSecondMoment_pos.le)
        setup.blockGain_pos.le)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) setup.randomFeedbackConstant_nonneg) hnode)
        setup.L_pos.le)
      halpha_a3
  have hstationary_mul :
      alpha *
          (setup.L * Real.sqrt (42 * setup.stationaryFeedbackConstant)) ≤ 1 := by
    exact mul_denominator_le_of_le_minWithPaperInfinity (by norm_num)
      (mul_nonneg setup.L_pos.le (Real.sqrt_nonneg _)) halpha_le
  have hstationary_arg :
      0 ≤ 42 * setup.stationaryFeedbackConstant :=
    mul_nonneg (by norm_num) setup.stationaryFeedbackConstant_nonneg
  have hstationary_product_nonneg :
      0 ≤ alpha *
          (setup.L * Real.sqrt (42 * setup.stationaryFeedbackConstant)) :=
    mul_nonneg halpha_pos.le
      (mul_nonneg setup.L_pos.le (Real.sqrt_nonneg _))
  have hstationary_sq :
      (alpha *
          (setup.L * Real.sqrt (42 * setup.stationaryFeedbackConstant))) ^ 2 ≤ 1 := by
    nlinarith
  have hstationary :
      42 * setup.stationaryFeedbackConstant * alpha ^ 2 * setup.L ^ 2 ≤ 1 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hstationary_arg] at hstationary_sq
    nlinarith
  refine ⟨halpha_le.trans setup.alphaMax_le_alphaStable, ?_, ?_, ?_, hstationary⟩
  · nlinarith [hdescent_mul]
  · nlinarith [heta]
  · nlinarith [hrandom]

/- Replacing the algorithmic stepsize leaves the canonical network gain
unchanged.  The Perron sequences are selected noncomputably, so this fact uses
their proved uniqueness rather than relying on definitional reduction. -/
theorem withStepsize_blockGain_eq (alpha : ℝ) :
    (setup.withStepsize alpha).blockGain = setup.blockGain := by
  let stepped := setup.withStepsize alpha
  have hperron : stepped.perronSequences = setup.perronSequences := by
    apply setup.perronSequences_unique stepped.perronSequences
    · simpa [stepped, withStepsize, PerronSequencesEquations] using
        stepped.perronSequences_spec.1
    · simpa [stepped, withStepsize, PerronSequencesPositivePeriodic] using
        stepped.perronSequences_spec.2.1
  have hleft (t : ℕ) : stepped.perronLeft t = setup.perronLeft t := by
    unfold perronLeft
    exact congrArg (fun seqs => seqs.1 t) hperron
  have hpull (r j : ℕ) :
      stepped.pullWindowProduct r j = setup.pullWindowProduct r j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [pullWindowProduct]
        rw [ih]
        rfl
  have hseries (r j : ℕ) :
      stepped.influenceSeriesTerm r j = setup.influenceSeriesTerm r j := by
    classical
    unfold influenceSeriesTerm
    rw [FiniteNetwork.periodicInfluenceSeriesTerm_def, hleft]
    rfl
  have hinfluence (r : ℕ) : stepped.influence r = setup.influence r := by
    unfold influence
    rw [hleft]
    congr 1
  unfold blockGain
  congr 1

/- Replacing the algorithmic stepsize also leaves the source's network-only
second influence moment unchanged.  As for `blockGain`, this is a theorem
rather than a definitional reduction because the canonical Perron sequences
are selected noncomputably. -/
theorem withStepsize_influenceSecondMoment_eq (alpha : ℝ) :
    (setup.withStepsize alpha).influenceSecondMoment =
      setup.influenceSecondMoment := by
  let stepped := setup.withStepsize alpha
  have hperron : stepped.perronSequences = setup.perronSequences := by
    apply setup.perronSequences_unique stepped.perronSequences
    · simpa [stepped, withStepsize, PerronSequencesEquations] using
        stepped.perronSequences_spec.1
    · simpa [stepped, withStepsize, PerronSequencesPositivePeriodic] using
        stepped.perronSequences_spec.2.1
  have hleft (t : ℕ) : stepped.perronLeft t = setup.perronLeft t := by
    unfold perronLeft
    exact congrArg (fun seqs => seqs.1 t) hperron
  have hpull (r j : ℕ) :
      stepped.pullWindowProduct r j = setup.pullWindowProduct r j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [pullWindowProduct]
        rw [ih]
        rfl
  have hseries (r j : ℕ) :
      stepped.influenceSeriesTerm r j = setup.influenceSeriesTerm r j := by
    classical
    unfold influenceSeriesTerm
    rw [FiniteNetwork.periodicInfluenceSeriesTerm_def, hleft]
    rfl
  have hinfluence (r : ℕ) : stepped.influence r = setup.influence r := by
    unfold influence
    rw [hleft]
    congr 1
  unfold influenceSecondMoment
  change ((setup.period : ℝ)⁻¹) *
      ∑ r : Fin setup.period, rowNormSq (Node := Node) (stepped.influence r.1) =
    ((setup.period : ℝ)⁻¹) *
      ∑ r : Fin setup.period, rowNormSq (Node := Node) (setup.influence r.1)
  congr 1

/- The three state-dependent terms in HCLD are packed by the source energy
`B_k`.  The explicit `L²` hypotheses below justify every use of Bochner
integral linearity; in particular this bridge does not rely on the totalized
integral outside its integrable domain. -/
theorem hcld_state_terms_sum_le_feedback_energy
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) :
    let stepped := setup.withStepsize alpha
    ∑ k ∈ Finset.range K,
        (5 * alpha * setup.blockGain * setup.L ^ 2 *
            (∫ ω,
              ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
          (21 * alpha / (4 * setup.blockGain)) *
            (∫ ω,
              (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
                ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ)) ≤
      (21 * alpha / (4 * setup.blockGain)) *
        stepped.stateFeedbackEnergySum μ oracle K := by
  classical
  dsimp only
  let stepped := setup.withStepsize alpha
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hcenter_mem (k : ℕ) : MemLp (fun ω =>
      stepped.blockStartHybridCenter (oracle.noise ω) k -
        stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)) 2 μ := by
    have hweighted : MemLp (fun ω =>
        weightedState (Node := Node) (E := E) (stepped.perronLeft 0)
          (stepped.primalState (oracle.noise ω) (stepped.blockStart k))) 2 μ := by
      unfold weightedState
      apply memLp_finset_sum Finset.univ
      intro i _hi
      simpa only [Pi.smul_apply] using
        ((stepped.generated_pushpull_coordinate_memLp μ oracle horacle_stepped
          (stepped.blockStart k)).1 i).const_smul (stepped.perronLeft 0 i)
    have havg : MemLp (fun ω =>
        stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)) 2 μ := by
      have hsum : MemLp (fun ω => ∑ i : Node,
          stepped.primalState (oracle.noise ω) (stepped.blockStart k) i) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro i _hi
        exact (stepped.generated_pushpull_coordinate_memLp μ oracle horacle_stepped
          (stepped.blockStart k)).1 i
      simpa [averageIterate, arithmeticAverage] using
        hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
    simpa only [blockStartHybridCenter] using hweighted.sub havg
  let KL : NNReal := ⟨stepped.L, stepped.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith KL (stepped.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      stepped.componentGradient_lipschitz_bound i x y
  have hgrad_mem (t : ℕ) (i : Node) : MemLp (fun ω =>
      stepped.gradientTable (stepped.primalState (oracle.noise ω) t) i) 2 μ := by
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (stepped.componentGradient i) KL
        (hgradient_lipschitz i)
        ((stepped.generated_pushpull_coordinate_memLp μ oracle horacle_stepped t).1 i)
  have hphase_mem (k : ℕ) : MemLp (fun ω =>
      stepped.blockPhaseError (oracle.noise ω) k) 2 μ := by
    have hweighted (r : Fin stepped.period) : MemLp (fun ω =>
        weightedState (Node := Node) (E := E) (stepped.influence r.1)
          (stepped.gradientTable
            (stepped.primalState (oracle.noise ω) (stepped.blockStart k + r.1))))
        2 μ := by
      unfold weightedState
      apply memLp_finset_sum Finset.univ
      intro i _hi
      simpa only [Pi.smul_apply] using
        (hgrad_mem (stepped.blockStart k + r.1) i).const_smul
          (stepped.influence r.1 i)
    have hsum : MemLp (fun ω => ∑ r : Fin stepped.period,
        weightedState (Node := Node) (E := E) (stepped.influence r.1)
          (stepped.gradientTable
            (stepped.primalState (oracle.noise ω) (stepped.blockStart k + r.1))))
        2 μ := by
      apply memLp_finset_sum Finset.univ
      intro r _hr
      exact hweighted r
    have hblock : MemLp (fun ω =>
        stepped.blockAverageGradient (oracle.noise ω) k) 2 μ := by
      simpa only [blockAverageGradient, randomAverageIterate] using
        stepped.averageGradient_randomAverageIterate_memLp_two
          μ oracle horacle_stepped (stepped.blockStart k)
    simpa only [blockPhaseError] using
      hsum.sub (hblock.const_smul stepped.blockGain)
  have hhigh_mem (k : ℕ) : MemLp (fun ω =>
      stepped.highPassIncrement (oracle.noise ω) k) 2 μ := by
    simpa only [highPassIncrement] using
      (stepped.meanLiftCorrection_memLp_two μ oracle horacle_stepped (k + 1)).sub
        (stepped.meanLiftCorrection_memLp_two μ oracle horacle_stepped k)
  have hcenter_int (k : ℕ) : Integrable (fun ω =>
      ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
        stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hcenter_mem k).aestronglyMeasurable).1
      (hcenter_mem k)
  have hphase_int (k : ℕ) : Integrable (fun ω =>
      ‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hphase_mem k).aestronglyMeasurable).1
      (hphase_mem k)
  have hhigh_int (k : ℕ) : Integrable (fun ω =>
      ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hhigh_mem k).aestronglyMeasurable).1
      (hhigh_mem k)
  have henergy_eq (k : ℕ) :
      (∫ ω, stepped.stateFeedbackEnergy (oracle.noise ω) k ∂μ) =
        stepped.blockGain ^ 2 * stepped.L ^ 2 *
            (∫ ω,
              ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
          (∫ ω, ‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ) +
          (∫ ω, ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ) := by
    unfold stateFeedbackEnergy
    rw [MeasureTheory.integral_add, MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul]
    all_goals
      first
      | exact (hcenter_int k).const_mul _
      | exact hphase_int k
      | exact hhigh_int k
      | exact ((hcenter_int k).const_mul _).add (hphase_int k)
  have hpoint (k : ℕ) :
      5 * alpha * setup.blockGain * setup.L ^ 2 *
            (∫ ω,
              ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
          (21 * alpha / (4 * setup.blockGain)) *
            (∫ ω,
              (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
                ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ) ≤
        (21 * alpha / (4 * setup.blockGain)) *
          (∫ ω, stepped.stateFeedbackEnergy (oracle.noise ω) k ∂μ) := by
    have hH : 0 < setup.blockGain := setup.blockGain_pos
    have hcenter_nonneg : 0 ≤ (∫ ω,
        ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
          stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) :=
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
    have hcenter_coeff :
        5 * alpha * setup.blockGain * setup.L ^ 2 ≤
          (21 * alpha / (4 * setup.blockGain)) *
            (stepped.blockGain ^ 2 * stepped.L ^ 2) := by
      have hprod : 0 ≤ alpha * setup.blockGain * setup.L ^ 2 :=
        mul_nonneg (mul_nonneg halpha_pos.le hH.le) (sq_nonneg setup.L)
      calc
        5 * alpha * setup.blockGain * setup.L ^ 2 ≤
            (21 / 4 : ℝ) * alpha * setup.blockGain * setup.L ^ 2 := by
          nlinarith
        _ = (21 * alpha / (4 * setup.blockGain)) *
            (stepped.blockGain ^ 2 * stepped.L ^ 2) := by
          have hstepped_H : stepped.blockGain = setup.blockGain := by
            exact setup.withStepsize_blockGain_eq alpha
          have hstepped_L : stepped.L = setup.L := by
            rfl
          rw [hstepped_H, hstepped_L]
          field_simp [ne_of_gt hH]
    rw [henergy_eq, MeasureTheory.integral_add (hphase_int k) (hhigh_int k)]
    calc
      _ ≤ (21 * alpha / (4 * setup.blockGain)) *
              (stepped.blockGain ^ 2 * stepped.L ^ 2) *
              (∫ ω,
                ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                  stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
            (21 * alpha / (4 * setup.blockGain)) *
              ((∫ ω, ‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ) +
                ∫ ω, ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcenter_coeff hcenter_nonneg) le_rfl
      _ = _ := by ring
  calc
    ∑ k ∈ Finset.range K,
        (5 * alpha * setup.blockGain * setup.L ^ 2 *
            (∫ ω,
              ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
          (21 * alpha / (4 * setup.blockGain)) *
            (∫ ω,
              (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
                ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ)) ≤
      ∑ k ∈ Finset.range K,
        (21 * alpha / (4 * setup.blockGain)) *
          (∫ ω, stepped.stateFeedbackEnergy (oracle.noise ω) k ∂μ) := by
        exact Finset.sum_le_sum fun k _hk => hpoint k
    _ = (21 * alpha / (4 * setup.blockGain)) *
        stepped.stateFeedbackEnergySum μ oracle K := by
      unfold stateFeedbackEnergySum
      rw [Finset.mul_sum]

/- A globally smooth finite-average objective is integrable along any `L²`
process.  The lower objective bound controls the negative part, while the
smooth quadratic model at `x₀` controls the positive part. -/
theorem objective_comp_integrable_of_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → E)
    (hX : MemLp X 2 μ) :
    Integrable (fun ω => setup.objective (X ω)) μ := by
  classical
  let g0 : E := SOptLib.finiteUniformAverage
    (fun i : Node => setup.componentGradient i setup.x0)
  have hobj_cont : Continuous setup.objective := by
    unfold objective finiteAverageObjectiveOf SOptLib.finiteUniformAverage
    apply Continuous.const_smul
    exact continuous_finset_sum _ fun i _hi =>
      (setup.componentObjective_differentiable i).continuous
  have hdiff : MemLp (fun ω => X ω - setup.x0) 2 μ := by
    simpa using hX.sub (memLp_const setup.x0)
  have hsq : Integrable (fun ω => ‖X ω - setup.x0‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).1 hdiff
  have hinner : Integrable (fun ω => ⟪g0, X ω - setup.x0⟫_ℝ) μ := by
    exact integrable_inner_of_memLp_two (memLp_const g0) hdiff
  have henvelope : Integrable (fun ω =>
      |setup.objectiveInfimum| + |setup.objective setup.x0| +
        |⟪g0, X ω - setup.x0⟫_ℝ| +
          |setup.L / 2| * ‖X ω - setup.x0‖ ^ 2) μ := by
    exact (((integrable_const (c :=
        |setup.objectiveInfimum| + |setup.objective setup.x0|)).add hinner.norm).add
      (hsq.const_mul |setup.L / 2|))
  refine henvelope.mono'
    (hobj_cont.comp_aestronglyMeasurable hX.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun ω => by
    have hlower : setup.objectiveInfimum ≤ setup.objective (X ω) := by
      unfold objectiveInfimum
      exact SOptLib.objectiveInfimumValue_le
        (by simpa [Set.image_univ] using setup.objective_bddBelow_source)
        (Set.mem_univ (X ω))
    have hupper : setup.objective (X ω) ≤
        setup.objective setup.x0 + ⟪g0, X ω - setup.x0⟫_ℝ +
          (setup.L / 2) * ‖X ω - setup.x0‖ ^ 2 := by
      have hsmooth :=
        SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
          (Set.univ : Set E) setup.componentObjective setup.componentGradient
          (fun _i : Node => setup.L) setup.L convex_univ
          (by simp [Fintype.card_ne_zero])
          (fun i z _hz => by
            simpa [componentGradient] using
              (setup.componentObjective_differentiable i).differentiableAt.hasGradientAt)
          (fun i z w _hz _hw => setup.componentGradient_lipschitz_bound i z w)
          (Set.mem_univ setup.x0) (Set.mem_univ (X ω))
      simpa [objective, finiteAverageObjectiveOf, g0] using hsmooth
    rw [Real.norm_eq_abs]
    apply (abs_le).2
    constructor
    · have htail_nonneg :
          0 ≤ |setup.L / 2| * ‖X ω - setup.x0‖ ^ 2 :=
        mul_nonneg (abs_nonneg _) (sq_nonneg ‖X ω - setup.x0‖)
      calc
        -(|setup.objectiveInfimum| + |setup.objective setup.x0| +
              |⟪g0, X ω - setup.x0⟫_ℝ| +
                |setup.L / 2| * ‖X ω - setup.x0‖ ^ 2) ≤
            -|setup.objectiveInfimum| := by
              apply neg_le_neg
              nlinarith [abs_nonneg (setup.objective setup.x0),
                abs_nonneg ⟪g0, X ω - setup.x0⟫_ℝ,
                htail_nonneg]
        _ ≤ setup.objectiveInfimum := neg_abs_le setup.objectiveInfimum
        _ ≤ setup.objective (X ω) := hlower
    · calc
        setup.objective (X ω) ≤
            setup.objective setup.x0 + ⟪g0, X ω - setup.x0⟫_ℝ +
              (setup.L / 2) * ‖X ω - setup.x0‖ ^ 2 := hupper
        _ ≤ |setup.objective setup.x0| + |⟪g0, X ω - setup.x0⟫_ℝ| +
              |setup.L / 2| * ‖X ω - setup.x0‖ ^ 2 := by
            exact add_le_add
              (add_le_add (le_abs_self _) (le_abs_self _))
              (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
        _ ≤ |setup.objectiveInfimum| + |setup.objective setup.x0| +
              |⟪g0, X ω - setup.x0⟫_ℝ| +
                |setup.L / 2| * ‖X ω - setup.x0‖ ^ 2 := by
            linarith [abs_nonneg setup.objectiveInfimum]

/- Deterministic left multiplication preserves measurability of a random
distributed state. -/
theorem leftMul_comp_measurable
    {Omega : Type*} {m : MeasurableSpace Omega} [MeasurableSpace E] [BorelSpace E]
    (A : NodeMatrix Node) {X : Omega → State Node E}
    (hX : Measurable[m] X) :
    Measurable[m] (fun omega => leftMul (Node := Node) (E := E) A (X omega)) := by
  classical
  refine measurable_pi_lambda _ ?_
  intro i
  unfold leftMul
  apply Finset.measurable_sum Finset.univ
  intro j _hj
  exact ((measurable_pi_apply j).comp hX).const_smul (A i j)

/- The deterministic component-gradient table is measurable. -/
theorem gradientTable_comp_measurable
    {Omega : Type*} {m : MeasurableSpace Omega} [MeasurableSpace E]
    [BorelSpace E] {X : Omega → State Node E}
    (hX : Measurable[m] X) :
    Measurable[m] (fun omega => setup.gradientTable (X omega)) := by
  let KL : NNReal := ⟨setup.L, setup.L_pos.le⟩
  refine measurable_pi_lambda _ ?_
  intro i
  have hlip : LipschitzWith KL (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  exact hlip.continuous.measurable.comp ((measurable_pi_apply i).comp hX)

/- The generated primal state is adapted to the strict past at its own time;
the tracker state, which contains the current oracle table, is adapted one
time later. -/
theorem generated_primal_tracker_strictPastMeasurable
    {Omega : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [BorelSpace E]
    (oracle : OracleNoiseProcess Omega Node E) :
    ∀ t : ℕ,
      Measurable[oracle.strictPastMeasurableSpace t]
          (fun omega => setup.primalState (oracle.noise omega) t) ∧
        Measurable[oracle.strictPastMeasurableSpace (t + 1)]
          (fun omega => setup.trackerState (oracle.noise omega) t) := by
  classical
  intro t
  induction t with
  | zero =>
      constructor
      · simpa only [setup.primalState_zero] using
          (measurable_const : Measurable[oracle.strictPastMeasurableSpace 0]
            (fun _ : Omega => setup.initialPrimal))
      · have hnoise : Measurable[oracle.strictPastMeasurableSpace 1]
            (oracle.noiseStream 0) := by
          exact SOptLib.measurable_sample_of_lt_prefixFiltration
            oracle.noiseStream oracle.noiseStream_measurable (by omega)
        have hgrad : Measurable[oracle.strictPastMeasurableSpace 1]
            (fun _ : Omega => setup.gradientTable setup.initialPrimal) :=
          measurable_const
        have hsum := hgrad.add hnoise
        simpa only [setup.trackerState_zero, oracleTable, sampledGradient,
          setup.primalState_zero, OracleNoiseProcess.noiseStream_apply] using hsum
  | succ t ih =>
      have hFt_Fsucc : oracle.strictPastMeasurableSpace t ≤
          oracle.strictPastMeasurableSpace (t + 1) :=
        (oracle.naturalFiltration).mono (Nat.le_succ t)
      have hFsucc_Fsuccsucc : oracle.strictPastMeasurableSpace (t + 1) ≤
          oracle.strictPastMeasurableSpace (t + 1 + 1) :=
        (oracle.naturalFiltration).mono (Nat.le_succ (t + 1))
      have hXcur_succ : Measurable[oracle.strictPastMeasurableSpace (t + 1)]
          (fun omega => setup.primalState (oracle.noise omega) t) :=
        ih.1.mono hFt_Fsucc le_rfl
      have hXnext : Measurable[oracle.strictPastMeasurableSpace (t + 1)]
          (fun omega => setup.primalState (oracle.noise omega) (t + 1)) := by
        have hraw :=
          (leftMul_comp_measurable (Node := Node) (E := E)
            (setup.R t) hXcur_succ).sub
            (ih.2.const_smul setup.alpha)
        simpa only [setup.primalState_succ] using hraw
      refine ⟨hXnext, ?_⟩
      have hYcur : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (fun omega => setup.trackerState (oracle.noise omega) t) :=
        ih.2.mono hFsucc_Fsuccsucc le_rfl
      have hXnext' : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (fun omega => setup.primalState (oracle.noise omega) (t + 1)) :=
        hXnext.mono hFsucc_Fsuccsucc le_rfl
      have hXcur' : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (fun omega => setup.primalState (oracle.noise omega) t) :=
        hXcur_succ.mono hFsucc_Fsuccsucc le_rfl
      have hnoise_next : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (oracle.noiseStream (t + 1)) := by
        exact SOptLib.measurable_sample_of_lt_prefixFiltration
          oracle.noiseStream oracle.noiseStream_measurable (by omega)
      have hnoise_cur : Measurable[oracle.strictPastMeasurableSpace (t + 1 + 1)]
          (oracle.noiseStream t) := by
        exact SOptLib.measurable_sample_of_lt_prefixFiltration
          oracle.noiseStream oracle.noiseStream_measurable (by omega)
      have hGnext :=
        (setup.gradientTable_comp_measurable hXnext').add hnoise_next
      have hGcur :=
        (setup.gradientTable_comp_measurable hXcur').add hnoise_cur
      have hraw :=
        ((leftMul_comp_measurable (Node := Node) (E := E)
          (setup.C t) hYcur).add hGnext).sub hGcur
      simpa only [setup.trackerState_succ, oracleTable, sampledGradient,
        OracleNoiseProcess.noiseStream_apply] using hraw

/- The noise-driven tracker error at time `t` is generated only by oracle
tables strictly before `t`.  This is the specialized use of the reusable
recursive-process adaptedness theorem needed at block starts. -/
theorem noiseTrackerError_strictPastMeasurable
    {Omega : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [BorelSpace E]
    (oracle : OracleNoiseProcess Omega Node E) (t : ℕ) :
    Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => setup.noiseTrackerError (oracle.noise omega) t) := by
  classical
  let process : ℕ → Omega → State Node E := fun n omega =>
    setup.noiseTrackerError (oracle.noise omega) n
  let driver : ℕ → Omega → State Node E := fun n omega =>
    oracle.noise omega n
  let step : ℕ → State Node E → State Node E → State Node E :=
    fun n current sample =>
      leftMul (Node := Node) (E := E) (setup.C n) current +
        leftMul (Node := Node) (E := E)
          (matrixSub (Node := Node) (setup.C n) (identityMatrix (Node := Node)))
          sample
  refine SOptLib.recursiveProcess_measurable_wrt_strictPast
    (past := oracle.strictPastMeasurableSpace) (process := process)
    (driver := driver) (step := step) (k := t) (N := t) ?_ ?_ ?_ ?_ t le_rfl
  · simpa [process, noiseTrackerError, SOptLib.recursiveIterateProcess] using
      (measurable_const : Measurable[oracle.strictPastMeasurableSpace t]
        (fun _ : Omega => (0 : State Node E)))
  · intro n hn _hprocess
    exact SOptLib.measurable_sample_of_lt_prefixFiltration
      oracle.noiseStream oracle.noiseStream_measurable (by omega)
  · intro n _hn
    dsimp only [step]
    refine measurable_pi_lambda _ ?_
    intro i
    apply Measurable.add
    · apply Finset.measurable_sum Finset.univ
      intro j _hj
      exact (((measurable_pi_apply j).comp measurable_fst).const_smul
        (setup.C n i j))
    · apply Finset.measurable_sum Finset.univ
      intro j _hj
      exact (((measurable_pi_apply j).comp measurable_snd).const_smul
        (matrixSub (Node := Node) (setup.C n) (identityMatrix (Node := Node)) i j))
  · intro n _hn
    funext omega
    simp [process, driver, step, noiseTrackerError,
      SOptLib.recursiveIterateProcess, leftMul]

/- Exact block-start adaptedness used by the Lemma 5.2 martingale
cancellation.  Both gradients multiplying the block noise are measurable with
respect to `F_{kp^-}`. -/
theorem block_start_hybrid_descent_adapted
    {Omega : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [BorelSpace E]
    (oracle : OracleNoiseProcess Omega Node E) (alpha : ℝ) (k : ℕ) :
    let stepped := setup.withStepsize alpha
    Measurable[oracle.strictPastMeasurableSpace (stepped.blockStart k)]
        (fun omega => stepped.blockAverageGradient (oracle.noise omega) k) ∧
      Measurable[oracle.strictPastMeasurableSpace (stepped.blockStart k)]
        (fun omega => stepped.averageGradient
          (stepped.hybridCenter (oracle.noise omega) k)) := by
  classical
  dsimp only
  let stepped := setup.withStepsize alpha
  let t := stepped.blockStart k
  have hX : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.primalState (oracle.noise omega) t) :=
    (stepped.generated_primal_tracker_strictPastMeasurable oracle t).1
  have havg : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.averageIterate (oracle.noise omega) t) := by
    unfold averageIterate arithmeticAverage
    apply Measurable.const_smul
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    exact (measurable_pi_apply i).comp hX
  let KL : NNReal := ⟨stepped.L, stepped.L_pos.le⟩
  have havg_lip : LipschitzWith KL stepped.averageGradient := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL] using stepped.averageGradient_lipschitz_bound x y
  have hgbar : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.blockAverageGradient (oracle.noise omega) k) := by
    simpa only [blockAverageGradient, t] using
      havg_lip.continuous.measurable.comp havg
  have hweighted : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.blockStartHybridCenter (oracle.noise omega) k) := by
    unfold blockStartHybridCenter weightedState
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    exact ((measurable_pi_apply i).comp hX).const_smul (stepped.perronLeft 0 i)
  have hnoiseError : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.noiseTrackerError (oracle.noise omega) t) :=
    stepped.noiseTrackerError_strictPastMeasurable oracle t
  have hnoiseErrorZeroSum : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.noiseTrackerErrorZeroSum (oracle.noise omega) t) := by
    exact hnoiseError.subtype_mk
  obtain ⟨Kcorr, hcorr⟩ := stepped.correctedLift_exists_lipschitz 0
  have heta : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.noiseLiftCorrection (oracle.noise omega) k) := by
    simpa only [noiseLiftCorrection, t] using
      hcorr.continuous.measurable.comp hnoiseErrorZeroSum
  have hcenter : Measurable[oracle.strictPastMeasurableSpace t]
      (fun omega => stepped.hybridCenter (oracle.noise omega) k) := by
    simpa only [hybridCenter] using hweighted.sub (heta.const_smul alpha)
  exact ⟨hgbar, havg_lip.continuous.measurable.comp hcenter⟩

/- The Hilbert-space algebra in the source proof before taking expectations.
The only unbounded block-noise cross term is displayed explicitly; its
multiplier is exactly the adapted quantity supplied above. -/
set_option maxHeartbeats 200000 in
theorem hybrid_center_descent_algebra
    (L H alpha : ℝ) (hL : 0 < L) (hH : 0 < H) (halpha : 0 < alpha)
    (hsmall : alpha * L * H ≤ 1 / 40) (q g d z : E) :
    ⟪q, -alpha • (H • g + d + z)⟫_ℝ +
        (L / 2) * ‖-alpha • (H • g + d + z)‖ ^ 2 ≤
      -((5 * alpha * H) / 8) * ‖g‖ ^ 2 +
        (21 * alpha / (8 * H)) * ‖d‖ ^ 2 +
        (5 * alpha * H / 2) * ‖q - g‖ ^ 2 +
        (5 / 8) * L * alpha ^ 2 * ‖z‖ ^ 2 +
        ⟪-alpha • q + (L * alpha ^ 2 * H) • g, z⟫_ℝ := by
  exact inner_neg_smul_three_term_add_quadratic_le_of_mul_le L H alpha hL.le hH
    halpha.le hsmall q g d z

/- The hybrid potential has an honest Bochner integral at every block endpoint.
This is the endpoint regularity required by the expected telescope in (7.4). -/
theorem hybridPotential_integrable
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (k : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    Integrable (fun ω =>
      (setup.withStepsize alpha).hybridPotential (oracle.noise ω) k) μ := by
  classical
  let stepped := setup.withStepsize alpha
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hweighted : MemLp (fun ω =>
      weightedState (Node := Node) (E := E) (stepped.perronLeft 0)
        (stepped.primalState (oracle.noise ω) (stepped.blockStart k))) 2 μ := by
    unfold weightedState
    apply memLp_finset_sum Finset.univ
    intro i _hi
    simpa only [Pi.smul_apply] using
      ((stepped.generated_pushpull_coordinate_memLp μ oracle horacle_stepped
        (stepped.blockStart k)).1 i).const_smul (stepped.perronLeft 0 i)
  have heta := stepped.noiseLiftCorrection_memLp_two
    μ oracle horacle_stepped k
  have hcenter : MemLp (fun ω =>
      stepped.hybridCenter (oracle.noise ω) k) 2 μ := by
    simpa only [hybridCenter, blockStartHybridCenter] using
      hweighted.sub (heta.const_smul alpha)
  simpa only [hybridPotential] using
    stepped.objective_comp_integrable_of_memLp_two μ _ hcenter

/- The source proof's intermediate inequality immediately before (5.14).
It consumes the generated-process adaptedness bridge, the exact hybrid-center
recursion, smoothness of the finite average, and the sharp block-noise law. -/
set_option maxHeartbeats 800000 in
theorem hybrid_center_intermediate_descent
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (k : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha)
    (halpha_small : alpha * setup.L * setup.blockGain ≤ 1 / 40) :
    let stepped := setup.withStepsize alpha
    ∫ omega,
        (stepped.hybridPotential (oracle.noise omega) (k + 1) -
          stepped.hybridPotential (oracle.noise omega) k) ∂μ ≤
      -((5 * alpha * stepped.blockGain) / 8) *
          (∫ omega, ‖stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (21 * alpha / (8 * stepped.blockGain)) *
          (∫ omega,
            ‖stepped.blockPhaseError (oracle.noise omega) k -
              stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (5 * alpha * stepped.blockGain / 2) *
          (∫ omega,
            ‖stepped.averageGradient
                (stepped.hybridCenter (oracle.noise omega) k) -
              stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 := by
  classical
  dsimp only
  let stepped := setup.withStepsize alpha
  change
    (∫ omega,
        (stepped.hybridPotential (oracle.noise omega) (k + 1) -
          stepped.hybridPotential (oracle.noise omega) k) ∂μ) ≤
      -((5 * alpha * stepped.blockGain) / 8) *
          (∫ omega, ‖stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (21 * alpha / (8 * stepped.blockGain)) *
          (∫ omega,
            ‖stepped.blockPhaseError (oracle.noise omega) k -
              stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (5 * alpha * stepped.blockGain / 2) *
          (∫ omega,
            ‖stepped.averageGradient
                (stepped.hybridCenter (oracle.noise omega) k) -
              stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2
  let Q : Ω → E := fun omega =>
    stepped.averageGradient (stepped.hybridCenter (oracle.noise omega) k)
  let G : Ω → E := fun omega =>
    stepped.blockAverageGradient (oracle.noise omega) k
  let D : Ω → E := fun omega =>
    stepped.blockPhaseError (oracle.noise omega) k -
      stepped.highPassIncrement (oracle.noise omega) k
  let Z : Ω → E := fun omega => stepped.blockNoise (oracle.noise omega) k
  let M : Ω → E := fun omega =>
    -alpha • Q omega +
      (stepped.L * alpha ^ 2 * stepped.blockGain) • G omega
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hH_eq : stepped.blockGain = setup.blockGain :=
    setup.withStepsize_blockGain_eq alpha
  have hsmall_stepped : alpha * stepped.L * stepped.blockGain ≤ 1 / 40 := by
    simpa [hH_eq] using halpha_small
  have hq_mem : MemLp Q 2 μ := by
    have hweighted : MemLp (fun omega =>
        weightedState (Node := Node) (E := E) (stepped.perronLeft 0)
          (stepped.primalState (oracle.noise omega) (stepped.blockStart k))) 2 μ := by
      unfold weightedState
      apply memLp_finset_sum Finset.univ
      intro i _hi
      simpa only [Pi.smul_apply] using
        ((stepped.generated_pushpull_coordinate_memLp μ oracle horacle_stepped
          (stepped.blockStart k)).1 i).const_smul (stepped.perronLeft 0 i)
    have heta := stepped.noiseLiftCorrection_memLp_two
      μ oracle horacle_stepped k
    have hcenter : MemLp (fun omega =>
        stepped.hybridCenter (oracle.noise omega) k) 2 μ := by
      simpa only [hybridCenter, blockStartHybridCenter] using
        hweighted.sub (heta.const_smul alpha)
    let KL : NNReal := ⟨stepped.L, stepped.L_pos.le⟩
    have hlip : LipschitzWith KL stepped.averageGradient := by
      rw [lipschitzWith_iff_norm_sub_le]
      intro x y
      simpa [KL] using stepped.averageGradient_lipschitz_bound x y
    simpa only [Q] using
      memLp_two_comp_lipschitz stepped.averageGradient KL hlip hcenter
  have hg_mem : MemLp G 2 μ := by
    simpa only [G, blockAverageGradient, randomAverageIterate] using
      stepped.averageGradient_randomAverageIterate_memLp_two
        μ oracle horacle_stepped (stepped.blockStart k)
  have hphase_mem := stepped.blockPhaseError_memLp_two
    μ oracle horacle_stepped k
  have hhigh_mem : MemLp (fun omega =>
      stepped.highPassIncrement (oracle.noise omega) k) 2 μ := by
    simpa only [highPassIncrement] using
      (stepped.meanLiftCorrection_memLp_two μ oracle horacle_stepped (k + 1)).sub
        (stepped.meanLiftCorrection_memLp_two μ oracle horacle_stepped k)
  have hd_mem : MemLp D 2 μ := by
    simpa only [D] using hphase_mem.sub hhigh_mem
  have hz_mem : MemLp Z 2 μ := by
    unfold Z blockNoise
    apply memLp_finset_sum Finset.univ
    intro r _hr
    exact stepped.weightedNoise_memLp_two μ oracle horacle_stepped
      (stepped.blockStart k + r.1) (stepped.influence r.1)
  have hm_mem : MemLp M 2 μ := by
    exact (hq_mem.const_smul (-alpha)).add
      (hg_mem.const_smul (stepped.L * alpha ^ 2 * stepped.blockGain))
  have hq_sq : Integrable (fun omega => ‖Q omega - G omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm
      (hq_mem.sub hg_mem).aestronglyMeasurable).1 (hq_mem.sub hg_mem)
  have hg_sq : Integrable (fun omega => ‖G omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg_mem.aestronglyMeasurable).1 hg_mem
  have hd_sq : Integrable (fun omega => ‖D omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hd_mem.aestronglyMeasurable).1 hd_mem
  have hz_sq : Integrable (fun omega => ‖Z omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hz_mem.aestronglyMeasurable).1 hz_mem
  have hinner : Integrable (fun omega => ⟪M omega, Z omega⟫_ℝ) μ :=
    integrable_inner_of_memLp_two hm_mem hz_mem
  have hVdiff : Integrable (fun omega =>
      stepped.hybridPotential (oracle.noise omega) (k + 1) -
        stepped.hybridPotential (oracle.noise omega) k) μ :=
    (stepped.hybridPotential_integrable μ oracle alpha (k + 1) horacle_stepped).sub
      (stepped.hybridPotential_integrable μ oracle alpha k horacle_stepped)
  have hadapt := setup.block_start_hybrid_descent_adapted oracle alpha k
  have hM_meas : Measurable[oracle.strictPastMeasurableSpace (stepped.blockStart k)] M := by
    exact (hadapt.2.const_smul (-alpha)).add
      (hadapt.1.const_smul (stepped.L * alpha ^ 2 * stepped.blockGain))
  have hnoise := stepped.blockNoise_conditional_mean_zero_and_secondMoment
    μ oracle horacle_stepped k
  let hm := strictPastMeasurableSpace_le (Node := Node) (E := E) oracle
    (stepped.blockStart k)
  letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace (stepped.blockStart k))
      (μ.trim hm) := strictPastMeasurableSpace_trim_sigmaFinite
        (Node := Node) (E := E) μ oracle (stepped.blockStart k)
  have hcancel : (∫ omega, ⟪M omega, Z omega⟫_ℝ ∂μ) = 0 := by
    have hraw := integral_inner_sub_const_eq_zero_of_condExp_eq_zero
      (P := μ) (m := oracle.strictPastMeasurableSpace (stepped.blockStart k))
      (δ := Z) (x := M) (c := (0 : E)) hm hM_meas
      (SOptLib.ConditionalExpectation.conditionalExpectationEq.ae_eq hnoise.1)
      (hz_mem.integrable (by norm_num))
      (by simpa [sub_zero, real_inner_comm] using hinner)
    simpa [sub_zero, real_inner_comm] using hraw
  have hsmooth (omega : Ω) :
      stepped.hybridPotential (oracle.noise omega) (k + 1) -
          stepped.hybridPotential (oracle.noise omega) k ≤
        ⟪Q omega,
          -alpha • (stepped.blockGain • G omega + D omega + Z omega)⟫_ℝ +
          (stepped.L / 2) *
            ‖-alpha • (stepped.blockGain • G omega + D omega + Z omega)‖ ^ 2 := by
    have hquad :=
      SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
        (Set.univ : Set E) stepped.componentObjective stepped.componentGradient
        (fun _i : Node => stepped.L) stepped.L convex_univ
        (by simp [Fintype.card_ne_zero])
        (fun i x _hx => by
          simpa [componentGradient] using
            (stepped.componentObjective_differentiable i).differentiableAt.hasGradientAt)
        (fun i x y _hx _hy => stepped.componentGradient_lipschitz_bound i x y)
        (Set.mem_univ (stepped.hybridCenter (oracle.noise omega) k))
        (Set.mem_univ (stepped.hybridCenter (oracle.noise omega) (k + 1)))
    have hbase :
        stepped.hybridPotential (oracle.noise omega) (k + 1) -
            stepped.hybridPotential (oracle.noise omega) k ≤
          ⟪stepped.averageGradient
              (stepped.hybridCenter (oracle.noise omega) k),
            stepped.hybridCenter (oracle.noise omega) (k + 1) -
              stepped.hybridCenter (oracle.noise omega) k⟫_ℝ +
            (stepped.L / 2) *
              ‖stepped.hybridCenter (oracle.noise omega) (k + 1) -
                stepped.hybridCenter (oracle.noise omega) k‖ ^ 2 := by
      simpa [hybridPotential, objective, finiteAverageObjectiveOf, nodeCount,
        stepped.averageGradient_eq_componentGradient_average,
        add_assoc, add_left_comm, add_comm] using
        (sub_le_iff_le_add.mpr hquad)
    have hrec := stepped.hybridCenter_succ (oracle.noise omega) k
    rw [hrec] at hbase
    simpa [Q, G, D, Z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hbase
  have hpoint (omega : Ω) :
      stepped.hybridPotential (oracle.noise omega) (k + 1) -
          stepped.hybridPotential (oracle.noise omega) k ≤
        -((5 * alpha * stepped.blockGain) / 8) * ‖G omega‖ ^ 2 +
          (21 * alpha / (8 * stepped.blockGain)) * ‖D omega‖ ^ 2 +
          (5 * alpha * stepped.blockGain / 2) * ‖Q omega - G omega‖ ^ 2 +
          (5 / 8) * stepped.L * alpha ^ 2 * ‖Z omega‖ ^ 2 +
          ⟪M omega, Z omega⟫_ℝ := by
    exact (hsmooth omega).trans
      (hybrid_center_descent_algebra stepped.L stepped.blockGain alpha
        stepped.L_pos stepped.blockGain_pos halpha_pos hsmall_stepped
        (Q omega) (G omega) (D omega) (Z omega))
  have hright : Integrable (fun omega =>
      -((5 * alpha * stepped.blockGain) / 8) * ‖G omega‖ ^ 2 +
        (21 * alpha / (8 * stepped.blockGain)) * ‖D omega‖ ^ 2 +
        (5 * alpha * stepped.blockGain / 2) * ‖Q omega - G omega‖ ^ 2 +
        (5 / 8) * stepped.L * alpha ^ 2 * ‖Z omega‖ ^ 2 +
        ⟪M omega, Z omega⟫_ℝ) μ :=
    ((((hg_sq.const_mul _).add (hd_sq.const_mul _)).add
      (hq_sq.const_mul _)).add (hz_sq.const_mul _)).add hinner
  have hmono := MeasureTheory.integral_mono hVdiff hright hpoint
  have hA := hg_sq.const_mul (-((5 * alpha * stepped.blockGain) / 8))
  have hB := hd_sq.const_mul (21 * alpha / (8 * stepped.blockGain))
  have hC := hq_sq.const_mul (5 * alpha * stepped.blockGain / 2)
  have hD := hz_sq.const_mul ((5 / 8) * stepped.L * alpha ^ 2)
  have hAB := MeasureTheory.integral_add hA hB
  have hABC := MeasureTheory.integral_add (hA.add hB) hC
  have hABCD := MeasureTheory.integral_add ((hA.add hB).add hC) hD
  have hABCDE :=
    MeasureTheory.integral_add (((hA.add hB).add hC).add hD) hinner
  have hsplit :
      (∫ x,
          -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 +
            (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 +
            (5 * alpha * stepped.blockGain / 2) * ‖Q x - G x‖ ^ 2 +
            (5 / 8) * stepped.L * alpha ^ 2 * ‖Z x‖ ^ 2 +
            ⟪M x, Z x⟫_ℝ ∂μ) =
        ((((∫ x, -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 ∂μ) +
            ∫ x, (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 ∂μ) +
          ∫ x, (5 * alpha * stepped.blockGain / 2) * ‖Q x - G x‖ ^ 2 ∂μ) +
        ∫ x, (5 / 8) * stepped.L * alpha ^ 2 * ‖Z x‖ ^ 2 ∂μ) +
        ∫ x, ⟪M x, Z x⟫_ℝ ∂μ := by
    calc
      _ = (∫ x,
            -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 +
              (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 +
              (5 * alpha * stepped.blockGain / 2) * ‖Q x - G x‖ ^ 2 +
              (5 / 8) * stepped.L * alpha ^ 2 * ‖Z x‖ ^ 2 ∂μ) +
            ∫ x, ⟪M x, Z x⟫_ℝ ∂μ := by
          simpa only [Pi.add_apply] using hABCDE
      _ = (((∫ x,
              -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 +
                (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 +
                (5 * alpha * stepped.blockGain / 2) * ‖Q x - G x‖ ^ 2 ∂μ) +
              ∫ x, (5 / 8) * stepped.L * alpha ^ 2 * ‖Z x‖ ^ 2 ∂μ) +
            ∫ x, ⟪M x, Z x⟫_ℝ ∂μ) := by
          rw [show (∫ x,
              -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 +
                (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 +
                (5 * alpha * stepped.blockGain / 2) * ‖Q x - G x‖ ^ 2 +
                (5 / 8) * stepped.L * alpha ^ 2 * ‖Z x‖ ^ 2 ∂μ) = _ by
            simpa only [Pi.add_apply] using hABCD]
      _ = _ := by
        rw [show (∫ x,
            -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 +
              (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 +
              (5 * alpha * stepped.blockGain / 2) * ‖Q x - G x‖ ^ 2 ∂μ) = _ by
          simpa only [Pi.add_apply] using hABC]
        rw [show (∫ x,
            -((5 * alpha * stepped.blockGain) / 8) * ‖G x‖ ^ 2 +
              (21 * alpha / (8 * stepped.blockGain)) * ‖D x‖ ^ 2 ∂μ) = _ by
          simpa only [Pi.add_apply] using hAB]
  rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hcancel, add_zero] at hmono
  have hnoise_coeff : 0 ≤ (5 / 8) * stepped.L * alpha ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) stepped.L_pos.le) (sq_nonneg alpha)
  have hnoise_scaled := mul_le_mul_of_nonneg_left hnoise.2 hnoise_coeff
  calc
    _ ≤ -((5 * alpha * stepped.blockGain) / 8) *
          (∫ omega, ‖G omega‖ ^ 2 ∂μ) +
        (21 * alpha / (8 * stepped.blockGain)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂μ) +
        (5 * alpha * stepped.blockGain / 2) *
          (∫ omega, ‖Q omega - G omega‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * alpha ^ 2 *
          (∫ omega, ‖Z omega‖ ^ 2 ∂μ) := hmono
    _ ≤ -((5 * alpha * stepped.blockGain) / 8) *
          (∫ omega, ‖G omega‖ ^ 2 ∂μ) +
        (21 * alpha / (8 * stepped.blockGain)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂μ) +
        (5 * alpha * stepped.blockGain / 2) *
          (∫ omega, ‖Q omega - G omega‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * alpha ^ 2 *
          (stepped.period * stepped.influenceSecondMoment * stepped.sigma ^ 2) := by
      gcongr
    _ = _ := by
      simp only [Q, G, D]
      rw [show stepped.period = setup.period by rfl,
        show stepped.influenceSecondMoment = setup.influenceSecondMoment by
          exact setup.withStepsize_influenceSecondMoment_eq alpha,
        show stepped.sigma = setup.sigma by rfl]
      ring

/-- Lemma 5.2 / (5.14): one-block descent for the hybrid center, on the
positive-stepsize domain used by Theorem 7.1. -/
theorem HybridCenterBlockDescent
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (k : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha)
    (halpha_small : alpha * setup.L * setup.blockGain ≤ 1 / 40) :
    let stepped := setup.withStepsize alpha
    ∫ ω,
        (stepped.hybridPotential (oracle.noise ω) (k + 1) -
          stepped.hybridPotential (oracle.noise ω) k) ∂μ ≤
      -((5 * alpha * stepped.blockGain) / 8) *
          (∫ ω, ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) +
        5 * alpha * stepped.blockGain * stepped.L ^ 2 *
          (∫ ω,
            ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
              stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
        (21 * alpha / (4 * stepped.blockGain)) *
          (∫ ω,
            (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
              ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ) +
        5 * stepped.L ^ 2 * alpha ^ 3 * stepped.blockGain *
          (∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 := by
  classical
  dsimp only
  let stepped := setup.withStepsize alpha
  change
    (∫ ω,
        (stepped.hybridPotential (oracle.noise ω) (k + 1) -
          stepped.hybridPotential (oracle.noise ω) k) ∂μ) ≤
      -((5 * alpha * stepped.blockGain) / 8) *
          (∫ ω, ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) +
        5 * alpha * stepped.blockGain * stepped.L ^ 2 *
          (∫ ω,
            ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
              stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
        (21 * alpha / (4 * stepped.blockGain)) *
          (∫ ω,
            (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
              ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ) +
        5 * stepped.L ^ 2 * alpha ^ 3 * stepped.blockGain *
          (∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hinter := setup.hybrid_center_intermediate_descent
    μ oracle alpha k horacle halpha_pos halpha_small
  dsimp only at hinter
  have hphase_mem := stepped.blockPhaseError_memLp_two
    μ oracle horacle_stepped k
  have hhigh_mem : MemLp (fun omega =>
      stepped.highPassIncrement (oracle.noise omega) k) 2 μ := by
    simpa only [highPassIncrement] using
      (stepped.meanLiftCorrection_memLp_two μ oracle horacle_stepped (k + 1)).sub
        (stepped.meanLiftCorrection_memLp_two μ oracle horacle_stepped k)
  have hphase_sq : Integrable (fun omega =>
      ‖stepped.blockPhaseError (oracle.noise omega) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hphase_mem.aestronglyMeasurable).1 hphase_mem
  have hhigh_sq : Integrable (fun omega =>
      ‖stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hhigh_mem.aestronglyMeasurable).1 hhigh_mem
  have hdiff_mem := hphase_mem.sub hhigh_mem
  have hdiff_sq : Integrable (fun omega =>
      ‖stepped.blockPhaseError (oracle.noise omega) k -
        stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hdiff_mem.aestronglyMeasurable).1 hdiff_mem
  have hdiff_bound :
      (∫ omega,
          ‖stepped.blockPhaseError (oracle.noise omega) k -
            stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2 ∂μ) ≤
        2 * (∫ omega,
          ‖stepped.blockPhaseError (oracle.noise omega) k‖ ^ 2 ∂μ) +
          2 * (∫ omega,
            ‖stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2 ∂μ) := by
    have hpoint (omega : Ω) :=
      SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        (stepped.blockPhaseError (oracle.noise omega) k)
        (-stepped.highPassIncrement (oracle.noise omega) k)
    have hmono := MeasureTheory.integral_mono hdiff_sq
      ((hphase_sq.const_mul 2).add (hhigh_sq.const_mul 2))
      (fun omega => by simpa [sub_eq_add_neg] using hpoint omega)
    simpa only [Pi.add_apply,
      MeasureTheory.integral_add (hphase_sq.const_mul 2) (hhigh_sq.const_mul 2),
      MeasureTheory.integral_const_mul] using hmono
  have hweighted : MemLp (fun omega =>
      weightedState (Node := Node) (E := E) (stepped.perronLeft 0)
        (stepped.primalState (oracle.noise omega) (stepped.blockStart k))) 2 μ := by
    unfold weightedState
    apply memLp_finset_sum Finset.univ
    intro i _hi
    simpa only [Pi.smul_apply] using
      ((stepped.generated_pushpull_coordinate_memLp μ oracle horacle_stepped
        (stepped.blockStart k)).1 i).const_smul (stepped.perronLeft 0 i)
  have havg_iter : MemLp (fun omega =>
      stepped.averageIterate (oracle.noise omega) (stepped.blockStart k)) 2 μ := by
    have hsum : MemLp (fun omega => ∑ i : Node,
        stepped.primalState (oracle.noise omega) (stepped.blockStart k) i) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (stepped.generated_pushpull_coordinate_memLp
        μ oracle horacle_stepped (stepped.blockStart k)).1 i
    simpa [averageIterate, arithmeticAverage] using
      hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hcenter_diff_mem : MemLp (fun omega =>
      stepped.blockStartHybridCenter (oracle.noise omega) k -
        stepped.averageIterate (oracle.noise omega) (stepped.blockStart k)) 2 μ := by
    simpa only [blockStartHybridCenter] using hweighted.sub havg_iter
  have heta_mem := stepped.noiseLiftCorrection_memLp_two
    μ oracle horacle_stepped k
  have hhybrid_mem : MemLp (fun omega =>
      stepped.hybridCenter (oracle.noise omega) k) 2 μ := by
    simpa only [hybridCenter, blockStartHybridCenter] using
      hweighted.sub (heta_mem.const_smul alpha)
  let KL : NNReal := ⟨stepped.L, stepped.L_pos.le⟩
  have havg_lip : LipschitzWith KL stepped.averageGradient := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL] using stepped.averageGradient_lipschitz_bound x y
  have hq_mem : MemLp (fun omega => stepped.averageGradient
      (stepped.hybridCenter (oracle.noise omega) k)) 2 μ :=
    memLp_two_comp_lipschitz stepped.averageGradient KL havg_lip hhybrid_mem
  have hg_mem : MemLp (fun omega =>
      stepped.blockAverageGradient (oracle.noise omega) k) 2 μ := by
    simpa only [blockAverageGradient, randomAverageIterate] using
      stepped.averageGradient_randomAverageIterate_memLp_two
        μ oracle horacle_stepped (stepped.blockStart k)
  have hgrad_diff_mem := hq_mem.sub hg_mem
  have hgrad_diff_sq : Integrable (fun omega =>
      ‖stepped.averageGradient (stepped.hybridCenter (oracle.noise omega) k) -
        stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hgrad_diff_mem.aestronglyMeasurable).1
      hgrad_diff_mem
  have hcenter_diff_sq : Integrable (fun omega =>
      ‖stepped.blockStartHybridCenter (oracle.noise omega) k -
        stepped.averageIterate (oracle.noise omega) (stepped.blockStart k)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hcenter_diff_mem.aestronglyMeasurable).1
      hcenter_diff_mem
  have heta_sq : Integrable (fun omega =>
      ‖stepped.noiseLiftCorrection (oracle.noise omega) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm heta_mem.aestronglyMeasurable).1 heta_mem
  have hgradient_bound :
      (∫ omega,
          ‖stepped.averageGradient
                (stepped.hybridCenter (oracle.noise omega) k) -
            stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) ≤
        2 * stepped.L ^ 2 *
          (∫ omega,
            ‖stepped.blockStartHybridCenter (oracle.noise omega) k -
              stepped.averageIterate (oracle.noise omega)
                (stepped.blockStart k)‖ ^ 2 ∂μ) +
          2 * stepped.L ^ 2 * alpha ^ 2 *
            (∫ omega,
              ‖stepped.noiseLiftCorrection (oracle.noise omega) k‖ ^ 2 ∂μ) := by
    simpa only [hybridCenter, blockAverageGradient] using
      (SOptLib.integral_norm_sq_lipschitz_sub_scaled_le_two
        μ stepped.averageGradient
        (fun omega => stepped.blockStartHybridCenter (oracle.noise omega) k)
        (fun omega => stepped.averageIterate (oracle.noise omega)
          (stepped.blockStart k))
        (fun omega => stepped.noiseLiftCorrection (oracle.noise omega) k)
        alpha stepped.L hgrad_diff_sq.aestronglyMeasurable hcenter_diff_sq heta_sq
        (ae_of_all μ fun omega => stepped.averageGradient_lipschitz_bound
          (stepped.blockStartHybridCenter (oracle.noise omega) k -
            alpha • stepped.noiseLiftCorrection (oracle.noise omega) k)
          (stepped.averageIterate (oracle.noise omega) (stepped.blockStart k))))
  have hDcoeff : 0 ≤ 21 * alpha / (8 * stepped.blockGain) := by
    exact div_nonneg
      (mul_nonneg (by norm_num) halpha_pos.le)
      (mul_nonneg (by norm_num) stepped.blockGain_pos.le)
  have hGcoeff : 0 ≤ 5 * alpha * stepped.blockGain / 2 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) halpha_pos.le)
        stepped.blockGain_pos.le)
      (by norm_num)
  have hdiff_scaled := mul_le_mul_of_nonneg_left hdiff_bound hDcoeff
  have hgradient_scaled := mul_le_mul_of_nonneg_left hgradient_bound hGcoeff
  have hphase_high_eq :
      (∫ omega,
          (‖stepped.blockPhaseError (oracle.noise omega) k‖ ^ 2 +
            ‖stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2) ∂μ) =
        (∫ omega,
            ‖stepped.blockPhaseError (oracle.noise omega) k‖ ^ 2 ∂μ) +
          ∫ omega,
            ‖stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2 ∂μ := by
    exact MeasureTheory.integral_add hphase_sq hhigh_sq
  calc
    _ ≤ -((5 * alpha * stepped.blockGain) / 8) *
          (∫ omega, ‖stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (21 * alpha / (8 * stepped.blockGain)) *
          (∫ omega,
            ‖stepped.blockPhaseError (oracle.noise omega) k -
              stepped.highPassIncrement (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (5 * alpha * stepped.blockGain / 2) *
          (∫ omega,
            ‖stepped.averageGradient
                (stepped.hybridCenter (oracle.noise omega) k) -
              stepped.blockAverageGradient (oracle.noise omega) k‖ ^ 2 ∂μ) +
        (5 / 8) * stepped.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 := hinter
    _ ≤ _ := by
      rw [hphase_high_eq]
      ring_nf at hdiff_scaled hgradient_scaled ⊢
      linarith

/-- The summed one-block descent after the three feedback absorptions in
Theorem 7.1, before telescoping the hybrid-potential endpoints. -/
theorem theoremSevenOne_summed_hybrid_descent
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaMax) :
    let stepped := setup.withStepsize alpha
    Finset.sum (Finset.range K) (fun k =>
        ∫ ω,
          (stepped.hybridPotential (oracle.noise ω) (k + 1) -
            stepped.hybridPotential (oracle.noise ω) k) ∂μ) ≤
      -((alpha * setup.blockGain) / 2) *
          stepped.blockGradientEnergy μ oracle K +
        (21 * alpha / (4 * setup.blockGain)) *
          setup.stateFeedbackInitialConstant *
          setup.initialGradientHeterogeneity ^ 2 +
        setup.L * (setup.period : ℝ) * setup.influenceSecondMoment *
          setup.sigma ^ 2 * alpha ^ 2 * K := by
  classical
  dsimp only
  let stepped := setup.withStepsize alpha
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  rcases setup.alphaMax_absorption_budget alpha halpha_pos halpha_le with
    ⟨hstable, hsmall, heta_budget, hrandom_budget, hstationary_budget⟩
  have hH_eq : stepped.blockGain = setup.blockGain := by
    exact setup.withStepsize_blockGain_eq alpha
  have hL_eq : stepped.L = setup.L := by rfl
  have hstep (k : ℕ) :
      (∫ ω,
          (stepped.hybridPotential (oracle.noise ω) (k + 1) -
            stepped.hybridPotential (oracle.noise ω) k) ∂μ) ≤
        -((5 * alpha * setup.blockGain) / 8) *
            (∫ ω, ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) +
          5 * alpha * setup.blockGain * setup.L ^ 2 *
            (∫ ω,
              ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)‖ ^ 2 ∂μ) +
          (21 * alpha / (4 * setup.blockGain)) *
            (∫ ω,
              (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
                ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ) +
          5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain *
            (∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) +
          (5 / 8) * setup.L * (setup.period : ℝ) *
            setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 := by
    have hraw := setup.HybridCenterBlockDescent μ oracle alpha k horacle
      halpha_pos hsmall
    dsimp only at hraw
    rw [hH_eq, hL_eq] at hraw
    exact hraw
  have hsum :
      Finset.sum (Finset.range K) (fun k =>
          ∫ ω,
            (stepped.hybridPotential (oracle.noise ω) (k + 1) -
              stepped.hybridPotential (oracle.noise ω) k) ∂μ) ≤
        -((5 * alpha * setup.blockGain) / 8) *
            stepped.blockGradientEnergy μ oracle K +
          (∑ k ∈ Finset.range K,
            (5 * alpha * setup.blockGain * setup.L ^ 2 *
                (∫ ω,
                  ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                    stepped.averageIterate (oracle.noise ω)
                      (stepped.blockStart k)‖ ^ 2 ∂μ) +
              (21 * alpha / (4 * setup.blockGain)) *
                (∫ ω,
                  (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
                    ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ))) +
          5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain *
            (∑ k ∈ Finset.range K,
              ∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) +
          (5 / 8) * setup.L * (setup.period : ℝ) *
            setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 * K := by
    calc
      _ ≤ ∑ k ∈ Finset.range K,
          (-((5 * alpha * setup.blockGain) / 8) *
              (∫ ω, ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) +
            5 * alpha * setup.blockGain * setup.L ^ 2 *
              (∫ ω,
                ‖stepped.blockStartHybridCenter (oracle.noise ω) k -
                  stepped.averageIterate (oracle.noise ω)
                    (stepped.blockStart k)‖ ^ 2 ∂μ) +
            (21 * alpha / (4 * setup.blockGain)) *
              (∫ ω,
                (‖stepped.blockPhaseError (oracle.noise ω) k‖ ^ 2 +
                  ‖stepped.highPassIncrement (oracle.noise ω) k‖ ^ 2) ∂μ) +
            5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain *
              (∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) +
            (5 / 8) * setup.L * (setup.period : ℝ) *
              setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2) := by
            exact Finset.sum_le_sum fun k _hk => hstep k
      _ = _ := by
        unfold blockGradientEnergy
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
        ring
  have hpack := setup.hcld_state_terms_sum_le_feedback_energy
    μ oracle alpha K horacle halpha_pos
  dsimp only at hpack
  have hsum_packed :
      Finset.sum (Finset.range K) (fun k =>
          ∫ ω,
            (stepped.hybridPotential (oracle.noise ω) (k + 1) -
              stepped.hybridPotential (oracle.noise ω) k) ∂μ) ≤
        -((5 * alpha * setup.blockGain) / 8) *
            stepped.blockGradientEnergy μ oracle K +
          (21 * alpha / (4 * setup.blockGain)) *
            stepped.stateFeedbackEnergySum μ oracle K +
          5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain *
            (∑ k ∈ Finset.range K,
              ∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) +
          (5 / 8) * setup.L * (setup.period : ℝ) *
            setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 * K := by
    linarith
  have hST := setup.JointStateEstimateST_universe μ oracle alpha K horacle
    halpha_pos hstable
  have hH_pos : 0 < setup.blockGain := setup.blockGain_pos
  have hG_nonneg :
      0 ≤ stepped.blockGradientEnergy μ oracle K := by
    unfold blockGradientEnergy
    exact Finset.sum_nonneg fun k _hk =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hfeedback_scale_nonneg :
      0 ≤ 21 * alpha / (4 * setup.blockGain) := by
    positivity
  have hST_scaled := mul_le_mul_of_nonneg_left hST hfeedback_scale_nonneg
  have hperron : stepped.perronSequences = setup.perronSequences := by
    apply setup.perronSequences_unique stepped.perronSequences
    · simpa [stepped, withStepsize, PerronSequencesEquations] using
        stepped.perronSequences_spec.1
    · simpa [stepped, withStepsize, PerronSequencesPositivePeriodic] using
        stepped.perronSequences_spec.2.1
  have hleft (t : ℕ) : stepped.perronLeft t = setup.perronLeft t := by
    unfold perronLeft
    exact congrArg (fun seqs => seqs.1 t) hperron
  have hpull (t j : ℕ) :
      stepped.pullLiftProduct t j = setup.pullLiftProduct t j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [pullLiftProduct]
        rw [ih]
        rfl
  have hcorrectedLift (t : ℕ) (W : ZeroSumState Node E) :
      stepped.correctedLift t W = setup.correctedLift t W := by
    unfold correctedLift
    apply tsum_congr
    intro j
    rw [hleft]
    rfl
  have hnoiseTrackerErrorZeroSum (noise : NoisePath Node E) (t : ℕ) :
      stepped.noiseTrackerErrorZeroSum noise t =
        setup.noiseTrackerErrorZeroSum noise t := by
    apply Subtype.ext
    rfl
  have hnoiseLiftCorrection (noise : NoisePath Node E) (k : ℕ) :
      stepped.noiseLiftCorrection noise k = setup.noiseLiftCorrection noise k := by
    unfold noiseLiftCorrection
    rw [hcorrectedLift, hnoiseTrackerErrorZeroSum]
    congr 2
  have heta_point (k : ℕ) :
      (∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        setup.noiseTrackerFilterConstant * setup.sigma ^ 2 := by
    simpa only [hnoiseLiftCorrection] using
      (setup.NoiseTrackerFilterBound_universe μ oracle horacle k)
  have heta_sum :
      (∑ k ∈ Finset.range K,
          ∫ ω, ‖stepped.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        K * (setup.noiseTrackerFilterConstant * setup.sigma ^ 2) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range K,
          setup.noiseTrackerFilterConstant * setup.sigma ^ 2 := by
        exact Finset.sum_le_sum fun k _hk => heta_point k
      _ = K * (setup.noiseTrackerFilterConstant * setup.sigma ^ 2) := by simp
  have heta_scale_nonneg :
      0 ≤ 5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain := by
    positivity
  have heta_scaled := mul_le_mul_of_nonneg_left heta_sum heta_scale_nonneg
  have hstationary_absorb :
      (21 * alpha / (4 * setup.blockGain)) *
          (setup.stationaryFeedbackConstant * alpha ^ 2 *
            setup.blockGain ^ 2 * setup.L ^ 2 *
              stepped.blockGradientEnergy μ oracle K) ≤
        (alpha * setup.blockGain / 8) *
          stepped.blockGradientEnergy μ oracle K := by
    calc
      _ = ((alpha * setup.blockGain / 8) *
              stepped.blockGradientEnergy μ oracle K) *
            (42 * setup.stationaryFeedbackConstant * alpha ^ 2 * setup.L ^ 2) := by
          field_simp [ne_of_gt hH_pos]
          <;> ring
      _ ≤ ((alpha * setup.blockGain / 8) *
              stepped.blockGradientEnergy μ oracle K) * 1 := by
          exact mul_le_mul_of_nonneg_left hstationary_budget (by positivity)
      _ = _ := by ring
  have hrandom_absorb :
      (21 * alpha / (4 * setup.blockGain)) *
          (setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
            (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K) ≤
        (1 / 4 : ℝ) * setup.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 * K := by
    have hfactor_nonneg :
        0 ≤ setup.L * alpha ^ 2 * setup.sigma ^ 2 * K /
          (4 * setup.blockGain) := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg setup.L_pos.le (sq_nonneg alpha))
            (sq_nonneg setup.sigma)) (Nat.cast_nonneg K))
        (mul_nonneg (by norm_num) hH_pos.le)
    calc
      _ = (setup.L * alpha ^ 2 * setup.sigma ^ 2 * K /
              (4 * setup.blockGain)) *
            (21 * setup.randomFeedbackConstant *
              (nodeCount (Node := Node) : ℝ) * setup.L * alpha) := by
          field_simp [ne_of_gt hH_pos]
          <;> ring
      _ ≤ (setup.L * alpha ^ 2 * setup.sigma ^ 2 * K /
              (4 * setup.blockGain)) *
            ((setup.period : ℝ) * setup.influenceSecondMoment *
              setup.blockGain) := by
          exact mul_le_mul_of_nonneg_left hrandom_budget hfactor_nonneg
      _ = _ := by
          field_simp [ne_of_gt hH_pos]
          <;> ring
  have heta_absorb :
      5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain *
          (K * (setup.noiseTrackerFilterConstant * setup.sigma ^ 2)) ≤
        (1 / 8 : ℝ) * setup.L * (setup.period : ℝ) *
          setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 * K := by
    have hfactor_nonneg :
        0 ≤ setup.L * alpha ^ 2 * setup.sigma ^ 2 * K / 8 := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg setup.L_pos.le (sq_nonneg alpha))
            (sq_nonneg setup.sigma)) (Nat.cast_nonneg K)) (by norm_num)
    calc
      _ = (setup.L * alpha ^ 2 * setup.sigma ^ 2 * K / 8) *
            (40 * setup.L * setup.blockGain *
              setup.noiseTrackerFilterConstant * alpha) := by ring
      _ ≤ (setup.L * alpha ^ 2 * setup.sigma ^ 2 * K / 8) *
            ((setup.period : ℝ) * setup.influenceSecondMoment) := by
          exact mul_le_mul_of_nonneg_left heta_budget hfactor_nonneg
      _ = _ := by ring
  have hST_scaled' :
      (21 * alpha / (4 * setup.blockGain)) *
          stepped.stateFeedbackEnergySum μ oracle K ≤
        (21 * alpha / (4 * setup.blockGain)) *
            (setup.stateFeedbackInitialConstant *
              setup.initialGradientHeterogeneity ^ 2) +
          (21 * alpha / (4 * setup.blockGain)) *
            (setup.stationaryFeedbackConstant * alpha ^ 2 *
              setup.blockGain ^ 2 * setup.L ^ 2 *
                stepped.blockGradientEnergy μ oracle K) +
          (21 * alpha / (4 * setup.blockGain)) *
            (setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K) := by
    calc
      _ ≤ (21 * alpha / (4 * setup.blockGain)) *
          (setup.stateFeedbackInitialConstant *
              setup.initialGradientHeterogeneity ^ 2 +
            setup.stationaryFeedbackConstant * alpha ^ 2 *
              setup.blockGain ^ 2 * setup.L ^ 2 *
                stepped.blockGradientEnergy μ oracle K +
            setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K) :=
        hST_scaled
      _ = _ := by ring
  have hsum_substituted :
      Finset.sum (Finset.range K) (fun k =>
          ∫ ω,
            (stepped.hybridPotential (oracle.noise ω) (k + 1) -
              stepped.hybridPotential (oracle.noise ω) k) ∂μ) ≤
        -((5 * alpha * setup.blockGain) / 8) *
            stepped.blockGradientEnergy μ oracle K +
          (21 * alpha / (4 * setup.blockGain)) *
            (setup.stateFeedbackInitialConstant *
              setup.initialGradientHeterogeneity ^ 2) +
          (21 * alpha / (4 * setup.blockGain)) *
            (setup.stationaryFeedbackConstant * alpha ^ 2 *
              setup.blockGain ^ 2 * setup.L ^ 2 *
                stepped.blockGradientEnergy μ oracle K) +
          (21 * alpha / (4 * setup.blockGain)) *
            (setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K) +
          5 * setup.L ^ 2 * alpha ^ 3 * setup.blockGain *
            (K * (setup.noiseTrackerFilterConstant * setup.sigma ^ 2)) +
          (5 / 8) * setup.L * (setup.period : ℝ) *
            setup.influenceSecondMoment * setup.sigma ^ 2 * alpha ^ 2 * K := by
    linarith [hsum_packed, hST_scaled', heta_scaled]
  linarith [hsum_substituted, hstationary_absorb, hrandom_absorb, heta_absorb]

/- Equation (7.5): telescope the integrable hybrid-potential endpoints in the
summed descent inequality and divide by the positive block descent scale. -/
theorem theoremSevenOne_blockGradientEnergy_bound_raw
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaMax) :
    (setup.withStepsize alpha).blockGradientEnergy μ oracle K ≤
      2 * setup.Delta / (alpha * setup.blockGain) +
        (21 * setup.stateFeedbackInitialConstant /
            (2 * setup.blockGain ^ 2)) *
          setup.initialGradientHeterogeneity ^ 2 +
          (2 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
            alpha * setup.sigma ^ 2 * K := by
  classical
  let stepped := setup.withStepsize alpha
  have hVint (k : ℕ) : Integrable (fun ω =>
      stepped.hybridPotential (oracle.noise ω) k) μ := by
    simpa only [stepped] using
      setup.hybridPotential_integrable μ oracle alpha k horacle
  have hcenter_zero (noise : NoisePath Node E) :
      stepped.hybridCenter noise 0 = setup.x0 := by
    have hchi : stepped.blockStartHybridCenter noise 0 = setup.x0 := by
      unfold blockStartHybridCenter blockStart
      simp only [zero_mul]
      rw [stepped.primalState_zero]
      unfold initialPrimal weightedState
      rw [← Finset.sum_smul]
      have hsum : ∑ i : Node, stepped.perronLeft 0 i = 1 := by
        simpa only [rowSum] using stepped.perronLeft_sum 0
      rw [hsum, one_smul]
      rfl
    let z0 : ZeroSumState Node E := ⟨0, by simp⟩
    have hnoise_zero :
        stepped.noiseTrackerErrorZeroSum noise 0 = z0 := by
      apply Subtype.ext
      simp [noiseTrackerErrorZeroSum, noiseTrackerError,
        SOptLib.recursiveIterateProcess, z0]
    have heta : stepped.noiseLiftCorrection noise 0 = 0 := by
      unfold noiseLiftCorrection
      simp only [blockStart, zero_mul]
      rw [hnoise_zero]
      simp [correctedLift, correctedLiftSeriesTerm, weightedState, leftMul, z0]
    simp only [hybridCenter, hchi, heta, smul_zero, sub_zero]
  have hVzero (ω : Ω) :
      stepped.hybridPotential (oracle.noise ω) 0 = setup.objective setup.x0 := by
    simp only [hybridPotential, hcenter_zero]
    rfl
  have htel := integral_sum_telescope_bound_of_pointwise_lower_bound
    (P := μ) (Finset.range K)
    (fun k ω => stepped.hybridPotential (oracle.noise ω) k -
      stepped.hybridPotential (oracle.noise ω) (k + 1))
    (fun ω => stepped.hybridPotential (oracle.noise ω) K)
    (setup.objective setup.x0) setup.objectiveInfimum
    (fun k _hk => (hVint k).sub (hVint (k + 1)))
    (fun ω => by
      rw [Finset.sum_range_sub']
      exact congrArg (fun z => z - stepped.hybridPotential (oracle.noise ω) K)
        (hVzero ω))
    (fun ω => by
      unfold hybridPotential objectiveInfimum
      exact SOptLib.objectiveInfimumValue_le
        (by simpa [stepped, withStepsize, objective, Set.image_univ] using
          setup.objective_bddBelow_source)
        (Set.mem_univ _))
  have hflip :
      -(Finset.sum (Finset.range K) (fun k =>
          ∫ ω, (stepped.hybridPotential (oracle.noise ω) (k + 1) -
            stepped.hybridPotential (oracle.noise ω) k) ∂μ)) =
        Finset.sum (Finset.range K) (fun k =>
          ∫ ω, (stepped.hybridPotential (oracle.noise ω) k -
            stepped.hybridPotential (oracle.noise ω) (k + 1)) ∂μ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← MeasureTheory.integral_neg]
    congr 1
    funext ω
    ring
  have htelescope_lower :
      -setup.Delta ≤
        Finset.sum (Finset.range K) (fun k =>
          ∫ ω, (stepped.hybridPotential (oracle.noise ω) (k + 1) -
            stepped.hybridPotential (oracle.noise ω) k) ∂μ) := by
    rw [← hflip] at htel
    unfold Delta at *
    linarith
  have hdescent := setup.theoremSevenOne_summed_hybrid_descent
    μ oracle alpha K horacle halpha_pos halpha_le
  dsimp only at hdescent
  have hraw :
      (alpha * setup.blockGain / 2) *
          stepped.blockGradientEnergy μ oracle K ≤
        setup.Delta +
          (21 * alpha / (4 * setup.blockGain)) *
            setup.stateFeedbackInitialConstant *
            setup.initialGradientHeterogeneity ^ 2 +
          setup.L * (setup.period : ℝ) * setup.influenceSecondMoment *
            setup.sigma ^ 2 * alpha ^ 2 * K := by
    linarith
  have hscale : 0 < alpha * setup.blockGain / 2 := by
    exact div_pos (mul_pos halpha_pos setup.blockGain_pos) (by norm_num)
  calc
    stepped.blockGradientEnergy μ oracle K ≤
        (setup.Delta +
          (21 * alpha / (4 * setup.blockGain)) *
            setup.stateFeedbackInitialConstant *
            setup.initialGradientHeterogeneity ^ 2 +
          setup.L * (setup.period : ℝ) * setup.influenceSecondMoment *
            setup.sigma ^ 2 * alpha ^ 2 * K) /
          (alpha * setup.blockGain / 2) := (le_div_iff₀ hscale).2 (by
            simpa [mul_comm] using hraw)
    _ = 2 * setup.Delta / (alpha * setup.blockGain) +
        (21 * setup.stateFeedbackInitialConstant /
            (2 * setup.blockGain ^ 2)) *
          setup.initialGradientHeterogeneity ^ 2 +
          (2 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
            alpha * setup.sigma ^ 2 * K := by
      unfold blockGain
      have hp : (setup.period : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt setup.period_pos)
      field_simp [ne_of_gt halpha_pos, hp, ne_of_gt setup.influenceGain_pos]
      <;> ring

/-- The shorthand `J = 21 C_{B,0} / (2 H^2)` from
`#/main_theorem/proof/4`. -/
noncomputable def theoremSevenOneJ : ℝ :=
  21 * setup.stateFeedbackInitialConstant / (2 * setup.blockGain ^ 2)

/-- Source-form unfolding of `J` from `#/main_theorem/proof/4`. -/
theorem theoremSevenOneJ_eq :
    setup.theoremSevenOneJ =
      21 * setup.stateFeedbackInitialConstant / (2 * setup.blockGain ^ 2) := by
  rfl

/- Source-notation form of equation (7.5), obtained from the endpoint
telescope above by folding the printed coefficient `J`. -/
theorem theoremSevenOne_blockGradientEnergy_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaMax) :
    (setup.withStepsize alpha).blockGradientEnergy μ oracle K ≤
      2 * setup.Delta / (alpha * setup.blockGain) +
        setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
          (2 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
            alpha * setup.sigma ^ 2 * K := by
  rw [setup.theoremSevenOneJ_eq]
  exact setup.theoremSevenOne_blockGradientEnergy_bound_raw
    μ oracle alpha K horacle halpha_pos halpha_le

/-- The source coefficient `a = (2 L^2 p^2 / n) Dhat_g` from
`#/main_theorem/proof/9`. -/
noncomputable def theoremSevenOnePreRateA : ℝ :=
  (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
      (nodeCount (Node := Node) : ℝ)) *
    setup.finalDisplacementGradientConstant

/-- Source-form unfolding of `a = (2 L^2 p^2 / n) Dhat_g` from
`#/main_theorem/proof/9`. -/
theorem theoremSevenOnePreRateA_eq :
    setup.theoremSevenOnePreRateA =
      (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) *
        setup.finalDisplacementGradientConstant := by
  rfl

/-- The source coefficient `b = (2 L^2 p^2 / n) Dhat_0` from
`#/main_theorem/proof/9`. -/
noncomputable def theoremSevenOnePreRateB : ℝ :=
  (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
      (nodeCount (Node := Node) : ℝ)) *
    setup.finalDisplacementInitialConstant

/-- Source-form unfolding of `b = (2 L^2 p^2 / n) Dhat_0` from
`#/main_theorem/proof/9`. -/
theorem theoremSevenOnePreRateB_eq :
    setup.theoremSevenOnePreRateB =
      (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) *
        setup.finalDisplacementInitialConstant := by
  rfl

/-- The source coefficient `d = 2 L^2 p^2 Dhat_sigma` from
`#/main_theorem/proof/9`. -/
noncomputable def theoremSevenOnePreRateD : ℝ :=
  2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 *
    setup.finalDisplacementNoiseConstant

/-- Source-form unfolding of `d = 2 L^2 p^2 Dhat_sigma` from
`#/main_theorem/proof/9`. -/
theorem theoremSevenOnePreRateD_eq :
    setup.theoremSevenOnePreRateD =
      2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 *
        setup.finalDisplacementNoiseConstant := by
  rfl

/- Arithmetic facts for the complete block chosen by
`K = floor((T-1)/p)+1 = ceil(T/p)`. -/
theorem theoremSevenOne_completeBlockCeiling_facts
    (T : ℕ) (hT : 1 ≤ T) :
    let K := (T - 1) / setup.period + 1
    let N := setup.completeBlockHorizon K
    T ≤ N ∧ K ≤ T ∧ N ≤ setup.period * T ∧
      N ≤ T + setup.period - 1 ∧ N - T ≤ setup.period - 1 := by
  dsimp only
  let q := (T - 1) / setup.period
  have hqmul : q * setup.period ≤ T - 1 := by
    exact Nat.div_mul_le_self (T - 1) setup.period
  have hqle : q ≤ T - 1 := by
    exact Nat.div_le_self (T - 1) setup.period
  have hdecomp :
      q * setup.period + (T - 1) % setup.period = T - 1 := by
    simpa [q, Nat.mul_comm] using (Nat.div_add_mod (T - 1) setup.period)
  have hmod : (T - 1) % setup.period < setup.period :=
    Nat.mod_lt _ setup.period_pos
  have hcover : T ≤ (q + 1) * setup.period := by
    rw [Nat.add_mul]
    omega
  have hKle : q + 1 ≤ T := by omega
  have hNle : (q + 1) * setup.period ≤ setup.period * T := by
    nlinarith
  have hNnear : (q + 1) * setup.period ≤ T + setup.period - 1 := by
    rw [Nat.add_mul]
    omega
  have hsub : (q + 1) * setup.period - T ≤ setup.period - 1 := by
    omega
  simpa [q, completeBlockHorizon] using
    And.intro hcover (And.intro hKle (And.intro hNle (And.intro hNnear hsub)))

/- Equation (7.8): extend an arbitrary positive horizon to its final complete
block, insert the Section 6 displacement estimate and (7.5), and isolate the
two leading terms from the full transient bracket. -/
theorem theoremSevenOne_preRate_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaMax) :
    let K := (T - 1) / setup.period + 1
    let N := setup.completeBlockHorizon K
    ((T : ℝ)⁻¹) *
        (Finset.sum (Finset.range T) fun t =>
          (setup.withStepsize alpha).expectedGradientNormSq μ oracle t) ≤
      4 * setup.Delta /
          (alpha * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * (T : ℝ)) +
        (4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
            alpha * setup.sigma ^ 2 +
          (1 / (T : ℝ)) *
            ((4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
                alpha * setup.sigma ^ 2 * ((N : ℝ) - (T : ℝ)) +
              2 * (setup.period : ℝ) * setup.theoremSevenOneJ *
                setup.initialGradientHeterogeneity ^ 2 +
              2 * setup.theoremSevenOnePreRateA * alpha * setup.Delta /
                setup.blockGain +
              setup.theoremSevenOnePreRateA * alpha ^ 2 *
                setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
              setup.theoremSevenOnePreRateB * alpha ^ 2 *
                setup.initialGradientHeterogeneity ^ 2 +
              2 * setup.theoremSevenOnePreRateA * setup.L *
                setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
                  alpha ^ 3 * setup.sigma ^ 2 * K +
              setup.theoremSevenOnePreRateD * alpha ^ 2 *
                setup.sigma ^ 2 * N) := by
  classical
  dsimp only
  let stepped := setup.withStepsize alpha
  let K := (T - 1) / setup.period + 1
  let N := setup.completeBlockHorizon K
  have hfacts := setup.theoremSevenOne_completeBlockCeiling_facts T hT
  change T ≤ N ∧ K ≤ T ∧ N ≤ setup.period * T ∧
      N ≤ T + setup.period - 1 ∧ N - T ≤ setup.period - 1 at hfacts
  rcases hfacts with ⟨hTN, hKT, hNpT, hNnear, hNTsub⟩
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hprefix :
      Finset.sum (Finset.range T) (fun t =>
          stepped.expectedGradientNormSq μ oracle t) ≤
        Finset.sum (Finset.range N) (fun t =>
          stepped.expectedGradientNormSq μ oracle t) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hTN)
    intro t _htN _htT
    unfold expectedGradientNormSq
    exact MeasureTheory.integral_nonneg fun _ω => sq_nonneg _
  have hall0 := stepped.allTimeAverageGradient_energy_bound
    μ oracle K horacle_stepped
  dsimp only at hall0
  have hall :
      Finset.sum (Finset.range N) (fun t =>
          stepped.expectedGradientNormSq μ oracle t) ≤
        2 * (setup.period : ℝ) * stepped.blockGradientEnergy μ oracle K +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
              stepped.displacementEnergy μ oracle N := by
    simpa [N, stepped, withStepsize, expectedGradientNormSq,
      randomAverageIterate] using hall0
  have hstable : alpha ≤ setup.alphaStable :=
    halpha_le.trans setup.alphaMax_le_alphaStable
  have hsection0 := setup.SectionSixFinalDisplacementConsensusEstimates_universe
    μ oracle alpha K horacle halpha_pos hstable
  dsimp only at hsection0
  have hsection : stepped.displacementEnergy μ oracle N ≤
      alpha ^ 2 *
        (setup.finalDisplacementInitialConstant *
            setup.initialGradientHeterogeneity ^ 2 +
          setup.finalDisplacementGradientConstant *
            stepped.blockGradientEnergy μ oracle K +
          setup.finalDisplacementNoiseConstant *
            (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N) := by
    simpa [N, stepped] using hsection0.1
  have hnpos : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast nodeCount_pos (Node := Node)
  have hcD : 0 ≤ 2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
      (nodeCount (Node := Node) : ℝ) := by positivity
  have hsection_scaled := mul_le_mul_of_nonneg_left hsection hcD
  have hSTall :
      Finset.sum (Finset.range T) (fun t =>
          stepped.expectedGradientNormSq μ oracle t) ≤
        (2 * (setup.period : ℝ) +
            setup.theoremSevenOnePreRateA * alpha ^ 2) *
              stepped.blockGradientEnergy μ oracle K +
          setup.theoremSevenOnePreRateB * alpha ^ 2 *
            setup.initialGradientHeterogeneity ^ 2 +
          setup.theoremSevenOnePreRateD * alpha ^ 2 *
            setup.sigma ^ 2 * N := by
    calc
      _ ≤ Finset.sum (Finset.range N) (fun t =>
          stepped.expectedGradientNormSq μ oracle t) := hprefix
      _ ≤ 2 * (setup.period : ℝ) * stepped.blockGradientEnergy μ oracle K +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
              stepped.displacementEnergy μ oracle N := hall
      _ ≤ 2 * (setup.period : ℝ) * stepped.blockGradientEnergy μ oracle K +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
            (alpha ^ 2 *
              (setup.finalDisplacementInitialConstant *
                  setup.initialGradientHeterogeneity ^ 2 +
                setup.finalDisplacementGradientConstant *
                  stepped.blockGradientEnergy μ oracle K +
                setup.finalDisplacementNoiseConstant *
                  (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N)) :=
        add_le_add le_rfl hsection_scaled
      _ = _ := by
        rw [setup.theoremSevenOnePreRateA_eq,
          setup.theoremSevenOnePreRateB_eq,
          setup.theoremSevenOnePreRateD_eq]
        field_simp [ne_of_gt hnpos]
        <;> ring
  have hDg : 0 ≤ setup.finalDisplacementGradientConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨1, by decide⟩
  have ha : 0 ≤ setup.theoremSevenOnePreRateA := by
    rw [setup.theoremSevenOnePreRateA_eq]
    exact mul_nonneg hcD hDg
  have hGcoeff :
      0 ≤ 2 * (setup.period : ℝ) +
        setup.theoremSevenOnePreRateA * alpha ^ 2 := by positivity
  have hG := setup.theoremSevenOne_blockGradientEnergy_bound
    μ oracle alpha K horacle halpha_pos halpha_le
  have hGscaled := mul_le_mul_of_nonneg_left hG hGcoeff
  have hsubstituted :
      Finset.sum (Finset.range T) (fun t =>
          stepped.expectedGradientNormSq μ oracle t) ≤
        (2 * (setup.period : ℝ) +
            setup.theoremSevenOnePreRateA * alpha ^ 2) *
          (2 * setup.Delta / (alpha * setup.blockGain) +
            setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
            (2 * setup.L * setup.influenceSecondMoment /
                (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) * alpha * setup.sigma ^ 2 * K) +
          setup.theoremSevenOnePreRateB * alpha ^ 2 *
            setup.initialGradientHeterogeneity ^ 2 +
          setup.theoremSevenOnePreRateD * alpha ^ 2 *
            setup.sigma ^ 2 * N := by
    exact hSTall.trans (add_le_add (add_le_add hGscaled le_rfl) le_rfl)
  have hscaled := mul_le_mul_of_nonneg_left hsubstituted
    (inv_nonneg.mpr hTreal.le)
  calc
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
        stepped.expectedGradientNormSq μ oracle t) ≤
      ((T : ℝ)⁻¹) *
        ((2 * (setup.period : ℝ) +
            setup.theoremSevenOnePreRateA * alpha ^ 2) *
          (2 * setup.Delta / (alpha * setup.blockGain) +
            setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
            (2 * setup.L * setup.influenceSecondMoment /
                (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) * alpha * setup.sigma ^ 2 * K) +
          setup.theoremSevenOnePreRateB * alpha ^ 2 *
            setup.initialGradientHeterogeneity ^ 2 +
          setup.theoremSevenOnePreRateD * alpha ^ 2 *
            setup.sigma ^ 2 * N) := hscaled
    _ = 4 * setup.Delta /
          (alpha * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * (T : ℝ)) +
        (4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
            alpha * setup.sigma ^ 2 +
          (1 / (T : ℝ)) *
            ((4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
                alpha * setup.sigma ^ 2 * ((N : ℝ) - (T : ℝ)) +
              2 * (setup.period : ℝ) * setup.theoremSevenOneJ *
                setup.initialGradientHeterogeneity ^ 2 +
              2 * setup.theoremSevenOnePreRateA * alpha * setup.Delta /
                setup.blockGain +
              setup.theoremSevenOnePreRateA * alpha ^ 2 *
                setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
              setup.theoremSevenOnePreRateB * alpha ^ 2 *
                setup.initialGradientHeterogeneity ^ 2 +
              2 * setup.theoremSevenOnePreRateA * setup.L *
                setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
                  alpha ^ 3 * setup.sigma ^ 2 * K +
              setup.theoremSevenOnePreRateD * alpha ^ 2 *
                setup.sigma ^ 2 * N) := by
      simp only [N, completeBlockHorizon, Nat.cast_mul]
      unfold blockGain
      have hp : (setup.period : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt setup.period_pos)
      field_simp [ne_of_gt hTreal, ne_of_gt halpha_pos, hp,
        ne_of_gt setup.influenceGain_pos]
      <;> ring

/-- Transient coefficient printed in (7.11), tied to the formula-defined
network/problem constants rather than supplied as an external witness.
Source: `#/main_theorem/proof/16`, where
`K_{I,N}=4Delta/(h alpha_max)+(4Lq/h)alpha_max sigma^2(p-1)+2pJH_0^2
+2a alpha_max Delta/H+a alpha_max^2 JH_0^2+b alpha_max^2 H_0^2
+2a alpha_max Delta/h+dpDelta/(Lq)`, with `a,b,d` from
`#/main_theorem/proof/9`. -/
noncomputable def theoremSevenOneTransientCoefficient : ℝ :=
  4 * setup.Delta / ((Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.alphaMax) +
    4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
        setup.alphaMax * setup.sigma ^ 2 * ((setup.period : ℝ) - 1) +
      2 * (setup.period : ℝ) *
          setup.theoremSevenOneJ *
          setup.initialGradientHeterogeneity ^ 2 +
        2 * setup.theoremSevenOnePreRateA * setup.alphaMax * setup.Delta /
            setup.blockGain +
          setup.theoremSevenOnePreRateA * setup.alphaMax ^ 2 *
              setup.theoremSevenOneJ *
              setup.initialGradientHeterogeneity ^ 2 +
            setup.theoremSevenOnePreRateB * setup.alphaMax ^ 2 *
                setup.initialGradientHeterogeneity ^ 2 +
              2 * setup.theoremSevenOnePreRateA * setup.alphaMax *
                  setup.Delta / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) +
                setup.theoremSevenOnePreRateD * (setup.period : ℝ) *
                  setup.Delta / (setup.L * setup.influenceSecondMoment)

/-- Family-level asymptotic notation `n_eff = Θ(n)`. -/
def EffectiveNodeCountThetaN (neff : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, ∃ N0 : ℕ, 0 < c ∧ c ≤ C ∧
    ∀ n : ℕ, N0 ≤ n →
      c * ((n + 1 : ℕ) : ℝ) ≤ neff n ∧
        neff n ≤ C * ((n + 1 : ℕ) : ℝ)

/-- The corollary's regime `T/n -> infinity`. -/
def TimeOverNodeDiverges (T : ℕ → ℕ) : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    M * ((n + 1 : ℕ) : ℝ) ≤ (T n : ℝ)

/-- Corollary 8.2 ranges over valid paper network/problem families and the
specific transient coefficient from (7.11). Because Lean cannot use `Fin n` as
a nonempty node type at `n = 0`, the sequence index `n` represents the
positive node count `n+1`. -/
def CorollaryFamilyRealizedByPaperInstances
    (neff L Delta sigma transient : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ inst : Setup (Fin (n + 1)) ℝ,
    neff n = inst.effectiveNodeCount ∧
      L n = inst.L ∧ Delta n = inst.Delta ∧ sigma n = inst.sigma ∧
        transient n = inst.theoremSevenOneTransientCoefficient

/-- Uniform boundedness of the problem/network family quantities named in
Corollary 8.2: `L`, `Delta`, `sigma`, and the transient coefficient from
(7.11). -/
def UniformlyBoundedCorollaryFamily
    (L Delta sigma transient : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    0 ≤ L n ∧ L n ≤ C ∧
      0 ≤ Delta n ∧ Delta n ≤ C ∧
        0 ≤ sigma n ∧ sigma n ≤ C ∧ |transient n| ≤ C

/-- Eventually positive stochastic-noise branch for the Corollary 8.2
leading-term comparison. The deterministic `σ = 0` case is modeled by
`DeterministicCorollaryBranch` instead of being forced into a stochastic
speedup ratio. -/
def EventuallyPositiveSigmaFamily (sigma : ℕ → ℝ) : Prop :=
  ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → 0 < sigma n

/-- The dominant stochastic term has centralized-SGD `n`-fold scaling along
the family and horizon regime. The `O(T^{-1})` transient from (7.11) is kept
out of this leading-term predicate; under `T/n -> infinity` and uniform
boundedness it is a lower-order theorem-side contribution, while the
`σ = 0` case belongs to the deterministic branch.

Book/PDF: `book/TimeVaryingPushPull/TimeVaryingPushPull.json` main theorem and
key lemma `TrueNfoldSpeedupCriterion`; `paper/TimeVaryingPushPull.pdf`,
Corollary 8.2 and equation (8.10). -/
def CentralizedSGDNFoldLeadingRoundComplexity
    (neff L Delta sigma : ℕ → ℝ) (T : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    sigma n * Real.sqrt (L n * Delta n / (neff n * (T n : ℝ))) ≤
      C * sigma n *
        Real.sqrt (L n * Delta n / (((n + 1 : ℕ) : ℝ) * (T n : ℝ)))

/-- Deterministic branch of Corollary 8.2: when `σ=0`, Theorem 7.1 has no
stochastic leading term and the paper records an `O(T^{-1})` rate instead of
an `n`-fold stochastic speedup comparison. -/
def DeterministicCorollaryBranch
    (sigma transient : ℕ → ℝ) (T : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, sigma n = 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      transient n / (T n : ℝ) ≤ C / (T n : ℝ)

theorem corollary_family_pointwise_positive_and_neff_bound
    {neff L Delta sigma transient : ℕ → ℝ}
    (hfamily :
      CorollaryFamilyRealizedByPaperInstances neff L Delta sigma transient)
    (n : ℕ) :
    0 < L n ∧ 0 < Delta n ∧ 0 < neff n ∧
      neff n ≤ ((n + 1 : ℕ) : ℝ) := by
  rcases hfamily n with ⟨inst, hneff, hL, hDelta, _hsigma, _htransient⟩
  rw [hneff, hL, hDelta]
  refine ⟨inst.L_pos, inst.Delta_positive,
    inst.effectiveNodeCount_pos_and_le_nodeCount.1, ?_⟩
  simpa [nodeCount] using inst.effectiveNodeCount_pos_and_le_nodeCount.2

theorem leading_sqrt_ratio_effective_node_forward
    {A e m tau s C : ℝ}
    (hA : 0 < A) (he : 0 < e) (hm : 0 < m) (htau : 0 < tau)
    (hs : 0 < s) (hC : 0 ≤ C)
    (hcompare :
      s * Real.sqrt (A / (e * tau)) ≤
        C * s * Real.sqrt (A / (m * tau))) :
    m ≤ C ^ 2 * e := by
  exact SOptLib.le_sq_mul_of_sqrt_div_le_mul_sqrt_div hA he hm htau
    ((mul_le_mul_iff_of_pos_left hs).mp (by convert hcompare using 1 <;> ring))

theorem leading_sqrt_ratio_effective_node_reverse
    {A e m tau s c : ℝ}
    (hA : 0 < A) (he : 0 < e) (hm : 0 < m) (htau : 0 < tau)
    (hs : 0 ≤ s) (hc : 0 < c) (hlower : c * m ≤ e) :
    s * Real.sqrt (A / (e * tau)) ≤
      Real.sqrt (c⁻¹) * s * Real.sqrt (A / (m * tau)) := by
  convert mul_le_mul_of_nonneg_left
    (SOptLib.sqrt_div_le_sqrt_inv_mul_sqrt_div_of_mul_le
      hA.le hm htau hc hlower) hs using 1 <;> ring

/-- Corollary 8.2: in the stochastic branch, true `n`-fold
round-complexity speedup occurs exactly when the effective node count scales
as `Theta(n)`. In the deterministic branch `σ=0`, Theorem 7.1 contributes the
separate `O(T^{-1})` rate rather than a stochastic speedup ratio. -/
theorem TrueNfoldSpeedupCriterion
    {neff Lfam Deltafam sigmafam transient : ℕ → ℝ} {T : ℕ → ℕ}
    (_hfamily :
      CorollaryFamilyRealizedByPaperInstances neff Lfam Deltafam sigmafam transient)
    (_hbounded : UniformlyBoundedCorollaryFamily Lfam Deltafam sigmafam transient)
    (_hT : TimeOverNodeDiverges T) :
    (EventuallyPositiveSigmaFamily sigmafam →
        (CentralizedSGDNFoldLeadingRoundComplexity neff Lfam Deltafam sigmafam T ↔
          EffectiveNodeCountThetaN neff)) ∧
      ((∀ n : ℕ, sigmafam n = 0) →
        DeterministicCorollaryBranch sigmafam transient T) := by
  rcases _hT 1 (by norm_num) with ⟨NT, hTlarge⟩
  have hTpos : ∀ n : ℕ, NT ≤ n → 0 < (T n : ℝ) := by
    intro n hn
    have hnT := hTlarge n hn
    have hnOne : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    norm_num at hnT
    exact lt_of_lt_of_le hnOne hnT
  constructor
  · intro hsigmaEventually
    rcases hsigmaEventually with ⟨Nsigma, hsigma⟩
    constructor
    · intro hcentral
      rcases hcentral with ⟨C, hC, NC, hcompare⟩
      let c : ℝ := (C ^ 2 + 1)⁻¹
      have hdenom : 0 < C ^ 2 + 1 := by positivity
      have hc : 0 < c := inv_pos.mpr hdenom
      have hcOne : c ≤ (1 : ℝ) := by
        dsimp [c]
        rw [inv_le_one₀ hdenom]
        nlinarith [sq_nonneg C]
      refine ⟨c, 1, max NC (max Nsigma NT), hc, hcOne, ?_⟩
      intro n hn
      have hnC : NC ≤ n := le_trans (le_max_left _ _) hn
      have hnRest : max Nsigma NT ≤ n := le_trans (le_max_right _ _) hn
      have hnSigma : Nsigma ≤ n := le_trans (le_max_left _ _) hnRest
      have hnT : NT ≤ n := le_trans (le_max_right _ _) hnRest
      rcases corollary_family_pointwise_positive_and_neff_bound _hfamily n with
        ⟨hL, hDelta, hneff, hneffUpper⟩
      have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hlinear : ((n + 1 : ℕ) : ℝ) ≤ C ^ 2 * neff n :=
        leading_sqrt_ratio_effective_node_forward
          (mul_pos hL hDelta) hneff hm (hTpos n hnT)
          (hsigma n hnSigma) hC (hcompare n hnC)
      have hlower : c * ((n + 1 : ℕ) : ℝ) ≤ neff n := by
        dsimp [c]
        rw [inv_mul_le_iff₀ hdenom]
        nlinarith [mul_pos hdenom hneff]
      exact ⟨hlower, by simpa using hneffUpper⟩
    · intro htheta
      rcases htheta with ⟨c, Ctheta, Ntheta, hc, _hcCtheta, htheta⟩
      refine ⟨Real.sqrt (c⁻¹), Real.sqrt_nonneg _,
        max Ntheta (max Nsigma NT), ?_⟩
      intro n hn
      have hnTheta : Ntheta ≤ n := le_trans (le_max_left _ _) hn
      have hnRest : max Nsigma NT ≤ n := le_trans (le_max_right _ _) hn
      have hnSigma : Nsigma ≤ n := le_trans (le_max_left _ _) hnRest
      have hnT : NT ≤ n := le_trans (le_max_right _ _) hnRest
      rcases corollary_family_pointwise_positive_and_neff_bound _hfamily n with
        ⟨hL, hDelta, hneff, _hneffUpper⟩
      have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      exact leading_sqrt_ratio_effective_node_reverse
        (mul_pos hL hDelta) hneff hm (hTpos n hnT)
        (hsigma n hnSigma).le hc (htheta n hnTheta).1
  · intro hsigmaZero
    rcases _hbounded with ⟨C, hC, hbounded⟩
    refine ⟨hsigmaZero, C, hC, NT, ?_⟩
    intro n hn
    have hnumerator : transient n ≤ C :=
      le_trans (le_abs_self (transient n)) (hbounded n).2.2.2.2.2.2
    exact (div_le_div_iff_of_pos_right (hTpos n hn)).2 hnumerator

/-- Horizon-dependent deterministic constant stepsize. In the stochastic branch
this is the clipped balancing value from (7.9); in the deterministic branch the
paper uses `α_max`. -/
noncomputable def horizonStepsize (T : ℕ) : ℝ :=
  SOptLib.cappedVarianceBalancedStepSize setup.alphaMax setup.Delta
    (setup.L * setup.influenceSecondMoment) setup.sigma (T : ℝ)

/-- Source-derived admissibility of the horizon-dependent stepsize. -/
theorem horizonStepsize_pos_le_alphaMax (T : ℕ) (hT : 1 ≤ T) :
    0 < setup.horizonStepsize T ∧ setup.horizonStepsize T ≤ setup.alphaMax := by
  exact SOptLib.cappedVarianceBalancedStepSize_pos_le_cap
    setup.alphaMax setup.Delta (setup.L * setup.influenceSecondMoment)
    setup.sigma (T : ℝ) setup.alphaMax_pos setup.Delta_positive
    (mul_pos setup.L_pos setup.influenceSecondMoment_pos)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT))

/- The scalar specialization of (7.8): the clipped balancing stepsize controls
the two leading terms, while the complete-block overshoot and the remaining
stepsize powers are absorbed by the printed transient coefficient (7.11). -/
set_option maxHeartbeats 800000 in
theorem horizon_stepsize_leading_and_transient_bounds
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (T : ℕ) (hT : 1 ≤ T)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ((T : ℝ)⁻¹) *
        (Finset.sum (Finset.range T) fun t =>
          (setup.withStepsize (setup.horizonStepsize T)).expectedGradientNormSq
            μ oracle t) ≤
      8 * setup.sigma *
          Real.sqrt (setup.L * setup.Delta /
            (setup.effectiveNodeCount * (T : ℝ))) +
        setup.theoremSevenOneTransientCoefficient / (T : ℝ) := by
  classical
  let alpha := setup.horizonStepsize T
  let K := (T - 1) / setup.period + 1
  let N := setup.completeBlockHorizon K
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  obtain ⟨halpha_pos, halpha_max⟩ := setup.horizonStepsize_pos_le_alphaMax T hT
  have hpre0 := setup.theoremSevenOne_preRate_bound
    μ oracle alpha T hT horacle (by simpa [alpha] using halpha_pos)
      (by simpa [alpha] using halpha_max)
  have hpre :
      ((T : ℝ)⁻¹) *
          (Finset.sum (Finset.range T) fun t =>
            (setup.withStepsize alpha).expectedGradientNormSq μ oracle t) ≤
        4 * setup.Delta /
            (alpha * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * (T : ℝ)) +
          (4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
              alpha * setup.sigma ^ 2 +
            (1 / (T : ℝ)) *
              ((4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
                  alpha * setup.sigma ^ 2 * ((N : ℝ) - (T : ℝ)) +
                2 * (setup.period : ℝ) * setup.theoremSevenOneJ *
                  setup.initialGradientHeterogeneity ^ 2 +
                2 * setup.theoremSevenOnePreRateA * alpha * setup.Delta /
                  setup.blockGain +
                setup.theoremSevenOnePreRateA * alpha ^ 2 *
                  setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
                setup.theoremSevenOnePreRateB * alpha ^ 2 *
                  setup.initialGradientHeterogeneity ^ 2 +
                2 * setup.theoremSevenOnePreRateA * setup.L *
                  setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
                    alpha ^ 3 * setup.sigma ^ 2 * K +
                setup.theoremSevenOnePreRateD * alpha ^ 2 *
                  setup.sigma ^ 2 * N) := by
    simpa [K, N] using hpre0
  have hfacts := setup.theoremSevenOne_completeBlockCeiling_facts T hT
  change T ≤ N ∧ K ≤ T ∧ N ≤ setup.period * T ∧
      N ≤ T + setup.period - 1 ∧ N - T ≤ setup.period - 1 at hfacts
  rcases hfacts with ⟨hTN, hKT, hNpT, _hNnear, hNTsub⟩
  have hKreal : (K : ℝ) ≤ (T : ℝ) := by exact_mod_cast hKT
  have hNreal : (N : ℝ) ≤ (setup.period : ℝ) * (T : ℝ) := by
    exact_mod_cast hNpT
  have hsubreal : (N : ℝ) - (T : ℝ) ≤ (setup.period : ℝ) - 1 := by
    have hcast : ((N - T : ℕ) : ℝ) ≤ ((setup.period - 1 : ℕ) : ℝ) := by
      exact_mod_cast hNTsub
    rw [Nat.cast_sub hTN, Nat.cast_sub setup.period_pos] at hcast
    norm_num at hcast
    linarith
  have hpminus : 0 ≤ (setup.period : ℝ) - 1 := by
    have hpone : (1 : ℝ) ≤ (setup.period : ℝ) := by
      exact_mod_cast setup.period_pos
    linarith
  have hD0 : 0 ≤ setup.finalDisplacementInitialConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨0, by decide⟩
  have hDg : 0 ≤ setup.finalDisplacementGradientConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨1, by decide⟩
  have hDsigma : 0 ≤ setup.finalDisplacementNoiseConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨2, by decide⟩
  have hJ : 0 ≤ setup.theoremSevenOneJ := by
    rw [setup.theoremSevenOneJ_eq]
    exact div_nonneg (mul_nonneg (by norm_num)
      setup.stateFeedbackInitialConstant_nonneg) (by positivity)
  have ha : 0 ≤ setup.theoremSevenOnePreRateA := by
    rw [setup.theoremSevenOnePreRateA_eq]
    positivity
  have hb : 0 ≤ setup.theoremSevenOnePreRateB := by
    rw [setup.theoremSevenOnePreRateB_eq]
    positivity
  have hd : 0 ≤ setup.theoremSevenOnePreRateD := by
    rw [setup.theoremSevenOnePreRateD_eq]
    positivity
  by_cases hsigma : setup.sigma = 0
  · have halpha_eq : alpha = setup.alphaMax := by
      simp [alpha, horizonStepsize, hsigma]
    have htransient :
        4 * setup.Delta / (setup.alphaMax * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) +
            (2 * (setup.period : ℝ) * setup.theoremSevenOneJ *
                setup.initialGradientHeterogeneity ^ 2 +
              2 * setup.theoremSevenOnePreRateA * setup.alphaMax * setup.Delta /
                setup.blockGain +
              setup.theoremSevenOnePreRateA * setup.alphaMax ^ 2 *
                setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
              setup.theoremSevenOnePreRateB * setup.alphaMax ^ 2 *
                setup.initialGradientHeterogeneity ^ 2) ≤
          setup.theoremSevenOneTransientCoefficient := by
      unfold theoremSevenOneTransientCoefficient
      rw [hsigma]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
      have hfirst :
          4 * setup.Delta / (setup.alphaMax * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) =
            4 * setup.Delta / ((Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.alphaMax) := by ring
      rw [hfirst]
      have hextra1 : 0 ≤ 2 * setup.theoremSevenOnePreRateA *
          setup.alphaMax * setup.Delta / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha)
            setup.alphaMax_pos.le) setup.Delta_positive.le)
          setup.influenceGain_pos.le
      have hextra2 : 0 ≤ setup.theoremSevenOnePreRateD *
          (setup.period : ℝ) * setup.Delta /
            (setup.L * setup.influenceSecondMoment) := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg hd (Nat.cast_nonneg _))
            setup.Delta_positive.le)
          (mul_pos setup.L_pos setup.influenceSecondMoment_pos).le
      linarith
    rw [halpha_eq, hsigma] at hpre
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul,
      add_zero] at hpre
    simp only [zero_add] at hpre
    have hscaled := mul_le_mul_of_nonneg_left htransient
      (inv_nonneg.mpr hTreal.le)
    have htail :
        4 * setup.Delta /
              (setup.alphaMax * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * (T : ℝ)) +
            (1 / (T : ℝ)) *
              (2 * (setup.period : ℝ) * setup.theoremSevenOneJ *
                  setup.initialGradientHeterogeneity ^ 2 +
                2 * setup.theoremSevenOnePreRateA * setup.alphaMax * setup.Delta /
                  setup.blockGain +
                setup.theoremSevenOnePreRateA * setup.alphaMax ^ 2 *
                  setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
                setup.theoremSevenOnePreRateB * setup.alphaMax ^ 2 *
                  setup.initialGradientHeterogeneity ^ 2) ≤
          setup.theoremSevenOneTransientCoefficient / (T : ℝ) := by
      convert hscaled using 1 <;>
        field_simp [ne_of_gt hTreal, ne_of_gt setup.alphaMax_pos,
          ne_of_gt setup.influenceGain_pos] <;> ring
    have hbound := hpre.trans htail
    rw [← halpha_eq] at hbound
    simpa [alpha, hsigma] using hbound
  · have hsigma_pos : 0 < setup.sigma :=
      lt_of_le_of_ne setup.sigma_nonneg_source (Ne.symm hsigma)
    have hsigma_sq : 0 < setup.sigma ^ 2 := sq_pos_of_pos hsigma_pos
    have halpha_eq :
        alpha = min setup.alphaMax
          (Real.sqrt (setup.Delta /
            (setup.L * setup.influenceSecondMoment * setup.sigma ^ 2 *
              (T : ℝ)))) := by
      simp [alpha, horizonStepsize, hsigma]
    obtain ⟨halpha_budget, hcube_budget, hN_budget⟩ :=
      clipped_sqrt_balancing_power_budgets
        (alpha := alpha) (cap := setup.alphaMax) (gap := setup.Delta)
        (varianceCoeff := setup.L * setup.influenceSecondMoment)
        (noise := setup.sigma) (T := (T : ℝ)) (K := (K : ℝ))
        (N := (N : ℝ)) (p := (setup.period : ℝ))
        setup.Delta_positive.le
        (mul_pos setup.L_pos setup.influenceSecondMoment_pos)
        (ne_of_gt hsigma_pos) hTreal halpha_pos.le halpha_max
        (by rw [halpha_eq]; exact min_le_right _ _)
        hKreal hNreal (Nat.cast_nonneg _)
    have hlead :
        4 * setup.Delta / (alpha * (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * (T : ℝ)) +
            (4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
              alpha * setup.sigma ^ 2 ≤
          8 * setup.sigma * Real.sqrt (setup.L * setup.Delta /
              (setup.effectiveNodeCount * (T : ℝ))) +
            (1 / (T : ℝ)) *
              (4 * setup.Delta /
                ((Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.alphaMax)) := by
      have halpha_balance :
          alpha = min setup.alphaMax
            (Real.sqrt
              ((setup.Delta / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) /
                ((setup.L * setup.influenceSecondMoment /
                    (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) * setup.sigma ^ 2 * (T : ℝ)))) := by
        rw [halpha_eq]
        congr 2
        field_simp [ne_of_gt setup.L_pos, ne_of_gt setup.influenceGain_pos,
          ne_of_gt setup.influenceSecondMoment_pos, ne_of_gt hsigma_sq,
          ne_of_gt hTreal]
      have hlead_base := inverse_linear_add_linear_at_clipped_sqrt_le
        (A := setup.Delta / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))))
        (B := setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))))
        (noise := setup.sigma) (T := (T : ℝ))
        (cap := setup.alphaMax) (alpha := alpha)
        (div_pos setup.Delta_positive setup.influenceGain_pos)
        (div_pos (mul_pos setup.L_pos setup.influenceSecondMoment_pos)
          setup.influenceGain_pos)
        hsigma_pos hTreal setup.alphaMax_pos halpha_balance
      have hlead_scaled := mul_le_mul_of_nonneg_left hlead_base
        (show (0 : ℝ) ≤ 4 by norm_num)
      have hroot_arg_eq :
          (setup.Delta / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
                (setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) /
              (T : ℝ) =
            setup.L * setup.Delta /
              (setup.effectiveNodeCount * (T : ℝ)) := by
        unfold effectiveNodeCount
        field_simp [ne_of_gt setup.influenceGain_pos,
          ne_of_gt setup.influenceSecondMoment_pos, ne_of_gt hTreal]
      rw [hroot_arg_eq] at hlead_scaled
      convert hlead_scaled using 1 <;>
        field_simp [ne_of_gt halpha_pos, ne_of_gt setup.alphaMax_pos,
          ne_of_gt setup.influenceGain_pos, ne_of_gt hTreal] <;> ring
    have hbracket :
        (4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
              alpha * setup.sigma ^ 2 * ((N : ℝ) - (T : ℝ)) +
            2 * (setup.period : ℝ) * setup.theoremSevenOneJ *
              setup.initialGradientHeterogeneity ^ 2 +
            2 * setup.theoremSevenOnePreRateA * alpha * setup.Delta /
              setup.blockGain +
            setup.theoremSevenOnePreRateA * alpha ^ 2 *
              setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 +
            setup.theoremSevenOnePreRateB * alpha ^ 2 *
              setup.initialGradientHeterogeneity ^ 2 +
            2 * setup.theoremSevenOnePreRateA * setup.L *
              setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
                alpha ^ 3 * setup.sigma ^ 2 * K +
            setup.theoremSevenOnePreRateD * alpha ^ 2 * setup.sigma ^ 2 * N ≤
          setup.theoremSevenOneTransientCoefficient -
            4 * setup.Delta / ((Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.alphaMax) := by
      unfold theoremSevenOneTransientCoefficient
      have hnoiseCoeff : 0 ≤ 4 * setup.L * setup.influenceSecondMoment /
          (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.sigma ^ 2 := by
        exact mul_nonneg
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) setup.L_pos.le)
            setup.influenceSecondMoment_pos.le) setup.influenceGain_pos.le)
          hsigma_sq.le
      have hovershootAlpha := mul_le_mul_of_nonneg_right halpha_max hnoiseCoeff
      have hovershootTime := mul_le_mul_of_nonneg_left hsubreal
        (mul_nonneg hnoiseCoeff (le_of_lt halpha_pos))
      have hovershoot :
          (4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1)))) *
                alpha * setup.sigma ^ 2 * ((N : ℝ) - (T : ℝ)) ≤
            4 * setup.L * setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
              setup.alphaMax * setup.sigma ^ 2 *
                ((setup.period : ℝ) - 1) := by
        calc
          _ ≤ (4 * setup.L * setup.influenceSecondMoment /
              (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.sigma ^ 2 * alpha) *
                ((setup.period : ℝ) - 1) := by
            convert hovershootTime using 1 <;> (try funext x) <;> ring
          _ ≤ (4 * setup.L * setup.influenceSecondMoment /
              (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) * setup.sigma ^ 2 * setup.alphaMax) *
                ((setup.period : ℝ) - 1) := by gcongr
          _ = _ := by ring
      have ha1coeff : 0 ≤ 2 * setup.theoremSevenOnePreRateA * setup.Delta /
          setup.blockGain := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) ha) setup.Delta_positive.le)
          setup.blockGain_pos.le
      have ha1 := mul_le_mul_of_nonneg_right halpha_max ha1coeff
      have ha2 : alpha ^ 2 ≤ setup.alphaMax ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self halpha_pos.le halpha_max
      have hhetero_sq : 0 ≤ setup.initialGradientHeterogeneity ^ 2 := sq_nonneg _
      have hAcoeff : 0 ≤ setup.theoremSevenOnePreRateA *
          setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 :=
        mul_nonneg (mul_nonneg ha hJ) hhetero_sq
      have hBcoeff : 0 ≤ setup.theoremSevenOnePreRateB *
          setup.initialGradientHeterogeneity ^ 2 := mul_nonneg hb hhetero_sq
      have hA2 := mul_le_mul_of_nonneg_left ha2 hAcoeff
      have hB2 := mul_le_mul_of_nonneg_left ha2 hBcoeff
      have hcubeCoeff : 0 ≤ 2 * setup.theoremSevenOnePreRateA * setup.L *
          setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) :=
        div_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ha)
              setup.L_pos.le) setup.influenceSecondMoment_pos.le)
          setup.influenceGain_pos.le
      have hcube := mul_le_mul_of_nonneg_left hcube_budget hcubeCoeff
      have hNterm := mul_le_mul_of_nonneg_left hN_budget hd
      have ha1' :
          2 * setup.theoremSevenOnePreRateA * alpha * setup.Delta /
                setup.blockGain ≤
            2 * setup.theoremSevenOnePreRateA * setup.alphaMax * setup.Delta /
                setup.blockGain := by
        convert ha1 using 1 <;> (try funext x) <;> ring
      have hA2' :
          setup.theoremSevenOnePreRateA * alpha ^ 2 * setup.theoremSevenOneJ *
                setup.initialGradientHeterogeneity ^ 2 ≤
            setup.theoremSevenOnePreRateA * setup.alphaMax ^ 2 *
              setup.theoremSevenOneJ * setup.initialGradientHeterogeneity ^ 2 := by
        convert hA2 using 1 <;> (try funext x) <;> ring
      have hB2' :
          setup.theoremSevenOnePreRateB * alpha ^ 2 *
                setup.initialGradientHeterogeneity ^ 2 ≤
            setup.theoremSevenOnePreRateB * setup.alphaMax ^ 2 *
              setup.initialGradientHeterogeneity ^ 2 := by
        convert hB2 using 1 <;> (try funext x) <;> ring
      have hcube' :
          2 * setup.theoremSevenOnePreRateA * setup.L *
                setup.influenceSecondMoment / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) *
                  alpha ^ 3 * setup.sigma ^ 2 * (K : ℝ) ≤
            2 * setup.theoremSevenOnePreRateA * setup.alphaMax *
              setup.Delta / (Finset.expect Finset.univ (fun r : Fin setup.period => rowSum (setup.influence r.1))) := by
        convert hcube using 1 <;>
          field_simp [ne_of_gt setup.L_pos,
            ne_of_gt setup.influenceSecondMoment_pos,
            ne_of_gt setup.influenceGain_pos] <;> ring
      have hNterm' :
          setup.theoremSevenOnePreRateD * alpha ^ 2 * setup.sigma ^ 2 *
                (N : ℝ) ≤
            setup.theoremSevenOnePreRateD * (setup.period : ℝ) *
              setup.Delta / (setup.L * setup.influenceSecondMoment) := by
        convert hNterm using 1 <;> (try funext x) <;> ring
      linarith [hovershoot, ha1', hA2', hB2', hcube', hNterm']
    have hscaled_bracket := mul_le_mul_of_nonneg_left hbracket
      (inv_nonneg.mpr hTreal.le)
    have hbound := hpre.trans (by
      have := add_le_add hlead hscaled_bracket
      convert this using 1 <;>
        field_simp [ne_of_gt hTreal, ne_of_gt setup.alphaMax_pos,
          ne_of_gt setup.influenceGain_pos] <;> ring)
    convert hbound using 1 <;>
      field_simp [alpha, ne_of_gt hTreal] <;> ring

section MainTheorem

variable {Ω : Type*} [MeasurableSpace Ω]
  [MeasurableSpace E] [BorelSpace E]

/-- The stationarity expectations used in Theorem 7.1 are well-defined for
the generated constant-stepsize run. This is the source-derived bridge that
keeps the paper theorem from relying on Lean's totalized integral fallback. -/
theorem TheoremSevenOneStationarityAverageWellDefined
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (alpha : ℝ) (T : ℕ) :
    (setup.withStepsize alpha).stationarityAverageWellDefined μ oracle T := by
  have horacle' :
      (setup.withStepsize alpha).StochasticOracleAssumptions μ oracle := by
    simpa [StochasticOracleAssumptions, withStepsize] using horacle
  exact (setup.withStepsize alpha).stationarityAverage_wellDefined μ oracle horacle' T

/-- The horizon-dependent stepsize specialization of the stationarity
well-definedness bridge used by Theorem 7.1. -/
theorem TheoremSevenOneStationarityAverageWellDefined_horizonStepsize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ T : ℕ, 1 ≤ T →
      (setup.withStepsize (setup.horizonStepsize T)).stationarityAverageWellDefined
        μ oracle T := by
  intro T _hT
  exact setup.TheoremSevenOneStationarityAverageWellDefined μ oracle horacle
    (setup.horizonStepsize T) T

/-- Theorem 7.1 with the paper's explicit horizon-dependent stepsize
`α_T` from (7.9). -/
theorem TheoremSevenOneUpperBound_horizonStepsize (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (_horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∃ KIN : ℝ, ∀ T : ℕ, 1 ≤ T →
      ((T : ℝ)⁻¹) *
          (Finset.sum (Finset.range T) fun t =>
            (setup.withStepsize (setup.horizonStepsize T)).expectedGradientNormSq μ oracle t)
        ≤ 8 * setup.sigma *
              Real.sqrt (setup.L * setup.Delta /
                (setup.effectiveNodeCount * (T : ℝ))) +
            KIN / (T : ℝ) := by
  refine ⟨setup.theoremSevenOneTransientCoefficient, ?_⟩
  intro T hT
  exact setup.horizon_stepsize_leading_and_transient_bounds
    μ oracle T hT _horacle

/-- Theorem 7.1 / (7.3): corrected sharp upper bound with effective node count. -/
theorem TheoremSevenOneUpperBound (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (_horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∃ KIN : ℝ, ∀ T : ℕ, 1 ≤ T →
      ∃ alphaT : ℝ,
        0 < alphaT ∧ alphaT ≤ setup.alphaMax ∧
          ((T : ℝ)⁻¹) *
              (Finset.sum (Finset.range T) fun t =>
                (setup.withStepsize alphaT).expectedGradientNormSq μ oracle t)
            ≤ 8 * setup.sigma *
                  Real.sqrt (setup.L * setup.Delta /
                    (setup.effectiveNodeCount * (T : ℝ))) +
                KIN / (T : ℝ) := by
  obtain ⟨KIN, hKIN⟩ :=
    setup.TheoremSevenOneUpperBound_horizonStepsize μ oracle _horacle
  refine ⟨KIN, ?_⟩
  intro T hT
  obtain ⟨halpha_pos, halpha_le⟩ := setup.horizonStepsize_pos_le_alphaMax T hT
  exact ⟨setup.horizonStepsize T, halpha_pos, halpha_le, hKIN T hT⟩

end MainTheorem

end Setup

end Algorithms.Unverified.TimeVaryingPushPull
