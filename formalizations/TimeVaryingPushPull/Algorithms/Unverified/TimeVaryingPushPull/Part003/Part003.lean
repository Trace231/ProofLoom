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
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope
import Algorithms.Unverified.TimeVaryingPushPull.Part002
import Algorithms.Unverified.TimeVaryingPushPull.Part003.Part002

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

/-- Deterministic scalar floor-block displacement split.

This is the source-local within-period motion edge for Appendix C.1 step 7:
unroll the scalar process from the exact floor representative
`(t / p) * p`, then separate the multiplier residue from the fresh propagated
noise term. -/
theorem quadraticScalarComparisonProcess_floor_block_displacement_sq_le
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    |quad.quadraticScalarComparisonProcess lambda alpha noise t -
        quad.quadraticScalarComparisonProcess lambda alpha noise
          ((t / quad.period) * quad.period)| ^ 2 ≤
      2 *
          |(quadraticScalarWithinPeriodMultiplier (Node := Node)
                quad lambda alpha (t % quad.period) - 1) *
              quad.quadraticScalarComparisonProcess lambda alpha noise
                ((t / quad.period) * quad.period)| ^ 2 +
        2 *
          |alpha *
              quadraticScalarWindowPropagatedNoise (Node := Node)
                quad lambda alpha noise ((t / quad.period) * quad.period)
                  (t % quad.period)| ^ 2 := by
  classical
  let base : ℕ := (t / quad.period) * quad.period
  let r : ℕ := t % quad.period
  let A : ℝ :=
    quadraticScalarWithinPeriodMultiplier (Node := Node) quad lambda alpha r
  let u0 : ℝ := quad.quadraticScalarComparisonProcess lambda alpha noise base
  let z : ℝ :=
    quadraticScalarWindowPropagatedNoise (Node := Node)
      quad lambda alpha noise base r
  have ht_eq : t = base + r := by
    simpa [base, r, Nat.mul_comm] using
      (Nat.div_add_mod t quad.period).symm
  have hprod :
      quadraticScalarWindowPhaseProduct (Node := Node)
          quad lambda alpha base r = A := by
    have hbase : base = quad.blockStart (t / quad.period) := by
      simp [base, blockStart]
    rw [hbase]
    exact quadraticScalarWindowPhaseProduct_blockStart_eq_withinPeriod
      (Node := Node) quad lambda alpha (t / quad.period) r
  have hunroll :=
    quadraticScalarComparisonProcess_unroll_window
      (Node := Node) quad lambda alpha noise base r
  have hsplit (a b : ℝ) :
      |a + b| ^ 2 ≤ 2 * |a| ^ 2 + 2 * |b| ^ 2 := by
    rw [sq_abs, sq_abs, sq_abs]
    nlinarith [sq_nonneg (a - b)]
  calc
    |quad.quadraticScalarComparisonProcess lambda alpha noise t -
        quad.quadraticScalarComparisonProcess lambda alpha noise
          ((t / quad.period) * quad.period)| ^ 2 =
        |(A - 1) * u0 + (-(alpha * z))| ^ 2 := by
          change
            |quad.quadraticScalarComparisonProcess lambda alpha noise t -
              quad.quadraticScalarComparisonProcess lambda alpha noise base| ^ 2 =
            |(A - 1) * u0 + (-(alpha * z))| ^ 2
          rw [ht_eq, hunroll, hprod]
          simp [A, u0, z]
          ring
    _ ≤
        2 * |(A - 1) * u0| ^ 2 +
          2 * |-(alpha * z)| ^ 2 :=
        hsplit ((A - 1) * u0) (-(alpha * z))
    _ =
        2 *
            |(quadraticScalarWithinPeriodMultiplier (Node := Node)
                  quad lambda alpha (t % quad.period) - 1) *
                quad.quadraticScalarComparisonProcess lambda alpha noise
                  ((t / quad.period) * quad.period)| ^ 2 +
          2 *
            |alpha *
                quadraticScalarWindowPropagatedNoise (Node := Node)
                  quad lambda alpha noise ((t / quad.period) * quad.period)
                    (t % quad.period)| ^ 2 := by
        simp [base, r, A, u0, z]

/-- Exact source-form residual for Appendix C.2 block innovations: `eta_k` is
`-alpha` times the propagated within-block noise sum. -/
theorem quadraticScalarBlockNoiseInnovation_eq_propagatedNoise
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha noise k =
      -alpha *
        quadraticScalarWindowPropagatedNoise (Node := Node)
          quad lambda alpha noise (quad.blockStart k) quad.period := by
  have hunroll :=
    quadraticScalarComparisonProcess_unroll_window
      (Node := Node) quad lambda alpha noise (quad.blockStart k) quad.period
  have hprod :=
    quadraticScalarWindowPhaseProduct_blockStart_period
      (Node := Node) quad lambda alpha k
  unfold quadraticScalarBlockNoiseInnovation
  rw [show (k + 1) * quad.period = quad.blockStart k + quad.period by
    simp [blockStart, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]]
  rw [hunroll, hprod]
  simp [blockStart]

/-- Exact block innovation as a finite propagated sum of within-period fresh
noise terms.  This is the Lean form of Appendix C.2 equation (C.2) before
applying martingale orthogonality and exact variance. -/
theorem quadraticScalarBlockNoiseInnovation_eq_finset_sum
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha noise k =
      -alpha *
        quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha noise (quad.blockStart k) quad.period := by
  rw [quadraticScalarBlockNoiseInnovation_eq_propagatedNoise]
  rw [quadraticScalarWindowPropagatedNoise_eq_finset]

/-- Coefficient-row form of the scalar block innovation, on the same
within-period noise basis used by the projected C.1 input. -/
theorem quadraticScalarBlockNoiseInnovation_eq_weightedCoeff_sum
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha noise k =
      (Finset.range quad.period).sum fun r =>
        weightedState (Node := Node) (E := ℝ)
          (fun j : Node =>
            -alpha *
              quadraticScalarWindowNoiseCoeff (Node := Node)
                quad lambda alpha (quad.blockStart k) quad.period r *
              quad.influence (quad.blockStart k + r) j)
          (noise (quad.blockStart k + r)) := by
  classical
  rw [quadraticScalarBlockNoiseInnovation_eq_finset_sum
    (Node := Node) quad lambda alpha noise k]
  unfold quadraticScalarWindowPropagatedNoiseFinset
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold weightedState
  simp [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- At `alpha = 0`, every phase multiplier and hence the period multiplier is
one.  This is the base point for the first-order expansion
`Gamma(alpha)=1-alpha*lambda*p*h+O(alpha^2)`. -/
theorem quadraticScalarPeriodMultiplier_zero
    (quad : Setup Node ℝ) (lambda : ℝ) :
    quadraticScalarPeriodMultiplier (Node := Node) quad lambda 0 = 1 := by
  simp [quadraticScalarPeriodMultiplier, quadraticScalarPhaseMultiplier]

/-- Each within-period multiplier is one at `alpha = 0`. -/
theorem quadraticScalarWithinPeriodMultiplier_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (r : ℕ) :
    quadraticScalarWithinPeriodMultiplier (Node := Node) quad lambda 0 r = 1 := by
  simp [quadraticScalarWithinPeriodMultiplier, quadraticScalarPhaseMultiplier]

/-- The within-period squared multiplier sum has the source value `p` at
`alpha = 0`.  This is the zeroth-order term used in the Appendix C.2 bias
summation. -/
theorem quadraticScalarWithinPeriodSquaredSum_zero
    (quad : Setup Node ℝ) (lambda : ℝ) :
    (∑ r : Fin quad.period,
      quadraticScalarWithinPeriodMultiplier (Node := Node) quad lambda 0 r.1 ^ 2) =
      (quad.period : ℝ) := by
  classical
  simp [quadraticScalarWithinPeriodMultiplier_zero]

/-- Each finite within-period multiplier is analytic at the expansion point. -/
theorem quadraticScalarWithinPeriodMultiplier_analyticAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (r : ℕ) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        quadraticScalarWithinPeriodMultiplier (Node := Node)
          quad lambda alpha r) 0 := by
  classical
  change AnalyticAt ℝ
    (fun alpha : ℝ =>
      ∏ j ∈ Finset.range r,
        quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha j) 0
  apply Finset.analyticAt_fun_prod
  intro j _hj
  unfold quadraticScalarPhaseMultiplier
  fun_prop

/-- The finite phase bias coefficient `sum_r A_r(alpha)^2` is analytic at
`alpha = 0`. -/
theorem quadraticScalarWithinPeriodSquaredSum_analyticAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        ∑ r : Fin quad.period,
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r.1 ^ 2) 0 := by
  classical
  apply Finset.analyticAt_fun_sum
  intro r _hr
  have hA :=
    quadraticScalarWithinPeriodMultiplier_analyticAt_zero
      (Node := Node) quad lambda r.1
  simpa [pow_two] using hA.mul hA

/-- Appendix C.2 finite-phase expansion
`sum_r A_r(alpha)^2 = p + O(alpha)`.  This is the deterministic bias-side
counterpart of the propagated-noise coefficient expansion. -/
theorem quadraticScalarWithinPeriodSquaredSum_isBigO_linear
    (quad : Setup Node ℝ) (lambda : ℝ) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        (∑ r : Fin quad.period,
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r.1 ^ 2) -
          (quad.period : ℝ))
      (fun alpha : ℝ => alpha) := by
  let phaseSum : ℝ → ℝ := fun alpha =>
    ∑ r : Fin quad.period,
      quadraticScalarWithinPeriodMultiplier (Node := Node)
        quad lambda alpha r.1 ^ 2
  have hanalytic : AnalyticAt ℝ phaseSum 0 :=
    quadraticScalarWithinPeriodSquaredSum_analyticAt_zero
      (Node := Node) quad lambda
  have hzero : phaseSum 0 = (quad.period : ℝ) :=
    quadraticScalarWithinPeriodSquaredSum_zero
      (Node := Node) quad lambda
  have hbig :
      (fun alpha : ℝ => phaseSum alpha - phaseSum 0)
        =O[nhds (0 : ℝ)] (fun alpha : ℝ => alpha - 0) :=
    hanalytic.differentiableAt.hasDerivAt.isBigO_sub
  refine hbig.congr ?_ ?_
  · intro alpha
    simp [phaseSum, hzero]
  · intro alpha
    simp

/-- Uniform finite-phase multiplier residue bound near zero.

This supplies the deterministic source premise needed by the scalar
floor-block aggregation: every within-period multiplier satisfies
`A_r(alpha) = 1 + O(alpha)` with one constant and one positive radius working
for all phases in the fixed period. -/
theorem quadraticScalarWithinPeriodMultiplier_residue_uniform_bound
    (quad : Setup Node ℝ) (lambda : ℝ) :
    ∃ alpha0 C : ℝ,
      0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ r : ℕ, r < quad.period →
            |quadraticScalarWithinPeriodMultiplier (Node := Node)
                quad lambda alpha r - 1| ≤ C * alpha := by
  obtain ⟨alpha0, C, halpha0, hC, hbound⟩ :=
    finite_family_abs_sub_le_mul_of_differentiableAt
      (f := fun ρ : Fin quad.period => fun alpha : ℝ =>
        quadraticScalarWithinPeriodMultiplier (Node := Node)
          quad lambda alpha ρ.1)
      (c := fun _ => 1)
      (fun ρ =>
        (quadraticScalarWithinPeriodMultiplier_analyticAt_zero
          (Node := Node) quad lambda ρ.1).differentiableAt)
      (fun ρ => quadraticScalarWithinPeriodMultiplier_zero
        (Node := Node) quad lambda ρ.1)
  exact ⟨alpha0, C, halpha0, hC, fun alpha halpha hle r hr =>
    hbound alpha halpha hle ⟨r, hr⟩⟩

/-- The period multiplier is analytic at the source expansion point. -/
theorem quadraticScalarPeriodMultiplier_analyticAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha) 0 := by
  classical
  change AnalyticAt ℝ
    (fun alpha : ℝ =>
      ∏ r ∈ (Finset.univ : Finset (Fin quad.period)),
        quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha r.1) 0
  apply Finset.analyticAt_fun_prod
  intro r _hr
  unfold quadraticScalarPhaseMultiplier
  fun_prop

/-- Appendix C.2 first derivative of
`Gamma(alpha)=prod_r (1-alpha*lambda*c_r)` at zero. -/
theorem quadraticScalarPeriodMultiplier_hasDerivAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) :
    HasDerivAt
      (fun alpha : ℝ =>
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
      (-(lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) 0 := by
  classical
  have hpReal : (quad.period : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt quad.period_pos)
  have hperiod_gain :
      (∑ r : Fin quad.period, quad.scalarComparisonGain r.1) =
        (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) := by
    simpa only [scalarComparisonGain, rowSum,
      Fintype.expect_eq_sum_div_card, Fintype.card_fin,
      div_eq_mul_inv, mul_comm, smul_eq_mul] using
      (smul_inv_smul₀ hpReal
        (∑ r : Fin quad.period, ∑ i : Node, quad.influence r.1 i)).symm
  simpa [quadraticScalarPeriodMultiplier, quadraticScalarPhaseMultiplier,
    ← Finset.mul_sum, hperiod_gain, mul_assoc] using
    (hasDerivAt_finset_prod_one_sub_mul_zero
      (Finset.univ : Finset (Fin quad.period))
      (fun r => lambda * quad.scalarComparisonGain r.1))

/-- Appendix C.2 first-order expansion
`Gamma(alpha)=1-alpha*lambda*p*h+O(alpha^2)`. -/
theorem quadraticScalarPeriodMultiplier_firstOrder_isBigO_sq
    (quad : Setup Node ℝ) (lambda : ℝ) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha -
          (1 - alpha * (lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
      (fun alpha : ℝ => alpha ^ 2) := by
  have h :=
    analyticAt_scalar_first_order_remainder_isBigO_sq
      (quadraticScalarPeriodMultiplier_analyticAt_zero
        (Node := Node) quad lambda)
      (quadraticScalarPeriodMultiplier_zero (Node := Node) quad lambda)
      (quadraticScalarPeriodMultiplier_hasDerivAt_zero
        (Node := Node) quad lambda)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using h

/-- The denominator `1-Gamma(alpha)^2` has derivative
`2*lambda*p*h` at zero. -/
theorem quadraticScalarPeriodDenominator_hasDerivAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) :
    HasDerivAt
      (fun alpha : ℝ =>
        1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2)
      (2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))) 0 := by
  simpa [mul_assoc] using
    hasDerivAt_one_sub_sq_at_zero_of_value_one
      (fun alpha : ℝ =>
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
      (lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
      (quadraticScalarPeriodMultiplier_hasDerivAt_zero
        (Node := Node) quad lambda)
      (quadraticScalarPeriodMultiplier_zero (Node := Node) quad lambda)

/-- Appendix C.2 denominator expansion
`1-Gamma(alpha)^2 = 2*alpha*lambda*p*h + O(alpha^2)`. -/
theorem quadraticScalarPeriodDenominator_firstOrder_isBigO_sq
    (quad : Setup Node ℝ) (lambda : ℝ) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        (1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2) -
          alpha * (2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))))
      (fun alpha : ℝ => alpha ^ 2) := by
  have hanalytic :
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2) 0 := by
    have hGamma :=
      quadraticScalarPeriodMultiplier_analyticAt_zero (Node := Node) quad lambda
    simpa [pow_two] using analyticAt_const.sub (hGamma.mul hGamma)
  have hzero :
      (fun alpha : ℝ =>
          1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2) 0 =
        0 := by
    simp [quadraticScalarPeriodMultiplier_zero]
  have h :=
    analyticAt_scalar_first_order_remainder_isBigO_sq
      hanalytic hzero
      (quadraticScalarPeriodDenominator_hasDerivAt_zero
        (Node := Node) quad lambda)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using h

/-- Positivity of the linear denominator coefficient under the homogeneous
quadratic source hypothesis. -/
theorem quadraticScalarPeriodDenominator_linearCoefficient_pos
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    0 < 2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) := by
  have hlambda : 0 < lambda := hquad.1
  have hperiod : 0 < (quad.period : ℝ) := by
    exact_mod_cast quad.period_pos
  exact mul_pos (mul_pos (mul_pos (by norm_num) hlambda) hperiod)
    quad.influenceGain_pos

/-- Small-stepsize two-sided linear control of the period denominator
`1-Gamma(alpha)^2`.  This is the denominator side of the Appendix C.2
geometric quotient estimate. -/
theorem quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∃ alpha0 dlow dup : ℝ,
      0 < alpha0 ∧ 0 < dlow ∧ 0 < dup ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          dlow * alpha ≤
              1 - quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ 2 ∧
            1 - quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ 2 ≤ dup * alpha := by
  exact two_sided_linear_bounds_near_zero_of_isBigO_sub_linear_sq
    (fun alpha : ℝ =>
      1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2)
    (2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
    (quadraticScalarPeriodDenominator_linearCoefficient_pos
      (Node := Node) quad lambda hquad)
    (quadraticScalarPeriodDenominator_firstOrder_isBigO_sq
      (Node := Node) quad lambda)

/-- Exact block-boundary AR identity in Appendix C.2.  The remaining source
work is to unfold `quadraticScalarBlockNoiseInnovation` into the finite
within-period noise sum and prove its second moment from
`ExactVarianceIidAdditiveNoise`. -/
theorem quadraticScalarBlockARRecursion
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    quad.quadraticScalarComparisonProcess lambda alpha noise ((k + 1) * quad.period) =
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha *
        quad.quadraticScalarComparisonProcess lambda alpha noise (k * quad.period) +
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha noise k := by
  unfold quadraticScalarBlockNoiseInnovation
  ring

/-- Second moment of the Appendix C.2 block innovation `eta_k`.  The source
next proves this is `alpha^2 * sigma^2 * p * q + O(alpha^3)` from iid exact
variance and finite within-period propagation. -/
noncomputable def quadraticScalarBlockInnovationSecondMoment
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) (k : ℕ) : ℝ :=
  ∫ ω,
    |quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ

/-- Block-boundary second moment `v_k = E|u_{kp}|^2` from Appendix C.2. -/
noncomputable def quadraticScalarBlockBoundarySecondMoment
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) (k : ℕ) : ℝ :=
  ∫ ω,
    |quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω)
      (k * quad.period)| ^ 2 ∂μ

/-- Recursive closed-form carrier for the block-boundary AR second moment.
This is the exact object produced by iterating
`v_{k+1}=Gamma(alpha)^2 v_k + E|eta_k|^2`. -/
noncomputable def quadraticScalarBlockBoundarySecondMomentARFormula
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) : ℕ → ℝ :=
  SOptLib.affineRecurrence (quad.x0 ^ 2)
    (quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2)
    (quadraticScalarBlockInnovationSecondMoment (Node := Node)
      quad lambda alpha μ oracle)

/-- Noise-only block-boundary variance from Appendix C.2.  The full
block-boundary second moment contains the deterministic squared bias
`x0^2 * Gamma(alpha)^(2k)`; subtracting it gives the variance component whose
initial value is zero and whose transient gap to steady state is only
`O(T^{-1})` after averaging. -/
noncomputable def quadraticScalarBlockBoundaryVariance
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) (k : ℕ) : ℝ :=
  quadraticScalarBlockBoundarySecondMoment (Node := Node)
      quad lambda alpha μ oracle k -
    quad.x0 ^ 2 *
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ (2 * k)

/-- Recursive closed-form carrier for the noise-only block-boundary variance.
This is the source recurrence `w_{k+1}=Gamma(alpha)^2 w_k+E|eta_k|^2` with
zero initial variance, separated from the deterministic bias part. -/
noncomputable def quadraticScalarBlockBoundaryVarianceARFormula
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 *
        quadraticScalarBlockBoundaryVarianceARFormula
          quad lambda alpha μ oracle k +
      quadraticScalarBlockInnovationSecondMoment (Node := Node)
        quad lambda alpha μ oracle k

/-- The block-boundary process starts from the deterministic scalar initial
condition, hence `v_0=x_0^2`. -/
theorem quadraticScalarBlockBoundarySecondMoment_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ) :
    quadraticScalarBlockBoundarySecondMoment (Node := Node)
        quad lambda alpha μ oracle 0 = quad.x0 ^ 2 := by
  unfold quadraticScalarBlockBoundarySecondMoment
  have hpoint :
      (fun ω : Ω =>
          |quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) (0 * quad.period)| ^ 2) =
        (fun _ : Ω => quad.x0 ^ 2) := by
    funext ω
    rw [Nat.zero_mul]
    rw [quadraticScalarComparisonProcess_zero
      (Node := Node) quad lambda alpha (oracle.noise ω)]
    exact sq_abs quad.x0
  rw [hpoint]
  simp

/-- The paper's variance component starts from zero after the deterministic
initial bias has been subtracted. -/
theorem quadraticScalarBlockBoundaryVariance_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ) :
    quadraticScalarBlockBoundaryVariance (Node := Node)
        quad lambda alpha μ oracle 0 = 0 := by
  unfold quadraticScalarBlockBoundaryVariance
  rw [quadraticScalarBlockBoundarySecondMoment_zero
    (Node := Node) quad lambda alpha μ oracle]
  ring

/-- The scalar weighted oracle noise has mean zero at every time. -/
theorem weightedNoise_integral_eq_zero
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (horacle : quad.StochasticOracleAssumptions μ oracle)
    (t : ℕ) (w : RowVector Node) :
    (∫ ω, weightedState (Node := Node) (E := ℝ) w
      (oracle.noise ω t) ∂μ) = 0 := by
  classical
  unfold weightedState
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i _hi
    rw [MeasureTheory.integral_smul]
    have hzero := quad.conditionalMeanZero_setIntegral_zero
      μ oracle horacle t i Set.univ MeasurableSet.univ
    simpa using congrArg (fun x : ℝ => w i • x) hzero
  · intro i _hi
    exact ((quad.nodeNoise_memLp_two μ oracle horacle t i).const_smul
      (w i)).integrable (by norm_num)

/-- Scalar products of two real L² processes are integrable. -/
theorem real_mul_integrable_of_memLp_two
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  have hprod : Integrable (fun ω => ‖f ω‖ * ‖g ω‖) μ := by
    simpa [Pi.mul_apply] using
      (MemLp.integrable_mul hf.norm hg.norm :
        Integrable ((fun ω => ‖f ω‖) * (fun ω => ‖g ω‖)) μ)
  exact hprod.mono'
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => by
      simp [norm_mul])

/-- The square of the absolute value of a real L² process is integrable. -/
theorem real_abs_sq_integrable_of_memLp_two
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun ω => |f ω| ^ 2) μ := by
  simpa [Real.norm_eq_abs] using
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf

/-- The scalar comparison process is square-integrable at every fixed time
under the source oracle L² assumptions. -/
theorem quadraticScalarComparisonProcess_memLp_two
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (horacle : quad.StochasticOracleAssumptions μ oracle) :
    ∀ t : ℕ,
      MemLp (fun ω : Ω =>
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) t) 2 μ := by
  exact memLp_two_of_affine_recurrence
    (fun t ω => quad.quadraticScalarComparisonProcess lambda alpha
      (oracle.noise ω) t)
    (fun t ω => weightedState (Node := Node) (E := ℝ) (quad.influence t)
      (oracle.noise ω t))
    (fun t => quadraticScalarPhaseMultiplier (Node := Node)
      quad lambda alpha t)
    (fun _ => -alpha)
    (by
      simpa only [quadraticScalarComparisonProcess_zero] using
        (memLp_const (quad.x0 : ℝ) : MemLp (fun _ : Ω => quad.x0) 2 μ))
    (fun t => quad.weightedNoise_memLp_two μ oracle horacle t (quad.influence t))
    (by
      intro t ω
      change quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) (t + 1) =
        quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha t •
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t +
          (-alpha) • weightedState (Node := Node) (E := ℝ) (quad.influence t)
            (oracle.noise ω t)
      rw [quadraticScalarComparisonProcess_succ
        (Node := Node) quad lambda alpha (oracle.noise ω) t]
      simp [sub_eq_add_neg])

/-- A scalar comparison state at time `t` is orthogonal to every weighted
oracle noise at a time `u ≥ t`.  This is the adapted-past/fresh-noise bridge
needed for the Appendix C.2 block martingale difference. -/
theorem quadraticScalarComparisonProcess_weightedNoise_cross_integral_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (horacle : quad.StochasticOracleAssumptions μ oracle)
    (w : RowVector Node) :
    ∀ {t u : ℕ}, t ≤ u →
      (∫ ω,
        quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) t *
          weightedState (Node := Node) (E := ℝ) w
            (oracle.noise ω u) ∂μ) = 0
  := by
    refine affine_recurrence_cross_integral_eq_zero_of_future_orthogonal μ
      (fun t ω => quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) t)
      (fun t ω => weightedState (Node := Node) (E := ℝ) (quad.influence t)
        (oracle.noise ω t))
      (fun u ω => weightedState (Node := Node) (E := ℝ) w
        (oracle.noise ω u))
      (fun t => quadraticScalarPhaseMultiplier (Node := Node)
        quad lambda alpha t) (fun _ => -alpha) ?_ ?_ ?_ ?_ ?_ ?_
    · exact quadraticScalarComparisonProcess_memLp_two
        quad lambda alpha μ oracle horacle
    · intro t
      exact quad.weightedNoise_memLp_two μ oracle horacle t (quad.influence t)
    · intro u
      exact quad.weightedNoise_memLp_two μ oracle horacle u w
    · intro t ω
      dsimp only
      rw [quadraticScalarComparisonProcess_succ
        (Node := Node) quad lambda alpha (oracle.noise ω) t]
      ring
    · intro u
      have hmean := weightedNoise_integral_eq_zero
        (Node := Node) quad μ oracle horacle u w
      calc
        (∫ ω,
          quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) 0 *
            weightedState (Node := Node) (E := ℝ) w
              (oracle.noise ω u) ∂μ) =
            ∫ ω, quad.x0 * weightedState (Node := Node) (E := ℝ) w
              (oracle.noise ω u) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [quadraticScalarComparisonProcess_zero
            (Node := Node) quad lambda alpha (oracle.noise ω)]
        _ = quad.x0 * (∫ ω, weightedState (Node := Node) (E := ℝ) w
              (oracle.noise ω u) ∂μ) := by
          rw [MeasureTheory.integral_const_mul]
        _ = 0 := by rw [hmean, mul_zero]
    · intro t u htu
      have hzero := quad.weightedNoise_crossTime_inner_integral_eq_zero
        μ oracle horacle (quad.influence t) w htu
      have hinner_eq :
          (fun ω : Ω =>
            ⟪weightedState (Node := Node) (E := ℝ) (quad.influence t)
                (oracle.noise ω t),
              weightedState (Node := Node) (E := ℝ) w
                (oracle.noise ω u)⟫_ℝ) =
            fun ω : Ω =>
              weightedState (Node := Node) (E := ℝ) (quad.influence t)
                  (oracle.noise ω t) *
                weightedState (Node := Node) (E := ℝ) w
                  (oracle.noise ω u) := by
        funext ω
        change RCLike.re
            (weightedState (Node := Node) (E := ℝ) w (oracle.noise ω u) *
              star (weightedState (Node := Node) (E := ℝ) (quad.influence t)
                (oracle.noise ω t))) = _
        simp [mul_comm]
      rw [← hinner_eq]
      exact hzero

/-- Same-head stochastic primitive for Appendix C.2 block assembly: the
period-boundary scalar state is generated by noises before block `k`, while
`eta_k` is the fresh within-block martingale difference.  This is the first
unavailable stochastic integral primitive after the block AR object has been
made canonical. -/
theorem quadraticScalarBlockBoundaryInnovation_cross_integral_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    (∫ ω,
      quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω)
          (k * quad.period) *
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) k ∂μ) = 0 := by
  classical
  let ublock : Ω → ℝ := fun ω =>
    quad.quadraticScalarComparisonProcess lambda alpha
      (oracle.noise ω) (k * quad.period)
  let term : ℕ → Ω → ℝ := fun r ω =>
    weightedState (Node := Node) (E := ℝ)
      (quad.influence (quad.blockStart k + r))
      (oracle.noise ω (quad.blockStart k + r))
  have hterm_int (r : ℕ) (_hr : r ∈ Finset.range quad.period) :
      Integrable (fun ω => ublock ω * term r ω) μ := by
    have hu : MemLp ublock 2 μ := by
      simpa [ublock] using
        quadraticScalarComparisonProcess_memLp_two
          (Node := Node) quad lambda alpha μ oracle hnoise.1
          (k * quad.period)
    have ht : MemLp (term r) 2 μ := by
      simpa [term] using
        quad.weightedNoise_memLp_two μ oracle hnoise.1
          (quad.blockStart k + r) (quad.influence (quad.blockStart k + r))
    exact real_mul_integrable_of_memLp_two hu ht
  have hterm_zero (r : ℕ) (hr : r ∈ Finset.range quad.period) :
      (∫ ω, ublock ω * term r ω ∂μ) = 0 := by
    have hle : k * quad.period ≤ quad.blockStart k + r := by
      simp [blockStart]
    simpa [ublock, term] using
      quadraticScalarComparisonProcess_weightedNoise_cross_integral_eq_zero
        (Node := Node) quad lambda alpha μ oracle hnoise.1
        (quad.influence (quad.blockStart k + r)) hle
  have hsum_zero :
      (∫ ω,
        (Finset.range quad.period).sum fun r =>
          (-alpha *
            quadraticScalarWindowNoiseCoeff (Node := Node)
              quad lambda alpha (quad.blockStart k) quad.period r) *
            (ublock ω * term r ω) ∂μ) = 0 := by
    exact integral_finset_sum_const_mul_eq_zero
      (Finset.range quad.period)
      (fun r =>
        -alpha *
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r)
      (fun r ω => ublock ω * term r ω)
      hterm_int hterm_zero
  calc
    (∫ ω,
      quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω)
          (k * quad.period) *
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) k ∂μ) =
        ∫ ω,
          (Finset.range quad.period).sum fun r =>
            (-alpha *
              quadraticScalarWindowNoiseCoeff (Node := Node)
                quad lambda alpha (quad.blockStart k) quad.period r) *
              (ublock ω * term r ω) ∂μ := by
      congr 1
      ext ω
      rw [quadraticScalarBlockNoiseInnovation_eq_finset_sum
        (Node := Node) quad lambda alpha (oracle.noise ω) k]
      simp [quadraticScalarWindowPropagatedNoiseFinset, ublock, term,
        Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = 0 := hsum_zero

/-- The period-boundary scalar state is orthogonal to any fresh propagated
within-block noise window.  This phase-local version is the cross-term
cancellation needed when expanding `u_{kp+r}` before summing over phases. -/
theorem quadraticScalarBlockBoundary_windowPropagatedNoiseFinset_cross_integral_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k r : ℕ) :
    (∫ ω,
      quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω)
          (k * quad.period) *
        quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) (quad.blockStart k) r ∂μ) = 0 := by
  classical
  let ublock : Ω → ℝ := fun ω =>
    quad.quadraticScalarComparisonProcess lambda alpha
      (oracle.noise ω) (k * quad.period)
  let term : ℕ → Ω → ℝ := fun s ω =>
    weightedState (Node := Node) (E := ℝ)
      (quad.influence (quad.blockStart k + s))
      (oracle.noise ω (quad.blockStart k + s))
  have hterm_int (s : ℕ) (_hs : s ∈ Finset.range r) :
      Integrable (fun ω => ublock ω * term s ω) μ := by
    have hu : MemLp ublock 2 μ := by
      simpa [ublock] using
        quadraticScalarComparisonProcess_memLp_two
          (Node := Node) quad lambda alpha μ oracle hnoise.1
          (k * quad.period)
    have ht : MemLp (term s) 2 μ := by
      simpa [term] using
        quad.weightedNoise_memLp_two μ oracle hnoise.1
          (quad.blockStart k + s) (quad.influence (quad.blockStart k + s))
    exact real_mul_integrable_of_memLp_two hu ht
  have hterm_zero (s : ℕ) (_hs : s ∈ Finset.range r) :
      (∫ ω, ublock ω * term s ω ∂μ) = 0 := by
    have hle : k * quad.period ≤ quad.blockStart k + s := by
      simp [blockStart]
    simpa [ublock, term] using
      quadraticScalarComparisonProcess_weightedNoise_cross_integral_eq_zero
        (Node := Node) quad lambda alpha μ oracle hnoise.1
        (quad.influence (quad.blockStart k + s)) hle
  have hsum_zero :
      (∫ ω,
        (Finset.range r).sum fun s =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) r s *
            (ublock ω * term s ω) ∂μ) = 0 := by
    exact integral_finset_sum_const_mul_eq_zero
      (Finset.range r)
      (fun s =>
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) r s)
      (fun s ω => ublock ω * term s ω)
      hterm_int hterm_zero
  calc
    (∫ ω,
      quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω)
          (k * quad.period) *
        quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) (quad.blockStart k) r ∂μ) =
        ∫ ω,
          (Finset.range r).sum fun s =>
            quadraticScalarWindowNoiseCoeff (Node := Node)
              quad lambda alpha (quad.blockStart k) r s *
              (ublock ω * term s ω) ∂μ := by
      congr 1
      ext ω
      simp [quadraticScalarWindowPropagatedNoiseFinset, ublock, term,
        Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = 0 := hsum_zero

/-- The propagated finite-window scalar noise is square-integrable under the
source oracle L² assumptions. -/
theorem quadraticScalarWindowPropagatedNoiseFinset_memLp_two
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (base n : ℕ) :
    MemLp (fun ω : Ω =>
      quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
        quad lambda alpha (oracle.noise ω) base n) 2 μ := by
  classical
  dsimp [quadraticScalarWindowPropagatedNoiseFinset]
  apply memLp_finset_sum
  intro r _hr
  exact (quad.weightedNoise_memLp_two μ oracle hnoise.1
    (base + r) (quad.influence (base + r))).const_smul
      (quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha base n r)

/-- Exact phase-local second-moment split after unrolling the scalar
comparison process within a block.  The cross term vanishes because the block
boundary state is adapted to the past and the propagated window only uses
fresh noises from the current block. -/
theorem quadraticScalarComparisonProcess_blockPhase_secondMoment_decomp
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k r : ℕ) :
    (∫ ω,
        |quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) (quad.blockStart k + r)| ^ 2 ∂μ) =
      quadraticScalarWindowPhaseProduct (Node := Node)
          quad lambda alpha (quad.blockStart k) r ^ 2 *
        quadraticScalarBlockBoundarySecondMoment (Node := Node)
          quad lambda alpha μ oracle k +
      alpha ^ 2 *
        (∫ ω,
          |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
            quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2 ∂μ) := by
  classical
  let A : ℝ :=
    quadraticScalarWindowPhaseProduct (Node := Node)
      quad lambda alpha (quad.blockStart k) r
  let u : Ω → ℝ := fun ω =>
    quad.quadraticScalarComparisonProcess lambda alpha
      (oracle.noise ω) (k * quad.period)
  let z : Ω → ℝ := fun ω =>
    quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
      quad lambda alpha (oracle.noise ω) (quad.blockStart k) r
  have hu_mem : MemLp u 2 μ := by
    simpa [u] using
      quadraticScalarComparisonProcess_memLp_two
        (Node := Node) quad lambda alpha μ oracle hnoise.1
        (k * quad.period)
  have hz_mem : MemLp z 2 μ := by
    simpa [z] using
      quadraticScalarWindowPropagatedNoiseFinset_memLp_two
        (Node := Node) quad lambda alpha μ oracle hnoise
        (quad.blockStart k) r
  have hu_sq_int : Integrable (fun ω => |u ω| ^ 2) μ :=
    real_abs_sq_integrable_of_memLp_two hu_mem
  have hz_sq_int : Integrable (fun ω => |z ω| ^ 2) μ :=
    real_abs_sq_integrable_of_memLp_two hz_mem
  have hcross_int : Integrable (fun ω => u ω * z ω) μ :=
    real_mul_integrable_of_memLp_two hu_mem hz_mem
  have hcross_zero :
      (∫ ω, u ω * z ω ∂μ) = 0 := by
    simpa [u, z, blockStart] using
      quadraticScalarBlockBoundary_windowPropagatedNoiseFinset_cross_integral_eq_zero
        (Node := Node) quad lambda alpha μ oracle hnoise k r
  have hinner_point :
      (fun ω => ⟪u ω, z ω⟫_ℝ) = fun ω => u ω * z ω := by
    funext ω
    change z ω * u ω = u ω * z ω
    ring
  have hcross_inner_int : Integrable (fun ω => ⟪u ω, z ω⟫_ℝ) μ := by
    rw [hinner_point]
    exact hcross_int
  have hcross_inner_zero : (∫ ω, ⟪u ω, z ω⟫_ℝ ∂μ) = 0 := by
    rw [hinner_point]
    exact hcross_zero
  calc
    (∫ ω,
        |quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) (quad.blockStart k + r)| ^ 2 ∂μ) =
        ∫ ω, |A * u ω - alpha * z ω| ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change |quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) (quad.blockStart k + r)| ^ 2 =
          |A * u ω - alpha * z ω| ^ 2
        rw [quadraticScalarComparisonProcess_unroll_window
          (Node := Node) quad lambda alpha (oracle.noise ω)
          (quad.blockStart k) r]
        rw [quadraticScalarWindowPropagatedNoise_eq_finset]
        simp [A, u, z, blockStart]
    _ =
        A ^ 2 * (∫ ω, |u ω| ^ 2 ∂μ) +
          alpha ^ 2 * (∫ ω, |z ω| ^ 2 ∂μ) := by
      simpa [smul_eq_mul, Real.norm_eq_abs] using
        (integral_norm_sq_smul_add_smul_eq_of_integral_inner_eq_zero
          μ u z A (-alpha) hu_sq_int hz_sq_int
          hcross_inner_int hcross_inner_zero)
    _ =
      quadraticScalarWindowPhaseProduct (Node := Node)
          quad lambda alpha (quad.blockStart k) r ^ 2 *
        quadraticScalarBlockBoundarySecondMoment (Node := Node)
          quad lambda alpha μ oracle k +
      alpha ^ 2 *
        (∫ ω,
          |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
            quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2 ∂μ) := by
      simp [A, u, z, quadraticScalarBlockBoundarySecondMoment, blockStart]

/-- The finite within-block innovation is square-integrable under the source
oracle L² assumptions. -/
theorem quadraticScalarBlockNoiseInnovation_memLp_two
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    MemLp (fun ω : Ω =>
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha (oracle.noise ω) k) 2 μ := by
  classical
  let propagated : Ω → ℝ := fun ω =>
    quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
      quad lambda alpha (oracle.noise ω) (quad.blockStart k) quad.period
  have hpropagated : MemLp propagated 2 μ := by
    dsimp [propagated, quadraticScalarWindowPropagatedNoiseFinset]
    apply memLp_finset_sum
    intro r _hr
    exact (quad.weightedNoise_memLp_two μ oracle hnoise.1
      (quad.blockStart k + r) (quad.influence (quad.blockStart k + r))).const_smul
        (quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) quad.period r)
  have hraw : MemLp (fun ω : Ω => -alpha * propagated ω) 2 μ :=
    hpropagated.const_smul (-alpha)
  refine MemLp.ae_eq ?_ hraw
  exact Filter.Eventually.of_forall fun ω => by
    change -alpha * propagated ω =
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha (oracle.noise ω) k
    rw [quadraticScalarBlockNoiseInnovation_eq_finset_sum
      (Node := Node) quad lambda alpha (oracle.noise ω) k]

/-- The scalar block innovation is mean-zero.

This is the expectation-level martingale input used by Appendix C.3 before
turning the deterministic slow multiplier into a lower bound. -/
theorem quadraticScalarBlockNoiseInnovation_integral_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    (∫ ω,
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha (oracle.noise ω) k ∂μ) = 0 := by
  classical
  let coeff : ℕ → RowVector Node := fun r j =>
    -alpha *
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart k) quad.period r *
      quad.influence (quad.blockStart k + r) j
  have hpoint :
      (fun ω : Ω =>
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) k) =
        fun ω : Ω =>
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ)
              (coeff r) (oracle.noise ω (quad.blockStart k + r)) := by
    funext ω
    simpa [coeff] using
      quadraticScalarBlockNoiseInnovation_eq_weightedCoeff_sum
        (Node := Node) quad lambda alpha (oracle.noise ω) k
  have hterm_int :
      ∀ r ∈ Finset.range quad.period,
        Integrable
          (fun ω : Ω =>
            weightedState (Node := Node) (E := ℝ)
              (coeff r) (oracle.noise ω (quad.blockStart k + r))) μ := by
    intro r _hr
    exact
      (quad.weightedNoise_memLp_two μ oracle hnoise.1
        (quad.blockStart k + r) (coeff r)).integrable (by norm_num)
  calc
    (∫ ω,
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha (oracle.noise ω) k ∂μ) =
        ∫ ω,
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ)
              (coeff r) (oracle.noise ω (quad.blockStart k + r)) ∂μ := by
          rw [hpoint]
    _ =
        (Finset.range quad.period).sum fun r =>
          ∫ ω,
            weightedState (Node := Node) (E := ℝ)
              (coeff r) (oracle.noise ω (quad.blockStart k + r)) ∂μ := by
          rw [MeasureTheory.integral_finset_sum]
          exact hterm_int
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro r _hr
          exact
            weightedNoise_integral_eq_zero
              (Node := Node) quad μ oracle hnoise.1
              (quad.blockStart k + r) (coeff r)

/-- The scalar comparison process has deterministic block-boundary mean
`x0 * Gamma(alpha)^k`.

This is the source C.3 slow-bias supplier obtained from the exact scalar AR
recursion and the mean-zero block innovations. -/
theorem quadraticScalarComparisonProcess_block_boundary_integral_eq_x0_mul_gamma_pow
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ k : ℕ,
      (∫ ω,
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) (k * quad.period) ∂μ) =
        quad.x0 *
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ k := by
  exact integral_affine_recurrence_eq_initial_mul_pow_of_innovation_zero μ
    (fun k ω => quad.quadraticScalarComparisonProcess lambda alpha
      (oracle.noise ω) (k * quad.period))
    (fun k ω => quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha (oracle.noise ω) k)
    quad.x0 (quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
    (fun k => (quadraticScalarComparisonProcess_memLp_two
      (Node := Node) quad lambda alpha μ oracle hnoise.1
      (k * quad.period)).integrable (by norm_num))
    (fun k => (quadraticScalarBlockNoiseInnovation_memLp_two
      (Node := Node) quad lambda alpha μ oracle hnoise k).integrable (by norm_num))
    (fun ω => by simpa using
      (quadraticScalarComparisonProcess_zero
        (Node := Node) quad lambda alpha (oracle.noise ω)))
    (fun k ω => by simpa using
      (quadraticScalarBlockARRecursion
        (Node := Node) quad lambda alpha (oracle.noise ω) k))
    (fun k => quadraticScalarBlockNoiseInnovation_integral_eq_zero
      (Node := Node) quad lambda alpha μ oracle hnoise k)

/-- Block-boundary second-moment recursion from the AR identity and the
fresh-block orthogonality primitive. -/
theorem quadraticScalarBlockBoundarySecondMoment_recursion
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ k : ℕ,
      quadraticScalarBlockBoundarySecondMoment (Node := Node)
          quad lambda alpha μ oracle (k + 1) =
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 *
          quadraticScalarBlockBoundarySecondMoment (Node := Node)
            quad lambda alpha μ oracle k +
        quadraticScalarBlockInnovationSecondMoment (Node := Node)
          quad lambda alpha μ oracle k := by
  classical
  let X : ℕ → Ω → ℝ := fun k ω =>
    quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω)
      (k * quad.period)
  let innovation : ℕ → Ω → ℝ := fun k ω =>
    quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha (oracle.noise ω) k
  simpa [X, innovation, Real.norm_eq_abs,
    quadraticScalarBlockBoundarySecondMoment,
    quadraticScalarBlockInnovationSecondMoment, smul_eq_mul] using
    (second_moment_affine_recurrence_eq_of_cross_zero μ X innovation
      (quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
      (fun k => by
        simpa [X] using
          quadraticScalarComparisonProcess_memLp_two
            quad lambda alpha μ oracle hnoise.1 (k * quad.period))
      (fun k => by
        simpa [innovation] using
          quadraticScalarBlockNoiseInnovation_memLp_two
            (Node := Node) quad lambda alpha μ oracle hnoise k)
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa [X, innovation, smul_eq_mul] using
          quadraticScalarBlockARRecursion
            (Node := Node) quad lambda alpha (oracle.noise ω) k)
      (fun k => by
        simpa [X, innovation, real_inner_comm] using
          quadraticScalarBlockBoundaryInnovation_cross_integral_eq_zero
            (Node := Node) quad lambda alpha μ oracle hnoise k))

/-- The canonical noise-only block-boundary variance satisfies the zero-initial
AR recursion used in Appendix C.2 after the deterministic bias term is
removed. -/
theorem quadraticScalarBlockBoundaryVariance_recursion
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ k : ℕ,
      quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle (k + 1) =
        quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 *
          quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle k +
        quadraticScalarBlockInnovationSecondMoment (Node := Node)
          quad lambda alpha μ oracle k := by
  simpa only [quadraticScalarBlockBoundaryVariance, pow_mul] using
    (sub_geometric_bias_satisfies_affine_recurrence
      (v := quadraticScalarBlockBoundarySecondMoment (Node := Node)
        quad lambda alpha μ oracle)
      (b := quadraticScalarBlockInnovationSecondMoment (Node := Node)
        quad lambda alpha μ oracle)
      (q := quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2)
      (c := quad.x0 ^ 2)
      (quadraticScalarBlockBoundarySecondMoment_recursion
        (Node := Node) quad lambda alpha μ oracle hnoise))

/-- Iterating the exact block-boundary second-moment recurrence gives the
recursive AR formula used before the geometric steady-state comparison. -/
theorem quadraticScalarBlockBoundarySecondMoment_closed_form
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hrec :
      ∀ k : ℕ,
        quadraticScalarBlockBoundarySecondMoment (Node := Node)
            quad lambda alpha μ oracle (k + 1) =
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 *
            quadraticScalarBlockBoundarySecondMoment (Node := Node)
              quad lambda alpha μ oracle k +
          quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k) :
    ∀ K : ℕ,
      quadraticScalarBlockBoundarySecondMoment (Node := Node)
          quad lambda alpha μ oracle K =
        quadraticScalarBlockBoundarySecondMomentARFormula (Node := Node)
          quad lambda alpha μ oracle K := fun K =>
  congrFun (SOptLib.eq_affineRecurrence_of_zero_of_succ
    (quadraticScalarBlockBoundarySecondMoment (Node := Node)
      quad lambda alpha μ oracle)
    (quad.x0 ^ 2)
    (quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2)
    (quadraticScalarBlockInnovationSecondMoment (Node := Node)
      quad lambda alpha μ oracle)
    (quadraticScalarBlockBoundarySecondMoment_zero
      (Node := Node) quad lambda alpha μ oracle)
    hrec) K

/-- Iterating the noise-only block-boundary variance recurrence gives the
zero-initial AR formula.  This is the exact Appendix C.2 variance carrier that
should be used for the transient estimate, rather than the full second moment
that still contains deterministic bias. -/
theorem quadraticScalarBlockBoundaryVariance_closed_form
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hrec :
      ∀ k : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle (k + 1) =
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2 *
            quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k +
          quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k) :
    ∀ K : ℕ,
      quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle K =
        quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
          quad lambda alpha μ oracle K := by
  intro K
  induction K with
  | zero =>
      exact quadraticScalarBlockBoundaryVariance_zero
        (Node := Node) quad lambda alpha μ oracle
  | succ K ih =>
      rw [hrec K, ih]
      rfl

/-- Exact iid diagonal moment for a deterministic weighted scalar noise row.
This strengthens the general source oracle upper bound in Part001 by using the
exact variance clause of `ExactVarianceIidAdditiveNoise`. -/
theorem sameTime_weightedNoise_secondMoment_eq_exact
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (t : ℕ)
    (w : RowVector Node) :
    (∫ ω, |weightedState (Node := Node) (E := ℝ) w
        (oracle.noise ω t)| ^ 2 ∂μ) =
      rowNormSq (Node := Node) w * quad.sigma ^ 2 := by
  classical
  simpa [weightedState, rowNormSq, Real.norm_eq_abs, Finset.sum_mul] using
    (integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero
      (Omega := Ω) (E := ℝ) (I := Node) μ Finset.univ w
      (fun i ω => oracle.noise ω t i) (fun _ => quad.sigma ^ 2)
      (fun i _hi =>
        (quad.nodeNoise_memLp_two μ oracle hnoise.1 t i).aestronglyMeasurable)
      (fun i _hi =>
        SOptLib.exactVarianceIidCenteredFamily.integrable_sq_norm hnoise.2 t i)
      (fun i _hi j _hj hij =>
        quad.sameTime_distinctNode_inner_integral_eq_zero
          μ oracle hnoise.1 t i j hij)
      (fun i _hi => hnoise.2.2.2.2.2 t i))

/-- Exact covariance diagonalization for the propagated finite within-block
scalar noise sum.  This is the stochastic core of Appendix C.2 equation (C.2);
the remaining asymptotic step is deterministic control of the propagation
coefficients, each of which is `1 + O(alpha)`. -/
theorem quadraticScalarWindowPropagatedNoiseFinset_secondMoment_exact
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (base n : ℕ) :
    (∫ ω,
        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) base n| ^ 2 ∂μ) =
      (Finset.range n).sum fun r =>
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha base n r ^ 2 *
          rowNormSq (Node := Node) (quad.influence (base + r)) *
          quad.sigma ^ 2 := by
  classical
  let term : ℕ → Ω → ℝ := fun r ω =>
    quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha base n r •
      weightedState (Node := Node) (E := ℝ)
        (quad.influence (base + r)) (oracle.noise ω (base + r))
  have horacle : quad.StochasticOracleAssumptions μ oracle := hnoise.1
  have hmem (r : ℕ) : MemLp (term r) 2 μ := by
    exact (quad.weightedNoise_memLp_two μ oracle horacle (base + r)
      (quad.influence (base + r))).const_smul
        (quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha base n r)
  have hsq (r : ℕ) : Integrable (fun ω => ‖term r ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hmem r).aestronglyMeasurable).1 (hmem r)
  have hcross (r : ℕ) (_hr : r ∈ Finset.range n)
      (s : ℕ) (_hs : s ∈ Finset.range n) (hrs : r ≠ s) :
      (∫ ω, ⟪term r ω, term s ω⟫_ℝ ∂μ) = 0 := by
    refine integral_inner_eq_zero_of_ne_of_forward_cross_zero μ term r s ?_ hrs
    intro a b hab
    have hzero := quad.weightedNoise_crossTime_inner_integral_eq_zero
      μ oracle horacle (quad.influence (base + a)) (quad.influence (base + b))
      (Nat.add_lt_add_left hab base)
    simp only [term, real_inner_smul_left, real_inner_smul_right]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hzero, mul_zero, mul_zero]
  have hdiag := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    μ (Finset.range n) term
    (fun r _hr => (hmem r).aestronglyMeasurable)
    (fun r _hr => hsq r) hcross
  calc
    (∫ ω,
        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) base n| ^ 2 ∂μ) =
        ∫ ω, ‖(Finset.range n).sum (fun r => term r ω)‖ ^ 2 ∂μ := by
      simp [quadraticScalarWindowPropagatedNoiseFinset, term, Real.norm_eq_abs,
        mul_assoc]
    _ = (Finset.range n).sum (fun r => ∫ ω, ‖term r ω‖ ^ 2 ∂μ) := hdiag
    _ = (Finset.range n).sum fun r =>
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha base n r ^ 2 *
          rowNormSq (Node := Node) (quad.influence (base + r)) *
          quad.sigma ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _hr
      have hrow :=
        sameTime_weightedNoise_secondMoment_eq_exact
          (Node := Node) quad μ oracle hnoise (base + r) (quad.influence (base + r))
      calc
        (∫ ω, ‖term r ω‖ ^ 2 ∂μ) =
            ∫ ω,
              quadraticScalarWindowNoiseCoeff (Node := Node)
                  quad lambda alpha base n r ^ 2 *
                |weightedState (Node := Node) (E := ℝ)
                  (quad.influence (base + r)) (oracle.noise ω (base + r))| ^ 2 ∂μ := by
          congr 1
          ext ω
          simp [term, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc]
        _ =
            quadraticScalarWindowNoiseCoeff (Node := Node)
                quad lambda alpha base n r ^ 2 *
              (∫ ω,
                |weightedState (Node := Node) (E := ℝ)
                  (quad.influence (base + r)) (oracle.noise ω (base + r))| ^ 2 ∂μ) := by
          rw [MeasureTheory.integral_const_mul]
        _ =
            quadraticScalarWindowNoiseCoeff (Node := Node)
                quad lambda alpha base n r ^ 2 *
              rowNormSq (Node := Node) (quad.influence (base + r)) *
              quad.sigma ^ 2 := by
          rw [hrow]
          ring

/-- Exact second moment of the Appendix C.2 block innovation after unrolling
`eta_k` to the propagated within-period finite sum.  This consumes the iid
orthogonality and exact variance assumptions; the only remaining asymptotic
work is deterministic control of the finite propagation coefficients. -/
theorem quadraticScalarBlockInnovationSecondMoment_eq_alpha_sq_finset_sum
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    quadraticScalarBlockInnovationSecondMoment (Node := Node)
        quad lambda alpha μ oracle k =
      alpha ^ 2 *
        ((Finset.range quad.period).sum fun r =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r ^ 2 *
            rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
            quad.sigma ^ 2) := by
  classical
  unfold quadraticScalarBlockInnovationSecondMoment
  have hpoint :
      (fun ω : Ω =>
          |quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k| ^ 2) =
        (fun ω : Ω =>
          alpha ^ 2 *
            |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
              quad lambda alpha (oracle.noise ω) (quad.blockStart k)
              quad.period| ^ 2) := by
    funext ω
    rw [quadraticScalarBlockNoiseInnovation_eq_finset_sum
      (Node := Node) quad lambda alpha (oracle.noise ω) k]
    rw [abs_mul, abs_neg, mul_pow, sq_abs alpha]
  rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  rw [quadraticScalarWindowPropagatedNoiseFinset_secondMoment_exact
    (Node := Node) quad lambda alpha μ oracle hnoise (quad.blockStart k)
    quad.period]

/-- Each finite propagated-noise coefficient is a continuous scalar function
of the stepsize. -/
theorem quadraticScalarWindowNoiseCoeff_continuous
    (quad : Setup Node ℝ) (lambda : ℝ) (base : ℕ) :
    ∀ n r : ℕ,
      Continuous
        (fun alpha : ℝ =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha base n r)
  | 0, r => by
      simpa [quadraticScalarWindowNoiseCoeff] using
        (continuous_const :
          Continuous (fun _ : ℝ => (0 : ℝ)))
  | n + 1, r => by
      by_cases hrn : r = n
      · simpa [quadraticScalarWindowNoiseCoeff, hrn] using
          (continuous_const :
            Continuous (fun _ : ℝ => (1 : ℝ)))
      · have hprev :=
          quadraticScalarWindowNoiseCoeff_continuous
            quad lambda base n r
        have hphase :
            Continuous
              (fun alpha : ℝ =>
                quadraticScalarPhaseMultiplier (Node := Node)
                  quad lambda alpha (base + n)) := by
          unfold quadraticScalarPhaseMultiplier
          fun_prop
        simpa [quadraticScalarWindowNoiseCoeff, hrn] using hphase.mul hprev

/-- Inside the active finite window, every deterministic propagated-noise
coefficient is one at `alpha = 0`. -/
theorem quadraticScalarWindowNoiseCoeff_zero_of_lt
    (quad : Setup Node ℝ) (lambda : ℝ) (base : ℕ) :
    ∀ n r : ℕ, r < n →
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda 0 base n r = 1
  | 0, r, hr => by omega
  | n + 1, r, hr => by
      by_cases hrn : r = n
      · simp [quadraticScalarWindowNoiseCoeff, hrn]
      · have hr_lt_n : r < n := by omega
        have hprev :=
          quadraticScalarWindowNoiseCoeff_zero_of_lt
            quad lambda base n r hr_lt_n
        simp [quadraticScalarWindowNoiseCoeff, hrn, hprev,
          quadraticScalarPhaseMultiplier]

/-- The deterministic propagated-noise coefficient is analytic at the
Appendix C.2 expansion point. -/
theorem quadraticScalarWindowNoiseCoeff_analyticAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (base : ℕ) :
    ∀ n r : ℕ,
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha base n r) 0
  | 0, r => by
      simpa [quadraticScalarWindowNoiseCoeff] using
        (analyticAt_const :
          AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)
  | n + 1, r => by
      by_cases hrn : r = n
      · simpa [quadraticScalarWindowNoiseCoeff, hrn] using
          (analyticAt_const :
            AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) 0)
      · have hprev :=
          quadraticScalarWindowNoiseCoeff_analyticAt_zero
            quad lambda base n r
        have hphase :
            AnalyticAt ℝ
              (fun alpha : ℝ =>
                quadraticScalarPhaseMultiplier (Node := Node)
                  quad lambda alpha (base + n)) 0 := by
          unfold quadraticScalarPhaseMultiplier
          fun_prop
        simpa [quadraticScalarWindowNoiseCoeff, hrn] using hphase.mul hprev

/-- Propagated-noise coefficients are periodic in the window base.  This
upgrades the pointwise block-noise expansion to a uniform-in-block source
input for the complete-period moment assembly. -/
theorem quadraticScalarWindowNoiseCoeff_blockStart_add
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (k base n r : ℕ) :
    quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart k + base) n r =
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha base n r := by
  induction n with
  | zero =>
      simp [quadraticScalarWindowNoiseCoeff]
  | succ n ih =>
      by_cases hrn : r = n
      · simp [quadraticScalarWindowNoiseCoeff, hrn]
      · have hphase :=
          quadraticScalarPhaseMultiplier_blockStart_add
            (Node := Node) quad lambda alpha k (base + n)
        simp [quadraticScalarWindowNoiseCoeff, hrn, ih, hphase,
          Nat.add_assoc]

/-- The zero-stepsize finite coefficient-square variance sum is the paper's
`sigma^2 * p * q` quantity, with `q = influenceSecondMoment`. -/
theorem quadraticScalarWindowNoiseCoeffSqVarianceSum_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (k : ℕ) :
    ((Finset.range quad.period).sum fun r =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda 0 (quad.blockStart k) quad.period r ^ 2 *
        rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
        quad.sigma ^ 2) =
      quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment := by
  classical
  have hperiod_ne : (quad.period : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt quad.period_pos)
  calc
    ((Finset.range quad.period).sum fun r =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda 0 (quad.blockStart k) quad.period r ^ 2 *
        rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
        quad.sigma ^ 2) =
        (Finset.range quad.period).sum fun r =>
          rowNormSq (Node := Node) (quad.influence r) * quad.sigma ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < quad.period := Finset.mem_range.mp hr
      rw [quadraticScalarWindowNoiseCoeff_zero_of_lt
        (Node := Node) quad lambda (quad.blockStart k) quad.period r hrlt]
      rw [quad.influence_blockStart_add k r]
      ring
    _ =
        (∑ r : Fin quad.period,
          rowNormSq (Node := Node) (quad.influence r.1) * quad.sigma ^ 2) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun r : ℕ =>
          rowNormSq (Node := Node) (quad.influence r) * quad.sigma ^ 2)
        quad.period]
    _ =
        ((∑ r : Fin quad.period,
          rowNormSq (Node := Node) (quad.influence r.1)) * quad.sigma ^ 2) := by
      rw [Finset.sum_mul]
    _ = quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment := by
      unfold influenceSecondMoment
      field_simp [hperiod_ne]

/-- The deterministic finite coefficient-square variance sum is analytic at
`alpha = 0`. -/
theorem quadraticScalarWindowNoiseCoeffSqVarianceSum_analyticAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (k : ℕ) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        ((Finset.range quad.period).sum fun r =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r ^ 2 *
            rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
            quad.sigma ^ 2)) 0 := by
  classical
  apply Finset.analyticAt_fun_sum
  intro r _hr
  have hcoeff :=
    quadraticScalarWindowNoiseCoeff_analyticAt_zero
      (Node := Node) quad lambda (quad.blockStart k) quad.period r
  simpa [pow_two, mul_assoc] using
    ((hcoeff.mul hcoeff).mul analyticAt_const).mul analyticAt_const

/-- Deterministic coefficient expansion remaining after the stochastic block
innovation variance has been diagonalized.  This is the precise Appendix C.2
`finite phase propagators are 1 + O(alpha)` leaf: the finite coefficient
square sum in the exact block-variance identity differs from its alpha-zero
value `sigma^2 * p * q` by `O(alpha)`. -/
theorem quadraticScalarWindowNoiseCoeffSqVarianceSum_isBigO_linear
    (quad : Setup Node ℝ) (lambda : ℝ) (k : ℕ) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        ((Finset.range quad.period).sum fun r =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r ^ 2 *
            rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
            quad.sigma ^ 2) -
          quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment)
      (fun alpha : ℝ => alpha) := by
  let coeffSum : ℝ → ℝ := fun alpha =>
    ((Finset.range quad.period).sum fun r =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart k) quad.period r ^ 2 *
        rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
        quad.sigma ^ 2)
  have hanalytic : AnalyticAt ℝ coeffSum 0 :=
    quadraticScalarWindowNoiseCoeffSqVarianceSum_analyticAt_zero
      (Node := Node) quad lambda k
  have hzero :
      coeffSum 0 =
        quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment :=
    quadraticScalarWindowNoiseCoeffSqVarianceSum_zero
      (Node := Node) quad lambda k
  have hbig :
      (fun alpha : ℝ => coeffSum alpha - coeffSum 0)
        =O[nhds (0 : ℝ)] (fun alpha : ℝ => alpha - 0) :=
    hanalytic.differentiableAt.hasDerivAt.isBigO_sub
  refine hbig.congr ?_ ?_
  · intro alpha
    simp [coeffSum, hzero]
  · intro alpha
    simp

/-- The deterministic finite coefficient-square variance sum is identical
across blocks.  The only phase data in the expression are periodic at
`blockStart`, so the expansion constants can be chosen uniformly in `k`. -/
theorem quadraticScalarWindowNoiseCoeffSqVarianceSum_block_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (k : ℕ) :
    ((Finset.range quad.period).sum fun r =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart k) quad.period r ^ 2 *
        rowNormSq (Node := Node) (quad.influence (quad.blockStart k + r)) *
        quad.sigma ^ 2) =
    ((Finset.range quad.period).sum fun r =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart 0) quad.period r ^ 2 *
        rowNormSq (Node := Node) (quad.influence (quad.blockStart 0 + r)) *
        quad.sigma ^ 2) := by
  classical
  apply Finset.sum_congr rfl
  intro r _hr
  have hcoeff_k :
      quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) quad.period r =
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha 0 quad.period r := by
    simpa using
      quadraticScalarWindowNoiseCoeff_blockStart_add
        (Node := Node) quad lambda alpha k 0 quad.period r
  have hcoeff_0 :
      quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart 0) quad.period r =
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha 0 quad.period r := by
    simpa using
      quadraticScalarWindowNoiseCoeff_blockStart_add
        (Node := Node) quad lambda alpha 0 0 quad.period r
  rw [hcoeff_k, hcoeff_0, quad.influence_blockStart_add k r,
    quad.influence_blockStart_add 0 r]

/-- Phase-local propagated-noise second moments are block-periodic.  After
the iid diagonalization, both the deterministic coefficients and influence
rows depend only on the within-period phase. -/
theorem
    quadraticScalarWindowPropagatedNoiseFinset_secondMoment_blockStart_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k r : ℕ) :
    (∫ ω,
        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2 ∂μ) =
      (∫ ω,
        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) 0 r| ^ 2 ∂μ) := by
  classical
  rw [quadraticScalarWindowPropagatedNoiseFinset_secondMoment_exact
      (Node := Node) quad lambda alpha μ oracle hnoise
      (quad.blockStart k) r,
    quadraticScalarWindowPropagatedNoiseFinset_secondMoment_exact
      (Node := Node) quad lambda alpha μ oracle hnoise 0 r]
  apply Finset.sum_congr rfl
  intro s _hs
  have hcoeff :
      quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) r s =
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha 0 r s := by
    simpa using
      quadraticScalarWindowNoiseCoeff_blockStart_add
        (Node := Node) quad lambda alpha k 0 r s
  rw [hcoeff, quad.influence_blockStart_add k s]
  simp

/-- Uniform boundedness of all phase-local fresh propagated-noise second
moments on a fixed small stepsize interval.  This is the finite-phase
`O(alpha^2)` input before the outer `alpha^2` factor is restored in the
complete-period decomposition. -/
theorem
    quadraticScalarWindowPropagatedNoiseFinset_phase_secondMoment_uniform_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ alpha0 M : ℝ,
      0 < alpha0 ∧ 0 ≤ M ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ k r : ℕ, r < quad.period →
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ) ≤ M := by
  classical
  let phaseMoment : Fin quad.period → ℝ → ℝ := fun ρ alpha =>
    (Finset.range ρ.1).sum fun s =>
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha 0 ρ.1 s ^ 2 *
        rowNormSq (Node := Node) (quad.influence s) *
        quad.sigma ^ 2
  have hphase_bound :
      ∀ ρ : Fin quad.period, ∃ C : ℝ, 0 ≤ C ∧
        ∀ alpha : ℝ, alpha ∈ Set.Icc (0 : ℝ) 1 →
          ‖phaseMoment ρ alpha‖ ≤ C := by
    intro ρ
    refine exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (phaseMoment ρ) isCompact_Icc ?_
    have hcont : Continuous (phaseMoment ρ) := by
      dsimp [phaseMoment]
      apply continuous_finset_sum
      intro s _hs
      have hcoeff :=
        quadraticScalarWindowNoiseCoeff_continuous
          (Node := Node) quad lambda 0 ρ.1 s
      exact ((hcoeff.pow 2).mul continuous_const).mul continuous_const
    exact hcont.continuousOn
  choose C hC_nonneg hC_bound using hphase_bound
  let M : ℝ := ∑ ρ : Fin quad.period, C ρ
  refine ⟨1, M, zero_lt_one, ?_, ?_⟩
  · dsimp [M]
    exact Finset.sum_nonneg fun ρ _hρ => hC_nonneg ρ
  intro alpha halpha_pos halpha_le k r hr
  let ρ : Fin quad.period := ⟨r, hr⟩
  have halpha_mem : alpha ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt halpha_pos, halpha_le⟩
  have hmoment_eq :
      (∫ ω,
        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
          ∂μ) = phaseMoment ρ alpha := by
    calc
      (∫ ω,
        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
          ∂μ) =
          (∫ ω,
            |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
              quad lambda alpha (oracle.noise ω) 0 r| ^ 2 ∂μ) :=
        quadraticScalarWindowPropagatedNoiseFinset_secondMoment_blockStart_eq_zero
          (Node := Node) quad lambda alpha μ oracle hnoise k r
      _ = phaseMoment ρ alpha := by
        rw [quadraticScalarWindowPropagatedNoiseFinset_secondMoment_exact
          (Node := Node) quad lambda alpha μ oracle hnoise 0 r]
        simp [phaseMoment, ρ]
  have hphase_le_C : phaseMoment ρ alpha ≤ C ρ := by
    calc
      phaseMoment ρ alpha ≤ |phaseMoment ρ alpha| := le_abs_self _
      _ = ‖phaseMoment ρ alpha‖ := by simp [Real.norm_eq_abs]
      _ ≤ C ρ := hC_bound ρ alpha halpha_mem
  have hC_le_M : C ρ ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun ρ _hρ => hC_nonneg ρ) (Finset.mem_univ ρ)
  rw [hmoment_eq]
  exact le_trans hphase_le_C hC_le_M

/-- Scalar floor-block displacement average from its source component bounds.

This is the stochastic aggregation layer for Appendix C.1 step 7: the
deterministic floor-block split is integrated, the multiplier-residue part is
charged to the scalar block-boundary second moment, and the fresh within-block
noise part is charged to a uniform propagated-noise second-moment bound. -/
theorem
    quadraticScalarComparisonProcess_floor_block_average_l2_bound_of_components
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {alpha Cphase Cboundary Cfresh : ℝ}
    (halpha_pos : 0 < alpha)
    (hCphase_nonneg : 0 ≤ Cphase)
    (hCboundary_nonneg : 0 ≤ Cboundary)
    (hCfresh_nonneg : 0 ≤ Cfresh)
    (hphase :
      ∀ r : ℕ, r < quad.period →
        |quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r - 1| ≤ Cphase * alpha)
    (hboundary :
      ∀ k : ℕ,
        quadraticScalarBlockBoundarySecondMoment (Node := Node)
          quad lambda alpha μ oracle k ≤ Cboundary)
    (hfresh :
      ∀ k r : ℕ, r < quad.period →
        (∫ ω,
          |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
            quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
            ∂μ) ≤ Cfresh)
    {T : ℕ} (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) *
      Finset.sum (Finset.range T) (fun t =>
        ∫ ω,
          |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
      (2 * Cphase ^ 2 * Cboundary + 2 * Cfresh) * alpha ^ 2 := by
  classical
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hT_pos : 0 < (T : ℝ) := by
    by_contra hnot
    have hT_nonpos : (T : ℝ) ≤ 0 := le_of_not_gt hnot
    have hT_zero : (T : ℝ) = 0 :=
      le_antisymm hT_nonpos (Nat.cast_nonneg T)
    have hprod_zero : alpha * (T : ℝ) = 0 := by
      rw [hT_zero, mul_zero]
    nlinarith
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  let B : ℝ := 2 * Cphase ^ 2 * Cboundary + 2 * Cfresh
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg Cphase, hCboundary_nonneg, hCfresh_nonneg]
  have hterm :
      ∀ t : ℕ,
        (∫ ω,
          |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
        B * alpha ^ 2 := by
    intro t
    let k : ℕ := t / quad.period
    let r : ℕ := t % quad.period
    let base : ℕ := (t / quad.period) * quad.period
    let A : ℝ :=
      quadraticScalarWithinPeriodMultiplier (Node := Node)
        quad lambda alpha r
    let u : Ω → ℝ := fun ω =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) base
    let z : Ω → ℝ := fun ω =>
      quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
        quad lambda alpha (oracle.noise ω) base r
    have hr : r < quad.period := Nat.mod_lt t quad.period_pos
    have hbase_eq : base = quad.blockStart k := by
      simp [base, k, blockStart]
    have hleft_int :
        Integrable
          (fun ω : Ω =>
            |quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) t -
              quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) base| ^ 2) μ := by
      exact
        real_abs_sq_integrable_of_memLp_two
          ((quadraticScalarComparisonProcess_memLp_two
              (Node := Node) quad lambda alpha μ oracle hnoise.1 t).sub
            (quadraticScalarComparisonProcess_memLp_two
              (Node := Node) quad lambda alpha μ oracle hnoise.1 base))
    have hu_int :
        Integrable (fun ω : Ω => |u ω| ^ 2) μ := by
      dsimp [u, base]
      exact
        real_abs_sq_integrable_of_memLp_two
          (quadraticScalarComparisonProcess_memLp_two
            (Node := Node) quad lambda alpha μ oracle hnoise.1
            ((t / quad.period) * quad.period))
    have hz_int :
        Integrable (fun ω : Ω => |z ω| ^ 2) μ := by
      dsimp [z]
      exact
        real_abs_sq_integrable_of_memLp_two
          (quadraticScalarWindowPropagatedNoiseFinset_memLp_two
            (Node := Node) quad lambda alpha μ oracle hnoise base r)
    have hpoint :
        (fun ω : Ω =>
          |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) base| ^ 2) ≤
        fun ω : Ω =>
          (2 * (Cphase * alpha) ^ 2) * |u ω| ^ 2 +
            (2 * alpha ^ 2) * |z ω| ^ 2 := by
      intro ω
      have hsplit :=
        quadraticScalarComparisonProcess_floor_block_displacement_sq_le
          (Node := Node) quad lambda alpha (oracle.noise ω) t
      have hz_eq :
          quadraticScalarWindowPropagatedNoise (Node := Node)
              quad lambda alpha (oracle.noise ω) base r =
            z ω := by
        simpa [z] using
          quadraticScalarWindowPropagatedNoise_eq_finset
            (Node := Node) quad lambda alpha (oracle.noise ω) base r
      have hphase_sq :
          |(A - 1) * u ω| ^ 2 ≤
            (Cphase * alpha) ^ 2 * |u ω| ^ 2 := by
        have hphase_abs :
            |(|A - 1|)| ≤ |Cphase * alpha| := by
          have hrhs_nonneg : 0 ≤ Cphase * alpha :=
            mul_nonneg hCphase_nonneg halpha_nonneg
          simpa [A, abs_of_nonneg hrhs_nonneg] using hphase r hr
        rw [abs_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (sq_le_sq.mpr hphase_abs) (sq_nonneg |u ω|)
      have hz_sq :
          |alpha * z ω| ^ 2 = alpha ^ 2 * |z ω| ^ 2 := by
        rw [abs_mul, mul_pow, sq_abs]
      have hraw :
          |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) base| ^ 2 ≤
          2 * |(A - 1) * u ω| ^ 2 +
            2 * |alpha * z ω| ^ 2 := by
        simpa [base, r, A, u, hz_eq] using hsplit
      calc
        |quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) t -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) base| ^ 2 ≤
            2 * |(A - 1) * u ω| ^ 2 +
              2 * |alpha * z ω| ^ 2 := hraw
        _ ≤
            2 * ((Cphase * alpha) ^ 2 * |u ω| ^ 2) +
              2 * (alpha ^ 2 * |z ω| ^ 2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hphase_sq (by norm_num))
            (le_of_eq (by rw [hz_sq]))
        _ =
            (2 * (Cphase * alpha) ^ 2) * |u ω| ^ 2 +
              (2 * alpha ^ 2) * |z ω| ^ 2 := by ring
    have hupper :=
      integral_le_integral_affine_combination μ
        (fun ω : Ω =>
          |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) base| ^ 2)
        (fun ω : Ω => |u ω| ^ 2)
        (fun ω : Ω => |z ω| ^ 2)
        (2 * (Cphase * alpha) ^ 2) (2 * alpha ^ 2)
        hleft_int hu_int hz_int hpoint
    have hu_bound :
        (∫ ω, |u ω| ^ 2 ∂μ) ≤ Cboundary := by
      have hb := hboundary k
      simpa [u, base, hbase_eq, quadraticScalarBlockBoundarySecondMoment,
        blockStart] using hb
    have hz_bound :
        (∫ ω, |z ω| ^ 2 ∂μ) ≤ Cfresh := by
      simpa [z, hbase_eq] using hfresh k r hr
    calc
      (∫ ω,
          |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) base| ^ 2 ∂μ) ≤
          (2 * (Cphase * alpha) ^ 2) *
              (∫ ω, |u ω| ^ 2 ∂μ) +
            (2 * alpha ^ 2) * (∫ ω, |z ω| ^ 2 ∂μ) := by
        simpa using hupper
      _ ≤
          (2 * (Cphase * alpha) ^ 2) * Cboundary +
            (2 * alpha ^ 2) * Cfresh := by
        gcongr
      _ = B * alpha ^ 2 := by
        dsimp [B]
        ring
  calc
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            |quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) t -
              quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun _t => B * alpha ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun t _ht => by simpa using hterm t)
        (inv_nonneg.mpr hT_pos.le)
    _ = B * alpha ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hT_ne]

/-- Complete-period aggregation of the fresh within-block propagated-noise
second moments.  This is the finite-sum arithmetic that turns the phase-local
uniform bound into the source `O(alpha^2)` fresh-noise residue. -/
theorem
    quadraticScalarWindowPropagatedNoiseFinset_completePeriod_freshAverage_alpha_sq_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ alpha0 Cfresh : ℝ,
      0 < alpha0 ∧ 0 ≤ Cfresh ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            let freshAverage : ℝ :=
              lambda ^ 2 * (((K * quad.period : ℕ) : ℝ)⁻¹) *
                ((Finset.range K).sum fun k =>
                  (Finset.range quad.period).sum fun r =>
                    alpha ^ 2 *
                      (∫ ω,
                        |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                          quad lambda alpha (oracle.noise ω)
                          (quad.blockStart k) r| ^ 2 ∂μ))
            |freshAverage| ≤ Cfresh * alpha ^ 2 := by
  classical
  obtain ⟨alphaF, M, halphaF_pos, hM_nonneg, hfresh_phase⟩ :=
    quadraticScalarWindowPropagatedNoiseFinset_phase_secondMoment_uniform_bound
      (Node := Node) quad lambda μ oracle hnoise
  let Cfresh : ℝ := lambda ^ 2 * M
  have hCfresh_nonneg : 0 ≤ Cfresh := by
    dsimp [Cfresh]
    exact mul_nonneg (sq_nonneg lambda) hM_nonneg
  refine ⟨alphaF, Cfresh, halphaF_pos, hCfresh_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let freshAverage : ℝ :=
    lambda ^ 2 * (((K * quad.period : ℕ) : ℝ)⁻¹) *
      ((Finset.range K).sum fun k =>
        (Finset.range quad.period).sum fun r =>
          alpha ^ 2 *
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ))
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK_pos)
  have hperiod_pos : 0 < (quad.period : ℝ) := by
    exact_mod_cast quad.period_pos
  have hperiod_ne : (quad.period : ℝ) ≠ 0 := ne_of_gt hperiod_pos
  have hT_pos : 0 < ((K * quad.period : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hK_pos quad.period_pos
  have hscale_nonneg :
      0 ≤ lambda ^ 2 * (((K * quad.period : ℕ) : ℝ)⁻¹) := by
    exact mul_nonneg (sq_nonneg lambda) (inv_nonneg.mpr (le_of_lt hT_pos))
  have hterm_nonneg (k r : ℕ) :
      0 ≤ alpha ^ 2 *
        (∫ ω,
          |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
            quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
            ∂μ) := by
    exact mul_nonneg (sq_nonneg alpha)
      (MeasureTheory.integral_nonneg fun ω => sq_nonneg _)
  have hfresh_nonneg : 0 ≤ freshAverage := by
    dsimp [freshAverage]
    exact mul_nonneg hscale_nonneg
      (Finset.sum_nonneg fun k _hk =>
        Finset.sum_nonneg fun r _hr => hterm_nonneg k r)
  have hsum_bound :
      ((Finset.range K).sum fun k =>
        (Finset.range quad.period).sum fun r =>
          alpha ^ 2 *
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ)) ≤
        (K : ℝ) * (quad.period : ℝ) * (alpha ^ 2 * M) := by
    calc
      ((Finset.range K).sum fun k =>
        (Finset.range quad.period).sum fun r =>
          alpha ^ 2 *
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ)) ≤
          (Finset.range K).sum fun _k =>
            (Finset.range quad.period).sum fun _r => alpha ^ 2 * M := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro r hr
        have hrlt : r < quad.period := Finset.mem_range.mp hr
        exact mul_le_mul_of_nonneg_left
          (hfresh_phase alpha halpha_pos halpha_le k r hrlt)
          (sq_nonneg alpha)
      _ = (K : ℝ) * (quad.period : ℝ) * (alpha ^ 2 * M) := by
        simp [mul_assoc]
  have hfresh_le :
      freshAverage ≤ Cfresh * alpha ^ 2 := by
    dsimp [freshAverage]
    calc
      lambda ^ 2 * (((K * quad.period : ℕ) : ℝ)⁻¹) *
          ((Finset.range K).sum fun k =>
            (Finset.range quad.period).sum fun r =>
              alpha ^ 2 *
                (∫ ω,
                  |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                    quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                    ∂μ)) ≤
          lambda ^ 2 * (((K * quad.period : ℕ) : ℝ)⁻¹) *
            ((K : ℝ) * (quad.period : ℝ) * (alpha ^ 2 * M)) :=
        mul_le_mul_of_nonneg_left hsum_bound hscale_nonneg
      _ = Cfresh * alpha ^ 2 := by
        dsimp [Cfresh]
        rw [Nat.cast_mul]
        field_simp [hK_ne, hperiod_ne]
  change |freshAverage| ≤ Cfresh * alpha ^ 2
  rw [abs_of_nonneg hfresh_nonneg]
  exact hfresh_le

/-- Exact finite-block deterministic bias average from Appendix C.2 for
`T=Kp`.  It is separated from the variance terms so the proof can apply the
period-multiplier expansion to the geometric factor explicitly. -/
noncomputable def quadraticScalarBiasBlockAverage
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (K : ℕ) : ℝ :=
  (lambda ^ 2 * quad.x0 ^ 2 / ((K : ℝ) * (quad.period : ℝ))) *
    (∑ r : Fin quad.period,
      quadraticScalarWithinPeriodMultiplier (Node := Node)
        quad lambda alpha r.1 ^ 2) *
      ((1 - quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha ^ (2 * K)) /
        (1 - quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha ^ 2))

/-- Complete-period block/phase expansion of the scalar moment functional.
This is the exact finite reindexing and phase-local second-moment split before
the deterministic boundary-bias cancellation. -/
theorem quadraticScalarMomentFunctional_completePeriod_phase_secondMoment_sum
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (K : ℕ) :
    quad.quadraticScalarMomentFunctional lambda alpha μ oracle
        (K * quad.period) =
      (((K * quad.period : ℕ) : ℝ)⁻¹) *
        ((Finset.range K).sum fun k =>
          (Finset.range quad.period).sum fun r =>
            lambda ^ 2 *
              (quadraticScalarWithinPeriodMultiplier (Node := Node)
                  quad lambda alpha r ^ 2 *
                quadraticScalarBlockBoundarySecondMoment (Node := Node)
                  quad lambda alpha μ oracle k +
              alpha ^ 2 *
                (∫ ω,
                  |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                    quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                    ∂μ))) := by
  classical
  unfold quadraticScalarMomentFunctional
  rw [sum_range_mul_eq_sum_blocks]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro r _hr
  have ht : k * quad.period + r = quad.blockStart k + r := by
    simp [blockStart]
  rw [ht]
  have hscale :
      (∫ ω,
          |lambda *
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) (quad.blockStart k + r)| ^ 2 ∂μ) =
        lambda ^ 2 *
          (∫ ω,
            |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) (quad.blockStart k + r)| ^ 2 ∂μ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change
        |lambda *
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) (quad.blockStart k + r)| ^ 2 =
        lambda ^ 2 *
          |quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) (quad.blockStart k + r)| ^ 2
      rw [abs_mul, mul_pow]
      rw [sq_abs lambda]
  rw [hscale]
  rw [quadraticScalarComparisonProcess_blockPhase_secondMoment_decomp
    (Node := Node) quad lambda alpha μ oracle hnoise k r]
  rw [quadraticScalarWindowPhaseProduct_blockStart_eq_withinPeriod
    (Node := Node) quad lambda alpha k r]

/-- Quotient form of the finite geometric range sum over real scalars. -/
theorem real_geom_range_sum_div_of_one_sub_ne_zero
    (q : ℝ) (K : ℕ) (hq : 1 - q ≠ 0) :
    (Finset.range K).sum (fun k => q ^ k) =
      (1 - q ^ K) / (1 - q) := by
  have hgeom := geom_sum_mul q K
  field_simp [hq]
  nlinarith [hgeom]

/-- The block-boundary second moment is the variance component plus the
deterministic squared bias at the block boundary. -/
theorem quadraticScalarBlockBoundarySecondMoment_eq_variance_add_bias
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) (k : ℕ) :
    quadraticScalarBlockBoundarySecondMoment (Node := Node)
        quad lambda alpha μ oracle k =
      quadraticScalarBlockBoundaryVariance (Node := Node)
        quad lambda alpha μ oracle k +
        quad.x0 ^ 2 *
          quadraticScalarPeriodMultiplier (Node := Node)
            quad lambda alpha ^ (2 * k) := by
  unfold quadraticScalarBlockBoundaryVariance
  ring

/-- Pure finite-grid algebra for the complete-period scalar second-moment
decomposition.  It splits the block/phase sum into the boundary variance
average, the deterministic geometric bias average, and the fresh within-block
noise average. -/
theorem real_complete_period_phase_bias_fresh_algebra
    {K p : ℕ} (hp : 0 < p) (hK : 1 ≤ K)
    (lambda x0 Gamma : ℝ) (A V : ℕ → ℝ) (F : ℕ → ℕ → ℝ)
    (hgeom :
      (Finset.range K).sum (fun k => Gamma ^ (2 * k)) =
        (1 - Gamma ^ (2 * K)) / (1 - Gamma ^ 2)) :
    let phaseSumNat : ℝ := (Finset.range p).sum (fun r => A r ^ 2)
    let phaseSumFin : ℝ := ∑ r : Fin p, A r.1 ^ 2
    let boundaryAverage : ℝ :=
      lambda ^ 2 * (K : ℝ)⁻¹ * ((Finset.range K).sum fun k => V k)
    let freshAverage : ℝ :=
      lambda ^ 2 * (((K * p : ℕ) : ℝ)⁻¹) *
        ((Finset.range K).sum fun k =>
          (Finset.range p).sum fun r => F k r)
    let biasAverage : ℝ :=
      (lambda ^ 2 * x0 ^ 2 / ((K : ℝ) * (p : ℝ))) *
        phaseSumFin *
          ((1 - Gamma ^ (2 * K)) / (1 - Gamma ^ 2))
    let phaseFactor : ℝ := phaseSumFin / (p : ℝ) - 1
    (((K * p : ℕ) : ℝ)⁻¹) *
        ((Finset.range K).sum fun k =>
          (Finset.range p).sum fun r =>
            lambda ^ 2 *
              (A r ^ 2 * (V k + x0 ^ 2 * Gamma ^ (2 * k)) +
                F k r)) -
      biasAverage - boundaryAverage =
    phaseFactor * boundaryAverage + freshAverage := by
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hK_ne : (K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK_pos)
  have hp_ne : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  exact complete_period_phase_bias_fresh_decomposition
    hK_ne hp_ne lambda x0 Gamma A V F hgeom

/-- Periodic steady boundary variance obtained by dividing the block innovation
variance by `1-Gamma(alpha)^2`, as in Appendix C.2. -/
noncomputable def quadraticScalarSteadyBoundaryVariance
    (quad : Setup Node ℝ) (lambda alpha blockNoiseSecondMoment : ℝ) : ℝ :=
  blockNoiseSecondMoment /
    (1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2)

/-- Under the homogeneous quadratic instance used in Appendix C, the paper's
finite-average objective is literally `x ↦ lambda*x^2/2`. -/
theorem homogeneousQuadratic_objective_eq
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∀ x : ℝ, quad.objective x = lambda * x ^ 2 / 2 := by
  intro x
  have hcard : (Fintype.card Node : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Node ≠ 0)
  have hcomponent :
      ∀ i : Node, quad.componentObjective i x = lambda * x ^ 2 / 2 :=
    fun i => hquad.2.2 i x
  simp [objective, finiteAverageObjectiveOf, SOptLib.finiteUniformAverage,
    nodeCount, hcomponent, hcard]

/-- Under the homogeneous quadratic instance used in Appendix C, each selected
component gradient is the scalar map `x ↦ lambda*x`. -/
theorem homogeneousQuadratic_componentGradient_eq_linear
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∀ i : Node, ∀ x : ℝ, quad.componentGradient i x = lambda * x := by
  intro i x
  have hfun :
      quad.componentObjective i = fun y : ℝ => lambda * y ^ 2 / 2 := by
    funext y
    exact hquad.2.2 i y
  have hgrad :
      HasGradientAt (fun y : ℝ => lambda * y ^ 2 / 2) (lambda * x) x := by
    have hcenter :=
      hasGradientAt_const_mul_norm_sub_sq_centered (E := ℝ) lambda 0 x
    simpa [Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hcenter
  unfold componentGradient
  rw [hfun]
  exact hgrad.gradient

/-- The finite-average gradient of the homogeneous quadratic instance is also
the scalar map `x ↦ lambda*x`. -/
theorem homogeneousQuadratic_averageGradient_eq_linear
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∀ x : ℝ, quad.averageGradient x = lambda * x := by
  intro x
  have hcomp :=
    homogeneousQuadratic_componentGradient_eq_linear
      (Node := Node) quad lambda hquad
  have hcard : (Fintype.card Node : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Node ≠ 0)
  calc
    quad.averageGradient x =
        ((nodeCount (Node := Node) : ℝ)⁻¹) •
          ∑ i : Node, quad.componentGradient i x := by
      exact quad.averageGradient_eq_componentGradient_average x
    _ = lambda * x := by
      simp [hcomp, nodeCount, hcard, smul_eq_mul]

/-- Under the homogeneous quadratic instance, the generated gradient table is
the nodewise scalar multiple `lambda • X`. -/
theorem homogeneousQuadratic_gradientTable_eq_linear
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (X : State Node ℝ) :
    quad.gradientTable X = fun i : Node => lambda * X i := by
  funext i
  simp [gradientTable,
    homogeneousQuadratic_componentGradient_eq_linear
      (Node := Node) quad lambda hquad i (X i)]

/-- For a homogeneous quadratic instance, the generated oracle table is the
linear gradient table plus the fresh noise. -/
theorem homogeneousQuadratic_oracleTable_eq_linear_add_noise
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    let stepped := quad.withStepsize alpha
    stepped.oracleTable noise t =
      (fun i : Node => lambda * stepped.primalState noise t i) + noise t := by
  classical
  let stepped := quad.withStepsize alpha
  have hquad_step :
      HomogeneousQuadraticComponents (Node := Node) stepped lambda := by
    simpa [stepped, withStepsize] using hquad
  unfold oracleTable
  change stepped.sampledGradient noise t (stepped.primalState noise t) =
    (fun i : Node => lambda * stepped.primalState noise t i) + noise t
  rw [stepped.sampledGradient_eq_gradientTable_add_noise]
  rw [homogeneousQuadratic_gradientTable_eq_linear
    (Node := Node) stepped lambda hquad_step (stepped.primalState noise t)]

/-- Appendix C.1 pathwise lifted one-step recursion for the true quadratic
push-pull process in the concrete `(X_t,w_t)` variables, where
`w_t = Y_t-G_t`. -/
theorem quadratic_true_lifted_one_step_recursion
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    let stepped := quad.withStepsize alpha
    let X : State Node ℝ := stepped.primalState noise t
    let w : State Node ℝ := stepped.trackerError noise t
    let Z : State Node ℝ := fun i : Node => lambda * X i
    stepped.primalState noise (t + 1) =
        leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
          alpha • (w + Z + noise t) ∧
      stepped.trackerError noise (t + 1) =
        leftMul (Node := Node) (E := ℝ) (stepped.C t) w +
          leftMul (Node := Node) (E := ℝ)
            (matrixSub (Node := Node) (stepped.C t)
              (identityMatrix (Node := Node))) (Z + noise t) := by
  classical
  let stepped := quad.withStepsize alpha
  let X : State Node ℝ := stepped.primalState noise t
  let w : State Node ℝ := stepped.trackerError noise t
  let Z : State Node ℝ := fun i : Node => lambda * X i
  have horacle :
      stepped.oracleTable noise t = Z + noise t := by
    simpa [stepped, X, Z] using
      homogeneousQuadratic_oracleTable_eq_linear_add_noise
        (Node := Node) quad lambda alpha hquad noise t
  have htracker :
      stepped.trackerState noise t = w + stepped.oracleTable noise t := by
    funext i
    simp [w, trackerError]
  constructor
  · calc
      stepped.primalState noise (t + 1) =
          leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
            (stepped.alpha : ℝ) • stepped.trackerState noise t := by
        simpa [X] using stepped.primalState_succ noise t
      _ =
          leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
            alpha • (w + Z + noise t) := by
        rw [htracker, horacle]
        funext i
        simp [stepped, withStepsize]
        ring
  · calc
      stepped.trackerError noise (t + 1) =
          leftMul (Node := Node) (E := ℝ) (stepped.C t) w +
            leftMul (Node := Node) (E := ℝ)
              (matrixSub (Node := Node) (stepped.C t)
                (identityMatrix (Node := Node)))
              (stepped.oracleTable noise t) := by
        simpa [w] using stepped.trackerError_succ_innovation noise t
      _ =
          leftMul (Node := Node) (E := ℝ) (stepped.C t) w +
            leftMul (Node := Node) (E := ℝ)
              (matrixSub (Node := Node) (stepped.C t)
                (identityMatrix (Node := Node))) (Z + noise t) := by
        rw [horacle]

/-- Concrete block-matrix realization of the Appendix C.1 lifted recurrence.

This is the finite-dimensional object needed before applying the periodic
spectral splitting: the true state `(X_t,w_t)` evolves by a square matrix on
`Node ⊕ Node`, plus a same-phase noise channel.  The tracker component is still
the full node vector here; the next source-local bridge is the zero-sum
restriction used to remove the spurious tracker unit mode. -/
theorem quadratic_true_lifted_one_step_block_action
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    let stepped := quad.withStepsize alpha
    let M : NodeMatrix (Sum Node Node) := fun a b =>
      match a, b with
      | Sum.inl i, Sum.inl j =>
          stepped.R t i j -
            alpha * lambda * identityMatrix (Node := Node) i j
      | Sum.inl i, Sum.inr j =>
          -alpha * identityMatrix (Node := Node) i j
      | Sum.inr i, Sum.inl j =>
          lambda *
            matrixSub (Node := Node) (stepped.C t)
              (identityMatrix (Node := Node)) i j
      | Sum.inr i, Sum.inr j =>
          stepped.C t i j
    let N : (Sum Node Node) → Node → ℝ := fun a j =>
      match a with
      | Sum.inl i => -alpha * identityMatrix (Node := Node) i j
      | Sum.inr i =>
          matrixSub (Node := Node) (stepped.C t)
            (identityMatrix (Node := Node)) i j
    let X : State Node ℝ := stepped.primalState noise t
    let w : State Node ℝ := stepped.trackerError noise t
    let lifted : RowVector (Sum Node Node) := fun a =>
      match a with
      | Sum.inl i => X i
      | Sum.inr i => w i
    let noiseLift : RowVector (Sum Node Node) := fun a =>
      ∑ j : Node, N a j * noise t j
    (fun a : Sum Node Node =>
      match a with
      | Sum.inl i => stepped.primalState noise (t + 1) i
      | Sum.inr i => stepped.trackerError noise (t + 1) i) =
      matrixMulVector (Node := Sum Node Node) M lifted + noiseLift := by
  classical
  let stepped := quad.withStepsize alpha
  let M : NodeMatrix (Sum Node Node) := fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j =>
        stepped.R t i j -
          alpha * lambda * identityMatrix (Node := Node) i j
    | Sum.inl i, Sum.inr j =>
        -alpha * identityMatrix (Node := Node) i j
    | Sum.inr i, Sum.inl j =>
        lambda *
          matrixSub (Node := Node) (stepped.C t)
            (identityMatrix (Node := Node)) i j
    | Sum.inr i, Sum.inr j =>
        stepped.C t i j
  let N : (Sum Node Node) → Node → ℝ := fun a j =>
    match a with
    | Sum.inl i => -alpha * identityMatrix (Node := Node) i j
    | Sum.inr i =>
        matrixSub (Node := Node) (stepped.C t)
          (identityMatrix (Node := Node)) i j
  let X : State Node ℝ := stepped.primalState noise t
  let w : State Node ℝ := stepped.trackerError noise t
  let lifted : RowVector (Sum Node Node) := fun a =>
    match a with
    | Sum.inl i => X i
    | Sum.inr i => w i
  let noiseLift : RowVector (Sum Node Node) := fun a =>
    ∑ j : Node, N a j * noise t j
  have hrec :=
    quadratic_true_lifted_one_step_recursion
      (Node := Node) quad lambda alpha hquad noise t
  have hX : stepped.primalState noise (t + 1) =
      leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
        alpha • (w + (fun i : Node => lambda * X i) + noise t) := by
    simpa [stepped, X, w] using hrec.1
  have hw : stepped.trackerError noise (t + 1) =
      leftMul (Node := Node) (E := ℝ) (stepped.C t) w +
        leftMul (Node := Node) (E := ℝ)
          (matrixSub (Node := Node) (stepped.C t)
            (identityMatrix (Node := Node)))
          ((fun i : Node => lambda * X i) + noise t) := by
    simpa [stepped, X, w] using hrec.2
  funext a
  cases a with
  | inl i =>
      have hXi := congrFun hX i
      have hdeltaX :
          (∑ x : Node, (if i = x then alpha * lambda else 0) * X x) =
            alpha * lambda * X i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _hb hb_ne
          have hne : i ≠ b := fun h => hb_ne h.symm
          simp [hne]
        · intro hi
          simp at hi
      have hsumMX :
          (∑ x : Node,
            (stepped.R t i x + -(if i = x then alpha * lambda else 0)) *
              X x) =
            (∑ x : Node, stepped.R t i x * X x) -
              alpha * lambda * X i := by
        calc
          (∑ x : Node,
            (stepped.R t i x + -(if i = x then alpha * lambda else 0)) *
              X x) =
              ∑ x : Node,
                (stepped.R t i x * X x -
                  (if i = x then alpha * lambda else 0) * X x) := by
                apply Finset.sum_congr rfl
                intro x _hx
                ring
          _ =
              (∑ x : Node, stepped.R t i x * X x) -
                ∑ x : Node, (if i = x then alpha * lambda else 0) * X x := by
                rw [Finset.sum_sub_distrib]
          _ =
              (∑ x : Node, stepped.R t i x * X x) -
                alpha * lambda * X i := by
                rw [hdeltaX]
      calc
        (match Sum.inl i with
          | Sum.inl i => stepped.primalState noise (t + 1) i
          | Sum.inr i => stepped.trackerError noise (t + 1) i) =
            (leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
              alpha • (w + (fun i : Node => lambda * X i) + noise t)) i := by
              simpa using hXi
        _ =
            (matrixMulVector (Node := Sum Node Node) M lifted +
              noiseLift) (Sum.inl i) := by
              simp [M, N, lifted, noiseLift, matrixMulVector, leftMul,
                matrixSub, identityMatrix, Finset.sum_add_distrib,
                Finset.mul_sum, smul_eq_mul, sub_eq_add_neg]
              rw [hsumMX]
              ring
  | inr i =>
      have hwi := congrFun hw i
      have hdist :
          (∑ x : Node,
            (stepped.C t i x + -(if i = x then 1 else 0)) *
              (lambda * X x + noise t x)) =
            (∑ x : Node,
              lambda * (stepped.C t i x + -(if i = x then 1 else 0)) *
                X x) +
              ∑ x : Node,
                (stepped.C t i x + -(if i = x then 1 else 0)) *
                  noise t x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      calc
        (match Sum.inr i with
          | Sum.inl i => stepped.primalState noise (t + 1) i
          | Sum.inr i => stepped.trackerError noise (t + 1) i) =
            (leftMul (Node := Node) (E := ℝ) (stepped.C t) w +
              leftMul (Node := Node) (E := ℝ)
                (matrixSub (Node := Node) (stepped.C t)
                  (identityMatrix (Node := Node)))
                ((fun i : Node => lambda * X i) + noise t)) i := by
              simpa using hwi
        _ =
            (matrixMulVector (Node := Sum Node Node) M lifted +
              noiseLift) (Sum.inr i) := by
              simp [M, N, lifted, noiseLift, matrixMulVector, leftMul,
                matrixSub, identityMatrix, Finset.sum_add_distrib,
                Finset.mul_sum, smul_eq_mul, sub_eq_add_neg]
              rw [hdist]
              ring

/-- Appendix C.1 lifted recurrence on the source state space
`R^n × {w : 1^T w = 0}`.

The previous block-action lemma realizes the same recurrence on the ambient
`Node ⊕ Node` coordinates.  This bridge packages the tracker coordinate as a
`ZeroSumState`, with both the transported tracker error and the pull innovation
kept inside the zero-sum subspace. -/
theorem quadratic_zero_sum_lifted_step_action
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    let stepped := quad.withStepsize alpha
    let X : State Node ℝ := stepped.primalState noise t
    let W : ZeroSumState Node ℝ := stepped.trackerErrorZeroSum noise t
    let Z : State Node ℝ := fun i : Node => lambda * X i
    let transported : ZeroSumState Node ℝ :=
      ⟨leftMul (Node := Node) (E := ℝ) (stepped.C t) W.1,
        stepped.C_leftMul_zeroSum t W⟩
    let innovation : ZeroSumState Node ℝ :=
      ⟨leftMul (Node := Node) (E := ℝ)
          (matrixSub (Node := Node) (stepped.C t)
            (identityMatrix (Node := Node))) (Z + noise t),
        stepped.pull_innovation_sum_zero t (Z + noise t)⟩
    stepped.primalState noise (t + 1) =
        leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
          alpha • (W.1 + Z + noise t) ∧
      stepped.trackerErrorZeroSum noise (t + 1) =
        ⟨transported.1 + innovation.1,
          zeroSumState_add_mem transported innovation⟩ := by
  classical
  let stepped := quad.withStepsize alpha
  let X : State Node ℝ := stepped.primalState noise t
  let W : ZeroSumState Node ℝ := stepped.trackerErrorZeroSum noise t
  let Z : State Node ℝ := fun i : Node => lambda * X i
  let transported : ZeroSumState Node ℝ :=
    ⟨leftMul (Node := Node) (E := ℝ) (stepped.C t) W.1,
      stepped.C_leftMul_zeroSum t W⟩
  let innovation : ZeroSumState Node ℝ :=
    ⟨leftMul (Node := Node) (E := ℝ)
        (matrixSub (Node := Node) (stepped.C t)
          (identityMatrix (Node := Node))) (Z + noise t),
      stepped.pull_innovation_sum_zero t (Z + noise t)⟩
  have _hblock :=
    quadratic_true_lifted_one_step_block_action
      (Node := Node) quad lambda alpha hquad noise t
  have hrec :=
    quadratic_true_lifted_one_step_recursion
      (Node := Node) quad lambda alpha hquad noise t
  constructor
  · simpa [stepped, X, W, Z] using hrec.1
  · apply Subtype.ext
    have hw :
        stepped.trackerError noise (t + 1) =
          leftMul (Node := Node) (E := ℝ) (stepped.C t) W.1 +
            leftMul (Node := Node) (E := ℝ)
              (matrixSub (Node := Node) (stepped.C t)
                (identityMatrix (Node := Node))) (Z + noise t) := by
      simpa [stepped, X, W, Z] using hrec.2
    simpa [stepped, W, transported, innovation, trackerErrorZeroSum] using hw

/-- Appendix C.1 base-period stability input for the restricted `alpha = 0`
period matrix.

On the source space `R^n × {w : 1^T w = 0}`, the two non-slow blocks at
`alpha = 0` are exactly the primal disagreement push product and the tracker
zero-sum pull product.  This packages the two estimates from
`PeriodicProductContraction` in the form used before applying the spectral
splitting theorem. -/
theorem quadratic_restricted_base_period_stable_blocks
    (quad : Setup Node ℝ) :
    0 ≤ quad.contractionRate ∧ quad.contractionRate < 1 ∧
      (∀ (t : ℕ) (W : ZeroSumState Node ℝ),
        stateFrobeniusNorm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct t quad.period) W.1) ≤
          quad.columnContractionConstant * quad.contractionRate ^ quad.period *
            stateFrobeniusNorm (Node := Node) (E := ℝ) W.1) ∧
      (∀ (t : ℕ) (X : State Node ℝ),
        stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pushLiftProduct t quad.period) X)) ≤
          quad.rowContractionConstant * quad.contractionRate ^ quad.period *
            stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ) X)) := by
  classical
  have hcontract := quad.PeriodicProductContraction
  refine ⟨hcontract.2.1, hcontract.2.2.1, ?_, ?_⟩
  · intro t W
    exact hcontract.2.2.2.1 t quad.period W
  · intro t X
    exact hcontract.2.2.2.2 t quad.period X

/-- Appendix C.1 stable-block input at the strength actually used by the
alpha-zero spectral proof.

The one-period estimates above are useful for local bookkeeping, but the
spectral-radius argument needs the full Lemma 4.2 geometric estimates for
arbitrary product lengths.  This source-facing private bridge keeps the
alpha-zero spectral certificate tied to `PeriodicProductContraction` rather
than to a too-weak one-period surrogate. -/
theorem quadratic_restricted_all_lengths_stable_blocks
    (quad : Setup Node ℝ) :
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
              (consensusError (Node := Node) (E := ℝ) X)) := by
  classical
  have hcontract := quad.PeriodicProductContraction
  exact ⟨hcontract.2.1, hcontract.2.2.1,
    hcontract.2.2.2.1, hcontract.2.2.2.2⟩

/-- Finite coordinate chart for the zero-sum tracker subspace, using all
non-base node coordinates as free coordinates.

This is the route-local finite-dimensional bridge needed before feeding the
Appendix C.1 restricted state space into the `NodeMatrix` spectral API. -/
theorem zero_sum_state_coordinate_chart
    (i0 : Node) :
    ∃ toCoord : ZeroSumState Node ℝ → ({i : Node // i ≠ i0} → ℝ),
    ∃ ofCoord : ({i : Node // i ≠ i0} → ℝ) → ZeroSumState Node ℝ,
      (∀ W : ZeroSumState Node ℝ, ofCoord (toCoord W) = W) ∧
        (∀ y : {i : Node // i ≠ i0} → ℝ, toCoord (ofCoord y) = y) := by
  classical exact FiniteNetwork.ZeroSumState.exists_restrict_compl_inverse i0

/-- Product coordinate chart for the Appendix C.1 restricted state space
`R^n × {w : 1^T w = 0}`.

The chart keeps all primal coordinates and uses the non-base tracker
coordinates from `zero_sum_state_coordinate_chart`, giving a `NodeMatrix`-ready
finite type `Node ⊕ {i // i ≠ i0}`. -/
theorem restricted_state_coordinate_chart
    (i0 : Node) :
    ∃ toCoord :
        (State Node ℝ × ZeroSumState Node ℝ) →
          RowVector (Sum Node {i : Node // i ≠ i0}),
    ∃ ofCoord :
        RowVector (Sum Node {i : Node // i ≠ i0}) →
          (State Node ℝ × ZeroSumState Node ℝ),
      (∀ S : State Node ℝ × ZeroSumState Node ℝ,
        ofCoord (toCoord S) = S) ∧
        (∀ y : RowVector (Sum Node {i : Node // i ≠ i0}),
          toCoord (ofCoord y) = y) := by
  classical
  obtain ⟨toW, ofW, hW_left, hW_right⟩ :=
    zero_sum_state_coordinate_chart (Node := Node) i0
  let toCoord :
      (State Node ℝ × ZeroSumState Node ℝ) →
        RowVector (Sum Node {i : Node // i ≠ i0}) := fun S a =>
    match a with
    | Sum.inl i => S.1 i
    | Sum.inr j => toW S.2 j
  let ofCoord :
      RowVector (Sum Node {i : Node // i ≠ i0}) →
        (State Node ℝ × ZeroSumState Node ℝ) := fun y =>
    (fun i : Node => y (Sum.inl i), ofW (fun j => y (Sum.inr j)))
  refine ⟨toCoord, ofCoord, ?_, ?_⟩
  · intro S
    cases S with
    | mk X W =>
        apply Prod.ext
        · funext i
          rfl
        · exact hW_left W
  · intro y
    funext a
    cases a with
    | inl i => rfl
    | inr j =>
        exact congrFun (hW_right (fun j => y (Sum.inr j))) j

/-- Private finite-index instance for the non-base tracker coordinates. -/
noncomputable instance restrictedNonbaseFintype
    (i0 : Node) : Fintype {i : Node // i ≠ i0} := by
  classical
  infer_instance

/-- Private finite-index instance for the restricted C.1 product coordinate
carrier. -/
noncomputable instance restrictedProductFintype
    (i0 : Node) : Fintype (Sum Node {i : Node // i ≠ i0}) := by
  classical
  infer_instance

/-- Canonical coordinates on the restricted Appendix C.1 state space. -/
noncomputable def restrictedStateToCoord
    (i0 : Node) :
    (State Node ℝ × ZeroSumState Node ℝ) →
      RowVector (Sum Node {i : Node // i ≠ i0}) :=
  fun S a =>
    match a with
    | Sum.inl i => S.1 i
    | Sum.inr j => S.2.1 j.1

/-- The base zero-sum coordinate is the negative sum of the free coordinates. -/
theorem zeroSumState_base_eq_neg_free_sum
    (i0 : Node) (W : ZeroSumState Node ℝ) :
    W.1 i0 = -∑ j : {j : Node // j ≠ i0}, W.1 j.1 := by
  classical exact FiniteNetwork.ZeroSumState.base_eq_neg_sum_compl i0 W

/-- The complex state assembled from two zero-sum real tracker states has its
base coordinate determined by the non-base coordinates. -/
theorem zero_sum_complex_base_eq_neg_free_sum
    (i0 : Node) (U V : ZeroSumState Node ℝ) :
    ((U.1 i0 : ℂ) + (V.1 i0 : ℂ) * Complex.I) =
      -∑ j : {j : Node // j ≠ i0},
        ((U.1 j.1 : ℂ) + (V.1 j.1 : ℂ) * Complex.I) := by
  classical
  rw [zeroSumState_base_eq_neg_free_sum (Node := Node) i0 U,
    zeroSumState_base_eq_neg_free_sum (Node := Node) i0 V]
  simp [Finset.sum_add_distrib, Finset.sum_mul, add_comm]

/-- Free-coordinate equality between two zero-sum real/imaginary tracker pairs
determines the full complex tracker state. -/
theorem zero_sum_complex_tracker_ext_of_free_coords
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
    (fun i : Node => (Xre.1 i : ℂ) + (Xim.1 i : ℂ) * Complex.I) =
      a • (fun i : Node => (Yre.1 i : ℂ) + (Yim.1 i : ℂ) * Complex.I) := by
  classical
  have hfree_complex :
      ∀ j : {i : Node // i ≠ i0},
        ((Xre.1 j.1 : ℂ) + (Xim.1 j.1 : ℂ) * Complex.I) =
          a * ((Yre.1 j.1 : ℂ) + (Yim.1 j.1 : ℂ) * Complex.I) := by
    intro j
    apply Complex.ext
    · simpa using hre j
    · simpa using him j
  funext i
  by_cases hi : i = i0
  · subst i
    calc
      ((Xre.1 i0 : ℂ) + (Xim.1 i0 : ℂ) * Complex.I) =
          -∑ j : {i : Node // i ≠ i0},
            ((Xre.1 j.1 : ℂ) + (Xim.1 j.1 : ℂ) * Complex.I) := by
          exact zero_sum_complex_base_eq_neg_free_sum (Node := Node) i0 Xre Xim
      _ =
          -∑ j : {i : Node // i ≠ i0},
            a * ((Yre.1 j.1 : ℂ) + (Yim.1 j.1 : ℂ) * Complex.I) := by
          exact congrArg Neg.neg
            (Finset.sum_congr rfl (fun j _hj => hfree_complex j))
      _ =
          a * (-(∑ j : {i : Node // i ≠ i0},
            ((Yre.1 j.1 : ℂ) + (Yim.1 j.1 : ℂ) * Complex.I))) := by
          rw [mul_neg, Finset.mul_sum]
      _ =
          a * ((Yre.1 i0 : ℂ) + (Yim.1 i0 : ℂ) * Complex.I) := by
          rw [← zero_sum_complex_base_eq_neg_free_sum (Node := Node) i0 Yre Yim]
      _ =
          (a • fun i : Node =>
            (Yre.1 i : ℂ) + (Yim.1 i : ℂ) * Complex.I) i0 := rfl
  · simpa [hi] using hfree_complex ⟨i, hi⟩

/-- Explicit zero-sum reconstruction from the non-base free coordinates. -/
theorem exists_zeroSumState_with_free_coords
    (i0 : Node) (y : {i : Node // i ≠ i0} → ℝ) :
    ∃ W : ZeroSumState Node ℝ, ∀ j : {i : Node // i ≠ i0}, W.1 j.1 = y j := by
  classical
  refine ⟨⟨fun i : Node =>
      if h : i = i0 then -∑ j : {j : Node // j ≠ i0}, y j else y ⟨i, h⟩,
    ?_⟩, ?_⟩
  · have hsplit :
        (∑ i : Node,
          (if h : i = i0 then
            -∑ j : {j : Node // j ≠ i0}, y j
          else
            y ⟨i, h⟩)) =
          (-∑ j : {j : Node // j ≠ i0}, y j) +
            (Finset.univ.erase i0).sum (fun i : Node =>
              if h : i = i0 then
                -∑ j : {j : Node // j ≠ i0}, y j
              else
                y ⟨i, h⟩) := by
      simpa using
        (Finset.sum_eq_add_sum_diff_singleton
          (s := (Finset.univ : Finset Node))
          (a := i0)
          (f := fun i : Node =>
            if h : i = i0 then
              -∑ j : {j : Node // j ≠ i0}, y j
            else
              y ⟨i, h⟩)
          (by simp))
    have hsub :
        (Finset.univ.erase i0).sum (fun i : Node =>
          if h : i = i0 then
            -∑ j : {j : Node // j ≠ i0}, y j
          else
            y ⟨i, h⟩) =
          ∑ j : {j : Node // j ≠ i0}, y j := by
      symm
      refine Finset.sum_bij
        (fun j _hj => (j : {j : Node // j ≠ i0}).1)
        ?_ ?_ ?_ ?_
      · intro j _hj
        simp [j.2]
      · intro a _ha b _hb h
        exact Subtype.ext h
      · intro b hb
        refine ⟨⟨b, ?_⟩, by simp, ?_⟩
        · exact (Finset.mem_erase.mp hb).1
        · rfl
      · intro j _hj
        simp [j.2]
    rw [hsplit, hsub]
    ring
  · intro j
    simp [j.2]

/-- The canonical restricted coordinates determine the restricted state. -/
theorem restrictedStateToCoord_injective
    (i0 : Node) :
    Function.Injective (restrictedStateToCoord (Node := Node) i0) := by
  classical
  intro S T h
  cases S with
  | mk X W =>
      cases T with
      | mk Y V =>
          apply Prod.ext
          · funext i
            simpa [restrictedStateToCoord] using congrFun h (Sum.inl i)
          · apply Subtype.ext
            funext i
            by_cases hi : i = i0
            · subst i
              have hfree :
                  ∀ j : {j : Node // j ≠ i0}, W.1 j.1 = V.1 j.1 := by
                intro j
                simpa [restrictedStateToCoord] using congrFun h (Sum.inr j)
              rw [zeroSumState_base_eq_neg_free_sum (Node := Node) i0 W,
                zeroSumState_base_eq_neg_free_sum (Node := Node) i0 V]
              exact congrArg Neg.neg
                (Finset.sum_congr rfl (fun j _hj => hfree j))
            · simpa [restrictedStateToCoord] using
                congrFun h (Sum.inr ⟨i, hi⟩)

/-- Coefficient of a free zero-sum coordinate in the full tracker vector.
The base node coordinate is the negative sum of all free coordinates. -/
noncomputable def restrictedTrackerCoordCoeff
    (i0 : Node) (i : Node) (j : {j : Node // j ≠ i0}) : ℝ :=
  by
    classical
    exact if i = i0 then -1 else if i = j.1 then 1 else 0

/-- The free-coordinate reconstruction coefficients recover a zero-sum tracker
coordinate. -/
theorem restrictedTrackerCoordCoeff_sum_apply
    (i0 : Node) (W : ZeroSumState Node ℝ) (i : Node) :
    (∑ j : {j : Node // j ≠ i0},
      restrictedTrackerCoordCoeff (Node := Node) i0 i j * W.1 j.1) =
      W.1 i := by
  classical
  by_cases hi : i = i0
  · subst i
    have hbase := zeroSumState_base_eq_neg_free_sum (Node := Node) i0 W
    simp [restrictedTrackerCoordCoeff, hbase]
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp [restrictedTrackerCoordCoeff, hi]
    · intro b _hb hb_ne
      have hne : i ≠ b.1 := by
        intro h
        apply hb_ne
        exact Subtype.ext h.symm
      simp [restrictedTrackerCoordCoeff, hi, hne]
    · intro hmem
      simp at hmem

/-- The bottom-right restricted tracker block is the pull action on the
zero-sum tracker, with the base coordinate eliminated. -/
theorem restrictedTrackerPullFreeCoord_sum_apply
    (quad : Setup Node ℝ) (i0 : Node) (W : ZeroSumState Node ℝ)
    (t : ℕ) (i : {i : Node // i ≠ i0}) :
    (∑ j : {j : Node // j ≠ i0},
      (quad.C t i.1 j.1 - quad.C t i.1 i0) * W.1 j.1) =
      leftMul (Node := Node) (E := ℝ) (quad.C t) W.1 i.1 := by
  classical
  simpa [leftMul, smul_eq_mul] using
    (Matrix.sum_compl_sub_base_mul_eq_mulVec_of_sum_eq_zero
      (A := quad.C t) (w := W.1) (i0 := i0) (i := i.1) W.property)

/-- Appendix C.1 restricted homogeneous one-step matrix in the concrete
coordinates `R^n × {w : 1^T w = 0} ≃ R^(Node ⊕ {i // i ≠ i0})`.

This is the block matrix
`[[R_t - alpha lambda I, -alpha I], [lambda(C_t-I), C_t]]`
from equation (C.1), with the tracker block written in free zero-sum
coordinates by eliminating the base coordinate `i0`. -/
noncomputable def quadraticRestrictedOneStepMatrix
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) (t : ℕ) :
    NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
  fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j =>
        quad.R t i j - alpha * lambda * identityMatrix (Node := Node) i j
    | Sum.inl i, Sum.inr j =>
        -alpha * restrictedTrackerCoordCoeff (Node := Node) i0 i j
    | Sum.inr i, Sum.inl j =>
        lambda *
          (quad.C t i.1 j - identityMatrix (Node := Node) i.1 j)
    | Sum.inr i, Sum.inr j =>
        quad.C t i.1 j.1 - quad.C t i.1 i0

/-- The true restricted one-period homogeneous propagator used in Appendix
C.1.  The product starts at phase zero and has length `quad.period`. -/
noncomputable def quadraticRestrictedPeriodMatrix
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) :
    NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
  by
    classical
    exact
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun t => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 t) 0 quad.period

/-- The deterministic homogeneous restricted C.1 one-step map on
`R^n × {w : 1^T w = 0}`. -/
noncomputable def quadraticRestrictedHomogeneousStep
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (t : ℕ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    State Node ℝ × ZeroSumState Node ℝ :=
  let X : State Node ℝ := S.1
  let W : ZeroSumState Node ℝ := S.2
  let Z : State Node ℝ := fun i : Node => lambda * X i
  let transported : ZeroSumState Node ℝ :=
    ⟨leftMul (Node := Node) (E := ℝ) (quad.C t) W.1,
      quad.C_leftMul_zeroSum t W⟩
  let innovation : ZeroSumState Node ℝ :=
    ⟨leftMul (Node := Node) (E := ℝ)
        (matrixSub (Node := Node) (quad.C t)
          (identityMatrix (Node := Node))) Z,
      quad.pull_innovation_sum_zero t Z⟩
  (leftMul (Node := Node) (E := ℝ) (quad.R t) X -
      alpha • (W.1 + Z),
    ⟨transported.1 + innovation.1,
      zeroSumState_add_mem transported innovation⟩)

/-- The concrete restricted one-step matrix acts as the deterministic
homogeneous restricted C.1 update in canonical coordinates. -/
theorem quadraticRestrictedOneStepMatrix_action
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) (t : ℕ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedOneStepMatrix (Node := Node)
          quad lambda alpha i0 t)
        (restrictedStateToCoord (Node := Node) i0 S) =
      restrictedStateToCoord (Node := Node) i0
        (quadraticRestrictedHomogeneousStep
          (Node := Node) quad lambda alpha t S) := by
  classical
  cases S with
  | mk X W =>
      funext a
      cases a with
      | inl i =>
          have htracker :=
            restrictedTrackerCoordCoeff_sum_apply
              (Node := Node) i0 W i
          have hdiag :
              (∑ x : Node, (if i = x then alpha * lambda else 0) * X x) =
                alpha * lambda * X i := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro b _hb hb_ne
              have hne : i ≠ b := fun h => hb_ne h.symm
              simp [hne]
            · intro hmem
              simp at hmem
          have htracker_scaled :
              (∑ x : {x : Node // x ≠ i0},
                alpha * restrictedTrackerCoordCoeff (Node := Node) i0 i x *
                  W.1 x.1) =
                alpha * W.1 i := by
            calc
              (∑ x : {x : Node // x ≠ i0},
                alpha * restrictedTrackerCoordCoeff (Node := Node) i0 i x *
                  W.1 x.1) =
                  alpha *
                    (∑ x : {x : Node // x ≠ i0},
                      restrictedTrackerCoordCoeff (Node := Node) i0 i x *
                        W.1 x.1) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro x _hx
                    ring
              _ = alpha * W.1 i := by rw [htracker]
          have hdiag_row :
              (∑ x : Node,
                (quad.R t i x + -(if i = x then alpha * lambda else 0)) *
                  X x) =
                (∑ x : Node, quad.R t i x * X x) -
                  alpha * lambda * X i := by
            calc
              (∑ x : Node,
                (quad.R t i x + -(if i = x then alpha * lambda else 0)) *
                  X x) =
                  ∑ x : Node,
                    (quad.R t i x * X x -
                      (if i = x then alpha * lambda else 0) * X x) := by
                    apply Finset.sum_congr rfl
                    intro x _hx
                    ring
              _ =
                  (∑ x : Node, quad.R t i x * X x) -
                    ∑ x : Node,
                      (if i = x then alpha * lambda else 0) * X x := by
                    rw [Finset.sum_sub_distrib]
              _ =
                  (∑ x : Node, quad.R t i x * X x) -
                    alpha * lambda * X i := by
                    rw [hdiag]
          simp [quadraticRestrictedOneStepMatrix,
            quadraticRestrictedHomogeneousStep, restrictedStateToCoord,
            matrixMulVector, leftMul, matrixSub, identityMatrix,
            Finset.sum_add_distrib, Finset.mul_sum,
            sub_eq_add_neg, smul_eq_mul]
          rw [hdiag_row, htracker_scaled]
          ring
      | inr i =>
          have hpull :=
            restrictedTrackerPullFreeCoord_sum_apply
              (Node := Node) quad i0 W t i
          have hpull' :
              (∑ x : {x : Node // x ≠ i0},
                (quad.C t i.1 x.1 - quad.C t i.1 i0) * W.1 x.1) =
                ∑ x : Node, quad.C t i.1 x * W.1 x := by
            simpa [leftMul, smul_eq_mul] using hpull
          have hpull'' :
              (∑ x : {x : Node // x ≠ i0},
                (quad.C t i.1 x.1 + -quad.C t i.1 i0) * W.1 x.1) =
                ∑ x : Node, quad.C t i.1 x * W.1 x := by
            calc
              (∑ x : {x : Node // x ≠ i0},
                (quad.C t i.1 x.1 + -quad.C t i.1 i0) * W.1 x.1) =
                  ∑ x : {x : Node // x ≠ i0},
                    (quad.C t i.1 x.1 - quad.C t i.1 i0) * W.1 x.1 := by
                    apply Finset.sum_congr rfl
                    intro x _hx
                    ring
              _ = ∑ x : Node, quad.C t i.1 x * W.1 x := hpull'
          simp [quadraticRestrictedOneStepMatrix,
            quadraticRestrictedHomogeneousStep, restrictedStateToCoord,
            matrixMulVector, leftMul, matrixSub, identityMatrix,
            Finset.sum_add_distrib, Finset.mul_sum,
            sub_eq_add_neg, smul_eq_mul]
          rw [hpull'']
          ring

/-- Appendix C.1 restricted noise channel in the same canonical coordinates as
`quadraticRestrictedOneStepMatrix`.

This is the coordinate form of `N_t(alpha) epsilon_t =
(-alpha * epsilon_t, (C_t-I) epsilon_t)` on
`R^n × {w : 1^T w = 0}`. -/
noncomputable def quadraticRestrictedNoiseInnovationCoord
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    RowVector (Sum Node {i : Node // i ≠ i0}) :=
  restrictedStateToCoord (Node := Node) i0
    (fun i : Node => -alpha * noise t i,
      ⟨leftMul (Node := Node) (E := ℝ)
        (matrixSub (Node := Node) (quad.C t)
          (identityMatrix (Node := Node))) (noise t),
        quad.pull_innovation_sum_zero t (noise t)⟩)

/-- Deterministic node-noise coefficient row for one restricted C.1 noise
channel coordinate.  This is the row form of
`N_t(alpha) epsilon_t = (-alpha epsilon_t, (C_t-I)epsilon_t)`. -/
noncomputable def quadraticRestrictedNoiseInnovationCoeff
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node) (t : ℕ)
    (a : Sum Node {i : Node // i ≠ i0}) : RowVector Node :=
  fun j : Node => by
    classical
    exact
      match a with
      | Sum.inl i => if i = j then -alpha else 0
      | Sum.inr i =>
          quad.C t i.1 j - identityMatrix (Node := Node) i.1 j

/-- The deterministic restricted noise row depends on a block time only through
its within-period phase. -/
theorem quadraticRestrictedNoiseInnovationCoeff_blockStart_add
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    (k r : ℕ) (a : Sum Node {i : Node // i ≠ i0}) :
    quadraticRestrictedNoiseInnovationCoeff
        (Node := Node) quad alpha i0 (quad.blockStart k + r) a =
      quadraticRestrictedNoiseInnovationCoeff
        (Node := Node) quad alpha i0 r a := by
  classical
  funext j
  cases a with
  | inl i =>
      simp [quadraticRestrictedNoiseInnovationCoeff]
  | inr i =>
      induction k with
      | zero =>
          simp [Setup.blockStart, quadraticRestrictedNoiseInnovationCoeff]
      | succ k ih =>
          have htime :
              quad.blockStart (k + 1) + r =
                (quad.blockStart k + r) + quad.period := by
            unfold Setup.blockStart
            rw [Nat.succ_mul]
            omega
          have hC :=
            congrFun (congrFun (quad.C_periodic (quad.blockStart k + r)) i.1) j
          calc
            quadraticRestrictedNoiseInnovationCoeff
                (Node := Node) quad alpha i0
                (quad.blockStart (k + 1) + r) (Sum.inr i) j =
              quad.C (quad.blockStart (k + 1) + r) i.1 j -
                identityMatrix (Node := Node) i.1 j := by
                  simp [quadraticRestrictedNoiseInnovationCoeff]
            _ =
              quad.C ((quad.blockStart k + r) + quad.period) i.1 j -
                identityMatrix (Node := Node) i.1 j := by
                  rw [htime]
            _ =
              quad.C (quad.blockStart k + r) i.1 j -
                identityMatrix (Node := Node) i.1 j := by
                  rw [hC]
            _ =
              quadraticRestrictedNoiseInnovationCoeff
                (Node := Node) quad alpha i0
                (quad.blockStart k + r) (Sum.inr i) j := by
                  simp [quadraticRestrictedNoiseInnovationCoeff]
            _ =
              quadraticRestrictedNoiseInnovationCoeff
                (Node := Node) quad alpha i0 r (Sum.inr i) j := by
                  exact ih

/-- The one-step restricted noise channel is exactly a deterministic weighted
node-noise row in every restricted coordinate. -/
theorem quadraticRestrictedNoiseInnovationCoord_eq_weightedCoeff
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (t : ℕ)
    (a : Sum Node {i : Node // i ≠ i0}) :
    quadraticRestrictedNoiseInnovationCoord
        (Node := Node) quad alpha i0 noise t a =
      weightedState (Node := Node) (E := ℝ)
        (quadraticRestrictedNoiseInnovationCoeff
          (Node := Node) quad alpha i0 t a)
        (noise t) := by
  classical
  cases a with
  | inl i =>
      change -alpha * noise t i =
        weightedState (Node := Node) (E := ℝ)
          (quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t (Sum.inl i)) (noise t)
      simp [quadraticRestrictedNoiseInnovationCoeff, weightedState]
  | inr i =>
      simp [quadraticRestrictedNoiseInnovationCoord,
        quadraticRestrictedNoiseInnovationCoeff, restrictedStateToCoord,
        weightedState, leftMul, matrixSub]

/-- One-step affine restricted recurrence for the true noisy quadratic process.

The homogeneous part is exactly the canonical restricted C.1 matrix, and the
inhomogeneous part is the finite same-phase noise channel above.  This is the
source bridge needed before unrolling one period and applying the restricted
spectral splitting. -/
theorem quadraticRestrictedOneStepMatrix_affine_process_action
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    let stepped := quad.withStepsize alpha
    restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise (t + 1),
          stepped.trackerErrorZeroSum noise (t + 1)) =
      matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda alpha i0 t)
          (restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise t,
              stepped.trackerErrorZeroSum noise t)) +
        quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 noise t := by
  classical
  let stepped := quad.withStepsize alpha
  let X : State Node ℝ := stepped.primalState noise t
  let W : ZeroSumState Node ℝ := stepped.trackerErrorZeroSum noise t
  let Z : State Node ℝ := fun i : Node => lambda * X i
  let transported : ZeroSumState Node ℝ :=
    ⟨leftMul (Node := Node) (E := ℝ) (stepped.C t) W.1,
      stepped.C_leftMul_zeroSum t W⟩
  let innovationFull : ZeroSumState Node ℝ :=
    ⟨leftMul (Node := Node) (E := ℝ)
        (matrixSub (Node := Node) (stepped.C t)
          (identityMatrix (Node := Node))) (Z + noise t),
      stepped.pull_innovation_sum_zero t (Z + noise t)⟩
  have hstep :=
    quadratic_zero_sum_lifted_step_action
      (Node := Node) quad lambda alpha hquad noise t
  have hhom :
      matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda alpha i0 t)
          (restrictedStateToCoord (Node := Node) i0 (X, W)) =
        restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousStep
            (Node := Node) quad lambda alpha t (X, W)) :=
    quadraticRestrictedOneStepMatrix_action
      (Node := Node) quad lambda alpha i0 t (X, W)
  change
    restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise (t + 1),
          stepped.trackerErrorZeroSum noise (t + 1)) =
      matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda alpha i0 t)
          (restrictedStateToCoord (Node := Node) i0 (X, W)) +
        quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 noise t
  rw [hhom]
  funext a
  cases a with
  | inl i =>
      have hXi := congrFun hstep.1 i
      simp [stepped, X, W, Z, transported, innovationFull,
        quadraticRestrictedHomogeneousStep,
        quadraticRestrictedNoiseInnovationCoord, restrictedStateToCoord,
        withStepsize, leftMul, matrixSub, identityMatrix, smul_eq_mul,
        sub_eq_add_neg] at hXi ⊢
      linarith
  | inr i =>
      have hWi := congrFun (congrArg Subtype.val hstep.2) i.1
      simp [stepped, X, W, Z, transported, innovationFull,
        quadraticRestrictedHomogeneousStep,
        quadraticRestrictedNoiseInnovationCoord, restrictedStateToCoord,
        withStepsize, leftMul, matrixSub, identityMatrix, smul_eq_mul,
        Finset.sum_add_distrib, Finset.mul_sum, add_comm, add_left_comm,
        add_assoc] at hWi ⊢
      rw [hWi]
      simp [mul_add, sub_mul, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring

/-- Linearity of the restricted coordinate matrix action in the vector input. -/
theorem quadraticRestricted_matrixMulVector_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : NodeMatrix ι) (x y : RowVector ι) :
    matrixMulVector (Node := ι) A (x + y) =
      matrixMulVector (Node := ι) A x +
        matrixMulVector (Node := ι) A y := by
  classical
  funext i
  simp [matrixMulVector, Finset.sum_add_distrib, mul_add]

/-- Finite Duhamel noise innovation accumulated by the restricted affine
C.1 recurrence over a consecutive window.

For `n + 1`, the previous window innovation is propagated by the next
homogeneous phase and then the phase-`start+n` noise channel is added. -/
noncomputable def quadraticRestrictedConsecutiveNoiseInnovationCoord
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (start : ℕ) :
    ℕ → RowVector (Sum Node {i : Node // i ≠ i0})
  | 0 => 0
  | n + 1 =>
      matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda alpha i0 (start + n))
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            quad lambda alpha i0 noise start n) +
        quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 noise (start + n)

/-- At `alpha = 0`, one restricted C.1 noise-channel vector has no primal
coordinate.  This is the source block `N_t(0) epsilon_t = (0,(C_t-I)epsilon_t)`
from Appendix C.1. -/
theorem quadraticRestrictedNoiseInnovationCoord_alpha_zero_top
    (quad : Setup Node ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (t : ℕ) (i : Node) :
    quadraticRestrictedNoiseInnovationCoord
        (Node := Node) quad 0 i0 noise t (Sum.inl i) = 0 := by
  simp [quadraticRestrictedNoiseInnovationCoord, restrictedStateToCoord]

/-- The alpha-zero restricted homogeneous matrix preserves the zero-primal
subspace.  It is the one-step form of the block-lower-triangular structure used
in Appendix C.1 before applying the stable Riesz projection. -/
theorem quadraticRestrictedOneStepMatrix_alpha_zero_top_apply_of_top_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (t : ℕ)
    (z : RowVector (Sum Node {i : Node // i ≠ i0}))
    (hz : ∀ i : Node, z (Sum.inl i) = 0) :
    ∀ i : Node,
      matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda 0 i0 t) z (Sum.inl i) = 0 := by
  classical
  intro i
  simp [matrixMulVector, quadraticRestrictedOneStepMatrix, hz]

/-- At `alpha = 0`, every finite restricted noise innovation accumulated over a
window has zero primal coordinates.  This is the finite-window version of the
Appendix C.1 block channel `N_t(0)`. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_alpha_zero_top
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (start : ℕ) :
    ∀ n : ℕ, ∀ i : Node,
      quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda 0 i0 noise start n (Sum.inl i) = 0 := by
  classical
  intro n
  induction n with
  | zero =>
      intro i
      simp [quadraticRestrictedConsecutiveNoiseInnovationCoord]
  | succ n ih =>
      intro i
      have hprop :
          matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedOneStepMatrix (Node := Node)
                quad lambda 0 i0 (start + n))
              (quadraticRestrictedConsecutiveNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise start n)
              (Sum.inl i) = 0 :=
        quadraticRestrictedOneStepMatrix_alpha_zero_top_apply_of_top_zero
          (Node := Node) quad lambda i0 (start + n)
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda 0 i0 noise start n) ih i
      have hnoise :
          quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad 0 i0 noise (start + n) (Sum.inl i) = 0 :=
        quadraticRestrictedNoiseInnovationCoord_alpha_zero_top
          (Node := Node) quad i0 noise (start + n) i
      simp [quadraticRestrictedConsecutiveNoiseInnovationCoord, hprop, hnoise]

/-- Consecutive-product form of the true restricted noisy quadratic dynamics.

This is Appendix C.1 step 1 after iterating the already-proved one-step
coordinate recurrence: the state at `start+n` is the homogeneous product
applied to the boundary state, plus the finite Duhamel noise innovation over
the same window. -/
theorem quadraticRestrictedConsecutiveProduct_affine_process_action
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (start : ℕ) :
    ∀ n : ℕ,
      let stepped := quad.withStepsize alpha
      restrictedStateToCoord (Node := Node) i0
          (stepped.primalState noise (start + n),
            stepped.trackerErrorZeroSum noise (start + n)) =
        matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
              (fun t => quadraticRestrictedOneStepMatrix
                (Node := Node) quad lambda alpha i0 t) start n)
            (restrictedStateToCoord (Node := Node) i0
              (stepped.primalState noise start,
                stepped.trackerErrorZeroSum noise start)) +
          quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start n := by
  classical
  intro n
  let stepped := quad.withStepsize alpha
  let step : ℕ → Matrix (Sum Node {i : Node // i ≠ i0})
      (Sum Node {i : Node // i ≠ i0}) ℝ :=
    fun t => quadraticRestrictedOneStepMatrix
      (Node := Node) quad lambda alpha i0 t
  have hproduct :
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          step start n =
        FiniteNetwork.consecutiveProduct step start n := by
    induction n with
    | zero =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        unfold identityMatrix
        funext u v
        by_cases h : u = v
        · subst v
          simp [Matrix.one_apply]
        · have h' : v ≠ u := Ne.symm h
          simp [Matrix.one_apply, h, h']
    | succ n ih =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        rw [ih]
        unfold matrixMul
        funext u v
        exact (Matrix.mul_apply
          (M := step (start + n))
          (N := FiniteNetwork.consecutiveProduct step start n)
          (i := u) (k := v)).symm
  have hmulVec
      (M : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
      (x : RowVector (Sum Node {i : Node // i ≠ i0})) :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) M x =
        Matrix.mulVec M x := by
    rfl
  rw [hproduct]
  simpa [hmulVec, step] using
    (affineRecurrence_window_unroll
      (A := step)
      (z := fun t => restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise t, stepped.trackerErrorZeroSum noise t))
      (b := fun t => quadraticRestrictedNoiseInnovationCoord
        (Node := Node) quad alpha i0 noise t)
      (acc := quadraticRestrictedConsecutiveNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise start)
      (start := start) (n := n)
      (by
        intro k _hk
        simpa [stepped] using
          quadraticRestrictedOneStepMatrix_affine_process_action
            (Node := Node) quad lambda alpha i0 hquad noise (start + k))
      (by simp [quadraticRestrictedConsecutiveNoiseInnovationCoord])
      (by
        intro k _hk
        simp [quadraticRestrictedConsecutiveNoiseInnovationCoord,
          hmulVec, step]))

/-- Iterates of the deterministic homogeneous restricted C.1 dynamics from a
given start phase. -/
noncomputable def quadraticRestrictedHomogeneousOrbit
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (start : ℕ) :
    ℕ → (State Node ℝ × ZeroSumState Node ℝ) →
      (State Node ℝ × ZeroSumState Node ℝ)
  | 0, S => S
  | n + 1, S =>
      quadraticRestrictedHomogeneousStep (Node := Node)
        quad lambda alpha (start + n)
        (quadraticRestrictedHomogeneousOrbit
          quad lambda alpha start n S)

/-- Tracker-only alpha-zero restricted orbits are exactly the original pull
product on the zero-sum tracker state.

This is the bottom diagonal block of the Appendix C.1 block triangular period
map, stated at the dynamics level so the remaining spectral leaves can use the
source contraction estimate on `pullLiftProduct` rather than a coordinate
surrogate. -/
theorem quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
    (quad : Setup Node ℝ) (lambda : ℝ) (start : ℕ) :
    ∀ (n : ℕ) (W : ZeroSumState Node ℝ),
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 start n ((fun _ : Node => (0 : ℝ)), W) =
        ((fun _ : Node => (0 : ℝ)),
          ⟨leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct start n) W.1,
            quad.pullLiftProduct_leftMul_zeroSum start n W⟩) := by
  classical
  intro n
  induction n with
  | zero =>
      intro W
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        funext i
        simp [quadraticRestrictedHomogeneousOrbit, pullLiftProduct,
          leftMul, identityMatrix]
  | succ n ih =>
      intro W
      simp [quadraticRestrictedHomogeneousOrbit, ih]
      have hzero_innovation :
          leftMul (Node := Node) (E := ℝ)
              (matrixSub (Node := Node) (quad.C (start + n))
                (identityMatrix (Node := Node)))
              (fun _ : Node => (0 : ℝ)) =
            fun _ : Node => (0 : ℝ) := by
        funext i
        simp [leftMul, matrixSub]
      apply Prod.ext
      · funext i
        simp [quadraticRestrictedHomogeneousStep, leftMul,
          matrixSub, identityMatrix, smul_eq_mul, hzero_innovation]
      · apply Subtype.ext
        funext i
        simp [quadraticRestrictedHomogeneousStep, matrixSub,
          identityMatrix, leftMul_matrixMul, pullLiftProduct, smul_eq_mul,
          hzero_innovation]

/-- Consecutive products of the restricted one-step matrices represent the
homogeneous restricted dynamics in canonical coordinates. -/
theorem quadraticRestrictedConsecutiveProduct_represents_orbit
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) (start : ℕ) :
    ∀ (n : ℕ) (S : State Node ℝ × ZeroSumState Node ℝ),
      matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun t => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 t) start n)
          (restrictedStateToCoord (Node := Node) i0 S) =
        restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit
            (Node := Node) quad lambda alpha start n S) := by
  classical
  intro n
  induction n with
  | zero =>
      intro S
      funext a
      simp [consecutiveProduct, quadraticRestrictedHomogeneousOrbit,
        matrixMulVector, identityMatrix]
  | succ n ih =>
      intro S
      simp [consecutiveProduct, quadraticRestrictedHomogeneousOrbit]
      rw [matrixMulVector_matrixMul]
      rw [ih]
      exact
        quadraticRestrictedOneStepMatrix_action
          (Node := Node) quad lambda alpha i0 (start + n)
          (quadraticRestrictedHomogeneousOrbit
            quad lambda alpha start n S)

/-- The one-period restricted matrix is the true phase-zero homogeneous
period propagator in canonical coordinates. -/
theorem quadraticRestrictedPeriodMatrix_represents_period
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        (restrictedStateToCoord (Node := Node) i0 S) =
      restrictedStateToCoord (Node := Node) i0
        (quadraticRestrictedHomogeneousOrbit
          quad lambda alpha 0 quad.period S) := by
  classical
  simpa [quadraticRestrictedPeriodMatrix] using
    quadraticRestrictedConsecutiveProduct_represents_orbit
      (Node := Node) quad lambda alpha i0 0 quad.period S

/-- Each entry of the restricted C.1 one-step matrix is affine in `alpha`. -/
theorem quadraticRestrictedOneStepMatrix_analyticAt
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (t : ℕ)
    (alphaBase : ℝ) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        quadraticRestrictedOneStepMatrix (Node := Node)
          quad lambda alpha i0 t) alphaBase := by
  classical
  apply AnalyticAt.pi
  intro a
  apply AnalyticAt.pi
  intro b
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          by_cases hij : i = j
          · simp [quadraticRestrictedOneStepMatrix, identityMatrix, hij]
            fun_prop
          · simp [quadraticRestrictedOneStepMatrix, identityMatrix, hij]
            fun_prop
      | inr j =>
          by_cases hi0 : i = i0
          · simp [quadraticRestrictedOneStepMatrix,
              restrictedTrackerCoordCoeff, hi0]
            fun_prop
          · by_cases hij : i = j.1
            · simp [quadraticRestrictedOneStepMatrix,
                restrictedTrackerCoordCoeff, hi0, hij, j.2]
              fun_prop
            · simp [quadraticRestrictedOneStepMatrix,
                restrictedTrackerCoordCoeff, hi0, hij, j.2]
              fun_prop
  | inr i =>
      cases b with
      | inl j =>
          by_cases hij : i.1 = j
          · simp [quadraticRestrictedOneStepMatrix, identityMatrix, hij]
            fun_prop
          · simp [quadraticRestrictedOneStepMatrix, identityMatrix, hij]
            fun_prop
      | inr j =>
          simp [quadraticRestrictedOneStepMatrix]
          fun_prop

/-- Finite products of the restricted C.1 one-step matrices remain analytic
entrywise. -/
theorem quadraticRestrictedConsecutiveProduct_analyticAt
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alphaBase : ℝ) :
    ∀ n : ℕ,
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun t => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 t) 0 n) alphaBase := by
  classical
  intro n
  induction n with
  | zero =>
      apply AnalyticAt.pi
      intro a
      apply AnalyticAt.pi
      intro b
      simp [consecutiveProduct, identityMatrix]
      fun_prop
  | succ n ih =>
      apply AnalyticAt.pi
      intro a
      apply AnalyticAt.pi
      intro c
      change AnalyticAt ℝ
        (fun alpha : ℝ =>
          matrixMul (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 (0 + n))
            (consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
              (fun t => quadraticRestrictedOneStepMatrix
                (Node := Node) quad lambda alpha i0 t) 0 n) a c)
        alphaBase
      unfold matrixMul
      apply Finset.analyticAt_fun_sum
      intro b _hb
      exact
        ((analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (quadraticRestrictedOneStepMatrix_analyticAt
              (Node := Node) quad lambda i0 (0 + n) alphaBase) a) b).mul
          (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp ih b) c))

/-- Finite restricted C.1 products from any start phase are analytic
entrywise. -/
theorem quadraticRestrictedConsecutiveProduct_analyticAt_start
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alphaBase : ℝ) (start : ℕ) :
    ∀ n : ℕ,
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun t => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 t) start n) alphaBase := by
  classical
  intro n
  induction n with
  | zero =>
      unfold consecutiveProduct
      convert (List.analyticAt_matrix_map_prod
          (K := ℝ) (E := ℝ) (R := ℝ)
          (ι := Sum Node {i : Node // i ≠ i0}) [] alphaBase (by simp)) using 1
      funext alpha a b
      simp [identityMatrix, Matrix.one_apply]
  | succ n ih =>
      simpa [consecutiveProduct, matrixMul] using
        (List.analyticAt_matrix_map_prod
          (K := ℝ) (E := ℝ) (R := ℝ)
          (ι := Sum Node {i : Node // i ≠ i0})
          [fun alpha : ℝ => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 (start + n),
            fun alpha : ℝ => consecutiveProduct
              (Node := Sum Node {i : Node // i ≠ i0})
              (fun t => quadraticRestrictedOneStepMatrix
                (Node := Node) quad lambda alpha i0 t) start n]
          alphaBase (by
            intro f hf
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
            rcases hf with rfl | rfl
            · exact quadraticRestrictedOneStepMatrix_analyticAt
                (Node := Node) quad lambda i0 (start + n) alphaBase
            · exact ih))

/-- The restricted C.1 period propagator is a real-analytic matrix family near
zero, as required by Lemma A.1. -/
theorem quadraticRestrictedPeriodMatrix_analytic_near_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) :
    RealAnalyticMatrixFamilyNear
      (Node := Sum Node {i : Node // i ≠ i0})
      (fun alpha : ℝ =>
        quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0) 1 := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro alpha _halpha
  simpa [quadraticRestrictedPeriodMatrix] using
    quadraticRestrictedConsecutiveProduct_analyticAt
      (Node := Node) quad lambda i0 alpha quad.period

/-- Alpha-zero block-entry sanity check for the restricted C.1 one-step
matrix: the primal-to-tracker forcing and tracker transport remain, but the
top-right tracker-to-primal block vanishes at `alpha = 0`. -/
theorem quadraticRestrictedOneStepMatrix_alpha_zero_top_right
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (t : ℕ)
    (i : Node) (j : {i : Node // i ≠ i0}) :
    quadraticRestrictedOneStepMatrix (Node := Node) quad lambda 0 i0 t
        (Sum.inl i) (Sum.inr j) = 0 := by
  simp [quadraticRestrictedOneStepMatrix]

/-- Alpha-zero top-left block of the restricted C.1 one-step matrix is the
push matrix of the original network. -/
theorem quadraticRestrictedOneStepMatrix_alpha_zero_top_left
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (t : ℕ)
    (i j : Node) :
    quadraticRestrictedOneStepMatrix (Node := Node) quad lambda 0 i0 t
        (Sum.inl i) (Sum.inl j) = quad.R t i j := by
  simp [quadraticRestrictedOneStepMatrix]

/-- Alpha-zero bottom-right block of the restricted C.1 one-step matrix is the
pull action on free zero-sum coordinates after eliminating the base node. -/
theorem quadraticRestrictedOneStepMatrix_alpha_zero_bottom_right
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (t : ℕ)
    (i j : {i : Node // i ≠ i0}) :
    quadraticRestrictedOneStepMatrix (Node := Node) quad lambda 0 i0 t
        (Sum.inr i) (Sum.inr j) =
      quad.C t i.1 j.1 - quad.C t i.1 i0 := by
  simp [quadraticRestrictedOneStepMatrix]

/-- Alpha-zero restricted products are block lower triangular: a tracker
coordinate cannot feed back into a primal coordinate over any finite window.

This is the concrete C.1 block-form fact used by the unit left eigenvector
and stable-spectrum arguments for the true restricted period matrix. -/
theorem quadraticRestrictedConsecutiveProduct_alpha_zero_top_right
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (start : ℕ) :
    ∀ (n : ℕ) (i : Node) (j : {i : Node // i ≠ i0}),
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          (fun t => quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda 0 i0 t) start n
          (Sum.inl i) (Sum.inr j) = 0 := by
  classical
  intro n i j
  let step : ℕ →
      _root_.Matrix (Sum Node {i : Node // i ≠ i0})
        (Sum Node {i : Node // i ≠ i0}) ℝ :=
    fun t => quadraticRestrictedOneStepMatrix
      (Node := Node) quad lambda 0 i0 t
  have hproduct :
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          step start n =
        FiniteNetwork.consecutiveProduct step start n := by
    induction n with
    | zero =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        unfold identityMatrix
        funext u v
        by_cases h : u = v <;> simp [Matrix.one_apply, h]
    | succ n ih =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        rw [ih]
        unfold matrixMul
        funext u v
        change
          (∑ k, step (start + n) u k *
            FiniteNetwork.consecutiveProduct step start n k v) =
          ∑ k, step (start + n) u k *
            FiniteNetwork.consecutiveProduct step start n k v
        rfl
  rw [show (fun t => quadraticRestrictedOneStepMatrix
      (Node := Node) quad lambda 0 i0 t) = step by rfl, hproduct]
  simpa [Matrix.toBlocks₁₂] using
    congrFun (congrFun
      (FiniteNetwork.consecutiveMatrixProduct_toBlocks_of_upperRight_eq_zero
        step start n
        (fun s _hs => by
          ext a b
          simp [step, Matrix.toBlocks₁₂,
            quadraticRestrictedOneStepMatrix])) i) j

/-- Alpha-zero restricted products have the original push product as their
top-left diagonal block.

Together with `quadraticRestrictedConsecutiveProduct_alpha_zero_top_right`,
this is the concrete block-lower-triangular structure of the Appendix C.1
period propagator. -/
theorem quadraticRestrictedConsecutiveProduct_alpha_zero_top_left
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) (start : ℕ) :
    ∀ (n : ℕ) (i j : Node),
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          (fun t => quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda 0 i0 t) start n
          (Sum.inl i) (Sum.inl j) =
        quad.pushLiftProduct start n i j := by
  classical
  intro n
  induction n with
  | zero =>
      intro i j
      simp [consecutiveProduct, pushLiftProduct, identityMatrix]
  | succ n ih =>
      intro i j
      simp [consecutiveProduct, matrixMul]
      have hleft :
          (∑ k : Node,
            quadraticRestrictedOneStepMatrix (Node := Node)
                quad lambda 0 i0 (start + n) (Sum.inl i) (Sum.inl k) *
              consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
                (fun t => quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0 t) start n
                (Sum.inl k) (Sum.inl j)) =
          (∑ k : Node,
            quad.R (start + n) i k * quad.pushLiftProduct start n k j) := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [quadraticRestrictedOneStepMatrix_alpha_zero_top_left,
          ih k j]
      have hright :
          (∑ k : {i : Node // i ≠ i0},
            quadraticRestrictedOneStepMatrix (Node := Node)
                quad lambda 0 i0 (start + n) (Sum.inl i) (Sum.inr k) *
              consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
                (fun t => quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda 0 i0 t) start n
                (Sum.inr k) (Sum.inl j)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _hk
        simp [quadraticRestrictedOneStepMatrix]
      rw [hleft, hright]
      simp [pushLiftProduct, matrixMul]

/-- Period-map form of
`quadraticRestrictedConsecutiveProduct_alpha_zero_top_right`. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_top_right
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (i : Node) (j : {i : Node // i ≠ i0}) :
    quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
        (Sum.inl i) (Sum.inr j) = 0 := by
  classical
  simpa [quadraticRestrictedPeriodMatrix] using
    quadraticRestrictedConsecutiveProduct_alpha_zero_top_right
      (Node := Node) quad lambda i0 0 quad.period i j

/-- Period-map form of
`quadraticRestrictedConsecutiveProduct_alpha_zero_top_left`. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_top_left
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (i j : Node) :
    quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
        (Sum.inl i) (Sum.inl j) =
      quad.pushLiftProduct 0 quad.period i j := by
  classical
  simpa [quadraticRestrictedPeriodMatrix] using
    quadraticRestrictedConsecutiveProduct_alpha_zero_top_left
      (Node := Node) quad lambda i0 0 quad.period i j

/-- Complexified top-block eigen-equation for the alpha-zero restricted
period matrix.

This is the first algebraic step in both remaining spectral leaves: because
the alpha-zero restricted period map is block lower triangular with zero
top-right block, the primal component of any complex eigenvector is an
eigenvector of the push-product top block with the same multiplier. -/
theorem quadraticRestrictedPeriodMatrix_alpha_zero_complex_top_eigen_equation
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (gamma : ℂ) (v : ComplexRowVector (Sum Node {i : Node // i ≠ i0}))
    (hv :
      complexMatrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0) v =
        gamma • v) :
    complexMatrixMulVector (Node := Node)
        (quad.pushLiftProduct 0 quad.period)
        (fun i : Node => v (Sum.inl i)) =
      gamma • (fun i : Node => v (Sum.inl i)) := by
  classical
  simpa [complexMatrixMulVector, Matrix.toBlocks₁₁,
    quadraticRestrictedPeriodMatrix_alpha_zero_top_left] using
    (Matrix.mulVec_inl_eq_smul_of_upperRight_mulVec_eq_zero
      (A := fun a b =>
        ((quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda 0 i0 a b : ℝ) : ℂ)) gamma v
      (by
        ext i
        simp [Matrix.mulVec, Matrix.toBlocks₁₂,
          quadraticRestrictedPeriodMatrix_alpha_zero_top_right]) hv)

/-- Push products compose over adjacent windows.  This is the push analogue
of the imported `pullLiftProduct_add`, routed through the generic consecutive
product API already used by the source contraction proof. -/
theorem pushLiftProduct_add_source
    (quad : Setup Node ℝ) (t j k : ℕ) :
    quad.pushLiftProduct t (j + k) =
      matrixMul (Node := Node) (quad.pushLiftProduct (t + j) k)
        (quad.pushLiftProduct t j) := by
  classical
  rw [quad.pushLiftProduct_eq_consecutiveProduct t (j + k)]
  rw [quad.pushLiftProduct_eq_consecutiveProduct (t + j) k]
  rw [quad.pushLiftProduct_eq_consecutiveProduct t j]
  exact consecutiveProduct_add (Node := Node) quad.R t j k

/-- Periodicity of the start phase iterated to any multiple of the period. -/
theorem pushLiftProduct_periodic_start_mul
    (quad : Setup Node ℝ) (m j : ℕ) :
    quad.pushLiftProduct (m * quad.period) j =
      quad.pushLiftProduct 0 j := by
  classical
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        quad.pushLiftProduct ((m + 1) * quad.period) j =
            quad.pushLiftProduct (m * quad.period + quad.period) j := by
              rw [Nat.succ_mul]
        _ = quad.pushLiftProduct (m * quad.period) j := by
              rw [quad.pushLiftProduct_periodic_start]
        _ = quad.pushLiftProduct 0 j := ih

/-- A complex eigen-equation for a real matrix iterates through the custom
matrix-power API. -/
theorem complex_matrixPower_eigen_iterate
    (A : NodeMatrix Node) (gamma : ℂ) (v : ComplexRowVector Node)
    (hv : complexMatrixMulVector (Node := Node) A v = gamma • v) :
    ∀ m : ℕ,
      complexMatrixMulVector (Node := Node)
          (matrixPower (Node := Node) A m) v =
        gamma ^ m • v := by
  classical
  intro m
  induction m with
  | zero =>
      funext i
      simp [matrixPower, complexMatrixMulVector, identityMatrix]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _hb hb
        simp [hb.symm]
      · intro hi
        simp at hi
  | succ m ih =>
      calc
        complexMatrixMulVector (Node := Node)
            (matrixPower (Node := Node) A (m + 1)) v =
          complexMatrixMulVector (Node := Node)
            (matrixMul (Node := Node) (matrixPower (Node := Node) A m) A) v := by
            rfl
        _ =
          complexMatrixMulVector (Node := Node)
            (matrixPower (Node := Node) A m)
            (complexMatrixMulVector (Node := Node) A v) := by
            rw [complexMatrixMulVector_matrixMul_real]
        _ =
          complexMatrixMulVector (Node := Node)
            (matrixPower (Node := Node) A m)
            (gamma • v) := by
            rw [hv]
        _ = gamma ^ (m + 1) • v := by
            rw [complexMatrixMulVector_smul_vector, ih, smul_smul]
            simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- A complex eigen-equation for one push period iterates to every integer
number of periods. -/
theorem complex_pushLiftProduct_period_eigen_iterate
    (quad : Setup Node ℝ) (gamma : ℂ) (X : ComplexRowVector Node)
    (hX :
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 quad.period) X =
        gamma • X) :
    ∀ m : ℕ,
      complexMatrixMulVector (Node := Node)
          (quad.pushLiftProduct 0 (m * quad.period)) X =
        gamma ^ m • X := by
  classical
  intro m
  induction m with
  | zero =>
      funext i
      simp [pushLiftProduct, complexMatrixMulVector, identityMatrix]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _hb hb
        simp [hb.symm]
      · intro hi
        simp at hi
  | succ m ih =>
      calc
        complexMatrixMulVector (Node := Node)
            (quad.pushLiftProduct 0 ((m + 1) * quad.period)) X =
          complexMatrixMulVector (Node := Node)
            (quad.pushLiftProduct 0 (m * quad.period + quad.period)) X := by
            rw [Nat.succ_mul]
        _ =
          complexMatrixMulVector (Node := Node)
            (matrixMul (Node := Node)
              (quad.pushLiftProduct (0 + m * quad.period) quad.period)
              (quad.pushLiftProduct 0 (m * quad.period))) X := by
            rw [pushLiftProduct_add_source]
        _ =
          complexMatrixMulVector (Node := Node)
            (quad.pushLiftProduct (m * quad.period) quad.period)
            (complexMatrixMulVector (Node := Node)
              (quad.pushLiftProduct 0 (m * quad.period)) X) := by
            rw [complexMatrixMulVector_matrixMul_real]
            simp
        _ =
          complexMatrixMulVector (Node := Node)
            (quad.pushLiftProduct 0 quad.period)
            (gamma ^ m • X) := by
            rw [ih]
            rw [pushLiftProduct_periodic_start_mul]
        _ = gamma ^ (m + 1) • X := by
            rw [complexMatrixMulVector_smul_vector, hX, smul_smul]
            simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- The file's right-recursive matrix powers commute with one more copy of
the same matrix. -/
theorem matrixPower_mul_self_comm
    (A : NodeMatrix Node) :
    ∀ m : ℕ,
      matrixMul (Node := Node) (matrixPower (Node := Node) A m) A =
        matrixMul (Node := Node) A (matrixPower (Node := Node) A m) := by
  classical
  intro m
  induction m with
  | zero =>
      simp [matrixPower, matrixMul_identity_left, matrixMul_identity_right]
  | succ m ih =>
      calc
        matrixMul (Node := Node) (matrixPower (Node := Node) A (m + 1)) A =
            matrixMul (Node := Node)
              (matrixMul (Node := Node) (matrixPower (Node := Node) A m) A) A := by
              rfl
        _ =
            matrixMul (Node := Node)
              (matrixMul (Node := Node) A (matrixPower (Node := Node) A m)) A := by
              rw [ih]
        _ =
            matrixMul (Node := Node) A
              (matrixMul (Node := Node) (matrixPower (Node := Node) A m) A) := by
              rw [matrixMul_assoc_local]
        _ =
            matrixMul (Node := Node) A
              (matrixPower (Node := Node) A (m + 1)) := by
              rfl

/-- The restricted one-step C.1 matrix inherits the network period. -/
theorem quadraticRestrictedOneStepMatrix_periodic
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) (t : ℕ) :
    quadraticRestrictedOneStepMatrix (Node := Node) quad lambda alpha i0
        (t + quad.period) =
      quadraticRestrictedOneStepMatrix (Node := Node) quad lambda alpha i0 t := by
  classical
  funext a b
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          simp [quadraticRestrictedOneStepMatrix, quad.R_periodic t]
      | inr j =>
          simp [quadraticRestrictedOneStepMatrix]
  | inr i =>
      cases b with
      | inl j =>
          simp [quadraticRestrictedOneStepMatrix, quad.C_periodic t]
      | inr j =>
          simp [quadraticRestrictedOneStepMatrix, quad.C_periodic t]

/-- Restricted consecutive products are periodic in the start phase. -/
theorem quadraticRestrictedConsecutiveProduct_periodic_start
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (t j : ℕ) :
    consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun s => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 s) (t + quad.period) j =
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun s => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 s) t j := by
  classical
  induction j with
  | zero =>
      simp [consecutiveProduct]
  | succ j ih =>
      simp [consecutiveProduct]
      rw [ih]
      rw [show t + quad.period + j = t + j + quad.period by omega]
      rw [quadraticRestrictedOneStepMatrix_periodic]

/-- Restricted consecutive products started at an integer number of periods
agree with phase-zero products. -/
theorem quadraticRestrictedConsecutiveProduct_periodic_start_mul
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (m j : ℕ) :
    consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun s => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 s) (m * quad.period) j =
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun s => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 s) 0 j := by
  classical
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s)
            ((m + 1) * quad.period) j =
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s)
            (m * quad.period + quad.period) j := by
              rw [Nat.succ_mul]
        _ =
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s)
            (m * quad.period) j := by
              rw [quadraticRestrictedConsecutiveProduct_periodic_start]
        _ =
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s) 0 j := ih

/-- Restricted consecutive products started at a block boundary depend only on
the within-period phase. -/
theorem quadraticRestrictedConsecutiveProduct_blockStart_add
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (k start j : ℕ) :
    consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun s => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 s)
        (quad.blockStart k + start) j =
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
        (fun s => quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 s) start j := by
  classical
  induction k with
  | zero =>
      simp [Setup.blockStart]
  | succ k ih =>
      calc
        consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s)
            (quad.blockStart (k + 1) + start) j =
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s)
            ((quad.blockStart k + start) + quad.period) j := by
              congr 1
              unfold Setup.blockStart
              rw [Nat.succ_mul]
              omega
        _ =
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s)
            (quad.blockStart k + start) j := by
              rw [quadraticRestrictedConsecutiveProduct_periodic_start]
        _ =
          consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
            (fun s => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 s) start j := ih

/-- Powers of the restricted period matrix are the restricted one-step product
over the corresponding number of complete periods. -/
theorem quadraticRestrictedPeriodMatrix_power_eq_consecutiveProduct
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) :
    ∀ m : ℕ,
      matrixPower (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0) m =
        consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          (fun s => quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0 s) 0
          (m * quad.period) := by
  classical
  intro m
  let localMonoid : Monoid (NodeMatrix (Sum Node {i : Node // i ≠ i0})) := {
    one := identityMatrix (Node := Sum Node {i : Node // i ≠ i0})
    mul := matrixMul (Node := Sum Node {i : Node // i ≠ i0})
    one_mul := matrixMul_identity_left (Node := Sum Node {i : Node // i ≠ i0})
    mul_one := matrixMul_identity_right (Node := Sum Node {i : Node // i ≠ i0})
    mul_assoc := fun A B C =>
      (matrixMul_assoc_local (Node := Sum Node {i : Node // i ≠ i0}) A B C).symm
    npow := fun n A => matrixPower (Node := Sum Node {i : Node // i ≠ i0}) A n
    npow_zero := fun _ => rfl
    npow_succ := fun _ _ => rfl
  }
  have hproduct
      (A : Nat → NodeMatrix (Sum Node {i : Node // i ≠ i0})) :
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0}) A =
        FiniteNetwork.consecutiveProduct A := by
    funext s n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [consecutiveProduct, FiniteNetwork.consecutiveProduct]
        exact congrArg (matrixMul (A (s + n))) ih
  rw [quadraticRestrictedPeriodMatrix, hproduct]
  exact
    (@FiniteNetwork.periodProduct_pow_eq_consecutiveProduct
      (NodeMatrix (Sum Node {i : Node // i ≠ i0})) localMonoid
      (A := fun s => quadraticRestrictedOneStepMatrix
        (Node := Node) quad lambda alpha i0 s)
      (p := quad.period) (m := m)
      (quadraticRestrictedOneStepMatrix_periodic
        (Node := Node) quad lambda alpha i0))

/-- Powers of the restricted period matrix represent the true homogeneous
restricted orbit over complete periods. -/
theorem quadraticRestrictedPeriodMatrix_power_represents_period_orbit
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (m : ℕ) (S : State Node ℝ × ZeroSumState Node ℝ) :
    matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
        (matrixPower (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0) m)
        (restrictedStateToCoord (Node := Node) i0 S) =
      restrictedStateToCoord (Node := Node) i0
        (quadraticRestrictedHomogeneousOrbit
          (Node := Node) quad lambda alpha 0 (m * quad.period) S) := by
  classical
  rw [quadraticRestrictedPeriodMatrix_power_eq_consecutiveProduct]
  exact
    quadraticRestrictedConsecutiveProduct_represents_orbit
      (Node := Node) quad lambda alpha i0 0 (m * quad.period) S

/-- Period-boundary inhomogeneous innovation for the restricted C.1 system. -/
noncomputable def quadraticRestrictedPeriodNoiseInnovationCoord
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    RowVector (Sum Node {i : Node // i ≠ i0}) :=
  quadraticRestrictedConsecutiveNoiseInnovationCoord
    (Node := Node) quad lambda alpha i0 noise (k * quad.period) quad.period

/-- One restricted C.1 noise-channel coordinate is square-integrable under the
source exact-variance oracle law. -/
theorem quadraticRestrictedNoiseInnovationCoord_coordinate_memLp
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (t : ℕ) :
    ∀ a : Sum Node {i : Node // i ≠ i0},
      MemLp
        (fun ω =>
          quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 (oracle.noise ω) t a) 2 μ := by
  classical
  intro a
  cases a with
  | inl i =>
      simpa [quadraticRestrictedNoiseInnovationCoord, restrictedStateToCoord]
        using
          (quad.nodeNoise_memLp_two μ oracle hnoise.1 t i).const_smul
            (-alpha)
  | inr i =>
      simpa [quadraticRestrictedNoiseInnovationCoord, restrictedStateToCoord]
        using
          quad.leftMul_noise_coordinate_memLp μ oracle hnoise.1
            (matrixSub (Node := Node) (quad.C t)
              (identityMatrix (Node := Node))) t i.1

/-- Exact one-step second moment for the canonical restricted C.1 noise
channel.

This is the local vector analogue of
`sameTime_weightedNoise_secondMoment_eq_exact`: after exposing the source
coefficient rows of `N_t(alpha)`, the exact iid variance law diagonalizes each
restricted coordinate. -/
theorem quadraticRestrictedNoiseInnovationCoord_secondMoment_eq_coeffSum
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (t : ℕ) :
    (∫ ω,
      rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 (oracle.noise ω) t) ^ 2 ∂μ) =
      (∑ a : Sum Node {i : Node // i ≠ i0},
        rowNormSq (Node := Node)
          (quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t a) * quad.sigma ^ 2) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  simpa only [rowEuclideanNorm_sq_eq_rowNormSq, rowNormSq,
      SOptLib.dependentProductNormSq_def, Matrix.mulVec,
      quadraticRestrictedNoiseInnovationCoord_eq_weightedCoeff,
      weightedState, Real.norm_eq_abs, sq_abs, Finset.sum_mul, Idx] using
    (integral_pi_norm_sq_matrix_mulVec_eq_sum_row_sq_mul_of_cross_zero
      (Omega := Ω) (I := Idx) (J := Node) μ
      (fun a j => quadraticRestrictedNoiseInnovationCoeff
        (Node := Node) quad alpha i0 t a j)
      (fun j ω => oracle.noise ω t j) (fun _ => quad.sigma ^ 2)
      (fun j =>
        (quad.nodeNoise_memLp_two μ oracle hnoise.1 t j).aestronglyMeasurable)
      (fun j =>
        SOptLib.exactVarianceIidCenteredFamily.integrable_sq_norm hnoise.2 t j)
      (fun j k hjk =>
        quad.sameTime_distinctNode_inner_integral_eq_zero
          μ oracle hnoise.1 t j k hjk)
      (fun j => hnoise.2.2.2.2.2 t j))

/-- Uniform one-step second-moment bound for the restricted C.1 noise channel
on a bounded stepsize interval.

The proof uses the exact iid variance identity above and only elementary
stochastic-matrix entry bounds.  It is the source stochastic input needed for
the finite-period innovation recursion. -/
theorem quadraticRestrictedNoiseInnovationCoord_secondMoment_uniform_bound
    (quad : Setup Node ℝ) (alpha0 : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ Ceta : ℝ, 0 ≤ Ceta ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ t : ℕ,
          (∫ ω,
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 (oracle.noise ω) t) ^ 2 ∂μ) ≤
            Ceta := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let M : ℝ := alpha0 + 2
  let Ceta : ℝ :=
    (Fintype.card Idx : ℝ) *
      ((nodeCount (Node := Node) : ℝ) * M ^ 2 * quad.sigma ^ 2)
  refine ⟨Ceta, ?_, ?_⟩
  · dsimp [Ceta, M]
    positivity
  intro alpha halpha_pos halpha_le t
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    linarith
  have htwo_le_M : (2 : ℝ) ≤ M := by
    dsimp [M]
    linarith
  have halpha_le_M : alpha ≤ M := by
    dsimp [M]
    linarith
  have hsigma_nonneg : 0 ≤ quad.sigma ^ 2 := sq_nonneg _
  have hcoeff_abs :
      ∀ a : Idx, ∀ j : Node,
        |quadraticRestrictedNoiseInnovationCoeff
          (Node := Node) quad alpha i0 t a j| ≤ M := by
    intro a j
    cases a with
    | inl i =>
        by_cases hij : i = j
        · simp [quadraticRestrictedNoiseInnovationCoeff, hij,
            abs_of_pos halpha_pos, halpha_le_M]
        · simp [quadraticRestrictedNoiseInnovationCoeff, hij, hM_nonneg]
    | inr i =>
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
        have habs :
            |quad.C t i.1 j - identityMatrix (Node := Node) i.1 j| ≤
              quad.C t i.1 j + identityMatrix (Node := Node) i.1 j := by
          refine abs_le.mpr ⟨?_, ?_⟩
          · nlinarith [hC_nonneg, hid_nonneg]
          · nlinarith [hC_nonneg, hid_nonneg]
        calc
          |quadraticRestrictedNoiseInnovationCoeff
              (Node := Node) quad alpha i0 t (Sum.inr i) j| =
              |quad.C t i.1 j - identityMatrix (Node := Node) i.1 j| := by
                simp [quadraticRestrictedNoiseInnovationCoeff]
          _ ≤ quad.C t i.1 j + identityMatrix (Node := Node) i.1 j := habs
          _ ≤ (2 : ℝ) := by linarith
          _ ≤ M := htwo_le_M
  have hrow_bound :
      ∀ a : Idx,
        rowNormSq (Node := Node)
          (quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t a) ≤
          (nodeCount (Node := Node) : ℝ) * M ^ 2 := by
    intro a
    unfold rowNormSq
    calc
      (∑ j : Node,
          (quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t a j) ^ 2) ≤
          ∑ _j : Node, M ^ 2 := by
            apply Finset.sum_le_sum
            intro j _hj
            have habs := hcoeff_abs a j
            have hsquare : |quadraticRestrictedNoiseInnovationCoeff
                (Node := Node) quad alpha i0 t a j| ^ 2 ≤ M ^ 2 :=
              (sq_le_sq₀ (abs_nonneg _) hM_nonneg).2 habs
            simpa [sq_abs] using hsquare
      _ = (nodeCount (Node := Node) : ℝ) * M ^ 2 := by
            simp [nodeCount]
  rw [quadraticRestrictedNoiseInnovationCoord_secondMoment_eq_coeffSum
    (Node := Node) quad alpha i0 μ oracle hnoise t]
  calc
    (∑ a : Idx,
        rowNormSq (Node := Node)
          (quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t a) * quad.sigma ^ 2) ≤
        ∑ _a : Idx,
          ((nodeCount (Node := Node) : ℝ) * M ^ 2) * quad.sigma ^ 2 := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_right (hrow_bound a) hsigma_nonneg
    _ = Ceta := by
          simp [Ceta, mul_assoc]

/-- Finite restricted period innovations inherit coordinatewise `L²` from the
finite collection of node-noise tables inside the period. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_coordinate_memLp
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (start n : ℕ) :
    ∀ a : Sum Node {i : Node // i ≠ i0},
      MemLp
        (fun ω =>
          quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 (oracle.noise ω) start n a)
          2 μ := by
  classical
  induction n with
  | zero =>
      intro a
      simpa [quadraticRestrictedConsecutiveNoiseInnovationCoord] using
        (memLp_const (0 : ℝ) : MemLp (fun _ : Ω => (0 : ℝ)) 2 μ)
  | succ n ih =>
      intro a
      have hpropagated :
          MemLp
            (fun ω =>
              matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (quadraticRestrictedOneStepMatrix (Node := Node)
                    quad lambda alpha i0 (start + n))
                  (quadraticRestrictedConsecutiveNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) start n) a) 2 μ := by
        unfold matrixMulVector
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (ih b).const_smul
          (quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda alpha i0 (start + n) a b)
      have hnew :
          MemLp
            (fun ω =>
              quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 (oracle.noise ω)
                (start + n) a) 2 μ :=
        quadraticRestrictedNoiseInnovationCoord_coordinate_memLp
          (Node := Node) quad alpha i0 μ oracle hnoise (start + n) a
      have hsum := hpropagated.add hnew
      refine MemLp.ae_eq ?_ hsum
      exact Filter.Eventually.of_forall fun ω => by
        simp [quadraticRestrictedConsecutiveNoiseInnovationCoord, Pi.add_apply]

/-- Deterministic norm recursion for a finite restricted C.1 innovation
window.

This is the finite-period propagation step left after the one-step stochastic
moment has been diagonalized by `ExactVarianceIidAdditiveNoise`: the accumulated
innovation at length `n+1` is the previous accumulated innovation propagated by
the next homogeneous one-step matrix plus the fresh one-step noise channel. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_succ_le
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (start n : ℕ) :
    rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise start (n + 1)) ≤
      matrixEuclideanOperatorNorm
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0 (start + n)) *
        rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start n) +
      rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 noise (start + n)) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let A : NodeMatrix Idx :=
    quadraticRestrictedOneStepMatrix
      (Node := Node) quad lambda alpha i0 (start + n)
  let y : RowVector Idx :=
    quadraticRestrictedConsecutiveNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 noise start n
  let eta : RowVector Idx :=
    quadraticRestrictedNoiseInnovationCoord
      (Node := Node) quad alpha i0 noise (start + n)
  calc
    rowEuclideanNorm (Node := Idx)
        (quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise start (n + 1)) =
        rowEuclideanNorm (Node := Idx)
          (matrixMulVector (Node := Idx) A y + eta) := by
          rfl
    _ ≤ rowEuclideanNorm (Node := Idx)
          (matrixMulVector (Node := Idx) A y) +
        rowEuclideanNorm (Node := Idx) eta :=
          rowEuclideanNorm_add_le (Node := Idx)
            (matrixMulVector (Node := Idx) A y) eta
    _ ≤ matrixEuclideanOperatorNorm (Node := Idx) A *
          rowEuclideanNorm (Node := Idx) y +
        rowEuclideanNorm (Node := Idx) eta := by
          exact add_le_add
            (rowEuclideanNorm_matrixMulVector_le (Node := Idx) A y)
            le_rfl

/-- Squared scalar form of the deterministic finite-period innovation
recursion.

The inequality `(a+b)^2 <= 2a^2+2b^2` is the algebraic bridge used to turn the
norm recursion into an `L²` induction. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_sq_succ_le
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (start n : ℕ) :
    rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise start (n + 1)) ^ 2 ≤
      2 *
        (matrixEuclideanOperatorNorm
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0 (start + n)) ^
          2 *
        rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start n) ^ 2) +
      2 *
        rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)) ^ 2 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let lhs : ℝ :=
    rowEuclideanNorm (Node := Idx)
      (quadraticRestrictedConsecutiveNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise start (n + 1))
  let a : ℝ :=
    matrixEuclideanOperatorNorm (Node := Idx)
      (quadraticRestrictedOneStepMatrix
        (Node := Node) quad lambda alpha i0 (start + n)) *
      rowEuclideanNorm (Node := Idx)
        (quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise start n)
  let b : ℝ :=
    rowEuclideanNorm (Node := Idx)
      (quadraticRestrictedNoiseInnovationCoord
        (Node := Node) quad alpha i0 noise (start + n))
  have hlhs_nonneg : 0 ≤ lhs := by
    dsimp [lhs]
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg
        (rowNormSq (Node := Idx)
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start (n + 1)))
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg
      ((matrixEuclideanOperatorNorm_spec
        (Node := Idx)
        (quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 (start + n))).1)
      (by
        simpa [rowEuclideanNorm] using
          Real.sqrt_nonneg
            (rowNormSq (Node := Idx)
              (quadraticRestrictedConsecutiveNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise start n)))
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg
        (rowNormSq (Node := Idx)
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)))
  have hle : lhs ≤ a + b := by
    simpa [lhs, a, b, Idx] using
      quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_succ_le
        (Node := Node) quad lambda alpha i0 noise start n
  have hsquare : lhs ^ 2 ≤ (a + b) ^ 2 :=
    (sq_le_sq₀ hlhs_nonneg (add_nonneg ha_nonneg hb_nonneg)).2 hle
  have habound : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  calc
    lhs ^ 2 ≤ (a + b) ^ 2 := hsquare
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := habound
    _ =
      2 *
        (matrixEuclideanOperatorNorm
          (Node := Idx)
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0 (start + n)) ^
          2 *
        rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start n) ^ 2) +
      2 *
        rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)) ^ 2 := by
          dsimp [a, b, Idx]
          ring

/-- Squared finite-window innovation recursion after applying a uniform
operator-norm bound to the one-step homogeneous matrix. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_sq_succ_le_of_operator_bound
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (start n : ℕ)
    {Mstep : ℝ}
    (hMstep_nonneg : 0 ≤ Mstep)
    (hstep_bound :
      matrixEuclideanOperatorNorm
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0 (start + n)) ≤ Mstep) :
    rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise start (n + 1)) ^ 2 ≤
      2 *
        (Mstep ^ 2 *
        rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start n) ^ 2) +
      2 *
        rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)) ^ 2 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let op : ℝ :=
    matrixEuclideanOperatorNorm (Node := Idx)
      (quadraticRestrictedOneStepMatrix
        (Node := Node) quad lambda alpha i0 (start + n))
  let ynorm : ℝ :=
    rowEuclideanNorm (Node := Idx)
      (quadraticRestrictedConsecutiveNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise start n)
  have hbase :=
    quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_sq_succ_le
      (Node := Node) quad lambda alpha i0 noise start n
  have hop_nonneg : 0 ≤ op := by
    dsimp [op]
    exact
      (matrixEuclideanOperatorNorm_spec
        (Node := Idx)
        (quadraticRestrictedOneStepMatrix
          (Node := Node) quad lambda alpha i0 (start + n))).1
  have hynorm_sq_nonneg : 0 ≤ ynorm ^ 2 := sq_nonneg ynorm
  have hop_sq_le : op ^ 2 ≤ Mstep ^ 2 :=
    (sq_le_sq₀ hop_nonneg hMstep_nonneg).2 (by
      simpa [op, Idx] using hstep_bound)
  have hterm :
      op ^ 2 * ynorm ^ 2 ≤ Mstep ^ 2 * ynorm ^ 2 :=
    mul_le_mul_of_nonneg_right hop_sq_le hynorm_sq_nonneg
  calc
    rowEuclideanNorm (Node := Idx)
        (quadraticRestrictedConsecutiveNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise start (n + 1)) ^ 2 ≤
      2 *
        (op ^ 2 * ynorm ^ 2) +
      2 *
        rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)) ^ 2 := by
          simpa [op, ynorm, Idx] using hbase
    _ ≤
      2 *
        (Mstep ^ 2 * ynorm ^ 2) +
      2 *
        rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)) ^ 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 2))
            le_rfl
    _ =
      2 *
        (Mstep ^ 2 *
        rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedConsecutiveNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise start n) ^ 2) +
      2 *
        rowEuclideanNorm (Node := Idx)
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + n)) ^ 2 := by
          simp [ynorm]

/-- Finite-length `L²` Gronwall bound for the restricted period innovation.

The constant depends only on the window length, the uniform homogeneous
operator bound, and the one-step innovation second-moment bound.  This is the
pure finite-induction part of Appendix C.1 step 5. -/
theorem finite_l2_recursion_uniform_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : ℕ) (Y Eta : ℕ → Ω → ℝ)
    {M Ceta : ℝ}
    (hM_nonneg : 0 ≤ M) (hCeta_nonneg : 0 ≤ Ceta)
    (hY0 : ∀ ω : Ω, Y 0 ω = 0)
    (hY_int : ∀ n : ℕ, n ≤ m → Integrable (fun ω => Y n ω) μ)
    (hEta_int : ∀ n : ℕ, n < m → Integrable (fun ω => Eta n ω) μ)
    (hEta_bound :
      ∀ n : ℕ, n < m → (∫ ω, Eta n ω ∂μ) ≤ Ceta)
    (hrec :
      ∀ n : ℕ, n < m → ∀ ω : Ω,
        Y (n + 1) ω ≤
          2 * (M ^ 2 * Y n ω) + 2 * Eta n ω) :
    ∀ n : ℕ, n ≤ m →
      (∫ ω, Y n ω ∂μ) ≤
        Finset.sum (Finset.range (m + 1)) (fun n =>
          Nat.rec 0 (fun _ prev => 2 * (M ^ 2 * prev) + 2 * Ceta) n) := by
  have hY0_integral : (∫ ω, Y 0 ω ∂μ) ≤ 0 := by
    have hconst : (fun ω : Ω => Y 0 ω) = fun _ : Ω => 0 := by
      funext ω
      exact hY0 ω
    simp [hconst]
  have hbound :=
    SOptLib.finite_horizon_integral_affine_recursion_le_majorant_sum
      (mu := μ) m Y Eta (2 * M ^ 2) 2 Ceta
      (mul_nonneg (by norm_num) (pow_nonneg hM_nonneg 2))
      (by norm_num) hCeta_nonneg hY0_integral hY_int hEta_int
      hEta_bound (fun n hn => Filter.Eventually.of_forall fun ω => by
        simpa [mul_assoc] using hrec n hn ω)
  intro n hn
  convert hbound n hn using 1
  apply Finset.sum_congr rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Nat.rec, ih]
      ring

/-- Period-window specialization of `finite_l2_recursion_uniform_bound` for
the canonical C.1 restricted innovation coordinates. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_period_l2_bound_of_uniform_step
    (quad : Setup Node ℝ) (lambda alphaBound : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    {Mstep Ceta : ℝ}
    (hMstep_nonneg : 0 ≤ Mstep) (hCeta_nonneg : 0 ≤ Ceta)
    (hstep_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBound →
        ∀ k n : ℕ, n < quad.period →
          matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0
              (k * quad.period + n)) ≤ Mstep)
    (heta_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBound →
        ∀ t : ℕ,
          (∫ ω,
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 (oracle.noise ω) t) ^ 2 ∂μ) ≤
            Ceta) :
    ∃ Cwin : ℝ, 0 ≤ Cwin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBound →
        ∀ k : ℕ,
          (∫ ω,
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedConsecutiveNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω)
                (k * quad.period) quad.period) ^ 2 ∂μ) ≤ Cwin := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let Dwin : ℕ → ℝ :=
    Nat.rec (motive := fun _ => ℝ) 0
      (fun _ prev => 2 * (Mstep ^ 2 * prev) + 2 * Ceta)
  let Cwin : ℝ :=
    Finset.sum (Finset.range (quad.period + 1)) (fun n => Dwin n)
  refine ⟨Cwin, ?_, ?_⟩
  · dsimp [Cwin]
    apply Finset.sum_nonneg
    intro n hn_range
    induction n with
    | zero =>
        dsimp [Dwin]
        norm_num
    | succ n ih =>
        have hn_range_prev : n ∈ Finset.range (quad.period + 1) := by
          exact Finset.mem_range.mpr
            (lt_trans (Nat.lt_succ_self n)
              (Finset.mem_range.mp hn_range))
        have hprev_nonneg :
            0 ≤ Dwin n :=
          ih hn_range_prev
        dsimp [Dwin]
        nlinarith [hCeta_nonneg, sq_nonneg Mstep, hprev_nonneg]
  intro alpha halpha_pos halpha_le k
  let Y : ℕ → Ω → ℝ := fun n ω =>
    rowEuclideanNorm (Node := Idx)
      (quadraticRestrictedConsecutiveNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 (oracle.noise ω)
        (k * quad.period) n) ^ 2
  let Eta : ℕ → Ω → ℝ := fun n ω =>
    rowEuclideanNorm (Node := Idx)
      (quadraticRestrictedNoiseInnovationCoord
        (Node := Node) quad alpha i0 (oracle.noise ω)
        (k * quad.period + n)) ^ 2
  have hY0 : ∀ ω : Ω, Y 0 ω = 0 := by
    intro ω
    simp [Y, quadraticRestrictedConsecutiveNoiseInnovationCoord,
      rowEuclideanNorm, rowNormSq]
  have hY_int :
      ∀ n : ℕ, n ≤ quad.period → Integrable (fun ω => Y n ω) μ := by
    intro n _hn
    dsimp [Y]
    exact
      rowEuclideanNorm_sq_integrable_of_coordinate_memLp
        (Node := Idx)
        (quadraticRestrictedConsecutiveNoiseInnovationCoord_coordinate_memLp
          (Node := Node) quad lambda alpha i0 μ oracle hnoise
          (k * quad.period) n)
  have hEta_int :
      ∀ n : ℕ, n < quad.period → Integrable (fun ω => Eta n ω) μ := by
    intro n _hn
    dsimp [Eta]
    exact
      rowEuclideanNorm_sq_integrable_of_coordinate_memLp
        (Node := Idx)
        (quadraticRestrictedNoiseInnovationCoord_coordinate_memLp
          (Node := Node) quad alpha i0 μ oracle hnoise
          (k * quad.period + n))
  have hEta_bound :
      ∀ n : ℕ, n < quad.period → (∫ ω, Eta n ω ∂μ) ≤ Ceta := by
    intro n _hn
    simpa [Eta, Idx] using
      heta_bound alpha halpha_pos halpha_le (k * quad.period + n)
  have hrec :
      ∀ n : ℕ, n < quad.period → ∀ ω : Ω,
        Y (n + 1) ω ≤
          2 * (Mstep ^ 2 * Y n ω) + 2 * Eta n ω := by
    intro n hn ω
    simpa [Y, Eta, Idx] using
      quadraticRestrictedConsecutiveNoiseInnovationCoord_norm_sq_succ_le_of_operator_bound
        (Node := Node) quad lambda alpha i0 (oracle.noise ω)
        (k * quad.period) n hMstep_nonneg
        (hstep_bound alpha halpha_pos halpha_le k n hn)
  have hC_bound :=
    finite_l2_recursion_uniform_bound
      (μ := μ) quad.period Y Eta hMstep_nonneg hCeta_nonneg
      hY0 hY_int hEta_int hEta_bound hrec
  simpa [Y, Cwin] using hC_bound quad.period le_rfl

/-- Period-boundary innovation coordinates are square-integrable. -/
theorem quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (k : ℕ) :
    ∀ a : Sum Node {i : Node // i ≠ i0},
      MemLp
        (fun ω =>
          quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 (oracle.noise ω) k a)
          2 μ := by
  classical
  simpa [quadraticRestrictedPeriodNoiseInnovationCoord] using
    quadraticRestrictedConsecutiveNoiseInnovationCoord_coordinate_memLp
      (Node := Node) quad lambda alpha i0 μ oracle hnoise
      (k * quad.period) quad.period

/-- Free-coordinate tracker reconstruction coefficients are uniformly bounded
by one. -/
theorem restrictedTrackerCoordCoeff_abs_le_one
    (i0 i : Node) (j : {j : Node // j ≠ i0}) :
    |restrictedTrackerCoordCoeff (Node := Node) i0 i j| ≤ (1 : ℝ) := by
  classical
  by_cases hi : i = i0
  · simp [restrictedTrackerCoordCoeff, hi]
  · by_cases hij : i = j.1
    · subst i
      simp [restrictedTrackerCoordCoeff, j.2]
    · simp [restrictedTrackerCoordCoeff, hi, hij]

/-- Uniform one-step homogeneous operator bound on a positive stepsize
interval.

The restricted one-step matrix is affine in `alpha`; the entries of `R_t` and
`C_t` are bounded by stochasticity, and the zero-sum reconstruction coefficients
are bounded by one. -/
theorem quadraticRestrictedOneStepMatrix_uniform_operator_bound_on_Icc
    (quad : Setup Node ℝ) (lambda alphaBound : ℝ) (i0 : Node)
    (halphaBound_pos : 0 < alphaBound) :
    ∃ Mstep : ℝ, 0 ≤ Mstep ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBound →
        ∀ k n : ℕ, n < quad.period →
          matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0
              (k * quad.period + n)) ≤ Mstep := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let B : ℝ := alphaBound * (|lambda| + 1) + 2 * |lambda| + 2
  let Mstep : ℝ :=
    (((nodeCount (Node := Idx) : ℝ) ^ 2) *
        Real.sqrt (nodeCount (Node := Idx) : ℝ)) * B
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Mstep, ?_, ?_⟩
  · dsimp [Mstep]
    positivity
  intro alpha halpha_pos halpha_le k n hn
  have halpha_nonneg : 0 ≤ alpha := halpha_pos.le
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
          (Node := Node) quad lambda alpha i0
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
            by_cases hij : i = j
            · subst j
              calc
                |quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda alpha i0
                    (k * quad.period + n) (Sum.inl i) (Sum.inl i)| =
                    |quad.R (k * quad.period + n) i i - alpha * lambda| := by
                      simp [quadraticRestrictedOneStepMatrix, identityMatrix]
                _ ≤ |quad.R (k * quad.period + n) i i| +
                      |alpha * lambda| := by
                      simpa [Real.norm_eq_abs] using
                        norm_sub_le (quad.R (k * quad.period + n) i i)
                          (alpha * lambda)
                _ ≤ 1 + alphaBound * |lambda| := by
                      rw [abs_of_nonneg hR_nonneg, abs_mul,
                        abs_of_nonneg halpha_nonneg]
                      nlinarith [hR_le, halpha_le, abs_nonneg lambda]
                _ ≤ B := by
                      dsimp [B]
                      nlinarith [halphaBound_pos.le, abs_nonneg lambda]
            · calc
                |quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda alpha i0
                    (k * quad.period + n) (Sum.inl i) (Sum.inl j)| =
                    |quad.R (k * quad.period + n) i j| := by
                      simp [quadraticRestrictedOneStepMatrix, identityMatrix, hij]
                _ ≤ 1 := by
                      rw [abs_of_nonneg hR_nonneg]
                      exact hR_le
                _ ≤ B := by
                      dsimp [B]
                      nlinarith [halphaBound_pos.le, abs_nonneg lambda]
        | inr j =>
            have hcoeff := restrictedTrackerCoordCoeff_abs_le_one
              (Node := Node) i0 i j
            calc
              |quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda alpha i0
                  (k * quad.period + n) (Sum.inl i) (Sum.inr j)| =
                  |alpha * restrictedTrackerCoordCoeff
                    (Node := Node) i0 i j| := by
                    simp [quadraticRestrictedOneStepMatrix, abs_neg, mul_comm]
              _ = alpha * |restrictedTrackerCoordCoeff
                    (Node := Node) i0 i j| := by
                    rw [abs_mul, abs_of_nonneg halpha_nonneg]
              _ ≤ alphaBound * 1 := by
                    exact mul_le_mul halpha_le hcoeff
                      (abs_nonneg _) halphaBound_pos.le
              _ ≤ B := by
                    dsimp [B]
                    nlinarith [halphaBound_pos.le, abs_nonneg lambda]
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
                  (Node := Node) quad lambda alpha i0
                  (k * quad.period + n) (Sum.inr i) (Sum.inl j)| =
                  |lambda| *
                    |quad.C (k * quad.period + n) i.1 j -
                      identityMatrix (Node := Node) i.1 j| := by
                    simp [quadraticRestrictedOneStepMatrix, abs_mul]
              _ ≤ |lambda| * 2 := by
                    exact mul_le_mul_of_nonneg_left habs (abs_nonneg lambda)
              _ ≤ B := by
                    dsimp [B]
                    nlinarith [halphaBound_pos.le, abs_nonneg lambda]
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
                  (Node := Node) quad lambda alpha i0
                  (k * quad.period + n) (Sum.inr i) (Sum.inr j)| =
                  |quad.C (k * quad.period + n) i.1 j.1 -
                    quad.C (k * quad.period + n) i.1 i0| := by
                    simp [quadraticRestrictedOneStepMatrix]
              _ ≤ 2 := habs
              _ ≤ B := by
                    dsimp [B]
                    nlinarith [halphaBound_pos.le, abs_nonneg lambda]
  simpa [Mstep, Idx] using
    matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound
      (Node := Idx)
      (quadraticRestrictedOneStepMatrix
        (Node := Node) quad lambda alpha i0 (k * quad.period + n))
      B hB_nonneg hentry

/-- A continuous matrix family has a uniform entrywise absolute bound on a
compact stepsize interval. -/
theorem matrixFamily_entries_uniform_abs_bound_on_Icc
    (P : ℝ → NodeMatrix Node) (alphaBound : ℝ)
    (hentry_cont :
      ∀ a b : Node, ContinuousOn (fun alpha : ℝ => P alpha a b)
        (Set.Icc (0 : ℝ) alphaBound)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ alpha : ℝ, alpha ∈ Set.Icc (0 : ℝ) alphaBound →
        ∀ a b : Node, |P alpha a b| ≤ B := by
  classical
  let C : Node × Node → ℝ := fun p =>
    Classical.choose
      (exists_nonneg_norm_bound_of_isCompact_of_continuousOn
        (fun alpha : ℝ => P alpha p.1 p.2)
        isCompact_Icc (hentry_cont p.1 p.2))
  have hC_spec :
      ∀ p : Node × Node, 0 ≤ C p ∧
        ∀ alpha : ℝ, alpha ∈ Set.Icc (0 : ℝ) alphaBound →
          ‖P alpha p.1 p.2‖ ≤ C p := by
    intro p
    dsimp [C]
    exact
      Classical.choose_spec
        (exists_nonneg_norm_bound_of_isCompact_of_continuousOn
          (fun alpha : ℝ => P alpha p.1 p.2)
          isCompact_Icc (hentry_cont p.1 p.2))
  let B : ℝ := ∑ p : Node × Node, C p
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    exact Finset.sum_nonneg (fun p _hp => (hC_spec p).1)
  intro alpha halpha a b
  let p : Node × Node := (a, b)
  have hCp_le_B : C p ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum
      (fun q _hq => (hC_spec q).1) (Finset.mem_univ p)
  have hbound := (hC_spec p).2 alpha halpha
  exact le_trans (by simpa [p, Real.norm_eq_abs] using hbound) hCp_le_B

/-- The alpha-zero period innovation has zero primal block.  This is the
complete-period form of Appendix C.1's block channel
`N_t(0) epsilon_t = (0,(C_t-I)epsilon_t)`. -/
theorem quadraticRestrictedPeriodNoiseInnovationCoord_alpha_zero_top
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (k : ℕ) (i : Node) :
    quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda 0 i0 noise k (Sum.inl i) = 0 := by
  simpa [quadraticRestrictedPeriodNoiseInnovationCoord] using
    quadraticRestrictedConsecutiveNoiseInnovationCoord_alpha_zero_top
      (Node := Node) quad lambda i0 noise (k * quad.period) quad.period i

/-- At the initial boundary, the alpha-zero restricted state is the common
primal initialization and zero tracker error.  This is the deterministic
`X_0 = 1 x_0`, `E_0 = 0` input used in Appendix C.1's stable cancellation. -/
theorem quadraticRestrictedInitialBoundaryCoord_alpha_zero
    (quad : Setup Node ℝ) (i0 : Node) (noise : NoisePath Node ℝ) :
    restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize 0).primalState noise 0,
          (quad.withStepsize 0).trackerErrorZeroSum noise 0) =
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

/-- Initial restricted boundary coordinates are square-integrable under the
source oracle law. -/
theorem quadraticRestrictedInitialBoundaryCoord_coordinate_memLp
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ a : Sum Node {i : Node // i ≠ i0},
      MemLp
        (fun ω =>
          restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
              (quad.withStepsize alpha).trackerErrorZeroSum
                (oracle.noise ω) 0) a) 2 μ := by
  classical
  let stepped := quad.withStepsize alpha
  have horacle_stepped :
      stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using hnoise.1
  intro a
  cases a with
  | inl i =>
      simpa [stepped, restrictedStateToCoord] using
        (stepped.generated_pushpull_coordinate_memLp μ oracle
          horacle_stepped 0).1 i
  | inr i =>
      have hsplit :=
        stepped.splitTrackerErrors_coordinate_memLp μ oracle
          horacle_stepped 0
      have hsum :
          MemLp
            (fun ω =>
              stepped.meanTrackerError (oracle.noise ω) 0 i.1 +
                stepped.noiseTrackerError (oracle.noise ω) 0 i.1) 2 μ :=
        (hsplit.1 i.1).add (hsplit.2 i.1)
      refine MemLp.ae_eq ?_ hsum
      exact Filter.Eventually.of_forall fun ω => by
        have hdecomp :=
          stepped.trackerErrorZeroSum_eq_mean_add_noise
            (oracle.noise ω) 0
        simpa [stepped, restrictedStateToCoord, Pi.add_apply] using
          (congrArg (fun W : ZeroSumState Node ℝ => W.1 i.1) hdecomp).symm

/-- Restricted boundary coordinates are square-integrable at every finite
time under the source oracle law. -/
theorem quadraticRestrictedBoundaryCoord_coordinate_memLp
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (t : ℕ) :
    ∀ a : Sum Node {i : Node // i ≠ i0},
      MemLp
        (fun ω =>
          restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState (oracle.noise ω) t,
              (quad.withStepsize alpha).trackerErrorZeroSum
                (oracle.noise ω) t) a) 2 μ := by
  classical
  let stepped := quad.withStepsize alpha
  have horacle_stepped :
      stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using hnoise.1
  intro a
  cases a with
  | inl i =>
      simpa [stepped, restrictedStateToCoord] using
        (stepped.generated_pushpull_coordinate_memLp μ oracle
          horacle_stepped t).1 i
  | inr i =>
      have hsplit :=
        stepped.splitTrackerErrors_coordinate_memLp μ oracle
          horacle_stepped t
      have hsum :
          MemLp
            (fun ω =>
              stepped.meanTrackerError (oracle.noise ω) t i.1 +
                stepped.noiseTrackerError (oracle.noise ω) t i.1) 2 μ :=
        (hsplit.1 i.1).add (hsplit.2 i.1)
      refine MemLp.ae_eq ?_ hsum
      exact Filter.Eventually.of_forall fun ω => by
        have hdecomp :=
          stepped.trackerErrorZeroSum_eq_mean_add_noise
            (oracle.noise ω) t
        simpa [stepped, restrictedStateToCoord, Pi.add_apply] using
          (congrArg (fun W : ZeroSumState Node ℝ => W.1 i.1) hdecomp).symm

/-- Appendix C.1 period-boundary AR recursion on the true restricted state.

At block boundaries, the homogeneous coefficient is the canonical restricted
one-period matrix used by the spectral splitting, and the inhomogeneous term is
the finite within-period Duhamel sum of noise channels. -/
theorem quadratic_restricted_period_inhomogeneous_recursion
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (noise : NoisePath Node ℝ) (k : ℕ) :
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
  classical
  let stepped := quad.withStepsize alpha
  let step : ℕ → NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
    fun t => quadraticRestrictedOneStepMatrix
      (Node := Node) quad lambda alpha i0 t
  have hwindow :=
    quadraticRestrictedConsecutiveProduct_affine_process_action
      (Node := Node) quad lambda alpha i0 hquad noise
      (k * quad.period) quad.period
  have hperiod :
      consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          step (k * quad.period) quad.period =
        quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0 := by
    simpa [step, quadraticRestrictedPeriodMatrix] using
      quadraticRestrictedConsecutiveProduct_periodic_start_mul
        (Node := Node) quad lambda alpha i0 k quad.period
  rw [show (k + 1) * quad.period = k * quad.period + quad.period by
    rw [Nat.succ_mul]]
  simpa [stepped, step, quadraticRestrictedPeriodNoiseInnovationCoord,
    hperiod] using hwindow

/-- Appendix C.1 stable-boundary deterministic square-sum bridge for the true
restricted period innovations.

This is the compiled source-sized bridge immediately before the stochastic
L2 step: once `ExactVarianceIidAdditiveNoise` controls the period-innovation
square sum, this theorem supplies the stable component's geometric budget. -/
theorem quadratic_restricted_stable_duhamel_square_sum_bound
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (F : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {K theta : ℝ}
    (hK : 0 ≤ K) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hpower :
      ∀ j : ℕ,
        matrixEuclideanOperatorNorm (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) F j) ≤
          K * theta ^ j)
    (noise : NoisePath Node ℝ) (z0 : RowVector (Sum Node {i : Node // i ≠ i0}))
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
      rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
        (stablePowerDuhamelClosedResponse
          (Node := Sum Node {i : Node // i ≠ i0}) F z0
          (fun k =>
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k) t) ^ 2) ≤
      (2 * K ^ 2 / (1 - theta ^ 2)) *
        (rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0}) z0) ^ 2 +
      (2 * K ^ 2 / (1 - theta) ^ 2) *
        Finset.sum (Finset.range N) (fun k =>
          (rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k)) ^ 2) := by
  classical
  exact
    stablePowerDuhamelClosedResponse_square_sum_le
      (Node := Sum Node {i : Node // i ≠ i0}) F z0
      (fun k =>
        quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise k)
      hK htheta_pos htheta_lt_one hpower N


/-- Uniform operator action bound for the stable projection complement
`I - P(alpha)` on a compact stepsize interval. -/
theorem spectralStableComplementVector_uniform_operator_bound_on_Icc
    (P : ℝ → NodeMatrix Node) (alphaBound : ℝ)
    (hentry_cont :
      ∀ a b : Node, ContinuousOn (fun alpha : ℝ => P alpha a b)
        (Set.Icc (0 : ℝ) alphaBound)) :
    ∃ Mproj : ℝ, 0 ≤ Mproj ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBound →
        ∀ z : RowVector Node,
          rowEuclideanNorm (Node := Node)
              ((1 - Matrix.mulVecLin (P alpha)) z) ^ 2 ≤
            Mproj ^ 2 * rowEuclideanNorm (Node := Node) z ^ 2 := by
  obtain ⟨Mproj, hMproj, hbound⟩ :=
    (Matrix.exists_uniform_one_sub_mulVec_norm_sq_bound_of_isCompact_of_entry_continuousOn
      (𝕜 := ℝ) (s := Set.Icc (0 : ℝ) alphaBound) (P := P) isCompact_Icc hentry_cont)
  refine ⟨Mproj, hMproj, fun alpha halpha_pos halpha_le z => ?_⟩
  simpa only [rowEuclideanNorm, rowNormSq, PiLp.norm_eq_of_L2,
    Real.norm_eq_abs, sq_abs] using
    hbound alpha ⟨halpha_pos.le, halpha_le⟩ z

/-- Appendix C.1 deterministic square-sum bridge for the projected stable
component.

This is the same geometric Duhamel estimate as
`quadratic_restricted_stable_duhamel_square_sum_bound`, but applied to the
canonical stable projection complement `(I-P(α))`.  It is the deterministic
input used before the iid period-innovation `L²` conversion. -/
theorem quadratic_restricted_projected_stable_duhamel_square_sum_bound
    (P F : NodeMatrix Node)
    {K theta : ℝ}
    (hK : 0 ≤ K) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hpower :
      ∀ j : ℕ,
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) F j) ≤
          K * theta ^ j)
    (z0 : RowVector Node) (xi : ℕ → RowVector Node) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
      rowEuclideanNorm (Node := Node)
        (stablePowerDuhamelClosedResponse (Node := Node) F
          ((1 - Matrix.mulVecLin P) z0)
          (fun k => (1 - Matrix.mulVecLin P) (xi k)) t) ^ 2) ≤
      (2 * K ^ 2 / (1 - theta ^ 2)) *
        (rowEuclideanNorm (Node := Node)
          ((1 - Matrix.mulVecLin P) z0)) ^ 2 +
      (2 * K ^ 2 / (1 - theta) ^ 2) *
        Finset.sum (Finset.range N) (fun k =>
          (rowEuclideanNorm (Node := Node)
            ((1 - Matrix.mulVecLin P) (xi k))) ^ 2) := by
  classical
  exact
    stablePowerDuhamelClosedResponse_square_sum_le
      (Node := Node) F
      ((1 - Matrix.mulVecLin P) z0)
      (fun k => (1 - Matrix.mulVecLin P) (xi k))
      hK htheta_pos htheta_lt_one hpower N

/-- Arithmetic-average output of a restricted C.1 coordinate vector.

The restricted coordinate carrier stores all primal coordinates on the `inl`
side and all non-base zero-sum tracker coordinates on the `inr` side.  This is
the canonical scalar output used when the stable component is projected back
to the paper's averaged primal iterate. -/
noncomputable def quadraticRestrictedPrimalAverageOutput
    (i0 : Node) (z : RowVector (Sum Node {i : Node // i ≠ i0})) : ℝ :=
  (nodeCount (Node := Node) : ℝ)⁻¹ *
    ∑ i : Node, z (Sum.inl i)

/-- The restricted coordinate output agrees with the true arithmetic average
of the primal state encoded in the restricted chart.

This is the block-boundary transport fact needed by the C.1 slow-recursion
comparison: once the full restricted state is related to its projected slow
and stable components, this lemma converts the coordinate statement back to
the paper's `averageIterate`. -/
theorem quadraticRestrictedPrimalAverageOutput_restrictedStateToCoord_eq_averageIterate
    (quad : Setup Node ℝ) (i0 : Node) (alpha : ℝ)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (restrictedStateToCoord (Node := Node) i0
          ((quad.withStepsize alpha).primalState noise t,
            (quad.withStepsize alpha).trackerErrorZeroSum noise t)) =
      (quad.withStepsize alpha).averageIterate noise t := by
  classical
  simp [quadraticRestrictedPrimalAverageOutput, restrictedStateToCoord,
    averageIterate, arithmeticAverage]

/-- A coordinate of a finite row vector is bounded by the custom Euclidean
row norm. -/
theorem rowVector_coordinate_abs_le_rowEuclideanNorm
    (z : RowVector Node) (i : Node) :
    |z i| ≤ rowEuclideanNorm (Node := Node) z := by
  classical
  have hsquare :
      |z i| ^ 2 ≤ rowNormSq (Node := Node) z := by
    unfold rowNormSq
    simpa [sq_abs] using
      Finset.single_le_sum
        (fun j _hj => sq_nonneg (z j)) (Finset.mem_univ i)
  calc
    |z i| = Real.sqrt (|z i| ^ 2) := by
        rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (rowNormSq (Node := Node) z) :=
        Real.sqrt_le_sqrt hsquare
    _ = rowEuclideanNorm (Node := Node) z := rfl

/-- The restricted arithmetic-average output is a bounded linear functional
with operator norm at most one for the file's Euclidean row norm. -/
theorem quadraticRestrictedPrimalAverageOutput_abs_le_rowEuclideanNorm
    (i0 : Node) (z : RowVector (Sum Node {i : Node // i ≠ i0})) :
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0 z| ≤
      rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0}) z := by
  simpa [quadraticRestrictedPrimalAverageOutput, rowEuclideanNorm, rowNormSq,
    nodeCount] using
      (abs_inv_card_mul_sum_le_sqrt_sum_sq z (fun i : Node => Sum.inl i))

/-- If the base propagated input has zero restricted average output, then the
alpha-input output is controlled by the action difference. -/
theorem quadraticRestrictedPrimalAverageOutput_le_of_action_diff_bound
    (i0 : Node)
    (A B : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (x y : RowVector (Sum Node {i : Node // i ≠ i0}))
    {R : ℝ}
    (hR_nonneg : 0 ≤ R)
    (hzero :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) B y) = 0)
    (hdiff :
      rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (fun a =>
            matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0}) A x a -
              matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0}) B y a) ≤ R) :
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) A x)| ≤ R := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hdiff_output :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (fun a : Idx =>
            matrixMulVector (Node := Idx) A x a -
              matrixMulVector (Node := Idx) B y a) =
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx) A x) -
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx) B y) := by
    unfold quadraticRestrictedPrimalAverageOutput
    simp only [Finset.sum_sub_distrib]
    ring
  calc
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Idx) A x)| =
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (fun a : Idx =>
              matrixMulVector (Node := Idx) A x a -
                matrixMulVector (Node := Idx) B y a)| := by
          rw [hdiff_output, hzero, sub_zero]
    _ ≤ rowEuclideanNorm (Node := Idx)
          (fun a : Idx =>
            matrixMulVector (Node := Idx) A x a -
              matrixMulVector (Node := Idx) B y a) :=
        quadraticRestrictedPrimalAverageOutput_abs_le_rowEuclideanNorm
          (Node := Node) i0 _
    _ ≤ R := hdiff

/-- Formula-level Appendix C.1 single-input transfer.

This is the reusable deterministic core of the stable impulse estimate.  If a
single input channel is alpha-close to an alpha-zero channel, the alpha-zero
channel has zero propagated primal-average output, and the base orbit is
geometrically bounded by a source envelope `E`, then the propagated alpha-input
output has the required `alpha * theta1^j` envelope. -/
theorem quadraticRestrictedPrimalAverageOutput_single_input_geometric_of_lipschitz
    (i0 : Node)
    (F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (x y : RowVector (Sum Node {i : Node // i ≠ i0}))
    (j : ℕ)
    {K theta LF LB MB alpha theta1 Ageo E : ℝ}
    (hK : 0 ≤ K) (htheta_pos : 0 < theta) (hLF : 0 ≤ LF)
    (hLB : 0 ≤ LB) (hMB : 0 ≤ MB) (halpha : 0 ≤ alpha)
    (htheta1_nonneg : 0 ≤ theta1) (hE : 0 ≤ E) (hAgeo : 0 ≤ Ageo)
    (hpower_alpha :
      ∀ n : ℕ,
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower
              (Node := Sum Node {i : Node // i ≠ i0})
              (F alpha) n) ≤
          K * theta ^ n)
    (hF_lip_alpha :
      matrixEuclideanOperatorNorm
          (Node := Sum Node {i : Node // i ≠ i0})
          (matrixSub
            (Node := Sum Node {i : Node // i ≠ i0})
            (F alpha) (F 0)) ≤
        LF * alpha)
    (hinput_lip :
      rowEuclideanNorm
          (Node := Sum Node {i : Node // i ≠ i0})
          (fun a => x a - y a) ≤
        LB * alpha * E)
    (hbase_orbit :
      ∀ n : ℕ,
        rowEuclideanNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower
                (Node := Sum Node {i : Node // i ≠ i0})
                (F 0) n) y) ≤
          (K * theta ^ n) * (MB * E))
    (hzero :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (matrixPower
            (Node := Sum Node {i : Node // i ≠ i0}) (F 0) j) y) = 0)
    (hgeom :
      ∀ j : ℕ, ((j : ℝ) + 1) * theta ^ j ≤ Ageo * theta1 ^ j) :
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (matrixPower
            (Node := Sum Node {i : Node // i ≠ i0}) (F alpha) j) x)| ≤
      ((K * LB + (K * K * LF * MB) / theta) * Ageo) *
        alpha * (theta1 ^ j * E) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let F₂ : ℝ → EuclideanSpace ℝ Idx →L[ℝ] EuclideanSpace ℝ Idx :=
    fun a => LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (F a))
  let ell : EuclideanSpace ℝ Idx →L[ℝ] ℝ :=
    (nodeCount (Node := Node) : ℝ)⁻¹ •
      ∑ i : Node, EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl i)
  have hnorm (z : RowVector Idx) :
      ‖WithLp.toLp 2 z‖ = rowEuclideanNorm (Node := Idx) z := by
    simp [EuclideanSpace.norm_eq, rowEuclideanNorm, rowNormSq,
      Real.norm_eq_abs, sq_abs]
  have hF₂_apply (a : ℝ) (z : RowVector Idx) :
      F₂ a (WithLp.toLp 2 z) =
        WithLp.toLp 2 (matrixMulVector (Node := Idx) (F a) z) := by
    rfl
  have hF₂_pow_apply (a : ℝ) (n : ℕ) (z : RowVector Idx) :
      (F₂ a ^ n) (WithLp.toLp 2 z) =
        WithLp.toLp 2
          (matrixMulVector (Node := Idx)
            (matrixPower (Node := Idx) (F a) n) z) := by
    induction n generalizing z with
    | zero =>
        rw [pow_zero, ContinuousLinearMap.one_apply, matrixPower]
        ext k
        simp only [PiLp.toLp_apply, matrixMulVector, identityMatrix]
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _hb hb
          simp [hb.symm]
        · intro hk
          simp at hk
    | succ n ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hF₂_apply, ih,
          matrixPower, matrixMulVector_matrixMul]
  have hell_apply (z : RowVector Idx) :
      ell (WithLp.toLp 2 z) =
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0 z := by
    simp [ell, quadraticRestrictedPrimalAverageOutput]
  have hell : ‖ell‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound ell (by norm_num)
    intro z
    rw [← WithLp.toLp_ofLp 2 z, hell_apply, Real.norm_eq_abs, hnorm]
    simpa using
      (quadraticRestrictedPrimalAverageOutput_abs_le_rowEuclideanNorm
        (Node := Node) i0 (WithLp.ofLp z))
  have hpower₂ : ∀ n : ℕ, ‖F₂ alpha ^ n‖ ≤ K * theta ^ n := by
    intro n
    apply ContinuousLinearMap.opNorm_le_bound
    · exact (matrixEuclideanOperatorNorm_spec
        (Node := Idx) (matrixPower (Node := Idx) (F alpha) n)).1.trans
          (hpower_alpha n)
    · intro z
      rw [← WithLp.toLp_ofLp 2 z, hF₂_pow_apply, hnorm, hnorm]
      exact le_trans
        (rowEuclideanNorm_matrixMulVector_le
          (Node := Idx) (matrixPower (Node := Idx) (F alpha) n)
            (WithLp.ofLp z))
        (mul_le_mul_of_nonneg_right (hpower_alpha n)
          (by exact Real.sqrt_nonneg _))
  have hF_lip₂ : ‖F₂ alpha - F₂ 0‖ ≤ LF * alpha := by
    apply ContinuousLinearMap.opNorm_le_bound
    · exact (matrixEuclideanOperatorNorm_spec
        (Node := Idx) (matrixSub (Node := Idx) (F alpha) (F 0))).1.trans
          hF_lip_alpha
    · intro z
      rw [← WithLp.toLp_ofLp 2 z, ContinuousLinearMap.sub_apply,
        hF₂_apply, hF₂_apply, ← WithLp.toLp_sub, hnorm, hnorm]
      change rowEuclideanNorm (Node := Idx)
        (fun i => matrixMulVector (Node := Idx) (F alpha) (WithLp.ofLp z) i -
          matrixMulVector (Node := Idx) (F 0) (WithLp.ofLp z) i) ≤ _
      rw [← matrixMulVector_matrixSub]
      exact le_trans
        (rowEuclideanNorm_matrixMulVector_le
          (Node := Idx) (matrixSub (Node := Idx) (F alpha) (F 0))
            (WithLp.ofLp z))
        (mul_le_mul_of_nonneg_right hF_lip_alpha
          (by exact Real.sqrt_nonneg _))
  simpa only [hF₂_pow_apply, hell_apply] using
    (ContinuousLinearMap.abs_apply_pow_le_geometric_of_lipschitz
      (F := F₂) (ell := ell) (x := WithLp.toLp 2 x)
      (y := WithLp.toLp 2 y) (j := j)
      (K := K) (theta := theta) (LF := LF) (LB := LB) (MB := MB)
      (alpha := alpha) (theta1 := theta1) (Ageo := Ageo) (E0 := E)
      hK htheta_pos hLF hLB hMB halpha hE hell hpower₂ hF_lip₂
      (by simpa only [← WithLp.toLp_sub, hnorm] using hinput_lip)
      (by
        intro n
        simpa only [hF₂_pow_apply, hnorm] using hbase_orbit n)
      (by simpa only [hF₂_pow_apply, hell_apply] using hzero)
      (hgeom j))

/-- The restricted primal-average output is additive in its coordinate
argument. -/
theorem quadraticRestrictedPrimalAverageOutput_add
    (i0 : Node)
    (x y : RowVector (Sum Node {i : Node // i ≠ i0})) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0 (x + y) =
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0 x +
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0 y := by
  classical
  unfold quadraticRestrictedPrimalAverageOutput
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- The restricted primal-average output commutes with finite sums. -/
theorem quadraticRestrictedPrimalAverageOutput_finset_sum
    (i0 : Node) (s : Finset ℕ)
    (x : ℕ → RowVector (Sum Node {i : Node // i ≠ i0})) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (∑ j ∈ s, x j) =
      ∑ j ∈ s,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0 (x j) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [quadraticRestrictedPrimalAverageOutput]
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [quadraticRestrictedPrimalAverageOutput_add, ih]

/-- Finite Duhamel assembly for the Appendix C.1 stable-output impulse
envelope.

This lemma contains no source-specific cancellation: it only says that once
the initial projected input and every period-innovation input have the
alpha-small stable-output envelope, the closed stable Duhamel response inherits
the same envelope by linearity and the triangle inequality. -/
theorem quadraticRestrictedPrimalAverageOutput_stableDuhamel_le_of_single_input
    (i0 : Node)
    (F : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (z0 : RowVector (Sum Node {i : Node // i ≠ i0}))
    (xi : ℕ → RowVector (Sum Node {i : Node // i ≠ i0}))
    (t : ℕ) {C alpha theta1 : ℝ}
    (hC_nonneg : 0 ≤ C) (halpha_nonneg : 0 ≤ alpha)
    (hinit :
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) F t)
            z0)| ≤
        C * alpha *
          (theta1 ^ t *
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0}) z0))
    (hxi :
      ∀ j : ℕ, j ∈ Finset.range t →
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) F
                (t - 1 - j))
              (xi j))| ≤
          C * alpha *
            (theta1 ^ (t - 1 - j) *
              rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0}) (xi j))) :
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (stablePowerDuhamelClosedResponse
          (Node := Sum Node {i : Node // i ≠ i0}) F z0 xi t)| ≤
      C * alpha *
        (theta1 ^ t *
          rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0}) z0 +
          Finset.sum (Finset.range t) (fun j =>
            theta1 ^ (t - 1 - j) *
              rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0}) (xi j))) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let init : RowVector Idx :=
    matrixMulVector (Node := Idx)
      (matrixPower (Node := Idx) F t) z0
  let forced : ℕ → RowVector Idx := fun j =>
    matrixMulVector (Node := Idx)
      (matrixPower (Node := Idx) F (t - 1 - j)) (xi j)
  have houtput :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (stablePowerDuhamelClosedResponse (Node := Idx) F z0 xi t) =
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0 init +
          ∑ j ∈ Finset.range t,
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (forced j) := by
    unfold stablePowerDuhamelClosedResponse
    rw [quadraticRestrictedPrimalAverageOutput_add]
    rw [quadraticRestrictedPrimalAverageOutput_finset_sum]
  have hsum_abs :
      |∑ j ∈ Finset.range t,
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (forced j)| ≤
        ∑ j ∈ Finset.range t,
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (forced j)| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (s := Finset.range t)
        (f := fun j =>
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (forced j)))
  have hsum_bound :
      ∑ j ∈ Finset.range t,
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (forced j)| ≤
        ∑ j ∈ Finset.range t,
          C * alpha *
            (theta1 ^ (t - 1 - j) *
              rowEuclideanNorm (Node := Idx) (xi j)) := by
    exact Finset.sum_le_sum fun j hj => by
      simpa [Idx, forced] using hxi j hj
  have hinit' :
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0 init| ≤
        C * alpha *
          (theta1 ^ t * rowEuclideanNorm (Node := Idx) z0) := by
    simpa [Idx, init] using hinit
  have hcoef_nonneg : 0 ≤ C * alpha :=
    mul_nonneg hC_nonneg halpha_nonneg
  calc
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (stablePowerDuhamelClosedResponse (Node := Idx) F z0 xi t)| =
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0 init +
          ∑ j ∈ Finset.range t,
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (forced j)| := by rw [houtput]
    _ ≤
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0 init| +
          |∑ j ∈ Finset.range t,
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (forced j)| := abs_add_le _ _
    _ ≤
        C * alpha *
            (theta1 ^ t * rowEuclideanNorm (Node := Idx) z0) +
          ∑ j ∈ Finset.range t,
            C * alpha *
              (theta1 ^ (t - 1 - j) *
                rowEuclideanNorm (Node := Idx) (xi j)) :=
          add_le_add hinit' (le_trans hsum_abs hsum_bound)
    _ =
        C * alpha *
          (theta1 ^ t * rowEuclideanNorm (Node := Idx) z0 +
            Finset.sum (Finset.range t) (fun j =>
              theta1 ^ (t - 1 - j) *
                rowEuclideanNorm (Node := Idx) (xi j))) := by
          rw [← Finset.mul_sum]
          ring

/-- Finite Duhamel assembly with the source-shaped Appendix C.1 envelope.

The source stable impulse estimate is stated against the raw initial/period
innovation envelopes, not against the projected stable inputs themselves.  This
is the same linearity/triangle step as
`quadraticRestrictedPrimalAverageOutput_stableDuhamel_le_of_single_input`, but
with caller-supplied envelope functions. -/
theorem quadraticRestrictedPrimalAverageOutput_stableDuhamel_le_of_source_envelope
    (i0 : Node)
    (F : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (z0 : RowVector (Sum Node {i : Node // i ≠ i0}))
    (xi : ℕ → RowVector (Sum Node {i : Node // i ≠ i0}))
    (t : ℕ) {C alpha theta1 E0 : ℝ} (Exi : ℕ → ℝ)
    (hC_nonneg : 0 ≤ C) (halpha_nonneg : 0 ≤ alpha)
    (hinit :
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) F t)
            z0)| ≤
        C * alpha * (theta1 ^ t * E0))
    (hxi :
      ∀ j : ℕ, j ∈ Finset.range t →
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) F
                (t - 1 - j))
              (xi j))| ≤
          C * alpha * (theta1 ^ (t - 1 - j) * Exi j)) :
    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (stablePowerDuhamelClosedResponse
          (Node := Sum Node {i : Node // i ≠ i0}) F z0 xi t)| ≤
      C * alpha *
        (theta1 ^ t * E0 +
          Finset.sum (Finset.range t) (fun j =>
            theta1 ^ (t - 1 - j) * Exi j)) := by
  classical
  simpa only [quadraticRestrictedPrimalAverageOutput,
      stablePowerDuhamelClosedResponse, SOptLib.linearDuhamelResponse,
      realMatrixContinuousLinearMap_pow_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] using
    (SOptLib.linearDuhamelResponse_apply_abs_le_of_component_bounds
      (F := realMatrixContinuousLinearMap (Node := Sum Node {i : Node // i ≠ i0}) F)
      (ell := (nodeCount (Node := Node) : ℝ)⁻¹ •
        ∑ i : Node, ContinuousLinearMap.proj (R := ℝ) (Sum.inl i))
      (z0 := z0) (xi := xi) (t := t) (c := C * alpha)
      (theta := theta1) (E0 := E0) (Exi := Exi)
      (by
        simpa only [quadraticRestrictedPrimalAverageOutput,
          realMatrixContinuousLinearMap_pow_apply,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul] using hinit)
      (by
        intro j hj
        simpa only [quadraticRestrictedPrimalAverageOutput,
          realMatrixContinuousLinearMap_pow_apply,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul] using hxi j hj))

/-- Canonical projected stable boundary response used in Appendix C.1.

This is the true restricted period-map stable component: project the initial
boundary state and each period innovation by `(I-P(α))`, then propagate them by
the stable complement `F(α)`. -/
noncomputable def quadraticRestrictedStableBoundaryResponse
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (alpha : ℝ) (noise : NoisePath Node ℝ) (t : ℕ) :
    RowVector (Sum Node {i : Node // i ≠ i0}) :=
  let z0 : RowVector (Sum Node {i : Node // i ≠ i0}) :=
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState noise 0,
        (quad.withStepsize alpha).trackerErrorZeroSum noise 0)
  let xi : ℕ → RowVector (Sum Node {i : Node // i ≠ i0}) :=
    fun k =>
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise k
  stablePowerDuhamelClosedResponse
    (Node := Sum Node {i : Node // i ≠ i0})
    (F alpha)
    ((1 - Matrix.mulVecLin (P alpha)) z0)
    (fun k =>
      (1 - Matrix.mulVecLin (P alpha)) (xi k)) t

/-- The restricted primal-average output vanishes on vectors whose primal block
is zero. -/
theorem quadraticRestrictedPrimalAverageOutput_eq_zero_of_top_zero
    (i0 : Node) (z : RowVector (Sum Node {i : Node // i ≠ i0}))
    (hz : ∀ i : Node, z (Sum.inl i) = 0) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0 z = 0 := by
  classical
  simp [quadraticRestrictedPrimalAverageOutput, hz]

/-- A rank-one projection with consensus right vector and nonuniform left
weights does not make the arithmetic-average output vanish on its whole
kernel.

This is a typed guardrail for the Appendix C.1 stable-output route: the
alpha-small output estimate cannot be proved from `P(alpha) z = 0` and
analyticity of `P` alone.  It must also use the source-specific stable
impulse/input cancellation of the canonical restricted response. -/
theorem rankOneConsensusProjection_kernel_not_arithmeticAverage_zero_bool :
    ∃ (P : NodeMatrix Bool) (right left z : RowVector Bool),
      P = (fun i j : Bool => right i * left j) ∧
        (∀ i : Bool, right i = 1) ∧
          rowDot (Node := Bool) left right = 1 ∧
            matrixMulVector (Node := Bool) P z = (fun _ : Bool => 0) ∧
              ((2 : ℝ)⁻¹ * ∑ i : Bool, z i) ≠ 0 := by
  classical
  let right : RowVector Bool := fun _ => 1
  let left : RowVector Bool := fun j => if j = false then 1 else 0
  let P : NodeMatrix Bool := fun i j => right i * left j
  let z : RowVector Bool := fun j => if j = false then 0 else 1
  refine ⟨P, right, left, z, rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [right]
  · simp [rowDot, right, left]
  · funext i
    simp [matrixMulVector, P, right, left, z]
  · norm_num [z]

/-- At `alpha = 0`, the projected initial stable boundary has zero primal
block.  This uses the explicit C.1 right/left unit vectors, not an abstract
rank-one projection surrogate. -/
theorem quadraticRestrictedStableComplement_initial_alpha_zero_top
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (noise : NoisePath Node ℝ) :
    ∀ i : Node,
      (1 - Matrix.mulVecLin (P 0))
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize 0).primalState noise 0,
              (quad.withStepsize 0).trackerErrorZeroSum noise 0))
          (Sum.inl i) = 0 := by
  classical
  intro i
  have hinit :=
    quadraticRestrictedInitialBoundaryCoord_alpha_zero
      (Node := Node) quad i0 noise
  have hsum :
      (∑ x : Node, quad.perronLeft 0 x * quad.x0) = quad.x0 := by
    calc
      (∑ x : Node, quad.perronLeft 0 x * quad.x0) =
          (∑ x : Node, quad.perronLeft 0 x) * quad.x0 := by
            rw [Finset.sum_mul]
      _ = quad.x0 := by
            simpa [rowSum] using congrArg (fun y : ℝ => y * quad.x0)
              (quad.perronLeft_sum 0)
  simp [LinearMap.sub_apply, Module.End.one_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, matrixMulVector, hP0,
    hright_top, hleft_top, hleft_bottom, rowDot, hinit, hsum]

/-- At `alpha = 0`, period innovations have zero projected stable primal
block.  This is the finite-period form of the source observation that tracker
innovations cannot enter the primal equation at zero stepsize. -/
theorem quadraticRestrictedStableComplement_periodInnovation_alpha_zero_top
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    ∀ i : Node,
      (1 - Matrix.mulVecLin (P 0))
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda 0 i0 noise k)
          (Sum.inl i) = 0 := by
  classical
  intro i
  simp [LinearMap.sub_apply, Module.End.one_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, matrixMulVector, hP0,
    hright_top, hleft_top, hleft_bottom, rowDot,
    quadraticRestrictedPeriodNoiseInnovationCoord_alpha_zero_top]

/-- The alpha-zero stable complement preserves the zero-primal block.

This is the remaining finite-coordinate algebra behind the Appendix C.1
stable-output cancellation: `A(0)=P(0)+F(0)`, the period map is block lower
triangular, and the explicit slow projection kills zero-primal vectors. -/
theorem quadraticRestrictedStableComplementMatrix_alpha_zero_top_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (z : RowVector (Sum Node {i : Node // i ≠ i0}))
    (hz : ∀ i : Node, z (Sum.inl i) = 0) :
    ∀ i : Node,
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
        (F 0) z (Sum.inl i) = 0 := by
  classical
  intro i
  have hsplit0 :=
    hsplitting.2.2.2.2.2.2.2.2 0 (by simpa using hsplitting.1.le)
  have hAeq := hsplit0.2.1
  have hgamma0 : gamma 0 = 1 := hsplitting.2.2.2.2.1
  let A0 : NodeMatrix (Sum Node {i : Node // i ≠ i0}) :=
    quadraticRestrictedPeriodMatrix (Node := Node) quad lambda 0 i0
  have hAvec_top :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0 z
        (Sum.inl i) = 0 := by
    simp [A0, matrixMulVector,
      quadraticRestrictedPeriodMatrix_alpha_zero_top_left,
      quadraticRestrictedPeriodMatrix_alpha_zero_top_right, hz]
  have hPvec_top :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) (P 0) z
        (Sum.inl i) = 0 := by
    simp [matrixMulVector, hP0, hright_top, hleft_top, hleft_bottom,
      rowDot, hz]
  have hslow_top :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
          ((gamma 0) • P 0) z (Sum.inl i) = 0 := by
    rw [hgamma0]
    simpa [matrixMulVector] using hPvec_top
  have hmul_add :
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) A0 z =
        fun a =>
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              ((gamma 0) • P 0) z a +
            matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (F 0) z a := by
    funext a
    change
      matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
          ((fun alpha : ℝ =>
            quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) 0) z a =
        matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
            ((gamma 0) • P 0) z a +
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
            (F 0) z a
    rw [hAeq]
    simp [A0, matrixMulVector, matrixAdd, Finset.sum_add_distrib, add_mul]
  have hcoord := congrFun hmul_add (Sum.inl i)
  nlinarith

/-- Powers of the alpha-zero stable complement preserve the zero-primal block. -/
theorem quadraticRestrictedStableComplementMatrix_alpha_zero_power_top_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F) :
    ∀ m : ℕ, ∀ z : RowVector (Sum Node {i : Node // i ≠ i0}),
      (∀ i : Node, z (Sum.inl i) = 0) →
        ∀ i : Node,
          matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower (Node := Sum Node {i : Node // i ≠ i0})
              (F 0) m) z (Sum.inl i) = 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  intro m
  induction m with
  | zero =>
      intro z hz i
      have hid :
          matrixMulVector (Node := Idx) (identityMatrix (Node := Idx)) z = z := by
        funext a
        unfold matrixMulVector identityMatrix
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _hb hb
          simp [hb.symm]
        · intro ha
          simp at ha
      simpa [Idx, matrixPower, hid] using hz i
  | succ m ih =>
      intro z hz i
      rw [matrixPower, matrixMulVector_matrixMul]
      exact ih (matrixMulVector (Node := Idx) (F 0) z)
        (fun i =>
          quadraticRestrictedStableComplementMatrix_alpha_zero_top_zero
            (Node := Node) quad lambda i0 r0 alpha0 theta K
            right left gamma P F hP0 hright_top hleft_top hleft_bottom
            hsplitting z hz i) i

/-- Alpha-zero cancellation for the single propagated initial stable input. -/
theorem quadraticRestrictedStableComplement_initial_single_output_alpha_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) (F 0) t)
        ((1 - Matrix.mulVecLin (P 0))
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize 0).primalState noise 0,
              (quad.withStepsize 0).trackerErrorZeroSum noise 0)))) = 0 := by
  classical
  apply quadraticRestrictedPrimalAverageOutput_eq_zero_of_top_zero
    (Node := Node) i0
  intro i
  exact
    quadraticRestrictedStableComplementMatrix_alpha_zero_power_top_zero
      (Node := Node) quad lambda i0 r0 alpha0 theta K
      right left gamma P F hP0 hright_top hleft_top hleft_bottom
      hsplitting t
      ((1 - Matrix.mulVecLin (P 0))
        (restrictedStateToCoord (Node := Node) i0
          ((quad.withStepsize 0).primalState noise 0,
            (quad.withStepsize 0).trackerErrorZeroSum noise 0)))
      (quadraticRestrictedStableComplement_initial_alpha_zero_top
        (Node := Node) quad lambda i0 right left P
        hP0 hright_top hleft_top hleft_bottom noise) i

/-- Alpha-zero cancellation for each single propagated period-innovation
stable input. -/
theorem quadraticRestrictedStableComplement_periodInnovation_single_output_alpha_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (noise : NoisePath Node ℝ) (k t : ℕ) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (matrixPower (Node := Sum Node {i : Node // i ≠ i0}) (F 0) t)
        ((1 - Matrix.mulVecLin (P 0))
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda 0 i0 noise k))) = 0 := by
  classical
  apply quadraticRestrictedPrimalAverageOutput_eq_zero_of_top_zero
    (Node := Node) i0
  intro i
  exact
    quadraticRestrictedStableComplementMatrix_alpha_zero_power_top_zero
      (Node := Node) quad lambda i0 r0 alpha0 theta K
      right left gamma P F hP0 hright_top hleft_top hleft_bottom
      hsplitting t
      ((1 - Matrix.mulVecLin (P 0))
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda 0 i0 noise k))
      (quadraticRestrictedStableComplement_periodInnovation_alpha_zero_top
        (Node := Node) quad lambda i0 right left P
        hP0 hright_top hleft_top hleft_bottom noise k) i

/-- The canonical projected stable boundary response has integrable squared
row norm at every fixed boundary time. -/
theorem quadraticRestrictedStableBoundaryResponse_norm_sq_integrable
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (t : ℕ) :
    Integrable
      (fun ω =>
        rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F alpha
            (oracle.noise ω) t) ^ 2) μ := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let z0 : Ω → RowVector Idx := fun ω =>
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
        (quad.withStepsize alpha).trackerErrorZeroSum
          (oracle.noise ω) 0)
  let xi : ℕ → Ω → RowVector Idx := fun k ω =>
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 (oracle.noise ω) k
  have hz0 : ∀ a : Idx, MemLp (fun ω => z0 ω a) 2 μ := by
    intro a
    exact
      quadraticRestrictedInitialBoundaryCoord_coordinate_memLp
        (Node := Node) quad alpha i0 μ oracle hnoise a
  have hxi : ∀ k : ℕ, ∀ a : Idx, MemLp (fun ω => xi k ω a) 2 μ := by
    intro k a
    exact
      quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
        (Node := Node) quad lambda alpha i0 μ oracle hnoise k a
  have hstable_coord :
      ∀ a : Idx,
        MemLp
          (fun ω =>
            stablePowerDuhamelClosedResponse
              (Node := Idx) (F alpha)
              ((1 - Matrix.mulVecLin (P alpha)) (z0 ω))
              (fun k =>
                (1 - Matrix.mulVecLin (P alpha)) (xi k ω)) t a) 2 μ := by
    apply
      stablePowerDuhamelClosedResponse_coordinate_memLp
        (Node := Idx) (F alpha)
        (fun ω =>
          (1 - Matrix.mulVecLin (P alpha)) (z0 ω))
        (fun k ω =>
          (1 - Matrix.mulVecLin (P alpha)) (xi k ω))
    · intro a
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      have hproj :
          MemLp
            (fun ω => ∑ b : Idx, P alpha a b * z0 ω b) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (hz0 b).const_smul (P alpha a b)
      exact (hz0 a).sub hproj
    · intro k a
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      have hproj :
          MemLp
            (fun ω => ∑ b : Idx, P alpha a b * xi k ω b) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (hxi k b).const_smul (P alpha a b)
      exact (hxi k a).sub hproj
  simpa [quadraticRestrictedStableBoundaryResponse, z0, xi] using
    rowEuclideanNorm_sq_integrable_of_coordinate_memLp
      (Node := Idx) hstable_coord

/-- The scalar primal-average output of the canonical stable boundary response
has an integrable square at every fixed boundary time. -/
theorem quadraticRestrictedStableBoundaryResponse_output_sq_integrable
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (t : ℕ) :
    Integrable
      (fun ω =>
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F alpha
            (oracle.noise ω) t)| ^ 2) μ := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let z0 : Ω → RowVector Idx := fun ω =>
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
        (quad.withStepsize alpha).trackerErrorZeroSum
          (oracle.noise ω) 0)
  let xi : ℕ → Ω → RowVector Idx := fun k ω =>
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 (oracle.noise ω) k
  have hz0 : ∀ a : Idx, MemLp (fun ω => z0 ω a) 2 μ := by
    intro a
    exact
      quadraticRestrictedInitialBoundaryCoord_coordinate_memLp
        (Node := Node) quad alpha i0 μ oracle hnoise a
  have hxi : ∀ k : ℕ, ∀ a : Idx, MemLp (fun ω => xi k ω a) 2 μ := by
    intro k a
    exact
      quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
        (Node := Node) quad lambda alpha i0 μ oracle hnoise k a
  have hstable_coord :
      ∀ a : Idx,
        MemLp
          (fun ω =>
            stablePowerDuhamelClosedResponse
              (Node := Idx) (F alpha)
              ((1 - Matrix.mulVecLin (P alpha)) (z0 ω))
              (fun k =>
                (1 - Matrix.mulVecLin (P alpha)) (xi k ω)) t a) 2 μ := by
    apply
      stablePowerDuhamelClosedResponse_coordinate_memLp
        (Node := Idx) (F alpha)
        (fun ω =>
          (1 - Matrix.mulVecLin (P alpha)) (z0 ω))
        (fun k ω =>
          (1 - Matrix.mulVecLin (P alpha)) (xi k ω))
    · intro a
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      have hproj :
          MemLp
            (fun ω => ∑ b : Idx, P alpha a b * z0 ω b) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (hz0 b).const_smul (P alpha a b)
      exact (hz0 a).sub hproj
    · intro k a
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      have hproj :
          MemLp
            (fun ω => ∑ b : Idx, P alpha a b * xi k ω b) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (hxi k b).const_smul (P alpha a b)
      exact (hxi k a).sub hproj
  have houtput_memLp :
      MemLp
        (fun ω =>
          (nodeCount (Node := Node) : ℝ)⁻¹ *
            ∑ i : Node,
              stablePowerDuhamelClosedResponse
                (Node := Idx) (F alpha)
                ((1 - Matrix.mulVecLin (P alpha)) (z0 ω))
                (fun k =>
                  (1 - Matrix.mulVecLin (P alpha)) (xi k ω)) t (Sum.inl i)) 2 μ := by
    have hsum :
        MemLp
          (fun ω =>
            ∑ i : Node,
              stablePowerDuhamelClosedResponse
                (Node := Idx) (F alpha)
                ((1 - Matrix.mulVecLin (P alpha)) (z0 ω))
                (fun k =>
                  (1 - Matrix.mulVecLin (P alpha)) (xi k ω)) t (Sum.inl i)) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact hstable_coord (Sum.inl i)
    exact hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  simpa [quadraticRestrictedPrimalAverageOutput,
    quadraticRestrictedStableBoundaryResponse, z0, xi] using
    real_abs_sq_integrable_of_memLp_two houtput_memLp

/-- The scalar primal-average output of the canonical stable boundary response
is an `L²` process at every fixed boundary time. -/
theorem quadraticRestrictedStableBoundaryResponse_output_memLp_two
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (t : ℕ) :
    MemLp
      (fun ω =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F alpha
            (oracle.noise ω) t)) 2 μ := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let z0 : Ω → RowVector Idx := fun ω =>
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
        (quad.withStepsize alpha).trackerErrorZeroSum
          (oracle.noise ω) 0)
  let xi : ℕ → Ω → RowVector Idx := fun k ω =>
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda alpha i0 (oracle.noise ω) k
  have hz0 : ∀ a : Idx, MemLp (fun ω => z0 ω a) 2 μ := by
    intro a
    exact
      quadraticRestrictedInitialBoundaryCoord_coordinate_memLp
        (Node := Node) quad alpha i0 μ oracle hnoise a
  have hxi : ∀ k : ℕ, ∀ a : Idx, MemLp (fun ω => xi k ω a) 2 μ := by
    intro k a
    exact
      quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
        (Node := Node) quad lambda alpha i0 μ oracle hnoise k a
  have hstable_coord :
      ∀ a : Idx,
        MemLp
          (fun ω =>
            stablePowerDuhamelClosedResponse
              (Node := Idx) (F alpha)
              ((1 - Matrix.mulVecLin (P alpha)) (z0 ω))
              (fun k =>
                (1 - Matrix.mulVecLin (P alpha)) (xi k ω)) t a) 2 μ := by
    apply
      stablePowerDuhamelClosedResponse_coordinate_memLp
        (Node := Idx) (F alpha)
        (fun ω =>
          (1 - Matrix.mulVecLin (P alpha)) (z0 ω))
        (fun k ω =>
          (1 - Matrix.mulVecLin (P alpha)) (xi k ω))
    · intro a
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      have hproj :
          MemLp
            (fun ω => ∑ b : Idx, P alpha a b * z0 ω b) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (hz0 b).const_smul (P alpha a b)
      exact (hz0 a).sub hproj
    · intro k a
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      have hproj :
          MemLp
            (fun ω => ∑ b : Idx, P alpha a b * xi k ω b) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro b _hb
        exact (hxi k b).const_smul (P alpha a b)
      exact (hxi k a).sub hproj
  have hsum :
      MemLp
        (fun ω =>
          ∑ i : Node,
            stablePowerDuhamelClosedResponse
              (Node := Idx) (F alpha)
              ((1 - Matrix.mulVecLin (P alpha)) (z0 ω))
              (fun k =>
                (1 - Matrix.mulVecLin (P alpha)) (xi k ω)) t (Sum.inl i)) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact hstable_coord (Sum.inl i)
  simpa [quadraticRestrictedPrimalAverageOutput,
    quadraticRestrictedStableBoundaryResponse, z0, xi] using
    hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)

/-- Appendix C.1 stable-output `L²` assembly from the two source-sized inputs.

The deterministic stable Duhamel estimate controls the stable restricted
state.  The source-specific cancellation at `alpha = 0` enters through
`houtput_l2_dominated`: applying the primal-average output to the stable
component costs an additional factor `alpha`.  The remaining stochastic work
is isolated in `hstate_l2_bound`, the averaged `L²` bound for the stable
restricted state obtained from the period innovations and the iid variance
law. -/
theorem quadratic_restricted_stable_output_average_l2_bound
    (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (response :
      ℝ → Ω → ℕ → RowVector (Sum Node {i : Node // i ≠ i0}))
    {alpha0 Lout Cstate : ℝ}
    (halpha0_pos : 0 < alpha0)
    (hCstate_nonneg : 0 ≤ Cstate)
    (houtput_l2_dominated :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ T : ℕ, 1 ≤ T →
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (response alpha ω t)| ^ 2 ∂μ) ≤
            (Lout ^ 2 * alpha ^ 2) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                    (response alpha ω t) ^ 2 ∂μ))
    (hstate_l2_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ T : ℕ, 1 ≤ T →
          Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                (response alpha ω t) ^ 2 ∂μ) ≤
            Cstate * (T : ℝ)) :
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
  exact
    exists_average_sq_bound_of_sum_dom_and_linear_sum_bound
      (fun alpha t =>
        ∫ ω,
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (response alpha ω t)| ^ 2 ∂μ)
      (fun alpha t =>
        ∫ ω,
          rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (response alpha ω t) ^ 2 ∂μ)
      alpha0 Lout Cstate halpha0_pos houtput_l2_dominated hstate_l2_bound

/-- Appendix C.1 finite-sum bridge for stable-output domination.

The source analytic work is the per-boundary integral estimate saying that the
primal-average output of the stable projection has an extra `alpha` factor.
Once that pointwise-in-time estimate is available, the averaged/summed form
used by `quadratic_restricted_stable_output_average_l2_bound` is only finite
monotonicity. -/
theorem quadratic_restricted_stable_output_dom_from_integral_bound
    (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (response :
      ℝ → Ω → ℕ → RowVector (Sum Node {i : Node // i ≠ i0}))
    {alpha0 Lout : ℝ}
    (hper_time :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ t : ℕ,
          (∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (response alpha ω t)| ^ 2 ∂μ) ≤
          (Lout ^ 2 * alpha ^ 2) *
            (∫ ω,
              rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                (response alpha ω t) ^ 2 ∂μ)) :
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
      ∀ T : ℕ, 1 ≤ T →
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (response alpha ω t)| ^ 2 ∂μ) ≤
          (Lout ^ 2 * alpha ^ 2) *
            Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                  (response alpha ω t) ^ 2 ∂μ) := by
  classical
  intro alpha halpha_pos halpha_le T _hT
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun t _ht =>
    hper_time alpha halpha_pos halpha_le t

/-- Appendix C.1 finite-sum bridge for the projected stable-state `L²` budget.

The stochastic work left by the deterministic Duhamel square-sum theorem is to
bound each projected stable boundary second moment uniformly.  This lemma
packages only the finite-horizon aggregation from that per-boundary bound. -/
theorem quadratic_restricted_projected_stable_state_l2_from_integral_bound
    (i0 : Node)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (response :
      ℝ → Ω → ℕ → RowVector (Sum Node {i : Node // i ≠ i0}))
    {alpha0 Cstate : ℝ}
    (hCstate_nonneg : 0 ≤ Cstate)
    (hper_time :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ t : ℕ,
          (∫ ω,
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (response alpha ω t) ^ 2 ∂μ) ≤ Cstate) :
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
      ∀ T : ℕ, 1 ≤ T →
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (response alpha ω t) ^ 2 ∂μ) ≤
          Cstate * (T : ℝ) := by
  classical
  intro alpha halpha_pos halpha_le T _hT
  calc
    Finset.sum (Finset.range T) (fun t =>
        ∫ ω,
          rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
            (response alpha ω t) ^ 2 ∂μ) ≤
        Finset.sum (Finset.range T) (fun _t => Cstate) := by
          exact Finset.sum_le_sum fun t _ht =>
            hper_time alpha halpha_pos halpha_le t
    _ = Cstate * (T : ℝ) := by simp [mul_comm]

/-- Source-sized pathwise alpha-small stable-output bound.

Appendix C.1 uses the fact that the primal-average output of the projected
stable response vanishes at `alpha = 0`; analyticity of the restricted Riesz
splitting then gives the extra `alpha` factor before taking expectations. -/
theorem quadraticRestrictedPrimalAverageOutput_stableResponse_alpha_zero
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
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F) :
    ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (quadraticRestrictedStableBoundaryResponse
          (Node := Node) quad lambda i0 P F 0 noise t) = 0 := by
  classical
  intro noise t
  apply
    quadraticRestrictedPrimalAverageOutput_eq_zero_of_top_zero
      (Node := Node) i0
  intro i
  let Idx := Sum Node {i : Node // i ≠ i0}
  let z0 : RowVector Idx :=
    restrictedStateToCoord (Node := Node) i0
      ((quad.withStepsize 0).primalState noise 0,
        (quad.withStepsize 0).trackerErrorZeroSum noise 0)
  let xi : ℕ → RowVector Idx := fun k =>
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda 0 i0 noise k
  let z0st : RowVector Idx :=
    (1 - Matrix.mulVecLin (P 0)) z0
  let xist : ℕ → RowVector Idx := fun k =>
    (1 - Matrix.mulVecLin (P 0)) (xi k)
  let S : Submodule ℝ (RowVector Idx) :=
    { carrier := {z : RowVector Idx | ∀ k : Node, z (Sum.inl k) = 0}
      zero_mem' := fun _ ↦ rfl
      add_mem' := fun {x y} hx hy k ↦ by simp [hx k, hy k]
      smul_mem' := fun c {x} hx k ↦ by simp [hx k] }
  simpa only [quadraticRestrictedStableBoundaryResponse,
      stablePowerDuhamelClosedResponse, SOptLib.linearDuhamelResponse,
      realMatrixContinuousLinearMap_pow_apply] using
    (SOptLib.linearDuhamelResponse_apply_eq_zero_of_invariant
      (F := realMatrixContinuousLinearMap (Node := Idx) (F 0))
      (ell := ContinuousLinearMap.proj (R := ℝ) (Sum.inl i))
      (S := S) (z0 := z0st) (xi := xist) (t := t)
      (by
        intro z hz
        have hz' : ∀ k : Node, z (Sum.inl k) = 0 := by
          simpa only [S] using hz
        simp only [S]
        intro k
        exact
          quadraticRestrictedStableComplementMatrix_alpha_zero_top_zero
            (Node := Node) quad lambda i0 r0 alpha0 theta K
            right left gamma P F hP0 hright_top hleft_top hleft_bottom
            hsplitting z hz' k)
      (by
        intro z hz
        apply LinearMap.mem_ker.mpr
        have hz' : ∀ k : Node, z (Sum.inl k) = 0 := by
          simpa only [S] using hz
        exact hz' i)
      (by
        simp only [S]
        intro k
        simpa [Idx, z0, z0st] using
          quadraticRestrictedStableComplement_initial_alpha_zero_top
            (Node := Node) quad lambda i0 right left P
            hP0 hright_top hleft_top hleft_bottom noise k)
      (by
        intro j _hj
        simp only [S]
        intro k
        simpa [Idx, xi, xist] using
          quadraticRestrictedStableComplement_periodInnovation_alpha_zero_top
            (Node := Node) quad lambda i0 right left P
            hP0 hright_top hleft_top hleft_bottom noise j k))

/-- Negating a finite scalar row vector does not change the custom Euclidean
norm. -/
theorem rowEuclideanNorm_neg
    (x : RowVector Node) :
    rowEuclideanNorm (Node := Node) (fun i => -x i) =
      rowEuclideanNorm (Node := Node) x := by
  classical
  simp [rowEuclideanNorm, rowNormSq]

/-- Triangle inequality for subtraction in the file's concrete row norm. -/
theorem rowEuclideanNorm_sub_le
    (x y : RowVector Node) :
    rowEuclideanNorm (Node := Node) (fun i => x i - y i) ≤
      rowEuclideanNorm (Node := Node) x +
        rowEuclideanNorm (Node := Node) y := by
  classical
  let negY : RowVector Node := fun i => -y i
  have hsub : (fun i : Node => x i - y i) = x + negY := by
    funext i
    simp [negY]
    ring
  calc
    rowEuclideanNorm (Node := Node) (fun i => x i - y i) =
        rowEuclideanNorm (Node := Node) (x + negY) := by rw [hsub]
    _ ≤ rowEuclideanNorm (Node := Node) x +
          rowEuclideanNorm (Node := Node) negY :=
        rowEuclideanNorm_add_le (Node := Node) x negY
    _ = rowEuclideanNorm (Node := Node) x +
          rowEuclideanNorm (Node := Node) y := by
        simp [negY, rowEuclideanNorm_neg]

/-- The custom operator norm is insensitive, at the inequality level needed
here, to swapping the two arguments of `matrixSub`. -/
theorem matrixEuclideanOperatorNorm_matrixSub_comm_le
    (A B : NodeMatrix Node) {C : ℝ}
    (hC : matrixEuclideanOperatorNorm (Node := Node)
        (matrixSub (Node := Node) A B) ≤ C) :
    matrixEuclideanOperatorNorm (Node := Node)
        (matrixSub (Node := Node) B A) ≤ C := by
  classical
  have hC_nonneg : 0 ≤ C :=
    le_trans
      ((matrixEuclideanOperatorNorm_spec (Node := Node)
        (matrixSub (Node := Node) A B)).1) hC
  unfold matrixEuclideanOperatorNorm
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro d hd
    exact hd.1
  · constructor
    · exact hC_nonneg
    · intro x
      have haction :
          rowEuclideanNorm (Node := Node)
              (matrixMulVector (Node := Node)
                (matrixSub (Node := Node) A B) x) ≤
            matrixEuclideanOperatorNorm (Node := Node)
                (matrixSub (Node := Node) A B) *
              rowEuclideanNorm (Node := Node) x :=
        rowEuclideanNorm_matrixMulVector_le
          (Node := Node) (matrixSub (Node := Node) A B) x
      have hnorm_nonneg :
          0 ≤ rowEuclideanNorm (Node := Node) x := by
        simpa [rowEuclideanNorm] using
          Real.sqrt_nonneg (rowNormSq (Node := Node) x)
      have hswap :
          matrixMulVector (Node := Node)
              (matrixSub (Node := Node) B A) x =
            fun i =>
              -matrixMulVector (Node := Node)
                (matrixSub (Node := Node) A B) x i := by
        funext i
        simp only [matrixMulVector, matrixSub, sub_mul]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      calc
        rowEuclideanNorm (Node := Node)
            (matrixMulVector (Node := Node)
              (matrixSub (Node := Node) B A) x) =
            rowEuclideanNorm (Node := Node)
              (fun i =>
                -matrixMulVector (Node := Node)
                  (matrixSub (Node := Node) A B) x i) := by
              rw [hswap]
        _ =
            rowEuclideanNorm (Node := Node)
              (matrixMulVector (Node := Node)
                (matrixSub (Node := Node) A B) x) :=
              rowEuclideanNorm_neg (Node := Node)
                (matrixMulVector (Node := Node)
                  (matrixSub (Node := Node) A B) x)
        _ ≤
            matrixEuclideanOperatorNorm (Node := Node)
                (matrixSub (Node := Node) A B) *
              rowEuclideanNorm (Node := Node) x :=
              haction
        _ ≤ C * rowEuclideanNorm (Node := Node) x :=
              mul_le_mul_of_nonneg_right hC hnorm_nonneg

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
